package sequentProver

import core.Formula.*
import core.Term
import core.Term.*
import core.*
import kotlin.system.measureTimeMillis

//const val unificationTermInstantiationMaxCountMax = 4
// TODO: 2022/01/20 そのうち消す

fun Sequent.prove(loopCountMax: Int = 500_000, unificationTermInstantiationMaxCountMax: Int = 5, totalUnificationTimeMax: Long = 30_000) {
	val start = System.currentTimeMillis()
	var count = 0
	var unificationTermInstantiationMaxCount = 0
	var unificationTermIndex = 0
	var totalUnificationTime = 0L

	val rootNode = Node(this, null)
	val nodes = mutableListOf(rootNode)
	val substitution = mutableMapOf<UnificationTerm,Term>()
	val allUnificationTerms = mutableSetOf<UnificationTerm>()

	loop@ while (true) {
		count++
		//nodes.forEach { println(it.sequentToBeApplied) }

		if (count >= loopCountMax) {
			println("PROOF FAILED: PROOF IS TOO LONG OR UNPROVABLE")
			break
		}

		if (nodes.isEmpty()) {
			println("PROOF SUCCEED!")
			break
		}

		for (node in nodes) {
			if (AXIOM.canApply(node.sequentToBeApplied)) {
				nodes.remove(node)
				//println(">>> $AXIOM")
				continue@loop
			}
		}

		for ((index, node) in nodes.withIndex()) {
			val sequentToBeApplied = node.sequentToBeApplied
			for (tactic in UnaryTactic.values()) {
				val fml = tactic.getAvailableFml(sequentToBeApplied) ?: continue
				// TODO: 2022/01/29 二重ループ改善?
				val applyData = UnaryTactic.ApplyData(tactic, fml)
				val sequent = applyData.applyTactic(sequentToBeApplied)
				val newNode = Node(sequent, node.siblingLabel)
				node.applyData = applyData
				node.child = newNode
				nodes[index] = newNode
				//println(">>> $tactic")
				continue@loop
			}
		}

		for ((index, node) in nodes.withIndex()) {
			val sequentToBeApplied = node.sequentToBeApplied
			for (tactic in BinaryTactic.values()) {
				val fml = tactic.getAvailableFml(sequentToBeApplied) ?: continue
				val applyData = BinaryTactic.ApplyData(tactic, fml)
				val leftSequent = applyData.applyTactic(sequentToBeApplied).first
				val rightSequent = applyData.applyTactic(sequentToBeApplied).second
				val leftNode = Node(leftSequent, node.siblingLabel)
				val rightNode = Node(rightSequent, node.siblingLabel)
				node.applyData = applyData
				node.leftChild = leftNode
				node.rightChild = rightNode
				nodes[index] = leftNode
				nodes.add(index + 1, rightNode)
				//println(">>> $tactic")
				continue@loop
			}
		}

		if (unificationTermInstantiationMaxCount == 0
			&& nodes.none {
				it.sequentToBeApplied.assumptions.filterIsInstance<ALL>().isNotEmpty()
						|| it.sequentToBeApplied.conclusions.filterIsInstance<EXISTS>().isNotEmpty() }) {
			println("UNPROVABLE")
			break
		}

		val siblingNodesList = nodes.groupBy { it.siblingLabel }.minus(null).values
		for (siblingNodes in siblingNodesList) {
			val siblingSubstitutionsList = siblingNodes.map { it.sequentToBeApplied }.map { it.getSubstitutions() }
			if (siblingSubstitutionsList.any { it.isEmpty() }) continue
			val siblingSubstitution: Substitution?
			val unificationTime = measureTimeMillis {
				siblingSubstitution = getSubstitution(siblingSubstitutionsList)
			}
			println("Unification try: $unificationTime ms")
			totalUnificationTime += unificationTime
			if (siblingSubstitution == null) continue
			//val siblingSubstitution = getSubstitution(siblingSubstitutionsList) ?: continue
			substitution.putAll(siblingSubstitution)
			nodes.removeAll(siblingNodes)
			println("node size: ${siblingNodes.size}")
			(siblingSubstitution).forEach { println(it) }
		}

		if (totalUnificationTime > totalUnificationTimeMax) {
			println("PROOF FAILED: PROOF IS TOO LONG OR UNPROVABLE")
			break
		}

		for ((index, node) in nodes.withIndex()) {
			val sequentToBeApplied = node.sequentToBeApplied
			val fmlAll 		= UnificationTermTactic.ALL_LEFT.getAvailableFml(sequentToBeApplied, unificationTermInstantiationMaxCount)
			val fmlExists 	= UnificationTermTactic.EXISTS_RIGHT.getAvailableFml(sequentToBeApplied, unificationTermInstantiationMaxCount)
			val availableVars = setOf(Var("v")) + sequentToBeApplied.freeVars
			val unificationTerm = UnificationTerm(unificationTermIndex, availableVars)
			val applyData = if (fmlAll != null) {
				UnificationTermTactic.ApplyData(UnificationTermTactic.ALL_LEFT, fmlAll, unificationTerm)
			} else if (fmlExists != null) {
				UnificationTermTactic.ApplyData(UnificationTermTactic.EXISTS_RIGHT, fmlExists, unificationTerm)
			} else {
				continue
			}
			/*
			val availableExistsRightFmls 	= UnificationTermTactic.EXISTS_RIGHT.availableFmls(sequentToBeApplied, unificationTermInstantiationMaxCount)
			val availableAllLeftFmls 		= UnificationTermTactic.ALL_LEFT.availableFmls(sequentToBeApplied, unificationTermInstantiationMaxCount)
			val applyData = if (availableExistsRightFmls.isNotEmpty()) {
				val fml = availableExistsRightFmls.first() as EXISTS
				val availableVars = sequentToBeApplied.freeVars.ifEmpty { setOf(fml.bddVar) }
				val unificationTerm = UnificationTerm(unificationTermIndex, availableVars)
				UnificationTermTactic.ApplyData(UnificationTermTactic.EXISTS_RIGHT, fml, unificationTerm)
			} else if (availableAllLeftFmls.isNotEmpty()) {
				val fml = availableAllLeftFmls.first() as ALL
				val availableVars = sequentToBeApplied.freeVars.ifEmpty { setOf(fml.bddVar) }
				val unificationTerm = UnificationTerm(unificationTermIndex, availableVars)
				UnificationTermTactic.ApplyData(UnificationTermTactic.ALL_LEFT, fml, unificationTerm)
			} else {
				continue
			}
			 */
			val sequent = applyData.applyTactic(sequentToBeApplied)
			val siblingLabel = node.siblingLabel ?: applyData.unificationTerm.id
			val newNode = Node(sequent, siblingLabel)
			node.applyData = applyData
			node.child = newNode
			nodes[index] = newNode
			unificationTermIndex++
			allUnificationTerms.add(unificationTerm)
			println(">>> ${applyData.tactic}")
			continue@loop
		}

		if (unificationTermInstantiationMaxCount == unificationTermInstantiationMaxCountMax) {
			println("PROOF FAILED: PROOF IS TOO LONG OR UNPROVABLE")
			break
		}

		unificationTermInstantiationMaxCount++
		println(">>> unificationTermMax: $unificationTermInstantiationMaxCount")

	}
	val end = System.currentTimeMillis()
	val time = end - start
	println("Completed in $time ms")
	println("unification time: $totalUnificationTime ms")
	println("other time: ${time - totalUnificationTime} ms")
	println("loop count: $count")

	println("Complete Proof Start... ")
	val completeProofTime = measureTimeMillis{
		val remainedSubstitution = allUnificationTerms.subtract(substitution.keys).associateWith { it.availableVars.first() }
		val completeSubstitution = (substitution + remainedSubstitution).getCompleteSubstitution()
		rootNode.completeProof(completeSubstitution)
		(completeSubstitution).forEach { println(it) }
	}
	println("Completed in $completeProofTime ms")

	val latexProof: String
	print("Latex Start...")
	val getLatexProofTime = measureTimeMillis{
		latexProof = rootNode.getProofTree()
	}
	println("Completed in $getLatexProofTime ms")

	print("Show Latex Output? (y/n) >>> ")
	if (readLine()!! == "y") {
		println("-----------------------------------")
		println("\\begin{prooftree}")
		println("\\def\\fCenter{\\mbox{\$\\vdash\$}}")
		println(latexProof)
		println("\\end{prooftree}")
		println("-----------------------------------")
	}

	if (nodes.isEmpty()) {
		print("Show Console Output? (y/n) >>> ")
		if (readLine()!! == "y") {
			println("-----------------------------------")
			rootNode.printProof()
			println("-----------------------------------")
		}
	}
}
