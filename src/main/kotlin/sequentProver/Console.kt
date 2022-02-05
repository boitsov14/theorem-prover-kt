package sequentProver

import core.Formula.*
import core.Term
import core.Term.*
import core.*
import kotlin.system.measureTimeMillis

const val max = 4
// TODO: 2022/01/20 そのうち消す

fun Sequent.prove() {
	val start = System.currentTimeMillis()
	var count = 0
	var unificationTermInstantiationMaxCount = 0
	var unificationTermIndex = 0
	var totalUnificationTime = 0L

	val rootNode = Node(this, null)
	val nodes = mutableListOf(rootNode)
	val substitution = mutableMapOf<UnificationTerm,Term>()
	val allUnificationTermsWithSiblingLabel = mutableMapOf<Int, MutableSet<UnificationTerm>>()

	loop@ while (true) {
		count++
		//nodes.forEach { println(it.sequentToBeApplied) }

		if (count >= 60000) {
			println("PROOF IS TOO LONG")
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
				val fmlIndex = tactic.getAvailableFmlIndex(sequentToBeApplied)
				if (fmlIndex == -1) continue
				//val fml = tactic.availableFmls(sequentToBeApplied).firstOrNull() ?: continue
				// TODO: 2022/01/29 二重ループ改善?
				val applyData = UnaryTactic.ApplyData(tactic, fmlIndex)
				val sequent = applyData.applyTactic(sequentToBeApplied)
				val newNode = Node(sequent, node.siblingLabel)
				node.applyDataWithNode = UnaryApplyDataWithNode(applyData, newNode)
				nodes[index] = newNode
				//println(">>> $tactic")
				continue@loop
			}
		}

		for ((index, node) in nodes.withIndex()) {
			val sequentToBeApplied = node.sequentToBeApplied
			for (tactic in BinaryTactic.values()) {
				val fmlIndex = tactic.getAvailableFmlIndex(sequentToBeApplied)
				if (fmlIndex == -1) continue
				//val fml = tactic.availableFmls(sequentToBeApplied).firstOrNull() ?: continue
				val applyData = BinaryTactic.ApplyData(tactic, fmlIndex)
				val leftSequent = applyData.applyTactic(sequentToBeApplied).first
				val rightSequent = applyData.applyTactic(sequentToBeApplied).second
				val leftNode = Node(leftSequent, node.siblingLabel)
				val rightNode = Node(rightSequent, node.siblingLabel)
				node.applyDataWithNode = BinaryApplyDataWithNodes(applyData, leftNode, rightNode)
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

		val startUnification = System.currentTimeMillis()
		val siblingNodesListWithLabel = nodes.groupBy { it.siblingLabel }.minus(null)
		for ((siblingLabel, siblingNodes) in siblingNodesListWithLabel) {
			val siblingSubstitutionsList = siblingNodes.map { it.sequentToBeApplied }.map { it.getSubstitutions() }
			if (siblingSubstitutionsList.any { it.isEmpty() }) continue
			val siblingSubstitution0 = getSubstitution(siblingSubstitutionsList) ?: continue
			val additionalSubstitution = allUnificationTermsWithSiblingLabel[siblingLabel]!!.subtract(siblingSubstitution0.keys).associateWith { it.availableVars.first() }
			val siblingSubstitution = (siblingSubstitution0 + additionalSubstitution).getCompleteSubstitution()
			substitution.putAll(siblingSubstitution)
			nodes.removeAll(siblingNodes)
			println("node size: ${siblingNodes.size}")
			(siblingSubstitution).forEach { println(it) }
		}
		val endUnification = System.currentTimeMillis()
		val unificationTime = endUnification - startUnification
		println("Unification try: $unificationTime ms")
		totalUnificationTime += unificationTime

		for ((index, node) in nodes.withIndex()) {
			val sequentToBeApplied = node.sequentToBeApplied
			val fmlAllIndex 	= UnificationTermTactic.ALL_LEFT.getAvailableFmlIndex(sequentToBeApplied, unificationTermInstantiationMaxCount)
			val fmlExistsIndex 	= UnificationTermTactic.EXISTS_RIGHT.getAvailableFmlIndex(sequentToBeApplied, unificationTermInstantiationMaxCount)
			val availableVars = sequentToBeApplied.freeVars.ifEmpty { setOf(Var("v")) }
			val unificationTerm = UnificationTerm(unificationTermIndex, availableVars)
			val applyData = if (fmlAllIndex != -1) {
				UnificationTermTactic.ApplyData(UnificationTermTactic.ALL_LEFT, fmlAllIndex, unificationTerm)
			} else if (fmlExistsIndex != -1) {
				UnificationTermTactic.ApplyData(UnificationTermTactic.EXISTS_RIGHT, fmlExistsIndex, unificationTerm)
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
			node.applyDataWithNode = UnificationTermApplyDataWithNode(applyData, newNode)
			nodes[index] = newNode
			unificationTermIndex++
			allUnificationTermsWithSiblingLabel.getOrPut(siblingLabel) { mutableSetOf() }.add(unificationTerm)
			println(">>> ${applyData.tactic}")
			continue@loop
		}

		if (unificationTermInstantiationMaxCount == max) {
			println("PROOF FAILED")
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

	print("Complete Proof Start... ")
	val completeProofTime = measureTimeMillis{
		rootNode.completeProof(substitution)
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
