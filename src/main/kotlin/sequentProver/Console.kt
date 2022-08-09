package sequentProver

import core.Formula.*
import core.Term
import core.Term.*
import core.*
import sequentProver.ProofState.*
import kotlin.system.measureTimeMillis

suspend fun Node.prove(
	printTimeInfo: Boolean = false,
	printUnificationInfo: Boolean = false,
	printTacticInfo: Boolean = false,
	printSequents: Boolean = false,
	unificationTermInstantiationMaxCountMax: Int = 4,
): ProofState {
	val start = System.currentTimeMillis()
	var count = 0
	var unificationTermInstantiationMaxCount = 0
	var unificationTermIndex = 0
	var totalUnificationTime = 0L

	val nodes = mutableListOf(this)
	val substitution = mutableMapOf<UnificationTerm, Term>()
	val allUnificationTerms = mutableSetOf<UnificationTerm>()
	val proofState: ProofState

	loop@ while (true) {
		count++
		if (printSequents) nodes.forEach { println(it.sequentToBeApplied) }

		if (nodes.isEmpty()) {
			proofState = Provable
			break
		}

		for (node in nodes) {
			if (AXIOM.canApply(node.sequentToBeApplied)) {
				nodes.remove(node)
				if (printTacticInfo) println(">>> $AXIOM")
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
				if (printTacticInfo) println(">>> $tactic")
				continue@loop
			}
		}

		for ((index, node) in nodes.withIndex()) {
			val sequentToBeApplied = node.sequentToBeApplied
			for (tactic in FreshVarInstantiationTactic.values()) {
				val fml = tactic.getAvailableFml(sequentToBeApplied) ?: continue
				val freshVar = fml.bddVar.getFreshVar(sequentToBeApplied.freeVars)
				val applyData = FreshVarInstantiationTactic.ApplyData(fml, freshVar)
				val sequent = applyData.applyTactic(sequentToBeApplied)
				val newNode = Node(sequent, node.siblingLabel)
				node.applyData = applyData
				node.child = newNode
				nodes[index] = newNode
				if (printTacticInfo) println(">>> $tactic")
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
				if (printTacticInfo) println(">>> $tactic")
				continue@loop
			}
		}

		if (nodes.all {
				it.sequentToBeApplied.assumptions.filterIsInstance<ALL>()
					.isEmpty() && it.sequentToBeApplied.conclusions.filterIsInstance<EXISTS>().isEmpty()
			}) {
			proofState = Unprovable
			break
		}

		val siblingNodesList = nodes.groupBy { it.siblingLabel }.minus(null).values
		for (siblingNodes in siblingNodesList) {
			val siblingSubstitutionsList =
				siblingNodes.map { it.sequentToBeApplied }.map { it.getSubstitutions() }.sortedBy { it.size }
			if (siblingSubstitutionsList.any { it.isEmpty() }) continue
			val siblingSubstitution: Substitution?
			val unificationTime = measureTimeMillis {
				siblingSubstitution = getSubstitution(siblingSubstitutionsList)
			}
			if (printUnificationInfo) println("Unification try: $unificationTime ms")
			totalUnificationTime += unificationTime
			if (siblingSubstitution == null) continue
			//val siblingSubstitution = getSubstitution(siblingSubstitutionsList) ?: continue
			substitution.putAll(siblingSubstitution)
			nodes.removeAll(siblingNodes)
			if (printUnificationInfo) {
				println("node size: ${siblingNodes.size}")
				(siblingSubstitution).forEach { println(it) }
			}
		}

		for ((index, node) in nodes.withIndex()) {
			val sequentToBeApplied = node.sequentToBeApplied
			val fml = TermInstantiationTactic.ALL_LEFT.getAvailableFml(
				sequentToBeApplied, unificationTermInstantiationMaxCount
			) ?: TermInstantiationTactic.EXISTS_RIGHT.getAvailableFml(
				sequentToBeApplied, unificationTermInstantiationMaxCount
			) ?: continue
			val availableVars = sequentToBeApplied.freeVars.ifEmpty { setOf(fml.bddVar) }
			val unificationTerm = UnificationTerm(unificationTermIndex, availableVars)
			val applyData = TermInstantiationTactic.ApplyData(fml, unificationTerm)
			val sequent = applyData.applyTactic(sequentToBeApplied)
			val siblingLabel = node.siblingLabel ?: unificationTerm.id
			val newNode = Node(sequent, siblingLabel)
			node.applyData = applyData
			node.child = newNode
			nodes[index] = newNode
			unificationTermIndex++
			allUnificationTerms.add(unificationTerm)
			if (printTacticInfo) println(">>> ${applyData.tactic}")
			continue@loop
		}

		if (unificationTermInstantiationMaxCount == unificationTermInstantiationMaxCountMax) {
			proofState = UnificationTermInstantiationCountFail
			break
		}

		unificationTermInstantiationMaxCount++
		if (printTacticInfo) println(">>> unificationTermMax: $unificationTermInstantiationMaxCount")

	}

	print(proofState)

	val end = System.currentTimeMillis()
	val time = end - start

	if (proofState == Provable || proofState == Unprovable) {
		print(" Completed in ${time / 1000.0}s.")
	}

	if (printTimeInfo) {
		println()
		println("Completed in $time ms")
		println("unification time: $totalUnificationTime ms")
		println("other time: ${time - totalUnificationTime} ms")
		println("loop count: $count")
	}

	val completeProofTime = measureTimeMillis {
		val remainedSubstitution = allUnificationTerms.subtract(substitution.keys).associateWith { Dummy }
		val completeSubstitution = if (nodes.isEmpty()) {
			(substitution + remainedSubstitution).getCompleteSubstitution()
		} else {
			substitution.getCompleteSubstitution()
		}
		this.completeProof(completeSubstitution)
		if (printUnificationInfo) completeSubstitution.forEach { println(it) }
	}
	if (printTimeInfo) println("Proof formatted in $completeProofTime ms")

	if (printTimeInfo) println(">>>>>>>>>>>>> $time ms")

	return proofState

	/*
	if (nodes.isEmpty()) {
		print("Show Console Output? (y/n) >>> ")
		if (readLine()!! == "y") {
			println("-----------------------------------")
			rootNode.printProof()
			println("-----------------------------------")
		}
	}
	 */
}
