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

		/*
		val axiomIndex = nodes.indexOfFirst { AXIOM.canApply(it.sequentToBeProved) }
		if (axiomIndex != -1) {
			nodes[axiomIndex].applyDataWithNode = AxiomApplyData
			nodes.removeAt(axiomIndex)
			//println(">>> $AXIOM")
			continue
		}
		 */
		// TODO: 2022/01/29 上と下どっちがよいか
		for (node in nodes) {
			if (AXIOM.canApply(node.sequentToBeApplied)) {
				//node.applyDataWithNode = AxiomApplyData
				nodes.remove(node)
				println(">>> $AXIOM")
				continue@loop
			}
		}

		// TODO: 2022/01/29 indexは必要なのか
		for ((index, node) in nodes.withIndex()) {
			val sequentToBeApplied = node.sequentToBeApplied
			for (tactic in UnaryTactic.values()) {
				val fml = tactic.availableFmls(sequentToBeApplied).firstOrNull() ?: continue
				// TODO: 2022/01/29 二重ループ改善?
				val applyData = UnaryTactic.ApplyData(tactic, fml)
				val sequent = applyData.applyTactic(sequentToBeApplied)
				val newNode = Node(sequent, node.siblingLabel)
				node.applyDataWithNode = UnaryApplyDataWithNode(applyData, newNode)
				nodes[index] = newNode
				println(">>> $tactic")
				continue@loop
			}
		}

		for ((index, node) in nodes.withIndex()) {
			val sequentToBeApplied = node.sequentToBeApplied
			for (tactic in BinaryTactic.values()) {
				val fml = tactic.availableFmls(sequentToBeApplied).firstOrNull() ?: continue
				val applyData = BinaryTactic.ApplyData(tactic, fml)
				val leftSequent = applyData.applyTactic(sequentToBeApplied).first
				val rightSequent = applyData.applyTactic(sequentToBeApplied).second
				val leftNode = Node(leftSequent, node.siblingLabel)
				val rightNode = Node(rightSequent, node.siblingLabel)
				node.applyDataWithNode = BinaryApplyDataWithNodes(applyData, leftNode, rightNode)
				nodes[index] = leftNode
				nodes.add(index + 1, rightNode)
				println(">>> $tactic")
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
		val siblingNodesList = nodes.groupBy { it.siblingLabel }.minus(null).values
		for (siblingNodes in siblingNodesList) {
			val siblingSubstitutionsList = siblingNodes.map { it.sequentToBeApplied }.map { it.getSubstitutions() }
			if (siblingSubstitutionsList.any { it.isEmpty() }) continue
			val siblingSubstitution = getSubstitution(siblingSubstitutionsList) ?: continue
			substitution.putAll(siblingSubstitution)
			nodes.removeAll(siblingNodes)
			println("node size: ${siblingNodes.size}")
			siblingSubstitution.forEach { println(it) }
		}
		val endUnification = System.currentTimeMillis()
		val unificationTime = endUnification - startUnification
		println("Unification try: $unificationTime ms")
		totalUnificationTime += unificationTime

		for ((index, node) in nodes.withIndex()) {
			val sequentToBeApplied = node.sequentToBeApplied
			// TODO: 2022/01/29 availableFmlsを使うか
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
			val sequent = applyData.applyTactic(sequentToBeApplied)
			val siblingLabel = node.siblingLabel ?: applyData.unificationTerm.id
			val newNode = Node(sequent, siblingLabel)
			node.applyDataWithNode = UnificationTermApplyDataWithNode(applyData, newNode)
			nodes[index] = newNode
			unificationTermIndex++
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

	/*
	val isCorrectProof: Boolean
	print("Proof Check Start... ")
	val checkProofTime = measureTimeMillis{
		isCorrectProof = rootNode.checkCorrectness()
	}
	if (isCorrectProof) {
		println("SUCCEED!")
	} else {
		println("FAIL!")
	}
	println("Completed in $checkProofTime ms")
	 */

	val latexProof: String
	println("Latex Start...")
	val getLatexProofTime = measureTimeMillis{
		latexProof = rootNode.getLatexProof()
	}
	println("Completed in $getLatexProofTime ms")

	print("Show Latex Output? (y/n) >>> ")
	if (readLine()!! == "y") {
		println("-----------------------------------")
		println(latexProof)
		println("-----------------------------------")
	}

	/*
	println("Print all proof Start...")
	val timePrintProof = measureTimeMillis{
		var currentSequents = this.toSequents()
		for (applyData in history) {
			//println(">>> ${applyData.tactic}")
			currentSequents = applyData.applyTactic(currentSequents)
			//currentSequents.forEach { println(it) }
		}
	}
	println("Completed in $timePrintProof ms")
	println("proof size: ${history.size}")
	 */
}

/*
((o11 ∨ o12 ∨ o13) ∧ (o21 ∨ o22 ∨ o23) ∧ (o31 ∨ o32 ∨ o33) ∧ (o41 ∨ o42 ∨ o43)) → ((o11 ∧ o21) ∨ (o11 ∧ o31) ∨ (o11 ∧ o41) ∨ (o21 ∧ o31) ∨ (o21 ∧ o41) ∨ (o31 ∧ o41) ∨ (o12 ∧ o22) ∨ (o12 ∧ o32) ∨ (o12 ∧ o42) ∨ (o22 ∧ o32) ∨ (o22 ∧ o42) ∨ (o32 ∧ o42) ∨ (o13 ∧ o23) ∨ (o13 ∧ o33) ∨ (o13 ∧ o43) ∨ (o23 ∧ o33) ∨ (o23 ∧ o43) ∨ (o33 ∧ o43))
PROOF SUCCEED!
Completed in 391 ms
loop count: 8669
Proof Check Start... SUCCEED!
Completed in 122 ms
Latex Start...
Completed in 245 ms

((o11 ∨ o12 ∨ o13 ∨ o14) ∧ (o21 ∨ o22 ∨ o23 ∨ o24) ∧ (o31 ∨ o32 ∨ o33 ∨ o34) ∧ (o41 ∨ o42 ∨ o43 ∨ o44) ∧ (o51 ∨ o52 ∨ o53 ∨ o54)) → ((o11 ∧ o21) ∨ (o11 ∧ o31) ∨ (o11 ∧ o41) ∨ (o11 ∧ o51) ∨ (o21 ∧ o31) ∨ (o21 ∧ o41) ∨ (o21 ∧ o51) ∨ (o31 ∧ o41) ∨ (o31 ∧ o51) ∨ (o41 ∧ o51) ∨ (o12 ∧ o22) ∨ (o12 ∧ o32) ∨ (o12 ∧ o42) ∨ (o12 ∧ o52) ∨ (o22 ∧ o32) ∨ (o22 ∧ o42) ∨ (o22 ∧ o52) ∨ (o32 ∧ o42) ∨ (o32 ∧ o52) ∨ (o42 ∧ o52) ∨ (o13 ∧ o23) ∨ (o13 ∧ o33) ∨ (o13 ∧ o43) ∨ (o13 ∧ o53) ∨ (o23 ∧ o33) ∨ (o23 ∧ o43) ∨ (o23 ∧ o53) ∨ (o33 ∧ o43) ∨ (o33 ∧ o53) ∨ (o43 ∧ o53) ∨ (o14 ∧ o24) ∨ (o14 ∧ o34) ∨ (o14 ∧ o44) ∨ (o14 ∧ o54) ∨ (o24 ∧ o34) ∨ (o24 ∧ o44) ∨ (o24 ∧ o54) ∨ (o34 ∧ o44) ∨ (o34 ∧ o54) ∨ (o44 ∧ o54))
PROOF IS TOO LONG
Completed in 3117 ms
loop count: 60000
Proof Check Start... FAIL!
Completed in 1177 ms
Latex Start...
Completed in 1004 ms

 */
