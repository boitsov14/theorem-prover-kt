package sequentProver

import core.Formula

const val max = 4
// TODO: 2022/01/20 そのうち消す

fun Sequent.prove() {
	val start = System.currentTimeMillis()
	var count = 0
	var unificationTermInstantiationMaxCount = 0
	var unificationTermIndex = 0
	val histories = mutableListOf<History0>(emptyList())
	val sequents = mutableListOf<Sequent?>(this)

	val rootNode = Node(this)
	val nodes = mutableListOf(rootNode)

	//var oldEnd = System.currentTimeMillis()
	//var tooLong = 10000L

	loop@ while (true) {
		count++
		//sequents.filterNotNull().forEach { println(it) }
		nodes.forEach { println(it.sequentToBeApplied) }

		if (count >= 60000) {
			println("PROOF IS TOO LONG")
			break
		}

		/*
		if (sequents.size >= tooLong) {
			println("The proof is too long!!! >>> $tooLong")
			val firstNotNull = sequents.indexOfFirst { it != null }
			println("Remained conjunction >>> ${sequents[firstNotNull]?.conclusions?.filterIsInstance<Formula.AND>()?.size}")
			println("Remained disjunction >>> ${sequents[firstNotNull]?.assumptions?.filterIsInstance<Formula.OR>()?.size}")
			println("${firstNotNull.toFloat() / sequents.size * 100} % DONE.")
			val end = System.currentTimeMillis()
			val time = end - start
			val minutes = time/1000/60
			val seconds = time/1000%60
			println("total time >>> $minutes min $seconds s")
			val interval = end - oldEnd
			println("interval time >>> ${interval/1000} s")
			oldEnd = end
			tooLong += 10000
			println("----------------------------------------")
		}
		 */

		/*
		if (sequents.filterNotNull().isEmpty()) {
			println("PROOF SUCCEED!")
			break
		}
		 */
		if (nodes.isEmpty()) {
			println("PROOF SUCCEED!")
			break
		}

		/*
		for ((index, sequent) in sequents.withIndex()) {
			if (sequent == null) continue
			if (AXIOM.canApply(sequent)) {
				histories[index] = histories[index] + AXIOM.ApplyData
				sequents[index] = null
				//println(">>> $AXIOM")
				continue@loop
				// TODO: 2022/01/25 break or continue@loop ?
			}
		}
		 */
		/*
		val axiomIndex = sequents.indexOfFirst { it != null && AXIOM.canApply(it) }
		if (axiomIndex != -1) {
			histories[axiomIndex] = histories[axiomIndex] + AXIOM.ApplyData
			sequents[axiomIndex] = null
			//println(">>> $AXIOM")
			continue
		}
		 */
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
				node.applyDataWithNode = AxiomApplyData
				nodes.remove(node)
				println(">>> $AXIOM")
				continue@loop
			}
		}

		/*
		for ((index, sequent) in sequents.withIndex()) {
			if (sequent == null) continue
			for (tactic in UnaryTactic.values()) {
				val fml = tactic.availableFmls(sequent).firstOrNull() ?: continue
				val applyData = UnaryTactic.ApplyData(tactic, fml)
				histories[index] = histories[index] + applyData
				sequents[index] = applyData.applyTactic(sequent)
				//println(">>> ${unaryApplyData.tactic}")
				continue@loop
			}
		}
		 */
		// TODO: 2022/01/29 indexは必要なのか
		for ((index, node) in nodes.withIndex()) {
			val sequentToBeApplied = node.sequentToBeApplied
			for (tactic in UnaryTactic.values()) {
				val fml = tactic.availableFmls(sequentToBeApplied).firstOrNull() ?: continue
				// TODO: 2022/01/29 二重ループ改善?
				val applyData = UnaryTactic.ApplyData(tactic, fml)
				val sequent = applyData.applyTactic(sequentToBeApplied)
				val newNode = Node(sequent)
				node.applyDataWithNode = UnaryApplyDataWithNode(applyData, newNode)
				nodes[index] = newNode
				println(">>> $tactic")
				continue@loop
			}
		}

		/*
		for ((index, sequent) in sequents.withIndex()) {
			if (sequent == null) continue
			for (tactic in BinaryTactic.values()) {
				val fml = tactic.availableFmls(sequent).firstOrNull() ?: continue
				val applyData0First = BinaryTactic.ApplyData0(tactic, fml, true)
				val applyData0Second = BinaryTactic.ApplyData0(tactic, fml, false)
				histories.add(index + 1, histories[index] + applyData0First)
				histories.add(index + 2, histories[index] + applyData0Second)
				histories.removeAt(index)
				sequents.add(index + 1, applyData0First.applyTactic(sequent))
				sequents.add(index + 2, applyData0Second.applyTactic(sequent))
				sequents.removeAt(index)
				//println(">>> ${binaryApplyData.first.tactic}")
				continue@loop
			}
		}
		 */
		for ((index, node) in nodes.withIndex()) {
			val sequentToBeApplied = node.sequentToBeApplied
			for (tactic in BinaryTactic.values()) {
				val fml = tactic.availableFmls(sequentToBeApplied).firstOrNull() ?: continue
				val applyData = BinaryTactic.ApplyData(tactic, fml)
				val leftSequent = tactic.applyTactic(sequentToBeApplied, fml).first
				val rightSequent = tactic.applyTactic(sequentToBeApplied, fml).second
				val leftNode = Node(leftSequent)
				val rightNode = Node(rightSequent)
				node.applyDataWithNode = BinaryApplyDataWithNodes(applyData, leftNode, rightNode)
				nodes[index] = leftNode
				nodes.add(index + 1, rightNode)
				println(">>> $tactic")
				continue@loop
			}
		}

		for ((index, node) in nodes.withIndex()) {
			val sequentToBeApplied = node.sequentToBeApplied
			// TODO: 2022/01/29 availableFmlsを使うか
			val availableExistsRightFmls 	= sequentToBeApplied.conclusions.filterIsInstance<Formula.EXISTS>().filter { it.unificationTermInstantiationCount <= unificationTermInstantiationMaxCount }
			val availableAllLeftFmls 		= sequentToBeApplied.assumptions.filterIsInstance<Formula.ALL>().filter { it.unificationTermInstantiationCount <= unificationTermInstantiationMaxCount }
			val applyData = if (availableExistsRightFmls.isNotEmpty()) {
				val fml = availableExistsRightFmls.first()
				UnificationTermTactic.ApplyData(UnificationTermTactic.EXISTS_RIGHT, fml, unificationTermIndex)
			} else if (availableAllLeftFmls.isNotEmpty()) {
				val fml = availableAllLeftFmls.first()
				UnificationTermTactic.ApplyData(UnificationTermTactic.ALL_LEFT, fml, unificationTermIndex)
			} else {
				continue
			}
			val sequent = applyData.applyTactic(sequentToBeApplied)
			val newNode = Node(sequent)
			node.applyDataWithNode = UnificationTermApplyDataWithNode(applyData, newNode)
			nodes[index] = newNode
			unificationTermIndex++
			println(">>> ${applyData.tactic}")
			continue@loop
		}

		if (unificationTermInstantiationMaxCount == 0
			&& nodes.none {
				it.sequentToBeApplied.assumptions.filterIsInstance<Formula.ALL>().isNotEmpty()
						|| it.sequentToBeApplied.conclusions.filterIsInstance<Formula.EXISTS>().isNotEmpty() }) {
			println("UNPROVABLE")
			break
		}

		if (unificationTermInstantiationMaxCount == max) {
			println("PROOF FAILED")
			break
		}

		unificationTermInstantiationMaxCount++
		println(">>> unificationTermMax: $unificationTermInstantiationMaxCount")

		/*

		val unProvable = sequents.filterNotNull().none { it.assumptions.filterIsInstance<Formula.ALL>().isNotEmpty()
				|| it.conclusions.filterIsInstance<Formula.EXISTS>().isNotEmpty() }
		if (unProvable) {
			println("UNPROVABLE")
			break
		}

		val unificationTacticIndex = sequents.indexOfFirst { it != null && applyUnificationTermTacticOrNull(it, unificationTermIndex, unificationTermInstantiationMaxCount) != null }
		if (unificationTacticIndex != -1) {
			val oldSequent = sequents[unificationTacticIndex]!!
			val unificationTermApplyData = applyUnificationTermTacticOrNull(oldSequent, unificationTermIndex, unificationTermInstantiationMaxCount)!!
			histories[unificationTacticIndex] = histories[unificationTacticIndex] + unificationTermApplyData
			sequents[unificationTacticIndex] = unificationTermApplyData.applyTactic(oldSequent)
			unificationTermIndex++
			println(">>> ${unificationTermApplyData.tactic}")
		} else {
			unificationTermInstantiationMaxCount++
			println(">>> unificationTermMax: $unificationTermInstantiationMaxCount")
		}
		if (unificationTermInstantiationMaxCount == max) {
			println("PROOF FAILED")
			break
		}
		 */
	}
	val end = System.currentTimeMillis()
	val time = end - start
	println("Completed in $time ms")
	println("loop count: $count")

	//println("histories size: ${histories.size}")
	//println("longest history size: ${histories.map { it.size }.maxOrNull()}")
	//println("total history size: ${histories.sumOf { it.size }}")

	/*

	val historyForLatex: HistoryWithSequents
	println("Latex Start...")
	val timeGetLatexProof = measureTimeMillis{
		historyForLatex = histories.getLatexProof(this)
	}
	println("Completed in $timeGetLatexProof ms")


	for (data in historyForLatex) {
		if (data == null) {
			println("\\AxiomC{}")
			continue
		}
		println("\\RightLabel{\\scriptsize ${data.applyData.tactic.toLatex()}}")
		when(data.applyData.tactic) {
			is BinaryTactic -> println("\\BinaryInf$${data.sequentToBeApplied.toLatex()}$")
			else -> println("\\UnaryInf$${data.sequentToBeApplied.toLatex()}$")
		}
	}

	if (sequents.filterNotNull().isNotEmpty()) return

	//println("-----------------------------------")
	//println(this)

	println("One line proof Start...")
	val history: History
	val timeGetOneLineProof = measureTimeMillis{
		history = histories.getOneLineProof()
	}
	println("Completed in $timeGetOneLineProof ms")

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

data class ApplyData0WithSequent(val sequentToBeApplied: Sequent, val applyData0: IApplyData0)

typealias History0WithSequents = List<ApplyData0WithSequent>

data class ApplyDataWithSequent(val sequentToBeApplied: Sequent, val applyData: IApplyData)

typealias HistoryWithSequents = List<ApplyDataWithSequent?>

private fun ApplyData0WithSequent.toApplyDataWithSequent(): ApplyDataWithSequent = ApplyDataWithSequent(this.sequentToBeApplied, this.applyData0.toApplyData())

private fun List<History0>.getOneLineProof(): History {
	val result = this.first().map { it.toApplyData() }.toMutableList()
	for ((index, history0) in this.drop(1).withIndex()) {
		val differIndex = this[index].zip(history0).indexOfFirst { it.first != it.second }
		result.addAll(history0.drop(differIndex + 1).map { it.toApplyData() })
	}
	return result
}

private fun List<History0>.getOneLineProofWithSequents(firstSequent: Sequent): HistoryWithSequents {
	var preHistory0WithSequents = this.first().toHistory0WithSequents(firstSequent)
	val result: MutableList<ApplyDataWithSequent?> = preHistory0WithSequents.map { it.toApplyDataWithSequent() }.toMutableList()
	result.add(null)
	for ((index, history0) in this.drop(1).withIndex()) {
		val differIndex = this[index].zip(history0).indexOfFirst { it.first != it.second }
		val newHistory0WithSequents = history0.drop(differIndex).toHistory0WithSequents(preHistory0WithSequents[differIndex].sequentToBeApplied)
		preHistory0WithSequents = preHistory0WithSequents.take(differIndex) + newHistory0WithSequents
		result.addAll(newHistory0WithSequents.drop(1).map { it.toApplyDataWithSequent() })
		result.add(null)
	}
	return result
}

private fun List<History0>.getLatexProof(firstSequent: Sequent): HistoryWithSequents =
	reversed().getOneLineProofWithSequents(firstSequent).reversed()

private fun History0.toHistory0WithSequents(firstSequent: Sequent): History0WithSequents {
	val result = mutableListOf<ApplyData0WithSequent>()
	var sequentToBeApplied = firstSequent
	for ((index, applyData0) in this.withIndex()) {
		sequentToBeApplied = this.elementAtOrNull(index - 1).applyTactic(sequentToBeApplied)
		result.add(ApplyData0WithSequent(sequentToBeApplied, applyData0))
	}
	return result
}

/*
((o11 ∨ o12 ∨ o13) ∧ (o21 ∨ o22 ∨ o23) ∧ (o31 ∨ o32 ∨ o33) ∧ (o41 ∨ o42 ∨ o43)) → ((o11 ∧ o21) ∨ (o11 ∧ o31) ∨ (o11 ∧ o41) ∨ (o21 ∧ o31) ∨ (o21 ∧ o41) ∨ (o31 ∧ o41) ∨ (o12 ∧ o22) ∨ (o12 ∧ o32) ∨ (o12 ∧ o42) ∨ (o22 ∧ o32) ∨ (o22 ∧ o42) ∨ (o32 ∧ o42) ∨ (o13 ∧ o23) ∨ (o13 ∧ o33) ∨ (o13 ∧ o43) ∨ (o23 ∧ o33) ∨ (o23 ∧ o43) ∨ (o33 ∧ o43))
PROOF SUCCEED!
Completed in 365 ms
loop count: 8669
Latex Start...
Completed in 161 ms
One line proof Start...
Completed in 26 ms
Print all proof Start...
Completed in 83 ms
proof size: 8668

((o11 ∨ o12 ∨ o13 ∨ o14) ∧ (o21 ∨ o22 ∨ o23 ∨ o24) ∧ (o31 ∨ o32 ∨ o33 ∨ o34) ∧ (o41 ∨ o42 ∨ o43 ∨ o44) ∧ (o51 ∨ o52 ∨ o53 ∨ o54)) → ((o11 ∧ o21) ∨ (o11 ∧ o31) ∨ (o11 ∧ o41) ∨ (o11 ∧ o51) ∨ (o21 ∧ o31) ∨ (o21 ∧ o41) ∨ (o21 ∧ o51) ∨ (o31 ∧ o41) ∨ (o31 ∧ o51) ∨ (o41 ∧ o51) ∨ (o12 ∧ o22) ∨ (o12 ∧ o32) ∨ (o12 ∧ o42) ∨ (o12 ∧ o52) ∨ (o22 ∧ o32) ∨ (o22 ∧ o42) ∨ (o22 ∧ o52) ∨ (o32 ∧ o42) ∨ (o32 ∧ o52) ∨ (o42 ∧ o52) ∨ (o13 ∧ o23) ∨ (o13 ∧ o33) ∨ (o13 ∧ o43) ∨ (o13 ∧ o53) ∨ (o23 ∧ o33) ∨ (o23 ∧ o43) ∨ (o23 ∧ o53) ∨ (o33 ∧ o43) ∨ (o33 ∧ o53) ∨ (o43 ∧ o53) ∨ (o14 ∧ o24) ∨ (o14 ∧ o34) ∨ (o14 ∧ o44) ∨ (o14 ∧ o54) ∨ (o24 ∧ o34) ∨ (o24 ∧ o44) ∨ (o24 ∧ o54) ∨ (o34 ∧ o44) ∨ (o34 ∧ o54) ∨ (o44 ∧ o54))
PROOF IS TOO LONG
Completed in 1914 ms
loop count: 60000
Latex Start...
Completed in 1665 ms

Completed in 6796 ms
Completed in 7593 ms
Completed in 6771 ms
Completed in 7110 ms
Completed in 7245 ms
Completed in 7197 ms

Completed in 8080 ms
Completed in 7693 ms
Completed in 7153 ms
Completed in 8303 ms
Completed in 8900 ms

 */
