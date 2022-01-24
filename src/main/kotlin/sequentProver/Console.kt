package sequentProver

import core.Formula
import kotlin.system.measureTimeMillis

const val max = 3
// TODO: 2022/01/20 そのうち消す

fun Sequent.prove() {
	val start = System.currentTimeMillis()
	var count = 0
	var unificationTermInstantiationMaxCount = 0
	var unificationTermIndex = 0
	val histories = mutableListOf<History0>(emptyList())
	val sequents = mutableListOf<Sequent?>(this)

	while (true) {
		count++
		//sequents.filterNotNull().forEach { println(it) }

		if (sequents.filterNotNull().isEmpty()) {
			println("PROOF SUCCEED!")
			break
		}
		val axiomIndex = sequents.indexOfFirst { it != null && AXIOM.canApply(it) }
		if (axiomIndex != -1) {
			histories[axiomIndex] = histories[axiomIndex] + AXIOM.ApplyData
			sequents[axiomIndex] = null
			//println(">>> $AXIOM")
			continue
		}
		val unaryIndex = sequents.indexOfFirst { it != null && applyUnaryTacticOrNull(it) != null }
		if (unaryIndex != -1) {
			val oldSequent = sequents[unaryIndex]!!
			val unaryApplyData = applyUnaryTacticOrNull(oldSequent)!!
			histories[unaryIndex] = histories[unaryIndex] + unaryApplyData
			sequents[unaryIndex] = unaryApplyData.applyTactic(oldSequent)
			//println(">>> ${unaryApplyData.tactic}")
			continue
		}
		val binaryIndex = sequents.indexOfFirst { it != null && applyBinaryTacticOrNull(it) != null }
		if (binaryIndex != -1) {
			val history = histories[binaryIndex]
			val oldSequent = sequents[binaryIndex]!!
			val binaryApplyData = applyBinaryTacticOrNull(oldSequent)!!
			histories.removeAt(binaryIndex)
			histories.add(binaryIndex, history + binaryApplyData.first)
			histories.add(binaryIndex + 1, history + binaryApplyData.second)
			sequents.removeAt(binaryIndex)
			sequents.add(binaryIndex, binaryApplyData.first.applyTactic(oldSequent))
			sequents.add(binaryIndex + 1, binaryApplyData.second.applyTactic(oldSequent))
			//println(">>> ${binaryApplyData.first.tactic}")
			continue
		}

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
	}
	val end = System.currentTimeMillis()
	val time = end - start
	println("Completed in $time ms")
	println("loop count: $count")

	//println("histories size: ${histories.size}")
	//println("longest history size: ${histories.map { it.size }.maxOrNull()}")
	//println("total history size: ${histories.sumOf { it.size }}")

	val historyForLatex: HistoryWithSequents
	println("Latex Start...")
	val timeGetLatexProof = measureTimeMillis{
		historyForLatex = histories.getLatexProof(this)
	}
	println("Completed in $timeGetLatexProof ms")
	//val historyForLatex = histories.getLatexProof(this)

	/*
	for (data in historyForLatex) {
		if (data == null) {
			println("\\AxiomC{}")
			continue
		}
		println("\\RightLabel{\\scriptsize ${data.applyData.tactic}}")
		when(data.applyData.tactic) {
			is BinaryTactic -> println("\\BinaryInf$${data.sequentToBeApplied}$")
			else -> println("\\UnaryInf$${data.sequentToBeApplied}$")
		}
	}
	 */

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
		for ((index, applyData) in history.withIndex()) {
			//println(">>> ${applyData.tactic}")
			val sequents0 = history.take(index + 1).applyTactics(this.toSequents())
			//sequents0.forEach { println(it) }
		}
	}
	println("Completed in $timePrintProof ms")
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
Completed in 585 ms
loop count: 8669
Latex Start...
Completed in 159 ms
One line proof Start...
Completed in 24 ms
Print all proof Start...
Completed in 205479 ms
 */
