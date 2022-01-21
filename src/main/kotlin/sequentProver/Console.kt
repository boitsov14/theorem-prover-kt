package sequentProver

import core.Formula

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
		sequents.filterNotNull().forEach { println(it) }

		if (sequents.filterNotNull().isEmpty()) {
			println("PROOF SUCCEED!")
			break
		}
		val axiomIndex = sequents.indexOfFirst { it != null && AXIOM.canApply(it) }
		if (axiomIndex != -1) {
			histories[axiomIndex] = histories[axiomIndex] + AXIOM.ApplyData
			sequents[axiomIndex] = null
			println(">>> $AXIOM")
			continue
		}
		val unaryIndex = sequents.indexOfFirst { it != null && applyUnaryTacticOrNull(it) != null }
		if (unaryIndex != -1) {
			val oldSequent = sequents[unaryIndex]!!
			val unaryApplyData = applyUnaryTacticOrNull(oldSequent)!!
			histories[unaryIndex] = histories[unaryIndex] + unaryApplyData
			sequents[unaryIndex] = unaryApplyData.applyTactic(oldSequent)
			println(">>> ${unaryApplyData.tactic}")
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
			println(">>> ${binaryApplyData.first.tactic}")
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

	val historyForLatex = histories.getLatexProof(this)
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

	if (sequents.filterNotNull().isNotEmpty()) return

	println("-----------------------------------")
	println(this)

	val history = histories.getOneLineProof()
	for ((index, applyData) in history.withIndex()) {
		println(">>> ${applyData.tactic}")
		val sequents0 = history.take(index + 1).applyTactics(this.toSequents())
		sequents0.forEach { println(it) }
	}
}

/*
private fun History0.toHistory(): History = this.map {
	when(it) {
		AXIOM.ApplyData -> it as IApplyData
		is UnaryTactic.ApplyData -> it
		is BinaryTactic.ApplyData0 -> BinaryTactic.ApplyData(it.tactic, it.fml)
		is UnificationTermTactic.ApplyData -> it
		is TermTactic.ApplyData -> it
	}
}
*/

private fun List<History0>.getOneLineProof(): History {
	val result = this.first().map { it.toApplyData() }.toMutableList()
	for ((index, history0) in this.drop(1).withIndex()) {
		val differIndex = this[index].zip(history0).indexOfFirst { it.first != it.second }
		result.addAll(history0.drop(differIndex + 1).map { it.toApplyData() })
	}
	return result
}

data class ApplyData0WithSequent(val sequentToBeApplied: Sequent, val applyData0: IApplyData0)

typealias History0WithSequents = List<ApplyData0WithSequent>

data class ApplyDataWithSequent(val sequentToBeApplied: Sequent, val applyData: IApplyData)

typealias HistoryWithSequents = List<ApplyDataWithSequent?>

private fun ApplyData0WithSequent.toApplyDataWithSequent(): ApplyDataWithSequent = ApplyDataWithSequent(this.sequentToBeApplied, this.applyData0.toApplyData())

private fun List<History0WithSequents>.getOneLineProofWithSequents(): HistoryWithSequents {
	val result: MutableList<ApplyDataWithSequent?> = this.first().map { it.toApplyDataWithSequent() }.toMutableList()
	result.add(null)
	for ((index, history0WithSequent) in this.drop(1).withIndex()) {
		val differIndex = this[index].zip(history0WithSequent).indexOfFirst { it.first.applyData0 != it.second.applyData0 }
		result.addAll(history0WithSequent.drop(differIndex + 1).map { it.toApplyDataWithSequent() })
		result.add(null)
	}
	return result
}

private fun List<History0>.getLatexProof(firstSequent: Sequent): HistoryWithSequents =
	map { it.toHistory0WithSequents(firstSequent) }.reversed().getOneLineProofWithSequents().reversed()

/*
private fun Sequent.toHistory0WithSequents(history0: History0): History0WithSequents {
	val result = mutableListOf<ApplyData0WithSequent>()
	for ((index, applyData0) in history0.withIndex()) {
		val sequentToBeApplied = history0.take(index).applyTactics(this)
		result.add(ApplyData0WithSequent(sequentToBeApplied, applyData0))
	}
	return result
}
 */

private fun History0.toHistory0WithSequents(firstSequent: Sequent): History0WithSequents =
	this.mapIndexed { index, applyData0 -> ApplyData0WithSequent(this.take(index).applyTactics(firstSequent), applyData0) }
