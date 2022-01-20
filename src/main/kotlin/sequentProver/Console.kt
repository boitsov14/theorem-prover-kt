package sequentProver

import core.Formula

/*
fun Sequents.prove() {
	val start = System.currentTimeMillis()
	var count = 0
	val history = mutableListOf<IApplyData>()

	while (true) {
		val sequents = history.applyTactics(this)
		printSequents(sequents)
		if (sequents.isEmpty()) {
			println("PROOF SUCCEED!")
			break
		}
		val sequent = sequents.first()
		val applyData = applyBasicTacticOrNull(sequent)
		if (applyData == null) {
			println("PROOF FAILED")
			break
		}
		println(">>> ${applyData.tactic}")
		history.add(applyData)
		count++
	}
	val end = System.currentTimeMillis()
	val time = end - start
	println("Completed in $time ms")
	println("loop count: $count")
}

fun printSequents(sequents: Sequents) {
	sequents.forEach { println(it) }
}
 */

const val max = 5
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
		sequents.forEach { println(it) }

		/*
		val index = sequents.indexOfFirst { it != null }
		//val index = duplicateHistories.indexOfFirst { it.lastOrNull() != AXIOM.ApplyData }
		if (index == -1) {
			println("PROOF SUCCEED!")
			break
		}
		 */

		//val sequentsToBeProven = sequents.filterNotNull()
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

		/*
		val history = duplicateHistories[index]
		val sequent = sequents[index] as Sequent
		//val sequent = history.applyTactics(this)
		println(sequent)
		if (AXIOM.canApply(sequent)) {
			duplicateHistories[index] = history + AXIOM.ApplyData
			sequents[index] = null
			println(">>> $AXIOM")
			continue
		}
		val unaryApplyData = applyUnaryTacticOrNull(sequent)
		if (unaryApplyData != null) {
			duplicateHistories[index] = history + unaryApplyData
			sequents[index] = unaryApplyData.applyTactic(sequent)
			println(">>> ${unaryApplyData.tactic}")
			continue
		}
		val binaryApplyData = applyBinaryTacticOrNull(sequent)
		if (binaryApplyData != null) {
			duplicateHistories.removeAt(index)
			duplicateHistories.add(index, history + binaryApplyData.first)
			duplicateHistories.add(index + 1, history + binaryApplyData.second)
			sequents.removeAt(index)
			sequents.add(index, binaryApplyData.first.applyTactic(sequent))
			sequents.add(index + 1, binaryApplyData.second.applyTactic(sequent))
			println(">>> ${binaryApplyData.first.tactic}")
			continue
		}
		 */
		val unProvable = sequents.filterNotNull().none { it.assumptions.filterIsInstance<Formula.ALL>().isNotEmpty()
				|| it.conclusions.filterIsInstance<Formula.EXISTS>().isNotEmpty() }
		/*
		var unProvable = true
		val remainedDuplicateHistories = duplicateHistories.filterNot { it.lastOrNull() == AXIOM.ApplyData }
		for (remainedHistory in remainedDuplicateHistories) {
			val remainedSequent = remainedHistory.applyTactics(this)
			if (remainedSequent.conclusions.filterIsInstance<Formula.EXISTS>().isNotEmpty()) {
				unProvable = false
				break
			}
			if (remainedSequent.assumptions.filterIsInstance<Formula.ALL>().isNotEmpty()) {
				unProvable = false
				break
			}
		}
		 */
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

		/*
		var temIndex = index
		while (true) {
			val tempHistory = histories[temIndex]
			val tepSequent = tempHistory.applyTactics(this)
			val unificationTermApplyData = applyUnificationTermTacticOrNull(tepSequent, unificationTermIndex, unificationTermInstantiationMaxCount)
			if (unificationTermApplyData == null) {
				while (true) {
					temIndex++
					if (temIndex == histories.size) {
						unificationTermInstantiationMaxCount++
						temIndex = index
						break
					}
					if (histories[temIndex].lastOrNull() != AXIOM.ApplyData) {
						continue
					}
					break
				}
			} else {
				histories[index] = history + unificationTermApplyData
				println(">>> ${unificationTermApplyData.tactic}")
				unificationTermIndex++
				break
			}
		}
		*/

		if (unificationTermInstantiationMaxCount == max) {
			println("PROOF FAILED")
			break
		}
		//printSequents(sequent)
	}
	val end = System.currentTimeMillis()
	val time = end - start
	println("Completed in $time ms")
	println("loop count: $count")

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

private fun History0.toHistory(): History = this.map {
	when(it) {
		AXIOM.ApplyData -> it as IApplyData
		is UnaryTactic.ApplyData -> it
		is BinaryTactic.ApplyData0 -> BinaryTactic.ApplyData(it.tactic, it.fml)
		is UnificationTermTactic.ApplyData -> it
		is TermTactic.ApplyData -> it
	}
}

private fun List<History0>.getOneLineProof(): History {
	val result = this.first().toHistory().toMutableList()
	for ((index, history0) in this.drop(1).withIndex()) {
		val differIndex = this[index].zip(history0).indexOfFirst { it.first != it.second }
		result.addAll(history0.drop(differIndex + 1).toHistory())
	}
	return result
}
