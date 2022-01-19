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
	val duplicateHistories = mutableListOf<History0>(emptyList())
	val sequents = mutableListOf<Sequent?>(this)

	while (true) {
		count++
		val index = sequents.indexOfFirst { it != null }
		//val index = duplicateHistories.indexOfFirst { it.lastOrNull() != AXIOM.ApplyData }
		if (index == -1) {
			println("PROOF SUCCEED!")
			break
		}
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
		var temIndex = index
		while (true) {
			val tempHistory = duplicateHistories[temIndex]
			val tepSequent = tempHistory.applyTactics(this)
			val unificationTermApplyData = applyUnificationTermTacticOrNull(tepSequent, unificationTermIndex, unificationTermInstantiationMaxCount)
			if (unificationTermApplyData == null) {
				while (true) {
					temIndex++
					if (temIndex == duplicateHistories.size) {
						unificationTermInstantiationMaxCount++
						temIndex = index
						break
					}
					if (duplicateHistories[temIndex].lastOrNull() != AXIOM.ApplyData) {
						continue
					}
					break
				}
			} else {
				duplicateHistories[index] = history + unificationTermApplyData
				println(">>> ${unificationTermApplyData.tactic}")
				unificationTermIndex++
				break
			}
		}
		if (unificationTermInstantiationMaxCount > max) {
			println("PROOF FAILED")
			break
		}
		//printSequents(sequent)
	}
	val end = System.currentTimeMillis()
	val time = end - start
	println("Completed in $time ms")
	println("loop count: $count")

	println("-----------------------------------")
	println(this)

	val history = getOneLineProof(duplicateHistories)
	for ((index, applyData) in history.withIndex()) {
		println(">>> ${applyData.tactic}")
		val sequents0 = history.take(index + 1).applyTactics(this.toSequents())
		sequents0.forEach { println(it) }
	}
}

fun History0.toHistory(): History = this.map {
	when(it) {
		AXIOM.ApplyData -> it as IApplyData
		is UnaryTactic.ApplyData -> it
		is BinaryTactic.ApplyData0 -> BinaryTactic.ApplyData(it.tactic, it.fml)
		is UnificationTermTactic.ApplyData -> it
		is TermTactic.ApplyData -> it
	}
}

fun getOneLineProof(duplicateHistories: List<History0>): History {
	val result = mutableListOf<IApplyData>()
	val firstHistory0 = duplicateHistories.first()
	result.addAll(firstHistory0.toHistory())
	for ((index, history0) in duplicateHistories.drop(1).withIndex()) {
		val oldHistory0 = duplicateHistories[index]
		val differIndex = oldHistory0.zip(history0).indexOfFirst { it.first != it.second }
		result.addAll(history0.drop(differIndex + 1).toHistory())
	}
	return result
}
