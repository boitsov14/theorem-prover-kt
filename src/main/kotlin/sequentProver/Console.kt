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


fun Sequent.prove() {
	val start = System.currentTimeMillis()
	var count = 0
	var currentUnificationTermSubstitutedCountMax = 0
	val unificationTermSubstitutedCountMax = 5
	var allUnificationTermsSize = 0
	val duplicateHistories = mutableListOf<History0>(emptyList())

	while (true) {
		count++
		val index = duplicateHistories.indexOfFirst { it.lastOrNull() != AXIOM.ApplyData }
		if (index == -1) {
			println("PROOF SUCCEED!")
			break
		}
		val history = duplicateHistories[index]
		val sequent = history.applyTactics(this)
		println(sequent)
		if (AXIOM.canApply(sequent)) {
			duplicateHistories[index] = history + AXIOM.ApplyData
			println(">>> $AXIOM")
			continue
		}
		val unaryApplyData = applyUnaryTacticOrNull(sequent)
		if (unaryApplyData != null) {
			duplicateHistories[index] = history + unaryApplyData
			println(">>> ${unaryApplyData.tactic}")
			continue
		}
		val binaryApplyData = applyBinaryTacticOrNull(sequent)
		if (binaryApplyData != null) {
			duplicateHistories.removeAt(index)
			duplicateHistories.add(index, history + binaryApplyData.first)
			duplicateHistories.add(index + 1, history + binaryApplyData.second)
			println(">>> ${binaryApplyData.first.tactic}")
			continue
		}
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
		if (unProvable) {
			println("UNPROVABLE")
			break
		}
		var temIndex = index
		while (true) {
			val tempHistory = duplicateHistories[temIndex]
			val tepSequent = tempHistory.applyTactics(this)
			val unificationTermApplyData = applyUnificationTermTacticOrNull(tepSequent, allUnificationTermsSize, currentUnificationTermSubstitutedCountMax)
			if (unificationTermApplyData == null) {
				while (true) {
					temIndex++
					if (temIndex == duplicateHistories.size) {
						currentUnificationTermSubstitutedCountMax++
						temIndex = index
						break
					}
					if (duplicateHistories[temIndex].lastOrNull() != AXIOM.ApplyData) {
						continue
					}
					break
				}
			} else {
				allUnificationTermsSize++
				duplicateHistories[index] = history + unificationTermApplyData
				println(">>> ${unificationTermApplyData.tactic}")
				break
			}
		}
		if (currentUnificationTermSubstitutedCountMax > unificationTermSubstitutedCountMax) {
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
		val sequents = history.take(index + 1).applyTactics(this.toSequents())
		sequents.forEach { println(it) }
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
