package sequentProver

import core.Formula

// TODO: 2022/01/21 これらは必要なのか
fun applyUnaryTacticOrNull(sequent: Sequent): IApplyData0? {
	val tactic = UnaryTactic.values().find { it.canApply(sequent) } ?: return null
	val fml = tactic.availableFmls(sequent).first()
	return UnaryTactic.ApplyData(tactic, fml)
}

fun applyBinaryTacticOrNull(sequent: Sequent): Pair<IApplyData0, IApplyData0>? {
	val tactic = BinaryTactic.values().find { it.canApply(sequent) } ?: return null
	val fml = tactic.availableFmls(sequent).first()
	return BinaryTactic.ApplyData0(tactic, fml, true) to BinaryTactic.ApplyData0(tactic, fml, false)
}

fun applyUnificationTermTacticOrNull(sequent: Sequent, unificationTermIndex: Int, unificationTermInstantiationMaxCount : Int): IApplyData0? {
	val availableERFmls = sequent.conclusions.filterIsInstance<Formula.EXISTS>().filter { it.unificationTermInstantiationCount <= unificationTermInstantiationMaxCount }
	val availableALFmls = sequent.assumptions.filterIsInstance<Formula.ALL>().filter { it.unificationTermInstantiationCount <= unificationTermInstantiationMaxCount }
	return if (availableERFmls.isNotEmpty()) {
		val fml = availableERFmls.first()
		UnificationTermTactic.ApplyData(UnificationTermTactic.EXISTS_RIGHT, fml, unificationTermIndex)
	} else if (availableALFmls.isNotEmpty()) {
		val fml = availableALFmls.first()
		UnificationTermTactic.ApplyData(UnificationTermTactic.ALL_LEFT, fml, unificationTermIndex)
	} else {
		null
	}
}
