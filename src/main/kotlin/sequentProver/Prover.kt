package sequentProver

import core.Formula

// TODO: 2022/01/21 これらは必要なのか
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
