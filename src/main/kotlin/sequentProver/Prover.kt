package sequentProver

import core.Formula

/*
val allBasicTactics = listOf(AXIOM, IMPLIES_RIGHT, NOT_RIGHT, NOT_LEFT, OR_RIGHT, AND_LEFT, IFF_LEFT, OR_LEFT, AND_RIGHT, IFF_RIGHT, ALL_RIGHT, EXISTS_LEFT, IMPLIES_LEFT)

fun applyBasicTacticOrNull(sequent: Sequent): IApplyData? {
	val tactic = allBasicTactics.find { it.canApply(sequent) } ?: return null
	val fml = tactic.availableFmls(sequent).first()
	return ApplyData(tactic, fml)
}
*/

fun applyAxiomOrNull(sequent: Sequent): IApplyData0? = if (AXIOM.canApply(sequent)) {
	AXIOM.ApplyData
} else {
	null
}

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

fun applyUnificationTermTacticOrNull(sequent: Sequent, allUnificationTermsSize: Int, currentUnificationTermSubstitutedCountMax : Int): IApplyData0? {
	val availableEXISTSFmls = sequent.conclusions.filterIsInstance<Formula.EXISTS>().filter { it.unificationTermSubstitutedCount <= currentUnificationTermSubstitutedCountMax }
	val availableALLFmls = sequent.assumptions.filterIsInstance<Formula.ALL>().filter { it.unificationTermSubstitutedCount <= currentUnificationTermSubstitutedCountMax }
	return if (availableEXISTSFmls.isNotEmpty()) {
		val fml = availableEXISTSFmls.first()
		UnificationTermTactic.ApplyData(UnificationTermTactic.EXISTS_RIGHT, fml, allUnificationTermsSize)
	} else if (availableALLFmls.isNotEmpty()) {
		val fml = availableALLFmls.first()
		UnificationTermTactic.ApplyData(UnificationTermTactic.ALL_LEFT, fml, allUnificationTermsSize)
	} else {
		null
	}
}
