package sequentProver

import sequentProver.BasicTactic.*

val allBasicTactics = listOf(ASSUMPTION, IMPLIES_RIGHT, NOT_RIGHT, NOT_LEFT, OR_RIGHT, AND_LEFT, IFF_LEFT, OR_LEFT, AND_RIGHT, IFF_RIGHT, ALL_RIGHT, EXISTS_LEFT, IMPLIES_LEFT)

fun applyBasicTacticOrNull(sequent: Sequent): IApplyData? {
	val tactic = allBasicTactics.find { it.canApply(sequent) } ?: return null
	val fml = tactic.availableFmls(sequent).first()
	return ApplyData(tactic, fml)
}
