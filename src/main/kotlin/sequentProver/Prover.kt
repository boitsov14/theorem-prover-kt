package sequentProver

import sequentProver.BasicTactic.*

// TODO: 2021/12/12 これ他にも使い道ありそう
// TODO: 2021/12/12 basicではないtacticを定義した際は修正が必要

val allBasicTactics = listOf(ASSUMPTION, IMPLIES_RIGHT, NOT_RIGHT, NOT_LEFT, OR_RIGHT, AND_LEFT, IFF_LEFT, OR_LEFT, AND_RIGHT, IFF_RIGHT, ALL_RIGHT, EXISTS_LEFT, IMPLIES_LEFT)

fun applyBasicTacticOrNull(sequent: Sequent): IApplyData? {
	val tactic = allBasicTactics.find { it.canApply(sequent) } ?: return null
	val fml = tactic.availableFmls(sequent).first()
	return ApplyData(tactic, fml)
}
