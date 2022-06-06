package tacticGame

import core.Formula.*
import tacticGame.Tactic0.*
import tacticGame.Tactic1WithFml.*

// import tacticGame.Tactic1WithVar.*
// import tacticGame.Tactic2WithVar.*

class UnableToProveException : Exception()

fun applyBasicTactic(goal: Goal): IApplyData = when {
	ASSUMPTION.canApply(goal) -> {
		Tactic0.ApplyData(ASSUMPTION)
	}
	FALSE in goal.assumptions -> {
		Tactic0.ApplyData(EXFALSO)
	}
	HAVE_NOT.canApply(goal) -> {
		val assumption = HAVE_NOT.availableAssumptions(goal).first()
		Tactic1WithFml.ApplyData(HAVE_NOT, assumption)
	}
	INTRO_IMPLIES.canApply(goal) -> {
		Tactic0.ApplyData(INTRO_IMPLIES)
	}
	INTRO_NOT.canApply(goal) -> {
		Tactic0.ApplyData(INTRO_NOT)
	}
	HAVE_IMPLIES.canApply(goal) -> {
		// TODO: 2021/11/30 (a to b) to c, a to b, a のようなときに先にa to bされると渋い？
		val assumption =
			HAVE_IMPLIES.availableAssumptions(goal).sortedWith(compareBy { it.toString().length }).reversed().first()
		Tactic1WithFml.ApplyData(HAVE_IMPLIES, assumption)
	}
	CASES_AND.canApply(goal) -> {
		val assumption = CASES_AND.availableAssumptions(goal).first()
		Tactic1WithFml.ApplyData(CASES_AND, assumption)
	}
	CASES_IFF.canApply(goal) -> {
		val assumption = CASES_IFF.availableAssumptions(goal).first()
		Tactic1WithFml.ApplyData(CASES_IFF, assumption)
	}
	CASES_OR.canApply(goal) -> {
		val assumption = CASES_OR.availableAssumptions(goal).first()
		Tactic1WithFml.ApplyData(CASES_OR, assumption)
	}
	SPLIT_AND.canApply(goal) -> {
		Tactic0.ApplyData(SPLIT_AND)
	}
	SPLIT_IFF.canApply(goal) -> {
		Tactic0.ApplyData(SPLIT_IFF)
	}
	else -> {
		throw UnableToProveException()
	}
}

fun applyAdvancedTactic(goal: Goal): List<IApplyData> {
	val result = mutableListOf<IApplyData>()
	for (assumption in APPLY_NOT.availableAssumptions(goal)) {
		result.add(Tactic1WithFml.ApplyData(APPLY_NOT, assumption))
	}
	for (assumption in APPLY_IMPLIES.availableAssumptions(goal)) {
		result.add(Tactic1WithFml.ApplyData(APPLY_IMPLIES, assumption))
	}
	for (assumption in HAVE_IMPLIES_WITHOUT_LEFT.availableAssumptions(goal)) {
		result.add(Tactic1WithFml.ApplyData(HAVE_IMPLIES_WITHOUT_LEFT, assumption))
	}
	if (EXFALSO.canApply(goal)) {
		result.add(Tactic0.ApplyData(EXFALSO))
	}
	if (BY_CONTRA.canApply(goal)) {
		result.add(Tactic0.ApplyData(BY_CONTRA))
	}
	return result
}

fun applyManyBasicTactics(inputGoals: Goals): History {
	val history = mutableListOf<IApplyData>()
	while (true) {
		val goals = history.applyTactics(inputGoals)
		if (goals.isEmpty()) {
			return history
		}
		val goal = goals.first()
		try {
			history.add(applyBasicTactic(goal))
		} catch (e: UnableToProveException) {
			return history
		}
	}
}

/*
INPUT A FORMULA >>> not (P and Q and R and S and T) to (not P or not Q or not R or not S or not T)
Completed in 604 ms
loop count: 14665
histories size: 11798
oldGoals size: 22899
duplicate count: 16272

INPUT A FORMULA >>> not (P and Q and R and S and T and U) to (not P or not Q or not R or not S or not T or not U)
Completed in 5325 ms
loop count: 161694
histories size: 128010
oldGoals size: 237527
duplicate count: 210007

INPUT A FORMULA >>> not (P and Q and R and S and T and U and V) to (not P or not Q or not R or not S or not T or not U or not V)
Completed in 81941 ms
loop count: 2057665
histories size: 1589524
 */
