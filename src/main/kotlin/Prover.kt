package prover

import formula.*
import goal.*
import tactic.*

class UnableToProveException: Exception()

fun applyBasicTactic(goal: Goal): IApplyData = when {
	Tactic0.ASSUMPTION.canApply(goal) -> {
		Tactic0.ApplyData(Tactic0.ASSUMPTION)
	}
	Formula.FALSE in goal.assumptions -> {
		Tactic0.ApplyData(Tactic0.EXFALSO)
	}
	Tactic1WithFml.HAVE_NOT.canApply(goal) -> {
		val assumption = Tactic1WithFml.HAVE_NOT.availableAssumptions(goal).first()
		Tactic1WithFml.ApplyData(Tactic1WithFml.HAVE_NOT, assumption)
	}
	Tactic0.INTRO_IMPLIES.canApply(goal) -> {
		Tactic0.ApplyData(Tactic0.INTRO_IMPLIES)
	}
	Tactic0.INTRO_NOT.canApply(goal) -> {
		Tactic0.ApplyData(Tactic0.INTRO_NOT)
	}
	Tactic1WithFml.HAVE_IMPLIES.canApply(goal) -> {
		// TODO: 2021/11/30 (a to b) to c, a to b, a のようなときに先にa to bされると渋い？
		val assumption = Tactic1WithFml.HAVE_IMPLIES.availableAssumptions(goal).sortedWith(compareBy { it.toString().length }).reversed().first()
		Tactic1WithFml.ApplyData(Tactic1WithFml.HAVE_IMPLIES,assumption)
	}
	Tactic1WithFml.CASES_AND.canApply(goal) -> {
		val assumption = Tactic1WithFml.CASES_AND.availableAssumptions(goal).first()
		Tactic1WithFml.ApplyData(Tactic1WithFml.CASES_AND, assumption)
	}
	Tactic1WithFml.CASES_IFF.canApply(goal) -> {
		val assumption = Tactic1WithFml.CASES_IFF.availableAssumptions(goal).first()
		Tactic1WithFml.ApplyData(Tactic1WithFml.CASES_IFF, assumption)
	}
	Tactic1WithFml.CASES_OR.canApply(goal) -> {
		val assumption = Tactic1WithFml.CASES_OR.availableAssumptions(goal).first()
		Tactic1WithFml.ApplyData(Tactic1WithFml.CASES_OR, assumption)
	}
	Tactic0.SPLIT_AND.canApply(goal) -> {
		Tactic0.ApplyData(Tactic0.SPLIT_AND)
	}
	Tactic0.SPLIT_IFF.canApply(goal) -> {
		Tactic0.ApplyData(Tactic0.SPLIT_IFF)
	}
	else -> {
		throw UnableToProveException()
	}
}

fun applyAdvancedTactic(goal: Goal): List<IApplyData> {
	val result = mutableListOf<IApplyData>()
	for (assumption in Tactic1WithFml.APPLY_NOT.availableAssumptions(goal)) {
		result.add(Tactic1WithFml.ApplyData(Tactic1WithFml.APPLY_NOT, assumption))
	}
	for (assumption in Tactic1WithFml.APPLY_IMPLIES.availableAssumptions(goal)) {
		result.add(Tactic1WithFml.ApplyData(Tactic1WithFml.APPLY_IMPLIES, assumption))
	}
	for (assumption in Tactic1WithFml.HAVE_IMPLIES_WITHOUT_LEFT.availableAssumptions(goal)) {
		result.add(Tactic1WithFml.ApplyData(Tactic1WithFml.HAVE_IMPLIES_WITHOUT_LEFT, assumption))
	}
	if (Tactic0.EXFALSO.canApply(goal)) {
		result.add(Tactic0.ApplyData(Tactic0.EXFALSO))
	}
	if (Tactic0.BY_CONTRA.canApply(goal)) {
		result.add(Tactic0.ApplyData(Tactic0.BY_CONTRA))
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
