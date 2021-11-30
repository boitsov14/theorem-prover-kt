package core.prover

import core.formula.*
import core.tactic.*

class UnableToProveException: Exception()

fun applyBasicApplicableTactic(goal: Goal): IApplyData = when {
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
	Tactic0.INTRO_ALL.canApply(goal) -> {
		Tactic0.ApplyData(Tactic0.INTRO_ALL)
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
