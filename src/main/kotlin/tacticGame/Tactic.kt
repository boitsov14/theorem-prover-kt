package tacticGame

import core.*
import core.Formula.*

sealed interface ITactic {
	fun canApply(goal: Goal): Boolean
}

val allTactics: List<ITactic> = Tactic0.values().toList() + Tactic1WithFml.values() + Tactic1WithVar.values() + Tactic2WithVar.values()
// TODO: 2021/10/28 change to set.

fun Goal.applicableTactics() = allTactics.filter { it.canApply(this) }

sealed interface IApplyData

typealias History = List<IApplyData>

fun IApplyData.applyTactic(goals: Goals): Goals = when(this) {
	is Tactic0.ApplyData 		-> this.tactic0.applyTactic(goals)
	is Tactic1WithFml.ApplyData -> this.tactic1WithFml.applyTactic(goals, this.assumption)
	is Tactic1WithVar.ApplyData -> this.tactic1WithVar.applyTactic(goals, this.fixedVar)
	is Tactic2WithVar.ApplyData -> this.tactic2WithVar.applyTactic(goals, this.assumption, this.fixedVar)
}

fun History.applyTactics(firstGoals: Goals): Goals = this.fold(firstGoals){ currentGoals, applyData -> applyData.applyTactic(currentGoals)}

class IllegalTacticException: Exception()

// Tactic with arity 0.
enum class Tactic0: ITactic {
	ASSUMPTION, INTRO_IMPLIES, INTRO_NOT, INTRO_ALL, SPLIT_AND, SPLIT_IFF, LEFT, RIGHT, EXFALSO, BY_CONTRA, USE_WITHOUT_FIXED_VARS;
	override fun toString(): String = when(this) {
		ASSUMPTION 	-> "assumption"
		INTRO_IMPLIES, INTRO_NOT, INTRO_ALL -> "intro"
		SPLIT_AND, SPLIT_IFF -> "split"
		LEFT -> "left"
		RIGHT -> "right"
		EXFALSO -> "exfalso"
		BY_CONTRA -> "by_contra"
		USE_WITHOUT_FIXED_VARS -> "use"
	}
	data class ApplyData(val tactic0: Tactic0): IApplyData
	override fun canApply(goal: Goal): Boolean {
		val conclusion = goal.conclusion
		return when(this) {
			ASSUMPTION		-> conclusion in goal.assumptions || conclusion == TRUE
			INTRO_IMPLIES 	-> conclusion is IMPLIES
			INTRO_NOT 		-> conclusion is NOT
			INTRO_ALL 		-> conclusion is ALL
			SPLIT_AND 		-> conclusion is AND
			SPLIT_IFF 		-> conclusion is IFF
			LEFT, RIGHT		-> conclusion is OR
			EXFALSO			-> conclusion != FALSE
			BY_CONTRA		-> conclusion != FALSE && NOT(conclusion) !in goal.assumptions
			USE_WITHOUT_FIXED_VARS -> conclusion is EXISTS && goal.freeVars.isEmpty()
		}
	}
	fun applyTactic(goals: Goals): Goals {
		val goal = goals[0]
		if (!(this.canApply(goal))) { throw IllegalTacticException() }
		val conclusion = goal.conclusion
		when(this) {
			ASSUMPTION -> return goals.replace()
			INTRO_IMPLIES -> {
				conclusion as IMPLIES
				val newGoal = goal.copy(
					assumptions = goal.assumptions.addIfDistinct(conclusion.leftFml),
					conclusion = conclusion.rightFml
				)
				return goals.replace(newGoal)
			}
			INTRO_NOT -> {
				conclusion as NOT
				val newGoal = goal.copy(
					assumptions = goal.assumptions.addIfDistinct(conclusion.operandFml),
					conclusion = FALSE
				)
				return goals.replace(newGoal)
			}
			INTRO_ALL -> {
				conclusion as ALL
				val newVar = conclusion.bddVar.getFreshVar(goal.freeVars.toSet())
				val newGoal = goal.copy(
					conclusion = conclusion.substitute(newVar)
				)
				return goals.replace(newGoal)
			}
			SPLIT_AND -> {
				conclusion as AND
				val left    = goal.copy(
					conclusion = conclusion.leftFml
				)
				val right   = goal.copy(
					conclusion = conclusion.rightFml
				)
				return goals.replace(left, right)
			}
			SPLIT_IFF -> {
				conclusion as IFF
				val toRight = goal.copy(
					conclusion = IMPLIES(conclusion.leftFml, conclusion.rightFml)
				)
				val toLeft  = goal.copy(
					conclusion = IMPLIES(conclusion.rightFml, conclusion.leftFml)
				)
				return goals.replace(toRight, toLeft)
			}
			LEFT -> {
				conclusion as OR
				val newGoal = goal.copy(
					conclusion = conclusion.leftFml
				)
				return goals.replace(newGoal)
			}
			RIGHT -> {
				conclusion as OR
				val newGoal = goal.copy(
					conclusion = conclusion.rightFml
				)
				return goals.replace(newGoal)
			}
			EXFALSO -> {
				val newGoal = goal.copy(
					conclusion = FALSE
				)
				return goals.replace(newGoal)
			}
			BY_CONTRA -> {
				val newGoal = goal.copy(
					assumptions = goal.assumptions + NOT(conclusion),
					conclusion = FALSE
				)
				return goals.replace(newGoal)
			}
			USE_WITHOUT_FIXED_VARS -> {
				conclusion as EXISTS
				val newGoal = goal.copy(
					conclusion = conclusion.operandFml
				)
				return goals.replace(newGoal)
			}
		}
	}
}

// Tactic with one formula.
enum class Tactic1WithFml: ITactic {
	APPLY_IMPLIES, APPLY_NOT, CASES_AND, CASES_OR, CASES_IFF, CASES_EXISTS, REVERT, CLEAR, HAVE_IMPLIES, HAVE_IMPLIES_WITHOUT_LEFT, HAVE_NOT, HAVE_WITHOUT_FIXED_VARS;
	override fun toString(): String = when(this) {
		APPLY_IMPLIES, APPLY_NOT -> "apply"
		CASES_AND, CASES_OR, CASES_IFF, CASES_EXISTS -> "cases"
		REVERT -> "revert"
		CLEAR -> "clear"
		HAVE_IMPLIES, HAVE_IMPLIES_WITHOUT_LEFT, HAVE_NOT, HAVE_WITHOUT_FIXED_VARS -> "have"
	}
	data class ApplyData(val tactic1WithFml: Tactic1WithFml, val assumption: Formula): IApplyData
	override fun canApply(goal: Goal): Boolean = availableAssumptions(goal).isNotEmpty()
	fun applyTactic(goals: Goals, assumption: Formula): Goals {
		val goal = goals[0]
		if (!(this.canApply(goal))) { throw IllegalTacticException() }
		when(this) {
			APPLY_IMPLIES -> {
				assumption as IMPLIES
				val newGoal = goal.copy(
					conclusion = assumption.leftFml
				)
				return goals.replace(newGoal)
			}
			APPLY_NOT -> {
				assumption as NOT
				val newGoal = goal.copy(
					conclusion = assumption.operandFml
				)
				return goals.replace(newGoal)
			}
			CASES_AND -> {
				assumption as AND
				val newGoal = goal.copy(
					assumptions = goal.assumptions.replaceIfDistinct(assumption, assumption.leftFml, assumption.rightFml)
				)
				return goals.replace(newGoal)
			}
			CASES_OR -> {
				assumption as OR
				val leftGoal	= goal.copy(
					assumptions = goal.assumptions.replace(assumption, assumption.leftFml)
				)
				val rightGoal	= goal.copy(
					assumptions = goal.assumptions.replace(assumption, assumption.rightFml)
				)
				return goals.replace(leftGoal, rightGoal)
			}
			CASES_IFF -> {
				assumption as IFF
				val toRight = IMPLIES(assumption.leftFml, assumption.rightFml)
				val toLeft  = IMPLIES(assumption.rightFml, assumption.leftFml)
				val newGoal = goal.copy(
					assumptions = goal.assumptions.replaceIfDistinct(assumption, toRight, toLeft)
				)
				return goals.replace(newGoal)
			}
			CASES_EXISTS -> {
				assumption as EXISTS
				val newVar = assumption.bddVar.getFreshVar(goal.freeVars.toSet())
				val newAssumption = assumption.substitute(newVar)
				val newGoal = goal.copy(
					assumptions = goal.assumptions.replace(assumption, newAssumption)
				)
				return goals.replace(newGoal)
			}
			REVERT -> {
				val newGoal = goal.copy(
					assumptions = goal.assumptions.minus(assumption),
					conclusion = IMPLIES(assumption, goal.conclusion)
				)
				return goals.replace(newGoal)
			}
			CLEAR -> {
				val newGoal = goal.copy(
					assumptions = goal.assumptions.minus(assumption)
				)
				return goals.replace(newGoal)
			}
			HAVE_IMPLIES -> {
				assumption as IMPLIES
				val newGoal = goal.copy(
					assumptions = goal.assumptions.replace(assumption, assumption.rightFml)
				)
				return goals.replace(newGoal)
			}
			HAVE_IMPLIES_WITHOUT_LEFT -> {
				assumption as IMPLIES
				val newGoal1 = goal.copy(
					assumptions = goal.assumptions,
					conclusion = assumption.leftFml
				)
				val newGoal2 = goal.copy(
					assumptions = goal.assumptions.replace(assumption, assumption.rightFml)
				)
				return goals.replace(newGoal1, newGoal2)
			}
			HAVE_NOT -> {
				val newGoal = goal.copy(
					assumptions = goal.assumptions + FALSE
				)
				return goals.replace(newGoal)
			}
			HAVE_WITHOUT_FIXED_VARS -> {
				assumption as ALL
				val newAssumption = assumption.operandFml
				val newGoal = goal.copy(
					assumptions = goal.assumptions.addBelow(assumption, newAssumption)
				)
				return goals.replace(newGoal)
			}
		}
	}
	// TODO: 2021/11/21 change to set.
	fun availableAssumptions(goal: Goal): List<Formula> = when(this) {
		APPLY_IMPLIES -> goal.assumptions
			.filterIsInstance<IMPLIES>()
			.filter { it.rightFml  == goal.conclusion }
			.filterNot { it.leftFml == goal.conclusion }
		APPLY_NOT -> goal.assumptions
			.filterIsInstance<NOT>()
			.filter { goal.conclusion == FALSE }
		CASES_AND -> goal.assumptions
			.filterIsInstance<AND>()
			.filterNot { it.leftFml in goal.assumptions && it.rightFml in goal.assumptions }
		CASES_OR -> goal.assumptions
			.filterIsInstance<OR>()
			.filterNot { it.leftFml in goal.assumptions || it.rightFml in goal.assumptions }
		CASES_IFF -> goal.assumptions
			.filterIsInstance<IFF>()
			.filterNot { it.leftFml in goal.assumptions && it.rightFml in goal.assumptions }
		CASES_EXISTS -> goal.assumptions
			.filterIsInstance<EXISTS>()
			.filterNot { assumption -> goal.freeVars.any { fixedVar -> assumption.substitute(fixedVar) in goal.assumptions } }
		REVERT, CLEAR -> goal.assumptions
		HAVE_IMPLIES -> goal.assumptions
			.filterIsInstance<IMPLIES>()
			.filter { it.leftFml in goal.assumptions }
			.filterNot { it.rightFml in goal.assumptions }
		HAVE_IMPLIES_WITHOUT_LEFT -> goal.assumptions
			.asSequence()
			.filterIsInstance<IMPLIES>()
			.filterNot { it.leftFml in goal.assumptions }
			.filterNot { it.leftFml == goal.conclusion }
			.filterNot { it.rightFml in goal.assumptions }
			.filterNot { it.rightFml == goal.conclusion }
			.toList()
		HAVE_NOT -> if (FALSE !in goal.assumptions) {
			goal.assumptions
				.filterIsInstance<NOT>()
				.filter { it.operandFml in goal.assumptions }
		} else { emptyList() }
		HAVE_WITHOUT_FIXED_VARS -> if (goal.freeVars.isEmpty()) {
			goal.assumptions
				.filterIsInstance<ALL>()
		} else { emptyList() }
	}
}

// Tactic with one variable.
enum class Tactic1WithVar: ITactic {
	REVERT, USE;
	override fun toString(): String = when(this) {
		REVERT 	-> "revert"
		USE 	-> "use"
	}
	data class ApplyData(val tactic1WithVar: Tactic1WithVar, val fixedVar: Var): IApplyData
	override fun canApply(goal: Goal): Boolean = when(this) {
		REVERT 	-> availableFixedVars(goal).isNotEmpty()
		USE 	-> goal.conclusion is EXISTS && availableFixedVars(goal).isNotEmpty()
	}
	fun applyTactic(goals: Goals, fixedVar: Var): Goals {
		val goal = goals[0]
		if (!(this.canApply(goal))) { throw IllegalTacticException() }
		return when(this) {
			REVERT -> {
				val conclusion = goal.conclusion
				val newConclusion = if (fixedVar in conclusion.bddVars) {
					val newVar = fixedVar.getFreshVar(conclusion.bddVars)
					val replacedConclusion = conclusion.replace(fixedVar, newVar)
					ALL(newVar, replacedConclusion)
				} else {
					ALL(fixedVar, conclusion)
				}
				val newGoal = goal.copy(
					conclusion = newConclusion
				)
				goals.replace(newGoal)
			}
			USE -> {
				val conclusion = goal.conclusion as EXISTS
				val newGoal = goal.copy(
					conclusion = conclusion.substitute(fixedVar)
				)
				goals.replace(newGoal)
			}
		}
	}
	// TODO: 2021/11/21 change to set.
	fun availableFixedVars(goal: Goal): Set<Var> = when(this) {
		REVERT -> {
			val fixedVarsInAssumptions = goal.assumptions.map { it.freeVars }.flatten()
			goal.freeVars.filterNot { it in fixedVarsInAssumptions }.toSet()
		}
		USE -> goal.freeVars
	}
}

// Tactic with one formula and one variable.
enum class Tactic2WithVar: ITactic {
	HAVE;
	override fun toString(): String = "have"
	data class ApplyData(val tactic2WithVar: Tactic2WithVar, val assumption: Formula, val fixedVar: Var): IApplyData
	override fun canApply(goal: Goal): Boolean = availablePairsOfAssumptionAndFixedVar(goal).isNotEmpty()
	fun applyTactic(goals: Goals, assumption: Formula, fixedVar: Var): Goals {
		val goal = goals[0]
		if (!(this.canApply(goal))) { throw IllegalTacticException() }
		assumption as ALL
		val newAssumption = assumption.substitute(fixedVar)
		val newGoal = goal.copy(
			assumptions = goal.assumptions.addBelow(assumption, newAssumption)
		)
		return goals.replace(newGoal)
	}
	fun availablePairsOfAssumptionAndFixedVar(goal: Goal): List<Pair<Formula, Var>> {
		val result = mutableListOf<Pair<Formula, Var>>()
		val possibleAssumptions = goal.assumptions.filterIsInstance<ALL>()
		for (assumption in possibleAssumptions) {
			for (fixedVar in goal.freeVars) {
				if (assumption.substitute(fixedVar) !in goal.assumptions) {
					result.add(Pair(assumption, fixedVar))
				}
			}
		}
		return result
	}
}
