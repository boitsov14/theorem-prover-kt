package tacticGame

import core.*
import core.Formula.*
import core.Term.*

sealed interface ITactic {
	fun canApply(goal: Goal): Boolean
}

val allTactics: Set<ITactic> = Tactic0.values().toSet() + Tactic1WithFml.values() + Tactic1WithVar.values() + Tactic2WithVar.values()

fun Goal.applicableTactics() = allTactics.filter { it.canApply(this) }

sealed interface IApplyData{
	val tactic: ITactic
}

typealias History = List<IApplyData>

fun IApplyData.applyTactic(goals: Goals): Goals = when(this) {
	is Tactic0.ApplyData 		-> this.tactic.applyTactic(goals)
	is Tactic1WithFml.ApplyData -> this.tactic.applyTactic(goals, this.assumption)
	is Tactic1WithVar.ApplyData -> this.tactic.applyTactic(goals, this.freeVar)
	is Tactic2WithVar.ApplyData -> this.tactic.applyTactic(goals, this.assumption, this.freeVar)
}

fun History.applyTactics(firstGoals: Goals): Goals = this.fold(firstGoals){ currentGoals, applyData -> applyData.applyTactic(currentGoals)}

class IllegalTacticException: Exception()

// Tactic with arity 0.
enum class Tactic0: ITactic {
	ASSUMPTION, INTRO_IMPLIES, INTRO_NOT, INTRO_ALL, SPLIT_AND, SPLIT_IFF, LEFT, RIGHT, EXFALSO, BY_CONTRA, USE_WITHOUT_FREE_VARS;
	override fun toString(): String = when(this) {
		ASSUMPTION 	-> "assumption"
		INTRO_IMPLIES, INTRO_NOT, INTRO_ALL -> "intro"
		SPLIT_AND, SPLIT_IFF -> "split"
		LEFT -> "left"
		RIGHT -> "right"
		EXFALSO -> "exfalso"
		BY_CONTRA -> "by_contra"
		USE_WITHOUT_FREE_VARS -> "use"
	}
	data class ApplyData(override val tactic: Tactic0): IApplyData
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
			USE_WITHOUT_FREE_VARS -> conclusion is EXISTS && goal.freeVars.isEmpty()
		}
	}
	fun applyTactic(goals: Goals): Goals {
		val goal = goals[0]
		if (!(this.canApply(goal))) { throw IllegalTacticException() }
		val conclusion = goal.conclusion
		when(this) {
			ASSUMPTION -> return goals.replaceFirst()
			INTRO_IMPLIES -> {
				conclusion as IMPLIES
				val newGoal = goal.copy(
					assumptions = goal.assumptions + conclusion.leftFml,
					conclusion = conclusion.rightFml
				)
				return goals.replaceFirst(newGoal)
			}
			INTRO_NOT -> {
				conclusion as NOT
				val newGoal = goal.copy(
					assumptions = goal.assumptions + conclusion.operandFml,
					conclusion = FALSE
				)
				return goals.replaceFirst(newGoal)
			}
			INTRO_ALL -> {
				conclusion as ALL
				val freshVar = conclusion.bddVar.getFreshVar(goal.freeVars)
				val newGoal = goal.copy(
					conclusion = conclusion.instantiate(freshVar)
				)
				return goals.replaceFirst(newGoal)
			}
			SPLIT_AND -> {
				conclusion as AND
				val left    = goal.copy(
					conclusion = conclusion.leftFml
				)
				val right   = goal.copy(
					conclusion = conclusion.rightFml
				)
				return goals.replaceFirst(left, right)
			}
			SPLIT_IFF -> {
				conclusion as IFF
				val toRight = goal.copy(
					conclusion = IMPLIES(conclusion.leftFml, conclusion.rightFml)
				)
				val toLeft  = goal.copy(
					conclusion = IMPLIES(conclusion.rightFml, conclusion.leftFml)
				)
				return goals.replaceFirst(toRight, toLeft)
			}
			LEFT -> {
				conclusion as OR
				val newGoal = goal.copy(
					conclusion = conclusion.leftFml
				)
				return goals.replaceFirst(newGoal)
			}
			RIGHT -> {
				conclusion as OR
				val newGoal = goal.copy(
					conclusion = conclusion.rightFml
				)
				return goals.replaceFirst(newGoal)
			}
			EXFALSO -> {
				val newGoal = goal.copy(
					conclusion = FALSE
				)
				return goals.replaceFirst(newGoal)
			}
			BY_CONTRA -> {
				val newGoal = goal.copy(
					assumptions = goal.assumptions + NOT(conclusion),
					conclusion = FALSE
				)
				return goals.replaceFirst(newGoal)
			}
			USE_WITHOUT_FREE_VARS -> {
				conclusion as EXISTS
				val newGoal = goal.copy(
					conclusion = conclusion.operandFml
				)
				return goals.replaceFirst(newGoal)
			}
		}
	}
}

// Tactic with one formula.
enum class Tactic1WithFml: ITactic {
	APPLY_IMPLIES, APPLY_NOT, CASES_AND, CASES_OR, CASES_IFF, CASES_EXISTS, REVERT, CLEAR, HAVE_IMPLIES, HAVE_IMPLIES_WITHOUT_LEFT, HAVE_NOT, HAVE_WITHOUT_FREE_VARS;
	override fun toString(): String = when(this) {
		APPLY_IMPLIES, APPLY_NOT -> "apply"
		CASES_AND, CASES_OR, CASES_IFF, CASES_EXISTS -> "cases"
		REVERT -> "revert"
		CLEAR -> "clear"
		HAVE_IMPLIES, HAVE_IMPLIES_WITHOUT_LEFT, HAVE_NOT, HAVE_WITHOUT_FREE_VARS -> "have"
	}
	data class ApplyData(override val tactic: Tactic1WithFml, val assumption: Formula): IApplyData
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
				return goals.replaceFirst(newGoal)
			}
			APPLY_NOT -> {
				assumption as NOT
				val newGoal = goal.copy(
					conclusion = assumption.operandFml
				)
				return goals.replaceFirst(newGoal)
			}
			CASES_AND -> {
				assumption as AND
				val newGoal = goal.copy(
					assumptions = goal.assumptions.minus(assumption) + assumption.leftFml + assumption.rightFml
				)
				return goals.replaceFirst(newGoal)
			}
			CASES_OR -> {
				assumption as OR
				val leftGoal	= goal.copy(
					assumptions = goal.assumptions.minus(assumption) + assumption.leftFml
				)
				val rightGoal	= goal.copy(
					assumptions = goal.assumptions.minus(assumption) + assumption.rightFml
				)
				return goals.replaceFirst(leftGoal, rightGoal)
			}
			CASES_IFF -> {
				assumption as IFF
				val toRight = IMPLIES(assumption.leftFml, assumption.rightFml)
				val toLeft  = IMPLIES(assumption.rightFml, assumption.leftFml)
				val newGoal = goal.copy(
					assumptions = goal.assumptions.minus(assumption) + toRight + toLeft
				)
				return goals.replaceFirst(newGoal)
			}
			CASES_EXISTS -> {
				assumption as EXISTS
				val freshVar = assumption.bddVar.getFreshVar(goal.freeVars)
				val newAssumption = assumption.instantiate(freshVar)
				val newGoal = goal.copy(
					assumptions = goal.assumptions.minus(assumption) + newAssumption
				)
				return goals.replaceFirst(newGoal)
			}
			REVERT -> {
				val newGoal = goal.copy(
					assumptions = goal.assumptions.minus(assumption),
					conclusion = IMPLIES(assumption, goal.conclusion)
				)
				return goals.replaceFirst(newGoal)
			}
			CLEAR -> {
				val newGoal = goal.copy(
					assumptions = goal.assumptions.minus(assumption)
				)
				return goals.replaceFirst(newGoal)
			}
			HAVE_IMPLIES -> {
				assumption as IMPLIES
				val newGoal = goal.copy(
					assumptions = goal.assumptions.minus(assumption) + assumption.rightFml
				)
				return goals.replaceFirst(newGoal)
			}
			HAVE_IMPLIES_WITHOUT_LEFT -> {
				assumption as IMPLIES
				val newGoal1 = goal.copy(
					assumptions = goal.assumptions,
					conclusion = assumption.leftFml
				)
				val newGoal2 = goal.copy(
					assumptions = goal.assumptions.minus(assumption) + assumption.rightFml
				)
				return goals.replaceFirst(newGoal1, newGoal2)
			}
			HAVE_NOT -> {
				val newGoal = goal.copy(
					assumptions = goal.assumptions + FALSE
				)
				return goals.replaceFirst(newGoal)
			}
			HAVE_WITHOUT_FREE_VARS -> {
				assumption as ALL
				val newAssumption = assumption.operandFml
				val newGoal = goal.copy(
					assumptions = goal.assumptions + newAssumption
				)
				return goals.replaceFirst(newGoal)
			}
		}
	}
	fun availableAssumptions(goal: Goal): Set<Formula> = when(this) {
		APPLY_IMPLIES -> goal.assumptions
			.filterIsInstance<IMPLIES>()
			.filter { it.rightFml  == goal.conclusion }
			.filterNot { it.leftFml == goal.conclusion }
			.toSet()
		APPLY_NOT -> goal.assumptions
			.filterIsInstance<NOT>()
			.filter { goal.conclusion == FALSE }
			.toSet()
		CASES_AND -> goal.assumptions
			.filterIsInstance<AND>()
			.filterNot { it.leftFml in goal.assumptions && it.rightFml in goal.assumptions }
			.toSet()
		CASES_OR -> goal.assumptions
			.filterIsInstance<OR>()
			.filterNot { it.leftFml in goal.assumptions || it.rightFml in goal.assumptions }
			.toSet()
		CASES_IFF -> goal.assumptions
			.filterIsInstance<IFF>()
			.filterNot { it.leftFml in goal.assumptions && it.rightFml in goal.assumptions }
			.toSet()
		CASES_EXISTS -> goal.assumptions
			.filterIsInstance<EXISTS>()
			.filterNot { assumption -> goal.freeVars.any { freeVar -> assumption.instantiate(freeVar) in goal.assumptions } }
			.toSet()
		REVERT, CLEAR -> goal.assumptions
		HAVE_IMPLIES -> goal.assumptions
			.filterIsInstance<IMPLIES>()
			.filter { it.leftFml in goal.assumptions }
			.filterNot { it.rightFml in goal.assumptions }
			.toSet()
		HAVE_IMPLIES_WITHOUT_LEFT -> goal.assumptions
			.asSequence()
			.filterIsInstance<IMPLIES>()
			.filterNot { it.leftFml in goal.assumptions }
			.filterNot { it.leftFml == goal.conclusion }
			.filterNot { it.rightFml in goal.assumptions }
			.filterNot { it.rightFml == goal.conclusion }
			.toSet()
		HAVE_NOT -> if (FALSE !in goal.assumptions) {
			goal.assumptions
				.filterIsInstance<NOT>()
				.filter { it.operandFml in goal.assumptions }
				.toSet()
		} else { emptySet() }
		HAVE_WITHOUT_FREE_VARS -> if (goal.freeVars.isEmpty()) {
			goal.assumptions
				.filterIsInstance<ALL>()
				.toSet()
		} else { emptySet() }
	}
}

// Tactic with one variable.
enum class Tactic1WithVar: ITactic {
	REVERT, USE;
	override fun toString(): String = when(this) {
		REVERT 	-> "revert"
		USE 	-> "use"
	}
	data class ApplyData(override val tactic: Tactic1WithVar, val freeVar: Var): IApplyData
	override fun canApply(goal: Goal): Boolean = when(this) {
		REVERT 	-> availableFreeVars(goal).isNotEmpty()
		USE 	-> goal.conclusion is EXISTS && availableFreeVars(goal).isNotEmpty()
	}
	fun applyTactic(goals: Goals, freeVar: Var): Goals {
		val goal = goals[0]
		if (!(this.canApply(goal))) { throw IllegalTacticException() }
		return when(this) {
			REVERT -> {
				val conclusion = goal.conclusion
				val newConclusion = if (freeVar in conclusion.bddVars) {
					val freshVar = freeVar.getFreshVar(conclusion.bddVars)
					val replacedConclusion = conclusion.replace(freeVar, freshVar)
					ALL(freshVar, replacedConclusion)
					// TODO: 2022/01/17 countの修正？
				} else {
					ALL(freeVar, conclusion)
				}
				val newGoal = goal.copy(
					conclusion = newConclusion
				)
				goals.replaceFirst(newGoal)
			}
			USE -> {
				val conclusion = goal.conclusion as EXISTS
				val newGoal = goal.copy(
					conclusion = conclusion.instantiate(freeVar)
				)
				goals.replaceFirst(newGoal)
			}
		}
	}
	fun availableFreeVars(goal: Goal): Set<Var> = when(this) {
		REVERT -> {
			val freeVarsInAssumptions = goal.assumptions.map { it.freeVars }.flatten()
			goal.freeVars.filterNot { it in freeVarsInAssumptions }.toSet()
		}
		USE -> goal.freeVars
	}
}

// Tactic with one formula and one variable.
enum class Tactic2WithVar: ITactic {
	HAVE;
	override fun toString(): String = "have"
	data class ApplyData(override val tactic: Tactic2WithVar, val assumption: Formula, val freeVar: Var): IApplyData
	override fun canApply(goal: Goal): Boolean = availableAssumptionAndFreeVars(goal).isNotEmpty()
	fun applyTactic(goals: Goals, assumption: Formula, freeVar: Var): Goals {
		val goal = goals[0]
		if (!(this.canApply(goal))) { throw IllegalTacticException() }
		assumption as ALL
		val newAssumption = assumption.instantiate(freeVar)
		val newGoal = goal.copy(
			assumptions = goal.assumptions + newAssumption
		)
		return goals.replaceFirst(newGoal)
	}
	fun availableAssumptionAndFreeVars(goal: Goal): Map<Formula, Set<Var>> {
		val result = mutableMapOf<Formula, Set<Var>>()
		val availableAssumptions = goal.assumptions.filterIsInstance<ALL>()
		for (assumption in availableAssumptions) {
			val availableFreeVars = goal.freeVars.filter { assumption.instantiate(it) !in goal.assumptions }.toSet()
			if (availableFreeVars.isNotEmpty()) {
				result[assumption] = availableFreeVars
			}
		}
		return result
	}
}
