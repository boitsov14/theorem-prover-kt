package tactic

import formula.*
import goal.*

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
enum class Tactic0(private val id: String): ITactic {
	ASSUMPTION("assumption"),
	INTRO_IMPLIES("intro"),
	INTRO_NOT("intro"),
	INTRO_ALL("intro"),
	SPLIT_AND("split"),
	SPLIT_IFF("split"),
	LEFT("left"),
	RIGHT("right"),
	EXFALSO("exfalso"),
	BY_CONTRA("by_contra"),
	USE_WITHOUT_FIXED_VARS("use");
	override fun toString(): String = id
	data class ApplyData(val tactic0: Tactic0): IApplyData
	override fun canApply(goal: Goal): Boolean {
		val conclusion = goal.conclusion
		return when(this) {
			ASSUMPTION		-> conclusion in goal.assumptions
			INTRO_IMPLIES 	-> conclusion is Formula.IMPLIES
			INTRO_NOT 		-> conclusion is Formula.NOT
			INTRO_ALL 		-> conclusion is Formula.ALL
			SPLIT_AND 		-> conclusion is Formula.AND
			SPLIT_IFF 		-> conclusion is Formula.IFF
			LEFT, RIGHT		-> conclusion is Formula.OR
			EXFALSO			-> conclusion != Formula.FALSE
			BY_CONTRA		-> conclusion != Formula.FALSE && Formula.NOT(conclusion) !in goal.assumptions
			USE_WITHOUT_FIXED_VARS -> conclusion is Formula.EXISTS && goal.fixedVars.isEmpty()
		}
	}
	fun applyTactic(goals: Goals): Goals {
		val goal = goals[0]
		if (!(this.canApply(goal))) { throw IllegalTacticException() }
		val conclusion = goal.conclusion
		when(this) {
			ASSUMPTION -> return goals.replace()
			INTRO_IMPLIES -> {
				conclusion as Formula.IMPLIES
				val newGoal = goal.copy(
					assumptions = goal.assumptions.addIfDistinct(conclusion.leftFml),
					conclusion = conclusion.rightFml
				)
				return goals.replace(newGoal)
			}
			INTRO_NOT -> {
				conclusion as Formula.NOT
				val newGoal = goal.copy(
					assumptions = goal.assumptions.addIfDistinct(conclusion.operandFml),
					conclusion = Formula.FALSE
				)
				return goals.replace(newGoal)
			}
			INTRO_ALL -> {
				conclusion as Formula.ALL
				val newVar = conclusion.bddVar.getUniqueVar(goal.fixedVars.toSet())
				val newGoal = goal.copy(
					fixedVars = goal.fixedVars + newVar,
					conclusion = conclusion.substitute(newVar)
				)
				return goals.replace(newGoal)
			}
			SPLIT_AND -> {
				conclusion as Formula.AND
				val left    = goal.copy(
					conclusion = conclusion.leftFml
				)
				val right   = goal.copy(
					conclusion = conclusion.rightFml
				)
				return goals.replace(left, right)
			}
			SPLIT_IFF -> {
				conclusion as Formula.IFF
				val toRight = goal.copy(
					conclusion = Formula.IMPLIES(conclusion.leftFml, conclusion.rightFml)
				)
				val toLeft  = goal.copy(
					conclusion = Formula.IMPLIES(conclusion.rightFml, conclusion.leftFml)
				)
				return goals.replace(toRight, toLeft)
			}
			LEFT -> {
				conclusion as Formula.OR
				val newGoal = goal.copy(
					conclusion = conclusion.leftFml
				)
				return goals.replace(newGoal)
			}
			RIGHT -> {
				conclusion as Formula.OR
				val newGoal = goal.copy(
					conclusion = conclusion.rightFml
				)
				return goals.replace(newGoal)
			}
			EXFALSO -> {
				val newGoal = goal.copy(
					conclusion = Formula.FALSE
				)
				return goals.replace(newGoal)
			}
			BY_CONTRA -> {
				val newGoal = goal.copy(
					assumptions = goal.assumptions + Formula.NOT(conclusion),
					conclusion = Formula.FALSE
				)
				return goals.replace(newGoal)
			}
			USE_WITHOUT_FIXED_VARS -> {
				conclusion as Formula.EXISTS
				val newGoal = goal.copy(
					fixedVars = listOf(conclusion.bddVar),
					conclusion = conclusion.operandFml
				)
				return goals.replace(newGoal)
			}
		}
	}
}

// Tactic with one formula.
enum class Tactic1WithFml(private val id: String): ITactic {
	APPLY_IMPLIES("apply"),
	APPLY_NOT("apply"),
	CASES_AND("cases"),
	CASES_OR("cases"),
	CASES_IFF("cases"),
	CASES_EXISTS("cases"),
	REVERT("revert"),
	CLEAR("clear"),
	HAVE_IMPLIES("have"),
	HAVE_IMPLIES_WITHOUT_LEFT("have"),
	HAVE_NOT("have"),
	HAVE_WITHOUT_FIXED_VARS("have");
	override fun toString(): String = id
	data class ApplyData(val tactic1WithFml: Tactic1WithFml, val assumption: Formula): IApplyData
	override fun canApply(goal: Goal): Boolean = availableAssumptions(goal).isNotEmpty()
	fun applyTactic(goals: Goals, assumption: Formula): Goals {
		val goal = goals[0]
		if (!(this.canApply(goal))) { throw IllegalTacticException() }
		when(this) {
			APPLY_IMPLIES -> {
				assumption as Formula.IMPLIES
				val newGoal = goal.copy(
					conclusion = assumption.leftFml
				)
				return goals.replace(newGoal)
			}
			APPLY_NOT -> {
				assumption as Formula.NOT
				val newGoal = goal.copy(
					conclusion = assumption.operandFml
				)
				return goals.replace(newGoal)
			}
			CASES_AND -> {
				assumption as Formula.AND
				val newGoal = goal.copy(
					assumptions = goal.assumptions.replaceIfDistinct(assumption, assumption.leftFml, assumption.rightFml)
				)
				return goals.replace(newGoal)
			}
			CASES_OR -> {
				assumption as Formula.OR
				val leftGoal	= goal.copy(
					assumptions = goal.assumptions.replace(assumption, assumption.leftFml)
				)
				val rightGoal	= goal.copy(
					assumptions = goal.assumptions.replace(assumption, assumption.rightFml)
				)
				return goals.replace(leftGoal, rightGoal)
			}
			CASES_IFF -> {
				assumption as Formula.IFF
				val toRight = Formula.IMPLIES(assumption.leftFml, assumption.rightFml)
				val toLeft  = Formula.IMPLIES(assumption.rightFml, assumption.leftFml)
				val newGoal = goal.copy(
					assumptions = goal.assumptions.replaceIfDistinct(assumption, toRight, toLeft)
				)
				return goals.replace(newGoal)
			}
			CASES_EXISTS -> {
				assumption as Formula.EXISTS
				val newVar = assumption.bddVar.getUniqueVar(goal.fixedVars.toSet())
				val newAssumption = assumption.substitute(newVar)
				val newGoal = goal.copy(
					fixedVars = goal.fixedVars + newVar,
					assumptions = goal.assumptions.replace(assumption, newAssumption)
				)
				return goals.replace(newGoal)
			}
			REVERT -> {
				val newGoal = goal.copy(
					assumptions = goal.assumptions.minus(assumption),
					conclusion = Formula.IMPLIES(assumption, goal.conclusion)
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
				assumption as Formula.IMPLIES
				val newGoal = goal.copy(
					assumptions = goal.assumptions.replace(assumption, assumption.rightFml)
				)
				return goals.replace(newGoal)
			}
			HAVE_IMPLIES_WITHOUT_LEFT -> {
				assumption as Formula.IMPLIES
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
					assumptions = goal.assumptions + Formula.FALSE
				)
				return goals.replace(newGoal)
			}
			HAVE_WITHOUT_FIXED_VARS -> {
				assumption as Formula.ALL
				val newAssumption = assumption.operandFml
				val newGoal = goal.copy(
					fixedVars = listOf(assumption.bddVar),
					assumptions = goal.assumptions.addBelow(assumption, newAssumption)
				)
				return goals.replace(newGoal)
			}
		}
	}
	// TODO: 2021/11/21 change to set.
	fun availableAssumptions(goal: Goal): List<Formula> = when(this) {
		APPLY_IMPLIES -> goal.assumptions
			.filterIsInstance<Formula.IMPLIES>()
			.filter { it.rightFml  == goal.conclusion }
			.filterNot { it.leftFml == goal.conclusion }
		APPLY_NOT -> goal.assumptions
			.filterIsInstance<Formula.NOT>()
			.filter { goal.conclusion == Formula.FALSE }
		CASES_AND -> goal.assumptions
			.filterIsInstance<Formula.AND>()
			.filterNot { it.leftFml in goal.assumptions && it.rightFml in goal.assumptions }
		CASES_OR -> goal.assumptions
			.filterIsInstance<Formula.OR>()
			.filterNot { it.leftFml in goal.assumptions || it.rightFml in goal.assumptions }
		CASES_IFF -> goal.assumptions
			.filterIsInstance<Formula.IFF>()
			.filterNot { it.leftFml in goal.assumptions && it.rightFml in goal.assumptions }
		CASES_EXISTS -> goal.assumptions
			.filterIsInstance<Formula.EXISTS>()
			.filterNot { assumption -> goal.fixedVars.any { fixedVar -> assumption.substitute(fixedVar) in goal.assumptions } }
		REVERT, CLEAR -> goal.assumptions
		HAVE_IMPLIES -> goal.assumptions
			.filterIsInstance<Formula.IMPLIES>()
			.filter { it.leftFml in goal.assumptions }
			.filterNot { it.rightFml in goal.assumptions }
		HAVE_IMPLIES_WITHOUT_LEFT -> goal.assumptions
			.asSequence()
			.filterIsInstance<Formula.IMPLIES>()
			.filterNot { it.leftFml in goal.assumptions }
			.filterNot { it.leftFml == goal.conclusion }
			.filterNot { it.rightFml in goal.assumptions }
			.filterNot { it.rightFml == goal.conclusion }
			.toList()
		HAVE_NOT -> if (Formula.FALSE !in goal.assumptions) {
			goal.assumptions
				.filterIsInstance<Formula.NOT>()
				.filter { it.operandFml in goal.assumptions }
		} else { emptyList() }
		HAVE_WITHOUT_FIXED_VARS -> if (goal.fixedVars.isEmpty()) {
			goal.assumptions
				.filterIsInstance<Formula.ALL>()
		} else { emptyList() }
	}
}

// Tactic with one variable.
enum class Tactic1WithVar(private val id: String): ITactic {
	REVERT("revert"),
	USE("use");
	override fun toString(): String = id
	data class ApplyData(val tactic1WithVar: Tactic1WithVar, val fixedVar: Var): IApplyData
	override fun canApply(goal: Goal): Boolean = when(this) {
		REVERT -> availableFixedVars(goal).isNotEmpty()
		USE -> goal.conclusion is Formula.EXISTS && availableFixedVars(goal).isNotEmpty()
	}
	fun applyTactic(goals: Goals, fixedVar: Var): Goals {
		val goal = goals[0]
		if (!(this.canApply(goal))) { throw IllegalTacticException() }
		return when(this) {
			REVERT -> {
				val conclusion = goal.conclusion
				val newConclusion = if (fixedVar in conclusion.bddVars) {
					val newVar = fixedVar.getUniqueVar(conclusion.bddVars)
					val replacedConclusion = conclusion.replace(fixedVar, newVar)
					Formula.ALL(newVar, replacedConclusion)
				} else {
					Formula.ALL(fixedVar, conclusion)
				}
				val newGoal = goal.copy(
					fixedVars = goal.fixedVars.minus(fixedVar),
					conclusion = newConclusion
				)
				goals.replace(newGoal)
			}
			USE -> {
				val conclusion = goal.conclusion as Formula.EXISTS
				val newGoal = goal.copy(
					conclusion = conclusion.substitute(fixedVar)
				)
				goals.replace(newGoal)
			}
		}
	}
	// TODO: 2021/11/21 change to set.
	fun availableFixedVars(goal: Goal): List<Var> = when(this) {
		REVERT -> {
			val fixedVarsInAssumptions = goal.assumptions.map { it.freeVars }.flatten()
			goal.fixedVars.filterNot { it in fixedVarsInAssumptions }
		}
		USE -> goal.fixedVars
	}
}

// Tactic with one formula and one variable.
enum class Tactic2WithVar(private val id: String): ITactic {
	HAVE("have");
	override fun toString(): String = id
	data class ApplyData(val tactic2WithVar: Tactic2WithVar, val assumption: Formula, val fixedVar: Var): IApplyData
	override fun canApply(goal: Goal): Boolean = availablePairsOfAssumptionAndFixedVar(goal).isNotEmpty()
	fun applyTactic(goals: Goals, assumption: Formula, fixedVar: Var): Goals {
		val goal = goals[0]
		if (!(this.canApply(goal))) { throw IllegalTacticException() }
		assumption as Formula.ALL
		val newAssumption = assumption.substitute(fixedVar)
		val newGoal = goal.copy(
			assumptions = goal.assumptions.addBelow(assumption, newAssumption)
		)
		return goals.replace(newGoal)
	}
	fun availablePairsOfAssumptionAndFixedVar(goal: Goal): List<Pair<Formula, Var>> {
		val result = mutableListOf<Pair<Formula, Var>>()
		val possibleAssumptions = goal.assumptions.filterIsInstance<Formula.ALL>()
		for (assumption in possibleAssumptions) {
			for (fixedVar in goal.fixedVars) {
				if (assumption.substitute(fixedVar) !in goal.assumptions) {
					result.add(Pair(assumption, fixedVar))
				}
			}
		}
		return result
	}
}