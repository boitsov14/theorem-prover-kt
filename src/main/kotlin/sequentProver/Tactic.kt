package sequentProver

import core.*

sealed interface ITactic {
	fun canApply(goal: Goal): Boolean
}

val allTactics: List<ITactic> = BasicTactic.values().toList()
// TODO: 2021/10/28 change to set.

fun Goal.applicableTactics() = allTactics.filter { it.canApply(this) }

sealed interface IApplyData

typealias History = List<IApplyData>

fun IApplyData.applyTactic(goals: Goals): Goals = when(this) {
	is BasicTactic.ApplyData -> this.basicTactic.applyTactic(goals, this.fml)
}

fun History.applyTactics(firstGoals: Goals): Goals = this.fold(firstGoals){ currentGoals, applyData -> applyData.applyTactic(currentGoals)}

class IllegalTacticException: Exception()

// Basic Tactic
enum class BasicTactic(private val id: String): ITactic {
	ASSUMPTION("assumption"),
	AND_LEFT("∧L"),
	AND_RIGHT("∧R"),
	OR_LEFT("∨L"),
	OR_RIGHT("∨R"),
	IMPLIES_LEFT("→L"),
	IMPLIES_RIGHT("→R"),
	NOT_LEFT("¬L"),
	NOT_RIGHT("¬R"),
	IFF_LEFT("↔L"),
	IFF_RIGHT("↔R"),
	ALL_RIGHT("∀R"),
	EXISTS_LEFT("∃L");
	override fun toString(): String = id
	data class ApplyData(val basicTactic: BasicTactic, val fml: Formula) : IApplyData
	override fun canApply(goal: Goal): Boolean = availableFmls(goal).isNotEmpty()
	fun availableFmls(goal: Goal): List<Formula> {
		val assumptions = goal.assumptions
		val conclusions = goal.conclusions
		return when(this) {
			ASSUMPTION -> conclusions
				.filter { it in assumptions }
			AND_LEFT -> assumptions
				.filterIsInstance<Formula.AND>()
				.filterNot { it.leftFml in assumptions && it.rightFml in assumptions }
			AND_RIGHT -> conclusions
				.filterIsInstance<Formula.AND>()
				.filterNot { it.leftFml in conclusions || it.rightFml in conclusions }
			OR_LEFT -> assumptions
				.filterIsInstance<Formula.OR>()
				.filterNot { it.leftFml in assumptions || it.rightFml in assumptions }
			OR_RIGHT -> conclusions
				.filterIsInstance<Formula.OR>()
				.filterNot { it.leftFml in conclusions && it.rightFml in conclusions }
			IMPLIES_LEFT -> assumptions
				.filterIsInstance<Formula.IMPLIES>()
				.filterNot { it.leftFml in conclusions }
				.filterNot { it.rightFml in assumptions }
			IMPLIES_RIGHT -> conclusions
				.filterIsInstance<Formula.IMPLIES>()
				.filterNot { it.leftFml in assumptions && it.rightFml in conclusions }
			NOT_LEFT -> assumptions
				.filterIsInstance<Formula.NOT>()
				.filterNot { it.operandFml in conclusions }
			NOT_RIGHT -> conclusions
				.filterIsInstance<Formula.NOT>()
				.filterNot { it.operandFml in assumptions }
			IFF_LEFT -> assumptions
				.filterIsInstance<Formula.IFF>()
				.filterNot { it.leftFml in assumptions && it.rightFml in assumptions }
			IFF_RIGHT -> conclusions
				.filterIsInstance<Formula.IFF>()
				.filterNot { it.leftFml in assumptions || it.rightFml in conclusions }
			EXISTS_LEFT -> assumptions
				.filterIsInstance<Formula.EXISTS>()
				.filterNot { assumption -> goal.freeVars.any { fixedVar -> assumption.substitute(fixedVar) in assumptions } }
			// TODO: 2021/12/12 関数記号も認めるようになったら修正要
			ALL_RIGHT -> conclusions
				.filterIsInstance<Formula.ALL>()
				.filterNot { conclusion -> goal.freeVars.any { fixedVar -> conclusion.substitute(fixedVar) in conclusions } }
		}
	}
	fun applyTactic(goals: Goals, fml: Formula): Goals {
		val goal = goals[0]
		if (!(this.canApply(goal))) { throw IllegalTacticException() }
		val assumptions = goal.assumptions
		val conclusions = goal.conclusions
		return when (this) {
			ASSUMPTION -> goals.replace()
			AND_LEFT -> {
				fml as Formula.AND
				val newGoal = goal.copy(
					assumptions = assumptions.replaceIfDistinct(fml, fml.leftFml, fml.rightFml)
				)
				goals.replace(newGoal)
			}
			AND_RIGHT -> {
				fml as Formula.AND
				val leftGoal = goal.copy(
					conclusions = conclusions.replace(fml, fml.leftFml)
				)
				val rightGoal = goal.copy(
					conclusions = conclusions.replace(fml, fml.rightFml)
				)
				return goals.replace(leftGoal, rightGoal)
			}
			OR_LEFT -> {
				fml as Formula.OR
				val leftGoal = goal.copy(
					assumptions = assumptions.replace(fml, fml.leftFml)
				)
				val rightGoal = goal.copy(
					assumptions = assumptions.replace(fml, fml.rightFml)
				)
				return goals.replace(leftGoal, rightGoal)
			}
			OR_RIGHT -> {
				fml as Formula.OR
				val newGoal = goal.copy(
					conclusions = conclusions.replaceIfDistinct(fml, fml.leftFml, fml.rightFml)
				)
				goals.replace(newGoal)
			}
			IMPLIES_LEFT -> {
				fml as Formula.IMPLIES
				val newGoal1 = goal.copy(
					assumptions = assumptions.minus(fml),
					conclusions = conclusions + fml.leftFml
				)
				val newGoal2 = goal.copy(
					assumptions = assumptions.replace(fml, fml.rightFml)
				)
				return goals.replace(newGoal1, newGoal2)
			}
			IMPLIES_RIGHT -> {
				fml as Formula.IMPLIES
				val newGoal = goal.copy(
					assumptions = assumptions.addIfDistinct(fml.leftFml),
					conclusions = conclusions.replaceIfDistinct(fml, fml.rightFml)
				)
				return goals.replace(newGoal)
			}
			NOT_LEFT -> {
				fml as Formula.NOT
				val newGoal = goal.copy(
					assumptions = assumptions.minus(fml),
					conclusions = conclusions + fml.operandFml
				)
				return goals.replace(newGoal)
			}
			NOT_RIGHT -> {
				fml as Formula.NOT
				val newGoal = goal.copy(
					assumptions = assumptions + fml.operandFml,
					conclusions = conclusions.minus(fml)
				)
				return goals.replace(newGoal)
			}
			IFF_LEFT -> {
				fml as Formula.IFF
				val newGoal = goal.copy(
					assumptions = assumptions.replaceIfDistinct(fml, fml.leftFml, fml.rightFml)
				)
				goals.replace(newGoal)
			}
			IFF_RIGHT -> {
				fml as Formula.IFF
				val leftGoal = goal.copy(
					conclusions = conclusions.replace(fml, fml.leftFml)
				)
				val rightGoal = goal.copy(
					conclusions = conclusions.replace(fml, fml.rightFml)
				)
				return goals.replace(leftGoal, rightGoal)
			}
			ALL_RIGHT -> {
				fml as Formula.ALL
				val newVar = fml.bddVar.getUniqueVar(goal.freeVars.toSet())
				val newConclusion = fml.substitute(newVar)
				val newGoal = goal.copy(
					conclusions = conclusions.replace(fml, newConclusion)
				)
				return goals.replace(newGoal)
			}
			EXISTS_LEFT -> {
				fml as Formula.EXISTS
				val newVar = fml.bddVar.getUniqueVar(goal.freeVars.toSet())
				val newAssumption = fml.substitute(newVar)
				val newGoal = goal.copy(
					assumptions = goal.assumptions.replace(fml, newAssumption)
				)
				return goals.replace(newGoal)
			}
		}
	}
}
