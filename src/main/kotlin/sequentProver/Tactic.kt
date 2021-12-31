package sequentProver

import core.*

sealed interface ITactic {
	fun canApply(sequent: Sequent): Boolean
}

val allTactics: List<ITactic> = BasicTactic.values().toList()
// TODO: 2021/10/28 change to set.

fun Sequent.applicableTactics() = allTactics.filter { it.canApply(this) }

sealed interface IApplyData

typealias History = List<IApplyData>

fun IApplyData.applyTactic(sequents: Sequents): Sequents = when(this) {
	is BasicTactic.ApplyData -> this.basicTactic.applyTactic(sequents, this.fml)
}

fun History.applyTactics(firstSequents: Sequents): Sequents = this.fold(firstSequents){ currentGoals, applyData -> applyData.applyTactic(currentGoals)}

class IllegalTacticException: Exception()

// Basic Tactic
enum class BasicTactic: ITactic {
	ASSUMPTION,
	AND_LEFT,
	AND_RIGHT,
	OR_LEFT,
	OR_RIGHT,
	IMPLIES_LEFT,
	IMPLIES_RIGHT,
	NOT_LEFT,
	NOT_RIGHT,
	IFF_LEFT,
	IFF_RIGHT,
	ALL_RIGHT,
	EXISTS_LEFT;
	override fun toString(): String = when(this) {
		ASSUMPTION 		-> "assumption"
		AND_LEFT 		-> "∧L"
		AND_RIGHT 		-> "∧R"
		OR_LEFT 		-> "∨L"
		OR_RIGHT 		-> "∨R"
		IMPLIES_LEFT 	-> "→L"
		IMPLIES_RIGHT 	-> "→R"
		NOT_LEFT 		-> "¬L"
		NOT_RIGHT 		-> "¬R"
		IFF_LEFT 		-> "↔L"
		IFF_RIGHT 		-> "↔R"
		ALL_RIGHT 		-> "∀R"
		EXISTS_LEFT 	-> "∃L"
	}
	data class ApplyData(val basicTactic: BasicTactic, val fml: Formula) : IApplyData
	override fun canApply(sequent: Sequent): Boolean = availableFmls(sequent).isNotEmpty()
	fun availableFmls(sequent: Sequent): List<Formula> {
		val assumptions = sequent.assumptions
		val conclusions = sequent.conclusions
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
				.filterNot { assumption -> sequent.freeVars.any { fixedVar -> assumption.substitute(fixedVar) in assumptions } }
			// TODO: 2021/12/12 関数記号も認めるようになったら修正要
			ALL_RIGHT -> conclusions
				.filterIsInstance<Formula.ALL>()
				.filterNot { conclusion -> sequent.freeVars.any { fixedVar -> conclusion.substitute(fixedVar) in conclusions } }
		}
	}
	fun applyTactic(sequents: Sequents, fml: Formula): Sequents {
		val goal = sequents[0]
		if (!(this.canApply(goal))) { throw IllegalTacticException() }
		val assumptions = goal.assumptions
		val conclusions = goal.conclusions
		return when (this) {
			ASSUMPTION -> sequents.replace()
			AND_LEFT -> {
				fml as Formula.AND
				val newGoal = goal.copy(
					assumptions = assumptions.replaceIfDistinct(fml, fml.leftFml, fml.rightFml)
				)
				sequents.replace(newGoal)
			}
			AND_RIGHT -> {
				fml as Formula.AND
				val leftGoal = goal.copy(
					conclusions = conclusions.replace(fml, fml.leftFml)
				)
				val rightGoal = goal.copy(
					conclusions = conclusions.replace(fml, fml.rightFml)
				)
				return sequents.replace(leftGoal, rightGoal)
			}
			OR_LEFT -> {
				fml as Formula.OR
				val leftGoal = goal.copy(
					assumptions = assumptions.replace(fml, fml.leftFml)
				)
				val rightGoal = goal.copy(
					assumptions = assumptions.replace(fml, fml.rightFml)
				)
				return sequents.replace(leftGoal, rightGoal)
			}
			OR_RIGHT -> {
				fml as Formula.OR
				val newGoal = goal.copy(
					conclusions = conclusions.replaceIfDistinct(fml, fml.leftFml, fml.rightFml)
				)
				sequents.replace(newGoal)
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
				return sequents.replace(newGoal1, newGoal2)
			}
			IMPLIES_RIGHT -> {
				fml as Formula.IMPLIES
				val newGoal = goal.copy(
					assumptions = assumptions.addIfDistinct(fml.leftFml),
					conclusions = conclusions.replaceIfDistinct(fml, fml.rightFml)
				)
				return sequents.replace(newGoal)
			}
			NOT_LEFT -> {
				fml as Formula.NOT
				val newGoal = goal.copy(
					assumptions = assumptions.minus(fml),
					conclusions = conclusions + fml.operandFml
				)
				return sequents.replace(newGoal)
			}
			NOT_RIGHT -> {
				fml as Formula.NOT
				val newGoal = goal.copy(
					assumptions = assumptions + fml.operandFml,
					conclusions = conclusions.minus(fml)
				)
				return sequents.replace(newGoal)
			}
			IFF_LEFT -> {
				fml as Formula.IFF
				val newGoal = goal.copy(
					assumptions = assumptions.replaceIfDistinct(fml, fml.leftFml, fml.rightFml)
				)
				sequents.replace(newGoal)
			}
			IFF_RIGHT -> {
				fml as Formula.IFF
				val leftGoal = goal.copy(
					conclusions = conclusions.replace(fml, fml.leftFml)
				)
				val rightGoal = goal.copy(
					conclusions = conclusions.replace(fml, fml.rightFml)
				)
				return sequents.replace(leftGoal, rightGoal)
			}
			ALL_RIGHT -> {
				fml as Formula.ALL
				val newVar = fml.bddVar.getFreshVar(goal.freeVars.toSet())
				val newConclusion = fml.substitute(newVar)
				val newGoal = goal.copy(
					conclusions = conclusions.replace(fml, newConclusion)
				)
				return sequents.replace(newGoal)
			}
			EXISTS_LEFT -> {
				fml as Formula.EXISTS
				val newVar = fml.bddVar.getFreshVar(goal.freeVars.toSet())
				val newAssumption = fml.substitute(newVar)
				val newGoal = goal.copy(
					assumptions = goal.assumptions.replace(fml, newAssumption)
				)
				return sequents.replace(newGoal)
			}
		}
	}
}
