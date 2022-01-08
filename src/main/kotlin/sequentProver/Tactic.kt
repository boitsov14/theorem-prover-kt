package sequentProver

import core.*
import core.Formula.*

sealed interface ITactic {
	fun canApply(sequent: Sequent): Boolean
}

val allTactics: Set<ITactic> = BasicTactic.values().toSet()

fun Sequent.applicableTactics() = allTactics.filter { it.canApply(this) }

sealed interface IApplyData {
	val tactic: ITactic
}

typealias History = List<IApplyData>

fun IApplyData.applyTactic(sequents: Sequents): Sequents = when(this) {
	is BasicTactic.ApplyData -> this.tactic.applyTactic(sequents, this.fml)
}

fun History.applyTactics(firstSequents: Sequents): Sequents = this.fold(firstSequents){ currentSequents, applyData -> applyData.applyTactic(currentSequents)}

class IllegalTacticException: Exception()

// Basic Tactic
enum class BasicTactic: ITactic {
	ASSUMPTION, AND_LEFT, AND_RIGHT, OR_LEFT, OR_RIGHT, IMPLIES_LEFT, IMPLIES_RIGHT, NOT_LEFT, NOT_RIGHT, IFF_LEFT, IFF_RIGHT, ALL_RIGHT, EXISTS_LEFT;
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
	data class ApplyData(override val tactic: BasicTactic, val fml: Formula) : IApplyData
	override fun canApply(sequent: Sequent): Boolean = availableFmls(sequent).isNotEmpty()
	fun availableFmls(sequent: Sequent): List<Formula> {
		val assumptions = sequent.assumptions
		val conclusions = sequent.conclusions
		return when(this) {
			ASSUMPTION -> conclusions
				.filter { it in assumptions } +
					assumptions.filter { it == FALSE } +
					conclusions.filter { it == TRUE }
			AND_LEFT -> assumptions
				.filterIsInstance<AND>()
				.filterNot { it.leftFml in assumptions && it.rightFml in assumptions }
			AND_RIGHT -> conclusions
				.filterIsInstance<AND>()
				.filterNot { it.leftFml in conclusions || it.rightFml in conclusions }
			OR_LEFT -> assumptions
				.filterIsInstance<OR>()
				.filterNot { it.leftFml in assumptions || it.rightFml in assumptions }
			OR_RIGHT -> conclusions
				.filterIsInstance<OR>()
				.filterNot { it.leftFml in conclusions && it.rightFml in conclusions }
			IMPLIES_LEFT -> assumptions
				.filterIsInstance<IMPLIES>()
				.filterNot { it.leftFml in conclusions }
				.filterNot { it.rightFml in assumptions }
			IMPLIES_RIGHT -> conclusions
				.filterIsInstance<IMPLIES>()
				.filterNot { it.leftFml in assumptions && it.rightFml in conclusions }
			NOT_LEFT -> assumptions
				.filterIsInstance<NOT>()
				.filterNot { it.operandFml in conclusions }
			NOT_RIGHT -> conclusions
				.filterIsInstance<NOT>()
				.filterNot { it.operandFml in assumptions }
			IFF_LEFT -> assumptions
				.filterIsInstance<IFF>()
				.filterNot { it.leftFml in assumptions && it.rightFml in assumptions }
			IFF_RIGHT -> conclusions
				.filterIsInstance<IFF>()
				.filterNot { it.leftFml in assumptions || it.rightFml in conclusions }
			EXISTS_LEFT -> assumptions
				.filterIsInstance<EXISTS>()
				.filterNot { assumption -> sequent.freeVars.any { freeVar -> assumption.substitute(freeVar) in assumptions } }
			// TODO: 2021/12/12 関数記号も認めるようになったら修正要
			ALL_RIGHT -> conclusions
				.filterIsInstance<ALL>()
				.filterNot { conclusion -> sequent.freeVars.any { freeVar -> conclusion.substitute(freeVar) in conclusions } }
		}
	}
	fun applyTactic(sequents: Sequents, fml: Formula): Sequents {
		val sequent = sequents[0]
		if (!(this.canApply(sequent))) { throw IllegalTacticException() }
		val assumptions = sequent.assumptions
		val conclusions = sequent.conclusions
		return when (this) {
			ASSUMPTION -> sequents.replaceFirst()
			AND_LEFT -> {
				fml as AND
				val newSequents = sequent.copy(
					assumptions = assumptions.minus(fml) + fml.leftFml + fml.rightFml
				)
				sequents.replaceFirst(newSequents)
			}
			AND_RIGHT -> {
				fml as AND
				val leftSequent = sequent.copy(
					conclusions = conclusions.minus(fml) + fml.leftFml
				)
				val rightSequent = sequent.copy(
					conclusions = conclusions.minus(fml) + fml.rightFml
				)
				return sequents.replaceFirst(leftSequent, rightSequent)
			}
			OR_LEFT -> {
				fml as OR
				val leftSequent = sequent.copy(
					assumptions = assumptions.minus(fml) + fml.leftFml
				)
				val rightSequent = sequent.copy(
					assumptions = assumptions.minus(fml) + fml.rightFml
				)
				return sequents.replaceFirst(leftSequent, rightSequent)
			}
			OR_RIGHT -> {
				fml as OR
				val newSequents = sequent.copy(
					conclusions = conclusions.minus(fml) + fml.leftFml + fml.rightFml
				)
				sequents.replaceFirst(newSequents)
			}
			IMPLIES_LEFT -> {
				fml as IMPLIES
				val newSequent1 = sequent.copy(
					assumptions = assumptions.minus(fml),
					conclusions = setOf(fml.leftFml) + conclusions
				)
				val newSequent2 = sequent.copy(
					assumptions = assumptions.minus(fml) + fml.rightFml
				)
				return sequents.replaceFirst(newSequent1, newSequent2)
			}
			IMPLIES_RIGHT -> {
				fml as IMPLIES
				val newSequents = sequent.copy(
					assumptions = assumptions + fml.leftFml,
					conclusions = conclusions.minus(fml) + fml.rightFml
				)
				return sequents.replaceFirst(newSequents)
			}
			NOT_LEFT -> {
				fml as NOT
				val newSequents = sequent.copy(
					assumptions = assumptions.minus(fml),
					conclusions = conclusions + fml.operandFml
				)
				return sequents.replaceFirst(newSequents)
			}
			NOT_RIGHT -> {
				fml as NOT
				val newSequents = sequent.copy(
					assumptions = assumptions + fml.operandFml,
					conclusions = conclusions.minus(fml)
				)
				return sequents.replaceFirst(newSequents)
			}
			IFF_LEFT -> {
				fml as IFF
				val toRight = IMPLIES(fml.leftFml, fml.rightFml)
				val toLeft  = IMPLIES(fml.rightFml, fml.leftFml)
				val newSequents = sequent.copy(
					assumptions = sequent.assumptions.minus(fml) + toRight + toLeft
				)
				sequents.replaceFirst(newSequents)
			}
			IFF_RIGHT -> {
				fml as IFF
				val leftSequent = sequent.copy(
					conclusions = conclusions.minus(fml) + fml.leftFml
				)
				val rightSequent = sequent.copy(
					conclusions = conclusions.minus(fml) + fml.rightFml
				)
				return sequents.replaceFirst(leftSequent, rightSequent)
			}
			ALL_RIGHT -> {
				fml as ALL
				val newVar = fml.bddVar.getFreshVar(sequent.freeVars)
				val newConclusion = fml.substitute(newVar)
				val newSequents = sequent.copy(
					conclusions = conclusions.minus(fml) + newConclusion
				)
				return sequents.replaceFirst(newSequents)
			}
			EXISTS_LEFT -> {
				fml as EXISTS
				val newVar = fml.bddVar.getFreshVar(sequent.freeVars)
				val newAssumption = fml.substitute(newVar)
				val newSequents = sequent.copy(
					assumptions = sequent.assumptions.minus(fml) + newAssumption
				)
				return sequents.replaceFirst(newSequents)
			}
		}
	}
}
