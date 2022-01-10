package sequentProver

import core.*
import core.Formula.*

sealed interface ITactic {
	fun canApply(sequent: Sequent): Boolean
}

//val allTactics: Set<ITactic> = BasicTactic.values().toSet()
//fun Sequent.applicableTactics() = allTactics.filter { it.canApply(this) }

sealed interface IApplyData {
	val tactic: ITactic
}

sealed interface IApplyData0 {
	val tactic: ITactic
}

typealias History = List<IApplyData>
typealias History0 = List<IApplyData0>

fun IApplyData.applyTactic(sequents: Sequents): Sequents {
	val sequent = sequents[0]
	return when(this) {
		AXIOM.ApplyData -> sequents.drop(1)
		is UnaryTactic.ApplyData -> this.tactic.applyTactic(sequent, fml).toSequents() + sequents.drop(1)
		is BinaryTactic.ApplyData -> this.tactic.applyTactic(sequent, fml).toList() + sequents.drop(1)
	}
}

fun IApplyData0.applyTactic(sequent: Sequent): Sequent = when(this) {
	AXIOM.ApplyData -> throw IllegalTacticException()
	is UnaryTactic.ApplyData -> this.tactic.applyTactic(sequent, fml)
	is BinaryTactic.ApplyData0 -> if (isFirst) { this.tactic.applyTactic(sequent, fml).first } else { this.tactic.applyTactic(sequent, fml).second }
}

fun History.applyTactics(firstSequents: Sequents): Sequents = this.fold(firstSequents){ sequents, applyData -> applyData.applyTactic(sequents)}
fun History0.applyTactics(firstSequent: Sequent): Sequent = this.fold(firstSequent){ sequent, applyData0 -> applyData0.applyTactic(sequent)}

class IllegalTacticException: Exception()

object AXIOM: ITactic {
	override fun toString(): String = "axiom"
	override fun canApply(sequent: Sequent): Boolean = (sequent.assumptions intersect sequent.conclusions).isNotEmpty() || TRUE in sequent.conclusions || FALSE in sequent.assumptions
	object ApplyData: IApplyData, IApplyData0 { override val tactic = AXIOM }
}

enum class UnaryTactic: ITactic {
	AND_LEFT, OR_RIGHT, IMPLIES_RIGHT, NOT_LEFT, NOT_RIGHT, IFF_LEFT, ALL_RIGHT, EXISTS_LEFT;
	override fun toString(): String = when(this) {
		AND_LEFT -> "∧L"
		OR_RIGHT -> "∨R"
		IMPLIES_RIGHT -> "→R"
		NOT_LEFT -> "¬L"
		NOT_RIGHT -> "¬R"
		IFF_LEFT -> "↔L"
		ALL_RIGHT -> "∀R"
		EXISTS_LEFT -> "∃L"
	}
	data class ApplyData(override val tactic: UnaryTactic, val fml: Formula) : IApplyData, IApplyData0
	override fun canApply(sequent: Sequent): Boolean = availableFmls(sequent).isNotEmpty()
	fun availableFmls(sequent: Sequent): List<Formula> {
		val assumptions = sequent.assumptions
		val conclusions = sequent.conclusions
		return when(this) {
			AND_LEFT -> assumptions
				.filterIsInstance<AND>()
				.filterNot { it.leftFml in assumptions && it.rightFml in assumptions }
			OR_RIGHT -> conclusions
				.filterIsInstance<OR>()
				.filterNot { it.leftFml in conclusions && it.rightFml in conclusions }
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
			EXISTS_LEFT -> assumptions
				.filterIsInstance<EXISTS>()
				.filterNot { assumption -> sequent.freeVars.any { freeVar -> assumption.substitute(freeVar) in assumptions } }
			// TODO: 2021/12/12 関数記号も認めるようになったら修正要
			ALL_RIGHT -> conclusions
				.filterIsInstance<ALL>()
				.filterNot { conclusion -> sequent.freeVars.any { freeVar -> conclusion.substitute(freeVar) in conclusions } }
		}
	}
	fun applyTactic(sequent: Sequent, fml: Formula): Sequent {
		if (!(this.canApply(sequent))) { throw IllegalTacticException() }
		val assumptions = sequent.assumptions
		val conclusions = sequent.conclusions
		return when (this) {
			AND_LEFT -> {
				fml as AND
				sequent.copy(
					assumptions = assumptions.minus(fml) + fml.leftFml + fml.rightFml
				)
			}
			OR_RIGHT -> {
				fml as OR
				sequent.copy(
					conclusions = conclusions.minus(fml) + fml.leftFml + fml.rightFml
				)
			}
			IMPLIES_RIGHT -> {
				fml as IMPLIES
				sequent.copy(
					assumptions = assumptions + fml.leftFml,
					conclusions = conclusions.minus(fml) + fml.rightFml
				)
			}
			NOT_LEFT -> {
				fml as NOT
				sequent.copy(
					assumptions = assumptions.minus(fml),
					conclusions = conclusions + fml.operandFml
				)
			}
			NOT_RIGHT -> {
				fml as NOT
				sequent.copy(
					assumptions = assumptions + fml.operandFml,
					conclusions = conclusions.minus(fml)
				)
			}
			IFF_LEFT -> {
				fml as IFF
				val toRight = IMPLIES(fml.leftFml, fml.rightFml)
				val toLeft  = IMPLIES(fml.rightFml, fml.leftFml)
				sequent.copy(
					assumptions = sequent.assumptions.minus(fml) + toRight + toLeft
				)
			}
			ALL_RIGHT -> {
				fml as ALL
				val newVar = fml.bddVar.getFreshVar(sequent.freeVars)
				val newConclusion = fml.substitute(newVar)
				sequent.copy(
					conclusions = conclusions.minus(fml) + newConclusion
				)
			}
			EXISTS_LEFT -> {
				fml as EXISTS
				val newVar = fml.bddVar.getFreshVar(sequent.freeVars)
				val newAssumption = fml.substitute(newVar)
				sequent.copy(
					assumptions = sequent.assumptions.minus(fml) + newAssumption
				)
			}
		}
	}
}

enum class BinaryTactic: ITactic {
	AND_RIGHT, OR_LEFT, IMPLIES_LEFT, IFF_RIGHT;
	override fun toString(): String = when(this) {
		AND_RIGHT -> "∧R"
		OR_LEFT -> "∨L"
		IMPLIES_LEFT -> "→L"
		IFF_RIGHT -> "↔R"
	}
	data class ApplyData(override val tactic: BinaryTactic, val fml: Formula) : IApplyData
	data class ApplyData0(override val tactic: BinaryTactic, val fml: Formula, val isFirst: Boolean) : IApplyData0
	override fun canApply(sequent: Sequent): Boolean = availableFmls(sequent).isNotEmpty()
	fun availableFmls(sequent: Sequent): List<Formula> {
		val assumptions = sequent.assumptions
		val conclusions = sequent.conclusions
		return when(this) {
			AND_RIGHT -> conclusions
				.filterIsInstance<AND>()
				.filterNot { it.leftFml in conclusions || it.rightFml in conclusions }
			OR_LEFT -> assumptions
				.filterIsInstance<OR>()
				.filterNot { it.leftFml in assumptions || it.rightFml in assumptions }
			IMPLIES_LEFT -> assumptions
				.filterIsInstance<IMPLIES>()
				.filterNot { it.leftFml in conclusions }
				.filterNot { it.rightFml in assumptions }
			IFF_RIGHT -> conclusions
				.filterIsInstance<IFF>()
				.filterNot { it.leftFml in assumptions || it.rightFml in conclusions }
		}
	}
	fun applyTactic(sequent: Sequent, fml: Formula): Pair<Sequent, Sequent> {
		if (!(this.canApply(sequent))) { throw IllegalTacticException() }
		val assumptions = sequent.assumptions
		val conclusions = sequent.conclusions
		return when (this) {
			AND_RIGHT -> {
				fml as AND
				val leftSequent = sequent.copy(
					conclusions = conclusions.minus(fml) + fml.leftFml
				)
				val rightSequent = sequent.copy(
					conclusions = conclusions.minus(fml) + fml.rightFml
				)
				leftSequent to rightSequent
			}
			OR_LEFT -> {
				fml as OR
				val leftSequent = sequent.copy(
					assumptions = assumptions.minus(fml) + fml.leftFml
				)
				val rightSequent = sequent.copy(
					assumptions = assumptions.minus(fml) + fml.rightFml
				)
				leftSequent to rightSequent
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
				newSequent1 to newSequent2
			}
			IFF_RIGHT -> {
				fml as IFF
				val leftSequent = sequent.copy(
					conclusions = conclusions.minus(fml) + fml.leftFml
				)
				val rightSequent = sequent.copy(
					conclusions = conclusions.minus(fml) + fml.rightFml
				)
				leftSequent to rightSequent
			}
		}
	}
}

// TODO: 2022/01/10 delete this class.
// Basic Tactic
private enum class BasicTactic: ITactic {
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
	//data class ApplyData(override val tactic: BasicTactic, val fml: Formula) : IApplyData
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
				val newSequent = sequent.copy(
					assumptions = assumptions.minus(fml) + fml.leftFml + fml.rightFml
				)
				sequents.replaceFirst(newSequent)
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
				val newSequent = sequent.copy(
					conclusions = conclusions.minus(fml) + fml.leftFml + fml.rightFml
				)
				sequents.replaceFirst(newSequent)
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
				val newSequent = sequent.copy(
					assumptions = assumptions + fml.leftFml,
					conclusions = conclusions.minus(fml) + fml.rightFml
				)
				return sequents.replaceFirst(newSequent)
			}
			NOT_LEFT -> {
				fml as NOT
				val newSequent = sequent.copy(
					assumptions = assumptions.minus(fml),
					conclusions = conclusions + fml.operandFml
				)
				return sequents.replaceFirst(newSequent)
			}
			NOT_RIGHT -> {
				fml as NOT
				val newSequent = sequent.copy(
					assumptions = assumptions + fml.operandFml,
					conclusions = conclusions.minus(fml)
				)
				return sequents.replaceFirst(newSequent)
			}
			IFF_LEFT -> {
				fml as IFF
				val toRight = IMPLIES(fml.leftFml, fml.rightFml)
				val toLeft  = IMPLIES(fml.rightFml, fml.leftFml)
				val newSequent = sequent.copy(
					assumptions = sequent.assumptions.minus(fml) + toRight + toLeft
				)
				sequents.replaceFirst(newSequent)
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
				val newSequent = sequent.copy(
					conclusions = conclusions.minus(fml) + newConclusion
				)
				return sequents.replaceFirst(newSequent)
			}
			EXISTS_LEFT -> {
				fml as EXISTS
				val newVar = fml.bddVar.getFreshVar(sequent.freeVars)
				val newAssumption = fml.substitute(newVar)
				val newSequent = sequent.copy(
					assumptions = sequent.assumptions.minus(fml) + newAssumption
				)
				return sequents.replaceFirst(newSequent)
			}
		}
	}
}
