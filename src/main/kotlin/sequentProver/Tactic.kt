package sequentProver

import core.*
import core.Formula.*
import core.Term.*

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
		is UnaryTactic.ApplyData -> tactic.applyTactic(sequent, fml).toSequents() + sequents.drop(1)
		is BinaryTactic.ApplyData -> tactic.applyTactic(sequent, fml).toList() + sequents.drop(1)
		is UnificationTermTactic.ApplyData -> tactic.applyTactic(sequent, fml, unificationTermIndex).toSequents() + sequents.drop(1)
		is TermTactic.ApplyData -> tactic.applyTactic(sequent, fml, term).toSequents() + sequents.drop(1)
	}
}

fun IApplyData0.applyTactic(sequent: Sequent): Sequent = when(this) {
	AXIOM.ApplyData -> throw IllegalTacticException()
	is UnaryTactic.ApplyData -> tactic.applyTactic(sequent, fml)
	is BinaryTactic.ApplyData0 -> if (isFirst) { tactic.applyTactic(sequent, fml).first } else { tactic.applyTactic(sequent, fml).second }
	is UnificationTermTactic.ApplyData -> tactic.applyTactic(sequent, fml, unificationTermIndex)
	is TermTactic.ApplyData -> tactic.applyTactic(sequent, fml, term)
}

fun History.applyTactics(firstSequents: Sequents): Sequents = this.fold(firstSequents){ sequents, applyData -> applyData.applyTactic(sequents)}
fun History0.applyTactics(firstSequent: Sequent): Sequent = this.fold(firstSequent){ sequent, applyData0 -> applyData0.applyTactic(sequent)}

fun IApplyData0.toApplyData(): IApplyData = when(this) {
	is BinaryTactic.ApplyData0 -> BinaryTactic.ApplyData(this.tactic, this.fml)
	else -> this as IApplyData
}

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
				//.filterNot { assumption -> sequent.freeVars.any { freeVar -> assumption.substitute(freeVar) in assumptions } }
			// TODO: 2021/12/12 関数記号も認めるようになったら修正要
			// TODO: 2022/01/17 unification使って表現できる？
			ALL_RIGHT -> conclusions
				.filterIsInstance<ALL>()
				//.filterNot { conclusion -> sequent.freeVars.any { freeVar -> conclusion.substitute(freeVar) in conclusions } }
		}
	}
	fun applyTactic(sequent: Sequent, fml: Formula): Sequent {
		if (!(this.canApply(sequent))) { throw IllegalTacticException() }
		return when (this) {
			AND_LEFT -> {
				fml as AND
				sequent.copy(
					assumptions = sequent.assumptions.minus(fml) + fml.leftFml + fml.rightFml
				)
			}
			OR_RIGHT -> {
				fml as OR
				sequent.copy(
					conclusions = sequent.conclusions.minus(fml) + fml.leftFml + fml.rightFml
				)
			}
			IMPLIES_RIGHT -> {
				fml as IMPLIES
				sequent.copy(
					assumptions = sequent.assumptions + fml.leftFml,
					conclusions = sequent.conclusions.minus(fml) + fml.rightFml
				)
			}
			NOT_LEFT -> {
				fml as NOT
				sequent.copy(
					assumptions = sequent.assumptions.minus(fml),
					conclusions = sequent.conclusions + fml.operandFml
				)
			}
			NOT_RIGHT -> {
				fml as NOT
				sequent.copy(
					assumptions = sequent.assumptions + fml.operandFml,
					conclusions = sequent.conclusions.minus(fml)
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
				val freshVar = fml.bddVar.getFreshVar(sequent.freeVars)
				val newConclusion = fml.instantiate(freshVar)
				sequent.copy(
					conclusions = sequent.conclusions.minus(fml) + newConclusion
				)
			}
			EXISTS_LEFT -> {
				fml as EXISTS
				val freshVar = fml.bddVar.getFreshVar(sequent.freeVars)
				val newAssumption = fml.instantiate(freshVar)
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
	fun availableFmls(sequent: Sequent): List<Formula> = when(this) {
		AND_RIGHT -> sequent.conclusions
			.filterIsInstance<AND>()
			.filterNot { it.leftFml in sequent.conclusions || it.rightFml in sequent.conclusions }
		OR_LEFT -> sequent.assumptions
			.filterIsInstance<OR>()
			.filterNot { it.leftFml in sequent.assumptions || it.rightFml in sequent.assumptions }
		IMPLIES_LEFT -> sequent.assumptions
			.filterIsInstance<IMPLIES>()
			.filterNot { it.leftFml in sequent.conclusions }
			.filterNot { it.rightFml in sequent.assumptions }
		IFF_RIGHT -> sequent.conclusions
			.filterIsInstance<IFF>()
			.filterNot { it.leftFml in sequent.assumptions || it.rightFml in sequent.conclusions }
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
					conclusions = conclusions + fml.leftFml
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

enum class UnificationTermTactic: ITactic {
	EXISTS_RIGHT, ALL_LEFT;
	override fun toString(): String = when(this) {
		EXISTS_RIGHT 	-> "∃R"
		ALL_LEFT 		-> "∀L"
	}
	data class ApplyData(override val tactic: UnificationTermTactic, val fml: Formula, val unificationTermIndex: Int) : IApplyData, IApplyData0
	override fun canApply(sequent: Sequent): Boolean = this.availableFmls(sequent).isNotEmpty()
	private fun availableFmls(sequent: Sequent): List<Formula> = when(this) {
		EXISTS_RIGHT 	-> sequent.conclusions.filterIsInstance<EXISTS>()
		ALL_LEFT 		-> sequent.assumptions.filterIsInstance<ALL>()
	}
	fun applyTactic(sequent: Sequent, fml: Formula, unificationTermIndex: Int): Sequent {
		if (!(this.canApply(sequent))) { throw IllegalTacticException() }
		return when(this) {
			EXISTS_RIGHT -> {
				fml as EXISTS
				val availableVars = sequent.freeVars.ifEmpty { setOf(fml.bddVar) }
				val unificationTerm = UnificationTerm("t_$unificationTermIndex", availableVars)
				val newConclusion = fml.instantiate(unificationTerm)
				val newFml = fml.copy(unificationTermInstantiationCount = fml.unificationTermInstantiationCount + 1)
				sequent.copy(
					conclusions = sequent.conclusions.map { if (it == fml) newFml else it }.toSet() + newConclusion
				)
			}
			ALL_LEFT -> {
				fml as ALL
				val availableVars = sequent.freeVars.ifEmpty { setOf(fml.bddVar) }
				val unificationTerm = UnificationTerm("t_$unificationTermIndex", availableVars)
				val newConclusion = fml.instantiate(unificationTerm)
				val newFml = fml.copy(unificationTermInstantiationCount = fml.unificationTermInstantiationCount + 1)
				sequent.copy(
					assumptions = sequent.assumptions.map { if (it == fml) newFml else it }.toSet() + newConclusion
				)
			}
		}
	}
}

enum class TermTactic: ITactic {
	EXISTS_RIGHT, ALL_LEFT;
	override fun toString(): String = when(this) {
		EXISTS_RIGHT -> "∃R"
		ALL_LEFT -> "∀L"
	}
	data class ApplyData(override val tactic: TermTactic, val fml: Formula, val term: Term) : IApplyData, IApplyData0
	override fun canApply(sequent: Sequent): Boolean = this.availableFmls(sequent).isNotEmpty()
	fun availableFmls(sequent: Sequent): List<Formula> = when(this) {
		EXISTS_RIGHT -> sequent.conclusions.filterIsInstance<EXISTS>()
		ALL_LEFT -> sequent.conclusions.filterIsInstance<ALL>()
	}
	fun applyTactic(sequent: Sequent, fml: Formula, term: Term): Sequent {
		if (!(this.canApply(sequent))) { throw IllegalTacticException() }
		return when(this) {
			EXISTS_RIGHT -> {
				fml as EXISTS
				val newConclusion = fml.instantiate(term)
				sequent.copy(
					conclusions = sequent.conclusions.minus(fml) + newConclusion
				)
			}
			ALL_LEFT -> {
				fml as ALL
				val newConclusion = fml.instantiate(term)
				sequent.copy(
					assumptions = sequent.conclusions.minus(fml) + newConclusion
				)
			}
		}
	}
}
