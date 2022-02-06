package sequentProver

import core.*
import core.Formula.*
import core.Term.*

sealed interface ITactic {
	fun toLatex(): String
}

sealed interface IApplyData {
	val tactic: ITactic
}

class IllegalTacticException: Exception()

object AXIOM: ITactic {
	override fun toString(): String = "axiom"
	override fun toLatex(): String = "axiom"
	fun canApply(sequent: Sequent): Boolean = (sequent.assumptions intersect sequent.conclusions).isNotEmpty() || TRUE in sequent.conclusions || FALSE in sequent.assumptions
	object ApplyData: IApplyData { override val tactic = AXIOM	}
}

enum class UnaryTactic: ITactic {
	AND_LEFT, OR_RIGHT, IMPLIES_RIGHT, NOT_LEFT, NOT_RIGHT, IFF_LEFT;
	override fun toString(): String = when(this) {
		AND_LEFT 		-> "∧: Left"
		OR_RIGHT 		-> "∨: Right"
		IMPLIES_RIGHT 	-> "→: Right"
		NOT_LEFT 		-> "¬: Left"
		NOT_RIGHT 		-> "¬: Right"
		IFF_LEFT 		-> "↔: Left"
	}
	override fun toLatex(): String = when(this) {
		AND_LEFT 		-> "$\\land$: Left"
		OR_RIGHT 		-> "$\\lor$: Right"
		IMPLIES_RIGHT 	-> "$\\rightarrow$: Right"
		NOT_LEFT 		-> "$\\neg$: Left"
		NOT_RIGHT 		-> "$\\neg$: Right"
		IFF_LEFT 		-> "$\\leftrightarrow$: Left"
	}
	data class ApplyData(override val tactic: UnaryTactic, val fml: Formula) : IApplyData {
		fun applyTactic(sequent: Sequent): Sequent = tactic.applyTactic(sequent, fml)
	}
	fun getAvailableFml(sequent: Sequent): Formula? = when(this) {
		AND_LEFT 		-> sequent.assumptions.firstOrNull { it is AND }
		OR_RIGHT 		-> sequent.conclusions.firstOrNull { it is OR }
		IMPLIES_RIGHT 	-> sequent.conclusions.firstOrNull { it is IMPLIES }
		NOT_LEFT 		-> sequent.assumptions.firstOrNull { it is NOT }
		NOT_RIGHT 		-> sequent.conclusions.firstOrNull { it is NOT }
		IFF_LEFT 		-> sequent.assumptions.firstOrNull { it is IFF }
	}
	/*
	fun availableFmls(sequent: Sequent): List<Formula> = when(this) {
		AND_LEFT 		-> sequent.assumptions.filterIsInstance<AND>()
		OR_RIGHT 		-> sequent.conclusions.filterIsInstance<OR>()
		IMPLIES_RIGHT 	-> sequent.conclusions.filterIsInstance<IMPLIES>()
		NOT_LEFT 		-> sequent.assumptions.filterIsInstance<NOT>()
		NOT_RIGHT 		-> sequent.conclusions.filterIsInstance<NOT>()
		IFF_LEFT 		-> sequent.assumptions.filterIsInstance<IFF>()
		EXISTS_LEFT 	-> sequent.assumptions.filterIsInstance<EXISTS>()
		ALL_RIGHT 		-> sequent.conclusions.filterIsInstance<ALL>()
	}
	 */
	private fun applyTactic(sequent: Sequent, fml: Formula): Sequent = when (this) {
		AND_LEFT -> {
			if (fml !is AND) throw IllegalTacticException()
			sequent.copy(
				assumptions = sequent.assumptions - fml + fml.leftFml + fml.rightFml
			)
		}
		OR_RIGHT -> {
			if (fml !is OR) { throw IllegalTacticException() }
			sequent.copy(
				conclusions = sequent.conclusions - fml + fml.leftFml + fml.rightFml
			)
		}
		IMPLIES_RIGHT -> {
			if (fml !is IMPLIES) { throw IllegalTacticException() }
			sequent.copy(
				assumptions = sequent.assumptions + fml.leftFml,
				conclusions = sequent.conclusions - fml + fml.rightFml
			)
		}
		NOT_LEFT -> {
			if (fml !is NOT) { throw IllegalTacticException() }
			sequent.copy(
				assumptions = sequent.assumptions - fml,
				conclusions = sequent.conclusions + fml.operandFml
			)
		}
		NOT_RIGHT -> {
			if (fml !is NOT) { throw IllegalTacticException() }
			sequent.copy(
				assumptions = sequent.assumptions + fml.operandFml,
				conclusions = sequent.conclusions - fml
			)
		}
		IFF_LEFT -> {
			if (fml !is IFF) { throw IllegalTacticException() }
			val toRight = IMPLIES(fml.leftFml, fml.rightFml)
			val toLeft  = IMPLIES(fml.rightFml, fml.leftFml)
			sequent.copy(
				assumptions = sequent.assumptions - fml + toRight + toLeft
			)
		}
	}
}

enum class BinaryTactic: ITactic {
	AND_RIGHT, OR_LEFT, IMPLIES_LEFT, IFF_RIGHT;
	override fun toString(): String = when(this) {
		AND_RIGHT 		-> "∧: Right"
		OR_LEFT 		-> "∨: Left"
		IMPLIES_LEFT 	-> "→: Left"
		IFF_RIGHT 		-> "↔: Right"
	}
	override fun toLatex(): String = when(this) {
		AND_RIGHT 		-> "$\\land$: Right"
		OR_LEFT 		-> "$\\lor$: Left"
		IMPLIES_LEFT 	-> "$\\rightarrow$: Left"
		IFF_RIGHT 		-> "$\\leftrightarrow$: Right"
	}
	data class ApplyData(override val tactic: BinaryTactic, val fml: Formula) : IApplyData {
		fun applyTactic(sequent: Sequent): Pair<Sequent, Sequent> = tactic.applyTactic(sequent, fml).first to tactic.applyTactic(sequent, fml).second
	}
	fun getAvailableFml(sequent: Sequent): Formula? = when(this) {
		AND_RIGHT 		-> sequent.conclusions.firstOrNull { it is AND && it.leftFml !in sequent.conclusions && it.rightFml !in sequent.conclusions }
		OR_LEFT 		-> sequent.assumptions.firstOrNull { it is OR && it.leftFml !in sequent.assumptions && it.rightFml !in sequent.assumptions }
		IMPLIES_LEFT 	-> sequent.assumptions.firstOrNull { it is IMPLIES && it.leftFml !in sequent.conclusions && it.rightFml !in sequent.assumptions }
		IFF_RIGHT 		-> sequent.conclusions.firstOrNull { it is IFF && IMPLIES(it.leftFml, it.rightFml) !in sequent.conclusions && IMPLIES(it.rightFml, it.leftFml) !in sequent.conclusions }
	}
	/*
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
			.filterNot { it.leftFml in sequent.conclusions || it.rightFml in sequent.conclusions }
	}
	 */
	private fun applyTactic(sequent: Sequent, fml: Formula): Pair<Sequent, Sequent> = when (this) {
		AND_RIGHT -> {
			if (fml !is AND) { throw IllegalTacticException() }
			val leftSequent = sequent.copy(
				conclusions = sequent.conclusions - fml + fml.leftFml
			)
			val rightSequent = sequent.copy(
				conclusions = sequent.conclusions - fml + fml.rightFml
			)
			leftSequent to rightSequent
		}
		OR_LEFT -> {
			if (fml !is OR) { throw IllegalTacticException() }
			val leftSequent = sequent.copy(
				assumptions = sequent.assumptions - fml + fml.leftFml
			)
			val rightSequent = sequent.copy(
				assumptions = sequent.assumptions - fml + fml.rightFml
			)
			leftSequent to rightSequent
		}
		IMPLIES_LEFT -> {
			if (fml !is IMPLIES) { throw IllegalTacticException() }
			val newSequent1 = sequent.copy(
				assumptions = sequent.assumptions - fml,
				conclusions = sequent.conclusions + fml.leftFml
			)
			val newSequent2 = sequent.copy(
				assumptions = sequent.assumptions - fml + fml.rightFml
			)
			newSequent1 to newSequent2
		}
		IFF_RIGHT -> {
			if (fml !is IFF) { throw IllegalTacticException() }
			val leftSequent = sequent.copy(
				conclusions = sequent.conclusions - fml + IMPLIES(fml.leftFml, fml.rightFml)
			)
			val rightSequent = sequent.copy(
				conclusions = sequent.conclusions - fml + IMPLIES(fml.rightFml, fml.leftFml)
			)
			leftSequent to rightSequent
		}
	}
}

enum class FreshVarInstantiationTactic: ITactic {
	ALL_RIGHT, EXISTS_LEFT;
	override fun toString(): String = when(this) {
		ALL_RIGHT 		-> "∀: Right"
		EXISTS_LEFT 	-> "∃: Left"
	}
	override fun toLatex(): String = when(this) {
		ALL_RIGHT 		-> "$\\forall$: Right"
		EXISTS_LEFT 	-> "$\\exists$: Left"
	}
	data class ApplyData(val fml: Formula, val freshVar: Var) : IApplyData {
		override val tactic: FreshVarInstantiationTactic
			get() = when(fml) {
				is ALL 		-> ALL_RIGHT
				is EXISTS 	-> EXISTS_LEFT
				else -> throw IllegalTacticException()
			}
		fun applyTactic(sequent: Sequent): Sequent = tactic.applyTactic(sequent, fml, freshVar)
	}
	fun getAvailableFml(sequent: Sequent): Quantified? = when(this) {
		ALL_RIGHT 		-> sequent.conclusions.firstOrNull { it is ALL } as Quantified?
		EXISTS_LEFT 	-> sequent.assumptions.firstOrNull { it is EXISTS } as Quantified?
	}
	private fun applyTactic(sequent: Sequent, fml: Formula, freshVar: Var): Sequent = when (this) {
		ALL_RIGHT -> {
			if (fml !is ALL) { throw IllegalTacticException() }
			sequent.copy(
				conclusions = sequent.conclusions - fml + fml.instantiate(freshVar)
			)
		}
		EXISTS_LEFT -> {
			if (fml !is EXISTS) { throw IllegalTacticException() }
			sequent.copy(
				assumptions = sequent.assumptions - fml + fml.instantiate(freshVar)
			)
		}
	}
}

enum class TermInstantiationTactic: ITactic {
	ALL_LEFT, EXISTS_RIGHT;
	override fun toString(): String = when(this) {
		ALL_LEFT 		-> "∀: Left"
		EXISTS_RIGHT 	-> "∃: Right"
	}
	override fun toLatex(): String = when(this) {
		ALL_LEFT 		-> "$\\forall$: Left"
		EXISTS_RIGHT 	-> "$\\exists$: Right"
	}
	data class ApplyData(val fml: Formula, val term: Term) : IApplyData {
		override val tactic: TermInstantiationTactic
			get() = when(fml) {
				is ALL 		-> ALL_LEFT
				is EXISTS 	-> EXISTS_RIGHT
				else -> throw IllegalTacticException()
			}
		fun applyTactic(sequent: Sequent): Sequent = tactic.applyTactic(sequent, fml, term)
	}
	// TODO: 2022/02/05 <= or <
	fun getAvailableFml(sequent: Sequent, unificationTermInstantiationMaxCount: Int): Quantified? = when(this) {
		ALL_LEFT 		-> sequent.assumptions.firstOrNull { it is ALL && it.unificationTermInstantiationCount <= unificationTermInstantiationMaxCount } as Quantified?
		EXISTS_RIGHT 	-> sequent.conclusions.firstOrNull { it is EXISTS && it.unificationTermInstantiationCount <= unificationTermInstantiationMaxCount } as Quantified?
	}
	private fun applyTactic(sequent: Sequent, fml: Formula, term: Term): Sequent = when(this) {
		ALL_LEFT -> {
			//if (fml !is ALL) { throw IllegalTacticException() }
			val fml0 = sequent.assumptions.filterIsInstance<ALL>().firstOrNull { it == fml } ?: throw IllegalTacticException()
			val newConclusion = fml0.instantiate(term)
			val newFml = fml0.copy(unificationTermInstantiationCount = fml0.unificationTermInstantiationCount + 1)
			// TODO: 2022/02/03 もっと良い書き方ある？
			sequent.copy(
				assumptions = sequent.assumptions.map { if (it == fml) newFml else it }.toSet() + newConclusion
			)
		}
		EXISTS_RIGHT -> {
			//if (fml !is EXISTS) { throw IllegalTacticException() }
			val fml0 = sequent.conclusions.filterIsInstance<EXISTS>().firstOrNull { it == fml } ?: throw IllegalTacticException()
			val newConclusion = fml0.instantiate(term)
			val newFml = fml0.copy(unificationTermInstantiationCount = fml0.unificationTermInstantiationCount + 1)
			sequent.copy(
				conclusions = sequent.conclusions.map { if (it == fml) newFml else it }.toSet() + newConclusion
			)
		}
	}
}
