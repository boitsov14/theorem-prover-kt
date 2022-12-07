package sequentProver

import core.*
import core.Formula.*
import core.Term.*

sealed interface ITactic {
	fun toLatex(): String
}

// TODO: 2022/11/23 catchしないならいらないのでは
class IllegalTacticException : Exception()

object AXIOM : ITactic {
	override fun toString(): String = "Axiom"
	override fun toLatex(): String = "Axiom"
	fun canApply(sequent: Sequent): Boolean =
		(sequent.assumptions intersect sequent.conclusions).isNotEmpty() || TRUE in sequent.conclusions || FALSE in sequent.assumptions
}

enum class UnaryTactic : ITactic {
	AND_LEFT, OR_RIGHT, IMPLIES_RIGHT, NOT_LEFT, NOT_RIGHT, IFF_LEFT;

	override fun toString(): String = when (this) {
		AND_LEFT -> "∧: Left"
		OR_RIGHT -> "∨: Right"
		IMPLIES_RIGHT -> "→: Right"
		NOT_LEFT -> "¬: Left"
		NOT_RIGHT -> "¬: Right"
		IFF_LEFT -> "↔: Left"
	}

	override fun toLatex(): String = when (this) {
		AND_LEFT -> "$\\land$: Left"
		OR_RIGHT -> "$\\lor$: Right"
		IMPLIES_RIGHT -> "$\\rightarrow$: Right"
		NOT_LEFT -> "$\\neg$: Left"
		NOT_RIGHT -> "$\\neg$: Right"
		IFF_LEFT -> "$\\leftrightarrow$: Left"
	}

	fun getFml(sequent: Sequent): Formula? = when (this) {
		AND_LEFT -> sequent.assumptions.asSequence().filterIsInstance<AND>().firstOrNull()
		OR_RIGHT -> sequent.conclusions.asSequence().filterIsInstance<OR>().firstOrNull()
		IMPLIES_RIGHT -> sequent.conclusions.asSequence().filterIsInstance<IMPLIES>().firstOrNull()
		NOT_LEFT -> sequent.assumptions.asSequence().filterIsInstance<NOT>().firstOrNull()
		NOT_RIGHT -> sequent.conclusions.asSequence().filterIsInstance<NOT>().firstOrNull()
		IFF_LEFT -> sequent.assumptions.asSequence().filterIsInstance<IFF>().firstOrNull()
	}

	fun apply(sequent: Sequent, fml: Formula): Sequent = when (this) {
		AND_LEFT -> {
			fml as AND
			sequent.copy(
				assumptions = sequent.assumptions - fml + fml.leftFml + fml.rightFml
			)
		}

		OR_RIGHT -> {
			fml as OR
			sequent.copy(
				conclusions = sequent.conclusions - fml + fml.leftFml + fml.rightFml
			)
		}

		IMPLIES_RIGHT -> {
			fml as IMPLIES
			sequent.copy(
				assumptions = sequent.assumptions + fml.leftFml, conclusions = sequent.conclusions - fml + fml.rightFml
			)
		}

		NOT_LEFT -> {
			fml as NOT
			sequent.copy(
				assumptions = sequent.assumptions - fml, conclusions = sequent.conclusions + fml.operandFml
			)
		}

		NOT_RIGHT -> {
			fml as NOT
			sequent.copy(
				assumptions = sequent.assumptions + fml.operandFml, conclusions = sequent.conclusions - fml
			)
		}

		IFF_LEFT -> {
			fml as IFF
			sequent.copy(
				assumptions = sequent.assumptions - fml + IMPLIES(fml.leftFml, fml.rightFml) + IMPLIES(
					fml.rightFml, fml.leftFml
				)
			)
		}
	}
}

enum class BinaryTactic : ITactic {
	AND_RIGHT, OR_LEFT, IMPLIES_LEFT, IFF_RIGHT;

	override fun toString(): String = when (this) {
		AND_RIGHT -> "∧: Right"
		OR_LEFT -> "∨: Left"
		IMPLIES_LEFT -> "→: Left"
		IFF_RIGHT -> "↔: Right"
	}

	override fun toLatex(): String = when (this) {
		AND_RIGHT -> "$\\land$: Right"
		OR_LEFT -> "$\\lor$: Left"
		IMPLIES_LEFT -> "$\\rightarrow$: Left"
		IFF_RIGHT -> "$\\leftrightarrow$: Right"
	}

	fun getFml(sequent: Sequent): Formula? = when (this) {
		AND_RIGHT -> sequent.conclusions.asSequence().filterIsInstance<AND>()
			.firstOrNull { it.leftFml !in sequent.conclusions && it.rightFml !in sequent.conclusions }

		OR_LEFT -> sequent.assumptions.asSequence().filterIsInstance<OR>()
			.firstOrNull { it.leftFml !in sequent.assumptions && it.rightFml !in sequent.assumptions }

		IMPLIES_LEFT -> sequent.assumptions.asSequence().filterIsInstance<IMPLIES>()
			.firstOrNull { it.leftFml !in sequent.conclusions && it.rightFml !in sequent.assumptions }

		IFF_RIGHT -> sequent.conclusions.asSequence().filterIsInstance<IFF>().firstOrNull {
			IMPLIES(it.leftFml, it.rightFml) !in sequent.conclusions && IMPLIES(
				it.rightFml, it.leftFml
			) !in sequent.conclusions
		}
	}

	fun apply(sequent: Sequent, fml: Formula): Pair<Sequent, Sequent> = when (this) {
		AND_RIGHT -> {
			fml as AND
			val left = sequent.copy(
				conclusions = sequent.conclusions - fml + fml.leftFml
			)
			val right = sequent.copy(
				conclusions = sequent.conclusions - fml + fml.rightFml
			)
			left to right
		}

		OR_LEFT -> {
			fml as OR
			val left = sequent.copy(
				assumptions = sequent.assumptions - fml + fml.leftFml
			)
			val right = sequent.copy(
				assumptions = sequent.assumptions - fml + fml.rightFml
			)
			left to right
		}

		IMPLIES_LEFT -> {
			fml as IMPLIES
			val left = Sequent(sequent.assumptions - fml, sequent.conclusions + fml.leftFml)
			val right = sequent.copy(
				assumptions = sequent.assumptions - fml + fml.rightFml
			)
			left to right
		}

		IFF_RIGHT -> {
			fml as IFF
			val left = sequent.copy(
				conclusions = sequent.conclusions - fml + IMPLIES(fml.leftFml, fml.rightFml)
			)
			val right = sequent.copy(
				conclusions = sequent.conclusions - fml + IMPLIES(fml.rightFml, fml.leftFml)
			)
			left to right
		}
	}
}

enum class FreshVarTactic : ITactic {
	ALL_RIGHT, EXISTS_LEFT;

	override fun toString(): String = when (this) {
		ALL_RIGHT -> "∀: Right"
		EXISTS_LEFT -> "∃: Left"
	}

	override fun toLatex(): String = when (this) {
		ALL_RIGHT -> "$\\forall$: Right"
		EXISTS_LEFT -> "$\\exists$: Left"
	}

	fun getFml(sequent: Sequent): Quantified? = when (this) {
		ALL_RIGHT -> sequent.conclusions.asSequence().filterIsInstance<ALL>().firstOrNull()
		EXISTS_LEFT -> sequent.assumptions.asSequence().filterIsInstance<EXISTS>().firstOrNull()
	}

	fun apply(sequent: Sequent, fml: Formula, freshVar: Var): Sequent = when (this) {
		ALL_RIGHT -> {
			fml as ALL
			sequent.copy(
				conclusions = sequent.conclusions - fml + fml.instantiate(freshVar)
			)
		}

		EXISTS_LEFT -> {
			fml as EXISTS
			sequent.copy(
				assumptions = sequent.assumptions - fml + fml.instantiate(freshVar)
			)
		}
	}
}

enum class TermTactic : ITactic {
	ALL_LEFT, EXISTS_RIGHT;

	override fun toString(): String = when (this) {
		ALL_LEFT -> "∀: Left"
		EXISTS_RIGHT -> "∃: Right"
	}

	override fun toLatex(): String = when (this) {
		ALL_LEFT -> "$\\forall$: Left"
		EXISTS_RIGHT -> "$\\exists$: Right"
	}

	fun getFml(sequent: Sequent, fmls: Set<Quantified>): Quantified? = when (this) {
		ALL_LEFT -> sequent.assumptions.asSequence().filterIsInstance<ALL>().minus(fmls).firstOrNull()
		EXISTS_RIGHT -> sequent.conclusions.asSequence().filterIsInstance<EXISTS>().minus(fmls).firstOrNull()
	}

	fun apply(sequent: Sequent, fml: Quantified, term: Term): Sequent =
		sequent.copy(assumptions = sequent.assumptions + fml.instantiate(term))
}
