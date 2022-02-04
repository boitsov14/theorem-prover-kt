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
	AND_LEFT, OR_RIGHT, IMPLIES_RIGHT, NOT_LEFT, NOT_RIGHT, IFF_LEFT, ALL_RIGHT, EXISTS_LEFT;
	override fun toString(): String = when(this) {
		AND_LEFT 		-> "∧: Left"
		OR_RIGHT 		-> "∨: Right"
		IMPLIES_RIGHT 	-> "→: Right"
		NOT_LEFT 		-> "¬: Left"
		NOT_RIGHT 		-> "¬: Right"
		IFF_LEFT 		-> "↔: Left"
		ALL_RIGHT 		-> "∀: Right"
		EXISTS_LEFT 	-> "∃: Left"
	}
	override fun toLatex(): String = when(this) {
		AND_LEFT 		-> "$\\land$: Left"
		OR_RIGHT 		-> "$\\lor$: Right"
		IMPLIES_RIGHT 	-> "$\\rightarrow$: Right"
		NOT_LEFT 		-> "$\\neg$: Left"
		NOT_RIGHT 		-> "$\\neg$: Right"
		IFF_LEFT 		-> "$\\leftrightarrow$: Left"
		ALL_RIGHT 		-> "$\\forall$: Right"
		EXISTS_LEFT 	-> "$\\exists$: Left"
	}
	data class ApplyData(override val tactic: UnaryTactic, val fml: Formula) : IApplyData {
		fun applyTactic(sequent: Sequent): Sequent = tactic.applyTactic(sequent, fml)
	}
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
	private fun applyTactic(sequent: Sequent, fml: Formula): Sequent = when (this) {
		AND_LEFT -> {
			if (fml !is AND) { throw IllegalTacticException() }
			sequent.copy(
				assumptions = sequent.assumptions.minus(fml) + fml.leftFml + fml.rightFml
			)
		}
		OR_RIGHT -> {
			if (fml !is OR) { throw IllegalTacticException() }
			sequent.copy(
				conclusions = sequent.conclusions.minus(fml) + fml.leftFml + fml.rightFml
			)
		}
		IMPLIES_RIGHT -> {
			if (fml !is IMPLIES) { throw IllegalTacticException() }
			sequent.copy(
				assumptions = sequent.assumptions + fml.leftFml,
				conclusions = sequent.conclusions.minus(fml) + fml.rightFml
			)
		}
		NOT_LEFT -> {
			if (fml !is NOT) { throw IllegalTacticException() }
			sequent.copy(
				assumptions = sequent.assumptions.minus(fml),
				conclusions = sequent.conclusions + fml.operandFml
			)
		}
		NOT_RIGHT -> {
			if (fml !is NOT) { throw IllegalTacticException() }
			sequent.copy(
				assumptions = sequent.assumptions + fml.operandFml,
				conclusions = sequent.conclusions.minus(fml)
			)
		}
		IFF_LEFT -> {
			if (fml !is IFF) { throw IllegalTacticException() }
			val toRight = IMPLIES(fml.leftFml, fml.rightFml)
			val toLeft  = IMPLIES(fml.rightFml, fml.leftFml)
			sequent.copy(
				assumptions = sequent.assumptions.minus(fml) + toRight + toLeft
			)
		}
		ALL_RIGHT -> {
			if (fml !is ALL) { throw IllegalTacticException() }
			val freshVar = fml.bddVar.getFreshVar(sequent.freeVars)
			val newConclusion = fml.instantiate(freshVar)
			sequent.copy(
				conclusions = sequent.conclusions.minus(fml) + newConclusion
			)
		}
		EXISTS_LEFT -> {
			if (fml !is EXISTS) { throw IllegalTacticException() }
			val freshVar = fml.bddVar.getFreshVar(sequent.freeVars)
			val newAssumption = fml.instantiate(freshVar)
			sequent.copy(
				assumptions = sequent.assumptions.minus(fml) + newAssumption
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
	private fun applyTactic(sequent: Sequent, fml: Formula): Pair<Sequent, Sequent> = when (this) {
		AND_RIGHT -> {
			if (fml !is AND) { throw IllegalTacticException() }
			val leftSequent = sequent.copy(
				conclusions = sequent.conclusions.minus(fml) + fml.leftFml
			)
			val rightSequent = sequent.copy(
				conclusions = sequent.conclusions.minus(fml) + fml.rightFml
			)
			leftSequent to rightSequent
		}
		OR_LEFT -> {
			if (fml !is OR) { throw IllegalTacticException() }
			val leftSequent = sequent.copy(
				assumptions = sequent.assumptions.minus(fml) + fml.leftFml
			)
			val rightSequent = sequent.copy(
				assumptions = sequent.assumptions.minus(fml) + fml.rightFml
			)
			leftSequent to rightSequent
		}
		IMPLIES_LEFT -> {
			if (fml !is IMPLIES) { throw IllegalTacticException() }
			val newSequent1 = sequent.copy(
				assumptions = sequent.assumptions.minus(fml),
				conclusions = sequent.conclusions + fml.leftFml
			)
			val newSequent2 = sequent.copy(
				assumptions = sequent.assumptions.minus(fml) + fml.rightFml
			)
			newSequent1 to newSequent2
		}
		IFF_RIGHT -> {
			if (fml !is IFF) { throw IllegalTacticException() }
			val leftSequent = sequent.copy(
				conclusions = sequent.conclusions.minus(fml) + fml.leftFml
			)
			val rightSequent = sequent.copy(
				conclusions = sequent.conclusions.minus(fml) + fml.rightFml
			)
			leftSequent to rightSequent
		}
	}
}

enum class UnificationTermTactic: ITactic {
	ALL_LEFT, EXISTS_RIGHT;
	override fun toString(): String = when(this) {
		ALL_LEFT 		-> "∀: Left"
		EXISTS_RIGHT 	-> "∃: Right"
	}
	override fun toLatex(): String = when(this) {
		ALL_LEFT 		-> "$\\forall$: Left"
		EXISTS_RIGHT 	-> "$\\exists$: Right"
	}
	data class ApplyData(override val tactic: UnificationTermTactic, val fml: Formula, val unificationTerm: UnificationTerm) : IApplyData {
		fun applyTactic(sequent: Sequent): Sequent = tactic.applyTactic(sequent, fml, unificationTerm)
		fun toTermTacticApplyData(term: Term): TermTactic.ApplyData = TermTactic.ApplyData(tactic.toTermTactic(), fml, term)
	}
	fun availableFmls(sequent: Sequent, unificationTermInstantiationMaxCount: Int): List<Formula> = when(this) {
		ALL_LEFT 		-> sequent.assumptions.filterIsInstance<ALL>().filter { it.unificationTermInstantiationCount <= unificationTermInstantiationMaxCount }
		EXISTS_RIGHT 	-> sequent.conclusions.filterIsInstance<EXISTS>().filter { it.unificationTermInstantiationCount <= unificationTermInstantiationMaxCount }
	}
	private fun applyTactic(sequent: Sequent, fml: Formula, unificationTerm: UnificationTerm): Sequent = when(this) {
		ALL_LEFT -> {
			if (fml !is ALL) { throw IllegalTacticException() }
			//val availableVars = sequent.freeVars.ifEmpty { setOf(fml.bddVar) }
			//val unificationTerm = UnificationTerm(unificationTermIndex, availableVars)
			val newConclusion = fml.instantiate(unificationTerm)
			val newFml = fml.copy(unificationTermInstantiationCount = fml.unificationTermInstantiationCount + 1)
			// TODO: 2022/02/03 もっと良い書き方ある？
			sequent.copy(
				assumptions = sequent.assumptions.map { if (it == fml) newFml else it }.toSet() + newConclusion
			)
		}
		EXISTS_RIGHT -> {
			if (fml !is EXISTS) { throw IllegalTacticException() }
			//val availableVars = sequent.freeVars.ifEmpty { setOf(fml.bddVar) }
			//val unificationTerm = UnificationTerm(unificationTermIndex, availableVars)
			val newConclusion = fml.instantiate(unificationTerm)
			val newFml = fml.copy(unificationTermInstantiationCount = fml.unificationTermInstantiationCount + 1)
			sequent.copy(
				conclusions = sequent.conclusions.map { if (it == fml) newFml else it }.toSet() + newConclusion
			)
		}
	}
	private fun toTermTactic(): TermTactic = when(this) {
		ALL_LEFT -> TermTactic.ALL_LEFT
		EXISTS_RIGHT -> TermTactic.EXISTS_RIGHT
	}
}

enum class TermTactic: ITactic {
	ALL_LEFT, EXISTS_RIGHT;
	override fun toString(): String = when(this) {
		ALL_LEFT 		-> "∀: Left"
		EXISTS_RIGHT 	-> "∃: Right"
	}
	override fun toLatex(): String = when(this) {
		ALL_LEFT 		-> "$\\forall$: Left"
		EXISTS_RIGHT 	-> "$\\exists$: Right"
	}
	data class ApplyData(override val tactic: TermTactic, val fml: Formula, val term: Term) : IApplyData {
		fun applyTactic(sequent: Sequent): Sequent = tactic.applyTactic(sequent, fml, term)
	}
	fun applyTactic(sequent: Sequent, fml: Formula, term: Term): Sequent = when(this) {
		ALL_LEFT -> {
			if (fml !is ALL) { throw IllegalTacticException() }
			val newConclusion = fml.instantiate(term)
			sequent.copy(
				assumptions = sequent.assumptions + newConclusion
			)
		}
		EXISTS_RIGHT -> {
			if (fml !is EXISTS) { throw IllegalTacticException() }
			val newConclusion = fml.instantiate(term)
			sequent.copy(
				conclusions = sequent.conclusions + newConclusion
			)
		}
	}
}
