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
	data class ApplyData(override val tactic: UnaryTactic, val fmlIndex: Int) : IApplyData {
		fun applyTactic(sequent: Sequent): Sequent = tactic.applyTactic(sequent, fmlIndex)
	}
	fun getAvailableFmlIndex(sequent: Sequent): Int = when(this) {
		AND_LEFT 		-> sequent.assumptions.indexOfFirst { it is AND }
		OR_RIGHT 		-> sequent.conclusions.indexOfFirst { it is OR }
		IMPLIES_RIGHT 	-> sequent.conclusions.indexOfFirst { it is IMPLIES }
		NOT_LEFT 		-> sequent.assumptions.indexOfFirst { it is NOT }
		NOT_RIGHT 		-> sequent.conclusions.indexOfFirst { it is NOT }
		IFF_LEFT 		-> sequent.assumptions.indexOfFirst { it is IFF }
		ALL_RIGHT 		-> sequent.conclusions.indexOfFirst { it is ALL }
		EXISTS_LEFT 	-> sequent.assumptions.indexOfFirst { it is EXISTS }
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
	private fun applyTactic(sequent: Sequent, fmlIndex: Int): Sequent = when (this) {
		AND_LEFT -> {
			val fml = sequent.assumptions.elementAtOrNull(fmlIndex)
			if (fml !is AND) throw IllegalTacticException()
			sequent.copy(
				assumptions = sequent.assumptions - fml + fml.leftFml + fml.rightFml
			)
		}
		OR_RIGHT -> {
			val fml = sequent.conclusions.elementAtOrNull(fmlIndex)
			if (fml !is OR) { throw IllegalTacticException() }
			sequent.copy(
				conclusions = sequent.conclusions - fml + fml.leftFml + fml.rightFml
			)
		}
		IMPLIES_RIGHT -> {
			val fml = sequent.conclusions.elementAtOrNull(fmlIndex)
			if (fml !is IMPLIES) { throw IllegalTacticException() }
			sequent.copy(
				assumptions = sequent.assumptions + fml.leftFml,
				conclusions = sequent.conclusions - fml + fml.rightFml
			)
		}
		NOT_LEFT -> {
			val fml = sequent.assumptions.elementAtOrNull(fmlIndex)
			if (fml !is NOT) { throw IllegalTacticException() }
			sequent.copy(
				assumptions = sequent.assumptions - fml,
				conclusions = sequent.conclusions + fml.operandFml
			)
		}
		NOT_RIGHT -> {
			val fml = sequent.conclusions.elementAtOrNull(fmlIndex)
			if (fml !is NOT) { throw IllegalTacticException() }
			sequent.copy(
				assumptions = sequent.assumptions + fml.operandFml,
				conclusions = sequent.conclusions - fml
			)
		}
		IFF_LEFT -> {
			val fml = sequent.assumptions.elementAtOrNull(fmlIndex)
			if (fml !is IFF) { throw IllegalTacticException() }
			val toRight = IMPLIES(fml.leftFml, fml.rightFml)
			val toLeft  = IMPLIES(fml.rightFml, fml.leftFml)
			sequent.copy(
				assumptions = sequent.assumptions - fml + toRight + toLeft
			)
		}
		// TODO: 2022/02/05 分離独立
		ALL_RIGHT -> {
			val fml = sequent.conclusions.elementAtOrNull(fmlIndex)
			if (fml !is ALL) { throw IllegalTacticException() }
			val freshVar = fml.bddVar.getFreshVar(sequent.freeVars)
			val newConclusion = fml.instantiate(freshVar)
			sequent.copy(
				conclusions = sequent.conclusions - fml + newConclusion
			)
		}
		EXISTS_LEFT -> {
			val fml = sequent.assumptions.elementAtOrNull(fmlIndex)
			if (fml !is EXISTS) { throw IllegalTacticException() }
			val freshVar = fml.bddVar.getFreshVar(sequent.freeVars)
			val newAssumption = fml.instantiate(freshVar)
			sequent.copy(
				assumptions = sequent.assumptions - fml + newAssumption
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
	data class ApplyData(override val tactic: BinaryTactic, val fmlIndex: Int) : IApplyData {
		fun applyTactic(sequent: Sequent): Pair<Sequent, Sequent> = tactic.applyTactic(sequent, fmlIndex).first to tactic.applyTactic(sequent, fmlIndex).second
	}
	fun getAvailableFmlIndex(sequent: Sequent): Int = when(this) {
		AND_RIGHT 		-> sequent.conclusions.indexOfFirst { it is AND && it.leftFml !in sequent.conclusions && it.rightFml !in sequent.conclusions }
		OR_LEFT 		-> sequent.assumptions.indexOfFirst { it is OR && it.leftFml !in sequent.assumptions && it.rightFml !in sequent.assumptions }
		IMPLIES_LEFT 	-> sequent.assumptions.indexOfFirst { it is IMPLIES && it.leftFml !in sequent.conclusions && it.rightFml !in sequent.assumptions }
		IFF_RIGHT 		-> sequent.conclusions.indexOfFirst { it is IFF && it.leftFml !in sequent.conclusions && it.rightFml !in sequent.conclusions }
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
	private fun applyTactic(sequent: Sequent, fmlIndex: Int): Pair<Sequent, Sequent> = when (this) {
		AND_RIGHT -> {
			val fml = sequent.conclusions.elementAtOrNull(fmlIndex)
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
			val fml = sequent.assumptions.elementAtOrNull(fmlIndex)
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
			val fml = sequent.assumptions.elementAtOrNull(fmlIndex)
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
			val fml = sequent.conclusions.elementAtOrNull(fmlIndex)
			if (fml !is IFF) { throw IllegalTacticException() }
			val leftSequent = sequent.copy(
				conclusions = sequent.conclusions - fml + fml.leftFml
			)
			val rightSequent = sequent.copy(
				conclusions = sequent.conclusions - fml + fml.rightFml
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
	data class ApplyData(override val tactic: UnificationTermTactic, val fmlIndex: Int, val unificationTerm: UnificationTerm) : IApplyData {
		fun applyTactic(sequent: Sequent): Sequent = tactic.applyTactic(sequent, fmlIndex, unificationTerm)
		fun toTermTacticApplyData(term: Term): TermTactic.ApplyData = TermTactic.ApplyData(tactic.toTermTactic(), fmlIndex, term)
	}
	// TODO: 2022/02/05 <= or <
	fun getAvailableFmlIndex(sequent: Sequent, unificationTermInstantiationMaxCount: Int): Int = when(this) {
		ALL_LEFT 		-> sequent.assumptions.indexOfFirst { it is ALL && it.unificationTermInstantiationCount <= unificationTermInstantiationMaxCount }
		EXISTS_RIGHT 	-> sequent.conclusions.indexOfFirst { it is EXISTS && it.unificationTermInstantiationCount <= unificationTermInstantiationMaxCount }
	}
	/*
	fun availableFmls(sequent: Sequent, unificationTermInstantiationMaxCount: Int): List<Formula> = when(this) {
		ALL_LEFT 		-> sequent.assumptions.filterIsInstance<ALL>().filter { it.unificationTermInstantiationCount <= unificationTermInstantiationMaxCount }
		EXISTS_RIGHT 	-> sequent.conclusions.filterIsInstance<EXISTS>().filter { it.unificationTermInstantiationCount <= unificationTermInstantiationMaxCount }
	}
	 */
	private fun applyTactic(sequent: Sequent, fmlIndex: Int, unificationTerm: UnificationTerm): Sequent = when(this) {
		ALL_LEFT -> {
			val fml = sequent.assumptions.elementAtOrNull(fmlIndex)
			if (fml !is ALL) { throw IllegalTacticException() }
			val newConclusion = fml.instantiate(unificationTerm)
			val newFml = fml.copy(unificationTermInstantiationCount = fml.unificationTermInstantiationCount + 1)
			// TODO: 2022/02/03 もっと良い書き方ある？
			sequent.copy(
				assumptions = sequent.assumptions.map { if (it == fml) newFml else it }.toSet() + newConclusion
			)
		}
		EXISTS_RIGHT -> {
			val fml = sequent.conclusions.elementAtOrNull(fmlIndex)
			if (fml !is EXISTS) { throw IllegalTacticException() }
			val newConclusion = fml.instantiate(unificationTerm)
			val newFml = fml.copy(unificationTermInstantiationCount = fml.unificationTermInstantiationCount + 1)
			sequent.copy(
				conclusions = sequent.conclusions.map { if (it == fml) newFml else it }.toSet() + newConclusion
			)
		}
	}
	private fun toTermTactic(): TermTactic = when(this) {
		ALL_LEFT 		-> TermTactic.ALL_LEFT
		EXISTS_RIGHT 	-> TermTactic.EXISTS_RIGHT
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
	data class ApplyData(override val tactic: TermTactic, val fmlIndex: Int, val term: Term) : IApplyData {
		fun applyTactic(sequent: Sequent): Sequent = tactic.applyTactic(sequent, fmlIndex, term)
	}
	fun applyTactic(sequent: Sequent, fmlIndex: Int, term: Term): Sequent = when(this) {
		ALL_LEFT -> {
			val fml = sequent.assumptions.elementAtOrNull(fmlIndex)
			if (fml !is ALL) { throw IllegalTacticException() }
			val newConclusion = fml.instantiate(term)
			sequent.copy(
				assumptions = sequent.assumptions + newConclusion
			)
		}
		EXISTS_RIGHT -> {
			val fml = sequent.conclusions.elementAtOrNull(fmlIndex)
			if (fml !is EXISTS) { throw IllegalTacticException() }
			val newConclusion = fml.instantiate(term)
			sequent.copy(
				conclusions = sequent.conclusions + newConclusion
			)
		}
	}
}
