package core

import core.Term.*

class DuplicateBddVarException : Exception()
class CannotQuantifyPredicateException : Exception()
class CannotQuantifyFunctionException : Exception()

sealed class Formula {
	object TRUE : Formula()
	object FALSE : Formula()
	data class PREDICATE(val id: String, val terms: List<Term>) : Formula()
	data class NOT(val operandFml: Formula) : Formula()
	data class AND(val leftFml: Formula, val rightFml: Formula) : Formula()
	data class OR(val leftFml: Formula, val rightFml: Formula) : Formula()
	data class IMPLIES(val leftFml: Formula, val rightFml: Formula) : Formula()
	data class IFF(val leftFml: Formula, val rightFml: Formula) : Formula()
	sealed class Quantified : Formula() {
		abstract val bddVar: Var
		abstract val operandFml: Formula
		fun instantiate(newTerm: Term): Formula = operandFml.replace(bddVar, newTerm)
		final override fun equals(other: Any?): Boolean {
			if (this === other) return true
			if (javaClass != other?.javaClass) return false
			other as Quantified
			if (bddVar == other.bddVar) return operandFml == other.operandFml
			if (bddVar in other.operandFml.freeVars) return false
			if (operandFml == other.instantiate(bddVar)) return true
			return false
		}

		final override fun hashCode(): Int {
			var result = javaClass.hashCode()
			result = 31 * result + operandFml.javaClass.hashCode()
			return result
		}
	}

	data class ALL(
		override val bddVar: Var, override val operandFml: Formula, val unificationTermInstantiationCount: Int = 0
	) : Quantified() {
		init {
			if (bddVar in operandFml.bddVars) {
				throw DuplicateBddVarException()
			}
			if (bddVar.id in operandFml.predicateIds) {
				throw CannotQuantifyPredicateException()
			}
			if (bddVar.id in operandFml.functionIds) {
				throw CannotQuantifyFunctionException()
			}
		}
	}

	data class EXISTS(
		override val bddVar: Var, override val operandFml: Formula, val unificationTermInstantiationCount: Int = 0
	) : Quantified() {
		init {
			if (bddVar in operandFml.bddVars) {
				throw DuplicateBddVarException()
			}
			if (bddVar.id in operandFml.predicateIds) {
				throw CannotQuantifyPredicateException()
			}
			if (bddVar.id in operandFml.functionIds) {
				throw CannotQuantifyFunctionException()
			}
		}
	}

	private fun recToString(): String = when (this) {
		TRUE -> "true"
		FALSE -> "false"
		is PREDICATE -> id + if (terms.isNotEmpty()) terms.joinToString(
			separator = ",", prefix = "(", postfix = ")"
		) else ""
		is NOT -> "¬${operandFml.recToString()}"
		is AND -> {
			val rightFmlStr =
				if (rightFml is AND) rightFml.recToString().removeSurrounding("(", ")") else rightFml.recToString()
			"(${leftFml.recToString()} ∧ $rightFmlStr)"
		}
		is OR -> {
			val rightFmlStr =
				if (rightFml is OR) rightFml.recToString().removeSurrounding("(", ")") else rightFml.recToString()
			"(${leftFml.recToString()} ∨ $rightFmlStr)"
		}
		is IMPLIES -> "(${leftFml.recToString()} → ${rightFml.recToString()})"
		is IFF -> "(${leftFml.recToString()} ↔ ${rightFml.recToString()})"
		is ALL -> "∀$bddVar${operandFml.recToString()}"
		is EXISTS -> "∃$bddVar${operandFml.recToString()}"
	}

	final override fun toString(): String = recToString().removeSurrounding("(", ")")
	fun toLatex(): String =
		toString().replace("true", "\\top ").replace("false", "\\bot ").replace("¬", "\\lnot ").replace("∧", "\\land")
			.replace("∨", "\\lor").replace("→", "\\rightarrow").replace("↔", "\\leftrightarrow")
			.replace("∀", "\\forall ").replace("∃", "\\exists ")

	val freeVars: Set<Var>
		get() = when (this) {
			TRUE -> emptySet()
			FALSE -> emptySet()
			is PREDICATE -> terms.map { it.freeVars }.flatten().toSet()
			is NOT -> operandFml.freeVars
			is AND -> leftFml.freeVars + rightFml.freeVars
			is OR -> leftFml.freeVars + rightFml.freeVars
			is IMPLIES -> leftFml.freeVars + rightFml.freeVars
			is IFF -> leftFml.freeVars + rightFml.freeVars
			is Quantified -> operandFml.freeVars.minus(bddVar)
		}
	val bddVars: Set<Var>
		get() = when (this) {
			TRUE -> emptySet()
			FALSE -> emptySet()
			is PREDICATE -> emptySet()
			is NOT -> operandFml.bddVars
			is AND -> leftFml.bddVars + rightFml.bddVars
			is OR -> leftFml.bddVars + rightFml.bddVars
			is IMPLIES -> leftFml.bddVars + rightFml.bddVars
			is IFF -> leftFml.bddVars + rightFml.bddVars
			is Quantified -> operandFml.bddVars + bddVar
		}

	/*
	val unificationTerms: Set<UnificationTerm>
		get() = when (this) {
			TRUE 			-> emptySet()
			FALSE 			-> emptySet()
			is PREDICATE 	-> terms.map { it.unificationTerms }.flatten().toSet()
			is NOT 			-> operandFml.unificationTerms
			is AND 			-> leftFml.unificationTerms + rightFml.unificationTerms
			is OR 			-> leftFml.unificationTerms + rightFml.unificationTerms
			is IMPLIES 		-> leftFml.unificationTerms + rightFml.unificationTerms
			is IFF 			-> leftFml.unificationTerms + rightFml.unificationTerms
			is ALL 			-> operandFml.unificationTerms
			is EXISTS 		-> operandFml.unificationTerms
		}
	 */
	private val predicateIds: Set<String>
		get() = when (this) {
			TRUE -> emptySet()
			FALSE -> emptySet()
			is PREDICATE -> setOf(id)
			is NOT -> operandFml.predicateIds
			is AND -> leftFml.predicateIds + rightFml.predicateIds
			is OR -> leftFml.predicateIds + rightFml.predicateIds
			is IMPLIES -> leftFml.predicateIds + rightFml.predicateIds
			is IFF -> leftFml.predicateIds + rightFml.predicateIds
			is Quantified -> operandFml.predicateIds
		}
	private val functionIds: Set<String>
		get() = when (this) {
			TRUE -> emptySet()
			FALSE -> emptySet()
			is PREDICATE -> terms.map { it.functionIds }.flatten().toSet()
			is NOT -> operandFml.functionIds
			is AND -> leftFml.functionIds + rightFml.functionIds
			is OR -> leftFml.functionIds + rightFml.functionIds
			is IMPLIES -> leftFml.functionIds + rightFml.functionIds
			is IFF -> leftFml.functionIds + rightFml.functionIds
			is Quantified -> operandFml.functionIds
		}

	fun replace(oldVar: Var, newTerm: Term): Formula = when (this) {
		TRUE -> this
		FALSE -> this
		is PREDICATE -> PREDICATE(id, terms.map { it.replace(oldVar, newTerm) })
		is NOT -> NOT(operandFml.replace(oldVar, newTerm))
		is AND -> AND(leftFml.replace(oldVar, newTerm), rightFml.replace(oldVar, newTerm))
		is OR -> OR(leftFml.replace(oldVar, newTerm), rightFml.replace(oldVar, newTerm))
		is IMPLIES -> IMPLIES(leftFml.replace(oldVar, newTerm), rightFml.replace(oldVar, newTerm))
		is IFF -> IFF(leftFml.replace(oldVar, newTerm), rightFml.replace(oldVar, newTerm))
		is ALL -> {
			if (oldVar == bddVar) {
				this
			} else if (bddVar in newTerm.freeVars && oldVar in freeVars) {
				val newBddVar = bddVar.getFreshVar(operandFml.bddVars + operandFml.freeVars + newTerm.freeVars)
				this.copy(
					bddVar = newBddVar, operandFml = operandFml.replace(bddVar, newBddVar).replace(oldVar, newTerm)
				)
			} else {
				this.copy(
					operandFml = operandFml.replace(oldVar, newTerm)
				)
			}
		}
		is EXISTS -> {
			if (oldVar == bddVar) {
				this
			} else if (bddVar in newTerm.freeVars && oldVar in freeVars) {
				val newBddVar = bddVar.getFreshVar(operandFml.bddVars + operandFml.freeVars + newTerm.freeVars)
				this.copy(
					bddVar = newBddVar, operandFml = operandFml.replace(bddVar, newBddVar).replace(oldVar, newTerm)
				)
			} else {
				this.copy(
					operandFml = operandFml.replace(oldVar, newTerm)
				)
			}
		}
	}

	private fun replace(oldUnificationTerm: UnificationTerm, newTerm: Term): Formula = when (this) {
		TRUE -> this
		FALSE -> this
		is PREDICATE -> PREDICATE(id, terms.map { it.replace(oldUnificationTerm, newTerm) })
		is NOT -> NOT(operandFml.replace(oldUnificationTerm, newTerm))
		is AND -> AND(leftFml.replace(oldUnificationTerm, newTerm), rightFml.replace(oldUnificationTerm, newTerm))
		is OR -> OR(leftFml.replace(oldUnificationTerm, newTerm), rightFml.replace(oldUnificationTerm, newTerm))
		is IMPLIES -> IMPLIES(
			leftFml.replace(oldUnificationTerm, newTerm), rightFml.replace(oldUnificationTerm, newTerm)
		)
		is IFF -> IFF(leftFml.replace(oldUnificationTerm, newTerm), rightFml.replace(oldUnificationTerm, newTerm))
		is ALL -> {
			if (!(oldUnificationTerm.availableVars.containsAll(newTerm.freeVars))) {
				throw IllegalArgumentException()
			}
			if (bddVar in oldUnificationTerm.availableVars) {
				this
			} else {
				this.copy(
					operandFml = operandFml.replace(oldUnificationTerm, newTerm)
				)
			}
		}
		is EXISTS -> {
			if (!(oldUnificationTerm.availableVars.containsAll(newTerm.freeVars))) {
				throw IllegalArgumentException()
			}
			if (bddVar in oldUnificationTerm.availableVars) {
				this
			} else {
				this.copy(
					operandFml = operandFml.replace(oldUnificationTerm, newTerm)
				)
			}
		}
	}

	fun replace(substitution: Substitution): Formula {
		var result = this
		substitution.forEach { (key, value) -> result = result.replace(key, value) }
		return result
	}

	// TODO: 2022/06/06 internalとは?
	internal fun simplify0(): Formula = when (this) {
		NOT(FALSE) -> TRUE
		NOT(TRUE) -> FALSE
		is NOT -> if (operandFml is NOT) operandFml.operandFml else this
		is AND -> if (leftFml == FALSE || rightFml == FALSE) FALSE
		else if (leftFml == TRUE) rightFml
		else if (rightFml == TRUE) leftFml
		else this
		is OR -> if (leftFml == TRUE || rightFml == TRUE) TRUE
		else if (leftFml == FALSE) rightFml
		else if (rightFml == FALSE) leftFml
		else this
		is IMPLIES -> if (leftFml == FALSE || rightFml == TRUE) TRUE
		else if (leftFml == TRUE) rightFml
		else if (rightFml == FALSE) NOT(leftFml)
		else this
		is IFF -> if (leftFml == TRUE) rightFml
		else if (rightFml == TRUE) leftFml
		else if (leftFml == FALSE) NOT(rightFml)
		else if (rightFml == FALSE) NOT(leftFml)
		else this
		else -> this
	}

	fun simplify(): Formula = when (this) {
		is NOT -> NOT(operandFml.simplify()).simplify0()
		is AND -> AND(leftFml.simplify(), rightFml.simplify()).simplify0()
		is OR -> OR(leftFml.simplify(), rightFml.simplify()).simplify0()
		is IMPLIES -> IMPLIES(leftFml.simplify(), rightFml.simplify()).simplify0()
		is IFF -> IFF(leftFml.simplify(), rightFml.simplify()).simplify0()
		else -> this
	}
}
