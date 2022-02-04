package core

import core.Term.*

class DuplicateBddVarException: Exception()

sealed class Formula {
	object TRUE: Formula()
	object FALSE: Formula()
	data class PREDICATE(val id: String, val terms: List<Term>): Formula()
	data class NOT(val operandFml: Formula): Formula()
	data class AND(val leftFml: Formula, val rightFml: Formula): Formula()
	data class OR(val leftFml: Formula, val rightFml: Formula): Formula()
	data class IMPLIES(val leftFml: Formula, val rightFml: Formula): Formula()
	data class IFF(val leftFml: Formula, val rightFml: Formula): Formula()
	data class ALL(val bddVar: Var, val operandFml: Formula, val unificationTermInstantiationCount: Int = 0): Formula() {
		init {
			if (bddVar in operandFml.bddVars) { throw DuplicateBddVarException() }
		}
		fun instantiate(newTerm: Term): Formula = operandFml.replace(bddVar, newTerm)
		override fun equals(other: Any?): Boolean {
			if (this === other) return true
			if (javaClass != other?.javaClass) return false
			other as ALL
			if (operandFml == other.instantiate(bddVar)) return true
			return false
		}
		override fun hashCode(): Int {
			return javaClass.hashCode()
		}
	}
	data class EXISTS(val bddVar: Var, val operandFml: Formula, val unificationTermInstantiationCount: Int = 0): Formula() {
		init {
			if (bddVar in operandFml.bddVars) { throw DuplicateBddVarException() }
		}
		fun instantiate(newTerm: Term): Formula = operandFml.replace(bddVar, newTerm)
		override fun equals(other: Any?): Boolean {
			if (this === other) return true
			if (javaClass != other?.javaClass) return false
			other as EXISTS
			if (operandFml == other.instantiate(bddVar)) return true
			return false
		}
		override fun hashCode(): Int {
			return javaClass.hashCode()
		}
	}
	private fun recToString(): String = when(this) {
		TRUE 			-> "true"
		FALSE 			-> "false"
		is PREDICATE 	-> id + if (terms.isNotEmpty()) terms.joinToString(separator = ",", prefix = "(", postfix = ")") else ""
		is NOT 			-> "¬${operandFml.recToString()}"
		is AND 			-> {
			val rightFmlStr = if (rightFml is AND) rightFml.recToString().removeSurrounding("(", ")") else rightFml.recToString()
			"(${leftFml.recToString()} ∧ $rightFmlStr)"
		}
		is OR 			-> {
			val rightFmlStr = if (rightFml is OR) rightFml.recToString().removeSurrounding("(", ")") else rightFml.recToString()
			"(${leftFml.recToString()} ∨ $rightFmlStr)"
		}
		is IMPLIES 		-> "(${leftFml.recToString()} → ${rightFml.recToString()})"
		is IFF 			-> "(${leftFml.recToString()} ↔ ${rightFml.recToString()})"
		is ALL 			-> "∀$bddVar${operandFml.recToString()}"
		is EXISTS 		-> "∃$bddVar${operandFml.recToString()}"
	}
	final override fun toString(): String = recToString().removeSurrounding("(", ")")
	fun toLatex(): String = toString()
		.replace("true", "\\top")
		.replace("false", "\\bot")
		.replace("¬", "\\neg ")
		.replace("∧", "\\land")
		.replace("∨", "\\or")
		.replace("→", "\\rightarrow")
		.replace("↔", "\\leftrightarrow")
		.replace("∀", "\\forall ")
		.replace("∃", "\\exists ")
	val freeVars: Set<Var>
		get() = when (this) {
			TRUE 			-> emptySet()
			FALSE 			-> emptySet()
			is PREDICATE 	-> terms.map { it.freeVars }.flatten().toSet()
			is NOT 			-> operandFml.freeVars
			is AND 			-> leftFml.freeVars + rightFml.freeVars
			is OR 			-> leftFml.freeVars + rightFml.freeVars
			is IMPLIES 		-> leftFml.freeVars + rightFml.freeVars
			is IFF 			-> leftFml.freeVars + rightFml.freeVars
			is ALL 			-> operandFml.freeVars.minus(bddVar)
			is EXISTS 		-> operandFml.freeVars.minus(bddVar)
		}
	val bddVars: Set<Var>
		get() = when (this) {
			TRUE 			-> emptySet()
			FALSE 			-> emptySet()
			is PREDICATE 	-> emptySet()
			is NOT 			-> operandFml.bddVars
			is AND 			-> leftFml.bddVars + leftFml.bddVars
			is OR 			-> leftFml.bddVars + leftFml.bddVars
			is IMPLIES 		-> leftFml.bddVars + leftFml.bddVars
			is IFF 			-> leftFml.bddVars + leftFml.bddVars
			is ALL 			-> operandFml.bddVars + bddVar
			is EXISTS 		-> operandFml.bddVars + bddVar
		}
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
	fun replace(oldVar: Var, newTerm: Term): Formula = when(this) {
		TRUE 			-> this
		FALSE 			-> this
		is PREDICATE 	-> PREDICATE(id, terms.map { it.replace(oldVar, newTerm) })
		is NOT 			-> NOT		(operandFml.replace(oldVar, newTerm))
		is AND 			-> AND		(leftFml.replace(oldVar, newTerm), rightFml.replace(oldVar, newTerm))
		is OR 			-> OR		(leftFml.replace(oldVar, newTerm), rightFml.replace(oldVar, newTerm))
		is IMPLIES 		-> IMPLIES	(leftFml.replace(oldVar, newTerm), rightFml.replace(oldVar, newTerm))
		is IFF 			-> IFF		(leftFml.replace(oldVar, newTerm), rightFml.replace(oldVar, newTerm))
		is ALL -> {
			if (oldVar == bddVar) {
				this
			} else if (bddVar in newTerm.freeVars && oldVar in freeVars) {
				val newBddVar = bddVar.getFreshVar(operandFml.bddVars + operandFml.freeVars + newTerm.freeVars)
				this.copy(
					bddVar = newBddVar,
					operandFml = operandFml.replace(bddVar, newBddVar).replace(oldVar, newTerm)
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
					bddVar = newBddVar,
					operandFml = operandFml.replace(bddVar, newBddVar).replace(oldVar, newTerm)
				)
			} else {
				this.copy(
					operandFml = operandFml.replace(oldVar, newTerm)
				)
			}
		}
	}
	private fun replace(oldUnificationTerm: UnificationTerm, newTerm: Term): Formula = when(this) {
		TRUE -> this
		FALSE -> this
		is PREDICATE -> PREDICATE(id, terms.map { it.replace(oldUnificationTerm, newTerm) })
		is NOT 			-> NOT		(operandFml.replace(oldUnificationTerm, newTerm))
		is AND 			-> AND		(leftFml.replace(oldUnificationTerm, newTerm), rightFml.replace(oldUnificationTerm, newTerm))
		is OR 			-> OR		(leftFml.replace(oldUnificationTerm, newTerm), rightFml.replace(oldUnificationTerm, newTerm))
		is IMPLIES 		-> IMPLIES	(leftFml.replace(oldUnificationTerm, newTerm), rightFml.replace(oldUnificationTerm, newTerm))
		is IFF 			-> IFF		(leftFml.replace(oldUnificationTerm, newTerm), rightFml.replace(oldUnificationTerm, newTerm))
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
}

