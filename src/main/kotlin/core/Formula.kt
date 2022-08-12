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

		final override fun hashCode(): Int = 31 * javaClass.hashCode() + operandFml.javaClass.hashCode()
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

	fun replace(substitution: Substitution): Formula =
		substitution.asIterable().fold(this) { tmp, (key, value) -> tmp.replace(key, value) }

	// TODO: 2022/07/21 check the errata!
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

	internal fun simplify(): Formula = when (this) {
		is NOT -> NOT(operandFml.simplify()).simplify0()
		is AND -> AND(leftFml.simplify(), rightFml.simplify()).simplify0()
		is OR -> OR(leftFml.simplify(), rightFml.simplify()).simplify0()
		is IMPLIES -> IMPLIES(leftFml.simplify(), rightFml.simplify()).simplify0()
		is IFF -> IFF(leftFml.simplify(), rightFml.simplify()).simplify0()
		else -> this
	}

	private fun negate(): Formula = if (this is NOT) operandFml else NOT(this)

	internal fun pureNNF(): Formula = when (this) {
		is NOT -> when (operandFml) {
			is NOT -> operandFml.operandFml.pureNNF()
			is AND -> OR(NOT(operandFml.leftFml).pureNNF(), NOT(operandFml.rightFml).pureNNF())
			is OR -> AND(NOT(operandFml.leftFml).pureNNF(), NOT(operandFml.rightFml).pureNNF())
			is IMPLIES -> AND(operandFml.leftFml.pureNNF(), NOT(operandFml.rightFml).pureNNF())
			is IFF -> OR(
				AND(operandFml.leftFml.pureNNF(), NOT(operandFml.rightFml).pureNNF()),
				AND(NOT(operandFml.leftFml).pureNNF(), operandFml.rightFml.pureNNF())
			)

			else -> this
		}

		is AND -> AND(leftFml.pureNNF(), rightFml.pureNNF())
		is OR -> OR(leftFml.pureNNF(), rightFml.pureNNF())
		is IMPLIES -> OR(NOT(leftFml).pureNNF(), rightFml.pureNNF())
		is IFF -> OR(AND(leftFml.pureNNF(), rightFml.pureNNF()), AND(NOT(leftFml).pureNNF(), NOT(rightFml).pureNNF()))
		else -> this
	}

	internal fun efficientNNF(): Formula = when (this) {
		is NOT -> when (operandFml) {
			is NOT -> operandFml.operandFml.efficientNNF()
			is AND -> OR(NOT(operandFml.leftFml).efficientNNF(), NOT(operandFml.rightFml).efficientNNF())
			is OR -> AND(NOT(operandFml.leftFml).efficientNNF(), NOT(operandFml.rightFml).efficientNNF())
			is IMPLIES -> AND(operandFml.leftFml.efficientNNF(), NOT(operandFml.rightFml).efficientNNF())
			is IFF -> IFF(operandFml.leftFml.efficientNNF(), NOT(operandFml.rightFml).efficientNNF())
			else -> this
		}

		is AND -> AND(leftFml.efficientNNF(), rightFml.efficientNNF())
		is OR -> OR(leftFml.efficientNNF(), rightFml.efficientNNF())
		is IMPLIES -> OR(NOT(leftFml).efficientNNF(), rightFml.efficientNNF())
		is IFF -> IFF(leftFml.efficientNNF(), rightFml.efficientNNF())
		else -> this
	}

	internal fun pureDNF(): Set<Set<Formula>> = when (this) {
		is AND -> distribute(leftFml.pureDNF(), rightFml.pureDNF())
		is OR -> leftFml.pureDNF() + rightFml.pureDNF()
		else -> setOf(setOf(this))
	}

	internal fun simpleDNF(): Set<Set<Formula>> = when (this) {
		TRUE -> setOf(emptySet())
		FALSE -> emptySet()
		else -> {
			val disjunctions = simplify().pureNNF().pureDNF().filterNot { isTrivial(it) }
			disjunctions.filter { d -> disjunctions.none { d0 -> d.containsAll(d0) && d0 != d } }.toSet()
		}
	}

	private fun pureCNF(): Set<Set<Formula>> = when (this) {
		is AND -> leftFml.pureCNF() + rightFml.pureCNF()
		is OR -> distribute(leftFml.pureCNF(), rightFml.pureCNF())
		else -> setOf(setOf(this))
	}

	internal fun simpleCNF(): Set<Set<Formula>> = when (this) {
		TRUE -> emptySet()
		FALSE -> setOf(emptySet())
		else -> {
			val conjunctions = simplify().pureNNF().pureCNF().filterNot { isTrivial(it) }
			conjunctions.filter { d -> conjunctions.none { d0 -> d.containsAll(d0) && d0 != d } }.toSet()
		}
	}

	private fun mainCNF(defs: Map<Formula, PREDICATE>, n: Int): Triple<Formula, Map<Formula, PREDICATE>, Int> =
		when (this) {
			is AND -> {
				val (fml0, defs0, n0) = leftFml.mainCNF(defs, n)
				val (fml1, defs1, n1) = rightFml.mainCNF(defs0, n0)
				val fml = AND(fml0, fml1)
				if (fml in defs1.keys) {
					Triple(defs1[fml]!!, defs1, n1)
				} else {
					val atom = PREDICATE("Def_$n1", emptyList())
					val newDefs = defs1 + (fml to atom)
					Triple(atom, newDefs, n1 + 1)
				}
			}

			is OR -> {
				val (fml0, defs0, n0) = leftFml.mainCNF(defs, n)
				val (fml1, defs1, n1) = rightFml.mainCNF(defs0, n0)
				val fml = OR(fml0, fml1)
				if (fml in defs1.keys) {
					Triple(defs1[fml]!!, defs1, n1)
				} else {
					val atom = PREDICATE("Def_$n1", emptyList())
					val newDefs = defs1 + (fml to atom)
					Triple(atom, newDefs, n1 + 1)
				}
			}

			is IFF -> {
				val (fml0, defs0, n0) = leftFml.mainCNF(defs, n)
				val (fml1, defs1, n1) = rightFml.mainCNF(defs0, n0)
				val fml = IFF(fml0, fml1)
				if (fml in defs1.keys) {
					Triple(defs1[fml]!!, defs1, n1)
				} else {
					val atom = PREDICATE("Def_$n1", emptyList())
					val newDefs = defs1 + (fml to atom)
					Triple(atom, newDefs, n1 + 1)
				}
			}

			else -> Triple(this, defs, n)
		}

	internal fun makeDefCNF(): Set<Set<Formula>> {
		val (fml, defs0, _) = simplify().efficientNNF().mainCNF(emptyMap(), 0)
		return defs0.map { (key, value) -> IFF(value, key).simpleCNF() }
			.reduce { acc, sets -> acc + sets } + fml.simpleCNF()
	}

	private fun subCNF(defs: Map<Formula, PREDICATE>, n: Int): Triple<Formula, Map<Formula, PREDICATE>, Int> =
		when (this) {
			is AND -> {
				val (fml0, defs0, n0) = leftFml.andCNF(defs, n)
				val (fml1, defs1, n1) = rightFml.andCNF(defs0, n0)
				Triple(AND(fml0, fml1), defs1, n1)
			}

			is OR -> {
				val (fml0, defs0, n0) = leftFml.orCNF(defs, n)
				val (fml1, defs1, n1) = rightFml.orCNF(defs0, n0)
				Triple(OR(fml0, fml1), defs1, n1)
			}

			else -> throw IllegalArgumentException()
		}

	private fun orCNF(defs: Map<Formula, PREDICATE>, n: Int): Triple<Formula, Map<Formula, PREDICATE>, Int> =
		when (this) {
			is OR -> {
				subCNF(defs, n)
			}

			else -> mainCNF(defs, n)
		}

	private fun andCNF(defs: Map<Formula, PREDICATE>, n: Int): Triple<Formula, Map<Formula, PREDICATE>, Int> =
		when (this) {
			is AND -> {
				subCNF(defs, n)
			}

			else -> orCNF(defs, n)
		}

	fun defCNF(): Set<Set<Formula>> {
		val (fml, defs0, _) = simplify().efficientNNF().andCNF(emptyMap(), 0)
		return defs0.map { (key, value) -> IFF(value, key).simpleCNF() }
			.fold(fml.simpleCNF()) { acc, sets -> acc + sets }
	}


}

private fun distribute(fmlsSet0: Set<Set<Formula>>, fmlsSet1: Set<Set<Formula>>): Set<Set<Formula>> {
	val result = mutableSetOf<Set<Formula>>()
	for (fmls0 in fmlsSet0) {
		for (fmls1 in fmlsSet1) {
			result.add(fmls0 + fmls1)
		}
	}
	return result
}

private fun isTrivial(fmls: Set<Formula>) =
	(fmls.filterIsInstance<Formula.NOT>().map { it.operandFml }.toSet() intersect fmls.filter { it !is Formula.NOT }
		.toSet()).isNotEmpty()

internal fun Iterable<Formula>.makeConjunction(): Formula =
	reversed().reduceOrNull { conj, fml -> Formula.AND(fml, conj) } ?: Formula.TRUE

internal fun Iterable<Formula>.makeDisjunction(): Formula =
	reversed().reduceOrNull { disj, fml -> Formula.OR(fml, disj) } ?: Formula.FALSE
