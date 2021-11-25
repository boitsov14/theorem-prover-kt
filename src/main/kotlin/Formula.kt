package core.formula

data class Var(private val id: String) {
	override fun toString() = id
	fun getUniqueVar(oldVars: Set<Var>): Var {
		if (this !in oldVars) { return this }
		var n = 1
		while (true) {
			val newVar = Var(this.id + "_$n")
			if (newVar !in oldVars) { return newVar }
			n++
		}
	}
}

class DuplicateBddVarException: Exception()

sealed class Formula {
	object FALSE: Formula()
	data class PREDICATE(val id: String, val vars: List<Var>): Formula()
	data class NOT(val operandFml: Formula): Formula()
	data class AND(val leftFml: Formula, val rightFml: Formula): Formula()
	data class OR(val leftFml: Formula, val rightFml: Formula): Formula()
	data class IMPLIES(val leftFml: Formula, val rightFml: Formula): Formula()
	data class IFF(val leftFml: Formula, val rightFml: Formula): Formula()
	data class ALL(val bddVar: Var, val operandFml: Formula): Formula() {
		init {
			if (bddVar in operandFml.bddVars) { throw DuplicateBddVarException() }
		}
		override fun equals(other: Any?): Boolean {
			if (this === other) return true
			if (javaClass != other?.javaClass) return false
			other as ALL
			if (operandFml == other.operandFml.replace(other.bddVar, bddVar)) return true
			return false
		}
		override fun hashCode(): Int {
			return javaClass.hashCode()
		}
	}
	data class EXISTS(val bddVar: Var, val operandFml: Formula): Formula() {
		init {
			if (bddVar in operandFml.bddVars) { throw DuplicateBddVarException() }
		}
		override fun equals(other: Any?): Boolean {
			if (this === other) return true
			if (javaClass != other?.javaClass) return false
			other as EXISTS
			if (operandFml == other.operandFml.replace(other.bddVar, bddVar)) return true
			return false
		}
		override fun hashCode(): Int {
			return javaClass.hashCode()
		}
	}
	private fun recursiveToString(): String = when(this) {
		FALSE 			-> "false"
		is PREDICATE 	-> id + if (vars.isNotEmpty()) vars.joinToString(separator = " ", prefix = " ") else ""
		is NOT 			-> "(¬${operandFml.recursiveToString()})"
		is AND 			-> "(${leftFml.recursiveToString()} ∧ ${rightFml.recursiveToString()})"
		is OR 			-> "(${leftFml.recursiveToString()} ∨ ${rightFml.recursiveToString()})"
		is IMPLIES 		-> "(${leftFml.recursiveToString()} → ${rightFml.recursiveToString()})"
		is IFF 			-> "(${leftFml.recursiveToString()} ↔ ${rightFml.recursiveToString()})"
		is ALL 			-> "(∀$bddVar, ${operandFml.recursiveToString()})"
		is EXISTS 		-> "(∃$bddVar, ${operandFml.recursiveToString()})"
	}
	final override fun toString(): String = recursiveToString().removeSurrounding("(", ")")
	val freeVars: Set<Var>
		get() = when (this) {
			FALSE 			-> emptySet()
			is PREDICATE 	-> vars.toSet()
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
	fun replace(oldVar: Var, newVar: Var): Formula = when(this) {
		FALSE 			-> this
		is PREDICATE 	-> PREDICATE(id, vars.map { if (it == oldVar) newVar else it })
		is NOT 			-> NOT		(operandFml.replace(oldVar, newVar))
		is AND 			-> AND		(leftFml.replace(oldVar, newVar), rightFml.replace(oldVar, newVar))
		is OR 			-> OR		(leftFml.replace(oldVar, newVar), rightFml.replace(oldVar, newVar))
		is IMPLIES 		-> IMPLIES	(leftFml.replace(oldVar, newVar), rightFml.replace(oldVar, newVar))
		is IFF 			-> IFF		(leftFml.replace(oldVar, newVar), rightFml.replace(oldVar, newVar))
		is ALL 			-> {
			if (oldVar == bddVar) {
				this
			} else if (newVar == bddVar) {
				val newBddVar = bddVar.getUniqueVar(operandFml.bddVars + operandFml.freeVars + newVar)
				ALL(newBddVar, operandFml.replace(bddVar, newBddVar).replace(oldVar, newVar))
			} else {
				ALL(bddVar, operandFml.replace(oldVar, newVar))
			}
		}
		is EXISTS 			-> {
			if (oldVar == bddVar) {
				this
			} else if (newVar == bddVar) {
				val newBddVar = bddVar.getUniqueVar(operandFml.bddVars + operandFml.freeVars + newVar)
				EXISTS(newBddVar, operandFml.replace(bddVar, newBddVar).replace(oldVar, newVar))
			} else {
				EXISTS(bddVar, operandFml.replace(oldVar, newVar))
			}
		}
	}
}

fun List<Formula>.addIfDistinct(newFml: Formula): List<Formula> = if (newFml !in this) this + newFml else this

fun List<Formula>.replaceIfDistinct(removedFml: Formula, vararg newFmls: Formula): List<Formula> {
	val index = this.indexOf(removedFml)
	val first = this.subList(0, index)
	val second = this.subList(index + 1, this.size)
	val newDistinctFmls = mutableListOf<Formula>()
	for (newFml in newFmls) {
		if (newFml !in first + newDistinctFmls + second) {
			newDistinctFmls.add(newFml)
		}
	}
	return first + newDistinctFmls + second
}

data class Goal(val fixedVars: List<Var>, val assumptions: List<Formula>, val conclusion: Formula) {
	constructor(assumptions: List<Formula>, conclusion: Formula) : this(emptyList(), assumptions, conclusion)
	constructor(conclusion: Formula) : this(emptyList(), conclusion)
	// TODO: 2021/10/31 Do we need these constructor?
	override fun toString() = (if (assumptions.isNotEmpty()) assumptions.joinToString(separator = ", ", postfix = " ") else "") + "⊢ " + "$conclusion"
	fun toGoals():Goals = listOf(this)
}

typealias Goals = List<Goal>

fun Goals.replace(vararg newFirstGoals: Goal): Goals = newFirstGoals.toList() + this.drop(1)
