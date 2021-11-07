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
	data class NOT(val fml: Formula): Formula()
	data class AND(val leftFml: Formula, val rightFml: Formula): Formula()
	data class OR(val leftFml: Formula, val rightFml: Formula): Formula()
	data class IMPLIES(val leftFml: Formula, val rightFml: Formula): Formula()
	data class IFF(val leftFml: Formula, val rightFml: Formula): Formula()
	data class ALL(val bddVar: Var, val fml: Formula): Formula() {
		init {
			if (bddVar in fml.bddVars) { throw DuplicateBddVarException() }
		}
		override fun equals(other: Any?): Boolean {
			if (this === other) return true
			if (javaClass != other?.javaClass) return false
			other as ALL
			if (fml == other.fml.replace(other.bddVar, bddVar)) return true
			return false
		}
		override fun hashCode(): Int {
			return javaClass.hashCode()
		}
	}
	data class EXISTS(val bddVar: Var, val fml: Formula): Formula() {
		init {
			if (bddVar in fml.bddVars) { throw DuplicateBddVarException() }
		}
		override fun equals(other: Any?): Boolean {
			if (this === other) return true
			if (javaClass != other?.javaClass) return false
			other as EXISTS
			if (fml == other.fml.replace(other.bddVar, bddVar)) return true
			return false
		}
		override fun hashCode(): Int {
			return javaClass.hashCode()
		}
	}
	private fun recursiveToString(): String = when(this) {
		FALSE 			-> "false"
		is PREDICATE 	-> id + if (vars.isNotEmpty()) vars.joinToString(separator = " ", prefix = " ") else ""
		is NOT 			-> "(¬${fml.recursiveToString()})"
		is AND 			-> "(${leftFml.recursiveToString()} ∧ ${rightFml.recursiveToString()})"
		is OR 			-> "(${leftFml.recursiveToString()} ∨ ${rightFml.recursiveToString()})"
		is IMPLIES 		-> "(${leftFml.recursiveToString()} → ${rightFml.recursiveToString()})"
		is IFF 			-> "(${leftFml.recursiveToString()} ↔ ${rightFml.recursiveToString()})"
		is ALL 			-> "(∀$bddVar, ${fml.recursiveToString()})"
		is EXISTS 		-> "(∃$bddVar, ${fml.recursiveToString()})"
	}
	final override fun toString(): String = recursiveToString().removeSurrounding("(", ")")
	val freeVars: Set<Var>
		get() = when (this) {
			FALSE 			-> setOf()
			is PREDICATE 	-> vars.toSet()
			is NOT 			-> fml.freeVars
			is AND 			-> leftFml.freeVars + rightFml.freeVars
			is OR 			-> leftFml.freeVars + rightFml.freeVars
			is IMPLIES 		-> leftFml.freeVars + rightFml.freeVars
			is IFF 			-> leftFml.freeVars + rightFml.freeVars
			is ALL 			-> fml.freeVars.minus(bddVar)
			is EXISTS 		-> fml.freeVars.minus(bddVar)
		}
	val bddVars: Set<Var>
		get() = when (this) {
			FALSE 			-> setOf()
			is PREDICATE 	-> setOf()
			is NOT 			-> fml.bddVars
			is AND 			-> leftFml.bddVars + leftFml.bddVars
			is OR 			-> leftFml.bddVars + leftFml.bddVars
			is IMPLIES 		-> leftFml.bddVars + leftFml.bddVars
			is IFF 			-> leftFml.bddVars + leftFml.bddVars
			is ALL 			-> fml.bddVars + bddVar
			is EXISTS 		-> fml.bddVars + bddVar
		}
	fun replace(oldVar: Var, newVar: Var): Formula = when(this) {
		FALSE 			-> this
		is PREDICATE 	-> PREDICATE(id, vars.map { if (it == oldVar) newVar else it })
		is NOT 			-> NOT		(fml.replace(oldVar, newVar))
		is AND 			-> AND		(leftFml.replace(oldVar, newVar), rightFml.replace(oldVar, newVar))
		is OR 			-> OR		(leftFml.replace(oldVar, newVar), rightFml.replace(oldVar, newVar))
		is IMPLIES 		-> IMPLIES	(leftFml.replace(oldVar, newVar), rightFml.replace(oldVar, newVar))
		is IFF 			-> IFF		(leftFml.replace(oldVar, newVar), rightFml.replace(oldVar, newVar))
		is ALL 			-> {
			if (bddVar == oldVar || bddVar == newVar) {
				throw DuplicateBddVarException()
			}
			ALL(bddVar, fml.replace(oldVar, newVar))
		}
		is EXISTS 		-> {
			if (bddVar == oldVar || bddVar == newVar) {
				throw DuplicateBddVarException()
			}
			EXISTS(bddVar, fml.replace(oldVar, newVar))
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
	constructor(assumptions: List<Formula>, conclusion: Formula) : this(listOf(), assumptions, conclusion)
	constructor(conclusion: Formula) : this(listOf(), conclusion)
	// TODO: 2021/10/31 Do we need these constructor?
	override fun toString() = (if (assumptions.isNotEmpty()) assumptions.joinToString(separator = ", ", postfix = " ") else "") + "⊢ " + "$conclusion"
	//fun getAllBddVars(): Set<Var> = assumptions.map { it.bddVars() }.flatten().toSet() + conclusion.bddVars()
	// TODO: 2021/10/28 Do we need this?
}

typealias Goals = List<Goal>

fun Goals.replaceFirstGoal(vararg newFirstGoals: Goal): Goals = newFirstGoals.toList() + this.drop(1)
