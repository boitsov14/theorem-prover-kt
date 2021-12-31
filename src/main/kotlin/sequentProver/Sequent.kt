package sequentProver

import core.*

class DuplicateAssumptionException: Exception()

data class Goal(val fixedVars: List<Var>, val assumptions: List<Formula>, val conclusions: List<Formula>) {
	init {
		if (assumptions.distinct().size < assumptions.size
			|| conclusions.distinct().size < conclusions.size
			|| fixedVars.distinct().size < fixedVars.size
		) { throw DuplicateAssumptionException() }
	}
	constructor(assumptions: List<Formula>, conclusions: List<Formula>) : this(emptyList(), assumptions, conclusions)
	constructor(conclusions: List<Formula>) : this(emptyList(), conclusions)
	override fun toString() = assumptions.joinToString(separator = ", ") + " ⊢ " + conclusions.joinToString(separator = ", ")
	// TODO: 2021/12/07 which is better?
	// = (if (assumptions.isNotEmpty()) assumptions.joinToString(separator = ", ", postfix = " ") else "") + "⊢ " + "$conclusions"
}

typealias Goals = List<Goal>

fun Goal.toGoals(): Goals = listOf(this)
// TODO: 2021/12/07 which is better?

fun Goals.replace(vararg newFirstGoals: Goal): Goals = newFirstGoals.toList() + this.drop(1)
