package goal

import formula.*

class DuplicateAssumptionException: Exception()

data class Goal(val fixedVars: List<Var>, val assumptions: List<Formula>, val conclusion: Formula) {
	init {
		if (assumptions.distinct().size < assumptions.size
			|| fixedVars.distinct().size < fixedVars.size
		) { throw DuplicateAssumptionException() }
	}
	constructor(assumptions: List<Formula>, conclusion: Formula) : this(emptyList(), assumptions, conclusion)
	constructor(conclusion: Formula) : this(emptyList(), conclusion)
	override fun toString() = (if (assumptions.isNotEmpty()) assumptions.joinToString(separator = ", ", postfix = " ") else "") + "⊢ " + "$conclusion"
	fun toGoals():Goals = listOf(this)
}

typealias Goals = List<Goal>

fun Goals.replace(vararg newFirstGoals: Goal): Goals = newFirstGoals.toList() + this.drop(1)
