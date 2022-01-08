package tacticGame

import core.*

class DuplicateAssumptionException: Exception()

data class Goal(val assumptions: List<Formula>, val conclusion: Formula) {
	init {
		if (assumptions.distinct().size < assumptions.size) { throw DuplicateAssumptionException() }
	}
	constructor(conclusion: Formula) : this(emptyList(), conclusion)
	override fun toString() = (if (assumptions.isNotEmpty()) assumptions.joinToString(separator = ", ", postfix = " ") else "") + "⊢ " + "$conclusion"
	val freeVars: Set<Var> = assumptions.map { it.freeVars }.flatten().toSet() + conclusion.freeVars
	fun toGoals():Goals = listOf(this)
}

typealias Goals = List<Goal>

fun Goals.replaceFirst(vararg newFirstGoals: Goal): Goals = newFirstGoals.toList() + this.drop(1)
