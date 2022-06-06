package tacticGame

import core.*
import core.Term.*

data class Goal(val assumptions: Set<Formula>, val conclusion: Formula) {
	constructor(conclusion: Formula) : this(emptySet(), conclusion)

	// TODO: 2022/01/09 constructorいらないかも
	override fun toString() = (if (assumptions.isNotEmpty()) assumptions.joinToString(
		separator = ", ",
		postfix = " "
	) else "") + "⊢ " + "$conclusion"

	val freeVars: Set<Var> = assumptions.map { it.freeVars }.flatten().toSet() + conclusion.freeVars
	fun toGoals(): Goals = listOf(this)
}

typealias Goals = List<Goal>

fun Goals.replaceFirst(vararg newFirstGoals: Goal): Goals = newFirstGoals.toList() + this.drop(1)
