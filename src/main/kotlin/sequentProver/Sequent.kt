package sequentProver

import core.*

class DuplicateAssumptionException: Exception()
class DuplicateConclusionException: Exception()

data class Sequent(val assumptions: List<Formula>, val conclusions: List<Formula>) {
	init {
		if (assumptions.distinct().size < assumptions.size) { throw DuplicateAssumptionException() }
		if (conclusions.distinct().size < conclusions.size) { throw DuplicateConclusionException() }
	}
	constructor(conclusions: List<Formula>) : this(emptyList(), conclusions)
	override fun toString() = assumptions.joinToString(separator = ", ") + " ⊢ " + conclusions.joinToString(separator = ", ")
	// TODO: 2021/12/07 which is better?
	// = (if (assumptions.isNotEmpty()) assumptions.joinToString(separator = ", ", postfix = " ") else "") + "⊢ " + "$conclusions"
	val freeVars: Set<Var> = (assumptions + conclusions).map { it.freeVars }.flatten().toSet()
}

typealias Sequents = List<Sequent>

fun Sequent.toGoals(): Sequents = listOf(this)
// TODO: 2021/12/07 which is better?

fun Sequents.replace(vararg newFirstSequents: Sequent): Sequents = newFirstSequents.toList() + this.drop(1)
