package sequentProver

import core.*
import core.Term.*

data class Sequent(val assumptions: Set<Formula>, val conclusions: Set<Formula>) {
	constructor(conclusions: Set<Formula>) : this(emptySet(), conclusions)
	override fun toString() = assumptions.joinToString(separator = ", ") + " ⊢ " + conclusions.joinToString(separator = ", ")
	// TODO: 2021/12/07 which is better?
	// = (if (assumptions.isNotEmpty()) assumptions.joinToString(separator = ", ", postfix = " ") else "") + "⊢ " + "$conclusions"
	val freeVars: Set<Var> = (assumptions + conclusions).map { it.freeVars }.flatten().toSet()
}

typealias Sequents = List<Sequent>

fun Sequent.toSequents(): Sequents = listOf(this)
// TODO: 2021/12/07 which is better?

fun Sequents.replaceFirst(vararg newFirstSequents: Sequent): Sequents = newFirstSequents.toList() + this.drop(1)
