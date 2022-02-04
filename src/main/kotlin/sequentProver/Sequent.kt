package sequentProver

import core.*
import core.Term.*

data class Sequent(val assumptions: Set<Formula>, val conclusions: Set<Formula>) {
	override fun toString() = assumptions.joinToString(separator = ", ") + " ⊢ " + conclusions.joinToString(separator = ", ")
	fun toLatex() = assumptions.joinToString(separator = ", ") { it.toLatex() } + " \\ \\fCenter \\ " + conclusions.joinToString(separator = ", ") { it.toLatex() }
	val freeVars: Set<Var> = (assumptions + conclusions).map { it.freeVars }.flatten().toSet()
}
