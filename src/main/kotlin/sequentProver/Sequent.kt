package sequentProver

import core.*
import core.Term.*
import core.Formula.*

data class Sequent(val assumptions: Set<Formula>, val conclusions: Set<Formula>) {
	override fun toString() =
		assumptions.joinToString(separator = ", ") + " ⊢ " + conclusions.joinToString(separator = ", ")

	fun toLatex() =
		assumptions.joinToString(separator = ", ") { it.toLatex() } + """\fCenter """ + conclusions.joinToString(
			separator = ", "
		) { it.toLatex() }

	val freeVars: Set<Var>
		get() = (assumptions + conclusions).flatMap { it.freeVars }.toSet()

	// TODO: 2022/12/01 返値の型はMapではなくListにすべきでは
	fun getSubstitutions(): Substitutions {
		val substitutions = mutableListOf<Substitution>()
		for (assumption in assumptions.filterIsInstance<PREDICATE>()) for (conclusion in conclusions.filterIsInstance<PREDICATE>()) {
			if (assumption.id != conclusion.id || assumption.terms.size != conclusion.terms.size) continue
			val substitution = unify(assumption.terms.zip(conclusion.terms)) ?: continue
			substitutions.add(substitution)
		}
		return substitutions
	}
}
