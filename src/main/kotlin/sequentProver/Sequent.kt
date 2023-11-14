package sequentProver

import core.Formula
import core.Formula.PREDICATE
import core.Substitution
import core.Substitutions
import core.Term.Var
import core.unify

data class Sequent(val assumptions: Set<Formula>, val conclusions: Set<Formula>) {
	override fun toString() =
		assumptions.joinToString(separator = ", ") + " ⊢ " + conclusions.joinToString(separator = ", ")

	fun toLatex() =
		assumptions.joinToString(separator = ", ") { it.toLatex() } + """\fCenter """ + conclusions.joinToString(
			separator = ", "
		) { it.toLatex() }

	val freeVars: Set<Var>
		get() = (assumptions + conclusions).flatMap { it.freeVars }.toSet()

	// TODO: 2022/12/25 unificationのファイルに移動
	fun getSubstitutions(): Substitutions {
		val substitutions = mutableListOf<Substitution>()
		for (assumption in assumptions.filterIsInstance<PREDICATE>()) for (conclusion in conclusions.filterIsInstance<PREDICATE>()) {
			if (assumption.id != conclusion.id || assumption.terms.size != conclusion.terms.size) continue
			val substitution = assumption.terms.zip(conclusion.terms).unify() ?: continue
			substitutions.add(substitution)
		}
		return substitutions
	}
}
