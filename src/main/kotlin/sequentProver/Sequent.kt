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

	val freeVars: Set<Var> = (assumptions + conclusions).map { it.freeVars }.flatten().toSet()

	// TODO: 2022/12/01 返値の型はMapではなくListにすべきでは
	fun getSubstitutions(): Substitutions {
		val result = mutableListOf<Substitution>()
		val assumptions = this.assumptions.filterIsInstance<PREDICATE>()
		val conclusions = this.conclusions.filterIsInstance<PREDICATE>()
		for (assumption in assumptions) {
			for (conclusion in conclusions) {
				// TODO: 2022/12/01 ここの条件なくてもよくない？
				if (assumption.id != conclusion.id || assumption.terms.size != conclusion.terms.size) continue
				val substitution = unify(assumption.terms.zip(conclusion.terms))
				if (substitution != null) {
					result.add(substitution)
				}
			}
		}
		return result
	}
}
