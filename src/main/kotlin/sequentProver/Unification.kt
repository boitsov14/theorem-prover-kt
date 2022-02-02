package sequentProver

import core.*
import core.Term.*
import core.Formula.*

fun Sequent.unify(): List<Map<UnificationTerm, Term>> {
	val result = mutableListOf<Map<UnificationTerm, Term>>()
	val assumptions = this.assumptions.filterIsInstance<PREDICATE>()
	val conclusions = this.conclusions.filterIsInstance<PREDICATE>()
	for (assumption in assumptions) {
		for (conclusion in conclusions) {
			if (assumption.id != conclusion.id || assumption.terms.size != conclusion.terms.size) continue
			val substitution = unify(assumption.terms.zip(conclusion.terms))
			if (substitution != null) {
				result.add(substitution)
			}
		}
	}
	return result
}
