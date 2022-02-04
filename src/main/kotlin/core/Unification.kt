package core

import core.Term.*

fun unify(pairs: List<Pair<Term, Term>>): Substitution? = emptyMap<UnificationTerm, Term>().unify(pairs)

private fun Substitution.unify(pairs: List<Pair<Term, Term>>): Substitution? {
	if (pairs.isEmpty()) return this
	val (first, second) = pairs.first()
	when {
		first is Var && second is Var -> return if (first == second) {
			unify(pairs.drop(1))
		} else {
			null
		}
		first is Term.Function && second is Term.Function ->
			return if (first.id == second.id && first.terms.size == second.terms.size) {
				unify(first.terms.zip(second.terms) + pairs.drop(1))
			} else {
				null
			}
		first is Var && second is Term.Function -> return null
		first is Term.Function && second is Var -> return null
		first is UnificationTerm -> {
			if (first in this.keys) {
				return unify(listOf(this[first]!! to second) + pairs.drop(1))
			}
			val second1 = second.replace(this)
			if (first in second1.unificationTerms) return null
			val unificationTermToShrink = second1.unificationTerms.filter { it.availableVars.size > first.availableVars.size }
			val unificationTermToShrinkMap = unificationTermToShrink.associateWith { UnificationTerm(it.id, first.availableVars) }
			val second2 = second1.replace(unificationTermToShrinkMap)
			if (!first.freeVars.containsAll(second2.freeVars)) return null
			val additionalSubstitution = mapOf(first to second2) + unificationTermToShrinkMap
			// TODO: 2022/02/04 .update(additionalSubstitution)みたな関数を定義する？
			val newMap = this.map { it.key to it.value.replace(additionalSubstitution) }.toMap() + additionalSubstitution
			return newMap.unify(pairs.drop(1))
		}
		second is UnificationTerm -> return unify(listOf(second to first) + pairs.drop(1))
		else -> throw IllegalArgumentException()
	}
}

fun getSubstitution(substitutionsList: List<List<Substitution>>): Substitution? = emptyMap<UnificationTerm, Term>().getSubstitution(substitutionsList)

private fun Substitution.getSubstitution(substitutionsList: List<List<Substitution>>): Substitution? {
	var index = 0
	if (substitutionsList.isEmpty()) return this
	val substitutions = substitutionsList.first()
	while (index < substitutions.size) {
		val pairs = substitutions[index].toList()
		val substitution1 = this.unify(pairs)
		if (substitution1 == null) {
			index++
			continue
		}
		val substitution2 = substitution1.getSubstitution(substitutionsList.drop(1))
		if (substitution2 == null) {
			index++
			continue
		}
		return substitution2
	}
	return null
}
