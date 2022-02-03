package core

import core.Term.*

fun unify(pairs: List<Pair<Term, Term>>): Map<UnificationTerm,Term>? = emptyMap<UnificationTerm, Term>().unify(pairs)

private fun Map<UnificationTerm, Term>.unify(pairs: List<Pair<Term, Term>>): Map<UnificationTerm,Term>? {
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
			val additionalMap = mapOf(first to second2) + unificationTermToShrinkMap
			val newMap = this.map { it.key to it.value.replace(additionalMap) }.toMap() + additionalMap
			return newMap.unify(pairs.drop(1))
		}
		second is UnificationTerm -> return unify(listOf(second to first) + pairs.drop(1))
		else -> throw IllegalArgumentException()
	}
}

// TODO: 2022/02/03 typealiasでsubstitution作る？

@JvmName("unify1")
fun unify(substitutionsList: List<List<Map<UnificationTerm, Term>>>): Map<UnificationTerm,Term>? = emptyMap<UnificationTerm, Term>().unify(substitutionsList)

@JvmName("unifyUnificationTermTerm")
private fun Map<UnificationTerm, Term>.unify(substitutionsList: List<List<Map<UnificationTerm, Term>>>): Map<UnificationTerm, Term>? {
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
		val substitution2 = substitution1.unify(substitutionsList.drop(1))
		if (substitution2 == null) {
			index++
			continue
		}
		return substitution2
	}
	return null
}
