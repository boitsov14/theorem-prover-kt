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
		first is Term.Function && second is Term.Function -> return if (first.id == second.id && first.terms.size == second.terms.size) {
			unify(first.terms.zip(second.terms) + pairs.drop(1))
		} else {
			null
		}
		first is Var && second is Term.Function -> return null
		first is Term.Function && second is Var -> return null
		first is UnificationTerm -> {
			if (first in this.keys) {
				// TODO: 2022/02/05 仮に不完全なsubstitutionでもこれで問題ないと思う． 毎回フルでやるのは効率悪い．
				return unify(listOf(this[first]!! to second) + pairs.drop(1))
			}
			val newSecond = second.replace(this)
			if (first == newSecond) return unify(pairs.drop(1))
			if (first in newSecond.unificationTerms) return null
			// TODO: 2022/02/05 本当にこのfilterでよいのかチェック
			val unificationTermShrinkMap =
				newSecond.unificationTerms.filter { it.availableVars.size > first.availableVars.size }
					.associateWith { UnificationTerm(it.id, first.availableVars) }
			if (!first.availableVars.containsAll(newSecond.replace(unificationTermShrinkMap).freeVars)) return null
			return (this + (first to newSecond) + unificationTermShrinkMap).unify(pairs.drop(1))
		}
		second is UnificationTerm -> return unify(listOf(second to first) + pairs.drop(1))
		else -> throw IllegalArgumentException()
	}
}

fun getSubstitution(substitutionsList: List<List<Substitution>>): Substitution? =
	emptyMap<UnificationTerm, Term>().getSubstitution(substitutionsList)

private fun Substitution.getSubstitution(substitutionsList: List<List<Substitution>>): Substitution? {
	var index = 0
	if (substitutionsList.isEmpty()) return this
	val substitutions = substitutionsList.first()
	while (index < substitutions.size) {
		val pairs = substitutions[index].toList()
		val ownSubstitution = this.unify(pairs)
		if (ownSubstitution == null) {
			index++
			continue
		}
		val nextSubstitution = ownSubstitution.getSubstitution(substitutionsList.drop(1))
		if (nextSubstitution == null) {
			index++
			continue
		}
		return nextSubstitution
	}
	return null
}

fun Substitution.getCompleteSubstitution(): Substitution =
	this.toList().mapIndexed { index, pair -> pair.first to pair.second.replace(this.toList().drop(index + 1).toMap()) }
		.toMap()
