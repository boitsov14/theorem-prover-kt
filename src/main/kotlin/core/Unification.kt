package core

import core.Term.*
import kotlinx.coroutines.*

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

suspend fun getSubstitution(substitutionsList: List<Substitutions>): Substitution? =
	emptyMap<UnificationTerm, Term>().getSubstitutionAsync(substitutionsList)

private fun Substitution.getSubstitution(substitutionsList: List<Substitutions>): Substitution? =
	if (substitutionsList.isEmpty()) this
	else substitutionsList.first().asSequence().map { this.unify(it.toList()) }.filterNotNull()
		.map { it.getSubstitution(substitutionsList.drop(1)) }.filterNotNull().firstOrNull()

private suspend fun Substitution.getSubstitutionAsync(substitutionsList: List<Substitutions>): Substitution? =
	coroutineScope {
		val substitutions = substitutionsList.firstOrNull() ?: return@coroutineScope this@getSubstitutionAsync
		substitutions.map {
			async {
				val substitution = this@getSubstitutionAsync.unify(it.toList()) ?: return@async null
				substitution.getSubstitutionAsync1(substitutionsList.drop(1))
			}
		}.awaitAll().filterNotNull().firstOrNull()
	}

private suspend fun Substitution.getSubstitutionAsync1(substitutionsList: List<Substitutions>): Substitution? =
	coroutineScope {
		val substitutions = substitutionsList.firstOrNull() ?: return@coroutineScope this@getSubstitutionAsync1
		substitutions.map {
			async {
				val substitution = this@getSubstitutionAsync1.unify(it.toList()) ?: return@async null
				substitution.getSubstitution(substitutionsList.drop(1))
			}
		}.awaitAll().filterNotNull().firstOrNull()
	}

// TODO: 2022/07/23 mapvaluesに変える？
fun Substitution.getCompleteSubstitution(): Substitution =
	this.toList().mapIndexed { index, pair -> pair.first to pair.second.replace(this.toList().drop(index + 1).toMap()) }
		.toMap()
