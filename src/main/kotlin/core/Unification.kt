package core

import core.Term.Var
import core.Term.UnificationTerm
import core.Term.Function
import kotlinx.coroutines.*

fun List<Pair<Term, Term>>.unify(): Substitution? = emptyMap<UnificationTerm, Term>().unify(this)

private tailrec fun Substitution.unify(pairs: List<Pair<Term, Term>>): Substitution? {
	if (pairs.isEmpty()) return this
	val (left, right) = pairs.first()
	val substitution = unify(left, right) ?: return null
	return (this + substitution).unify(pairs.drop(1))
}

private tailrec fun Substitution.unify(left: Term, right: Term): Substitution? {
	when {
		left == right -> return emptyMap()
		left is Var && right is Var -> return null
		left is Function && right is Function -> return if (left.id == right.id && left.terms.size == right.terms.size) unify(
			left.terms.zip(right.terms)
		)
		else null

		left is UnificationTerm -> {
			this[left]?.let { return unify(it, right) }
			val newRight = right.replace(this)
			if (newRight is Function && left in newRight.unificationTerms) return null
			val shrinkVars = newRight.unificationTerms.filter { it.availableVars.size > left.availableVars.size }
				.associateWith { it.copy(availableVars = left.availableVars) }
			return if (left.availableVars.containsAll(newRight.replace(shrinkVars).freeVars)) mapOf(left to newRight) + shrinkVars else null
		}

		right is UnificationTerm -> return unify(right, left)
		left is Var && right is Function -> return null
		left is Function && right is Var -> return null
		else -> throw IllegalArgumentException()
	}
}

const val ASYNC_DEPTH = 3

suspend fun List<Substitutions>.getSubstitution(): Substitution? =
	emptyMap<UnificationTerm, Term>().getSubstitutionAsync(this, ASYNC_DEPTH)

private suspend fun Substitution.getSubstitutionAsync(
	substitutionsList: List<Substitutions>, asyncDepth: Int
): Substitution? = if (asyncDepth == 0) getSubstitutionSync(substitutionsList)
else coroutineScope {
	val substitutions = substitutionsList.firstOrNull() ?: return@coroutineScope this@getSubstitutionAsync
	substitutions.map {
		async {
			val substitution = this@getSubstitutionAsync.unify(it.toList()) ?: return@async null
			substitution.getSubstitutionAsync(substitutionsList.drop(1), asyncDepth - 1)
		}
	}.awaitAll().filterNotNull().firstOrNull()
}

private fun Substitution.getSubstitutionSync(substitutionsList: List<Substitutions>): Substitution? =
	if (substitutionsList.isEmpty()) this
	else substitutionsList.first().asSequence().map { this.unify(it.toList()) }.filterNotNull()
		.map { it.getSubstitutionSync(substitutionsList.drop(1)) }.filterNotNull().firstOrNull()

// TODO: 2022/07/23 map valuesに変える？
fun Substitution.getCompleteSubstitution(): Substitution =
	this.toList().mapIndexed { index, pair -> pair.first to pair.second.replace(this.toList().drop(index + 1).toMap()) }
		.toMap()
