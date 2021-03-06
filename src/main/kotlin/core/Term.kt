package core

sealed class Term {
	data class Var(internal val id: String) : Term() {
		fun getFreshVar(oldVars: Set<Var>): Var {
			if (this !in oldVars) {
				return this
			}
			val regex = "_\\d+".toRegex()
			val preId = regex.replace(id, "")
			var n = regex.find(id)?.value?.drop(1)?.toInt() ?: 1
			while (true) {
				val newVar = Var(preId + "_$n")
				if (newVar !in oldVars) {
					return newVar
				}
				n++
			}
		}
	}

	data class UnificationTerm(val id: Int, val availableVars: Set<Var>) : Term()
	data class Function(val id: String, val terms: List<Term>) : Term()
	object Dummy : Term()

	final override fun toString(): String = when (this) {
		is Var -> id
		is UnificationTerm -> "t_$id" + availableVars.joinToString(separator = ",", prefix = "(", postfix = ")")
		is Function -> id + terms.joinToString(separator = ",", prefix = "(", postfix = ")")
		Dummy -> "\\_"
	}

	val freeVars: Set<Var>
		get() = when (this) {
			is Var -> setOf(this)
			is UnificationTerm -> availableVars
			is Function -> terms.map { it.freeVars }.flatten().toSet()
			Dummy -> emptySet()
		}
	val unificationTerms: Set<UnificationTerm>
		get() = when (this) {
			is Var -> emptySet()
			is UnificationTerm -> setOf(this)
			is Function -> terms.map { it.unificationTerms }.flatten().toSet()
			Dummy -> emptySet()
		}
	val functionIds: Set<String>
		get() = when (this) {
			is Var -> emptySet()
			is UnificationTerm -> emptySet()
			is Function -> setOf(id) + terms.map { it.functionIds }.flatten()
			Dummy -> emptySet()
		}

	fun replace(oldVar: Var, newTerm: Term): Term = when (this) {
		is Var -> if (this == oldVar) newTerm else this
		is UnificationTerm -> this
		is Function -> Function(id, terms.map { it.replace(oldVar, newTerm) })
		Dummy -> this
	}

	fun replace(oldUnificationTerm: UnificationTerm, newTerm: Term): Term = when (this) {
		is Var -> this
		is UnificationTerm -> if (this == oldUnificationTerm) newTerm else this
		is Function -> Function(id, terms.map { it.replace(oldUnificationTerm, newTerm) })
		Dummy -> this
	}

	fun replace(substitution: Substitution): Term {
		var result = this
		substitution.forEach { (key, value) -> result = result.replace(key, value) }
		return result
	}
}

typealias Substitution = Map<Term.UnificationTerm, Term>
typealias Substitutions = List<Substitution>
