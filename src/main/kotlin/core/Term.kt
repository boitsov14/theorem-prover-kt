package core

// TODO: 2022/01/09 varのidをpublicにするかどうか．

sealed class Term {
	data class Var(internal val id: String): Term() {
		fun getFreshVar(oldVars: Set<Var>): Var {
			if (this !in oldVars) { return this }
			var n = 1
			while (true) {
				val newVar = Var(id + "_$n")
				if (newVar !in oldVars) { return newVar }
				n++
			}
		}
	}
	data class UnificationTerm(val id: String, val unifiableVars: Set<Var>): Term() {
		fun getFreshUnificationTerm(oldUnificationTerms: Set<UnificationTerm>): UnificationTerm {
			val oldIDs = oldUnificationTerms.map { it.id }
			if (id !in oldIDs) { return this }
			var n = 1
			while (true) {
				val newID = id + "_$n"
				if (newID !in oldIDs) { return UnificationTerm(newID, unifiableVars) }
				n++
			}
		}
	}
	data class Function(val id: String, val terms: List<Term>): Term()
	final override fun toString(): String = when(this) {
		is Var -> id
		is UnificationTerm -> id + unifiableVars.joinToString(separator = ", ", prefix = "(", postfix = ")")
		is Function -> id + terms.joinToString(separator = ", ", prefix = "(", postfix = ")")
	}
	val freeVars: Set<Var>
		get() = when (this) {
			is Var -> setOf(this)
			is UnificationTerm -> unifiableVars
			is Function -> terms.map { it.freeVars }.flatten().toSet()
		}
	val freeUnificationTerm: Set<UnificationTerm>
		get() = when (this) {
			is Var -> emptySet()
			is UnificationTerm -> setOf(this)
			is Function -> terms.map { it.freeUnificationTerm }.flatten().toSet()
		}
}