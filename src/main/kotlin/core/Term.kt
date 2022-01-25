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
	data class UnificationTerm(val id: Int, val availableVars: Set<Var>): Term()
	data class Function(val id: String, val terms: List<Term>): Term()
	final override fun toString(): String = when(this) {
		is Var -> id
		is UnificationTerm -> "t_$id" + availableVars.joinToString(separator = ",", prefix = "(", postfix = ")")
		is Function -> id + terms.joinToString(separator = ",", prefix = "(", postfix = ")")
	}
	val freeVars: Set<Var>
		get() = when (this) {
			is Var -> setOf(this)
			is UnificationTerm -> availableVars
			// TODO: 2022/01/17 availableVarsにするかemptySetにするか
			is Function -> terms.map { it.freeVars }.flatten().toSet()
		}
	val unificationTerm: Set<UnificationTerm>
		get() = when (this) {
			is Var -> emptySet()
			is UnificationTerm -> setOf(this)
			is Function -> terms.map { it.unificationTerm }.flatten().toSet()
		}
	fun replace(oldVar: Var, newTerm: Term): Term = when(this) {
		is Var -> if (this == oldVar) newTerm else this
		is UnificationTerm -> this
		is Function -> Function(id, terms.map { it.replace(oldVar, newTerm) })
	}
	fun replace(oldUnificationTerm: UnificationTerm, newTerm: Term): Term = when(this) {
		is Var -> this
		is UnificationTerm -> if (this == oldUnificationTerm) newTerm else this
		is Function -> Function(id, terms.map { it.replace(oldUnificationTerm, newTerm) })
	}
}
