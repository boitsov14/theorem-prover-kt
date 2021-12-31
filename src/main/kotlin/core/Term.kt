package core

sealed interface Term
// TODO: 2021/12/31 make term

data class Var(private val id: String): Term {
	override fun toString() = id
	fun getUniqueVar(oldVars: Set<Var>): Var {
		if (this !in oldVars) { return this }
		var n = 1
		while (true) {
			val newVar = Var(this.id + "_$n")
			if (newVar !in oldVars) { return newVar }
			n++
		}
	}
}