data class Var(val id: String): SemiToken {
	override fun toString() = id
}

enum class UnaryConnective(val id: Char, override val precedence: Int): OperatorToken {
	NOT('¬',4);
	override fun toString() = "$id"
}

enum class BinaryConnective(val id: Char, override val precedence: Int): OperatorToken {
	IMPLY('→', 1),
	AND('∧', 3),
	OR('∨', 2),
	IFF('↔', 0);
	override fun toString() = "$id"
}

enum class Quantifier(val id: Char): SemiToken {
	FOR_ALL('∀'),
	THERE_EXISTS('∃');
	override fun toString() = "$id"
}

sealed class Formula {
	object False: Formula(), Token {
		override fun toString(): String = "false"
		const val id = '⊥'
	}
	data class PredicateFml(val predicate: Char, val vars: List<Var>): Formula(), Token {
		override fun toString() = "$predicate" + (if (vars.isNotEmpty()) " " else "") + vars.joinToString()
	}
	data class UnaryConnectiveFml(val connective: UnaryConnective, val formula: Formula): Formula() {
		override fun toString() = "($connective$formula)"
	}
	data class BinaryConnectiveFml(val connective: BinaryConnective, val leftFml: Formula, val rightFml: Formula): Formula() {
		override fun toString() = "($leftFml $connective $rightFml)"
	}
	data class QuantifiedFml(val quantifier: Quantifier, val bddVar: Var, val formula: Formula): Formula() {
		override fun toString() = "($quantifier $bddVar, $formula)"
		override fun equals(other: Any?): Boolean {
			if (this === other) return true
			if (javaClass != other?.javaClass) return false
			other as QuantifiedFml
			if (quantifier != other.quantifier) return false
			if (formula == other.formula.replace(other.bddVar, bddVar)) return true
			return false
		}
		override fun hashCode(): Int = quantifier.hashCode()
	}
	fun freeVars(): Set<Var> = when(this) {
		False -> setOf()
		is PredicateFml -> vars.toSet()
		is UnaryConnectiveFml -> formula.freeVars()
		is BinaryConnectiveFml -> leftFml.freeVars() + rightFml.freeVars()
		is QuantifiedFml -> formula.freeVars().filterNot { it == bddVar }.toSet()
	}
	fun bddVars(): Set<Var> = when(this) {
		False -> setOf()
		is PredicateFml -> setOf()
		is UnaryConnectiveFml -> formula.bddVars()
		is BinaryConnectiveFml -> leftFml.bddVars() + leftFml.bddVars()
		is QuantifiedFml -> formula.bddVars() + setOf(bddVar)
	}
	fun replace(old: Var, new: Var): Formula = when(this) {
		False -> this
		is PredicateFml -> PredicateFml(predicate, vars.map { if (it == old) new else it })
		is UnaryConnectiveFml -> UnaryConnectiveFml(connective, formula.replace(old, new))
		is BinaryConnectiveFml -> BinaryConnectiveFml(connective, leftFml.replace(old, new), rightFml.replace(old, new))
		is QuantifiedFml -> QuantifiedFml(quantifier, bddVar, formula.replace(old, new))
	}
}

data class Goal(val fixedVars: List<Var>, val assumptions: List<Formula>, val conclusion: Formula) {
	constructor(assumptions: List<Formula>, conclusion: Formula) : this(listOf(), assumptions, conclusion)
	constructor(conclusion: Formula) : this(listOf(), conclusion)
	override fun toString() =
		((if (fixedVars.isNotEmpty()) fixedVars.joinToString(separator = " ", postfix = " : Fixed, ") else "")
				+ assumptions.joinToString { "$it".removeSurrounding("(", ")") }
				+ (if (assumptions.isNotEmpty()) " " else "")
				+ "⊢ "
				+ "$conclusion".removeSurrounding("(", ")"))
	fun possibleTactics() = allTactics.filter { it.canApply(this) }
}

val allTactics: List<ITactic> = listOf(Tactic0.values().toList(), Tactic1.values().toList(), Tactic2.values().toList()).flatten()

typealias Goals = List<Goal>

fun Goals.replaceFirstGoal(vararg newFirstGoals: Goal): Goals = newFirstGoals.toList() + this.drop(1)

fun Goals.isEqual(other: Goals): Boolean {
	// TODO: 2021/10/01
	return true
}