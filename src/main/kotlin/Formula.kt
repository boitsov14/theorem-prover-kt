// Formula = PreDefinedAtomFml | PredicateFml | BinaryConnectiveFml | UnaryConnectiveFml | QuantifiedFml
interface Formula {
	override fun toString(): String
	fun freeVars(): Set<Var>
	fun bddVars() : Set<Var>
	fun replace(old: Var, new: Var): Formula
}

enum class PreDefinedAtomFml(private val str: String, val id: Char): Formula, Token {
	FALSE("false", '⊥');
	override fun toString() = str
	override fun freeVars() = setOf<Var>()
	override fun bddVars()  = setOf<Var>()
	override fun replace(old: Var, new: Var) = this
}

val falseFormula = PreDefinedAtomFml.FALSE

data class Var(val id: String): SemiToken {
	override fun toString() = id
}

data class PredicateFml(val predicate: Char, val vars: List<Var>): Formula, Token {
	override fun toString() = "$predicate" + if (vars.isEmpty()) "" else vars.joinToString(prefix = " ")
	override fun freeVars() = vars.toSet()
	override fun bddVars()  = setOf<Var>()
	override fun replace(old: Var, new: Var) = PredicateFml(predicate, vars.map { if (it == old) new else it })
}

enum class UnaryConnective(val id: Char, override val precedence: Int): OperatorToken {
	NOT('¬',4);
	override fun toString() = "$id"
}

data class UnaryConnectiveFml(val connective: UnaryConnective, val formula: Formula): Formula {
	override fun toString() = "($connective$formula)"
	override fun freeVars() = formula.freeVars()
	override fun bddVars() = formula.bddVars()
	override fun replace(old: Var, new: Var) = UnaryConnectiveFml(connective, formula.replace(old, new))
}

enum class BinaryConnective(val id: Char, override val precedence: Int): OperatorToken {
	IMPLY('→', 1),
	AND('∧', 3),
	OR('∨', 2),
	IFF('↔', 0);
	override fun toString() = "$id"
}

data class BinaryConnectiveFml(val connective: BinaryConnective, val leftFml: Formula, val rightFml: Formula): Formula {
	override fun toString() = "($leftFml $connective $rightFml)"
	override fun freeVars() = leftFml.freeVars() + rightFml.freeVars()
	override fun bddVars()  = leftFml.bddVars()  + leftFml.bddVars()
	override fun replace(old: Var, new: Var) = BinaryConnectiveFml(connective, leftFml.replace(old, new), rightFml.replace(old, new))
}

enum class Quantifier(val id: Char): SemiToken {
	FOR_ALL('∀'),
	THERE_EXISTS('∃');
	override fun toString() = "$id"
}

data class QuantifiedFml(val quantifier: Quantifier, val bddVar: Var, val formula: Formula): Formula {
	init {
		if (bddVar in formula.bddVars()) {
			println("束縛変数がかぶっています．")
		}
	}
	override fun toString() = "($quantifier $bddVar, $formula)"
	override fun freeVars() = formula.freeVars().filterNot { it == bddVar }.toSet()
	override fun bddVars()  = formula.bddVars() + setOf(bddVar)
	override fun replace(old: Var, new: Var) = QuantifiedFml(quantifier, bddVar, formula.replace(old, new))
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
