fun main() {
	val predicateOfP2 = Predicate('P',2)
	val varOfX = Var('x')
	val varOfY = Var('y')
	val predicateFmlOfPxy = PredicateFml(predicateOfP2, listOf(varOfX, varOfY))
	val allyPredicateFmlOfPxy = QuantifiedFml(Quantifier.FOR_ALL, varOfY, predicateFmlOfPxy)
	val allxAllyPredicateFmlOfPxy = QuantifiedFml(Quantifier.FOR_ALL, varOfX, allyPredicateFmlOfPxy)
	val goalOfAllxAllyPredicateFmlOfPxy = Goal(allxAllyPredicateFmlOfPxy)
	val goals0 = mutableListOf(goalOfAllxAllyPredicateFmlOfPxy)

	val predicateOfP = Predicate('P')
	val predicateOfQ = Predicate('Q')
	val propP = PredicateFml(predicateOfP)
	val propQ = PredicateFml(predicateOfQ)
	val propPAndQ = BinaryConnectiveFml(BinaryConnective.AND, propP, propQ)
	val propQAndP = BinaryConnectiveFml(BinaryConnective.AND, propQ, propP)
	val propOfAnd = BinaryConnectiveFml(BinaryConnective.IMPLY, propPAndQ, propQAndP)
	val goalOfPropOfAnd = Goal(propOfAnd)
	val goalOfPropOfAnd0 = Goal(mutableListOf(propP, propQ), propPAndQ)
	val goals1 = mutableListOf(goalOfPropOfAnd)

	val propPAOrQ = BinaryConnectiveFml(BinaryConnective.OR, propP, propQ)
	val propQOrP = BinaryConnectiveFml(BinaryConnective.OR, propQ, propP)
	val propOfOr = BinaryConnectiveFml(BinaryConnective.IMPLY, propPAOrQ, propQOrP)
	val goalOfPropOfOr = Goal(propOfOr)
	val goals2 = mutableListOf(goalOfPropOfOr)

	val goals = goals1

	allTactic.forEach { println(it) }

	while (goals.isNotEmpty()) {
		println("--------------------------------------")
		printGoals(goals)
		val goal = goals[0]
		print("Possible tactics are >>> ")
		println(goal.possibleTactics().joinToString())
		print("Select a tactic >>> ")
		when (val tactic = goal.possibleTactics()[readLine()!!.toInt()]) {
			is Tactic0 -> tactic.apply(goals)
			is Tactic1 -> {
				print("Possible formulas are >>> ")
				println(tactic.possibleAssumptions(goal).joinToString())
				print("Select an assumption >>> ")
				val assumption = tactic.possibleAssumptions(goal)[readLine()!!.toInt()]
				tactic.apply(goals, assumption)
			}
			is Tactic1WithVar -> {
				print("Possible variables and formulas are >>> ")
				if (tactic.possibleFixedVars(goal).isNotEmpty()) {
					print(tactic.possibleFixedVars(goal).joinToString(postfix = " : Fixed, "))
				}
				println(goal.assumptions.joinToString())
				print("Select an assumption? (y/n) >>> ")
				when (readLine()) {
					"y" -> {
						print("Select an assumption >>> ")
						val assumption = goal.assumptions[readLine()!!.toInt()]
						tactic.apply(goals, assumption)
					}
					"n" -> {
						print("Select a variable >>> ")
						val fixedVar = tactic.possibleFixedVars(goal)[readLine()!!.toInt()]
						tactic.apply(goals, fixedVar)
					}
				}
			}
		}
	}
	println("--------------------------------------")

	println("Proof complete!")



}

interface Formula {
	override fun toString(): String
	fun freeVariables(): Set<Var>
	fun replace(old: Var, new: Var): Formula
}

interface AtomFml: Formula {}

enum class PreDefinedAtomFml: AtomFml {
	FALSE;
	override fun freeVariables(): Set<Var> = setOf()
	override fun replace(old: Var, new: Var) = this
}

val falseFormula = PreDefinedAtomFml.FALSE

data class Var(val chr: Char) {
	override fun toString() = "$chr"
}

data class Predicate(val id: Char, val arity: Int) {
	constructor(id: Char) : this(id, 0)
	override fun toString() = "$id"
	fun canSubstitute(inputVars: List<Var>): Boolean = inputVars.size == arity
}

data class PredicateFml(val predicate: Predicate, val vars: List<Var>): AtomFml {
	constructor(predicate: Predicate) : this(predicate, listOf())
	override fun toString() = "$predicate" + if (vars.isEmpty()) "" else vars.joinToString(prefix = " ")
	override fun freeVariables() = vars.toSet()
	override fun replace(old: Var, new: Var) = PredicateFml(predicate, vars.map { if (it == old) new else it })
}

interface Connective {
	val id: Char
	val precedence: Int
	override fun toString(): String
}

interface ConnectiveFml: Formula {
	val connective: Connective
}

enum class UnaryConnective(override val id: Char, override val precedence: Int): Connective {
	NOT('¬',4);
	override fun toString() = "$id"
}

data class UnaryConnectiveFml(override val connective: UnaryConnective, val formula: Formula): ConnectiveFml {
	override fun toString() = "($connective$formula)"
	override fun freeVariables() = formula.freeVariables()
	override fun replace(old: Var, new: Var) = UnaryConnectiveFml(connective, formula.replace(old, new))
}

enum class BinaryConnective(override val id: Char, override val precedence: Int): Connective {
	IMPLY('→', 1),
	AND('∧', 3),
	OR('∨', 2),
	IFF('↔', 0);
	override fun toString() = "$id"
}

data class BinaryConnectiveFml(override val connective: BinaryConnective, val leftFml: Formula, val rightFml: Formula): ConnectiveFml {
	override fun toString() = "($leftFml $connective $rightFml)"
	override fun freeVariables() = leftFml.freeVariables().union(rightFml.freeVariables()).toSet()
	override fun replace(old: Var, new: Var) = BinaryConnectiveFml(connective, leftFml.replace(old, new), rightFml.replace(old, new))
}

enum class Quantifier(private val id: Char) {
	FOR_ALL('∀'),
	THERE_EXISTS('∃');
	override fun toString() = "$id"
}

data class QuantifiedFml(val quantifier: Quantifier, val bddVar: Var, val formula: Formula): Formula {
	override fun toString() = "$quantifier $bddVar, $formula"
	override fun freeVariables() = formula.freeVariables().filterNot { it == bddVar }.toSet()
	override fun replace(old: Var, new: Var) = QuantifiedFml(quantifier, bddVar, formula.replace(old, new))
}

data class Goal(var fixedVars: MutableList<Var>, var assumptions: MutableList<Formula>, var conclusion: Formula) {
	constructor(assumptions: MutableList<Formula>, conclusion: Formula) : this(mutableListOf(), assumptions, conclusion)
	constructor(conclusion: Formula) : this(mutableListOf(), conclusion)
	override fun toString() =
		((if (fixedVars.isNotEmpty()) fixedVars.joinToString(postfix = " : Fixed, ") else "")
			+ assumptions.joinToString { "$it".removeSurrounding("(", ")") }
			+ (if (assumptions.isNotEmpty()) " " else "")
			+ "⊢ "
			+ "$conclusion".removeSurrounding("(", ")"))
	fun possibleTactics() = allTactic.filter { it.canApply(this) }
	fun deepCopy(fixedVars: MutableList<Var> = this.fixedVars.toMutableList(), assumptions: MutableList<Formula> = this.assumptions.toMutableList(), conclusion: Formula = this.conclusion): Goal = Goal(fixedVars, assumptions, conclusion)
}

val allTactic: List<ITactic> = Tactic0.values().union(Tactic1.values().union(Tactic1WithVar.values().toList())).toList()

typealias Goals = MutableList<Goal>

fun printGoals(goals: Goals) {
	for (goal in goals) {
		if (goal.fixedVars.isNotEmpty()) println(goal.fixedVars.joinToString(postfix = " : Fixed"))
		goal.assumptions.forEach { println("$it".removeSurrounding("(", ")")) }
		println("⊢ " + "${goal.conclusion}".removeSurrounding("(", ")"))
	}
}

interface ITactic {
	val id: String
	override fun toString(): String
	fun canApply(goal: Goal): Boolean
}

// Tactic with arity 0.
enum class Tactic0(override val id: String): ITactic {
	ASSUMPTION  ("assumption"),
	INTRO       ("intro"),
	SPLIT       ("split"),
	LEFT        ("left"),
	RIGHT       ("right"),
	EXFALSO     ("exfalso"),
	BY_CONTRA   ("by_contra");
	override fun toString(): String = id
	override fun canApply(goal: Goal): Boolean {
		val conclusion = goal.conclusion
		return when(this) {
			ASSUMPTION			-> conclusion in goal.assumptions
			INTRO				-> conclusion is ConnectiveFml && conclusion.connective in setOf(BinaryConnective.IMPLY, UnaryConnective.NOT)
								|| conclusion is QuantifiedFml && conclusion.quantifier == Quantifier.FOR_ALL
			SPLIT				-> conclusion is ConnectiveFml && conclusion.connective in setOf(BinaryConnective.AND, BinaryConnective.IFF)
			LEFT, RIGHT			-> conclusion is ConnectiveFml && conclusion.connective == BinaryConnective.OR
			EXFALSO, BY_CONTRA	-> conclusion != falseFormula
		}
	}
	fun apply(goals: Goals) {
		val goal = goals[0]
		val conclusion = goal.conclusion
		when(this) {
			ASSUMPTION -> goals.removeAt(0)
			INTRO -> when(conclusion) {
				// IMPLY
				is BinaryConnectiveFml -> {
					goal.assumptions.add(conclusion.leftFml)
					goal.conclusion = conclusion.rightFml
				}
				// NOT
				is UnaryConnectiveFml -> {
					goal.assumptions.add(conclusion.formula)
					goal.conclusion = falseFormula
				}
				// FOR_ALL
				is QuantifiedFml -> {
					goal.fixedVars.add(conclusion.bddVar)
					goal.conclusion = conclusion.formula
				}
			}
			SPLIT -> if (conclusion is BinaryConnectiveFml && conclusion.connective == BinaryConnective.AND) {
				val left    = goal.deepCopy(conclusion = conclusion.leftFml)
				val right   = goal.deepCopy(conclusion = conclusion.rightFml)
				goals.removeAt(0)
				goals.add(0, left)
				goals.add(1, right)
			} else if   (conclusion is BinaryConnectiveFml && conclusion.connective == BinaryConnective.IFF) {
				val toRight = goal.deepCopy(conclusion = BinaryConnectiveFml(BinaryConnective.IMPLY, conclusion.leftFml, conclusion.rightFml))
				val toLeft  = goal.deepCopy(conclusion = BinaryConnectiveFml(BinaryConnective.IMPLY, conclusion.rightFml, conclusion.leftFml))
				goals.removeAt(0)
				goals.add(0, toLeft)
				goals.add(1, toRight)
			}
			LEFT    -> goal.conclusion = (goal.conclusion as BinaryConnectiveFml).leftFml
			RIGHT   -> goal.conclusion = (goal.conclusion as BinaryConnectiveFml).rightFml
			EXFALSO -> goal.conclusion = falseFormula
			BY_CONTRA -> {
				goal.assumptions.add(UnaryConnectiveFml(UnaryConnective.NOT, goal.conclusion))
				goal.conclusion = falseFormula
			}
		}
	}
}

// Tactic with arity 1.
enum class Tactic1(override val id: String): ITactic {
	APPLY("apply"),
	CASES("cases");
	override fun toString(): String = id
	override fun canApply(goal: Goal): Boolean = possibleAssumptions(goal).isNotEmpty()
	fun apply(goals: Goals, assumption: Formula) {
		val goal = goals[0]
		when(this) {
			APPLY -> if (assumption is BinaryConnectiveFml  && assumption.connective == BinaryConnective.IMPLY) {
				goal.conclusion = assumption.leftFml
			} else if   (assumption is UnaryConnectiveFml   && assumption.connective == UnaryConnective.NOT) {
				goal.conclusion = assumption.formula
			}
			CASES -> {
				goal.assumptions.removeAll { it == assumption }
				if (assumption is BinaryConnectiveFml && assumption.connective == BinaryConnective.AND) {
					goal.assumptions.add(assumption.leftFml)
					goal.assumptions.add(assumption.rightFml)
				} else if (assumption is BinaryConnectiveFml && assumption.connective == BinaryConnective.OR) {
					val leftGoal    = goal.deepCopy()
					val rightGoal   = goal.deepCopy()
					leftGoal.assumptions.add(assumption.leftFml)
					rightGoal.assumptions.add(assumption.rightFml)
					goals.removeAt(0)
					goals.add(0,leftGoal)
					goals.add(1,rightGoal)
				} else if (assumption is BinaryConnectiveFml && assumption.connective == BinaryConnective.IFF) {
					val toRight = BinaryConnectiveFml(BinaryConnective.IMPLY, assumption.leftFml,  assumption.rightFml)
					val toLeft  = BinaryConnectiveFml(BinaryConnective.IMPLY, assumption.rightFml, assumption.leftFml)
					goal.assumptions.add(toRight)
					goal.assumptions.add(toLeft)
				}
			}
		}
	}
	fun possibleAssumptions(goal: Goal): List<Formula> = when(this) {
		APPLY   -> goal.assumptions
			.filter {   (it is BinaryConnectiveFml  && it.connective == BinaryConnective.IMPLY  && it.rightFml  == goal.conclusion)
					||  (it is UnaryConnectiveFml   && it.connective == UnaryConnective.NOT     && goal.conclusion == falseFormula) }
		CASES   -> goal.assumptions
			.filter { it is BinaryConnectiveFml && it.connective in setOf(BinaryConnective.AND, BinaryConnective.OR, BinaryConnective.IFF) }
		else    -> listOf()
	}
}

// Tactic with arity 1 which is related to quantification.
enum class Tactic1WithVar(override val id: String): ITactic {
	REVERT("revert");
	override fun toString(): String = id
	override fun canApply(goal: Goal): Boolean = goal.assumptions.isNotEmpty() || possibleFixedVars(goal).isNotEmpty()
	fun apply(goals: Goals, assumption: Formula) {
		val goal = goals[0]
		goal.conclusion = BinaryConnectiveFml(BinaryConnective.IMPLY, assumption, goal.conclusion)
		goal.assumptions.removeAll { it == assumption }
	}
	fun apply(goals: Goals, fixedVar: Var) {
		val goal = goals[0]
		goal.conclusion = QuantifiedFml(Quantifier.FOR_ALL, fixedVar, goal.conclusion)
		goal.fixedVars.remove(fixedVar)
	}
	fun possibleFixedVars(goal: Goal): List<Var> {
		val fixedVarsInAssumptions = goal.assumptions.map { it.freeVariables() }.flatten().toSet()
		return goal.fixedVars.filterNot { fixedVarsInAssumptions.contains(it) }
	}
}

// Tactic with arity 2.
enum class Tactic2(override val id: String): ITactic {
	HAVE("have");
	override fun toString(): String = id
	override fun canApply(goal: Goal): Boolean {
		TODO("Not yet implemented")
	}
	fun apply(goals: Goals, assumption: Formula) {
		TODO("Not yet implemented")
	}
	fun possibleAssumptions(goal: Goal): Set<Formula> {
		TODO("Not yet implemented")
	}
}

/*
fun isConnective(chr: Char): Boolean = chr in Connective.values().map{it.chr}
fun getConnective(chr: Char) : Connective? = Connective.values().find{it.chr == chr}
*/