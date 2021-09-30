fun main() {
	val variousGoals = listOf(
	listOf(Goal("all x, all y, P x y".parse()!!)),
	listOf(Goal("P and Q to Q and P".parse()!!)),
	listOf(Goal("P or Q to Q or P".parse()!!)),
	listOf(Goal("(ex x, P x) to ex y, P y".parse()!!)),
	listOf(Goal("(ex x, P x) to all x, P x".parse()!!)),
	listOf(Goal("(ex x, P x) to (ex x, Q x) to (all x, R x)".parse()!!)),
	listOf(Goal("(all x, P x) to (ex x, P x)".parse()!!)),
	listOf(Goal("P to (P to Q) to Q".parse()!!)),
	listOf(Goal("P to not P to false".parse()!!))
	)

	print("Input a formula you want to prove >>> ")
	var currentGoals = listOf(Goal(readLine()!!.parse()!!))

	while (currentGoals.isNotEmpty()) {
		println("--------------------------------------")
		printGoals(currentGoals)
		val goal = currentGoals[0]
		print("Possible tactics are >>> ")
		println(goal.possibleTactics().joinToString())
		print("Select a tactic >>> ")
		when (val tactic = goal.possibleTactics()[readLine()!!.toInt()]) {
			is Tactic0 -> currentGoals = tactic.apply(currentGoals)
			is Tactic1 -> {
				print("Possible variables are >>> ")
				println(tactic.possibleFixedVars(goal).joinToString())
				print("Possible formulas are  >>> ")
				println(tactic.possibleAssumptions(goal).joinToString())
				print("Select an variable or an formula >>> ")
				val inputList = readLine()!!.split(" ").map(String::toInt)
				val input = inputList[1]
				when (inputList[0]) {
					0 -> {
						val fixedVar = tactic.possibleFixedVars(goal)[input]
						currentGoals = tactic.apply(currentGoals, fixedVar)
					}
					1 -> {
						val assumption = tactic.possibleAssumptions(goal)[input]
						currentGoals = tactic.apply(currentGoals, assumption)
					}
				}
			}
			is Tactic2 -> {
				print("Possible formulas are >>> ")
				println(tactic.possibleAssumptionsPairs(goal).map { it.first }.distinct().joinToString()) // don't need distinct() in an app
				print("Possible formulas are >>> ")
				println(tactic.possibleAssumptionsWithFixedVar(goal).joinToString())
				print("Select a formula >>> ")
				val inputList = readLine()!!.split(" ").map(String::toInt)
				val input = inputList[1]
				when (inputList[0]) {
					0 -> {
						val assumptionApply = tactic.possibleAssumptionsPairs(goal).map { it.first }.distinct()[input]
						print("Possible formulas are >>> ")
						println(tactic.possibleAssumptionsPairs(goal).filter { it.first == assumptionApply }.map { it.second }.joinToString())
						print("Select a formula >>> ")
						val assumptionApplied = tactic.possibleAssumptionsPairs(goal).filter { it.first == assumptionApply }.map { it.second }[readLine()!!.toInt()]
						currentGoals = tactic.apply(currentGoals, assumptionApply, assumptionApplied)
					}
					1 -> {
						val assumption = tactic.possibleAssumptionsWithFixedVar(goal)[input]
						if (assumption !is QuantifiedFml) {break}
						if (goal.fixedVars.isNotEmpty()) {
							print("Possible fixed variables are >>> ")
							println(goal.fixedVars.joinToString())
							print("Select a fixed variable >>> ")
							val fixedVar = goal.fixedVars[readLine()!!.toInt()]
							currentGoals = tactic.apply(currentGoals, assumption, fixedVar)
						} else {
							currentGoals = tactic.apply(currentGoals, assumption, assumption.bddVar)
							currentGoals = currentGoals.getNewGoals(currentGoals[0].copy(fixedVars = currentGoals[0].fixedVars + assumption.bddVar))
						}
					}
				}
			}
		}
	}
	println("--------------------------------------")

	println("Proof complete!")

}

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

fun Goals.getNewGoals(vararg newGoals: Goal): Goals = newGoals.toList() + this.drop(1)

fun printGoals(goals: Goals) {
	for (goal in goals) {
		if (goal.fixedVars.isNotEmpty()) println(goal.fixedVars.joinToString(separator = " ", postfix = " : Fixed"))
		goal.assumptions.forEach { println("$it".removeSurrounding("(", ")")) }
		println("⊢ " + "${goal.conclusion}".removeSurrounding("(", ")"))
	}
}

// ITactic = Tactic0 | Tactic1 | Tactic2
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
			INTRO				-> conclusion is BinaryConnectiveFml && conclusion.connective == BinaryConnective.IMPLY
								|| conclusion is UnaryConnectiveFml && conclusion.connective == UnaryConnective.NOT
								|| conclusion is QuantifiedFml && conclusion.quantifier == Quantifier.FOR_ALL
			SPLIT				-> conclusion is BinaryConnectiveFml && conclusion.connective in setOf(BinaryConnective.AND, BinaryConnective.IFF)
			LEFT, RIGHT			-> conclusion is BinaryConnectiveFml && conclusion.connective == BinaryConnective.OR
			EXFALSO, BY_CONTRA	-> conclusion != falseFormula
		}
	}
	fun apply(goals: Goals): Goals {
		val goal = goals[0]
		when(this) {
			ASSUMPTION -> return goals.getNewGoals()
			INTRO -> when(goal.conclusion) {
				// IMPLY
				is BinaryConnectiveFml -> return goals.getNewGoals(goal.copy(assumptions = goal.assumptions + goal.conclusion.leftFml, conclusion = goal.conclusion.rightFml))
				// NOT
				is UnaryConnectiveFml -> return goals.getNewGoals(goal.copy(assumptions = goal.assumptions + goal.conclusion.formula, conclusion = falseFormula))
				// FOR_ALL
				is QuantifiedFml -> {
					if (goal.conclusion.bddVar !in goal.fixedVars) {
						return goals.getNewGoals(goal.copy(fixedVars = goal.fixedVars + goal.conclusion.bddVar, conclusion = goal.conclusion.formula))
					} else {
						// Suppose that the goal is the form of "all x, P x" but "x" is already in bddVars.
						// "x" must be arbitrary, so change "x" to "x_1" and "P x" to "P x_1".
						var n = 1
						while (true) {
							val newFixedVar = Var(goal.conclusion.bddVar.id + "_$n")
							if (newFixedVar !in goal.fixedVars) {
								return goals.getNewGoals(goal.copy(fixedVars = goal.fixedVars + newFixedVar, conclusion = goal.conclusion.formula.replace(goal.conclusion.bddVar, newFixedVar)))
							} else {
								n++
							}
						}
					}
				}
			}
			SPLIT -> if (goal.conclusion is BinaryConnectiveFml && goal.conclusion.connective == BinaryConnective.AND) {
				val left    = goal.copy(conclusion = goal.conclusion.leftFml)
				val right   = goal.copy(conclusion = goal.conclusion.rightFml)
				return goals.getNewGoals(left, right)
			} else if   (goal.conclusion is BinaryConnectiveFml && goal.conclusion.connective == BinaryConnective.IFF) {
				val toRight = goal.copy(conclusion = BinaryConnectiveFml(BinaryConnective.IMPLY, goal.conclusion.leftFml, goal.conclusion.rightFml))
				val toLeft  = goal.copy(conclusion = BinaryConnectiveFml(BinaryConnective.IMPLY, goal.conclusion.rightFml, goal.conclusion.leftFml))
				return goals.getNewGoals(toLeft, toRight)
			}
			LEFT	-> if (goal.conclusion is BinaryConnectiveFml) return goals.getNewGoals(goal.copy(conclusion = (goal.conclusion).leftFml))
			RIGHT   -> if (goal.conclusion is BinaryConnectiveFml) return goals.getNewGoals(goal.copy(conclusion = goal.conclusion.rightFml))
			EXFALSO -> return goals.getNewGoals(goal.copy(conclusion = falseFormula))
			BY_CONTRA -> return goals.getNewGoals(goal.copy(assumptions = goal.assumptions + UnaryConnectiveFml(UnaryConnective.NOT, goal.conclusion), conclusion = falseFormula))
		}
		return goals
	}
}

// Tactic with arity 1.
enum class Tactic1(override val id: String): ITactic {
	APPLY("apply"),
	CASES("cases"),
	REVERT("revert"),
	USE("use");
	override fun toString(): String = id
	override fun canApply(goal: Goal): Boolean {
		val conclusion = goal.conclusion
		return when(this) {
			APPLY, CASES	-> possibleAssumptions(goal).isNotEmpty()
			REVERT	-> goal.assumptions.isNotEmpty()
					|| possibleFixedVars(goal).isNotEmpty()
			USE	->	conclusion is QuantifiedFml
					&& conclusion.quantifier == Quantifier.THERE_EXISTS
					&& possibleFixedVars(goal).isNotEmpty()
		}
	}
	fun apply(goals: Goals, assumption: Formula): Goals {
		val goal = goals[0]
		when(this) {
			APPLY -> if (assumption is BinaryConnectiveFml) { // IMPLY
				return goals.getNewGoals(goal.copy(conclusion = assumption.leftFml))
			} else if   (assumption is UnaryConnectiveFml) {  // NOT
				return goals.getNewGoals(goal.copy(conclusion = assumption.formula))
			}
			CASES -> {
				val removedAssumptions = goal.assumptions.filterNot { it == assumption }
				if (assumption is BinaryConnectiveFml && assumption.connective == BinaryConnective.AND) {
					return goals.getNewGoals(goal.copy(assumptions = removedAssumptions + assumption.leftFml + assumption.rightFml))
				} else if (assumption is BinaryConnectiveFml && assumption.connective == BinaryConnective.OR) {
					val leftGoal    = goal.copy(assumptions = removedAssumptions + assumption.leftFml)
					val rightGoal   = goal.copy(assumptions = removedAssumptions + assumption.rightFml)
					return goals.getNewGoals(leftGoal, rightGoal)
				} else if (assumption is BinaryConnectiveFml && assumption.connective == BinaryConnective.IFF) {
					val toRight = BinaryConnectiveFml(BinaryConnective.IMPLY, assumption.leftFml,  assumption.rightFml)
					val toLeft  = BinaryConnectiveFml(BinaryConnective.IMPLY, assumption.rightFml, assumption.leftFml)
					return goals.getNewGoals(goal.copy(assumptions = removedAssumptions + toRight), goal.copy(assumptions = removedAssumptions + toLeft))
				} else if (assumption is QuantifiedFml && assumption.quantifier == Quantifier.THERE_EXISTS) {
					if (assumption.bddVar !in goal.fixedVars) {
						return goals.getNewGoals(goal.copy(fixedVars = goal.fixedVars + assumption.bddVar, assumptions = removedAssumptions + assumption.formula))
					} else {
						// Suppose that the given assumption is the form of "ex x, P x" but "x" is already in bddVars.
						// "x" must be arbitrary, so change "x" to "x_1" and "P x" to "P x_1".
						var n = 1
						while (true) {
							val newFixedVar = Var(assumption.bddVar.id + "_$n")
							if (newFixedVar !in goal.fixedVars) {
								return goals.getNewGoals(goal.copy(fixedVars = goal.fixedVars + newFixedVar, assumptions = removedAssumptions + assumption.formula.replace(assumption.bddVar, newFixedVar)))
							} else {
								n++
							}
						}
					}
				}
			}
			REVERT -> return goals.getNewGoals(goal.copy(assumptions = goal.assumptions.filterNot { it == assumption }, conclusion = BinaryConnectiveFml(BinaryConnective.IMPLY, assumption, goal.conclusion)))
			else -> {}
		}
		return goals
	}
	fun apply(goals: Goals, fixedVar: Var): Goals {
		val goal = goals[0]
		when(this) {
			REVERT -> return goals.getNewGoals(goal.copy(fixedVars = goal.fixedVars.filterNot { it == fixedVar }, conclusion = QuantifiedFml(Quantifier.FOR_ALL, fixedVar, goal.conclusion)))
			USE -> {
				if (goal.conclusion is QuantifiedFml) { // THERE_EXISTS
					return goals.getNewGoals(goal.copy(fixedVars = goal.fixedVars.filterNot { it == fixedVar }, conclusion = goal.conclusion.formula.replace(goal.conclusion.bddVar, fixedVar)))
				}
			}
			else -> {}
		}
		return goals
	}

	// TODO: 2021/09/22
	// don't need to be a list but a set in an app.
	fun possibleAssumptions(goal: Goal): List<Formula> = when(this) {
		APPLY   -> goal.assumptions
			.filter {   (it is BinaryConnectiveFml  && it.connective == BinaryConnective.IMPLY  && it.rightFml  == goal.conclusion)
					||  (it is UnaryConnectiveFml   && it.connective == UnaryConnective.NOT     && goal.conclusion == falseFormula) }
		CASES   -> listOf(
			goal.assumptions
				.filter { it is BinaryConnectiveFml && it.connective in setOf(BinaryConnective.AND, BinaryConnective.OR, BinaryConnective.IFF) }
			, goal.assumptions
				.filter { it is QuantifiedFml && it.quantifier == Quantifier.THERE_EXISTS })
			.flatten()
		REVERT -> goal.assumptions
		USE -> listOf()
	}
	fun possibleFixedVars(goal: Goal): List<Var> = when(this) {
		REVERT -> {
			val fixedVarsInAssumptions = goal.assumptions.map { it.freeVars() }.flatten().toSet()
			goal.fixedVars.filterNot { fixedVarsInAssumptions.contains(it) }
		}
		USE -> goal.fixedVars
		else -> listOf()
	}
}

// Tactic with arity 2.
enum class Tactic2(override val id: String): ITactic {
	HAVE("have");
	override fun toString(): String = id
	override fun canApply(goal: Goal): Boolean = possibleAssumptionsPairs(goal).isNotEmpty() || possibleAssumptionsWithFixedVar(goal).isNotEmpty()
	fun apply(goals: Goals, assumptionApply: Formula, assumptionApplied: Formula): Goals {
		val goal = goals[0]
		return when(assumptionApply) {
			// IMPLY
			is BinaryConnectiveFml -> goals.getNewGoals(goal.copy(assumptions = goal.assumptions + assumptionApply.rightFml))
			// NOT
			is UnaryConnectiveFml -> goals.getNewGoals(goal.copy(assumptions = goal.assumptions + falseFormula))
			else -> goals
		}
	}
	fun apply(goals: Goals, assumption: Formula, fixedVar: Var): Goals {
		val goal = goals[0]
		if (assumption is QuantifiedFml) {
			return goals.getNewGoals(goal.copy(assumptions = goal.assumptions + assumption.formula.replace(assumption.bddVar, fixedVar)))
		}
		return goals
	}
	fun possibleAssumptionsPairs(goal: Goal): List<Pair<Formula, Formula>> {
		val result = mutableListOf<Pair<Formula, Formula>>()
		for (assumptionApply in goal.assumptions) {
			for (assumptionApplied in goal.assumptions) {
				if (assumptionApply is BinaryConnectiveFml
					&& assumptionApply.connective == BinaryConnective.IMPLY
					&& assumptionApply.leftFml == assumptionApplied) {
					result.add(Pair(assumptionApply, assumptionApplied))
				} else if (assumptionApply is UnaryConnectiveFml
					&& assumptionApply.connective == UnaryConnective.NOT
					&& assumptionApply.formula == assumptionApplied) {
					result.add(Pair(assumptionApply, assumptionApplied))
				}
			}
		}
		return result
	}
	fun possibleAssumptionsWithFixedVar(goal: Goal): List<Formula> = goal.assumptions
		.filter { it is QuantifiedFml && it.quantifier == Quantifier.FOR_ALL }
}
