fun main() {
	val goals0 = mutableListOf(Goal("all x, all y, P x y".parse()!!))
	val goals1 = mutableListOf(Goal("P and Q to Q and P".parse()!!))
	val goals2 = mutableListOf(Goal("P or Q to Q or P".parse()!!))
	val goals3 = mutableListOf(Goal("(ex x, P x) to ex y, P y".parse()!!))
	val goals4 = mutableListOf(Goal("(ex x, P x) to all x, P x".parse()!!))
	val goals5 = mutableListOf(Goal("(ex x, P x) to (ex x, Q x) to (all x, R x)".parse()!!))
	val goals6 = mutableListOf(Goal("(all x, P x) to (ex x, P x)".parse()!!))
	val goals7 = mutableListOf(Goal("P to (P to Q) to Q".parse()!!))
	val goals8 = mutableListOf(Goal("P to not P to false".parse()!!))

	val goals = goals8

	val fmlStrings = listOf("P and all x, Q x", "all x, Q x and P", "(all x, Q x) and P", "false", "not false", "all x, ex x, P x")
	fmlStrings.forEach { println(Goal(it.parse()!!)) }
	println()

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
						tactic.apply(goals, fixedVar)
					}
					1 -> {
						val assumption = tactic.possibleAssumptions(goal)[input]
						tactic.apply(goals, assumption)
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
						tactic.apply(goals, assumptionApply, assumptionApplied)
					}
					1 -> {
						val assumption = tactic.possibleAssumptionsWithFixedVar(goal)[input]
						if (assumption !is QuantifiedFml) {break}
						if (goal.fixedVars.isNotEmpty()) {
							print("Possible fixed variables are >>> ")
							println(goal.fixedVars.joinToString())
							print("Select a fixed variable >>> ")
							val fixedVar = goal.fixedVars[readLine()!!.toInt()]
							tactic.apply(goals, assumption, fixedVar)
						} else {
							tactic.apply(goals, assumption, assumption.bddVar)
							goals[0].fixedVars.add(assumption.bddVar)
						}
					}
				}
			}
		}
	}
	println("--------------------------------------")

	println("Proof complete!")

}

// Formula = AtomFml | ConnectiveFml | QuantifiedFml
interface Formula {
	override fun toString(): String
	fun freeVars(): Set<Var>
	fun bddVars() : Set<Var>
	fun replace(old: Var, new: Var): Formula
}

// AtomFml = PreDefinedAtomFml | PredicateFml
interface AtomFml: Formula, Token {}

enum class PreDefinedAtomFml(private val str: String, val id: Char): AtomFml {
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

data class PredicateFml(val predicate: Char, val vars: List<Var>): AtomFml {
	override fun toString() = "$predicate" + if (vars.isEmpty()) "" else vars.joinToString(prefix = " ")
	override fun freeVars() = vars.toSet()
	override fun bddVars()  = setOf<Var>()
	override fun replace(old: Var, new: Var) = PredicateFml(predicate, vars.map { if (it == old) new else it })
}

// Connective = BinaryConnective | UnaryConnective
interface Connective: OperatorToken {
	val id: Char
	override fun toString(): String
}

// ConnectiveFml = BinaryConnectiveFml | UnaryConnectiveFml
interface ConnectiveFml: Formula {
	val connective: Connective
}

enum class UnaryConnective(override val id: Char, override val precedence: Int): Connective {
	NOT('¬',4);
	override fun toString() = "$id"
}

data class UnaryConnectiveFml(override val connective: UnaryConnective, val formula: Formula): ConnectiveFml {
	override fun toString() = "($connective$formula)"
	override fun freeVars() = formula.freeVars()
	override fun bddVars() = formula.bddVars()
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

data class Goal(var fixedVars: MutableList<Var>, var assumptions: MutableList<Formula>, var conclusion: Formula) {
	constructor(assumptions: MutableList<Formula>, conclusion: Formula) : this(mutableListOf(), assumptions, conclusion)
	constructor(conclusion: Formula) : this(mutableListOf(), conclusion)
	override fun toString() =
		((if (fixedVars.isNotEmpty()) fixedVars.joinToString(separator = " ", postfix = " : Fixed, ") else "")
			+ assumptions.joinToString { "$it".removeSurrounding("(", ")") }
			+ (if (assumptions.isNotEmpty()) " " else "")
			+ "⊢ "
			+ "$conclusion".removeSurrounding("(", ")"))
	fun possibleTactics() = allTactics.filter { it.canApply(this) }
	fun deepCopy(fixedVars: MutableList<Var> = this.fixedVars.toMutableList(), assumptions: MutableList<Formula> = this.assumptions.toMutableList(), conclusion: Formula = this.conclusion): Goal = Goal(fixedVars, assumptions, conclusion)
}

val allTactics: List<ITactic> = listOf(Tactic0.values().toList(), Tactic1.values().toList(), Tactic2.values().toList()).flatten()

typealias Goals = MutableList<Goal>

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
					if (conclusion.bddVar !in goal.fixedVars) {
						goal.fixedVars.add(conclusion.bddVar)
						goal.conclusion = conclusion.formula
					} else {
						// Suppose that the goal is the form of "all x, P x" but "x" is already in bddVars.
						// "x" must be arbitrary, so change "x" to "x_1" and "P x" to "P x_1".
						var n = 1
						while (true) {
							val newFixedVar = Var(conclusion.bddVar.id + "_$n")
							if (newFixedVar !in goal.fixedVars) {
								goal.fixedVars.add(newFixedVar)
								goal.conclusion = conclusion.formula.replace(conclusion.bddVar, newFixedVar)
								break
							} else {
								n++
							}
						}
					}
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
				} else if (assumption is QuantifiedFml && assumption.quantifier == Quantifier.THERE_EXISTS) {
					if (assumption.bddVar !in goal.fixedVars) {
						goal.assumptions.add(assumption.formula)
						goal.fixedVars.add(assumption.bddVar)
					} else {
						// Suppose that the given assumption is the form of "ex x, P x" but "x" is already in bddVars.
						// "x" must be arbitrary, so change "x" to "x_1" and "P x" to "P x_1".
						var n = 1
						while (true) {
							val newFixedVar = Var(assumption.bddVar.id + "_$n")
							if (newFixedVar !in goal.fixedVars) {
								goal.assumptions.add(assumption.formula.replace(assumption.bddVar, newFixedVar))
								goal.fixedVars.add(newFixedVar)
								break
							} else {
								n++
							}
						}
					}
				}
			}
			REVERT -> {
				goal.conclusion = BinaryConnectiveFml(BinaryConnective.IMPLY, assumption, goal.conclusion)
				goal.assumptions.removeAll { it == assumption }
			}
			else -> {}
		}
	}
	fun apply(goals: Goals, fixedVar: Var) {
		val goal = goals[0]
		val conclusion = goal.conclusion
		when(this) {
			REVERT -> {
				goal.conclusion = QuantifiedFml(Quantifier.FOR_ALL, fixedVar, goal.conclusion)
				goal.fixedVars.remove(fixedVar)
			}
			USE -> {
				if (conclusion is QuantifiedFml && conclusion.quantifier == Quantifier.THERE_EXISTS) {
					goal.conclusion = conclusion.formula.replace(conclusion.bddVar, fixedVar)
					goal.fixedVars.remove(fixedVar)
				}
			}
			else -> {}
		}

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
	fun apply(goals: Goals, assumptionApply: Formula, assumptionApplied: Formula) {
		val goal = goals[0]
		when(assumptionApply) {
			// IMPLY
			is BinaryConnectiveFml -> goal.assumptions.add(assumptionApply.rightFml)
			// NOT
			is UnaryConnectiveFml -> goal.assumptions.add(falseFormula)
		}
	}
	fun apply(goals: Goals, assumption: Formula, fixedVar: Var) {
		val goal = goals[0]
		if (assumption is QuantifiedFml) {
			goal.assumptions.add(assumption.formula.replace(assumption.bddVar, fixedVar))
		}
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
