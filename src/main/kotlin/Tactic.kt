// ITactic = Tactic0 | Tactic1 | Tactic2
interface ITactic {
	fun canApply(goal: Goal): Boolean
}

val allTactics: List<ITactic> = Tactic0.values().toList() + Tactic1.values() + Tactic2.values()
// TODO: 2021/10/28 this doesn't need to be a list in an app.

fun applicableTactics(goal: Goal) = allTactics.filter { it.canApply(goal) }

// IApplyData = ApplyData  | ApplyDataWithFormula | ApplyDataWithVar | ApplyDataWithFormula | ApplyDataWithVar
sealed interface IApplyData

typealias History = List<IApplyData>

fun IApplyData.apply(goals: Goals): Goals = when(this) {
	is Tactic0.ApplyData 			-> this.tactic0.apply(goals)
	is Tactic1.ApplyDataWithFormula -> this.tactic1.apply(goals, this.assumption)
	is Tactic1.ApplyDataWithVar 	-> this.tactic1.apply(goals, this.fixedVar)
	is Tactic2.ApplyDataWithFormula -> this.tactic2.apply(goals, this.assumptionApply, this.assumptionApplied)
	is Tactic2.ApplyDataWithVar 	-> this.tactic2.apply(goals, this.assumption, this.fixedVar)
}

fun History.apply(goals: Goals): Goals = this.fold(goals){currentGoals, applyData -> applyData.apply(currentGoals)}

// Tactic with arity 0.
enum class Tactic0(private val id: String): ITactic {
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
			INTRO				-> conclusion is Formula.BinaryConnectiveFml && conclusion.connective == BinaryConnective.IMPLY
					|| conclusion is Formula.UnaryConnectiveFml && conclusion.connective == UnaryConnective.NOT
					|| conclusion is Formula.QuantifiedFml && conclusion.quantifier == Quantifier.FOR_ALL
			SPLIT				-> conclusion is Formula.BinaryConnectiveFml && conclusion.connective in setOf(BinaryConnective.AND, BinaryConnective.IFF)
			LEFT, RIGHT			-> conclusion is Formula.BinaryConnectiveFml && conclusion.connective == BinaryConnective.OR
			EXFALSO, BY_CONTRA	-> conclusion != Formula.FALSE
		}
	}
	fun apply(goals: Goals): Goals {
		val goal = goals[0]
		when(this) {
			ASSUMPTION -> return goals.replaceFirstGoal()
			INTRO -> when(goal.conclusion) {
				// IMPLY
				is Formula.BinaryConnectiveFml -> return goals.replaceFirstGoal(goal.copy(assumptions = goal.assumptions + goal.conclusion.leftFml, conclusion = goal.conclusion.rightFml))
				// NOT
				is Formula.UnaryConnectiveFml -> return goals.replaceFirstGoal(goal.copy(assumptions = goal.assumptions + goal.conclusion.fml, conclusion = Formula.FALSE))
				// FOR_ALL
				is Formula.QuantifiedFml -> {
					val newVar = goal.conclusion.bddVar.getNewVar(goal.fixedVars.toSet() + goal.conclusion.formula.bddVars())
					return goals.replaceFirstGoal(goal.copy(fixedVars = goal.fixedVars + newVar, conclusion = goal.conclusion.formula.replace(goal.conclusion.bddVar, newVar)))
				}
				else -> {}
			}
			SPLIT -> if (goal.conclusion is Formula.BinaryConnectiveFml && goal.conclusion.connective == BinaryConnective.AND) {
				val left    = goal.copy(conclusion = goal.conclusion.leftFml)
				val right   = goal.copy(conclusion = goal.conclusion.rightFml)
				return goals.replaceFirstGoal(left, right)
			} else if   (goal.conclusion is Formula.BinaryConnectiveFml && goal.conclusion.connective == BinaryConnective.IFF) {
				val toRight = goal.copy(conclusion = Formula.BinaryConnectiveFml(BinaryConnective.IMPLY, goal.conclusion.leftFml, goal.conclusion.rightFml))
				val toLeft  = goal.copy(conclusion = Formula.BinaryConnectiveFml(BinaryConnective.IMPLY, goal.conclusion.rightFml, goal.conclusion.leftFml))
				return goals.replaceFirstGoal(toLeft, toRight)
			}
			LEFT	-> if (goal.conclusion is Formula.BinaryConnectiveFml) return goals.replaceFirstGoal(goal.copy(conclusion = (goal.conclusion).leftFml))
			RIGHT   -> if (goal.conclusion is Formula.BinaryConnectiveFml) return goals.replaceFirstGoal(goal.copy(conclusion = goal.conclusion.rightFml))
			EXFALSO -> return goals.replaceFirstGoal(goal.copy(conclusion = Formula.FALSE))
			BY_CONTRA -> return goals.replaceFirstGoal(goal.copy(assumptions = goal.assumptions + Formula.UnaryConnectiveFml(UnaryConnective.NOT, goal.conclusion), conclusion = Formula.FALSE))
		}
		return goals
	}
	data class ApplyData(val tactic0: Tactic0): IApplyData
}

// Tactic with arity 1.
enum class Tactic1(private val id: String): ITactic {
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
			USE	->	conclusion is Formula.QuantifiedFml
					&& conclusion.quantifier == Quantifier.THERE_EXISTS
					//&& possibleFixedVars(goal).isNotEmpty()
		}
	}
	fun apply(goals: Goals, assumption: Formula): Goals {
		val goal = goals[0]
		when(this) {
			APPLY -> if (assumption is Formula.BinaryConnectiveFml) { // IMPLY
				return goals.replaceFirstGoal(goal.copy(conclusion = assumption.leftFml))
			} else if   (assumption is Formula.UnaryConnectiveFml) {  // NOT
				return goals.replaceFirstGoal(goal.copy(conclusion = assumption.fml))
			}
			CASES -> {
				val removedAssumptions = goal.assumptions.filterNot { it == assumption }
				if (assumption is Formula.BinaryConnectiveFml && assumption.connective == BinaryConnective.AND) {
					return goals.replaceFirstGoal(goal.copy(assumptions = removedAssumptions + assumption.leftFml + assumption.rightFml))
				} else if (assumption is Formula.BinaryConnectiveFml && assumption.connective == BinaryConnective.OR) {
					val leftGoal    = goal.copy(assumptions = removedAssumptions + assumption.leftFml)
					val rightGoal   = goal.copy(assumptions = removedAssumptions + assumption.rightFml)
					return goals.replaceFirstGoal(leftGoal, rightGoal)
				} else if (assumption is Formula.BinaryConnectiveFml && assumption.connective == BinaryConnective.IFF) {
					val toRight = Formula.BinaryConnectiveFml(BinaryConnective.IMPLY, assumption.leftFml,  assumption.rightFml)
					val toLeft  = Formula.BinaryConnectiveFml(BinaryConnective.IMPLY, assumption.rightFml, assumption.leftFml)
					return goals.replaceFirstGoal(goal.copy(assumptions = removedAssumptions + toRight + toLeft))
				} else if (assumption is Formula.QuantifiedFml && assumption.quantifier == Quantifier.THERE_EXISTS) {
					val newVar = assumption.bddVar.getNewVar(goal.fixedVars.toSet())
					return goals.replaceFirstGoal(goal.copy(fixedVars = goal.fixedVars + newVar, assumptions = removedAssumptions + assumption.formula.replace(assumption.bddVar, newVar)))
				}
			}
			REVERT -> return goals.replaceFirstGoal(goal.copy(assumptions = goal.assumptions.filterNot { it == assumption }, conclusion = Formula.BinaryConnectiveFml(BinaryConnective.IMPLY, assumption, goal.conclusion)))
			else -> {}
		}
		return goals
	}
	fun apply(goals: Goals, fixedVar: Var): Goals {
		val goal = goals[0]
		when(this) {
			REVERT -> return goals.replaceFirstGoal(goal.copy(fixedVars = goal.fixedVars.filterNot { it == fixedVar }, conclusion = Formula.QuantifiedFml(Quantifier.FOR_ALL, fixedVar, goal.conclusion)))
			USE -> {
				if (goal.conclusion is Formula.QuantifiedFml) { // THERE_EXISTS
					return goals.replaceFirstGoal(goal.copy(conclusion = goal.conclusion.formula.replace(goal.conclusion.bddVar, fixedVar)))
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
			.filter {   (it is Formula.BinaryConnectiveFml  && it.connective == BinaryConnective.IMPLY  && it.rightFml  == goal.conclusion)
					||  (it is Formula.UnaryConnectiveFml   && it.connective == UnaryConnective.NOT     && goal.conclusion == Formula.FALSE) }
		CASES   -> listOf(
			goal.assumptions
				.filter { it is Formula.BinaryConnectiveFml && it.connective in setOf(BinaryConnective.AND, BinaryConnective.OR, BinaryConnective.IFF) }
			, goal.assumptions
				.filter { it is Formula.QuantifiedFml && it.quantifier == Quantifier.THERE_EXISTS })
			.flatten()
		REVERT -> goal.assumptions
		USE -> listOf()
	}
	fun possibleFixedVars(goal: Goal): List<Var> = when(this) {
		REVERT -> {
			val fixedVarsInAssumptions = goal.assumptions.map { it.freeVars() }.flatten().toSet()
			goal.fixedVars.filterNot { it in fixedVarsInAssumptions }.filterNot { it in goal.conclusion.bddVars() }
		}
		USE -> {
			if (goal.conclusion is Formula.QuantifiedFml) {
				goal.fixedVars.filterNot { it in goal.conclusion.formula.bddVars() }
			} else {
				listOf()
			}
		}
		else -> listOf()
	}
	data class ApplyDataWithFormula(val tactic1: Tactic1, val assumption: Formula): IApplyData
	data class ApplyDataWithVar(val tactic1: Tactic1, val fixedVar: Var): IApplyData
}

// Tactic with arity 2.
enum class Tactic2(private val id: String): ITactic {
	HAVE("have");
	override fun toString(): String = id
	override fun canApply(goal: Goal): Boolean = possibleAssumptionsPairs(goal).isNotEmpty() || possibleAssumptionsWithFixedVar(goal).isNotEmpty()
	fun apply(goals: Goals, assumptionApply: Formula, assumptionApplied: Formula): Goals {
		val goal = goals[0]
		return when(assumptionApply) {
			// IMPLY
			is Formula.BinaryConnectiveFml -> goals.replaceFirstGoal(goal.copy(assumptions = goal.assumptions + assumptionApply.rightFml))
			// NOT
			is Formula.UnaryConnectiveFml -> goals.replaceFirstGoal(goal.copy(assumptions = goal.assumptions + Formula.FALSE))
			else -> goals
		}
	}
	fun apply(goals: Goals, assumption: Formula, fixedVar: Var): Goals {
		val goal = goals[0]
		if (assumption is Formula.QuantifiedFml) {
			return goals.replaceFirstGoal(goal.copy(assumptions = goal.assumptions + assumption.formula.replace(assumption.bddVar, fixedVar)))
		}
		return goals
	}
	fun possibleAssumptionsPairs(goal: Goal): List<Pair<Formula, Formula>> {
		val result = mutableListOf<Pair<Formula, Formula>>()
		for (assumptionApply in goal.assumptions) {
			for (assumptionApplied in goal.assumptions) {
				if (assumptionApply is Formula.BinaryConnectiveFml
					&& assumptionApply.connective == BinaryConnective.IMPLY
					&& assumptionApply.leftFml == assumptionApplied) {
					result.add(Pair(assumptionApply, assumptionApplied))
				} else if (assumptionApply is Formula.UnaryConnectiveFml
					&& assumptionApply.connective == UnaryConnective.NOT
					&& assumptionApply.fml == assumptionApplied) {
					result.add(Pair(assumptionApply, assumptionApplied))
				}
			}
		}
		return result
	}
	fun possibleAssumptionsWithFixedVar(goal: Goal): List<Formula> = goal.assumptions
		.filter { it is Formula.QuantifiedFml && it.quantifier == Quantifier.FOR_ALL }
	data class ApplyDataWithFormula(val tactic2: Tactic2, val assumptionApply: Formula, val assumptionApplied: Formula): IApplyData
	data class ApplyDataWithVar(val tactic2: Tactic2, val assumption: Formula, val fixedVar: Var): IApplyData
	/*
	fun possibleAssumptionsWithFixedVar(goal: Goal): List<Pair<Formula, List<Var>>> =
		goal.assumptions
		.filter { it is Formula.QuantifiedFml && it.quantifier == Quantifier.FOR_ALL }
			.map { Pair(it, goal.fixedVars.filterNot { it in goal.conclusion.bddVars() }) }


	 */

	/*
	fun possibleAssumptionsWithFixedVar(goal: Goal): List<Pair<Formula, List<Var>>> {
		for (assumption in goal.assumptions.filter { it is Formula.QuantifiedFml && it.quantifier == Quantifier.FOR_ALL }) {
			val newVar = assumption.bddVar.getNewVar(currentGoal.getAllBddVars() + currentGoal.fixedVars)
			val tempCurrentGoals = currentGoals.replaceFirstGoal(currentGoal.copy(fixedVars = currentGoal.fixedVars + newVar))
		}
	}

	 */
}
