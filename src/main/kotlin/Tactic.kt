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
			INTRO				-> conclusion is Formula.IMPLIES || conclusion is Formula.NOT || conclusion is Formula.ALL
			SPLIT				-> conclusion is Formula.AND || conclusion is Formula.IFF
			LEFT, RIGHT			-> conclusion is Formula.OR
			EXFALSO, BY_CONTRA	-> conclusion != Formula.FALSE
		}
	}
	fun apply(goals: Goals): Goals {
		val goal = goals[0]
		when(this) {
			ASSUMPTION -> return goals.replaceFirstGoal()
			INTRO -> when(val conclusion = goal.conclusion) {
				is Formula.IMPLIES -> return goals.replaceFirstGoal(goal.copy(assumptions = goal.assumptions + conclusion.leftFml, conclusion = conclusion.rightFml))
				is Formula.NOT -> return goals.replaceFirstGoal(goal.copy(assumptions = goal.assumptions + conclusion.fml, conclusion = Formula.FALSE))
				is Formula.ALL -> {
					val newVar = conclusion.bddVar.getNewVar(goal.fixedVars.toSet() + conclusion.fml.bddVars())
					return goals.replaceFirstGoal(goal.copy(fixedVars = goal.fixedVars + newVar, conclusion = conclusion.fml.replace(conclusion.bddVar, newVar)))
				}
			}
			SPLIT -> when(val conclusion = goal.conclusion) {
				is Formula.AND -> {
					val left    = goal.copy(conclusion = conclusion.leftFml)
					val right   = goal.copy(conclusion = conclusion.rightFml)
					return goals.replaceFirstGoal(left, right)
				}
				is Formula.IFF -> {
					val toRight = goal.copy(conclusion = Formula.IMPLIES(conclusion.leftFml, conclusion.rightFml))
					val toLeft  = goal.copy(conclusion = Formula.IMPLIES(conclusion.rightFml, conclusion.leftFml))
					return goals.replaceFirstGoal(toLeft, toRight)
				}
			}
			LEFT	-> return goals.replaceFirstGoal(goal.copy(conclusion = (goal.conclusion as Formula.OR).leftFml))
			RIGHT   -> return goals.replaceFirstGoal(goal.copy(conclusion = (goal.conclusion as Formula.OR).rightFml))
			EXFALSO -> return goals.replaceFirstGoal(goal.copy(conclusion = Formula.FALSE))
			BY_CONTRA -> return goals.replaceFirstGoal(goal.copy(assumptions = goal.assumptions + Formula.NOT(goal.conclusion), conclusion = Formula.FALSE))
		}
		throw IllegalArgumentException()
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
			REVERT			-> goal.assumptions.isNotEmpty() || possibleFixedVars(goal).isNotEmpty()
			USE				-> conclusion is Formula.EXISTS //&& possibleFixedVars(goal).isNotEmpty()
		}
	}
	fun apply(goals: Goals, assumption: Formula): Goals {
		val goal = goals[0]
		when(this) {
			APPLY -> return when(assumption) {
				is Formula.IMPLIES -> goals.replaceFirstGoal(goal.copy(conclusion = assumption.leftFml))
				is Formula.NOT -> goals.replaceFirstGoal(goal.copy(conclusion = assumption.fml))
				else -> throw IllegalArgumentException()
			}
			CASES -> {
				val removedAssumptions = goal.assumptions.minus(assumption)
				when(assumption) {
					is Formula.AND -> return goals.replaceFirstGoal(goal.copy(assumptions = removedAssumptions + assumption.leftFml + assumption.rightFml))
					is Formula.OR -> {
						val leftGoal    = goal.copy(assumptions = removedAssumptions + assumption.leftFml)
						val rightGoal   = goal.copy(assumptions = removedAssumptions + assumption.rightFml)
						return goals.replaceFirstGoal(leftGoal, rightGoal)
					}
					is Formula.IFF -> {
						val toRight = Formula.IMPLIES(assumption.leftFml, assumption.rightFml)
						val toLeft  = Formula.IMPLIES(assumption.rightFml, assumption.leftFml)
						return goals.replaceFirstGoal(goal.copy(assumptions = removedAssumptions + toRight + toLeft))
					}
					is Formula.EXISTS -> {
						val newVar = assumption.bddVar.getNewVar(goal.fixedVars.toSet())
						return goals.replaceFirstGoal(goal.copy(fixedVars = goal.fixedVars + newVar, assumptions = removedAssumptions + assumption.fml.replace(assumption.bddVar, newVar)))
					}
					else -> throw IllegalArgumentException()
				}
			}
			REVERT -> return goals.replaceFirstGoal(goal.copy(assumptions = goal.assumptions.filterNot { it == assumption }, conclusion = Formula.IMPLIES(assumption, goal.conclusion)))
			else -> throw IllegalArgumentException()
		}
	}
	fun apply(goals: Goals, fixedVar: Var): Goals {
		val goal = goals[0]
		when(this) {
			REVERT -> return goals.replaceFirstGoal(goal.copy(fixedVars = goal.fixedVars.filterNot { it == fixedVar }, conclusion = Formula.ALL(fixedVar, goal.conclusion)))
			USE -> {
				when(val conclusion = goal.conclusion) {
					is Formula.EXISTS -> return goals.replaceFirstGoal(goal.copy(conclusion = conclusion.fml.replace(conclusion.bddVar, fixedVar)))
				}
			}
			else -> throw IllegalArgumentException()
		}
		throw IllegalArgumentException()
	}

	// TODO: 2021/09/22
	// don't need to be a list but a set in an app.
	private fun possibleAssumptions(goal: Goal): List<Formula> = when(this) {
		APPLY   -> goal.assumptions.filter { (it is Formula.IMPLIES && it.rightFml  == goal.conclusion) ||  (it is Formula.NOT && goal.conclusion == Formula.FALSE) }
		CASES   -> goal.assumptions.filter { it is Formula.AND || it is Formula.OR || it is Formula.IFF || it is Formula.EXISTS }
		REVERT -> goal.assumptions
		else -> listOf()
	}
	private fun possibleFixedVars(goal: Goal): List<Var> = when(this) {
		REVERT -> {
			val fixedVarsInAssumptions: Set<Var> = goal.assumptions.fold(setOf()){ set, assumption -> set + assumption.freeVars() }
			goal.fixedVars.filterNot { it in fixedVarsInAssumptions }.filterNot { it in goal.conclusion.bddVars() }
		}
		USE -> if (goal.conclusion is Formula.EXISTS) goal.fixedVars.filterNot { it in goal.conclusion.fml.bddVars() } else listOf()
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
			is Formula.IMPLIES -> goals.replaceFirstGoal(goal.copy(assumptions = goal.assumptions + assumptionApply.rightFml))
			is Formula.NOT -> goals.replaceFirstGoal(goal.copy(assumptions = goal.assumptions + Formula.FALSE))
			else -> throw IllegalArgumentException()
		}
	}
	fun apply(goals: Goals, assumption: Formula, fixedVar: Var): Goals {
		val goal = goals[0]
		return when(assumption) {
			is Formula.ALL -> goals.replaceFirstGoal(goal.copy(assumptions = goal.assumptions + assumption.fml.replace(assumption.bddVar, fixedVar)))
			else -> throw IllegalArgumentException()
		}
	}
	private fun possibleAssumptionsPairs(goal: Goal): List<Pair<Formula, Formula>> {
		val result = mutableListOf<Pair<Formula, Formula>>()
		for (assumptionApply in goal.assumptions) {
			for (assumptionApplied in goal.assumptions) {
				if (assumptionApply is Formula.IMPLIES && assumptionApply.leftFml == assumptionApplied) {
					result.add(Pair(assumptionApply, assumptionApplied))
				} else if (assumptionApply is Formula.NOT
					&& assumptionApply.fml == assumptionApplied) {
					result.add(Pair(assumptionApply, assumptionApplied))
				}
			}
		}
		return result
	}
	private fun possibleAssumptionsWithFixedVar(goal: Goal): List<Formula> = goal.assumptions.filterIsInstance<Formula.ALL>()
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
