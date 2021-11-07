package core.tactic

import core.formula.*

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
	ASSUMPTION("assumption"),
	INTRO("intro"),
	SPLIT("split"),
	LEFT("left"),
	RIGHT("right"),
	EXFALSO("exfalso"),
	BY_CONTRA("by_contra");
	override fun toString(): String = id
	override fun canApply(goal: Goal): Boolean {
		val conclusion = goal.conclusion
		return when(this) {
			ASSUMPTION	-> conclusion in goal.assumptions
			INTRO		-> conclusion is Formula.IMPLIES || conclusion is Formula.NOT || conclusion is Formula.ALL
			SPLIT		-> conclusion is Formula.AND || conclusion is Formula.IFF
			LEFT, RIGHT	-> conclusion is Formula.OR
			EXFALSO		-> conclusion != Formula.FALSE
			BY_CONTRA	-> conclusion != Formula.FALSE && Formula.NOT(conclusion) !in goal.assumptions
		}
	}
	fun apply(goals: Goals): Goals {
		val goal = goals[0]
		when(this) {
			ASSUMPTION -> return goals.replaceFirstGoal()
			INTRO -> when(val conclusion = goal.conclusion) {
				is Formula.IMPLIES -> {
					val newGoal = goal.copy(
						assumptions = goal.assumptions.addIfDistinct(conclusion.leftFml),
						conclusion = conclusion.rightFml
					)
					return goals.replaceFirstGoal(newGoal)
				}
				is Formula.NOT -> {
					val newGoal = goal.copy(
						assumptions = goal.assumptions.addIfDistinct(conclusion.fml),
						conclusion = Formula.FALSE
					)
					return goals.replaceFirstGoal(newGoal)
				}
				is Formula.ALL -> {
					val newVar = conclusion.bddVar.getUniqueVar(goal.fixedVars.toSet() + conclusion.fml.bddVars)
					val newGoal = goal.copy(
						fixedVars = goal.fixedVars + newVar,
						conclusion = conclusion.fml.replace(conclusion.bddVar, newVar)
					)
					return goals.replaceFirstGoal(newGoal)
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
			LEFT -> when(val conclusion = goal.conclusion) {
				is Formula.OR -> {
					val newGoal = goal.copy(conclusion = conclusion.leftFml)
					return goals.replaceFirstGoal(newGoal)
				}
			}
			RIGHT -> when(val conclusion = goal.conclusion) {
				is Formula.OR -> {
					val newGoal = goal.copy(conclusion = conclusion.rightFml)
					return goals.replaceFirstGoal(newGoal)
				}
			}
			EXFALSO -> {
				val newGoal = goal.copy(conclusion = Formula.FALSE)
				return goals.replaceFirstGoal(newGoal)
			}
			BY_CONTRA -> {
				val newGoal = goal.copy(
					assumptions = goal.assumptions.addIfDistinct(Formula.NOT(goal.conclusion)),
					conclusion = Formula.FALSE
				)
				return goals.replaceFirstGoal(newGoal)
			}
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
	USE("use"),
	CLEAR("clear");
	override fun toString(): String = id
	override fun canApply(goal: Goal): Boolean = when(this) {
		APPLY, CASES, CLEAR	-> possibleAssumptions(goal).isNotEmpty()
		REVERT				-> possibleAssumptions(goal).isNotEmpty() || possibleFixedVars(goal).isNotEmpty()
		USE					-> goal.conclusion is Formula.EXISTS
	}
	fun apply(goals: Goals, assumption: Formula): Goals {
		val goal = goals[0]
		when(this) {
			APPLY -> return when(assumption) {
				is Formula.IMPLIES -> {
					val newGoal = goal.copy(conclusion = assumption.leftFml)
					goals.replaceFirstGoal(newGoal)
				}
				is Formula.NOT -> {
					val newGoal = goal.copy(conclusion = assumption.fml)
					goals.replaceFirstGoal(newGoal)
				}
				else -> throw IllegalArgumentException()
			}
			CASES -> {
				when(assumption) {
					is Formula.AND -> {
						val newGoal = goal.copy(assumptions = goal.assumptions.replaceIfDistinct(assumption, assumption.leftFml, assumption.rightFml))
						return goals.replaceFirstGoal(newGoal)
					}
					is Formula.OR -> {
						val leftGoal	= goal.copy(assumptions = goal.assumptions.replaceIfDistinct(assumption, assumption.leftFml))
						val rightGoal	= goal.copy(assumptions = goal.assumptions.replaceIfDistinct(assumption, assumption.rightFml))
						return goals.replaceFirstGoal(leftGoal, rightGoal)
					}
					is Formula.IFF -> {
						val toRight = Formula.IMPLIES(assumption.leftFml, assumption.rightFml)
						val toLeft  = Formula.IMPLIES(assumption.rightFml, assumption.leftFml)
						val newGoal = goal.copy(assumptions = goal.assumptions.replaceIfDistinct(assumption, toRight, toLeft))
						return goals.replaceFirstGoal(newGoal)
					}
					is Formula.EXISTS -> {
						val newVar = assumption.bddVar.getUniqueVar(goal.fixedVars.toSet())
						val newGoal = goal.copy(
							fixedVars = goal.fixedVars + newVar,
							assumptions = goal.assumptions.replaceIfDistinct(assumption, assumption.fml.replace(assumption.bddVar, newVar))
						)
						return goals.replaceFirstGoal(newGoal)
					}
					else -> throw IllegalArgumentException()
				}
			}
			REVERT -> {
				val newGoal = goal.copy(
					assumptions = goal.assumptions.minus(assumption),
					conclusion = Formula.IMPLIES(assumption, goal.conclusion)
				)
				return goals.replaceFirstGoal(newGoal)
			}
			CLEAR -> {
				val newGoal = goal.copy(assumptions = goal.assumptions.minus(assumption))
				return goals.replaceFirstGoal(newGoal)
			}
			else -> throw IllegalArgumentException()
		}
	}
	fun apply(goals: Goals, fixedVar: Var): Goals {
		val goal = goals[0]
		when(this) {
			REVERT -> {
				val newGoal = goal.copy(
					fixedVars = goal.fixedVars.minus(fixedVar),
					conclusion = Formula.ALL(fixedVar, goal.conclusion)
				)
				return goals.replaceFirstGoal(newGoal)
			}
			USE -> {
				when(val conclusion = goal.conclusion) {
					is Formula.EXISTS -> {
						val newGoal = goal.copy(conclusion = conclusion.fml.replace(conclusion.bddVar, fixedVar))
						return goals.replaceFirstGoal(newGoal)
					}
				}
			}
			else -> throw IllegalArgumentException()
		}
		throw IllegalArgumentException()
	}

	// TODO: 2021/09/22
	// don't need to be a list but a set in an app.
	private fun possibleAssumptions(goal: Goal): List<Formula> = when(this) {
		APPLY   		-> goal.assumptions.filter { (it is Formula.IMPLIES && it.rightFml  == goal.conclusion) ||  (it is Formula.NOT && goal.conclusion == Formula.FALSE) }
		CASES   		-> goal.assumptions.filter { it is Formula.AND || it is Formula.OR || it is Formula.IFF || it is Formula.EXISTS }
		REVERT, CLEAR	-> goal.assumptions
		else			-> listOf()
	}
	private fun possibleFixedVars(goal: Goal): List<Var> = when(this) {
		REVERT -> {
			val fixedVarsInAssumptions = goal.assumptions.fold(setOf<Var>()){ set, assumption -> set + assumption.freeVars }
			goal.fixedVars.filterNot { it in fixedVarsInAssumptions }.filterNot { it in goal.conclusion.bddVars }
		}
		USE -> if (goal.conclusion is Formula.EXISTS) {
			goal.fixedVars.filterNot { it in goal.conclusion.fml.bddVars }
		} else listOf()
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
			is Formula.IMPLIES -> {
				val newGoal = goal.copy(assumptions = goal.assumptions.replaceIfDistinct(assumptionApply, assumptionApply.rightFml))
				goals.replaceFirstGoal(newGoal)
			}
			is Formula.NOT -> {
				val newGoal = goal.copy(assumptions = goal.assumptions.addIfDistinct(Formula.FALSE))
				goals.replaceFirstGoal(newGoal)
			}
			else -> throw IllegalArgumentException()
		}
	}
	fun apply(goals: Goals, assumption: Formula, fixedVar: Var): Goals {
		val goal = goals[0]
		return when(assumption) {
			is Formula.ALL -> {
				val newGoal = goal.copy(assumptions = goal.assumptions.addIfDistinct(assumption.fml.replace(assumption.bddVar, fixedVar)))
				goals.replaceFirstGoal(newGoal)
			}
			else -> throw IllegalArgumentException()
		}
	}
	private fun possibleAssumptionsPairs(goal: Goal): List<Pair<Formula, Formula>> {
		val result = mutableListOf<Pair<Formula, Formula>>()
		for (assumptionApply in goal.assumptions) {
			for (assumptionApplied in goal.assumptions) {
				if (assumptionApply is Formula.IMPLIES
					&& assumptionApply.leftFml == assumptionApplied
					&& assumptionApply.rightFml !in goal.assumptions
				) {
					result.add(Pair(assumptionApply, assumptionApplied))
				} else if (assumptionApply is Formula.NOT
					&& assumptionApply.fml == assumptionApplied
					&& Formula.FALSE !in goal.assumptions
				) {
					result.add(Pair(assumptionApply, assumptionApplied))
				}
			}
		}
		return result
	}
	private fun possibleAssumptionsWithFixedVar(goal: Goal): List<Formula> = goal.assumptions.filterIsInstance<Formula.ALL>()
	data class ApplyDataWithFormula(val tactic2: Tactic2, val assumptionApply: Formula, val assumptionApplied: Formula): IApplyData
	data class ApplyDataWithVar(val tactic2: Tactic2, val assumption: Formula, val fixedVar: Var): IApplyData
}
