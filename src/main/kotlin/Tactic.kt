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
			INTRO				-> conclusion is Formula.BinaryConnectiveFml && conclusion.connective == BinaryConnective.IMPLY
					|| conclusion is Formula.UnaryConnectiveFml && conclusion.connective == UnaryConnective.NOT
					|| conclusion is Formula.QuantifiedFml && conclusion.quantifier == Quantifier.FOR_ALL
			SPLIT				-> conclusion is Formula.BinaryConnectiveFml && conclusion.connective in setOf(BinaryConnective.AND, BinaryConnective.IFF)
			LEFT, RIGHT			-> conclusion is Formula.BinaryConnectiveFml && conclusion.connective == BinaryConnective.OR
			EXFALSO, BY_CONTRA	-> conclusion != Formula.False
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
				is Formula.UnaryConnectiveFml -> return goals.replaceFirstGoal(goal.copy(assumptions = goal.assumptions + goal.conclusion.formula, conclusion = Formula.False))
				// FOR_ALL
				is Formula.QuantifiedFml -> {
					if (goal.conclusion.bddVar !in goal.fixedVars) {
						return goals.replaceFirstGoal(goal.copy(fixedVars = goal.fixedVars + goal.conclusion.bddVar, conclusion = goal.conclusion.formula))
					} else {
						// Suppose that the goal is the form of "all x, P x" but "x" is already in bddVars.
						// "x" must be arbitrary, so change "x" to "x_1" and "P x" to "P x_1".
						var n = 1
						while (true) {
							val newFixedVar = Var(goal.conclusion.bddVar.id + "_$n")
							if (newFixedVar !in goal.fixedVars) {
								return goals.replaceFirstGoal(goal.copy(fixedVars = goal.fixedVars + newFixedVar, conclusion = goal.conclusion.formula.replace(goal.conclusion.bddVar, newFixedVar)))
							} else {
								n++
							}
						}
					}
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
			EXFALSO -> return goals.replaceFirstGoal(goal.copy(conclusion = Formula.False))
			BY_CONTRA -> return goals.replaceFirstGoal(goal.copy(assumptions = goal.assumptions + Formula.UnaryConnectiveFml(UnaryConnective.NOT, goal.conclusion), conclusion = Formula.False))
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
			USE	->	conclusion is Formula.QuantifiedFml
					&& conclusion.quantifier == Quantifier.THERE_EXISTS
					&& possibleFixedVars(goal).isNotEmpty()
		}
	}
	fun apply(goals: Goals, assumption: Formula): Goals {
		val goal = goals[0]
		when(this) {
			APPLY -> if (assumption is Formula.BinaryConnectiveFml) { // IMPLY
				return goals.replaceFirstGoal(goal.copy(conclusion = assumption.leftFml))
			} else if   (assumption is Formula.UnaryConnectiveFml) {  // NOT
				return goals.replaceFirstGoal(goal.copy(conclusion = assumption.formula))
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
					return goals.replaceFirstGoal(goal.copy(assumptions = removedAssumptions + toRight), goal.copy(assumptions = removedAssumptions + toLeft))
				} else if (assumption is Formula.QuantifiedFml && assumption.quantifier == Quantifier.THERE_EXISTS) {
					if (assumption.bddVar !in goal.fixedVars) {
						return goals.replaceFirstGoal(goal.copy(fixedVars = goal.fixedVars + assumption.bddVar, assumptions = removedAssumptions + assumption.formula))
					} else {
						// Suppose that the given assumption is the form of "ex x, P x" but "x" is already in bddVars.
						// "x" must be arbitrary, so change "x" to "x_1" and "P x" to "P x_1".
						var n = 1
						while (true) {
							val newFixedVar = Var(assumption.bddVar.id + "_$n")
							if (newFixedVar !in goal.fixedVars) {
								return goals.replaceFirstGoal(goal.copy(fixedVars = goal.fixedVars + newFixedVar, assumptions = removedAssumptions + assumption.formula.replace(assumption.bddVar, newFixedVar)))
							} else {
								n++
							}
						}
					}
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
					return goals.replaceFirstGoal(goal.copy(fixedVars = goal.fixedVars.filterNot { it == fixedVar }, conclusion = goal.conclusion.formula.replace(goal.conclusion.bddVar, fixedVar)))
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
					||  (it is Formula.UnaryConnectiveFml   && it.connective == UnaryConnective.NOT     && goal.conclusion == Formula.False) }
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
			is Formula.BinaryConnectiveFml -> goals.replaceFirstGoal(goal.copy(assumptions = goal.assumptions + assumptionApply.rightFml))
			// NOT
			is Formula.UnaryConnectiveFml -> goals.replaceFirstGoal(goal.copy(assumptions = goal.assumptions + Formula.False))
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
					&& assumptionApply.formula == assumptionApplied) {
					result.add(Pair(assumptionApply, assumptionApplied))
				}
			}
		}
		return result
	}
	fun possibleAssumptionsWithFixedVar(goal: Goal): List<Formula> = goal.assumptions
		.filter { it is Formula.QuantifiedFml && it.quantifier == Quantifier.FOR_ALL }
}
