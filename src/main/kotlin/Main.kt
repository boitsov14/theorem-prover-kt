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

	val currentHistories: Histories = mutableListOf()
	print("Input a formula you want to prove >>> ")
	var currentGoals = listOf(Goal(readLine()!!.parse()!!))

	while (currentGoals.isNotEmpty()) {
		println("--------------------------------------")
		printGoals(currentGoals)
		val currentGoal = currentGoals[0]
		print("Possible tactics are >>> ")
		println(currentGoal.possibleTactics().joinToString())
		print("Select a tactic >>> ")
		when (val tactic = currentGoal.possibleTactics()[readLine()!!.toInt()]) {
			is Tactic0 -> {
				currentHistories.add(History0(currentGoals, tactic))
				currentGoals = tactic.apply(currentGoals)
			}
			is Tactic1 -> {
				print("Possible variables are >>> ")
				println(tactic.possibleFixedVars(currentGoal).joinToString())
				print("Possible formulas are  >>> ")
				println(tactic.possibleAssumptions(currentGoal).joinToString())
				print("Select an variable or an formula >>> ")
				val inputList = readLine()!!.split(" ").map(String::toInt)
				val input = inputList[1]
				when (inputList[0]) {
					0 -> {
						val fixedVar = tactic.possibleFixedVars(currentGoal)[input]
						currentHistories.add(History1WithVar(currentGoals, tactic, fixedVar))
						currentGoals = tactic.apply(currentGoals, fixedVar)
					}
					1 -> {
						val assumption = tactic.possibleAssumptions(currentGoal)[input]
						currentHistories.add(History1WithFormula(currentGoals, tactic, assumption))
						currentGoals = tactic.apply(currentGoals, assumption)
					}
				}
			}
			is Tactic2 -> {
				print("Possible formulas are >>> ")
				println(tactic.possibleAssumptionsPairs(currentGoal).map { it.first }.distinct().joinToString()) // don't need distinct() in an app
				print("Possible formulas are >>> ")
				println(tactic.possibleAssumptionsWithFixedVar(currentGoal).joinToString())
				print("Select a formula >>> ")
				val inputList = readLine()!!.split(" ").map(String::toInt)
				val input = inputList[1]
				when (inputList[0]) {
					0 -> {
						val assumptionApply = tactic.possibleAssumptionsPairs(currentGoal).map { it.first }.distinct()[input]
						print("Possible formulas are >>> ")
						println(tactic.possibleAssumptionsPairs(currentGoal).filter { it.first == assumptionApply }.map { it.second }.joinToString())
						print("Select a formula >>> ")
						val assumptionApplied = tactic.possibleAssumptionsPairs(currentGoal).filter { it.first == assumptionApply }.map { it.second }[readLine()!!.toInt()]
						currentHistories.add(History2WithFormulaAndFormula(currentGoals, tactic, assumptionApply, assumptionApplied))
						currentGoals = tactic.apply(currentGoals, assumptionApply, assumptionApplied)
					}
					1 -> {
						val assumption = tactic.possibleAssumptionsWithFixedVar(currentGoal)[input]
						if (assumption !is Formula.QuantifiedFml) {break}
						if (assumption.bddVar !in currentGoal.fixedVars) {
							val tempCurrentGoals = currentGoals.replaceFirstGoal(currentGoal.copy(fixedVars = currentGoal.fixedVars + assumption.bddVar))
							val tempCurrentGoal = tempCurrentGoals[0]
							print("Possible fixed variables are >>> ")
							println(tempCurrentGoal.fixedVars.joinToString())
							print("Select a fixed variable >>> ")
							val fixedVar = tempCurrentGoal.fixedVars[readLine()!!.toInt()]
							currentHistories.add(History2WithFormulaAndVar(currentGoals, tactic, assumption, fixedVar))
							currentGoals = if (fixedVar != assumption.bddVar) {
								tactic.apply(currentGoals, assumption, fixedVar)
							} else {
								tactic.apply(tempCurrentGoals, assumption, fixedVar)
							}
						} else {
							print("Possible fixed variables are >>> ")
							println(currentGoal.fixedVars.joinToString())
							print("Select a fixed variable >>> ")
							val fixedVar = currentGoal.fixedVars[readLine()!!.toInt()]
							currentHistories.add(History2WithFormulaAndVar(currentGoals, tactic, assumption, fixedVar))
							currentGoals = tactic.apply(currentGoals, assumption, fixedVar)
						}
					}
				}
			}
		}
	}
	println("--------------------------------------")
	println("Proof complete!")
	println("The following is the histories")
	printHistories(currentHistories)
	println("--------------------------------------")
	println("Proof complete!")

}

fun printGoals(goals: Goals) {
	for (goal in goals) {
		if (goal.fixedVars.isNotEmpty()) println(goal.fixedVars.joinToString(separator = " ", postfix = " : Fixed"))
		goal.assumptions.forEach { println("$it".removeSurrounding("(", ")")) }
		println("⊢ " + "${goal.conclusion}".removeSurrounding("(", ")"))
	}
}

fun printHistories(histories: Histories) {
	for (history in histories) {
		println("--------------------------------------")
		printGoals(history.previousGoals)
		println()
		print(">>> ")
		println(history)
	}
}
