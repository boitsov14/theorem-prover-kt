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
							currentGoals = currentGoals.replaceFirstGoal(currentGoals[0].copy(fixedVars = currentGoals[0].fixedVars + assumption.bddVar))
						}
					}
				}
			}
		}
	}
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
