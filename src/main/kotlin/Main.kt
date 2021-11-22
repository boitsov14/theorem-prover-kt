import kotlin.system.measureTimeMillis
import core.formula.*
import core.parser.*
import core.tactic.*

fun main() {
	/*
	val x = Var("x")
	val y = Var("y")
	val fml0 = Formula.PREDICATE("P", listOf(x))
	val fml1 = Formula.ALL(x, fml0) // all x, P x
	//val fml2 = Formula.ALL(x, fml1) // throw exception
	//val fml3 = fml1.replace(y, x) // throw exception
	 */

	//println(""" /\ \/ and or forall x ~false""".toUnicode())

	/*
	while (true) {
		print("INPUT A FORMULA >>> ")
		val str = readLine()!!
		try {
			println(parse(str))
		} catch (e: FormulaParserException) {
			println(e.message)
		}
		println("--------------------------------------")
	}
	 */

	/*
	val x = Var("x")
	val x_1 = Var("x_1")
	val x_2 = Var("x_2")
	val y = Var("y")
	val str = "ex x, ex x_1, P x x_1 x_2 y"
	val fml = parse(str)
	println(fml)
	try {
		println(fml.replace(y, x_1))
	} catch (e: DuplicateBddVarException) {
		println(e)
	}
	 */
}

/*
fun main() {
	val currentHistory: History = mutableListOf()
	//print("Input a formula you want to prove >>> ")
	//var currentGoals = listOf(Goal(readLine()!!.parse()!!))
	/*
	not (P and Q) to (not P or not Q)
	not (P and Q and R) to (not P or not Q or not R)
	not (P and Q and R and S) to (not P or not Q or not R or not S)
	not (P and Q and R and S and T) to (not P or not Q or not R or not S or not T)
	*/
	val fml = "(P and Q) to (not P or not Q)"
	println("--------------------------------------")
	var currentGoals = listOf(Goal(fml.parse()!!))
	print("INPUT FORMULA : ")
	printGoals(currentGoals)
	println("--------------------------------------")

	val histories0: List<History>
	val timeInMillis = measureTimeMillis {
		histories0 = prover(currentGoals,false, 30)
	}
	val histories1 = histories0.getIntuitionisticProofs()

	val histories
	= if (histories0.isEmpty()) {
		println("We couldn't find the proof...")
		listOf()
	} else if (histories1.isEmpty()) {
		println("We found (not intuitionistic) proofs!")
		histories0
	} else {
		println("We found intuitionistic proofs!!")
		histories1
	}

	println("TIME >>> $timeInMillis ms")

	/*
	for (history in histories) {
		for (flow in history) {
			println(flow.previousGoals)
		}
		println("--------------------------------------")
	}

	 */


	println("The following is the history")
	printHistory(histories.first())
	println("--------------------------------------")
	println("Proof complete!")



	while (currentGoals.isNotEmpty()) {
		println("--------------------------------------")
		printGoals(currentGoals)
		val currentGoal = currentGoals[0]
		print("Possible tactics are >>> ")
		println(currentGoal.applicableTactics().joinToString())
		print("Select a tactic >>> ")
		when (val tactic = currentGoal.applicableTactics()[readLine()!!.toInt()]) {
			is Tactic0 -> {
				currentHistory.add(FlowOfGoals0(currentGoals, tactic.apply(currentGoals), tactic))
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
						currentHistory.add(FlowOfGoals1WithVar(
							currentGoals,
							tactic.apply(currentGoals, fixedVar),
							tactic,
							fixedVar
						))
					}
					1 -> {
						val assumption = tactic.possibleAssumptions(currentGoal)[input]
						currentHistory.add(FlowOfGoals1WithFormula(
							currentGoals,
							tactic.apply(currentGoals, assumption),
							tactic,
							assumption
						))
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
						currentHistory.add(FlowOfGoals2WithFormulaAndFormula(
							currentGoals,
							tactic.apply(currentGoals, assumptionApply, assumptionApplied),
							tactic,
							assumptionApply,
							assumptionApplied
						))
					}
					1 -> {
						val assumption = tactic.possibleAssumptionsWithFixedVar(currentGoal)[input]
						if (assumption !is Formula.QuantifiedFml) {break}
						val newVar = assumption.bddVar.getNewVar(currentGoal.getAllBddVars() + currentGoal.fixedVars)
						val tempCurrentGoals = currentGoals.replaceFirstGoal(currentGoal.copy(fixedVars = currentGoal.fixedVars + newVar))
						val tempCurrentGoal = tempCurrentGoals[0]
						print("Possible fixed variables are >>> ")
						println(tempCurrentGoal.fixedVars.filterNot { it in assumption.formula.bddVars() }.joinToString())
						print("Select a fixed variable >>> ")
						val inputVar = tempCurrentGoal.fixedVars[readLine()!!.toInt()]
						if (inputVar != newVar) {
							currentHistory.add(FlowOfGoals2WithFormulaAndVar(
								currentGoals,
								tactic.apply(currentGoals, assumption, inputVar),
								tactic,
								assumption,
								inputVar
							))
						} else {
							currentHistory.add(FlowOfGoals2WithFormulaAndVar(
								currentGoals,
								tactic.apply(tempCurrentGoals, assumption, inputVar),
								tactic,
								assumption,
								inputVar
							))
						}
					}
				}
			}
		}
		currentGoals = currentHistory.last().nextGoals
	}
	println("--------------------------------------")
	println("Proof complete!")
	println("The following is the history")
	printHistory(currentHistory)
	println("--------------------------------------")
	println("Proof complete!")

}
*/

fun printGoals(goals: Goals) {
	for (goal in goals) {
		if (goal.fixedVars.isNotEmpty()) println(goal.fixedVars.joinToString(separator = " ", postfix = " : Fixed"))
		goal.assumptions.forEach { println("$it") }
		println("⊢ " + "${goal.conclusion}")
	}
}

// TODO: 2021/11/01 Need to rewrite
/*
fun printHistory(history: History) {
	for (flow in history) {
		println("--------------------------------------")
		printGoals(flow.previousGoals)
		println("--------------------------------------")
		print(">>> ")
		println(flow)
	}
}
 */

/*
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
	*/
