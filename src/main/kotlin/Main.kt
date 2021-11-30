import core.formula.*
import core.parser.*
import core.tactic.*

/*
(all x, P x) to (ex x, P x)
(ex y, all x, P x y) to (all x, ex y, P x y)
not (P and Q) to (not P or not Q)
P and not P to Q
P to Q to (P and Q to R and S) to R
((A to B) to A) to A
 */

fun main() {
	val history = mutableListOf<IApplyData>()
	print("INPUT A FORMULA >>> ")
	val fml = readLine()!!.parse()
	val firstGoals = Goal(fml).toGoals()

	while (true) {
		val goals = history.apply(firstGoals)
		if (goals.isEmpty()) { break }
		println("--------------------------------------")
		printGoals(goals)
		val goal = goals.first()
		print("APPLICABLE TACTICS >>> ")
		println(goal.applicableTactics().joinToString())
		print("SELECT A TACTIC >>> ")
		val tacticStr = readLine()!!
		if (tacticStr == "back") {
			history.removeLast()
			continue
		}
		when(val tactic = goal.applicableTactics().find { "$it" == tacticStr }!!) {
			is Tactic0 -> {
				history.add(Tactic0.ApplyData(tactic))
				if (tactic == Tactic0.USE_WITHOUT_FIXED_VARS) {
					goal.conclusion as Formula.EXISTS
					println("USE >>> ${goal.conclusion.bddVar}")
					print("PRESS ENTER >>> ")
					readLine()
				}
			}
			is Tactic1WithFml -> {
				print("AVAILABLE FORMULAS >>> ")
				println(tactic.availableAssumptions(goal).joinToString())
				print("SELECT A FORMULA >>> ")
				val assumptionNum = readLine()!!.toInt()
				val assumption = tactic.availableAssumptions(goal)[assumptionNum]
				history.add(Tactic1WithFml.ApplyData(tactic, assumption))
				if (tactic == Tactic1WithFml.HAVE_IMPLIES || tactic == Tactic1WithFml.HAVE_IMPLIES_WITHOUT_LEFT) {
					assumption as Formula.IMPLIES
					println("PAIR >>> ${assumption.leftFml}")
					print("PRESS ENTER >>> ")
					readLine()
				}
				if (tactic == Tactic1WithFml.HAVE_NOT) {
					assumption as Formula.NOT
					println("PAIR >>> ${assumption.operandFml}")
					print("PRESS ENTER >>> ")
					readLine()
				}
				if (tactic == Tactic1WithFml.HAVE_WITHOUT_FIXED_VARS) {
					assumption as Formula.ALL
					println("HAVE >>> ${assumption.bddVar}")
					print("PRESS ENTER >>> ")
					readLine()
				}
			}
			is Tactic1WithVar -> {
				print("AVAILABLE VARIABLES >>> ")
				println(tactic.availableFixedVars(goal).joinToString())
				print("SELECT A VARIABLE >>> ")
				val varStr = readLine()!!
				val inputVar = tactic.availableFixedVars(goal).find { "$it" == varStr }!!
				history.add(Tactic1WithVar.ApplyData(tactic, inputVar))
			}
			is Tactic2WithVar -> {
				print("AVAILABLE FORMULAS >>> ")
				val possibleAssumptions = tactic.availablePairsOfAssumptionAndFixedVar(goal).map { it.first }.distinct()
				println(possibleAssumptions.joinToString())
				print("SELECT A FORMULA >>> ")
				val assumptionNum = readLine()!!.toInt()
				val assumption = possibleAssumptions[assumptionNum]
				print("AVAILABLE VARIABLES >>> ")
				val possibleVars = tactic.availablePairsOfAssumptionAndFixedVar(goal).filter { it.first == assumption }.map { it.second }
				println(possibleVars.joinToString())
				print("SELECT A VARIABLE >>> ")
				val varStr = readLine()!!
				val inputVar = possibleVars.find { "$it" == varStr }!!
				history.add(Tactic2WithVar.ApplyData(tactic, assumption, inputVar))
			}
		}
	}
	println("--------------------------------------")
	println("Proof complete!")
}
/*
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
	//val str = "ex x, ex x_1, P x x_1 x_2 y"
	val str = "P x and ex x , Q x and P x"
	val fml = parse(str)
	println(fml)
	try {
		println(fml.replace(x, x_1))
	} catch (e: DuplicateBddVarException) {
		println(e)
	}
	 */

}
 */

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
