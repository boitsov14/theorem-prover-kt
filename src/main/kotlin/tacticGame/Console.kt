package tacticGame

import core.Formula.*
import tacticGame.Tactic0.*
import tacticGame.Tactic1WithFml.*

fun prove(firstGoals: Goals) {
	val start = System.currentTimeMillis()
	val histories = ArrayDeque<History>()
	histories.add(listOf())
	val oldGoals = mutableSetOf<Goals>()
	var count = 0
	var duplicate = 0
	while (true) {
		val history0 = histories.removeFirst()
		val goals0 = history0.applyTactics(firstGoals)
		val history = history0 + applyManyBasicTactics(goals0)
		val goals = history.applyTactics(firstGoals)
		if (goals.isEmpty()) {
			val end = System.currentTimeMillis()
			val time = end - start
			println("Completed in $time ms")
			println("proof size: ${history.size}")
			println("loop count: $count")
			println("histories size: ${histories.size}")
			println("oldGoals size: ${oldGoals.size}")
			println("duplicate count: $duplicate")
			if (Tactic0.ApplyData(BY_CONTRA) in history) {
				println("classic")
			} else {
				println("intuitionistic")
			}
			printHistory(firstGoals, history)
			break
		}
		val goal = goals.first()
		if (LEFT.canApply(goal)) {
			histories.addFirst(history + Tactic0.ApplyData(RIGHT))
			histories.addFirst(history + Tactic0.ApplyData(LEFT))
		}
		oldGoals.add(goals)
		for (applyData in applyAdvancedTactic(goal)) {
			val newGoals = applyData.applyTactic(goals)
			if (newGoals in oldGoals) {
				duplicate++
				continue
			}
			oldGoals.add(newGoals)
			histories.add(history + applyData)
		}
		count++
	}
}

fun letMeProve(firstGoals: Goals) {
	val history = mutableListOf<IApplyData>()
	while (true) {
		val goals = history.applyTactics(firstGoals)
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
				if (tactic == USE_WITHOUT_FIXED_VARS) {
					goal.conclusion as EXISTS
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
				if (tactic == HAVE_IMPLIES || tactic == HAVE_IMPLIES_WITHOUT_LEFT) {
					assumption as IMPLIES
					println("PAIR >>> ${assumption.leftFml}")
					print("PRESS ENTER >>> ")
					readLine()
				}
				if (tactic == HAVE_NOT) {
					assumption as NOT
					println("PAIR >>> ${assumption.operandFml}")
					print("PRESS ENTER >>> ")
					readLine()
				}
				if (tactic == HAVE_WITHOUT_FIXED_VARS) {
					assumption as ALL
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

fun printGoals(goals: Goals) {
	for (goal in goals) {
		if (goal.freeVars.isNotEmpty()) println(goal.freeVars.joinToString(separator = " ", postfix = " : Fixed"))
		goal.assumptions.forEach { println("$it") }
		println("⊢ " + "${goal.conclusion}")
	}
}

fun printHistory(firstGoals: Goals, history: History) {
	var goals = firstGoals
	for (applyData in history) {
		printGoals(goals)
		print(">>> ")
		println(applyData.getString())
		goals = applyData.applyTactic(goals)
	}
}

fun IApplyData.getString(): String = when(this) {
	is Tactic0.ApplyData -> "${this.tactic0}"
	is Tactic1WithFml.ApplyData -> "${this.tactic1WithFml} ${this.assumption}"
	is Tactic1WithVar.ApplyData -> "${this.tactic1WithVar} ${this.fixedVar}"
	is Tactic2WithVar.ApplyData -> "${this.tactic2WithVar} ${this.assumption} ${this.fixedVar}"
}
