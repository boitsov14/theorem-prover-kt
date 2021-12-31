package sequentProver

fun Goals.prove() {
	val start = System.currentTimeMillis()
	var count = 0
	val history = mutableListOf<IApplyData>()

	while (true) {
		val goals = history.applyTactics(this)
		printGoals(goals)
		if (goals.isEmpty()) {
			println("PROOF SUCCEED!")
			break
		}
		val goal = goals.first()
		val applyData = applyBasicTacticOrNull(goal)
		if (applyData == null) {
			println("PROOF FAILED")
			break
		}
		println(">>> $applyData")
		history.add(applyData)
		count++
	}
	val end = System.currentTimeMillis()
	val time = end - start
	println("Completed in $time ms")
	println("loop count: $count")
}

fun printGoals(goals: Goals) {
	goals.forEach { println(it) }
}
