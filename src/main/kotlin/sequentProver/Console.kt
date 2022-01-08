package sequentProver

fun Sequents.prove() {
	val start = System.currentTimeMillis()
	var count = 0
	val history = mutableListOf<IApplyData>()

	while (true) {
		val sequents = history.applyTactics(this)
		printSequents(sequents)
		if (sequents.isEmpty()) {
			println("PROOF SUCCEED!")
			break
		}
		val sequent = sequents.first()
		val applyData = applyBasicTacticOrNull(sequent)
		if (applyData == null) {
			println("PROOF FAILED")
			break
		}
		println(">>> ${applyData.tactic}")
		history.add(applyData)
		count++
	}
	val end = System.currentTimeMillis()
	val time = end - start
	println("Completed in $time ms")
	println("loop count: $count")
}

fun printSequents(sequents: Sequents) {
	sequents.forEach { println(it) }
}
