package sequentProver

import core.*

private fun String.toOneLetter(): String {
	var result = this
	listOf("proves", "prove", "\\vdash", "vdash").forEach { result = result.replace(it, "⊢", true) }
	return result
}

private fun String.toFormulas(): Set<Formula> {
	val fmls = mutableSetOf<Formula>()
	var counter = 0
	var startPos = 0
	for ((index, chr) in this.withIndex()) {
		when(chr) {
			'(' -> counter++
			')' -> counter--
			',' -> {
				if (counter == 0) {
					val fml = this.substring(startPos, index).parseToFormula()
					fmls.add(fml)
					startPos = index + 1
				}
			}
		}
	}
	if (counter != 0) throw FormulaParserException("Parenthesis Error")
	val fml = this.substring(startPos).parseToFormula()
	fmls.add(fml)
	return fmls
}

fun String.parseToSequent(): Sequent {
	val str = this.toOneLetter()
	val count = str.filter { it == '⊢' }.length
	if (count == 0) {
		val fml = str.parseToFormula()
		return Sequent(emptySet(), setOf(fml))
	} else if (count == 1) {
		val strList = str.split("⊢")
		val assumptions = strList[0].toFormulas()
		val conclusions = strList[1].toFormulas()
		return Sequent(assumptions, conclusions)
	} else {
		throw FormulaParserException("⊢ must occur one time")
	}
}
