package sequentProver

import core.*

private fun String.toFormulas(): Set<Formula> {
	val fmls = mutableSetOf<Formula>()
	var counter = 0
	var startPos = 0
	for ((index, chr) in this.withIndex()) {
		when (chr) {
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
	if (counter != 0) throw FormulaParserException("Parenthesis Error.")
	val lastFml = this.substring(startPos).parseToFormula()
	fmls.add(lastFml)
	return fmls
}

fun String.parseToSequent(): Sequent {
	val str = this.toOneLetter()
	return when (str.count { it == '⊢' }) {
		0 -> {
			val fml = str.parseToFormula()
			Sequent(emptySet(), setOf(fml))
		}

		1 -> {
			val strList = str.split("⊢")
			val assumptions = if (strList[0].trim().isNotEmpty()) {
				strList[0].toFormulas()
			} else {
				emptySet()
			}
			val conclusions = if (strList[1].trim().isNotEmpty()) {
				strList[1].toFormulas()
			} else {
				emptySet()
			}
			Sequent(assumptions, conclusions)
		}

		else -> {
			throw FormulaParserException("⊢ must occur one time.")
		}
	}
}
