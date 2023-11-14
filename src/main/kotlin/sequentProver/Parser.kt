package sequentProver

import core.*
import java.text.Normalizer

private fun String.toFormulas(): Set<Formula> {
	val fmls = mutableSetOf<Formula>()
	var counter = 0
	var startPos = 0
	for ((index, chr) in withIndex()) {
		when (chr) {
			'(' -> counter++
			')' -> counter--
			',' -> {
				if (counter == 0) {
					val str = substring(startPos, index)
					if (('∀' !in str && '∃' !in str) || !("""[a-zA-Zα-ωΑ-Ω]\d*(,[a-zA-Zα-ωΑ-Ω]\d*)*""".toRegex()
							.matches(str.takeLastWhile { it !in setOf('∀', '∃') }))
					) {
						fmls.add(str.parseToFormula())
						startPos = index + 1
					}
				}
			}
		}
	}
	if (counter != 0) throw FormulaParserException("Parenthesis Error.")
	val lastFml = substring(startPos).parseToFormula()
	fmls.add(lastFml)
	return fmls
}

fun String.parseToSequent(): Sequent {
	val str = Normalizer.normalize(this, Normalizer.Form.NFKC).toOneLetter().trimSpace()
	return when (str.count { it == '⊢' }) {
		0 -> {
			val fml = str.parseToFormula()
			Sequent(emptySet(), setOf(fml))
		}

		1 -> {
			val strList = str.split("⊢")
			val assumptions = if (strList[0].isNotEmpty()) {
				strList[0].toFormulas()
			} else {
				emptySet()
			}
			val conclusions = if (strList[1].isNotEmpty()) {
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
