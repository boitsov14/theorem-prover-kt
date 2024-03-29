package core

import core.Term.Var

class DuplicateBddVarException : Exception()

sealed class Formula {
	object TRUE : Formula()
	object FALSE : Formula()
	data class PREDICATE(val id: String, val terms: List<Term>) : Formula()
	data class NOT(val operandFml: Formula) : Formula()
	data class AND(val leftFml: Formula, val rightFml: Formula) : Formula()
	data class OR(val leftFml: Formula, val rightFml: Formula) : Formula()
	data class IMPLIES(val leftFml: Formula, val rightFml: Formula) : Formula()
	data class IFF(val leftFml: Formula, val rightFml: Formula) : Formula()
	sealed class Quantified : Formula() {
		abstract val bddVar: Var
		abstract val operandFml: Formula
		fun instantiate(newTerm: Term): Formula = operandFml.replace(bddVar, newTerm)
		final override fun equals(other: Any?): Boolean {
			if (this === other) return true
			if (javaClass != other?.javaClass) return false
			other as Quantified
			if (bddVar == other.bddVar) return operandFml == other.operandFml
			if (bddVar in other.operandFml.freeVars) return false
			if (operandFml == other.instantiate(bddVar)) return true
			return false
		}

		final override fun hashCode(): Int = 31 * javaClass.hashCode() + operandFml.javaClass.hashCode()
	}

	data class ALL(override val bddVar: Var, override val operandFml: Formula) : Quantified() {
		init {
			if (bddVar in operandFml.bddVars) throw DuplicateBddVarException()
		}
	}

	data class EXISTS(override val bddVar: Var, override val operandFml: Formula) : Quantified() {
		init {
			if (bddVar in operandFml.bddVars) throw DuplicateBddVarException()
		}
	}

	private fun toStringRec(): String = when (this) {
		TRUE -> "true"
		FALSE -> "false"
		is PREDICATE -> id + if (terms.isNotEmpty()) terms.joinToString(
			separator = ",", prefix = "(", postfix = ")"
		) else ""

		is NOT -> "¬${operandFml.toStringRec()}"
		is AND -> "(${leftFml.toStringRec()} ∧ ${
			if (rightFml is AND) rightFml.toStringRec().removeSurrounding("(", ")") else rightFml.toStringRec()
		})"

		is OR -> "(${leftFml.toStringRec()} ∨ ${
			if (rightFml is OR) rightFml.toStringRec().removeSurrounding("(", ")") else rightFml.toStringRec()
		})"

		is IMPLIES -> "(${leftFml.toStringRec()} → ${rightFml.toStringRec()})"
		is IFF -> "(${leftFml.toStringRec()} ↔ ${rightFml.toStringRec()})"
		is ALL -> "∀$bddVar${
			if (operandFml is ALL) ',' + operandFml.toStringRec().drop(1) else operandFml.toStringRec()
		}"

		is EXISTS -> "∃$bddVar${
			if (operandFml is EXISTS) ',' + operandFml.toStringRec().drop(1) else operandFml.toStringRec()
		}"
	}

	final override fun toString(): String = toStringRec().removeSurrounding("(", ")")

	fun toLatex(): String =
		toString().replace("true", """\top""").replace("false", """\bot""").replace("¬", """\lnot """)
			.replace("∧", """\land""").replace("∨", """\lor""").replace("→", """\rightarrow""")
			.replace("↔", """\leftrightarrow""").replace("∀", """\forall """).replace("∃", """\exists """).toGreekName()

	private fun String.toGreekName(): String =
		greekLetters.zip(greekNames).fold(this) { temp, (letter, name) -> temp.replace(letter, name) }

	private val greekLetters = "αβγδεζηθικλμνξοπρστυφχψωΑΒΓΔΕΖΗΘΙΚΛΜΝΞΟΠΡΣΤΥΦΧΨΩ".map { it.toString() }

	private val greekNames = listOf(
		"""\alpha """,
		"""\beta """,
		"""\gamma """,
		"""\delta """,
		"""\varepsilon """,
		"""\zeta """,
		"""\eta """,
		"""\theta """,
		"""\iota """,
		"""\kappa """,
		"""\lambda """,
		"""\mu """,
		"""\nu """,
		"""\xi """,
		"o",
		"""\pi """,
		"""\rho """,
		"""\sigma """,
		"""\tau """,
		"""\upsilon """,
		"""\varphi """,
		"""\chi """,
		"""\psi """,
		"""\omega """,
		"A",
		"B",
		"""\Gamma """,
		"""\Delta """,
		"E",
		"Z",
		"H",
		"""\Theta """,
		"I",
		"K",
		"""\Lambda """,
		"M",
		"N",
		"""\Xi """,
		"O",
		"""\Pi """,
		"P",
		"""\Sigma """,
		"T",
		"""\Upsilon """,
		"""\Phi """,
		"X",
		"""\Psi """,
		"""\Omega """
	)

	val freeVars: Set<Var>
		get() = when (this) {
			TRUE, FALSE -> emptySet()
			is PREDICATE -> terms.flatMap { it.freeVars }.toSet()
			is NOT -> operandFml.freeVars
			is AND -> leftFml.freeVars + rightFml.freeVars
			is OR -> leftFml.freeVars + rightFml.freeVars
			is IMPLIES -> leftFml.freeVars + rightFml.freeVars
			is IFF -> leftFml.freeVars + rightFml.freeVars
			is Quantified -> operandFml.freeVars.minus(bddVar)
		}
	val bddVars: Set<Var>
		get() = when (this) {
			TRUE, FALSE, is PREDICATE -> emptySet()
			is NOT -> operandFml.bddVars
			is AND -> leftFml.bddVars + rightFml.bddVars
			is OR -> leftFml.bddVars + rightFml.bddVars
			is IMPLIES -> leftFml.bddVars + rightFml.bddVars
			is IFF -> leftFml.bddVars + rightFml.bddVars
			is Quantified -> operandFml.bddVars + bddVar
		}
	val predicateIds: Set<String>
		get() = when (this) {
			TRUE, FALSE -> emptySet()
			is PREDICATE -> setOf(id)
			is NOT -> operandFml.predicateIds
			is AND -> leftFml.predicateIds + rightFml.predicateIds
			is OR -> leftFml.predicateIds + rightFml.predicateIds
			is IMPLIES -> leftFml.predicateIds + rightFml.predicateIds
			is IFF -> leftFml.predicateIds + rightFml.predicateIds
			is Quantified -> operandFml.predicateIds
		}
	val functionIds: Set<String>
		get() = when (this) {
			TRUE -> emptySet()
			FALSE -> emptySet()
			is PREDICATE -> terms.flatMap { it.functionIds }.toSet()
			is NOT -> operandFml.functionIds
			is AND -> leftFml.functionIds + rightFml.functionIds
			is OR -> leftFml.functionIds + rightFml.functionIds
			is IMPLIES -> leftFml.functionIds + rightFml.functionIds
			is IFF -> leftFml.functionIds + rightFml.functionIds
			is Quantified -> operandFml.functionIds
		}

	fun replace(oldVar: Var, newTerm: Term): Formula = when (this) {
		TRUE, FALSE -> this
		is PREDICATE -> PREDICATE(id, terms.map { it.replace(oldVar, newTerm) })
		is NOT -> NOT(operandFml.replace(oldVar, newTerm))
		is AND -> AND(leftFml.replace(oldVar, newTerm), rightFml.replace(oldVar, newTerm))
		is OR -> OR(leftFml.replace(oldVar, newTerm), rightFml.replace(oldVar, newTerm))
		is IMPLIES -> IMPLIES(leftFml.replace(oldVar, newTerm), rightFml.replace(oldVar, newTerm))
		is IFF -> IFF(leftFml.replace(oldVar, newTerm), rightFml.replace(oldVar, newTerm))
		is Quantified -> {
			if (oldVar == bddVar) {
				this
			} else if (bddVar in newTerm.freeVars) {
				val newBddVar = bddVar.getFreshVar(operandFml.bddVars + operandFml.freeVars + newTerm.freeVars)
				when (this) {
					is ALL -> ALL(newBddVar, operandFml.replace(bddVar, newBddVar).replace(oldVar, newTerm))
					is EXISTS -> EXISTS(newBddVar, operandFml.replace(bddVar, newBddVar).replace(oldVar, newTerm))
				}
			} else {
				when (this) {
					is ALL -> ALL(bddVar, operandFml.replace(oldVar, newTerm))
					is EXISTS -> EXISTS(bddVar, operandFml.replace(oldVar, newTerm))
				}
			}
		}
	}

	fun replace(substitution: Substitution): Formula = when (this) {
		TRUE, FALSE -> this
		is PREDICATE -> PREDICATE(id, terms.map { it.replace(substitution) })
		is NOT -> NOT(operandFml.replace(substitution))
		is AND -> AND(leftFml.replace(substitution), rightFml.replace(substitution))
		is OR -> OR(leftFml.replace(substitution), rightFml.replace(substitution))
		is IMPLIES -> IMPLIES(
			leftFml.replace(substitution), rightFml.replace(substitution)
		)

		is IFF -> IFF(leftFml.replace(substitution), rightFml.replace(substitution))
		is Quantified -> {
			when (this) {
				is ALL -> ALL(bddVar, operandFml.replace(substitution))
				is EXISTS -> EXISTS(bddVar, operandFml.replace(substitution))
			}
		}
	}

	// TODO: 2022/07/21 check the errata!
	internal fun simplify0(): Formula = when (this) {
		NOT(FALSE) -> TRUE
		NOT(TRUE) -> FALSE
		is NOT -> if (operandFml is NOT) operandFml.operandFml else this
		is AND -> if (leftFml == FALSE || rightFml == FALSE) FALSE
		else if (leftFml == TRUE) rightFml
		else if (rightFml == TRUE) leftFml
		else this

		is OR -> if (leftFml == TRUE || rightFml == TRUE) TRUE
		else if (leftFml == FALSE) rightFml
		else if (rightFml == FALSE) leftFml
		else this

		is IMPLIES -> if (leftFml == FALSE || rightFml == TRUE) TRUE
		else if (leftFml == TRUE) rightFml
		else if (rightFml == FALSE) NOT(leftFml)
		else this

		is IFF -> if (leftFml == TRUE) rightFml
		else if (rightFml == TRUE) leftFml
		else if (leftFml == FALSE) NOT(rightFml)
		else if (rightFml == FALSE) NOT(leftFml)
		else this

		else -> this
	}

	internal fun simplify(): Formula = when (this) {
		is NOT -> NOT(operandFml.simplify()).simplify0()
		is AND -> AND(leftFml.simplify(), rightFml.simplify()).simplify0()
		is OR -> OR(leftFml.simplify(), rightFml.simplify()).simplify0()
		is IMPLIES -> IMPLIES(leftFml.simplify(), rightFml.simplify()).simplify0()
		is IFF -> IFF(leftFml.simplify(), rightFml.simplify()).simplify0()
		else -> this
	}

	private fun negate(): Formula = if (this is NOT) operandFml else NOT(this)

	internal fun pureNNF(): Formula = when (this) {
		is NOT -> when (operandFml) {
			is NOT -> operandFml.operandFml.pureNNF()
			is AND -> OR(NOT(operandFml.leftFml).pureNNF(), NOT(operandFml.rightFml).pureNNF())
			is OR -> AND(NOT(operandFml.leftFml).pureNNF(), NOT(operandFml.rightFml).pureNNF())
			is IMPLIES -> AND(operandFml.leftFml.pureNNF(), NOT(operandFml.rightFml).pureNNF())
			is IFF -> OR(
				AND(operandFml.leftFml.pureNNF(), NOT(operandFml.rightFml).pureNNF()),
				AND(NOT(operandFml.leftFml).pureNNF(), operandFml.rightFml.pureNNF())
			)

			else -> this
		}

		is AND -> AND(leftFml.pureNNF(), rightFml.pureNNF())
		is OR -> OR(leftFml.pureNNF(), rightFml.pureNNF())
		is IMPLIES -> OR(NOT(leftFml).pureNNF(), rightFml.pureNNF())
		is IFF -> OR(AND(leftFml.pureNNF(), rightFml.pureNNF()), AND(NOT(leftFml).pureNNF(), NOT(rightFml).pureNNF()))
		else -> this
	}

	internal fun efficientNNF(): Formula = when (this) {
		is NOT -> when (operandFml) {
			is NOT -> operandFml.operandFml.efficientNNF()
			is AND -> OR(NOT(operandFml.leftFml).efficientNNF(), NOT(operandFml.rightFml).efficientNNF())
			is OR -> AND(NOT(operandFml.leftFml).efficientNNF(), NOT(operandFml.rightFml).efficientNNF())
			is IMPLIES -> AND(operandFml.leftFml.efficientNNF(), NOT(operandFml.rightFml).efficientNNF())
			is IFF -> IFF(operandFml.leftFml.efficientNNF(), NOT(operandFml.rightFml).efficientNNF())
			else -> this
		}

		is AND -> AND(leftFml.efficientNNF(), rightFml.efficientNNF())
		is OR -> OR(leftFml.efficientNNF(), rightFml.efficientNNF())
		is IMPLIES -> OR(NOT(leftFml).efficientNNF(), rightFml.efficientNNF())
		is IFF -> IFF(leftFml.efficientNNF(), rightFml.efficientNNF())
		else -> this
	}

	internal fun pureDNF(): Set<Set<Formula>> = when (this) {
		is AND -> distribute(leftFml.pureDNF(), rightFml.pureDNF())
		is OR -> leftFml.pureDNF() + rightFml.pureDNF()
		else -> setOf(setOf(this))
	}

	internal fun simpleDNF(): Set<Set<Formula>> = when (this) {
		TRUE -> setOf(emptySet())
		FALSE -> emptySet()
		else -> {
			val disjunctions = simplify().pureNNF().pureDNF().filterNot { isTrivial(it) }
			disjunctions.filter { d -> disjunctions.none { d0 -> d.containsAll(d0) && d0 != d } }.toSet()
		}
	}

	private fun pureCNF(): Set<Set<Formula>> = when (this) {
		is AND -> leftFml.pureCNF() + rightFml.pureCNF()
		is OR -> distribute(leftFml.pureCNF(), rightFml.pureCNF())
		else -> setOf(setOf(this))
	}

	internal fun simpleCNF(): Set<Set<Formula>> = when (this) {
		TRUE -> emptySet()
		FALSE -> setOf(emptySet())
		else -> {
			val conjunctions = simplify().pureNNF().pureCNF().filterNot { isTrivial(it) }
			conjunctions.filter { d -> conjunctions.none { d0 -> d.containsAll(d0) && d0 != d } }.toSet()
		}
	}

	private fun mainCNF(defs: Map<Formula, PREDICATE>, n: Int): Triple<Formula, Map<Formula, PREDICATE>, Int> =
		when (this) {
			is AND -> {
				val (fml0, defs0, n0) = leftFml.mainCNF(defs, n)
				val (fml1, defs1, n1) = rightFml.mainCNF(defs0, n0)
				val fml = AND(fml0, fml1)
				if (fml in defs1.keys) {
					Triple(defs1[fml]!!, defs1, n1)
				} else {
					val atom = PREDICATE("Def_$n1", emptyList())
					val newDefs = defs1 + (fml to atom)
					Triple(atom, newDefs, n1 + 1)
				}
			}

			is OR -> {
				val (fml0, defs0, n0) = leftFml.mainCNF(defs, n)
				val (fml1, defs1, n1) = rightFml.mainCNF(defs0, n0)
				val fml = OR(fml0, fml1)
				if (fml in defs1.keys) {
					Triple(defs1[fml]!!, defs1, n1)
				} else {
					val atom = PREDICATE("Def_$n1", emptyList())
					val newDefs = defs1 + (fml to atom)
					Triple(atom, newDefs, n1 + 1)
				}
			}

			is IFF -> {
				val (fml0, defs0, n0) = leftFml.mainCNF(defs, n)
				val (fml1, defs1, n1) = rightFml.mainCNF(defs0, n0)
				val fml = IFF(fml0, fml1)
				if (fml in defs1.keys) {
					Triple(defs1[fml]!!, defs1, n1)
				} else {
					val atom = PREDICATE("Def_$n1", emptyList())
					val newDefs = defs1 + (fml to atom)
					Triple(atom, newDefs, n1 + 1)
				}
			}

			else -> Triple(this, defs, n)
		}

	internal fun makeDefCNF(): Set<Set<Formula>> {
		val (fml, defs0, _) = simplify().efficientNNF().mainCNF(emptyMap(), 0)
		return defs0.map { (key, value) -> IFF(value, key).simpleCNF() }
			.reduce { acc, sets -> acc + sets } + fml.simpleCNF()
	}

	private fun subCNF(defs: Map<Formula, PREDICATE>, n: Int): Triple<Formula, Map<Formula, PREDICATE>, Int> =
		when (this) {
			is AND -> {
				val (fml0, defs0, n0) = leftFml.andCNF(defs, n)
				val (fml1, defs1, n1) = rightFml.andCNF(defs0, n0)
				Triple(AND(fml0, fml1), defs1, n1)
			}

			is OR -> {
				val (fml0, defs0, n0) = leftFml.orCNF(defs, n)
				val (fml1, defs1, n1) = rightFml.orCNF(defs0, n0)
				Triple(OR(fml0, fml1), defs1, n1)
			}

			else -> throw IllegalArgumentException()
		}

	private fun orCNF(defs: Map<Formula, PREDICATE>, n: Int): Triple<Formula, Map<Formula, PREDICATE>, Int> =
		when (this) {
			is OR -> {
				subCNF(defs, n)
			}

			else -> mainCNF(defs, n)
		}

	private fun andCNF(defs: Map<Formula, PREDICATE>, n: Int): Triple<Formula, Map<Formula, PREDICATE>, Int> =
		when (this) {
			is AND -> {
				subCNF(defs, n)
			}

			else -> orCNF(defs, n)
		}

	fun defCNF(): Set<Set<Formula>> {
		val (fml, defs0, _) = simplify().efficientNNF().andCNF(emptyMap(), 0)
		return defs0.map { (key, value) -> IFF(value, key).simpleCNF() }
			.fold(fml.simpleCNF()) { acc, sets -> acc + sets }
	}


}

private fun distribute(fmlsSet0: Set<Set<Formula>>, fmlsSet1: Set<Set<Formula>>): Set<Set<Formula>> {
	val result = mutableSetOf<Set<Formula>>()
	for (fmls0 in fmlsSet0) {
		for (fmls1 in fmlsSet1) {
			result.add(fmls0 + fmls1)
		}
	}
	return result
}

private fun isTrivial(fmls: Set<Formula>) =
	(fmls.filterIsInstance<Formula.NOT>().map { it.operandFml }.toSet() intersect fmls.filter { it !is Formula.NOT }
		.toSet()).isNotEmpty()

internal fun Iterable<Formula>.makeConjunction(): Formula =
	reversed().reduceOrNull { conj, fml -> Formula.AND(fml, conj) } ?: Formula.TRUE

internal fun Iterable<Formula>.makeDisjunction(): Formula =
	reversed().reduceOrNull { disj, fml -> Formula.OR(fml, disj) } ?: Formula.FALSE
