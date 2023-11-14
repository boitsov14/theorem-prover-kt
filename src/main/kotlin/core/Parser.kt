package core

import core.Formula.*
import core.Term.Function
import core.Term.Var
import java.text.Normalizer.Form
import java.text.Normalizer.normalize

class FormulaParserException(message: String) : Exception(message)

fun String.parseToFormula(): Formula =
	normalize(this, Form.NFKC).toOneLetter().trimSpace().tokenize().toRPN().makeFormula()

private sealed interface Token {
	data object LP : Token
	data object RP : Token
	sealed interface Operator : Token {
		val precedence: Int

		enum class Binary(override val precedence: Int) : Operator {
			AND(3), OR(2), IMPLIES(1), IFF(0)
		}

		sealed interface Unary : Operator {
			data object NOT : Unary {
				override val precedence = 4
			}

			data class ALL(val bddVar: Var) : Unary {
				override val precedence = 4
			}

			data class EXISTS(val bddVar: Var) : Unary {
				override val precedence = 4
			}
		}
	}

	data class PREDICATE(val id: String, val terms: List<Term>) : Token
	data object TRUE : Token
	data object FALSE : Token
}

// TODO: 2023/01/02 privateにする？
fun String.toOneLetter(): String = listOf(
	'⊢' to setOf("proves", "vdash", """\vdash""", "|-", "├", "┣"),
	'⊤' to setOf("true", "tautology", "top", """\top"""),
	'⊥' to setOf("false", "contradiction", "bottom", "bot", """\bot"""),
	'¬' to setOf("not", "~", "negation", "lnot", """\lnot""", "neg", """\neg"""),
	'∧' to setOf("and", "land", """\land""", """/\""", "&", "&&", "wedge", """\wedge"""),
	'∨' to setOf("or", "lor", """\lor""", """\/""", "|", "||", "vee", """\vee"""),
	'→' to setOf(
		"to",
		"""\to""",
		"imp",
		"""\imp""",
		"implies",
		"imply",
		"->",
		"=>",
		"-->",
		"==>",
		"⇒",
		"rightarrow",
		"""\rightarrow"""
	),
	'↔' to setOf(
		"iff",
		"""\iff""",
		"<->",
		"<=>",
		"<-->",
		"<==>",
		"⇔",
		"≡",
		"if and only if",
		"leftrightarrow",
		"""\leftrightarrow""",
		"equiv",
		"equivalent"
	),
	'∀' to setOf("forall", """\forall""", "all", "for all", "!"),
	'∃' to setOf("exists", """\exists""", "ex", "there exists", "?"),
	'(' to setOf("{", "["),
	')' to setOf("}", "]")
).flatMap { (key, sets) -> sets.map { it to "$key" } }.sortedBy { it.first.length }.asReversed()
	.fold(this) { tmp, (str, letter) -> tmp.replace(str, letter, true) }

fun String.trimSpace(): String = replace("""\s""".toRegex(), "")

private fun String.getParenthesisEndPos(): Int? {
	var cnt = 0
	for ((pos, chr) in this.withIndex()) {
		when (chr) {
			'(' -> cnt++
			')' -> cnt--
		}
		if (cnt == 0) return pos
	}
	return null
}

private fun String.toTerms(): List<Term> {
	if (isEmpty()) return emptyList()
	val id = """[a-zA-Zα-ωΑ-Ω\d]+""".toRegex().matchAt(this, 0)?.value
		?: throw FormulaParserException("Illegal Argument: '${first()}'")
	val remained0 = drop(id.length)
	val (remained1, term) = if (remained0.firstOrNull() == '(') {
		val pos = remained0.getParenthesisEndPos() ?: throw FormulaParserException("Parenthesis Error.")
		val terms = remained0.substring(1..<pos).toTerms()
		remained0.substring(pos + 1) to Function(id, terms)
	} else {
		remained0 to Var(id)
	}
	return if (remained1.isEmpty()) listOf(term)
	else if (remained1.first() == ',') listOf(term) + remained1.drop(1).toTerms()
	else throw FormulaParserException("Illegal Argument: '${remained1.first()}'")
}

private tailrec fun String.tokenize(tokens: List<Token> = emptyList()): List<Token> = if (isEmpty()) tokens
else when (first()) {
	'(' -> drop(1).tokenize(tokens + Token.LP)
	')' -> drop(1).tokenize(tokens + Token.RP)
	'¬' -> drop(1).tokenize(tokens + Token.Operator.Unary.NOT)
	'∧' -> drop(1).tokenize(tokens + Token.Operator.Binary.AND)
	'∨' -> drop(1).tokenize(tokens + Token.Operator.Binary.OR)
	'→' -> drop(1).tokenize(tokens + Token.Operator.Binary.IMPLIES)
	'↔' -> drop(1).tokenize(tokens + Token.Operator.Binary.IFF)
	'⊤' -> drop(1).tokenize(tokens + Token.TRUE)
	'⊥' -> drop(1).tokenize(tokens + Token.FALSE)
	'∀' -> {
		val str = """[a-zA-Zα-ωΑ-Ω]\d*(,[a-zA-Zα-ωΑ-Ω]\d*)*""".toRegex().matchAt(this, 1)?.value
			?: throw FormulaParserException("The quantifier must be used in the form '∀x'")
		drop(str.length + 1).tokenize(tokens + str.split(',').map(::Var).map(Token.Operator.Unary::ALL))
	}

	'∃' -> {
		val str = """[a-zA-Zα-ωΑ-Ω]\d*(,[a-zA-Zα-ωΑ-Ω]\d*)*""".toRegex().matchAt(this, 1)?.value
			?: throw FormulaParserException("The quantifier must be used in the form '∃x'")
		drop(str.length + 1).tokenize(tokens + str.split(',').map(::Var).map(Token.Operator.Unary::EXISTS))
	}

	else -> {
		val id = """[a-zA-Zα-ωΑ-Ω\d]+""".toRegex().matchAt(this, 0)?.value
			?: throw FormulaParserException("Illegal Argument: '${first()}'")
		val remained = drop(id.length)
		if (remained.firstOrNull() == '(') {
			val pos = remained.getParenthesisEndPos() ?: throw FormulaParserException("Parenthesis Error.")
			val terms = remained.substring(1..<pos).toTerms()
			remained.substring(pos + 1).tokenize(tokens + Token.PREDICATE(id, terms))
		} else {
			remained.tokenize(tokens + Token.PREDICATE(id, emptyList()))
		}
	}
}

private fun List<Token>.toRPN(): List<Token> {
	val tokens = mutableListOf<Token>()
	val stack = mutableListOf<Token>()
	for (token in this) when (token) {
		Token.TRUE, Token.FALSE, is Token.PREDICATE -> tokens += token
		Token.LP -> stack += token
		Token.RP -> {
			while (stack.isNotEmpty() && stack.last() != Token.LP) {
				tokens += stack.removeLast()
			}
			if (stack.isEmpty()) throw FormulaParserException("Parenthesis Error.")
			stack.removeLast()
		}

		is Token.Operator -> {
			while (stack.lastOrNull() is Token.Operator && token.precedence < (stack.last() as Token.Operator).precedence) {
				tokens += stack.removeLast()
			}
			stack += token
		}
	}
	if (Token.LP in stack) throw FormulaParserException("Parenthesis Error.")
	tokens.addAll(stack.asReversed())
	return tokens
}

private fun List<Token>.makeFormula(): Formula {
	val stack = mutableListOf<Formula>()
	for (token in this) when (token) {
		Token.TRUE -> stack += TRUE
		Token.FALSE -> stack += FALSE
		is Token.PREDICATE -> stack += PREDICATE(token.id, token.terms)
		is Token.Operator.Unary -> {
			if (stack.isEmpty()) throw FormulaParserException("Parse Error.")
			val fml = stack.removeLast()
			when (token) {
				Token.Operator.Unary.NOT -> stack += NOT(fml)
				is Token.Operator.Unary.ALL -> {
					if (token.bddVar.id in fml.predicateIds) throw FormulaParserException("Cannot Quantify Predicate: ${token.bddVar}")
					if (token.bddVar.id in fml.functionIds) throw FormulaParserException("Cannot Quantify Function: ${token.bddVar}")
					try {
						stack += ALL(token.bddVar, fml)
					} catch (e: DuplicateBddVarException) {
						throw FormulaParserException("Duplicated Bounded Variables: ${token.bddVar}")
					}
				}

				is Token.Operator.Unary.EXISTS -> {
					if (token.bddVar.id in fml.predicateIds) throw FormulaParserException("Cannot Quantify Predicate: ${token.bddVar}")
					if (token.bddVar.id in fml.functionIds) throw FormulaParserException("Cannot Quantify Function: ${token.bddVar}")
					try {
						stack += EXISTS(token.bddVar, fml)
					} catch (e: DuplicateBddVarException) {
						throw FormulaParserException("Duplicated Bounded Variables: ${token.bddVar}")
					}
				}
			}
		}

		is Token.Operator.Binary -> {
			if (stack.size < 2) throw FormulaParserException("Parse Error.")
			val rightFml = stack.removeLast()
			val leftFml = stack.removeLast()
			stack += when (token) {
				Token.Operator.Binary.AND -> AND(leftFml, rightFml)
				Token.Operator.Binary.OR -> OR(leftFml, rightFml)
				Token.Operator.Binary.IMPLIES -> IMPLIES(leftFml, rightFml)
				Token.Operator.Binary.IFF -> IFF(leftFml, rightFml)
			}
		}

		Token.LP, Token.RP -> throw IllegalArgumentException()
	}
	return stack.singleOrNull() ?: throw FormulaParserException("Parse Error.")
}
