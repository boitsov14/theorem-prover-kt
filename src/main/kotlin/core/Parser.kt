package core

import core.Formula.*
import core.Term.*

class FormulaParserException(message: String): Exception(message)

fun String.parse(): Formula {
	println(this)
	val chrs = ArrayDeque(this.toOneLetter().toCharArray().toList())
	println(chrs)
	val preTokens = preTokenize(chrs)
	println(preTokens)
	val tokens = tokenize(preTokens)
	println(tokens)
	val reversePolishNotation = toReversePolishNotation(tokens)
	println(reversePolishNotation)
	println(getFormula(reversePolishNotation))
	return getFormula(reversePolishNotation)
}

private sealed interface PreToken {
	enum class Symbol(val chr: Char): PreToken {
		LP('('),
		RP(')'),
		NOT('¬'),
		AND('∧'),
		OR('∨'),
		IMPLIES('→'),
		IFF('↔'),
		ALL('∀'),
		EXISTS('∃'),
		FALSE('⊥'),
		TRUE('⊤')
	}
	data class PREDICATE(val id: String): PreToken
	data class VAR(val id: String): PreToken
}

private sealed interface Token {
	object LP: Token
	object RP: Token
	sealed interface Operator: Token {
		val precedence: Int
		enum class Binary(override val precedence: Int): Operator {
			AND(3),
			OR(2),
			IMPLIES(1),
			IFF(0)
		}
		sealed interface Unary: Operator {
			object NOT: Unary {	override val precedence = 4 }
			data class ALL(val bddVar: Var): Unary { override val precedence = 4 }
			data class EXISTS(val bddVar: Var): Unary { override val precedence = 4 }
		}
	}
	data class PREDICATE(val id: String, val vars: List<Var>): Token
	object FALSE: Token
	object TRUE: Token
}

private fun String.toOneLetter(): String {
	var result = this
	oneLetterMap.forEach { (key, values) -> values.forEach { value -> result = result.replace(value, key, true) } }
	return result
}

private val oneLetterMap = mapOf(
	"T" to setOf("true", "tautology", "top"),
	"⊥" to setOf("false", "contradiction", "bottom"),
	"¬" to setOf("not ", "~", "negation ", "\\neg ", "neg "),
	"∧" to setOf(" \\land ", " and ", "/\\", "&&", "&"),
	"∨" to setOf(" \\or ", " or ", "\\/", "||", "|"),
	"↔" to setOf(" \\iff ", " iff ", "<-->", "<==>", "<->", "<=>", "if and only if"),
	"→" to setOf(" \\to ", " implies ", "-->", "==>", "->", "=>", " to ", " imply "),
	"∀" to setOf("\\forall ", "forall ", "all "),
	"∃" to setOf("\\exists ", "exists ", "ex "),
	"(" to setOf("（"),
	")" to setOf("）"),
	"⊢" to setOf("\\vdash", "vdash", "proves")
)

private fun preTokenize(inputChrs: ArrayDeque<Char>): ArrayDeque<PreToken> {
	val preTokens = ArrayDeque<PreToken>()
	while (inputChrs.isNotEmpty()) {
		when (val currentChr = inputChrs.removeFirst()) {
			in PreToken.Symbol.values().map { it.chr } -> preTokens.add(PreToken.Symbol.values().find { it.chr == currentChr }!!)
			' ' -> {}
			in ('A'..'Z')+('a'..'z') -> {
				val chrs = mutableListOf(currentChr)
				while (inputChrs.isNotEmpty() && (inputChrs.first().isLetterOrDigit() || inputChrs.first() == '_')) {
					chrs.add(inputChrs.removeFirst())
				}
				val str = String(chrs.toCharArray())
				preTokens.add(
					when(currentChr) {
						in ('A'..'Z') -> PreToken.PREDICATE(str)
						in ('a'..'z') -> PreToken.VAR(str)
						else -> throw IllegalArgumentException()
					}
				)
			}
			else -> throw FormulaParserException("Illegal Argument >> $currentChr")
		}
	}
	return preTokens
}

private fun tokenize(preTokens: ArrayDeque<PreToken>): List<Token> {
	val tokens = mutableListOf<Token>()
	while (preTokens.isNotEmpty()) {
		when (val preToken = preTokens.removeFirst()) {
			PreToken.Symbol.LP 	-> tokens.add(Token.LP)
			PreToken.Symbol.RP 	-> tokens.add(Token.RP)
			PreToken.Symbol.NOT 				-> tokens.add(Token.Operator.Unary.NOT)
			PreToken.Symbol.AND 				-> tokens.add(Token.Operator.Binary.AND)
			PreToken.Symbol.OR 					-> tokens.add(Token.Operator.Binary.OR)
			PreToken.Symbol.IMPLIES 			-> tokens.add(Token.Operator.Binary.IMPLIES)
			PreToken.Symbol.IFF 				-> tokens.add(Token.Operator.Binary.IFF)
			PreToken.Symbol.FALSE 				-> tokens.add(Token.FALSE)
			PreToken.Symbol.TRUE 				-> tokens.add(Token.TRUE)
			is PreToken.PREDICATE -> {
				val vars = mutableListOf<Var>()
				while (preTokens.isNotEmpty() && preTokens.first() is PreToken.VAR) {
					val preTokenVar = preTokens.removeFirst() as PreToken.VAR
					vars.add(Var(preTokenVar.id))
				}
				val predicate = Token.PREDICATE(preToken.id, vars)
				tokens.add(predicate)
			}
			PreToken.Symbol.ALL, PreToken.Symbol.EXISTS -> {
				if (!(preTokens.size >= 1 && preTokens[0] is PreToken.VAR)) {
					throw FormulaParserException("Parse Error with quantifier")
				}
				val preTokenVar = preTokens.removeFirst() as PreToken.VAR
				val bddVar = Var(preTokenVar.id)
				tokens.add(
					when(preToken) {
						PreToken.Symbol.ALL 	-> Token.Operator.Unary.ALL(bddVar)
						PreToken.Symbol.EXISTS 	-> Token.Operator.Unary.EXISTS(bddVar)
						else -> throw IllegalArgumentException()
					}
				)
			}
			else -> throw FormulaParserException("Parse Error")
		}
	}
	return tokens
}

private fun toReversePolishNotation(inputTokens: List<Token>): List<Token> {
	val outputTokens = ArrayDeque<Token>()
	val stack = mutableListOf<Token>()
	for (token in inputTokens) {
		when(token) {
			Token.FALSE -> outputTokens.add(token)
			Token.TRUE 	-> outputTokens.add(token)
			is Token.PREDICATE -> outputTokens.add(token)
			Token.LP -> stack.add(token)
			Token.RP -> {
				while (stack.isNotEmpty() && stack.last() != Token.LP) {
					outputTokens.add(stack.removeLast())
				}
				if (stack.isEmpty()) {
					throw FormulaParserException("Parenthesis Error")
				}
				stack.removeLast()
			}
			is Token.Operator.Unary -> stack.add(token)
			is Token.Operator.Binary -> {
				while (stack.isNotEmpty()
					&& stack.last() is Token.Operator
					&& token.precedence < (stack.last() as Token.Operator).precedence) {
					outputTokens.add(stack.removeLast())
				}
				stack.add(token)
			}
		}
	}
	if (Token.LP in stack) {
		throw FormulaParserException("Parenthesis Error")
	}
	outputTokens.addAll(stack.reversed())
	return outputTokens
}

private fun getFormula(tokens: List<Token>): Formula {
	val stack = mutableListOf<Formula>()
	for (token in tokens) {
		when(token) {
			Token.FALSE -> stack.add(FALSE)
			Token.TRUE 	-> stack.add(TRUE)
			is Token.PREDICATE -> stack.add(PREDICATE(token.id, token.vars))
			is Token.Operator.Unary -> {
				if (stack.isEmpty()) {
					throw FormulaParserException("Parse Error")
				}
				val fml = stack.removeLast()
				when(token) {
					Token.Operator.Unary.NOT -> stack.add(NOT(fml))
					is Token.Operator.Unary.ALL -> {
						try {
							stack.add(ALL(token.bddVar, fml))
						} catch (e: DuplicateBddVarException) {
							throw FormulaParserException("bounded variable is duplicated.")
						}
					}
					is Token.Operator.Unary.EXISTS -> {
						try {
							stack.add(EXISTS(token.bddVar, fml))
						} catch (e: DuplicateBddVarException) {
							throw FormulaParserException("bounded variable is duplicated.")
						}
					}
				}
			}
			is Token.Operator.Binary -> {
				if (stack.size < 2) {
					throw FormulaParserException("Parse Error")
				}
				val rightFml = stack.removeLast()
				val leftFml = stack.removeLast()
				stack.add(
					when(token) {
						Token.Operator.Binary.AND 		-> AND(leftFml, rightFml)
						Token.Operator.Binary.OR 		-> OR(leftFml, rightFml)
						Token.Operator.Binary.IMPLIES 	-> IMPLIES(leftFml, rightFml)
						Token.Operator.Binary.IFF 		-> IFF(leftFml, rightFml)
					}
				)
			}
			else -> throw IllegalArgumentException()
		}
	}
	if (stack.size != 1) {
		throw FormulaParserException("Parse Error")
	}
	return stack.last()
}
