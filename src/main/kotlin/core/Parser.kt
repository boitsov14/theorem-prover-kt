package core

import core.Formula.*
import core.Term.*

class FormulaParserException(message: String): Exception(message)

fun String.parse(): Formula {
	println(this)
	val str = this.toOneLetter()
	println(str)
	val tokens = str.tokenize()
	println(tokens)
	val reversePolishNotation = tokens.toReversePolishNotation()
	println(reversePolishNotation)
	println(reversePolishNotation.getFormula())
	return reversePolishNotation.getFormula()
}

/*
fun String.parse(): Formula {
	println(this)
	val chrs = ArrayDeque(this.toOneLetter().toCharArray().toList())
	println(chrs)
	val preTokens = preTokenize(chrs)
	println(preTokens)
	val tokens = tokenize0(preTokens)
	println(tokens)
	val reversePolishNotation = toReversePolishNotation(tokens)
	println(reversePolishNotation)
	println(getFormula(reversePolishNotation))
	return getFormula(reversePolishNotation)
}
 */

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
	data class PREDICATE(val id: String, val terms: List<Term>): Token
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

@OptIn(ExperimentalStdlibApi::class)
private fun String.getIdEndPos(startPos: Int): Int {
	if (!(this[startPos].isLetter())) throw FormulaParserException("Illegal Argument >> ${this[startPos]}")
	val regex = "[a-zA-Z0-9_]+".toRegex()
	val str = regex.matchAt(this, startPos)!!.value
	return startPos + str.length - 1
}

private fun String.getParenthesisEndPos(startPos: Int): Int? {
	if (this[startPos] != '(') throw IllegalArgumentException()
	var counter = 0
	var pos = startPos
	while (pos < this.length) {
		when(this[pos]) {
			'(' -> counter++
			')' -> counter--
		}
		if (counter == 0) return pos
		pos++
	}
	return null
}

private fun String.toTerms(): List<Term> {
	if (this.isEmpty()) return emptyList()
	if (!(this.first().isLetter())) throw FormulaParserException("Illegal Argument >> ${this.first()}")
	val firstTerm: Term
	val firstTermEndPos: Int
	val idEndPos = this.getIdEndPos(0)
	val id = this.substring(0, idEndPos + 1)
	if (idEndPos + 1 < this.length && this[idEndPos + 1] == '(') {
		val parenthesisEndPos = this.getParenthesisEndPos(idEndPos + 1) ?: throw FormulaParserException("Parenthesis Error")
		val operandTermsStr = this.substring(idEndPos + 2, parenthesisEndPos)
		val operandTerms = operandTermsStr.toTerms()
		firstTerm = Function(id, operandTerms)
		firstTermEndPos = parenthesisEndPos
	} else {
		firstTerm = Var(id)
		firstTermEndPos = idEndPos
	}
	if (firstTermEndPos + 2 < this.length && this[firstTermEndPos + 1] == ',') {
		return listOf(firstTerm) + this.drop(firstTermEndPos + 2).toTerms()
	}
	if (firstTermEndPos == this.lastIndex) {
		return listOf(firstTerm)
	}
	throw FormulaParserException("Illegal Argument >> ${this[firstTermEndPos + 1]}")
}

private fun String.tokenize(): List<Token> {
	val tokens = mutableListOf<Token>()
	var index = 0
	while (index < this.length) {
		when(this[index]) {
			' ' -> {}
			'(' -> tokens.add(Token.LP)
			')' -> tokens.add(Token.RP)
			'¬' -> tokens.add(Token.Operator.Unary.NOT)
			'∧' -> tokens.add(Token.Operator.Binary.AND)
			'∨' -> tokens.add(Token.Operator.Binary.OR)
			'→' -> tokens.add(Token.Operator.Binary.IMPLIES)
			'↔' -> tokens.add(Token.Operator.Binary.IFF)
			'⊥' -> tokens.add(Token.FALSE)
			'⊤' -> tokens.add(Token.TRUE)
			'∀' -> {
				if (!(index < this.lastIndex && this[index + 1].isLetter())) {
					throw FormulaParserException("Quantifier must be used in the form '∀x'")
				}
				val endPos = this.getIdEndPos(index + 1)
				val bddVar = Var(this.substring(index + 1, endPos + 1))
				tokens.add(Token.Operator.Unary.ALL(bddVar))
				index = endPos
			}
			'∃' -> {
				if (!(index < this.lastIndex && this[index + 1].isLetter())) {
					throw FormulaParserException("Quantifier must be used in the form '∃x'")
				}
				val endPos = this.getIdEndPos(index + 1)
				val bddVar = Var(this.substring(index + 1, endPos + 1))
				tokens.add(Token.Operator.Unary.EXISTS(bddVar))
				index = endPos
			}
			in ('A'..'Z')+('a'..'z') -> {
				val idEndPos = this.getIdEndPos(index)
				val id = this.substring(index, idEndPos + 1)
				index = idEndPos
				// TODO: 2022/01/21 述語とtermsのかっこの間に空白がある場合の対処
				if (index + 1 < this.length && this[index + 1] == '(') {
					val parenthesisEndPos = this.getParenthesisEndPos(index + 1) ?: throw FormulaParserException("Parenthesis Error")
					val termsStr = this.substring(index + 2, parenthesisEndPos)
					val terms = termsStr.toTerms()
					tokens.add(Token.PREDICATE(id, terms))
					index = parenthesisEndPos
				} else {
					tokens.add(Token.PREDICATE(id, emptyList()))
				}
			}
			else -> throw FormulaParserException("Illegal Argument >> ${this[index]}")
		}
		index++
	}
	return tokens
}

private fun tokenize0(preTokens: ArrayDeque<PreToken>): List<Token> {
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

private fun List<Token>.toReversePolishNotation(): List<Token> {
	val outputTokens = ArrayDeque<Token>()
	val stack = mutableListOf<Token>()
	for (token in this) {
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

private fun List<Token>.getFormula(): Formula {
	val stack = mutableListOf<Formula>()
	for (token in this) {
		when(token) {
			Token.FALSE -> stack.add(FALSE)
			Token.TRUE 	-> stack.add(TRUE)
			is Token.PREDICATE -> stack.add(PREDICATE(token.id, token.terms))
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
