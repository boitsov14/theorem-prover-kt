package core.parser

import core.formula.*

class FormulaParserException(message:String): Exception(message)

fun parse(str: String): Formula {
	val chrs = ArrayDeque(str.toUnicode().toCharArray().toList())
	val preTokens = preTokenize(chrs)
	val tokens = tokenize(preTokens)
	val reversePolishNotation = toReversePolishNotation(tokens)
	return getFormula(reversePolishNotation)
}

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

private fun tokenize(preTokens: ArrayDeque<PreToken>): ArrayDeque<Token> {
	val tokens = ArrayDeque<Token>()
	while (preTokens.isNotEmpty()) {
		when (val preToken = preTokens.removeFirst()) {
			PreToken.Symbol.LEFT_PARENTHESIS 	-> tokens.add(Token.LEFT_PARENTHESIS)
			PreToken.Symbol.RIGHT_PARENTHESIS 	-> tokens.add(Token.RIGHT_PARENTHESIS)
			PreToken.Symbol.NOT 				-> tokens.add(Token.Operator.Unary.NOT)
			PreToken.Symbol.AND 				-> tokens.add(Token.Operator.Binary.AND)
			PreToken.Symbol.OR 					-> tokens.add(Token.Operator.Binary.OR)
			PreToken.Symbol.IMPLIES 			-> tokens.add(Token.Operator.Binary.IMPLIES)
			PreToken.Symbol.IFF 				-> tokens.add(Token.Operator.Binary.IFF)
			PreToken.Symbol.FALSE 				-> tokens.add(Token.FALSE)
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
				if (!(preTokens.size >= 2 && preTokens[0] is PreToken.VAR && preTokens[1] == PreToken.Symbol.COMMA)) {
					throw FormulaParserException("Parse Error with quantifier")
				}
				val preTokenVar = preTokens.removeFirst() as PreToken.VAR
				val bddVar = Var(preTokenVar.id)
				preTokens.removeFirst()
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

private fun toReversePolishNotation(inputTokens: ArrayDeque<Token>): ArrayDeque<Token> {
	val outputTokens = ArrayDeque<Token>()
	val stack = ArrayDeque<Token>()
	for (token in inputTokens) {
		when(token) {
			Token.FALSE -> outputTokens.add(token)
			is Token.PREDICATE -> outputTokens.add(token)
			Token.LEFT_PARENTHESIS -> stack.addFirst(token)
			Token.RIGHT_PARENTHESIS -> {
				while (stack.isNotEmpty() && stack.first() != Token.LEFT_PARENTHESIS) {
					outputTokens.add(stack.removeFirst())
				}
				if (stack.isEmpty()) {
					throw FormulaParserException("Parenthesis Error")
				}
				stack.removeFirst()
			}
			is Token.Operator.Unary -> stack.addFirst(token)
			is Token.Operator.Binary -> {
				while (stack.isNotEmpty()
					&& stack.first() is Token.Operator
					&& token.precedence < (stack.first() as Token.Operator).precedence) {
					outputTokens.add(stack.removeFirst())
				}
				stack.addFirst(token)
			}
		}
	}
	if (Token.LEFT_PARENTHESIS in stack) {
		throw FormulaParserException("Parenthesis Error")
	}
	outputTokens.addAll(stack)
	return outputTokens
}

private fun getFormula(tokens: ArrayDeque<Token>): Formula {
	val stack = ArrayDeque<Formula>()
	for (token in tokens) {
		when(token) {
			Token.FALSE -> stack.addFirst(Formula.FALSE)
			is Token.PREDICATE -> stack.addFirst(Formula.PREDICATE(token.id, token.vars))
			is Token.Operator.Unary -> {
				if (stack.isEmpty()) {
					throw FormulaParserException("Parse Error")
				}
				val fml = stack.removeFirst()
				when(token) {
					Token.Operator.Unary.NOT -> stack.addFirst(Formula.NOT(fml))
					is Token.Operator.Unary.ALL -> {
						try {
							stack.addFirst(Formula.ALL(token.bddVar, fml))
						} catch (e: DuplicateBddVarException) {
							throw FormulaParserException("bounded variable is duplicated.")
						}
					}
					is Token.Operator.Unary.EXISTS -> {
						try {
							stack.addFirst(Formula.EXISTS(token.bddVar, fml))
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
				val rightFml = stack.removeFirst()
				val leftFml = stack.removeFirst()
				stack.addFirst(
					when(token) {
						Token.Operator.Binary.AND -> 		Formula.AND(leftFml, rightFml)
						Token.Operator.Binary.OR -> 		Formula.OR(leftFml, rightFml)
						Token.Operator.Binary.IMPLIES -> 	Formula.IMPLIES(leftFml, rightFml)
						Token.Operator.Binary.IFF -> 		Formula.IFF(leftFml, rightFml)
					}
				)
			}
			else -> throw IllegalArgumentException()
		}
	}
	if (stack.size != 1) {
		throw FormulaParserException("Parse Error")
	}
	return stack.first()
}

sealed interface PreToken {
	enum class Symbol(val chr: Char): PreToken {
		LEFT_PARENTHESIS('('),
		RIGHT_PARENTHESIS(')'),
		COMMA(','),
		NOT('¬'),
		AND('∧'),
		OR('∨'),
		IMPLIES('→'),
		IFF('↔'),
		ALL('∀'),
		EXISTS('∃'),
		FALSE('⊥')
	}
	data class PREDICATE(val id: String): PreToken
	data class VAR(val id: String): PreToken
}

sealed interface Token {
	object LEFT_PARENTHESIS: Token
	object RIGHT_PARENTHESIS: Token
	sealed interface Operator: Token {
		val precedence: Int
		enum class Binary(override val precedence: Int): Operator {
			AND(4),
			OR(3),
			IMPLIES(2),
			IFF(1)
		}
		sealed interface Unary: Operator {
			object NOT: Unary {	override val precedence = 5 }
			data class ALL(val bddVar: Var): Unary { override val precedence = 0 }
			data class EXISTS(val bddVar: Var): Unary { override val precedence = 0 }
		}
	}
	data class PREDICATE(val id: String, val vars: List<Var>): Token
	object FALSE: Token
}

private fun String.replace(
	oldValues: List<String>,
	newValue: String
): String {
	var result = this
	oldValues.forEach { result = result.replace(it, newValue, true) }
	return result
}

private fun String.toUnicode(): String = this
	.replace(listOf("false ", "contradiction "), "⊥ ")
	.replace(listOf("not ", "~", "negation "), "¬")
	.replace(listOf(" and ",""" /\ """), " ∧ ")
	.replace(listOf(" or ", """ \/ """), " ∨ ")
	.replace(listOf(" implies ", " -> ", " => ", " --> ", " ==> ", " to ", " imply "), " → ")
	.replace(listOf(" iff ", " <-> ", " <=> ", " <--> ", " <==> ", " if and only if "), " ↔ ")
	.replace(listOf("forall ", "all "), "∀")
	.replace(listOf("exists ", "ex "), "∃")
