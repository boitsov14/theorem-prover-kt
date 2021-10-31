import PreToken.Binary.*

class FormulaParserException(message:String): Exception(message)

/*
// SemiToken = Token | Var | Quantifier | PredicateSemiToken
interface  SemiToken

// Token = Formula.False | Formula.PredicateFml | OperatorToken | SymbolToken
interface Token: SemiToken

// OperatorToken = UnaryConnective | BinaryConnective | QuantifierWithVarOperatorToken
interface OperatorToken: Token {
	val precedence: Int
}



data class PredicateSemiToken(val id: Char): SemiToken

data class QuantifierWithVarOperatorToken(val quantifier: Quantifier, val bddVar: Var): OperatorToken {
	override val precedence = -1
}

fun String.parse(): Formula? {
	val semiTokens = this.toUnicode().toCharArray().map { parseCharacter(it) }.filterNot { it == Symbol.WHITESPACE }
	val tokens = toReversePolishNotation(ArrayDeque(semiTokens))
	return toFormula(tokens)
}

fun toReversePolishNotation(tokens: ArrayDeque<SemiToken>): List<Token> {
	val output: MutableList<Token> = mutableListOf()
	val stack = ArrayDeque<Token>()
	while (tokens.isNotEmpty()) {
		when (tokens[0]) {
			is Formula.FALSE			-> output.add		(tokens.removeFirst() as Token)
			is Formula.PREDICATE					-> output.add 		(tokens.removeFirst() as Token)
			Symbol.LEFT_PARENTHESIS	-> stack.addFirst	(tokens.removeFirst() as Token)
			Symbol.RIGHT_PARENTHESIS -> {
				while (stack.isNotEmpty()) {
					if (stack.first() != Symbol.LEFT_PARENTHESIS) {
						output.add(stack.removeFirst())
					} else {
						stack.removeFirst()
						tokens.removeFirst()
						break
					}
				}
				// TODO: 2021/09/20
				// need error with parenthesis?
			}
			is Quantifier -> {
				if (tokens.size >= 3 && tokens[1] is Var && tokens[2] == Symbol.COMMA) {
					val quantifierWithVarOperatorToken = QuantifierWithVarOperatorToken(tokens.removeFirst() as Quantifier, tokens.removeFirst() as Var)
					tokens.removeFirst() // COMMA
					tokens.addFirst(quantifierWithVarOperatorToken)
				} else {
					println("量化子の後には変数とコンマが必要です")
					break
					// TODO: 2021/09/20
					// need test
				}
			}
			is PredicateSemiToken -> {
				val predicateSemiToken = tokens.removeFirst() as PredicateSemiToken
				val vars = mutableListOf<Var>()
				while (tokens.isNotEmpty() && tokens[0] is Var) {
					vars.add(tokens.removeFirst() as Var)
				}
				tokens.addFirst(Formula.PREDICATE(predicateSemiToken.id, vars))
			}
			is BinaryConnective -> {
				while (stack.isNotEmpty()
					&& stack[0] is OperatorToken
					&& (tokens[0] as OperatorToken).precedence < (stack[0] as OperatorToken).precedence) {
					output.add(stack.removeFirst())
				}
				stack.addFirst(tokens.removeFirst() as Token)
			}
			is UnaryConnective		-> stack.addFirst(tokens.removeFirst() as Token)
			is QuantifierWithVarOperatorToken	-> stack.addFirst(tokens.removeFirst() as Token)
			else -> {
				// TODO: 2021/09/20
				// そのうち消す
				println("わいのミス")
				println(tokens[0])
				tokens.removeFirst()
			}
		}
	}
	output.addAll(stack)
	return output
}

fun toFormula(tokens: List<Token>): Formula? {
	val output = mutableListOf<Formula>()
	for (token in tokens) {
		when(token) {
			is Formula.FALSE -> output.add(token)
			is Formula.PREDICATE -> output.add(token)
			is UnaryConnective -> {
				if (output.isEmpty()) {
					println("syntax error in UnaryConnective")
					break
					// TODO: 2021/09/20
					// need test
				}
				val newFml = Formula.UnaryConnectiveFml(token, output.removeLast())
				output.add(newFml)
			}
			is QuantifierWithVarOperatorToken -> {
				if (output.isEmpty()) {
					println("syntax error with QuantifierWithVar")
					break
					// TODO: 2021/09/20
					// need test
				}
				// TODO: 2021/10/01 ここで束縛変数に被りがないかどうかチェック
				// if (bddVar in formula.bddVars()) { println("束縛変数がかぶっています．") }
				val newFml = Formula.QuantifiedFml(token.quantifier, token.bddVar, output.removeLast())
				output.add(newFml)
			}
			is BinaryConnective -> {
				if (output.size < 2){
					println("syntax error with BinaryConnective")
					break
					// TODO: 2021/09/20
					// need test
				}
				val rightFml	= output.removeLast()
				val leftFml		= output.removeLast()
				val newFml = Formula.BinaryConnectiveFml(token, leftFml, rightFml)
				output.add(newFml)
			}
			else -> {
				println("syntax error with parenthesis")
				break
				// TODO: 2021/09/20
				// need test
			}
		}
	}
	return if (output.size == 1) {
		output[0]
	} else {
		println("syntax error ???")
		null
		// TODO: 2021/09/20
		// need test
	}
}

fun parseCharacter(chr: Char): SemiToken = when {
	chr in Symbol			.values().map{it.chr} -> Symbol			.values().find{it.chr == chr}!!
	chr in UnaryConnective		.values().map{it.id} -> UnaryConnective		.values().find{it.id == chr}!!
	chr in BinaryConnective		.values().map{it.id} -> BinaryConnective	.values().find{it.id == chr}!!
	chr == Formula.FALSE.id							 -> Formula.FALSE
	chr in Quantifier			.values().map{it.id} -> Quantifier			.values().find{it.id == chr}!!
	chr.isLowerCase()								 -> Var("$chr")
	chr.isUpperCase() 								 -> PredicateSemiToken(chr)
	else 											 -> Symbol.WHITESPACE
}
*/

fun preTokenize(str: String): List<PreToken> {
	val chrs = str.toCharArray()
	val preTokens = mutableListOf<PreToken>()
	var index = 0
	while (index < chrs.size) {
		val currentChr = chrs[index]
		if (currentChr in Symbol.values().map { it.chr }) {
			preTokens.add(Symbol.values().find { it.chr == currentChr }!!)
		} else if (currentChr.isUpperCase()) {
			val predicateId = mutableListOf<Char>()
			while (chrs[index].isLetter()) {
				predicateId.add(chrs[index])
				index++
				if (index == chrs.size) break
			}
			index--
			preTokens.add(PredicateId(String(predicateId.toCharArray())))
		} else if (currentChr.isLowerCase()) {
			val varId = mutableListOf<Char>()
			while (chrs[index].isLowerCase()) {
				varId.add(chrs[index])
				index++
				if (index == chrs.size) break
			}
			index--
			preTokens.add(VarId(String(varId.toCharArray())))
		} else {
			throw FormulaParserException("$currentChr is an illegal character.")
		}
		index++
	}
	return preTokens
}

fun tokenize(preTokens: List<PreToken>): List<Token> {
	val tokens = mutableListOf<Token>()
	var index = 0
	while (index < preTokens.size) {
		when(val currentPreToken = preTokens[index]) {
			PreToken.Symbol.LEFT_PARENTHESIS 	-> tokens.add(Token.LeftParenthesis)
			PreToken.Symbol.RIGHT_PARENTHESIS 	-> tokens.add(Token.RightParenthesis)
			PreToken.Symbol.WHITESPACE 			-> {}
			PreToken.Unary.NOT 					-> tokens.add(Token.Operator.Unary.NOT)
			is PreToken.Binary 					-> tokens.add(Token.Operator.Binary(currentPreToken))
			is PreToken.PredicateId -> {
				val varIds = mutableListOf<PreToken.VarId>()
				while (preTokens.elementAtOrNull(index++) is PreToken.VarId) {


					varIds.add(chrs[index])
					index++
					if (index == chrs.size) break
				}
				index--
				preTokens.add(VarId(String(varIds.toCharArray())))
			}

		}
		index++
	}
	return tokens
}

sealed interface PreToken {
	enum class Symbol(val chr: Char): PreToken {
		LEFT_PARENTHESIS('('),
		RIGHT_PARENTHESIS(')'),
		COMMA(','),
		WHITESPACE(' ')
	}
	enum class Unary(val chr: Char): PreToken {
		NOT('¬')
	}
	enum class Binary(val chr: Char): PreToken {
		AND('∧'),
		OR('∨'),
		IMPLIES('→'),
		IFF('↔')
	}
	enum class Quantifier(val chr: Char): PreToken {
		ALL('∀'),
		EXISTS('∃')
	}
	data class PredicateId(val id: String): PreToken
	data class VarId(val id: String): PreToken
}

sealed interface Token {
	object LeftParenthesis: Token
	object RightParenthesis: Token
	data class PREDICATE(val id: String, val vars: List<PreToken.VarId>): Token
	sealed interface Operator: Token {
		val precedence: Int
		data class Binary(val binary: PreToken.Binary): Operator {
			override val precedence = when(binary) {
				AND 	-> 4
				OR 		-> 3
				IMPLIES -> 2
				IFF 	-> 1
			}
		}
		sealed interface Unary: Operator {
			object NOT: Unary {
				override val precedence = 5
			}
			data class ALL(val bddVar: PreToken.VarId): Unary {
				override val precedence = 0
			}
			data class EXISTS(val bddVar: PreToken.VarId): Unary {
				override val precedence = 0
			}
		}
	}
}



// OperatorToken = UnaryConnective | BinaryConnective | QuantifierWithVarOperatorToken
interface OperatorToken: Token {
	val precedence: Int
}
data class PredicateSemiToken(val id: Char): SemiToken
data class QuantifierWithVarOperatorToken(val quantifier: Quantifier, val bddVar: Var): OperatorToken {
	override val precedence = -1
}





fun String.toUnicode(): String = this
	.replace("false", "⊥")
	.replace("not", "¬")
	.replace("to", "→")
	.replace("and", "∧")
	.replace("or", "∨")
	.replace("iff", "↔")
	.replace("all", "∀")
	.replace("ex", "∃")
