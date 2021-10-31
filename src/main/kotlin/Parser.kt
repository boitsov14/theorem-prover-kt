class FormulaParserException(message:String): Exception(message)

// SemiToken = Token | Var | Quantifier | PredicateSemiToken
interface  SemiToken

// Token = Formula.False | Formula.PredicateFml | OperatorToken | SymbolToken
interface Token: SemiToken

// OperatorToken = UnaryConnective | BinaryConnective | QuantifierWithVarOperatorToken
interface OperatorToken: Token {
	val precedence: Int
}

enum class SymbolToken(val id: Char): Token {
	LEFT_PARENTHESIS('('),
	RIGHT_PARENTHESIS(')'),
	COMMA(','),
	WHITESPACE(' '),
}

data class PredicateSemiToken(val id: Char): SemiToken

data class QuantifierWithVarOperatorToken(val quantifier: Quantifier, val bddVar: Var): OperatorToken {
	override val precedence = -1
}

fun String.parse(): Formula? {
	val semiTokens = this.toUnicode().toCharArray().map { parseCharacter(it) }.filterNot { it == SymbolToken.WHITESPACE }
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
			SymbolToken.LEFT_PARENTHESIS	-> stack.addFirst	(tokens.removeFirst() as Token)
			SymbolToken.RIGHT_PARENTHESIS -> {
				while (stack.isNotEmpty()) {
					if (stack.first() != SymbolToken.LEFT_PARENTHESIS) {
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
				if (tokens.size >= 3 && tokens[1] is Var && tokens[2] == SymbolToken.COMMA) {
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
	chr in SymbolToken			.values().map{it.id} -> SymbolToken			.values().find{it.id == chr}!!
	chr in UnaryConnective		.values().map{it.id} -> UnaryConnective		.values().find{it.id == chr}!!
	chr in BinaryConnective		.values().map{it.id} -> BinaryConnective	.values().find{it.id == chr}!!
	chr == Formula.FALSE.id							 -> Formula.FALSE
	chr in Quantifier			.values().map{it.id} -> Quantifier			.values().find{it.id == chr}!!
	chr.isLowerCase()								 -> Var("$chr")
	chr.isUpperCase() 								 -> PredicateSemiToken(chr)
	else 											 -> SymbolToken.WHITESPACE
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
