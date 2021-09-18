interface Token {}

enum class SymbolToken(val id: Char): Token {
	LEFT_PARENTHESIS('('),
	RIGHT_PARENTHESIS(')'),
	COMMA(','),
	WHITESPACE(' '),
}

enum class ConnectiveToken(val id: Char, val precedence: Int): Token {
	NOT('¬',4),
	IMPLY('→', 1),
	AND('∧', 3),
	OR('∨', 2),
	IFF('↔', 0)
}

enum class PreDefinedAtomToken(val id: Char): Token {
	FALSE('⊥')
}

data class VarToken(val id: Char): Token {}

data class PredicateToken(val id: Char, var arity: Int? = null): Token {}

enum class QuantifierToken(val id: Char): Token {
	FOR_ALL('∀'),
	THERE_EXISTS('∃')
}

data class PredicateFmlToken(val predicate: PredicateToken, val vars: List<VarToken>): Token {
	constructor(predicate: PredicateToken) : this(predicate, listOf())
}

// TODO: 2021/09/19
/*
fun getPredicates(tokens: List<Token>): List<PredicateToken> {

}

fun parse(str: String): Formula {
	val tokens = str.toCharArray().map { parseCharacter(it) }
}
*/

fun parseCharacter(chr: Char): Token = when {
	chr in SymbolToken			.values().map{it.id} -> SymbolToken			.values().find{it.id == chr}!!
	chr in ConnectiveToken		.values().map{it.id} -> ConnectiveToken		.values().find{it.id == chr}!!
	chr in PreDefinedAtomToken	.values().map{it.id} -> PreDefinedAtomToken	.values().find{it.id == chr}!!
	chr in QuantifierToken		.values().map{it.id} -> QuantifierToken		.values().find{it.id == chr}!!
	chr.isLowerCase()								 -> VarToken(chr)
	chr.isUpperCase() 								 -> PredicateToken(chr)
	else 											 -> SymbolToken.WHITESPACE
}
