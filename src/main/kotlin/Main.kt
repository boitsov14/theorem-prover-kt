import core.FormulaParserException
import sequentProver.*
import java.io.File

suspend fun main(args: Array<String>) {
	try {
		mainForJar(args)
	} catch (e: Exception) {
		print("An unexpected error has occurred: $e")
	}
	//temp()
	//mainForConsole()
}

suspend fun mainForJar(args: Array<String>) {
	val id = args[0]
	val sequentStr = args[1]
	// Parser
	val sequent = try {
		sequentStr.parseToSequent()
	} catch (e: FormulaParserException) {
		print(e.message)
		return
	}
	// Prover
	val rootNode = Node(sequent)
	val proofState = rootNode.prove()
	// TeX
	File("${id}.tex").writeText(rootNode.getLatexOutput(proofState))
}
