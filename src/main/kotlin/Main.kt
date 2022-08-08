//import tacticGame.*
import core.FormulaParserException
import sequentProver.*
import java.io.File
import kotlin.system.measureTimeMillis

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

suspend fun mainForConsole() {
	print("INPUT A FORMULA >>> ")
	val sequent = readln().parseToSequent()
	val rootNode = Node(sequent)
	val proofState = rootNode.prove(
		printSequents = false, printTacticInfo = false, printTimeInfo = true, printUnificationInfo = true
	)
	//val output = File("src/main/resources/Output.tex")
	//output.writeText(rootNode.getLatexOutput(proofState))
	/*
	val time = measureTimeMillis {
		try {
			val output = File("src/main/resources/Output.tex")
			output.writeText(rootNode.getLatexOutput(proofState))
		} catch (e: OutOfMemoryError) {
			println(e)
		}
	}
	println("Latex produced in $time ms")
	*/
}

fun mainForTest() {
	TODO()
}
