//import tacticGame.*
import core.FormulaParserException
import kotlinx.coroutines.*
import sequentProver.*
import java.io.File
import kotlin.system.measureTimeMillis

suspend fun main(args: Array<String>) {
	mainForJar(args)
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
	} catch (e: Throwable) {
		print("An unexpected error has occurred: $e")
		return
	}
	// Prover
	val rootNode = Node(sequent)
	val proofState = try {
		withTimeout(300_000) {
			rootNode.prove()
		}
	} catch (e: TimeoutCancellationException) {
		print("Proof Failed: Timeout.")
		return
	} catch (e: OutOfMemoryError) {
		print("Proof Failed: OutOfMemoryError.")
		return
	} catch (e: Throwable) {
		print("An unexpected error has occurred: $e")
		return
	}
	// TeX
	val latexOutput = try {
		rootNode.getLatexOutput(proofState)
	} catch (e: OutOfMemoryError) {
		print("The proof tree is too large to output: OutOfMemoryError.")
		return
	} catch (e: Throwable) {
		print("An unexpected error has occurred: $e")
		return
	}
	File("${id}.tex").writeText(latexOutput)
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
