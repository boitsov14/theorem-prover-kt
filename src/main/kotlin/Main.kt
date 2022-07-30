//import tacticGame.*
import core.FormulaParserException
import kotlinx.coroutines.*
import sequentProver.*
import java.io.File

suspend fun main(args: Array<String>) {
	mainForJar(args)
	//temp()
	//mainForConsole()
}

suspend fun mainForJar(args: Array<String>) {
	val id = args[0]
	val sequentStr = args[1]
	val messageFile = File("${id}_message.txt")
	// Parser
	val sequent = try {
		sequentStr.parseToSequent()
	} catch (e: FormulaParserException) {
		messageFile.writeText(e.message!!)
		return
	} catch (e: Throwable) {
		messageFile.writeText("An unexpected error has occurred: $e")
		return
	}
	// Prover
	val rootNode = Node(sequent, null)
	val proofState = try {
		withTimeout(300_000) {
			rootNode.prove()
		}
	} catch (e: TimeoutCancellationException) {
		messageFile.writeText("Proof Failed: Timeout.")
		return
	} catch (e: OutOfMemoryError) {
		messageFile.writeText("Proof Failed: OutOfMemoryError.")
		return
	} catch (e: Throwable) {
		messageFile.writeText("An unexpected error has occurred: $e")
		return
	}
	messageFile.writeText(proofState.toString())
	// TeX
	val latexOutput = try {
		rootNode.getLatexOutput(proofState)
	} catch (e: OutOfMemoryError) {
		messageFile.appendText("The proof tree is too large to output: OutOfMemoryError.")
		return
	} catch (e: Throwable) {
		messageFile.appendText("An unexpected error has occurred: $e")
		return
	}
	val latexFile = File("${id}.tex")
	latexFile.writeText(latexOutput)
}

suspend fun mainForConsole() {
	print("INPUT A FORMULA >>> ")
	val sequent = readln().parseToSequent()
	val rootNode = Node(sequent, null)
	val proofState = rootNode.prove(
		printSequents = false, printTacticInfo = false, printTimeInfo = true, printUnificationInfo = true
	)
	println(proofState)
	//val output = File("src/main/resources/Output.tex")
	//output.writeText(rootNode.getLatexOutput(proofState))
}

fun mainForTest() {
	TODO()
}
