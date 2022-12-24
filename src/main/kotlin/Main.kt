import core.FormulaParserException
import sequentProver.*
import sequentProver.ProofState.*
import java.io.File

suspend fun main(args: Array<String>) {
	if (args.isNotEmpty()) {
		prover(args[0], args[1])
	} else {
		prover()
	}
}

suspend fun prover(id: String, sequentString: String) {
	// Parse
	val sequent = try {
		sequentString.parseToSequent()
	} catch (e: FormulaParserException) {
		print(e.message)
		return
	}
	// Prove
	val start = System.currentTimeMillis()
	val (proofState, node) = sequent.prove()
	val end = System.currentTimeMillis()
	print(proofState)
	if (proofState == Provable || proofState == Unprovable) {
		print(" Completed in ${(end - start) / 1000.0} seconds.")
	}
	// TeX
	File("${id}.tex").writeText(node.getLatex(proofState))
}

suspend fun prover() {
	print("INPUT A FORMULA >>> ")
	val sequent = readln().parseToSequent()
	val start = System.currentTimeMillis()
	val (proofState, node) = sequent.prove()
	val end = System.currentTimeMillis()
	println(proofState)
	println("Completed in ${end - start} ms")
	File("src/main/resources/Output.tex").writeText(node.getLatex(proofState))
}
