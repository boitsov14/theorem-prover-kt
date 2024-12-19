import core.Formula
import core.FormulaParserException
import core.parseToFormula
import sequentProver.*
import sequentProver.ProofState.Provable
import sequentProver.ProofState.Unprovable
import java.io.File

suspend fun main(args: Array<String>) {
	when (args.size) {
		0 -> {
			//example()
			prover()
		}

		1 -> prover(args[0], null, true, true)
		3 -> {
			val out = args[1]
			when (args[2]) {
				"--format=bussproofs,ebproof", "--format=ebproof,bussproofs" -> prover(args[0], out, true, true)
				"--format=bussproofs" -> prover(args[0], out, true, false)
				"--format=ebproof" -> prover(args[0], out, false, true)
				"--format=" -> prover(args[0], out, false, false)
				else -> {
					println("Invalid arguments.")
				}
			}
		}

		else -> {
			println("Invalid arguments.")
		}
	}
}

suspend fun prover(sequentString: String, out: String?, bussproofs: Boolean, ebproof: Boolean) {
	// Parse
	val sequent = try {
		sequentString.parseToSequent()
	} catch (e: FormulaParserException) {
		println(e.message)
		return
	}
	// Prove
	println("Proving...")
	val start = System.currentTimeMillis()
	val (proofState, node) = sequent.prove()
	val end = System.currentTimeMillis()
	println(proofState)
	if (proofState == Provable || proofState == Unprovable) {
		println("Completed in ${end - start} ms.")
	}
	// TeX
	if (bussproofs) {
		println("Generating bussproofs TeX...")
		File(out, "out-bussproofs.tex").writeText(node.getBussproofsLatex())
		println("Done!")
	}
	if (ebproof) {
		println("Generating ebproof TeX...")
		File(out, "out-ebproof.tex").writeText(node.getEbproofLatex())
		println("Done!")
	}
}

suspend fun prover() {
	print("INPUT A FORMULA >>> ")
	val sequent = readln().parseToSequent()
	println(sequent)
	val start = System.currentTimeMillis()
	val (proofState, node) = sequent.prove()
	val end = System.currentTimeMillis()
	println(proofState)
	println("Completed in ${end - start} ms")
	File("out-bussproofs.tex").writeText(node.getBussproofsLatex())
	File("out-ebproof.tex").writeText(node.getEbproofLatex())
	listOf(node).printProof()
}

suspend fun example() {
	val lines = File("src/main/resources/Examples.txt").readLines().iterator()
	var time = 0L
	while (lines.hasNext()) {
		print(lines.next())
		print(": ")
		val fmls = mutableListOf<Formula>()
		while (lines.hasNext()) {
			val line = lines.next()
			if (line.isEmpty()) break
			fmls += line.parseToFormula()
		}
		val assumptions = fmls.dropLast(1).toSet()
		val conclusions = setOf(fmls.last())
		val sequent = Sequent(assumptions, conclusions)
		val start = System.currentTimeMillis()
		val (proofState, _) = sequent.prove()
		val end = System.currentTimeMillis()
		println(proofState)
		time += end - start
		println(end - start)
	}
	println("Completed in $time ms")
}
