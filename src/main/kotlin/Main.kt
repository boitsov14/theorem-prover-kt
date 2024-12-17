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

		1 -> prover(args.first())
		2 -> {
			when (args[1]) {
				"--out=bussproofs,ebproof" -> prover(args.first())
				"--out=bussproofs" -> prover(args.first(), ebproof = false)
				"--out=ebproof" -> prover(args.first(), bussproofs = false)
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

suspend fun prover(sequentString: String, bussproofs: Boolean = true, ebproof: Boolean = true) {
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
		File("out-bussproofs.tex").writeText(node.getBussproofsLatex())
		println("Done!")
	}
	if (ebproof) {
		println("Generating ebproof TeX...")
		File("out-ebproof.tex").writeText(node.getEbproofLatex())
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
	File("out.tex").writeText(node.getBussproofsLatex())
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
