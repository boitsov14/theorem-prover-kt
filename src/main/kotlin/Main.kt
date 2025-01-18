import core.Formula
import core.FormulaParserException
import core.parseToFormula
import sequentProver.*
import sequentProver.ProofState.Provable
import sequentProver.ProofState.Unprovable
import java.io.File

suspend fun main(args: Array<String>) {
	// check the number of args
	when (args.size) {
		// interactively
		0 -> {
			// example()
			prover()
		}
		// args: sequent string
		1 -> prover(args[0], null, null, true, true)
		// args: output directory, memory limit in bytes, bussproofs, ebproof
		else -> {
			val out = args[0]
			val memory = args[1].toInt()
			val bussproofs = "--format=bussproofs" in args
			val ebproof = "--format=ebproof" in args
			val sequentString = File(out, "formula.txt").readText()
			prover(sequentString, out, memory, bussproofs, ebproof)
		}
	}
}

suspend fun prover(sequentString: String, out: String?, memory: Int?, bussproofs: Boolean, ebproof: Boolean) {
	val log = File(out, "prover-log.txt")
	// Parse
	log.writeText("Parsing...\n")
	val sequent = try {
		sequentString.parseToSequent()
	} catch (e: FormulaParserException) {
		log.appendText("Failed: ${e.message}\n")
		return
	}
	log.appendText("Done!\n")
	File(out, "formula.tex").writeText(sequent.toLatex())
	// Prove
	log.appendText("Proving...\n")
	val start = System.currentTimeMillis()
	val (proofState, node) = sequent.prove()
	val end = System.currentTimeMillis()
	log.appendText("$proofState\n")
	if (proofState == Provable || proofState == Unprovable) {
		log.appendText("Completed in ${end - start} ms.\n")
	}
	// TeX
	if (bussproofs) {
		log.appendText("Generating bussproofs LaTeX...\n")
		val latex = node.getBussproofsLatex()
		if (memory != null && latex.toByteArray().size > memory) {
			log.appendText("Failed: LaTeX Too Large\n")
		} else {
			File(out, "out-bussproofs.tex").writeText(latex)
			log.appendText("Done!\n")
		}
	}
	if (ebproof) {
		log.appendText("Generating ebproof LaTeX...\n")
		val latex = node.getEbproofLatex()
		if (memory != null && latex.toByteArray().size > memory) {
			log.appendText("Failed: LaTeX Too Large\n")
		} else {
			File(out, "out-ebproof.tex").writeText(latex)
			log.appendText("Done!\n")
		}
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
