package sequentProver

import core.*
import core.Formula.*

data class Node(
	var sequentToBeApplied: Sequent,
	val siblingLabel: Int?,
	var applyData: IApplyData? = null,
	var child: Node? = null,
	var leftChild: Node? = null,
	var rightChild: Node? = null
)

data class IndependentNode(val sequentToBeApplied: Sequent, val applyData: IApplyData?)

fun Node.toIndependentNode(): IndependentNode = IndependentNode(sequentToBeApplied, applyData)

fun Node.completeProof(substitution: Substitution) {
	if (AXIOM.canApply(sequentToBeApplied)) {
		applyData = AXIOM.ApplyData
		child = null
	}
	when(val oldApplyData = applyData) {
		AXIOM.ApplyData, null -> {}
		is UnaryTactic.ApplyData -> {
			val newFml = (sequentToBeApplied.assumptions + sequentToBeApplied.conclusions)
				.firstOrNull { it == oldApplyData.fml.replace(substitution) }
				?: throw IllegalTacticException()
			val newApplyData = oldApplyData.copy(fml = newFml)
			applyData = newApplyData
			child!!.sequentToBeApplied = newApplyData.applyTactic(sequentToBeApplied)
			child!!.completeProof(substitution)
		}
		is BinaryTactic.ApplyData -> {
			val newFml = (sequentToBeApplied.assumptions + sequentToBeApplied.conclusions)
				.firstOrNull { it == oldApplyData.fml.replace(substitution) }
				?: throw IllegalTacticException()
			val newApplyData = oldApplyData.copy(fml = newFml)
			applyData = newApplyData
			leftChild!!.sequentToBeApplied = newApplyData.applyTactic(sequentToBeApplied).first
			rightChild!!.sequentToBeApplied = newApplyData.applyTactic(sequentToBeApplied).second
			leftChild!!.completeProof(substitution)
			rightChild!!.completeProof(substitution)
		}
		is FreshVarInstantiationTactic.ApplyData -> {
			val newFml = (sequentToBeApplied.assumptions + sequentToBeApplied.conclusions)
				.filterIsInstance<Quantified>()
				.firstOrNull { it == oldApplyData.fml.replace(substitution) }
				?: throw IllegalTacticException()
			val newApplyData = oldApplyData.copy(fml = newFml)
			applyData = newApplyData
			child!!.sequentToBeApplied = newApplyData.applyTactic(sequentToBeApplied)
			child!!.completeProof(substitution)
		}
		is TermInstantiationTactic.ApplyData -> {
			val unificationTerm = oldApplyData.term
			val term = substitution[unificationTerm] ?: unificationTerm
			val newFml = (sequentToBeApplied.assumptions + sequentToBeApplied.conclusions)
				.filterIsInstance<Quantified>()
				.firstOrNull { it == oldApplyData.fml.replace(substitution) }
				?: throw IllegalTacticException()
			val newApplyData = TermInstantiationTactic.ApplyData(newFml, term)
			applyData = newApplyData
			child!!.sequentToBeApplied = newApplyData.applyTactic(sequentToBeApplied)
			child!!.completeProof(substitution)
		}
	}
}

/*
private fun Node.getProof(): List<IApplyData> = listOf(applyData!!) + when(applyData!!) {
	AXIOM.ApplyData -> emptyList()
	is UnaryTactic.ApplyData, is FreshVarInstantiationTactic.ApplyData, is TermInstantiationTactic.ApplyData -> child!!.getProof()
	is BinaryTactic.ApplyData -> leftChild!!.getProof() + rightChild!!.getProof()
}
fun Node.printProof() {
	val proof = getProof()
	val sequents = mutableListOf(this.sequentToBeApplied)
	for (data in proof) {
		sequents.forEach { println(it) }
		when(data) {
			AXIOM.ApplyData -> sequents.removeFirst()
			is UnaryTactic.ApplyData -> sequents[0] = data.applyTactic(sequents[0])
			is BinaryTactic.ApplyData -> {
				val newSequents = data.applyTactic(sequents[0])
				sequents[0] = newSequents.first
				sequents.add(1, newSequents.second)
			}
			is FreshVarInstantiationTactic.ApplyData -> sequents[0] = data.applyTactic(sequents[0])
			is TermInstantiationTactic.ApplyData -> sequents[0] = data.applyTactic(sequents[0])
		}
		println(">>> ${data.tactic}")
	}
	if (sequents.isNotEmpty()) throw IllegalArgumentException()
}
 */

private fun Node.getReversedProof(): List<IndependentNode> = listOf(toIndependentNode()) + when(applyData) {
	AXIOM.ApplyData, null -> emptyList()
	is UnaryTactic.ApplyData, is TermInstantiationTactic.ApplyData, is FreshVarInstantiationTactic.ApplyData -> child!!.getReversedProof()
	is BinaryTactic.ApplyData -> rightChild!!.getReversedProof() + leftChild!!.getReversedProof()
}

fun Node.getProofTree(): String = getReversedProof().reversed().joinToString(separator = "\n") {
	when(it.applyData) {
		null -> "\\Axiom$${it.sequentToBeApplied.toLatex()}$"
		AXIOM.ApplyData -> "\\AxiomC{}\n\\RightLabel{\\scriptsize ${it.applyData.tactic.toLatex()}}\n\\UnaryInf$${it.sequentToBeApplied.toLatex()}$"
		is UnaryTactic.ApplyData, is FreshVarInstantiationTactic.ApplyData, is TermInstantiationTactic.ApplyData -> "\\RightLabel{\\scriptsize ${it.applyData.tactic.toLatex()}}\n\\UnaryInf$${it.sequentToBeApplied.toLatex()}$"
		is BinaryTactic.ApplyData -> "\\RightLabel{\\scriptsize ${it.applyData.tactic.toLatex()}}\n\\BinaryInf$${it.sequentToBeApplied.toLatex()}$"
	}
}

fun Node.getLatexOutput(proofState: ProofState): String = "\\documentclass[preview,varwidth=10000px,border=3mm]{standalone}\n" +
		"\\usepackage{bussproofs}\n" +
		"\\begin{document}\n" +
		"\$${sequentToBeApplied.toLatex().replace("\\fCenter", "\\vdash").replace("""^\s\\\s""".toRegex(), "")}\$\\par\n" +
		"$proofState\n" +
		"\\begin{prooftree}\n" +
		"\\def\\fCenter{\\mbox{\$\\vdash\$}}\n" +
		getProofTree() +
		"\n" +
		"\\end{prooftree}\n" +
		"\\rightline{@sequent\\_bot}\n" +
		"\\end{document}\n"

/*
	val latexProof: String
	print("Latex Start...")
	val getLatexProofTime = measureTimeMillis{
		latexProof = this.getProofTree()
	}
	println("Completed in $getLatexProofTime ms")
 */

fun Node.checkProof(): Boolean {
	TODO()
}

/*
fun Node.checkCorrectness(): Boolean = try {
	when(val applyDataWithNode = applyDataWithNode) {
		null -> false
		AxiomApplyData 						-> AXIOM.canApply(sequentToBeApplied)
		is UnaryApplyDataWithNode 			-> applyDataWithNode.applyData.applyTactic(sequentToBeApplied) == applyDataWithNode.node.sequentToBeApplied && applyDataWithNode.node.checkCorrectness()
		is BinaryApplyDataWithNodes 		-> applyDataWithNode.applyData.applyTactic(sequentToBeApplied) == applyDataWithNode.leftNode.sequentToBeApplied to applyDataWithNode.rightNode.sequentToBeApplied && applyDataWithNode.leftNode.checkCorrectness() && applyDataWithNode.rightNode.checkCorrectness()
		is UnificationTermApplyDataWithNode -> applyDataWithNode.applyData.applyTactic(sequentToBeApplied) == applyDataWithNode.node.sequentToBeApplied && applyDataWithNode.node.checkCorrectness()
		is TermApplyDataWithNode 			-> applyDataWithNode.applyData.applyTactic(sequentToBeApplied) == applyDataWithNode.node.sequentToBeApplied && applyDataWithNode.node.checkCorrectness()
}
} catch (e: IllegalTacticException) {
	false
 */

enum class ProofState {
	Success, Unprovable, LoopCountFail, UnificationTermInstantiationCountFail, UnificationTimeFail, MemoryError;
	override fun toString(): String = when(this) {
		Success -> "Provable."
		Unprovable -> "Unprovable."
		LoopCountFail -> "Proof Failed: too many loops."
		UnificationTermInstantiationCountFail -> "Proof Failed: too many unification terms."
		UnificationTimeFail -> "Proof Failed: too long unification time."
		MemoryError -> "Proof Failed: out of memory error."
	}
}
