package sequentProver

import core.*

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
	}
	when(val applyData = applyData) {
		AXIOM.ApplyData, null -> {}
		is UnaryTactic.ApplyData -> {
			val newApplyData = applyData.copy(fml = applyData.fml.replace(substitution))
			child!!.sequentToBeApplied = newApplyData.applyTactic(sequentToBeApplied)
			child!!.completeProof(substitution)
		}
		is BinaryTactic.ApplyData -> {
			val newApplyData = applyData.copy(fml = applyData.fml.replace(substitution))
			leftChild!!.sequentToBeApplied = newApplyData.applyTactic(sequentToBeApplied).first
			rightChild!!.sequentToBeApplied = newApplyData.applyTactic(sequentToBeApplied).second
			leftChild!!.completeProof(substitution)
			rightChild!!.completeProof(substitution)
		}
		is FreshVarInstantiationTactic.ApplyData -> {
			val newApplyData = applyData.copy(fml = applyData.fml.replace(substitution))
			child!!.sequentToBeApplied = newApplyData.applyTactic(sequentToBeApplied)
			child!!.completeProof(substitution)
		}
		is TermInstantiationTactic.ApplyData -> {
			val unificationTerm = applyData.term
			val term = substitution[unificationTerm] ?: unificationTerm
			val newApplyData = TermInstantiationTactic.ApplyData(applyData.fml.replace(substitution), term)
			this.applyData = newApplyData
			child!!.sequentToBeApplied = newApplyData.applyTactic(sequentToBeApplied)
			child!!.completeProof(substitution)
		}
	}
}

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
