package sequentProver

import core.*

// TODO: 2022/02/04 nested classにする？
sealed interface IApplyDataWithNode {
	val applyData: IApplyData
}

object AxiomApplyData: IApplyDataWithNode {
	override val applyData = AXIOM.ApplyData
}

data class UnaryApplyDataWithNode(
	override val applyData: UnaryTactic.ApplyData,
	val node: Node
): IApplyDataWithNode

data class BinaryApplyDataWithNodes(
	override val applyData: BinaryTactic.ApplyData,
	val leftNode: Node,
	val rightNode: Node
): IApplyDataWithNode

data class UnificationTermApplyDataWithNode(
	override val applyData: UnificationTermTactic.ApplyData,
	val node: Node
): IApplyDataWithNode

data class TermApplyDataWithNode(
	override val applyData: TermTactic.ApplyData,
	val node: Node
): IApplyDataWithNode

data class Node(
	var sequentToBeApplied: Sequent,
	val siblingLabel: Int?,
	var applyDataWithNode: IApplyDataWithNode? = null
)

data class IndependentNode(val sequentToBeApplied: Sequent, val applyData: IApplyData?)

fun Node.toIndependentNode(): IndependentNode = IndependentNode(sequentToBeApplied, applyDataWithNode?.applyData)

fun Node.completeProof(substitution: Substitution) {
	if (AXIOM.canApply(sequentToBeApplied)) {
		applyDataWithNode = AxiomApplyData
	}
	when(val applyDataWithNode = applyDataWithNode) {
		AxiomApplyData, null -> {}
		is UnaryApplyDataWithNode -> {
			val newApplyData = applyDataWithNode.applyData.copy(fml = applyDataWithNode.applyData.fml.replace(substitution))
			this.applyDataWithNode = applyDataWithNode.copy(newApplyData)
			applyDataWithNode.node.sequentToBeApplied = newApplyData.applyTactic(sequentToBeApplied)
			applyDataWithNode.node.completeProof(substitution)
		}
		is BinaryApplyDataWithNodes -> {
			val newApplyData = applyDataWithNode.applyData.copy(fml = applyDataWithNode.applyData.fml.replace(substitution))
			this.applyDataWithNode = applyDataWithNode.copy(newApplyData)
			applyDataWithNode.leftNode.sequentToBeApplied = newApplyData.applyTactic(sequentToBeApplied).first
			applyDataWithNode.rightNode.sequentToBeApplied = newApplyData.applyTactic(sequentToBeApplied).second
			applyDataWithNode.leftNode.completeProof(substitution)
			applyDataWithNode.rightNode.completeProof(substitution)
		}
		is UnificationTermApplyDataWithNode -> {
			val unificationTerm = applyDataWithNode.applyData.unificationTerm
			val term = substitution[unificationTerm]
			if (term == null) {
				val variable = unificationTerm.availableVars.first()
				val applyData = applyDataWithNode.applyData.toTermTacticApplyData(variable)
				this.applyDataWithNode = TermApplyDataWithNode(applyData, applyDataWithNode.node)
				applyDataWithNode.node.sequentToBeApplied = applyData.applyTactic(sequentToBeApplied)
				val additionalSubstitution = mapOf(unificationTerm to variable)
				applyDataWithNode.node.completeProof(substitution.map { it.key to it.value.replace(additionalSubstitution) }.toMap() + additionalSubstitution)
			} else {
				val additionalSubstitution = term.unificationTerms.associateWith { it.availableVars.first() }
				val applyData = applyDataWithNode.applyData.toTermTacticApplyData(term)
				this.applyDataWithNode = TermApplyDataWithNode(applyData, applyDataWithNode.node)
				applyDataWithNode.node.sequentToBeApplied = applyData.applyTactic(sequentToBeApplied)
				applyDataWithNode.node.completeProof(substitution.map { it.key to it.value.replace(additionalSubstitution) }.toMap() + additionalSubstitution)
			}
		}
		is TermApplyDataWithNode -> throw IllegalArgumentException()
	}
}

private fun Node.getProof(): List<IApplyData> = listOf(applyDataWithNode!!.applyData) + when(val applyDataWithNode = applyDataWithNode!!) {
	AxiomApplyData		 				-> emptyList()
	is UnaryApplyDataWithNode 			-> applyDataWithNode.node.getProof()
	is BinaryApplyDataWithNodes 		-> applyDataWithNode.leftNode.getProof() + applyDataWithNode.rightNode.getProof()
	is UnificationTermApplyDataWithNode -> applyDataWithNode.node.getProof()
	is TermApplyDataWithNode 			-> applyDataWithNode.node.getProof()
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
			is UnificationTermTactic.ApplyData -> throw IllegalArgumentException()
			is TermTactic.ApplyData -> sequents[0] = data.applyTactic(sequents[0])
		}
		println(">>> ${data.tactic}")
	}
	if (sequents.isNotEmpty()) throw IllegalArgumentException()
}

private fun Node.getReversedProof(): List<IndependentNode> = listOf(toIndependentNode()) + when(val applyDataWithNode = applyDataWithNode) {
	AxiomApplyData, null 				-> emptyList()
	is UnaryApplyDataWithNode 			-> applyDataWithNode.node.getReversedProof()
	is BinaryApplyDataWithNodes 		-> applyDataWithNode.rightNode.getReversedProof() + applyDataWithNode.leftNode.getReversedProof()
	is UnificationTermApplyDataWithNode -> applyDataWithNode.node.getReversedProof()
	is TermApplyDataWithNode 			-> applyDataWithNode.node.getReversedProof()
}

fun Node.getProofTree(): String = getReversedProof().reversed().joinToString(separator = "\n") {
	when(it.applyData) {
		null -> "\\Axiom$${it.sequentToBeApplied.toLatex()}$"
		AXIOM.ApplyData 	    -> "\\AxiomC{}\n\\RightLabel{\\scriptsize ${it.applyData.tactic.toLatex()}}\n\\UnaryInf$${it.sequentToBeApplied.toLatex()}$"
		is UnaryTactic.ApplyData 			-> "\\RightLabel{\\scriptsize ${it.applyData.tactic.toLatex()}}\n\\UnaryInf$${it.sequentToBeApplied.toLatex()}$"
		is BinaryTactic.ApplyData 			-> "\\RightLabel{\\scriptsize ${it.applyData.tactic.toLatex()}}\n\\BinaryInf$${it.sequentToBeApplied.toLatex()}$"
		is UnificationTermTactic.ApplyData 	-> "\\RightLabel{\\scriptsize ${it.applyData.tactic.toLatex()}}\n\\UnaryInf$${it.sequentToBeApplied.toLatex()}$"
		is TermTactic.ApplyData 			-> "\\RightLabel{\\scriptsize ${it.applyData.tactic.toLatex()}}\n\\UnaryInf$${it.sequentToBeApplied.toLatex()}$"
	}
}
