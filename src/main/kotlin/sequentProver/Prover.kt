package sequentProver

import core.Term
import core.Term.*

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

// TODO: 2022/01/29 valではダメか
data class Node(
	var sequentToBeApplied: Sequent,
	val siblingLabel: Int?,
	var applyDataWithNode: IApplyDataWithNode? = null
)

data class IndependentNode(val sequentToBeApplied: Sequent, val applyData: IApplyData?)

fun Node.toIndependentNode(): IndependentNode = IndependentNode(sequentToBeApplied, applyDataWithNode?.applyData)

fun Node.completeProof(substitution: Map<UnificationTerm, Term>) {
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
				applyDataWithNode.node.completeProof(substitution + mapOf(unificationTerm to variable))
			} else {
				val additionalSubstitution = term.unificationTerms.associateWith { it.availableVars.first() }
				val applyData = applyDataWithNode.applyData.toTermTacticApplyData(term)
				this.applyDataWithNode = TermApplyDataWithNode(applyData, applyDataWithNode.node)
				applyDataWithNode.node.sequentToBeApplied = applyData.applyTactic(sequentToBeApplied)
				applyDataWithNode.node.completeProof(substitution + additionalSubstitution)
			}
		}
		is TermApplyDataWithNode -> throw IllegalArgumentException()
	}
}

// TODO: 2022/02/03 消す
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
}
 */

private fun Node.getReversedProof(): List<IndependentNode> = listOf(toIndependentNode()) + when(val applyDataWithNode = applyDataWithNode) {
	AxiomApplyData, null 				-> emptyList()
	is UnaryApplyDataWithNode 			-> applyDataWithNode.node.getReversedProof()
	is BinaryApplyDataWithNodes 		-> applyDataWithNode.rightNode.getReversedProof() + applyDataWithNode.leftNode.getReversedProof()
	is UnificationTermApplyDataWithNode -> applyDataWithNode.node.getReversedProof()
	is TermApplyDataWithNode 			-> applyDataWithNode.node.getReversedProof()
}

fun Node.getLatexProof(): String = getReversedProof().reversed().joinToString(separator = "\n") {
	when(it.applyData) {
		null 																							 -> "\\Axiom$${it.sequentToBeApplied.toLatex()}$"
		AXIOM.ApplyData 	    -> "\\AxiomC{}\n\\RightLabel{\\scriptsize ${it.applyData.tactic.toLatex()}}\n\\UnaryInf$${it.sequentToBeApplied.toLatex()}$"
		is UnaryTactic.ApplyData 			-> "\\RightLabel{\\scriptsize ${it.applyData.tactic.toLatex()}}\n\\UnaryInf$${it.sequentToBeApplied.toLatex()}$"
		is BinaryTactic.ApplyData 			-> "\\RightLabel{\\scriptsize ${it.applyData.tactic.toLatex()}}\n\\BinaryInf$${it.sequentToBeApplied.toLatex()}$"
		is UnificationTermTactic.ApplyData 	-> "\\RightLabel{\\scriptsize ${it.applyData.tactic.toLatex()}}\n\\UnaryInf$${it.sequentToBeApplied.toLatex()}$"
		is TermTactic.ApplyData 			-> "\\RightLabel{\\scriptsize ${it.applyData.tactic.toLatex()}}\n\\UnaryInf$${it.sequentToBeApplied.toLatex()}$"
	}
}
