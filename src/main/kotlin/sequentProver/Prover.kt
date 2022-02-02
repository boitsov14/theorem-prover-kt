package sequentProver

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
	val siblingLabel: Int?
) {
	lateinit var applyDataWithNode: IApplyDataWithNode
}

data class IndependentNode(val sequentToBeApplied: Sequent, val applyData: IApplyData)

fun Node.toIndependentNode(): IndependentNode = IndependentNode(sequentToBeApplied, applyDataWithNode.applyData)

fun Node.checkCorrectness(): Boolean = try {
	when(val applyDataWithNode = applyDataWithNode) {
		AxiomApplyData 						-> AXIOM.canApply(sequentToBeApplied)
		is UnaryApplyDataWithNode 			-> applyDataWithNode.applyData.applyTactic(sequentToBeApplied) == applyDataWithNode.node.sequentToBeApplied && applyDataWithNode.node.checkCorrectness()
		is BinaryApplyDataWithNodes 		-> applyDataWithNode.applyData.applyTactic(sequentToBeApplied) == applyDataWithNode.leftNode.sequentToBeApplied to applyDataWithNode.rightNode.sequentToBeApplied && applyDataWithNode.leftNode.checkCorrectness() && applyDataWithNode.rightNode.checkCorrectness()
		is UnificationTermApplyDataWithNode -> applyDataWithNode.applyData.applyTactic(sequentToBeApplied) == applyDataWithNode.node.sequentToBeApplied && applyDataWithNode.node.checkCorrectness()
		is TermApplyDataWithNode 			-> applyDataWithNode.applyData.applyTactic(sequentToBeApplied) == applyDataWithNode.node.sequentToBeApplied && applyDataWithNode.node.checkCorrectness()
	}
} catch (e: IllegalTacticException) {
	false
}

private fun Node.getReversedProof(): List<IndependentNode> = listOf(toIndependentNode()) + when(val applyDataWithNode = applyDataWithNode) {
	AxiomApplyData 						-> emptyList()
	is UnaryApplyDataWithNode 			-> applyDataWithNode.node.getReversedProof()
	is BinaryApplyDataWithNodes 		-> applyDataWithNode.rightNode.getReversedProof() + applyDataWithNode.leftNode.getReversedProof()
	is UnificationTermApplyDataWithNode -> applyDataWithNode.node.getReversedProof()
	is TermApplyDataWithNode 			-> applyDataWithNode.node.getReversedProof()
}

fun Node.getLatexProof(): String = getReversedProof().reversed().joinToString(separator = "\n") {
	when(it.applyData) {
		AXIOM.ApplyData 	    -> "\\AxiomC{}\n\\RightLabel{\\scriptsize ${it.applyData.tactic.toLatex()}}\n\\UnaryInf$${it.sequentToBeApplied.toLatex()}$"
		is UnaryTactic.ApplyData 			-> "\\RightLabel{\\scriptsize ${it.applyData.tactic.toLatex()}}\n\\UnaryInf$${it.sequentToBeApplied.toLatex()}$"
		is BinaryTactic.ApplyData 			-> "\\RightLabel{\\scriptsize ${it.applyData.tactic.toLatex()}}\n\\BinaryInf$${it.sequentToBeApplied.toLatex()}$"
		is UnificationTermTactic.ApplyData 	-> "\\RightLabel{\\scriptsize ${it.applyData.tactic.toLatex()}}\n\\UnaryInf$${it.sequentToBeApplied.toLatex()}$"
		is TermTactic.ApplyData 			-> "\\RightLabel{\\scriptsize ${it.applyData.tactic.toLatex()}}\n\\UnaryInf$${it.sequentToBeApplied.toLatex()}$"
	}
}
