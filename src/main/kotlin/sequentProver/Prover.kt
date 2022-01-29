package sequentProver

import core.Formula

// TODO: 2022/01/21 これらは必要なのか
fun applyUnificationTermTacticOrNull(sequent: Sequent, unificationTermIndex: Int, unificationTermInstantiationMaxCount : Int): IApplyData0? {
	val availableERFmls = sequent.conclusions.filterIsInstance<Formula.EXISTS>().filter { it.unificationTermInstantiationCount <= unificationTermInstantiationMaxCount }
	val availableALFmls = sequent.assumptions.filterIsInstance<Formula.ALL>().filter { it.unificationTermInstantiationCount <= unificationTermInstantiationMaxCount }
	return if (availableERFmls.isNotEmpty()) {
		val fml = availableERFmls.first()
		UnificationTermTactic.ApplyData(UnificationTermTactic.EXISTS_RIGHT, fml, unificationTermIndex)
	} else if (availableALFmls.isNotEmpty()) {
		val fml = availableALFmls.first()
		UnificationTermTactic.ApplyData(UnificationTermTactic.ALL_LEFT, fml, unificationTermIndex)
	} else {
		null
	}
}

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
	var sequentToBeApplied: Sequent
) {
	lateinit var applyDataWithNode: IApplyDataWithNode
}

data class IndependentNode(val sequentToBeApplied: Sequent, val applyData: IApplyData)

fun Node.toIndependentNode(): IndependentNode = IndependentNode(this.sequentToBeApplied, this.applyDataWithNode.applyData)

// TODO: 2022/01/29 Binaryのとこ修正
// TODO: 2022/01/29 try&catch将来的にはなくす
fun Node.checkCorrectness(): Boolean = try {
	when(val applyDataWithNode = this.applyDataWithNode) {
		AxiomApplyData 						-> AXIOM.canApply(this.sequentToBeApplied)
		is UnaryApplyDataWithNode 			-> applyDataWithNode.applyData.applyTactic(sequentToBeApplied) == applyDataWithNode.node.sequentToBeApplied && applyDataWithNode.node.checkCorrectness()
		is BinaryApplyDataWithNodes 		-> applyDataWithNode.applyData.tactic.applyTactic(sequentToBeApplied, applyDataWithNode.applyData.fml) == applyDataWithNode.leftNode.sequentToBeApplied to applyDataWithNode.rightNode.sequentToBeApplied && applyDataWithNode.leftNode.checkCorrectness() && applyDataWithNode.rightNode.checkCorrectness()
		is UnificationTermApplyDataWithNode -> applyDataWithNode.applyData.applyTactic(sequentToBeApplied) == applyDataWithNode.node.sequentToBeApplied && applyDataWithNode.node.checkCorrectness()
		is TermApplyDataWithNode 			-> applyDataWithNode.applyData.applyTactic(sequentToBeApplied) == applyDataWithNode.node.sequentToBeApplied && applyDataWithNode.node.checkCorrectness()
	}
} catch (e: IllegalTacticException) {
	false
} catch (e: UninitializedPropertyAccessException) {
	false
}

private fun Node.getReversedProof(): List<IndependentNode> = listOf(this.toIndependentNode()) + when(val applyDataWithNode = this.applyDataWithNode) {
	AxiomApplyData 						-> emptyList()
	is UnaryApplyDataWithNode 			-> applyDataWithNode.node.getReversedProof()
	is BinaryApplyDataWithNodes 		-> applyDataWithNode.rightNode.getReversedProof() + applyDataWithNode.leftNode.getReversedProof()
	is UnificationTermApplyDataWithNode -> applyDataWithNode.node.getReversedProof()
	is TermApplyDataWithNode 			-> applyDataWithNode.node.getReversedProof()
}

fun Node.getLatexProof(): String = this.getReversedProof().reversed().joinToString(separator = "\n") {
	when(it.applyData) {
		AXIOM.ApplyData 	    -> "\\AxiomC{}\n\\RightLabel{\\scriptsize ${it.applyData.tactic.toLatex()}}\n\\UnaryInf$${it.sequentToBeApplied.toLatex()}$"
		is UnaryTactic.ApplyData 			-> "\\RightLabel{\\scriptsize ${it.applyData.tactic.toLatex()}}\n\\UnaryInf$${it.sequentToBeApplied.toLatex()}$"
		is BinaryTactic.ApplyData 			-> "\\RightLabel{\\scriptsize ${it.applyData.tactic.toLatex()}}\n\\BinaryInf$${it.sequentToBeApplied.toLatex()}$"
		is UnificationTermTactic.ApplyData 	-> "\\RightLabel{\\scriptsize ${it.applyData.tactic.toLatex()}}\n\\UnaryInf$${it.sequentToBeApplied.toLatex()}$"
		is TermTactic.ApplyData 			-> "\\RightLabel{\\scriptsize ${it.applyData.tactic.toLatex()}}\n\\UnaryInf$${it.sequentToBeApplied.toLatex()}$"
	}
}
