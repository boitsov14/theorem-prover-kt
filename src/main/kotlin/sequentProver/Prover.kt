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

data class Node(
	var sequentToBeApplied: Sequent
) {
	lateinit var applyDataWithNode: IApplyDataWithNode
}
