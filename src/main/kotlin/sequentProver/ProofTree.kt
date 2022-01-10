package sequentProver

/*
sealed interface ToChild {
	val applyData: IApplyData
}
data class BinaryTacticToChildren(
	override val applyData: BinaryTactic.ApplyData,
	val leftChild: Node,
	val rightChild: Node
): ToChild

data class UnaryTacticToChild(
	override val applyData: UnaryTactic.ApplyData,
	val child: Node
): ToChild

object NoChildren: ToChild {
	override val applyData: IApplyData = AXIOM.ApplyData
}

sealed interface FromParent {
	val parent: Node?
}

data class FromUnaryTacticParent(
	override val parent: Node
): FromParent

data class FromBinaryTacticParent(
	override val parent: Node,
	val isFirstSequent: Boolean
): FromParent

object NoParent: FromParent {
	override val parent: Node? = null
}

data class ApplyDataWithInfo(
	val applyData: IApplyData,
	val isFirstSequent: Boolean? = null
)

data class Node(
	val fromParent: FromParent,
	var toChild: ToChild? = null
) {
	fun setChild(applyData: IApplyData) {
		if (toChild != null) { throw IllegalArgumentException() }
		toChild = when(applyData) {
			AXIOM.ApplyData -> NoChildren
			is UnaryTactic.ApplyData -> {
				val newNode = Node(FromUnaryTacticParent(this))
				UnaryTacticToChild(applyData, newNode)
			}
			is BinaryTactic.ApplyData -> {
				val newFirstNode 	= Node(FromBinaryTacticParent(this, true))
				val newSecondNode 	= Node(FromBinaryTacticParent(this, false))
				BinaryTacticToChildren(applyData, newFirstNode, newSecondNode)
			}
		}
	}
	fun getAllUnprovedLeaves(): Set<Node> = when(toChild) {
			is UnaryTacticToChild -> (toChild as UnaryTacticToChild).child.getAllUnprovedLeaves()
			is BinaryTacticToChildren -> {
				val leftLeaves = (toChild as BinaryTacticToChildren).leftChild.getAllUnprovedLeaves()
				val rightLeaves = (toChild as BinaryTacticToChildren).rightChild.getAllUnprovedLeaves()
				leftLeaves + rightLeaves
			}
			NoChildren -> emptySet()
			null -> setOf(this)
		}
	fun getApplyDataWithInfo(isFirstSequent: Boolean?): ApplyDataWithInfo? = when(toChild) {
		is BinaryTacticToChildren -> TODO()
		NoChildren -> ApplyDataWithInfo(AXIOM.ApplyData)
		is UnaryTacticToChild -> ApplyDataWithInfo()
		null -> null
	}
	fun getAllApplyDataWithInfo(): List<ApplyDataWithInfo> {
		val result = mutableListOf<ApplyDataWithInfo>()
		if (toChild == null && fromParent.parent == null) {
			return result
		} else if (toChild == null && fromParent.parent != null) {
			return fromParent.parent!!.getAllApplyDataWithInfo()
		} else if (toChild != null && fromParent.parent == null) {
			return toChild!!.applyData
		}

		if (toChild != null) {

		}


		val toChildApplyData: List<IApplyData> = if (toChild == null) { emptyList() } else listOf(toChild!!.applyData)
	}
}
*/
