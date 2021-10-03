/*
// 毎回比べるのは効率悪いよね．
private data class GoalToSet(val fixedVars: Set<Var>, val assumptions: Set<Formula>, val conclusion: Formula)
private fun Goals.toSet(): Set<GoalToSet> = this.map { GoalToSet(it.fixedVars.toSet(), it.assumptions.toSet(), it.conclusion) }.toSet()
fun Goals.isEqual(other: Goals): Boolean {
	if (this == other) return true
	if (this.toSet() == other.toSet()) return true
	return true
}
 */

interface IFlowOfGoals {
	val previousGoals: Goals
	val nextGoals: Goals
	val tactic: ITactic
}

data class FlowOfGoals0(
	override val previousGoals: Goals,
	override val nextGoals: Goals,
	override val tactic: Tactic0
): IFlowOfGoals {
	override fun toString() = "$tactic"
}

data class FlowOfGoals1WithFormula(
	override val previousGoals: Goals,
	override val nextGoals: Goals,
	override val tactic: Tactic1,
	val assumption: Formula
): IFlowOfGoals {
	override fun toString() = "$tactic $assumption"
}

data class FlowOfGoals1WithVar(
	override val previousGoals: Goals,
	override val nextGoals: Goals,
	override val tactic: Tactic1,
	val fixedVar: Var
): IFlowOfGoals {
	override fun toString() = "$tactic ($fixedVar)"
}

data class FlowOfGoals2WithFormulaAndFormula(
	override val previousGoals: Goals,
	override val nextGoals: Goals,
	override val tactic: Tactic2,
	val assumptionApply: Formula,
	val assumptionApplied: Formula
): IFlowOfGoals {
	override fun toString() = "$tactic $assumptionApply $assumptionApplied"
}

data class FlowOfGoals2WithFormulaAndVar(
	override val previousGoals: Goals,
	override val nextGoals: Goals,
	override val tactic: Tactic2,
	val assumption: Formula,
	val fixedVar: Var
): IFlowOfGoals {
	override fun toString() = "$tactic $assumption ($fixedVar)"
}

typealias History = MutableList<IFlowOfGoals>

data class TreeNodeOfHistory(
	val currentGoals: Goals,
	val parent: Pair<IFlowOfGoals, TreeNodeOfHistory>? = null,
	val childrenOfGoals: MutableList<Pair<IFlowOfGoals, TreeNodeOfHistory>> = mutableListOf(),
	var isDead: Boolean = false,
	var isSolved: Boolean = false
) {
	fun getAllDescendants(): List<TreeNodeOfHistory> {
		val result = mutableListOf(this)
		for (children in this.childrenOfGoals) {
			result.addAll(children.second.getAllDescendants())
		}
		return result
	}
	fun getAllAliveNodes(): List<TreeNodeOfHistory> = getAllDescendants().filterNot { it.isDead }

	fun getAllSolvedNodes(): List<TreeNodeOfHistory> = getAllDescendants().filter { it.isSolved }

	private fun getAllParents(): List<TreeNodeOfHistory> {
		val result = mutableListOf(this)
		if (parent != null) {
			result.addAll(parent.second.getAllParents())
		}
		return result
	}

	fun getHistory(): History = getAllParents().mapNotNull { it.parent?.first }.reversed().toMutableList()

	fun addNewPossibleNode() {
		if (isDead) { return }
		val currentGoal = currentGoals[0]
		val possibleTactic0s = Tactic0.values().filter { it.canApply(currentGoal) }
		val possibleTactic1s = Tactic1.values().filter { it.canApply(currentGoal) }
		val possibleTactic2s = Tactic2.values().filter { it.canApply(currentGoal) }
		for (tactic in possibleTactic0s) {
			val newGoals = tactic.apply(currentGoals)
			val newIFlowOfGoals = FlowOfGoals0(currentGoals, newGoals, tactic)
			val newNode = TreeNodeOfHistory(newGoals, Pair(newIFlowOfGoals, this))
			childrenOfGoals.add(Pair(newIFlowOfGoals, newNode))
		}
		/*
		for (tactic in possibleTactic1s) {
			// TODO: 2021/10/03
		}
		for (tactic in possibleTactic2s) {
			// TODO: 2021/10/03
		}
		*/
		for (child in childrenOfGoals) {
			if (child.second.currentGoals.isEmpty()) {
				child.second.isSolved = true
			}
		}
		isDead = true
		for (child in childrenOfGoals) {
			print("${child.second.currentGoals}, ")
		}
		println("\b\b are new children.")
	}
}

const val MAX_STEP = 10

fun prover(goals: Goals): List<History> {
	val root = TreeNodeOfHistory(goals)
	//val solvedNodes = root.getAllSolvedNodes()
	//val allNodes = root.getAllDescendants()
	var steps = 0
	while (root.getAllSolvedNodes().isEmpty() && root.getAllAliveNodes().isNotEmpty() && steps < MAX_STEP) {
		println("This is the ${steps}th step.")
		root.getAllDescendants().forEach { it.addNewPossibleNode() }
		steps++
		println("the size of all nodes is ${root.getAllDescendants().size}.")
		println("the size of all alive nodes is ${root.getAllAliveNodes().size}.")
		println("the size of all solved nodes is ${root.getAllSolvedNodes().size}.")
		println("--------------------------------------")
	}
	return root.getAllSolvedNodes().map { it.getHistory() }
}

private fun History.isIntuitionistic(): Boolean = this.all { it.tactic != Tactic0.BY_CONTRA }

fun List<History>.getIntuitionisticProofs(): List<History> = this.filter { it.isIntuitionistic() }
