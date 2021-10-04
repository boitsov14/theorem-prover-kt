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

	fun getAllDeadLeaves() = getAllDescendants().filter { it.isDead }.filter { it.childrenOfGoals.isEmpty() }

	private fun getAllParents(): List<TreeNodeOfHistory> {
		val result = mutableListOf(this)
		if (parent != null) {
			result.addAll(parent.second.getAllParents())
		}
		return result
	}

	fun getHistory(): History = getAllParents().mapNotNull { it.parent?.first }.reversed().toMutableList()

	fun addNewPossibleNode(isIntuitionistic: Boolean) {
		val currentGoal = currentGoals[0]
		val possibleTactic0s = Tactic0.values()
			.filterNot { it == if (isIntuitionistic) {Tactic0.BY_CONTRA} else {Tactic0.EXFALSO} }
			.filter { it.canApply(currentGoal) }
		val possibleTactic1s = Tactic1.values()
			.filterNot { it == Tactic1.REVERT }
			.filter { it.canApply(currentGoal) }
		val possibleTactic2s = Tactic2.values().filter { it.canApply(currentGoal) }
		for (tactic in possibleTactic0s) {
			val newGoals = tactic.apply(currentGoals)
			val newIFlowOfGoals = FlowOfGoals0(currentGoals, newGoals, tactic)
			val newNode = TreeNodeOfHistory(newGoals, Pair(newIFlowOfGoals, this))
			childrenOfGoals.add(Pair(newIFlowOfGoals, newNode))
		}
		for (tactic in possibleTactic1s) {
			for (fixedVar in tactic.possibleFixedVars(currentGoal)) {
				val newGoals = tactic.apply(currentGoals, fixedVar)
				val newIFlowOfGoals = FlowOfGoals1WithVar(currentGoals, newGoals, tactic, fixedVar)
				val newNode = TreeNodeOfHistory(newGoals, Pair(newIFlowOfGoals, this))
				childrenOfGoals.add(Pair(newIFlowOfGoals, newNode))
			}
			for (assumption in tactic.possibleAssumptions(currentGoal)) {
				val newGoals = tactic.apply(currentGoals, assumption)
				val newIFlowOfGoals = FlowOfGoals1WithFormula(currentGoals, newGoals, tactic, assumption)
				val newNode = TreeNodeOfHistory(newGoals, Pair(newIFlowOfGoals, this))
				childrenOfGoals.add(Pair(newIFlowOfGoals, newNode))
			}
		}
		for (tactic in possibleTactic2s) {
			for ((assumptionApply, assumptionApplied) in tactic.possibleAssumptionsPairs(currentGoal)) {
				val newGoals = tactic.apply(currentGoals, assumptionApply, assumptionApplied)
				val newIFlowOfGoals = FlowOfGoals2WithFormulaAndFormula(currentGoals, newGoals, tactic, assumptionApply, assumptionApplied)
				val newNode = TreeNodeOfHistory(newGoals, Pair(newIFlowOfGoals, this))
				childrenOfGoals.add(Pair(newIFlowOfGoals, newNode))
			}
			// TODO: 2021/10/03
		}
		for (child in childrenOfGoals) {
			if (child.second.currentGoals.isEmpty()) {
				child.second.isSolved = true
			}
		}
		isDead = true
		/*
		if (childrenOfGoals.isEmpty() && parent != null) {
			val bool = parent.second.childrenOfGoals.remove(Pair(parent.first, this))
			print("(creates nothing)")
		}
		 */

		/*
		for (child in childrenOfGoals) {
			print("${child.second.currentGoals}, ")
		}
		println("\b\b are new children.")
		 */
	}
}

fun prover(goals: Goals, isIntuitionistic: Boolean, maxStep: Int = 20): List<History> {
	val root = TreeNodeOfHistory(goals)
	val experiencedGoals = mutableSetOf(root.currentGoals.getGoalToSet())
	//val solvedNodes = root.getAllSolvedNodes()
	//val allNodes = root.getAllDescendants()
	var steps = 1
	while (root.getAllSolvedNodes().isEmpty() && root.getAllAliveNodes().isNotEmpty() && steps < maxStep) {
		println("STEP : $steps")
		root.getAllAliveNodes().forEach { it.addNewPossibleNode(isIntuitionistic) }

		println("${root.getAllAliveNodes().map { it.currentGoals.getGoalToSet() }.filter { it in experiencedGoals }.size} duplicate goals is deleted.")

		//val experiencedGoals0 = experiencedGoals.toSet()
		for (newNode in root.getAllAliveNodes()) {
			val newGoalToSet = newNode.currentGoals.getGoalToSet()
			if (newNode.isSolved) {
				//println("we found a proof.")
			} else if (newGoalToSet !in experiencedGoals) {
				experiencedGoals.add(newGoalToSet)
			} else {
				newNode.isDead = true
				if (newNode.parent != null) {
					val bool = newNode.parent.second.childrenOfGoals.removeAll { it == Pair(newNode.parent.first, newNode)}
					//println("duplicated goals : ${newNode.currentGoals}")
				}
			}
		}


		while (true) {
			for (node in root.getAllDeadLeaves()) {
				if (node.parent != null) {
					val bool = node.parent.second.childrenOfGoals.remove(Pair(node.parent.first, node))
					//print("(dead leaf)")
				}
			}
			if (root.getAllDeadLeaves().isEmpty() || root.getAllDescendants().size == 1) {break}
		}

		steps++
		println("NODES >>> ${root.getAllDescendants().size}")
		println("ALIVE >>> ${root.getAllAliveNodes().size}")

		//println(root.getAllDescendants().map { it.currentGoals }.distinct().size)
		//println(root.getAllDeadLeaves().map { it.currentGoals }.size)


		/*
		for (node in root.getAllDescendants()) {
			print(node.currentGoals)
			print(" : ")
		}
		println()
		for (node in root.getAllAliveNodes()) {
			print(node.currentGoals)
			print(" : ")
		}
		println()
		 */

		println("--------------------------------------")
	}
	println("TOTAL STEPS >>> ${steps-1}")
	println("PROOFS >>> ${root.getAllSolvedNodes().size}")
	return root.getAllSolvedNodes().map { it.getHistory() }
}

private fun History.isIntuitionistic(): Boolean = this.all { it.tactic != Tactic0.BY_CONTRA }

fun List<History>.getIntuitionisticProofs(): List<History> = this.filter { it.isIntuitionistic() }
