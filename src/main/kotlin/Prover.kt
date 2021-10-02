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





/*
fun prover(goals: Goals): List<History> {
	val listOfHistory: MutableList<History> = mutableListOf(mutableListOf(FlowOfGoals0(
		listOf(),
		goals,
		Tactic0.INTRO
	)))
	//val currentGoals = goals
	//val currentGoal = currentGoals[0]
	for (histories in listOfHistory) {
		listOfHistory.remove(histories)
		val history = histories.last()
		val currentGoals = history.nextGoals
		for (tactic0 in Tactic0.values().filter { it.canApply(currentGoals[0]) }) {
			histories.add(FlowOfGoals0(currentGoals, tactic0.apply(currentGoals), tactic0))
		}
	}
}
 */
