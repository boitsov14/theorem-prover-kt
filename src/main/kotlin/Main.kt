fun main() {
    val formula0 = Formula(Formula('P'), Formula('Q'), Connective.IMPLY)
    val formula1 = Formula(Formula('P'), Formula('Q'), Connective.IMPLY)
    println(formula0 == formula1)
    println(formula0)
    val formula2 = Formula(Formula('P'),null,Connective.NOT)
    println(formula2)
    //var formula2 = formula1
    //var formula3 = formula1.copy() //プロパティがすべてval（読み取り専用）なのでcopyの意味はここでは特にない
    val formula4 = Formula('P')
    val goal0 = Goal(mutableListOf(formula4), formula4)
    println(goal0)
    val goal1 = Goal(mutableListOf(formula0), formula0)
    val goal2 = goal0.copy()
    goal0.assumptions.clear()
    println(goal1)
    println(goal2)
    println(Connective.IMPLY)
    println(Connective.IMPLY.precedence)
    println(Connective.IMPLY.chr)
    val imply0 = Connective.valueOf("IMPLY")
    println(imply0.precedence)
    println(isConnective('→'))
    println(isConnective('a'))
    val imp = getConnective('→')
    println(imp?.precedence)
    println(Tactic.LEFT.canApply(goal0))
    val str = "bc)"
    println(str.removeSurrounding("(", ")"))
}

data class Formula(val left: Formula?, val right: Formula?, val connective: Connective?, val atom: Char? = null){
    constructor (atom: Char?) : this(null, null, null, atom)
    private fun toString0(): String {
        if (atom == '⊥')
            return "false"
        if (atom != null)
            return "$atom"
        if (left != null && connective == Connective.NOT)
            return "${Connective.NOT.chr}${left.toString0()}"
        if (left != null && right != null && connective != null)
            return "(${left.toString0()} ${connective.chr} ${right.toString0()})"
        return "Something is wrong." //エラー処理
    }
    override fun toString(): String = this.toString0().removeSurrounding("(", ")")
}

data class Goal(var assumptions: MutableList<Formula>, var conclusion: Formula) {
    constructor (conclusion: Formula) : this(mutableListOf(), conclusion)
    override fun toString(): String {
        var str = ""
        assumptions.forEach { str += "$it, " }
        str = str.removeSuffix(", ")
        if (str.isNotEmpty()) { str += " " }
        return "$str|- $conclusion"
    }
} //コンストラクタを別に定義した方がいいかも．リストをセットしたらリストのコピーを格納してほしい．

typealias Goals = MutableList<Goal>

enum class Connective(val chr: Char, val precedence: Int){
    IMPLY('→', 1),
    AND('∧', 3),
    OR('∨', 2),
    IFF('↔', 0),
    NOT('¬', 4);
    override fun toString(): String = "$chr"
}

fun isConnective(chr: Char): Boolean = chr in Connective.values().map{it.chr}

fun getConnective(chr: Char) : Connective? = Connective.values().find{it.chr == chr}

enum class Tactic(val ID: String, val arity: Int){
    ASSUMPTION("assumption", 0),
    INTRO("intro", 0),
    SPLIT("split", 0),
    APPLY("apply", 1),
    CASES("cases", 1),
    HAVE("have", 2),
    LEFT("left", 0),
    RIGHT("right", 0),
    EXFALSO("exfalso", 0),
    BY_CONTRA("by_contra", 0),
    CLEAR("clear", 1);
    fun canApply(goal: Goal): Boolean = when(this) {
        ASSUMPTION			-> goal.conclusion in goal.assumptions
        INTRO				-> goal.conclusion.connective in listOf(Connective.IMPLY, Connective.NOT)
        SPLIT				-> goal.conclusion.connective in listOf(Connective.AND, Connective.IFF)
        LEFT, RIGHT			-> goal.conclusion.connective == Connective.OR
        EXFALSO, BY_CONTRA	-> goal.conclusion.atom != '⊥'
        CLEAR				-> goal.assumptions.isNotEmpty() //もしくはavailablesで
        else                -> possibleAssumptions(goal).isNotEmpty()
    }
    fun possibleAssumptions(goal: Goal): List<Formula> = when(this) {
        APPLY   -> goal.assumptions
            .filter { (it.connective == Connective.IMPLY && it.right == goal.conclusion)
                    || (it.connective == Connective.NOT && goal.conclusion == Formula('⊥')) }
        CASES   -> goal.assumptions.filter { it.connective in listOf(Connective.AND, Connective.OR, Connective.IFF) }
        else    -> listOf()
    }
    fun apply(goals: Goals) {
        val goal = goals[0]
        when(this) {
            ASSUMPTION  -> goals.removeAt(0)
            INTRO       -> when(goal.conclusion.connective) {
                Connective.IMPLY    -> {
                    goal.assumptions.add(goal.conclusion.left!!)
                    goal.conclusion = goal.conclusion.right!!
                }
                Connective.NOT      -> {
                    goal.assumptions.add(goal.conclusion.left!!)
                    goal.conclusion = Formula('⊥')
                }
            }
            SPLIT       -> when(goal.conclusion.connective) {
                    Connective.AND  -> {
                        val left = Goal(goal.assumptions.toMutableList(), goal.conclusion.left!!)
                        val right = Goal(goal.assumptions.toMutableList(), goal.conclusion.right!!)
                        goals.removeAt(0)
                        goals.add(0, left)
                        goals.add(1, right)
                    }
                    Connective.IFF  -> {
                        val toLeft = Goal(goal.assumptions.toMutableList(), Formula(goal.conclusion.left, goal.conclusion.right, Connective.IMPLY))
                        val toRight = Goal(goal.assumptions.toMutableList(), Formula(goal.conclusion.right, goal.conclusion.left, Connective.IMPLY))
                        goals.removeAt(0)
                        goals.add(0, toLeft)
                        goals.add(1, toRight)
                    }
                }
            APPLY       -> TODO()
            CASES       -> TODO()
            HAVE        -> TODO()
            LEFT        -> goal.conclusion = goal.conclusion.left!!
            RIGHT       -> goal.conclusion = goal.conclusion.right!!
            EXFALSO     -> goal.conclusion = Formula('⊥')
            BY_CONTRA   -> {
                goal.assumptions.add(Formula(goal.conclusion, null, Connective.NOT))
                goal.conclusion = Formula('⊥')
            }
            CLEAR       -> TODO()
        }
    }
}
