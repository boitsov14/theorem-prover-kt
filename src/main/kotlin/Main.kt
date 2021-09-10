fun main() {
    println("Hello.")
}

interface Formula {
    override fun toString(): String
}

interface AtomFml: Formula {}

enum class PreDefinedAtomFml: AtomFml {
    FALSE
}

val falseFormula = PreDefinedAtomFml.FALSE

data class Var(val chr: Char) {
    override fun toString() = "$chr"
}

data class Predicate(val id: Char, val arity: Int) {
    override fun toString(): String = "$id"
    fun canSubstitute(inputVars: List<Var>): Boolean = inputVars.size == arity
}

data class PredicateFml(val predicate: Predicate, val vars: List<Var>): AtomFml {
    override fun toString(): String {
        var str = "$predicate "
        vars.forEach { str += "$it " }
        str = str.trimEnd()
        return str
    }
}

interface Connective {
    val id: Char
    val precedence: Int
    override fun toString(): String
}

interface ConnectiveFml: Formula {
    val connective: Connective
}

enum class UnaryConnective(override val id: Char, override val precedence: Int): Connective {
    NOT('¬',4);
    override fun toString() = "$id"
}

data class UnaryConnectiveFml(override val connective: UnaryConnective, val formula: Formula): ConnectiveFml {
    override fun toString(): String = "($connective$formula)"
}

enum class BinaryConnective(override val id: Char, override val precedence: Int): Connective {
    IMPLY('→', 1),
    AND('∧', 3),
    OR('∨', 2),
    IFF('↔', 0);
    override fun toString(): String = "$id"
}

data class BinaryConnectiveFml(override val connective: BinaryConnective, val leftFml: Formula, val rightFml: Formula): ConnectiveFml {
    override fun toString(): String = "($leftFml $connective $rightFml)"
}

enum class Quantifier(private val id: Char) {
    FOR_ALL('∀'),
    THERE_EXISTS('∃');
    override fun toString(): String = "$id"
}

data class QuantifiedFml(val quantifier: Quantifier, val bddVars: List<Var>, val formula: Formula): Formula {
    override fun toString(): String {
        var str = "$quantifier"
        bddVars.forEach { str += " $it" }
        str += ", "
        str += "$formula"
        return str
    }
}

data class Goal(var freeVars: MutableList<Var>, var assumptions: MutableList<Formula>, var conclusion: Formula) {
    constructor(assumptions: MutableList<Formula>, conclusion: Formula) : this(mutableListOf(), assumptions, conclusion)
    constructor(conclusion: Formula) : this(mutableListOf(), conclusion)
    override fun toString(): String {
        var str = ""
        assumptions.forEach { str += "$it".removeSurrounding("(", ")") + ", "}
        str = str.removeSuffix(", ")
        if (str.isNotEmpty()) { str += " " }
        return "$str⊢ $conclusion"
    }
}

typealias Goals = MutableList<Goal>

interface ITactic {
    val id: String
    override fun toString(): String
    fun canApply(goal: Goal): Boolean
    fun apply(goals: Goals)
}

// Tactic with arity 0.
enum class Tactic0(override val id: String): ITactic {
    ASSUMPTION  ("assumption"),
    INTRO       ("intro"),
    SPLIT       ("split"),
    LEFT        ("left"),
    RIGHT       ("right"),
    EXFALSO     ("exfalso"),
    BY_CONTRA   ("by_contra");
    override fun toString(): String = id
    override fun canApply(goal: Goal): Boolean = when(this) {
        ASSUMPTION			-> goal.conclusion in goal.assumptions
        INTRO				-> (goal.conclusion as? ConnectiveFml)?.connective in setOf(BinaryConnective.IMPLY, UnaryConnective.NOT)
        SPLIT				-> (goal.conclusion as? ConnectiveFml)?.connective in setOf(BinaryConnective.AND, BinaryConnective.IFF)
        LEFT, RIGHT			-> (goal.conclusion as? ConnectiveFml)?.connective == BinaryConnective.OR
        EXFALSO, BY_CONTRA	-> goal.conclusion != falseFormula
    }
    override fun apply(goals: Goals) {
        val goal = goals[0]
        when(this) {
            ASSUMPTION -> goals.removeAt(0)
            INTRO -> when((goal.conclusion as ConnectiveFml).connective) {
                BinaryConnective.IMPLY  -> {
                    goal.assumptions.add((goal.conclusion as BinaryConnectiveFml).leftFml)
                    goal.conclusion = (goal.conclusion as BinaryConnectiveFml).rightFml
                }
                UnaryConnective.NOT -> {
                    goal.assumptions.add((goal.conclusion as UnaryConnectiveFml).formula)
                    goal.conclusion = falseFormula
                }
            }
            SPLIT -> when((goal.conclusion as ConnectiveFml).connective) {
                BinaryConnective.AND    -> {
                    val left  = Goal(goal.assumptions.toMutableList(), (goal.conclusion as BinaryConnectiveFml).leftFml)
                    val right = Goal(goal.assumptions.toMutableList(), (goal.conclusion as BinaryConnectiveFml).rightFml)
                    goals.removeAt(0)
                    goals.add(0, left)
                    goals.add(1, right)
                }
                BinaryConnective.IFF    -> {
                    val toLeft  = Goal(goal.assumptions.toMutableList(), BinaryConnectiveFml(BinaryConnective.IMPLY, (goal.conclusion as BinaryConnectiveFml).leftFml, (goal.conclusion as BinaryConnectiveFml).rightFml))
                    val toRight = Goal(goal.assumptions.toMutableList(), BinaryConnectiveFml(BinaryConnective.IMPLY, (goal.conclusion as BinaryConnectiveFml).rightFml, (goal.conclusion as BinaryConnectiveFml).leftFml))
                    goals.removeAt(0)
                    goals.add(0, toLeft)
                    goals.add(1, toRight)
                }
            }
            LEFT    -> goal.conclusion = (goal.conclusion as BinaryConnectiveFml).leftFml
            RIGHT   -> goal.conclusion = (goal.conclusion as BinaryConnectiveFml).rightFml
            EXFALSO -> goal.conclusion = falseFormula
            BY_CONTRA -> {
                goal.assumptions.add(UnaryConnectiveFml(UnaryConnective.NOT, goal.conclusion))
                goal.conclusion = falseFormula
            }
        }
    }
}

// Tactic with arity 1.
enum class Tactic1(override val id: String): ITactic {
    APPLY("apply"),
    CASES("cases"),
    CLEAR("clear");
    override fun toString(): String = id
    override fun canApply(goal: Goal): Boolean = when(this) {
        CLEAR   -> goal.assumptions.isNotEmpty()
        else    -> possibleAssumptions(goal).isNotEmpty()
    }
    override fun apply(goals: Goals) {
        TODO("Not yet implemented")
    }
    fun possibleAssumptions(goal: Goal): List<Formula> = when(this) {
        APPLY   -> goal.assumptions
            .filter {   ((it as? ConnectiveFml)?.connective == BinaryConnective.IMPLY   && (it as BinaryConnectiveFml).rightFml == goal.conclusion)
                    ||  ((it as? ConnectiveFml)?.connective == UnaryConnective.NOT      && goal.conclusion == falseFormula) }
        CASES   -> goal.assumptions
            .filter { (it as? ConnectiveFml)?.connective in setOf(BinaryConnective.AND, BinaryConnective.OR, BinaryConnective.IFF) }
        else    -> listOf()
    }
}

// Tactic with arity 2.
enum class Tactic2(override val id: String): ITactic {
    HAVE("have");
    override fun toString(): String = id
    override fun canApply(goal: Goal): Boolean {
        TODO("Not yet implemented")
    }
    override fun apply(goals: Goals) {
        TODO("Not yet implemented")
    }
    fun possibleAssumptions(goal: Goal): Set<Formula> {
        TODO("Not yet implemented")
    }
}

/*
fun isConnective(chr: Char): Boolean = chr in Connective.values().map{it.chr}
fun getConnective(chr: Char) : Connective? = Connective.values().find{it.chr == chr}
*/

/*
fun main() {
    val fml1 = Prop('P')
    val fml11 = Prop('P')
    println(fml1 == fml11)
    println(fml1)
    println(UnaryConnective.NOT)
    val fml2 = UnaryConnectiveFml(UnaryConnective.NOT, fml1)
    val fml21 = UnaryConnectiveFml(UnaryConnective.NOT, fml11)
    println(fml2 == fml21)
    println(fml2)
    val fml3 = BinaryConnectiveFml(BinaryConnective.AND, fml1, fml2)
    println(fml3)
    println(BinaryConnective.values().map{it.id})
    val goal1 = Goal(mutableListOf(fml3,fml2), fml1)
    println(goal1)
    println(BinaryConnective.IFF.ordinal)

    val propOfP = Predicate("P", listOf(Type.UNIVERSE, Type.UNIVERSE))
    val varOfx = Var('x', Type.UNIVERSE)
    val varOfy = Var('y', Type.UNIVERSE)
    val propOfPxy = PredicateFml(propOfP, listOf(varOfx,varOfy))
    println(propOfPxy)
    println(propOfP)
    println(varOfx.toStringWithExplicitType())
}
*/

/*
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
 */