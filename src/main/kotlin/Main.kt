fun main() {
    val predicateOfP2 = Predicate('P',2)
    val varOfX = Var('x')
    val varOfY = Var('y')
    val predicateFmlOfPxy = PredicateFml(predicateOfP2, listOf(varOfX, varOfY))
    val allyPredicateFmlOfPxy = QuantifiedFml(Quantifier.FOR_ALL, varOfY, predicateFmlOfPxy)
    val allxAllyPredicateFmlOfPxy = QuantifiedFml(Quantifier.FOR_ALL, varOfX, allyPredicateFmlOfPxy)
    val goalOfAllxAllyPredicateFmlOfPxy = Goal(allxAllyPredicateFmlOfPxy)
    val goals0 = mutableListOf(goalOfAllxAllyPredicateFmlOfPxy)

    val predicateOfP = Predicate('P')
    val predicateOfQ = Predicate('Q')
    val propP = PredicateFml(predicateOfP)
    val propQ = PredicateFml(predicateOfQ)
    val propPAndQ = BinaryConnectiveFml(BinaryConnective.AND, propP, propQ)
    val propQAndP = BinaryConnectiveFml(BinaryConnective.AND, propQ, propP)
    val propOfAnd = BinaryConnectiveFml(BinaryConnective.IMPLY, propPAndQ, propQAndP)
    val goalOfPropOfAnd = Goal(propOfAnd)
    val goalOfPropOfAnd0 = Goal(mutableListOf(propP, propQ), propPAndQ)
    val goals = mutableListOf(goalOfPropOfAnd0)

    val propPAOrQ = BinaryConnectiveFml(BinaryConnective.OR, propP, propQ)
    val propQOrP = BinaryConnectiveFml(BinaryConnective.OR, propQ, propP)
    val propOfOr = BinaryConnectiveFml(BinaryConnective.IMPLY, propPAOrQ, propQOrP)
    val goalOfPropOfOr = Goal(propOfOr)
    val goals2 = mutableListOf(goalOfPropOfOr)

    while (goals.isNotEmpty()) {
        println("--------------------------------------")
        printGoals(goals)
        val goal = goals[0]
        print("Possible tactics are >>> ")
        goal.possibleTactics().forEach { print("$it, ") }
        print("\b\b")
        println()
        print("Select a tactic >>> ")
        val tactic = goal.possibleTactics()[readLine()!!.toInt()]
        tactic.apply(goals)
    }
    println("--------------------------------------")

    println("Proof complete!")



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
    constructor(id: Char) : this(id, 0)
    override fun toString(): String = "$id"
    fun canSubstitute(inputVars: List<Var>): Boolean = inputVars.size == arity
}

data class PredicateFml(val predicate: Predicate, val vars: List<Var>): AtomFml {
    constructor(predicate: Predicate) : this(predicate, listOf())
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

data class QuantifiedFml(val quantifier: Quantifier, val bddVar: Var, val formula: Formula): Formula {
    override fun toString() = "$quantifier $bddVar, $formula"
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
    fun possibleTactics() = Tactic0.values().filter { it.canApply(this) }
}

typealias Goals = MutableList<Goal>

fun printGoals(goals: Goals) {
    for (goal in goals) {
        if (goal.freeVars.isNotEmpty()) {
            goal.freeVars.forEach { print("$it, ") }
            print("\b\b")
            println(" : Fixed")
        }
        goal.assumptions.forEach { println("$it".removeSurrounding("(", ")")) }
        println("⊢ ${goal.conclusion}")
    }
}

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
                            || (goal.conclusion as? QuantifiedFml)?.quantifier == Quantifier.FOR_ALL
        SPLIT				-> (goal.conclusion as? ConnectiveFml)?.connective in setOf(BinaryConnective.AND, BinaryConnective.IFF)
        LEFT, RIGHT			-> (goal.conclusion as? ConnectiveFml)?.connective == BinaryConnective.OR
        EXFALSO, BY_CONTRA	-> goal.conclusion != falseFormula
    }
    override fun apply(goals: Goals) {
        val goal = goals[0]
        when(this) {
            ASSUMPTION -> goals.removeAt(0)
            INTRO -> when((goal.conclusion as? ConnectiveFml)?.connective) {
                BinaryConnective.IMPLY  -> {
                    goal.assumptions.add((goal.conclusion as BinaryConnectiveFml).leftFml)
                    goal.conclusion = (goal.conclusion as BinaryConnectiveFml).rightFml
                }
                UnaryConnective.NOT -> {
                    goal.assumptions.add((goal.conclusion as UnaryConnectiveFml).formula)
                    goal.conclusion = falseFormula
                }
                else -> {
                    goal.freeVars.add((goal.conclusion as QuantifiedFml).bddVar)
                    goal.conclusion = (goal.conclusion as QuantifiedFml).formula
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
    REVERT("revert"),
    APPLY("apply"),
    CASES("cases"),
    CLEAR("clear");
    override fun toString(): String = id
    override fun canApply(goal: Goal): Boolean = when(this) {
        APPLY, CASES    -> possibleAssumptions(goal).isNotEmpty()
        REVERT, CLEAR   -> goal.assumptions.isNotEmpty()
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