fun main() {
    val fml1 = Prop('P')
    val fml11 = Prop('P')
    println(fml1 == fml11)
    println(fml1)
    println(UnaryConnectiveType.NOT)
    val fml2 = UnaryConnective(UnaryConnectiveType.NOT, fml1)
    val fml21 = UnaryConnective(UnaryConnectiveType.NOT, fml11)
    println(fml2 == fml21)
    println(fml2)
    val fml3 = BinaryConnective(BinaryConnectiveType.AND, fml1, fml2)
    println(fml3)
    println(BinaryConnectiveType.values().map{it.chr})
    val goal1 = Goal(mutableListOf(fml3,fml2), fml1)
    println(goal1)
    println(BinaryConnectiveType.IFF.ordinal)

    val propOfP = Predicate("P", listOf(Type.UNIVERSE, Type.UNIVERSE))
    val varOfx = Var('x', Type.UNIVERSE)
    val varOfy = Var('y', Type.UNIVERSE)
    val propOfPxy = PredicateFml(propOfP, listOf(varOfx,varOfy))
    println(propOfPxy)
    println(propOfP)
    println(varOfx.toStringWithExplicitType())
}

enum class Type(private val id: String) {
    PROP("Prop"),
    UNIVERSE("U"),
    NAT("nat");
    override fun toString(): String = id
}

interface IType {
    val type: Type
}

interface Formula {
    override fun toString(): String
}

interface AtomFml: Formula {}

data class Prop(val chr: Char): AtomFml {
    override fun toString() = "$chr"
}

enum class PreDefinedAtomFml: AtomFml {
    FALSE
}

val falseFormula = PreDefinedAtomFml.FALSE

interface Term: IType {
    override fun toString(): String
}

data class Var(val chr: Char, override val type: Type): Term {
    override fun toString() = "$chr"
    fun toStringWithExplicitType() = "$chr : $type"
}

fun canSubstitute(inputTypes : List<Type>, inputTerms: List<Term>): Boolean {
    if (inputTypes.size != inputTerms.size) {
        return false
    }
    return inputTypes.zip(inputTerms).all { (type, term) -> type == term.type }
}

data class Function(val id: String, val inputTypes: List<Type>, val outputType: Type) {
    override fun toString(): String = id
}

data class FunctionTerm(val function: Function, val inputTerms: List<Term>): Term {
    override fun toString(): String {
        var str = "$function "
        inputTerms.forEach { str += "$it " }
        str = str.trimEnd()
        return str
    }
    override val type = function.outputType
}

data class Predicate(val id: String, val inputTypes: List<Type>) {
    override fun toString(): String = id
}

data class PredicateFml(val predicate: Predicate, val terms: List<Term>): AtomFml {
    override fun toString(): String {
        var str = "$predicate "
        terms.forEach { str += "$it " }
        str = str.trimEnd()
        return str
    }
}

interface ConnectiveType {
    val chr: Char
    val precedence: Int
    override fun toString(): String
}

interface Connective: Formula {
    val connective: ConnectiveType
}

enum class UnaryConnectiveType(override val chr: Char, override val precedence: Int): ConnectiveType {
    NOT('¬',4);
    override fun toString() = "$chr"
}

data class UnaryConnective(override val connective: UnaryConnectiveType, val formula: Formula): Connective {
    override fun toString(): String = "($connective$formula)"
}

enum class BinaryConnectiveType(override val chr: Char, override val precedence: Int): ConnectiveType {
    IMPLY('→', 1),
    AND('∧', 3),
    OR('∨', 2),
    IFF('↔', 0);
    override fun toString(): String = "$chr"
}

data class BinaryConnective(override val connective: BinaryConnectiveType, val left: Formula, val right: Formula): Connective {
    override fun toString(): String = "($left $connective $right)"
}

data class Goal(var assumptions: MutableList<Formula>, var conclusion: Formula) {
    constructor (conclusion: Formula) : this(mutableListOf(), conclusion)
    override fun toString(): String {
        var str = ""
        assumptions.forEach { str += "$it".removeSurrounding("(", ")") + ", "}
        str = str.removeSuffix(", ")
        if (str.isNotEmpty()) { str += " " }
        return "$str⊢ $conclusion"
    }
}

typealias Goals = MutableList<Goal>

interface TacticType {
    val id: String
    override fun toString(): String
    fun canApply(goal: Goal): Boolean
    fun apply(goals: Goals)
}

interface TacticType0: TacticType {}

enum class Tactic0(override val id: String): TacticType0 {
    ASSUMPTION("assumption"),
    INTRO("intro"),
    SPLIT("split"),
    LEFT("left"),
    RIGHT("right"),
    EXFALSO("exfalso"),
    BY_CONTRA("by_contra");
    override fun toString(): String = id
    override fun canApply(goal: Goal): Boolean = when(this) {
        ASSUMPTION			-> goal.conclusion in goal.assumptions
        INTRO				-> (goal.conclusion as? Connective)?.connective in setOf(BinaryConnectiveType.IMPLY, UnaryConnectiveType.NOT)
        SPLIT				-> (goal.conclusion as? Connective)?.connective in setOf(BinaryConnectiveType.AND, BinaryConnectiveType.IFF)
        LEFT, RIGHT			-> (goal.conclusion as? Connective)?.connective == BinaryConnectiveType.OR
        EXFALSO, BY_CONTRA	-> goal.conclusion != falseFormula
    }
    override fun apply(goals: Goals) {
        val goal = goals[0]
        when(this) {
            ASSUMPTION -> goals.removeAt(0)
            INTRO -> when((goal.conclusion as Connective).connective) {
                BinaryConnectiveType.IMPLY  -> {
                    goal.assumptions.add((goal.conclusion as BinaryConnective).left)
                    goal.conclusion = (goal.conclusion as BinaryConnective).right
                }
                UnaryConnectiveType.NOT -> {
                    goal.assumptions.add((goal.conclusion as UnaryConnective).formula)
                    goal.conclusion = falseFormula
                }
            }
            SPLIT -> when((goal.conclusion as Connective).connective) {
                BinaryConnectiveType.AND    -> {
                    val left  = Goal(goal.assumptions.toMutableList(), (goal.conclusion as BinaryConnective).left)
                    val right = Goal(goal.assumptions.toMutableList(), (goal.conclusion as BinaryConnective).right)
                    goals.removeAt(0)
                    goals.add(0, left)
                    goals.add(1, right)
                }
                BinaryConnectiveType.IFF    -> {
                    val toLeft  = Goal(goal.assumptions.toMutableList(), BinaryConnective(BinaryConnectiveType.IMPLY, (goal.conclusion as BinaryConnective).left, (goal.conclusion as BinaryConnective).right))
                    val toRight = Goal(goal.assumptions.toMutableList(), BinaryConnective(BinaryConnectiveType.IMPLY, (goal.conclusion as BinaryConnective).right, (goal.conclusion as BinaryConnective).left))
                    goals.removeAt(0)
                    goals.add(0, toLeft)
                    goals.add(1, toRight)
                }
            }
            LEFT    -> goal.conclusion = (goal.conclusion as BinaryConnective).left
            RIGHT   -> goal.conclusion = (goal.conclusion as BinaryConnective).right
            EXFALSO -> goal.conclusion = falseFormula
            BY_CONTRA -> {
                goal.assumptions.add(UnaryConnective(UnaryConnectiveType.NOT, goal.conclusion))
                goal.conclusion = falseFormula
            }
        }
    }
}




/*

fun isConnective(chr: Char): Boolean = chr in Connective.values().map{it.chr}

fun getConnective(chr: Char) : Connective? = Connective.values().find{it.chr == chr}

enum class Tactic(val ID: String, val arity: Int){
    APPLY("apply", 1),
    CASES("cases", 1),
    HAVE("have", 2),
    CLEAR("clear", 1);
    fun canApply(goal: Goal): Boolean = when(this) {
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
            APPLY       -> TODO()
            CASES       -> TODO()
            HAVE        -> TODO()
            CLEAR       -> TODO()
        }
    }
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