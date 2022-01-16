import core.*
//import tacticGame.*
import sequentProver.*

/*
(all x, P x) to (ex x, P x)
(ex y, all x, P x y) to (all x, ex y, P x y)
not (P and Q) to (not P or not Q)
P and not P to Q
P to Q to (P and Q to R and S) to R
((A to B) to A) to A
A to (A to B) to ((A to B) to C) to C
((P or not P) to Q and not Q) to false
not (P and Q and R and S and T) to (not P or not Q or not R or not S or not T)
not (P and Q and R and S and T and U) to (not P or not Q or not R or not S or not T or not U)
not (P and Q and R and S and T and U and V) to (not P or not Q or not R or not S or not T or not U or not V)
((A and B) to C) to (A to C) or (B to C)
(A or B or C or D or E or F or G or X) or (AA or BB or CC or DD or EE or FF or GG or not X)
(A to B) to (not A or B)
(A to B) to not not (not A or B)
(A iff not A) to false
false to P
P to true
(forall x. P(x)) implies (forall x. R(x) and Q(x)) implies S(a) implies exists x. (P(x) and Q(x) and R(x))
(forall x. P(x)) and (forall x. Q(x)) implies exists x. (P(x) and Q(x))
exists x. P(x) and Q(x) implies Q(x) and P(x)
(exists y. forall x. P(x,y)) implies forall x. exists y. P(x,y)
A & B | A & ~B | ~A & B | ~A & ~B
 */

fun main() {
	while (true) {
		print("INPUT A FORMULA >>> ")
		val fml = readLine()!!.parse()
	}
	//print("INPUT A FORMULA >>> ")
	//val fml = readLine()!!.parse()
	//val firstSequent = Sequent(setOf(fml))
	//firstSequent.prove()

	/*
	val firstGoals = Goal(fml).toGoals()
	prove(firstGoals)
	letMeProve(firstGoals)
	 */
}

/*
fun main() {
	/*
	val x = Var("x")
	val y = Var("y")
	val fml0 = Formula.PREDICATE("P", listOf(x))
	val fml1 = Formula.ALL(x, fml0) // all x, P x
	//val fml2 = Formula.ALL(x, fml1) // throw exception
	//val fml3 = fml1.replace(y, x) // throw exception
	 */

	//println(""" /\ \/ and or forall x ~false""".toUnicode())

	/*
	while (true) {
		print("INPUT A FORMULA >>> ")
		val str = readLine()!!
		try {
			println(parse(str))
		} catch (e: FormulaParserException) {
			println(e.message)
		}
		println("--------------------------------------")
	}
	 */

	/*
	val x = Var("x")
	val x_1 = Var("x_1")
	val x_2 = Var("x_2")
	val y = Var("y")
	//val str = "ex x, ex x_1, P x x_1 x_2 y"
	val str = "P x and ex x , Q x and P x"
	val fml = parse(str)
	println(fml)
	try {
		println(fml.replace(x, x_1))
	} catch (e: DuplicateBddVarException) {
		println(e)
	}
	 */

}
 */

/*
	val variousGoals = listOf(
	listOf(Goal("all x, all y, P x y".parse()!!)),
	listOf(Goal("P and Q to Q and P".parse()!!)),
	listOf(Goal("P or Q to Q or P".parse()!!)),
	listOf(Goal("(ex x, P x) to ex y, P y".parse()!!)),
	listOf(Goal("(ex x, P x) to all x, P x".parse()!!)),
	listOf(Goal("(ex x, P x) to (ex x, Q x) to (all x, R x)".parse()!!)),
	listOf(Goal("(all x, P x) to (ex x, P x)".parse()!!)),
	listOf(Goal("P to (P to Q) to Q".parse()!!)),
	listOf(Goal("P to not P to false".parse()!!))
	)
	*/
