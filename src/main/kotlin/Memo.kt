//import tacticGame.*
import core.*
import core.makeConjunction
import kotlinx.coroutines.*
import kotlin.system.measureTimeMillis
import sequentProver.*

suspend fun mainForConsole() {
	print("INPUT A FORMULA >>> ")
	val sequent = readln().parseToSequent()
	val rootNode = Node(sequent)
	val proofState = rootNode.prove(
		printSequents = false, printTacticInfo = false, printTimeInfo = true, printUnificationInfo = true
	)
	//val output = File("src/main/resources/Output.tex")
	//output.writeText(rootNode.getLatexOutput(proofState))
	/*
	val time = measureTimeMillis {
		try {
			val output = File("src/main/resources/Output.tex")
			output.writeText(rootNode.getLatexOutput(proofState))
		} catch (e: OutOfMemoryError) {
			println(e)
		}
	}
	println("Latex produced in $time ms")
	*/
}

fun mainForTest() {
	TODO()
}

fun temp() {
	/*
	while (true) {
		print("INPUT A FORMULA >>> ")
		val fml = readLine()!!.parse()
	}
	 */
	/*
	println("all x P(x, x)".parseToFormula() == "all y P(x, y)".parseToFormula())
	println("all x P(x)".parseToFormula() == "all y P(y)".parseToFormula())
	println("all x P(x)".parseToFormula() == "ex x P(x)".parseToFormula())
	println("all x P(x)".parseToFormula() == "all y P(c)".parseToFormula())
	 */
	/*
	val firstGoals = Goal(fml).toGoals()
	prove(firstGoals)
	letMeProve(firstGoals)
	 */

	/*
	val testFile = File("src/main/resources/Test.txt")
	val lines = testFile.readLines()
	val time = measureTimeMillis {
		for ((idx, line) in lines.withIndex()) {
			val sequent = try {
				line.drop(1).replace("\t", " ").parseToSequent()
			} catch (e: Exception) {
				println("ParseErr: $idx: $line")
				throw e
			}

			val rootNode = Node(sequent, null)
			val proofState = rootNode.prove()
		}
	}
	println(time)
	return
	 */

	val veryLong =
		"((o11 ∨ o12 ∨ o13) ∧ (o21 ∨ o22 ∨ o23) ∧ (o31 ∨ o32 ∨ o33) ∧ (o41 ∨ o42 ∨ o43)) → ((o11 ∧ o21) ∨ (o11 ∧ o31) ∨ (o11 ∧ o41) ∨ (o21 ∧ o31) ∨ (o21 ∧ o41) ∨ (o31 ∧ o41) ∨ (o12 ∧ o22) ∨ (o12 ∧ o32) ∨ (o12 ∧ o42) ∨ (o22 ∧ o32) ∨ (o22 ∧ o42) ∨ (o32 ∧ o42) ∨ (o13 ∧ o23) ∨ (o13 ∧ o33) ∨ (o13 ∧ o43) ∨ (o23 ∧ o33) ∨ (o23 ∧ o43) ∨ (o33 ∧ o43))"
	val tooLong =
		"((o11 ∨ o12 ∨ o13 ∨ o14) ∧ (o21 ∨ o22 ∨ o23 ∨ o24) ∧ (o31 ∨ o32 ∨ o33 ∨ o34) ∧ (o41 ∨ o42 ∨ o43 ∨ o44) ∧ (o51 ∨ o52 ∨ o53 ∨ o54)) → ((o11 ∧ o21) ∨ (o11 ∧ o31) ∨ (o11 ∧ o41) ∨ (o11 ∧ o51) ∨ (o21 ∧ o31) ∨ (o21 ∧ o41) ∨ (o21 ∧ o51) ∨ (o31 ∧ o41) ∨ (o31 ∧ o51) ∨ (o41 ∧ o51) ∨ (o12 ∧ o22) ∨ (o12 ∧ o32) ∨ (o12 ∧ o42) ∨ (o12 ∧ o52) ∨ (o22 ∧ o32) ∨ (o22 ∧ o42) ∨ (o22 ∧ o52) ∨ (o32 ∧ o42) ∨ (o32 ∧ o52) ∨ (o42 ∧ o52) ∨ (o13 ∧ o23) ∨ (o13 ∧ o33) ∨ (o13 ∧ o43) ∨ (o13 ∧ o53) ∨ (o23 ∧ o33) ∨ (o23 ∧ o43) ∨ (o23 ∧ o53) ∨ (o33 ∧ o43) ∨ (o33 ∧ o53) ∨ (o43 ∧ o53) ∨ (o14 ∧ o24) ∨ (o14 ∧ o34) ∨ (o14 ∧ o44) ∨ (o14 ∧ o54) ∨ (o24 ∧ o34) ∨ (o24 ∧ o44) ∨ (o24 ∧ o54) ∨ (o34 ∧ o44) ∨ (o34 ∧ o54) ∨ (o44 ∧ o54))"
	val veryLongIff = "((((((((a⇔b)⇔c)⇔d)⇔e)⇔f)⇔g)⇔h)⇔(a⇔(b⇔(c⇔(d⇔(e⇔(f⇔(g⇔h))))))))"
	val tooLongIff =
		"((((((((((((((((a⇔b)⇔c)⇔d)⇔e)⇔f)⇔g)⇔h)⇔i)⇔j)⇔k)⇔l)⇔m)⇔n)⇔o)⇔p)⇔(a⇔(b⇔(c⇔(d⇔(e⇔(f⇔(g⇔(h⇔(i⇔(j⇔(k⇔(l⇔(m⇔(n⇔(o⇔p))))))))))))))))"
	val tooLongIff2 =
		"(((((((((((((((((((((a⇔b)⇔c)⇔d)⇔e)⇔f)⇔g)⇔h)⇔i)⇔j)⇔k)⇔l)⇔m)⇔n)⇔o)⇔p) iff q ) iff r) iff s)iff t)iff u)⇔(a⇔(b⇔(c⇔(d⇔(e⇔(f⇔(g⇔(h⇔(i⇔(j⇔(k⇔(l⇔(m⇔(n⇔(o⇔p iff q iff r iff s iff t iff u))))))))))))))))"
	val example = "(p or (q and not r)) and s"
	val example2 = "(((p or q) or r) and s) and t"

	val long =
		"((o11 ∨ o12 ∨ o13 ∨ o14) ∧ (o21 ∨ o22 ∨ o23 ∨ o24) ∧ (o31 ∨ o32 ∨ o33 ∨ o34) ∧ (o41 ∨ o42 ∨ o43 ∨ o44) ∧ (o51 ∨ o52 ∨ o53 ∨ o54))"
	val long2 = "(o11 ∨ o12 ∨ o13) ∧ (o21 ∨ o22 ∨ o23) ∧ (o31 ∨ o32 ∨ o33) ∧ (o41 ∨ o42 ∨ o43)"
	//println(long2.parseToFormula().pureDNF().map { it.makeConjunction() }.makeDisjunction())
	/*
	println(
		"(o11 ∨ o12) ∧ (o21 ∨ o22) ∧ (o31 ∨ o32) ∧ (o41 ∨ o42)".parseToFormula().simpleDNF()
			.map { it.makeConjunction() }.makeDisjunction()
	)
	*/

}

/*
((o11 ∨ o12 ∨ o13) ∧ (o21 ∨ o22 ∨ o23) ∧ (o31 ∨ o32 ∨ o33) ∧ (o41 ∨ o42 ∨ o43)) → ((o11 ∧ o21) ∨ (o11 ∧ o31) ∨ (o11 ∧ o41) ∨ (o21 ∧ o31) ∨ (o21 ∧ o41) ∨ (o31 ∧ o41) ∨ (o12 ∧ o22) ∨ (o12 ∧ o32) ∨ (o12 ∧ o42) ∨ (o22 ∧ o32) ∨ (o22 ∧ o42) ∨ (o32 ∧ o42) ∨ (o13 ∧ o23) ∨ (o13 ∧ o33) ∨ (o13 ∧ o43) ∨ (o23 ∧ o33) ∨ (o23 ∧ o43) ∨ (o33 ∧ o43))
PROOF SUCCEED!
Completed in 370 ms
unification time: 0 ms
other time: 370 ms
loop count: 8669
Complete Proof Start... Completed in 133 ms
Latex Start...Completed in 250 ms

(o11 ∨ o12 ∨ o13) ∧ (o21 ∨ o22 ∨ o23) ∧ (o31 ∨ o32 ∨ o33) -> (o11 ∧ o21 ∧ o31) ∨ (o11 ∧ o21 ∧ o32) ∨ (o11 ∧ o21 ∧ o33) ∨ (o11 ∧ o22 ∧ o31) ∨ (o11 ∧ o22 ∧ o32) ∨ (o11 ∧ o22 ∧ o33) ∨ (o11 ∧ o23 ∧ o31) ∨ (o11 ∧ o23 ∧ o32) ∨ (o11 ∧ o23 ∧ o33) ∨ (o12 ∧ o21 ∧ o31) ∨ (o12 ∧ o21 ∧ o32) ∨ (o12 ∧ o21 ∧ o33) ∨ (o12 ∧ o22 ∧ o31) ∨ (o12 ∧ o22 ∧ o32) ∨ (o12 ∧ o22 ∧ o33) ∨ (o12 ∧ o23 ∧ o31) ∨ (o12 ∧ o23 ∧ o32) ∨ (o12 ∧ o23 ∧ o33) ∨ (o13 ∧ o21 ∧ o31) ∨ (o13 ∧ o21 ∧ o32) ∨ (o13 ∧ o21 ∧ o33) ∨ (o13 ∧ o22 ∧ o31) ∨ (o13 ∧ o22 ∧ o32) ∨ (o13 ∧ o22 ∧ o33) ∨ (o13 ∧ o23 ∧ o31) ∨ (o13 ∧ o23 ∧ o32) ∨ (o13 ∧ o23 ∧ o33)
Completed in 2375 ms
unification time: 0 ms
other time: 2375 ms
loop count: 90771
Proof formatted in 1983 ms
Provable.

(o11 ∨ o12) ∧ (o21 ∨ o22) ∧ (o31 ∨ o32) ∧ (o41 ∨ o42) -> (o11 ∧ o21 ∧ o31 ∧ o41) ∨ (o11 ∧ o21 ∧ o31 ∧ o42) ∨ (o11 ∧ o21 ∧ o32 ∧ o41) ∨ (o11 ∧ o21 ∧ o32 ∧ o42) ∨ (o11 ∧ o22 ∧ o31 ∧ o41) ∨ (o11 ∧ o22 ∧ o31 ∧ o42) ∨ (o11 ∧ o22 ∧ o32 ∧ o41) ∨ (o11 ∧ o22 ∧ o32 ∧ o42) ∨ (o12 ∧ o21 ∧ o31 ∧ o41) ∨ (o12 ∧ o21 ∧ o31 ∧ o42) ∨ (o12 ∧ o21 ∧ o32 ∧ o41) ∨ (o12 ∧ o21 ∧ o32 ∧ o42) ∨ (o12 ∧ o22 ∧ o31 ∧ o41) ∨ (o12 ∧ o22 ∧ o31 ∧ o42) ∨ (o12 ∧ o22 ∧ o32 ∧ o41) ∨ (o12 ∧ o22 ∧ o32 ∧ o42)
Completed in 828 ms
unification time: 0 ms
other time: 828 ms
loop count: 29437
Proof formatted in 545 ms
Provable.

(o11 ∨ o12 ∨ o13) ∧ (o21 ∨ o22 ∨ o23) ∧ (o31 ∨ o32 ∨ o33) ∧ (o41 ∨ o42 ∨ o43) -> (o11 ∧ o21 ∧ o31 ∧ o41) ∨ (o11 ∧ o21 ∧ o31 ∧ o42) ∨ (o11 ∧ o21 ∧ o31 ∧ o43) ∨ (o11 ∧ o21 ∧ o32 ∧ o41) ∨ (o11 ∧ o21 ∧ o32 ∧ o42) ∨ (o11 ∧ o21 ∧ o32 ∧ o43) ∨ (o11 ∧ o21 ∧ o33 ∧ o41) ∨ (o11 ∧ o21 ∧ o33 ∧ o42) ∨ (o11 ∧ o21 ∧ o33 ∧ o43) ∨ (o11 ∧ o22 ∧ o31 ∧ o41) ∨ (o11 ∧ o22 ∧ o31 ∧ o42) ∨ (o11 ∧ o22 ∧ o31 ∧ o43) ∨ (o11 ∧ o22 ∧ o32 ∧ o41) ∨ (o11 ∧ o22 ∧ o32 ∧ o42) ∨ (o11 ∧ o22 ∧ o32 ∧ o43) ∨ (o11 ∧ o22 ∧ o33 ∧ o41) ∨ (o11 ∧ o22 ∧ o33 ∧ o42) ∨ (o11 ∧ o22 ∧ o33 ∧ o43) ∨ (o11 ∧ o23 ∧ o31 ∧ o41) ∨ (o11 ∧ o23 ∧ o31 ∧ o42) ∨ (o11 ∧ o23 ∧ o31 ∧ o43) ∨ (o11 ∧ o23 ∧ o32 ∧ o41) ∨ (o11 ∧ o23 ∧ o32 ∧ o42) ∨ (o11 ∧ o23 ∧ o32 ∧ o43) ∨ (o11 ∧ o23 ∧ o33 ∧ o41) ∨ (o11 ∧ o23 ∧ o33 ∧ o42) ∨ (o11 ∧ o23 ∧ o33 ∧ o43) ∨ (o12 ∧ o21 ∧ o31 ∧ o41) ∨ (o12 ∧ o21 ∧ o31 ∧ o42) ∨ (o12 ∧ o21 ∧ o31 ∧ o43) ∨ (o12 ∧ o21 ∧ o32 ∧ o41) ∨ (o12 ∧ o21 ∧ o32 ∧ o42) ∨ (o12 ∧ o21 ∧ o32 ∧ o43) ∨ (o12 ∧ o21 ∧ o33 ∧ o41) ∨ (o12 ∧ o21 ∧ o33 ∧ o42) ∨ (o12 ∧ o21 ∧ o33 ∧ o43) ∨ (o12 ∧ o22 ∧ o31 ∧ o41) ∨ (o12 ∧ o22 ∧ o31 ∧ o42) ∨ (o12 ∧ o22 ∧ o31 ∧ o43) ∨ (o12 ∧ o22 ∧ o32 ∧ o41) ∨ (o12 ∧ o22 ∧ o32 ∧ o42) ∨ (o12 ∧ o22 ∧ o32 ∧ o43) ∨ (o12 ∧ o22 ∧ o33 ∧ o41) ∨ (o12 ∧ o22 ∧ o33 ∧ o42) ∨ (o12 ∧ o22 ∧ o33 ∧ o43) ∨ (o12 ∧ o23 ∧ o31 ∧ o41) ∨ (o12 ∧ o23 ∧ o31 ∧ o42) ∨ (o12 ∧ o23 ∧ o31 ∧ o43) ∨ (o12 ∧ o23 ∧ o32 ∧ o41) ∨ (o12 ∧ o23 ∧ o32 ∧ o42) ∨ (o12 ∧ o23 ∧ o32 ∧ o43) ∨ (o12 ∧ o23 ∧ o33 ∧ o41) ∨ (o12 ∧ o23 ∧ o33 ∧ o42) ∨ (o12 ∧ o23 ∧ o33 ∧ o43) ∨ (o13 ∧ o21 ∧ o31 ∧ o41) ∨ (o13 ∧ o21 ∧ o31 ∧ o42) ∨ (o13 ∧ o21 ∧ o31 ∧ o43) ∨ (o13 ∧ o21 ∧ o32 ∧ o41) ∨ (o13 ∧ o21 ∧ o32 ∧ o42) ∨ (o13 ∧ o21 ∧ o32 ∧ o43) ∨ (o13 ∧ o21 ∧ o33 ∧ o41) ∨ (o13 ∧ o21 ∧ o33 ∧ o42) ∨ (o13 ∧ o21 ∧ o33 ∧ o43) ∨ (o13 ∧ o22 ∧ o31 ∧ o41) ∨ (o13 ∧ o22 ∧ o31 ∧ o42) ∨ (o13 ∧ o22 ∧ o31 ∧ o43) ∨ (o13 ∧ o22 ∧ o32 ∧ o41) ∨ (o13 ∧ o22 ∧ o32 ∧ o42) ∨ (o13 ∧ o22 ∧ o32 ∧ o43) ∨ (o13 ∧ o22 ∧ o33 ∧ o41) ∨ (o13 ∧ o22 ∧ o33 ∧ o42) ∨ (o13 ∧ o22 ∧ o33 ∧ o43) ∨ (o13 ∧ o23 ∧ o31 ∧ o41) ∨ (o13 ∧ o23 ∧ o31 ∧ o42) ∨ (o13 ∧ o23 ∧ o31 ∧ o43) ∨ (o13 ∧ o23 ∧ o32 ∧ o41) ∨ (o13 ∧ o23 ∧ o32 ∧ o42) ∨ (o13 ∧ o23 ∧ o32 ∧ o43) ∨ (o13 ∧ o23 ∧ o33 ∧ o41) ∨ (o13 ∧ o23 ∧ o33 ∧ o42) ∨ (o13 ∧ o23 ∧ o33 ∧ o43)
java.lang.OutOfMemoryError

(o11 ∨ o12 ∨ o13) ∧ (o21 ∨ o22 ∨ o23) ∧ (o31 ∨ o32 ∨ o33) ∧ (o41 ∨ o42 ∨ o43) <-> (o11 ∧ o21 ∧ o31 ∧ o41) ∨ (o11 ∧ o21 ∧ o31 ∧ o42) ∨ (o11 ∧ o21 ∧ o31 ∧ o43) ∨ (o11 ∧ o21 ∧ o32 ∧ o41) ∨ (o11 ∧ o21 ∧ o32 ∧ o42) ∨ (o11 ∧ o21 ∧ o32 ∧ o43) ∨ (o11 ∧ o21 ∧ o33 ∧ o41) ∨ (o11 ∧ o21 ∧ o33 ∧ o42) ∨ (o11 ∧ o21 ∧ o33 ∧ o43) ∨ (o11 ∧ o22 ∧ o31 ∧ o41) ∨ (o11 ∧ o22 ∧ o31 ∧ o42) ∨ (o11 ∧ o22 ∧ o31 ∧ o43) ∨ (o11 ∧ o22 ∧ o32 ∧ o41) ∨ (o11 ∧ o22 ∧ o32 ∧ o42) ∨ (o11 ∧ o22 ∧ o32 ∧ o43) ∨ (o11 ∧ o22 ∧ o33 ∧ o41) ∨ (o11 ∧ o22 ∧ o33 ∧ o42) ∨ (o11 ∧ o22 ∧ o33 ∧ o43) ∨ (o11 ∧ o23 ∧ o31 ∧ o41) ∨ (o11 ∧ o23 ∧ o31 ∧ o42) ∨ (o11 ∧ o23 ∧ o31 ∧ o43) ∨ (o11 ∧ o23 ∧ o32 ∧ o41) ∨ (o11 ∧ o23 ∧ o32 ∧ o42) ∨ (o11 ∧ o23 ∧ o32 ∧ o43) ∨ (o11 ∧ o23 ∧ o33 ∧ o41) ∨ (o11 ∧ o23 ∧ o33 ∧ o42) ∨ (o11 ∧ o23 ∧ o33 ∧ o43) ∨ (o12 ∧ o21 ∧ o31 ∧ o41) ∨ (o12 ∧ o21 ∧ o31 ∧ o42) ∨ (o12 ∧ o21 ∧ o31 ∧ o43) ∨ (o12 ∧ o21 ∧ o32 ∧ o41) ∨ (o12 ∧ o21 ∧ o32 ∧ o42) ∨ (o12 ∧ o21 ∧ o32 ∧ o43) ∨ (o12 ∧ o21 ∧ o33 ∧ o41) ∨ (o12 ∧ o21 ∧ o33 ∧ o42) ∨ (o12 ∧ o21 ∧ o33 ∧ o43) ∨ (o12 ∧ o22 ∧ o31 ∧ o41) ∨ (o12 ∧ o22 ∧ o31 ∧ o42) ∨ (o12 ∧ o22 ∧ o31 ∧ o43) ∨ (o12 ∧ o22 ∧ o32 ∧ o41) ∨ (o12 ∧ o22 ∧ o32 ∧ o42) ∨ (o12 ∧ o22 ∧ o32 ∧ o43) ∨ (o12 ∧ o22 ∧ o33 ∧ o41) ∨ (o12 ∧ o22 ∧ o33 ∧ o42) ∨ (o12 ∧ o22 ∧ o33 ∧ o43) ∨ (o12 ∧ o23 ∧ o31 ∧ o41) ∨ (o12 ∧ o23 ∧ o31 ∧ o42) ∨ (o12 ∧ o23 ∧ o31 ∧ o43) ∨ (o12 ∧ o23 ∧ o32 ∧ o41) ∨ (o12 ∧ o23 ∧ o32 ∧ o42) ∨ (o12 ∧ o23 ∧ o32 ∧ o43) ∨ (o12 ∧ o23 ∧ o33 ∧ o41) ∨ (o12 ∧ o23 ∧ o33 ∧ o42) ∨ (o12 ∧ o23 ∧ o33 ∧ o43) ∨ (o13 ∧ o21 ∧ o31 ∧ o41) ∨ (o13 ∧ o21 ∧ o31 ∧ o42) ∨ (o13 ∧ o21 ∧ o31 ∧ o43) ∨ (o13 ∧ o21 ∧ o32 ∧ o41) ∨ (o13 ∧ o21 ∧ o32 ∧ o42) ∨ (o13 ∧ o21 ∧ o32 ∧ o43) ∨ (o13 ∧ o21 ∧ o33 ∧ o41) ∨ (o13 ∧ o21 ∧ o33 ∧ o42) ∨ (o13 ∧ o21 ∧ o33 ∧ o43) ∨ (o13 ∧ o22 ∧ o31 ∧ o41) ∨ (o13 ∧ o22 ∧ o31 ∧ o42) ∨ (o13 ∧ o22 ∧ o31 ∧ o43) ∨ (o13 ∧ o22 ∧ o32 ∧ o41) ∨ (o13 ∧ o22 ∧ o32 ∧ o42) ∨ (o13 ∧ o22 ∧ o32 ∧ o43) ∨ (o13 ∧ o22 ∧ o33 ∧ o41) ∨ (o13 ∧ o22 ∧ o33 ∧ o42) ∨ (o13 ∧ o22 ∧ o33 ∧ o43) ∨ (o13 ∧ o23 ∧ o31 ∧ o41) ∨ (o13 ∧ o23 ∧ o31 ∧ o42) ∨ (o13 ∧ o23 ∧ o31 ∧ o43) ∨ (o13 ∧ o23 ∧ o32 ∧ o41) ∨ (o13 ∧ o23 ∧ o32 ∧ o42) ∨ (o13 ∧ o23 ∧ o32 ∧ o43) ∨ (o13 ∧ o23 ∧ o33 ∧ o41) ∨ (o13 ∧ o23 ∧ o33 ∧ o42) ∨ (o13 ∧ o23 ∧ o33 ∧ o43)
java.lang.OutOfMemoryError

((o11 ∨ o12 ∨ o13 ∨ o14) ∧ (o21 ∨ o22 ∨ o23 ∨ o24) ∧ (o31 ∨ o32 ∨ o33 ∨ o34) ∧ (o41 ∨ o42 ∨ o43 ∨ o44) ∧ (o51 ∨ o52 ∨ o53 ∨ o54)) → ((o11 ∧ o21) ∨ (o11 ∧ o31) ∨ (o11 ∧ o41) ∨ (o11 ∧ o51) ∨ (o21 ∧ o31) ∨ (o21 ∧ o41) ∨ (o21 ∧ o51) ∨ (o31 ∧ o41) ∨ (o31 ∧ o51) ∨ (o41 ∧ o51) ∨ (o12 ∧ o22) ∨ (o12 ∧ o32) ∨ (o12 ∧ o42) ∨ (o12 ∧ o52) ∨ (o22 ∧ o32) ∨ (o22 ∧ o42) ∨ (o22 ∧ o52) ∨ (o32 ∧ o42) ∨ (o32 ∧ o52) ∨ (o42 ∧ o52) ∨ (o13 ∧ o23) ∨ (o13 ∧ o33) ∨ (o13 ∧ o43) ∨ (o13 ∧ o53) ∨ (o23 ∧ o33) ∨ (o23 ∧ o43) ∨ (o23 ∧ o53) ∨ (o33 ∧ o43) ∨ (o33 ∧ o53) ∨ (o43 ∧ o53) ∨ (o14 ∧ o24) ∨ (o14 ∧ o34) ∨ (o14 ∧ o44) ∨ (o14 ∧ o54) ∨ (o24 ∧ o34) ∨ (o24 ∧ o44) ∨ (o24 ∧ o54) ∨ (o34 ∧ o44) ∨ (o34 ∧ o54) ∨ (o44 ∧ o54))
PROOF IS TOO LONG
Completed in 13208 ms
unification time: 0 ms
other time: 13208 ms
loop count: 500000
Complete Proof Start... Completed in 10843 ms
Latex Start...Completed in 10193 ms

Completed in 75636 ms
unification time: 0 ms
other time: 75636 ms
loop count: 2820140
Proof formatted in 73075 ms
Provable.

((((((E → B) ∨ (D ∨ B)) → ((E ∨ D) → (C ∧ C))) ∧ ((C ∧ (⊥)) → (E → B))) → ((((A ∨ D) → (E → B)) ∨ ((E → B) ∧ C)) → (((B ∨ D) → (E → B)) ∧ E))) → ((((D ∨ D) ∨ (A → C)) ∨ ((B ∨ D) → C)) ∨ (((D → C) → D) → (E ∨ (E → D))))) → ((((D → E → B) ∨ ((B ∨ D) → C)) → (((C ∧ (⊥)) → (E → B)) → ((E → B) ∧ (E → A)))) ∧ (((A ∧ (E → D)) → (((E → B) ∧ C) → (E ∨ (E → D)))) ∨ (((E ∨ D) → (A ∨ D)) ∨ ((E ∨ B) ∧ (E → D)))))
Completed in 103 ms
unification time: 0 ms
other time: 103 ms
loop count: 599
Proof formatted in 25 ms
Unprovable.

P(a) to all x (P(x) to P(f(x))) to P(f(f(f(f(f(f(f(f(f(f(a)))))))))))
PROOF SUCCEED!
Completed in 5990 ms
unification time: 5967 ms
other time: 23 ms
loop count: 27
Complete Proof Start... Completed in 8 ms
Latex Start...Completed in 11 ms

PROOF SUCCEED!
Completed in 3042 ms
unification time: 3010 ms
other time: 32 ms
loop count: 27

//async
PROOF SUCCEED!
Completed in 2644 ms
unification time: 2612 ms
other time: 32 ms
loop count: 27

//async + ordinal
PROOF SUCCEED!
Completed in 1833 ms
unification time: 1790 ms
other time: 43 ms
loop count: 27

//async*2 + ordinal
PROOF SUCCEED!
Completed in 1374 ms
unification time: 1341 ms
other time: 33 ms
loop count: 27

P(a) to all x (P(x) to P(f(x))) to P(f(f(f(f(f(f(f(f(f(f(f(a))))))))))))
PROOF SUCCEED!
Completed in 42568 ms
unification time: 42544 ms
other time: 24 ms
loop count: 29
Complete Proof Start... Completed in 6 ms
Latex Start...Completed in 9 ms

PROOF SUCCEED!
Completed in 19173 ms
unification time: 19142 ms
other time: 31 ms
loop count: 29

//async
PROOF SUCCEED!
Completed in 15719 ms
unification time: 15676 ms
other time: 43 ms
loop count: 29

//async + ordinal
PROOF SUCCEED!
Completed in 9969 ms
unification time: 9938 ms
other time: 31 ms
loop count: 29

//async * 2 + ordinal
PROOF SUCCEED!
Completed in 6620 ms
unification time: 6592 ms
other time: 28 ms
loop count: 29

//async * 3 + ord
PROOF SUCCEED!
Completed in 6161 ms
unification time: 6130 ms
other time: 31 ms
loop count: 29

P(a) to all x (P(x) to P(f(x))) to P(f(f(f(f(f(f(f(f(f(f(f(f(a)))))))))))))
PROOF SUCCEED!
Completed in 327889 ms
unification time: 327868 ms
other time: 21 ms
loop count: 31
Complete Proof Start... Completed in 6 ms
Latex Start...Completed in 9 ms

PROOF SUCCEED!
Completed in 113168 ms
unification time: 113121 ms
other time: 47 ms
loop count: 31

PROOF SUCCEED!
Completed in 38834 ms
unification time: 38703 ms
other time: 131 ms
loop count: 31

P(a) to all x (P(x) to P(f(x))) to P(f(f(f(f(f(f(f(f(f(f(f(f(f(a))))))))))))))
PROOF SUCCEED!
Completed in 289192 ms
unification time: 289148 ms
other time: 44 ms
loop count: 33

P(a) to all x (P(x) to P(f(x))) to P(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(a)))))))))))))))))))))
PROOF FAILED: PROOF IS TOO LONG OR UNPROVABLE
Completed in 341069 ms
unification time: 341035 ms
other time: 34 ms
loop count: 34

not all a all b all c all d all e all f all g all h P(a,b,c,d,e,f,g,h) proves ex a ex b ex c ex d ex e ex f ex g ex h not P(a,b,c,d,e,f,g,h)
PROOF SUCCEED!
Completed in 87 ms
unification time: 5 ms
other time: 82 ms
loop count: 20
Complete Proof Start... Completed in 44 ms
Latex Start...Completed in 11 ms

((((((((((((((((a⇔b)⇔c)⇔d)⇔e)⇔f)⇔g)⇔h)⇔i)⇔j)⇔k)⇔l)⇔m)⇔n)⇔o)⇔p)⇔(a⇔(b⇔(c⇔(d⇔(e⇔(f⇔(g⇔(h⇔(i⇔(j⇔(k⇔(l⇔(m⇔(n⇔(o⇔p))))))))))))))))
PROOF IS TOO LONG
Completed in 10305 ms
unification time: 0 ms
other time: 10305 ms
loop count: 500000
Complete Proof Start... Completed in 10130 ms
Latex Start...Exception in thread "main" java.lang.OutOfMemoryError: Java heap space

((((((((((((a⇔b)⇔c)⇔d)⇔e)⇔f)⇔g)⇔h)⇔i)⇔j)⇔k)⇔l)⇔(a⇔(b⇔(c⇔(d⇔(e⇔(f⇔(g⇔(h⇔(i⇔(j⇔(k⇔l))))))))))))
Completed in 26849 ms
unification time: 0 ms
other time: 26849 ms
loop count: 1775140
Proof formatted in 29661 ms
Provable.

((((((((a⇔b)⇔c)⇔d)⇔e)⇔f)⇔g)⇔h)⇔(a⇔(b⇔(c⇔(d⇔(e⇔(f⇔(g⇔h))))))))
PROOF SUCCEED!
Completed in 553 ms
unification time: 0 ms
other time: 553 ms
loop count: 33762
Complete Proof Start... Completed in 253 ms
Latex Start...Completed in 478 ms

(∀x∃yP(x, y)) → ∀x0∃x1∃x2(P(x0, x1)∧P(x1, x2))
PROOF SUCCEED!
Completed in 109 ms
unification time: 76 ms
other time: 33 ms
loop count: 15

(∀x ∃y P(x, y)) → ∀ x0 ∃ x1 ∃x2 ∃x3 (P(x0, x1)∧P(x1, x2)∧P(x2, x3))
PROOF FAILED: PROOF IS TOO LONG OR UNPROVABLE
Completed in 97992 ms
unification time: 97843 ms
other time: 149 ms
loop count: 65

PROOF FAILED: PROOF IS TOO LONG OR UNPROVABLE
Completed in 1334836 ms
unification time: 1334558 ms
other time: 278 ms
loop count: 130

//async
Exception: java.lang.OutOfMemoryError thrown from the UncaughtExceptionHandler in thread "DefaultDispatcher-worker-8"

//async*2 + ordinal
PROOF FAILED: PROOF IS TOO LONG OR UNPROVABLE
Completed in 916706 ms
unification time: 916448 ms
other time: 258 ms
loop count: 130

∀xR(x,x), ∀x∀y∀z(R(x,y)∧R(y,z)→R(z,x)) |- ∀x∀y(R(x,y)→R(y,x))

∀x∀y∀z((R(x,y)∧R(x,z))→∃u(R(y,u)∧R(z,u))) ┣ ∀x∀s∀t(∃y∃z(R(x,y)∧R(y,s)∧R(x,z)∧R(z,t))→∃r∃q∃w(R(s,r)∧R(r,w)∧R(t,q)∧R(q,w)))

*/

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
not (P and Q and R and S and T and U and V and W and X and Y and Z) to (not P or not Q or not R or not S or not T or not U or not V or not W or not X or not Y or not Z)
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
(ex y, all x, P x y) to (all x, ex y, P x y)
(ex x, P x) and Q and R
A and B and C and D and E to E and D and C and B and A
all x P (x) to ex x P (x)
P(a) to all x (P(x) to P(f(x))) to P(f(f(a)))
p(y,f(x,z),veryLongNameFunction(veryLongNameVariable,z,z,z,z,z))
all x p( y ,f ( x , z ) ,  veryLongNameFunction (  veryLongNameVariable , z , z , z , z , z )    )
P, P to Q proves Q
( o11 | o12 | o13 ) & ( o21 | o22 | o23 ) & ( o31 | o32 | o33 ) & ( o41 | o42 | o43 ) => o11 & o21 |  o11 & o31  |  o11 & o41  | o21 & o31 | o21 & o41 | o31 & o41 | o12 & o22 | o12 & o32 | o12 & o42 | o22 & o32 | o22 & o42 | o32 & o42 | o13 & o23 | o13 & o33 | o13 & o43 | o23 & o33 | o23 & o43 | o33 & o43
 ( o11 | o12 | o13 | o14 ) & ( o21 | o22 | o23 | o24 ) & ( o31 | o32 | o33 | o34 ) & ( o41 | o42 | o43 | o44 ) & ( o51 | o52 | o53 | o54 ) => o11 & o21 | o11 & o31 | o11 & o41 | o11 & o51 | o21 & o31 | o21 & o41 | o21 & o51 | o31 & o41 | o31 & o51 | o41 & o51 | o12 & o22 | o12 & o32 | o12 & o42 | o12 & o52 | o22 & o32 | o22 & o42 | o22 & o52 | o32 & o42 | o32 & o52 | o42 & o52 | o13 & o23 | o13 & o33 | o13 & o43 | o13 & o53 | o23 & o33 | o23 & o43 | o23 & o53 | o33 & o43 | o33 & o53 | o43 & o53 | o14 & o24 | o14 & o34 | o14 & o44 | o14 & o54 | o24 & o34 | o24 & o44 | o24 & o54 | o34 & o44 | o34 & o54 | o44 & o54
A and B and C and D to D and C and B and A
A and B and C to C and B and A
P(a) to all x (P(x) to P(f(x))) to P(f(f(f(f(a)))))
P(a) to all x (P(x) to P(f(x))) to P(f(f(f(f(f(f(f(f(a))))))))) //433ms
P(a) to all x (P(x) to P(f(x))) to P(f(f(f(f(f(f(f(f(f(f(a)))))))))))
P(a) to all x (P(x) to P(f(x))) to P(f(f(f(f(f(f(f(f(f(f(f(a))))))))))))
P(a) to all x (P(x) to P(f(x))) to P(f(f(f(f(f(f(f(f(f(f(f(f(a))))))))))))) //490,981 ms
P(a) to all x (P(x) to P(f(x))) to P(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(a)))))))))))))))))))))
P(a), P(b), Q(b) proves exists x (P(x) and Q(x))
exists x (P(x) implies forall y P(y))
all x1 ex x2 all x3 ex x4 all x5 ex x6 all x7 P(x1,x2,x3,x4,x5,x6,x7) proves all y1 ex y2 all y3 ex y4 all y5 ex y6 all y7 P(y1,y2,y3,y4,y5,y6,y7)
ex x all y P(x,y) proves all y ex x P(x,y)
ex x (P(x) and Q(x)) proves ex x P(x) and ex x Q(x)
all x P(x) proves ex x P(x)
ex x P(x) proves all x P(x)
(P to Q) or (Q to P)
not all x P(x) proves ex x not P(x)
not all a all b all c all d all e all f all g all h P(a,b,c,d,e,f,g,h) proves ex a ex b ex c ex d ex e ex f ex g ex h not P(a,b,c,d,e,f,g,h)
all x P(x) proves Q
Q(a) proves ex x ex y (P(x,y) to P(y,y))
Q(a) proves ex x (P(x) to P(x))
ex x P(x), ex y Q(y) proves exists x (P(x) and Q(x))
T proves P(a), ex x (not P(x) and ( P(x) or all v Q(v))), ex x not Q(x) /// fresh var instantiation tactic に分けないとバグる例
not all a all b all c P(a,b,c) proves ex a ex b ex c not P(a,b,c)
((n1→c1)∧(p2→c1)∧(p2→c2)∧(n3→c2)∧(n4→c2)∧(c1→c2→m)∧((p4→m)→q4)∧((n4→m)→q4)∧((p3→q4)→q3)∧((n3→q4)→q3)∧((p2→q3)→q2)∧((n3→q3)→q2)∧((p1→q2)→q1)∧((n3→q2)→q1)) → q1
∀x∀y (F (x) ∧ F (y) → E(x, y)) ⊢ ∃y∀x (F (x) → E(x, y))
∀x∀y (F (x) ∧ F (y) → E(x, y)) ⊢  (F (a) → E(a, b)), (F (c) → E(c, a))
ex x (P(x) to all y P(y))
ex x (P(x) to P(f(x)))
P(a) to all x (P(x) to P(f(x))) to P(f(f(a)))
(∀x ∃y P(x, y)) → ∀ x0 ∃ x1 ∃x2 ∃x3 (P(x0, x1)∧P(x1, x2)∧P(x2, x3))
∃y P(x, y) → ∃ x1 ∃x2 ∃x3 (P(x, x1)∧P(x1, x2)∧P(x2, x3))
∃y∀x∃z∀u∃v∀w ((F (x, y, z) ∧ G (u, v, w)) → H (x, y, z, u, v, w)) → ∀x∃y∀u∃z∀w∃v ((￢F (x, y, z) ∨ ￢G (u, v, w)) ∨ H (x, y, z, u, v, w))
∃y∀x∃z∀u∃v∀w P(x,y,z,u,v,w) → ∀x∃y∀u∃z∀w∃v P(x,y,z,u,v,w)
P(a), ∀x(P(x) -> P(f(x))) |- P(f(f(f(a))))
P(a), ∀x(P(x) -> P(f(x))) |- P(f(f(f(f(f(f(f(f(f(f(f(f(a)))))))))))))
∀xP(x) -> ∃y00P(y00)
∃a∀b∃c∀d∃e∀f(P(a,d,f)→P(b,c,e))
∃a∀b∃c∀d∃e∀f(P(a,c,e)→P(b,d,f))
(∀y(p(y)→∀x p(x))→ ∀x p(x))→ ∀x p(x)
 */
