package core

import org.junit.jupiter.api.Test
import kotlin.test.assertEquals

internal class FormulaTest {
	@Test
	fun simplify() {
		assertEquals(
			"not P to not Q".parseToFormula(),
			"(true to (P iff false)) to not(Q or false and R)".parseToFormula().simplify()
		)
		assertEquals("true".parseToFormula(), "((x ==> y) ==> true) or ~false".parseToFormula().simplify())
	}

	@Test
	fun nnf() {
		assertEquals(
			"(p and q or not p and not q) and r and not s or(p and not q or not p and q) and (not r or s)".parseToFormula(),
			"(p iff q) iff not (r to s)".parseToFormula().simplify().pureNNF()
		)
	}

	@Test
	fun dnf() {
		assertEquals(
			setOf(
				setOf("P".parseToFormula(), "not P".parseToFormula()),
				setOf("P".parseToFormula(), "not R".parseToFormula()),
				setOf("Q".parseToFormula(), "R".parseToFormula(), "not P".parseToFormula()),
				setOf("Q".parseToFormula(), "R".parseToFormula(), "not R".parseToFormula())
			), "(P or Q and R) and (not P or not R)".parseToFormula().pureDNF()
		)
		assertEquals(
			setOf(
				setOf("P".parseToFormula(), "not R".parseToFormula()),
				setOf("Q".parseToFormula(), "R".parseToFormula(), "not P".parseToFormula())
			), "(P or Q and R) and (not P or not R)".parseToFormula().simpleDNF()
		)
	}

	@Test
	fun cnf() {
		assertEquals(
			setOf(
				setOf("P".parseToFormula(), "Q".parseToFormula()),
				setOf("P".parseToFormula(), "R".parseToFormula()),
				setOf("not R".parseToFormula(), "not P".parseToFormula())
			), "(P or Q and R) and (not P or not R)".parseToFormula().simpleCNF()
		)
		assertEquals(
			"[[Def_0, ¬q, r], [q, ¬Def_0], [¬r, ¬Def_0], [Def_1, ¬p], [Def_1, ¬Def_0], [p, Def_0, ¬Def_1], [Def_2, ¬Def_1, ¬s], [Def_1, ¬Def_2], [s, ¬Def_2], [Def_2]]",
			"(p or (q and not r)) and s".parseToFormula().makeDefCNF().toString()
		)
	}
}
