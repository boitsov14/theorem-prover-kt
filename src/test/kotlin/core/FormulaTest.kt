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
}
