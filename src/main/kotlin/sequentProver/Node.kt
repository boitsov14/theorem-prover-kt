package sequentProver

import core.Formula
import core.Formula.Quantified
import core.Substitution
import core.Term
import core.Term.*

/**
 * A node to construct a proof tree
 *
 * @property sequent the sequent to be applied.
 */
sealed interface INode {
	val sequent: Sequent
}

// TODO: 2022/11/27 tacticをもつNodeと持たないNodeで分けて考える？
// TODO: 2022/11/23 INodeとは別にIHasChildみたいなの用意する？
data class AxiomNode(
	override val sequent: Sequent,
) : INode

data class UnaryNode(
	override val sequent: Sequent, val tactic: UnaryTactic, val fml: Formula, val child: INode
) : INode

data class BinaryNode(
	override val sequent: Sequent,
	val tactic: BinaryTactic,
	val fml: Formula,
	val leftChild: INode,
	val rightChild: INode
) : INode

data class FreshVarNode(
	override val sequent: Sequent, val tactic: FreshVarTactic, val fml: Quantified, val freshVar: Var, val child: INode
) : INode

data class TermNode(
	override val sequent: Sequent, val tactic: TermTactic, val fml: Quantified, val term: Term, val child: INode
) : INode

data class UnificationNode(
	override val sequent: Sequent, var fmls: Set<Quantified> = emptySet(), var child: INode? = null
) : INode

typealias UnificationNodes = List<UnificationNode>

fun INode.complete(substitution: Substitution, newSequent: Sequent): INode = if (AXIOM.canApply(newSequent)) {
	AxiomNode(newSequent)
} else when (this) {
	is AxiomNode -> AxiomNode(newSequent)
	is UnaryNode -> {
		val newFml = (newSequent.assumptions + newSequent.conclusions).first { it == fml.replace(substitution) }
		val newChildSequent = tactic.apply(newSequent, newFml)
		UnaryNode(newSequent, tactic, newFml, child.complete(substitution, newChildSequent))
	}

	is BinaryNode -> {
		val newFml = (newSequent.assumptions + newSequent.conclusions).first { it == fml.replace(substitution) }
		val (newLeftSequent, newRightSequent) = tactic.apply(newSequent, newFml)
		BinaryNode(
			newSequent,
			tactic,
			newFml,
			leftChild.complete(substitution, newLeftSequent),
			rightChild.complete(substitution, newRightSequent)
		)
	}

	is FreshVarNode -> {
		val newFml =
			(newSequent.assumptions + newSequent.conclusions).first { it == fml.replace(substitution) } as Quantified
		// TODO: 2022/12/24 FreshVarを取り直すとうれしい具体例がほしい
		// TODO: 2023/06/04 "∀x∃y(P(x) ∧ Q(y)) → ∃y∀x(P(x) ∧ Q(y))"の証明がバグるので一旦FreshVarを変えないようにする
		// val newFreshVar = newFml.bddVar.getFreshVar(newSequent.freeVars)
		val newChildSequent = tactic.apply(newSequent, newFml, freshVar)
		// val newSubstitution = substitution.mapValues { it.value.replace(freshVar, newFreshVar) }
		FreshVarNode(newSequent, tactic, newFml, freshVar, child.complete(substitution, newChildSequent))
	}

	is TermNode -> {
		term as UnificationTerm
		val newTerm = substitution[term] ?: Dummy
		val newFml =
			(newSequent.assumptions + newSequent.conclusions).first { it == fml.replace(substitution) } as Quantified
		val newChildSequent = tactic.apply(newSequent, newFml, newTerm)
		val newSubstitution = if (newTerm is Dummy) substitution + mapOf(term to newTerm) else substitution
		TermNode(newSequent, tactic, newFml, newTerm, child.complete(newSubstitution, newChildSequent))
	}

	is UnificationNode -> {
		child!!.complete(substitution, newSequent)
	}
}

private fun INode.getLatexRec(): String = when (this) {
	is AxiomNode -> """\AxiomC{}
		|\RightLabel{\scriptsize Axiom}
		|\UnaryInf$${sequent.toLatex()}$
	""".trimMargin()

	is UnaryNode -> """${child.getLatexRec()}
		|\RightLabel{\scriptsize ${tactic.toLatex()}}
		|\UnaryInf$${sequent.toLatex()}$
	""".trimMargin()

	is FreshVarNode -> """${child.getLatexRec()}
		|\RightLabel{\scriptsize ${tactic.toLatex()}}
		|\UnaryInf$${sequent.toLatex()}$
	""".trimMargin()

	is TermNode -> """${child.getLatexRec()}
		|\RightLabel{\scriptsize ${tactic.toLatex()}}
		|\UnaryInf$${sequent.toLatex()}$
	""".trimMargin()

	is BinaryNode -> """${leftChild.getLatexRec()}
		|${rightChild.getLatexRec()}
		|\RightLabel{\scriptsize ${tactic.toLatex()}}
		|\BinaryInf$${sequent.toLatex()}$
	""".trimMargin()

	is UnificationNode -> child?.getLatexRec() ?: """\Axiom$${sequent.toLatex()}$"""
}

private fun INode.getLatexRec2(): String = when (this) {
	is AxiomNode -> """\infer0[\scriptsize Axiom]{ ${sequent.toLatex()} }"""

	is UnaryNode -> """${child.getLatexRec2()}
		|\infer1[\scriptsize ${tactic.toLatex()}]{ ${sequent.toLatex()} }
	""".trimMargin()

	is FreshVarNode -> """${child.getLatexRec2()}
		|\infer1[\scriptsize ${tactic.toLatex()}]{ ${sequent.toLatex()} }
	""".trimMargin()

	is TermNode -> """${child.getLatexRec2()}
		|\infer1[\scriptsize ${tactic.toLatex()}]{ ${sequent.toLatex()} }
	""".trimMargin()

	is BinaryNode -> """${leftChild.getLatexRec2()}
		|${rightChild.getLatexRec2()}
		|\infer2[\scriptsize ${tactic.toLatex()}]{ ${sequent.toLatex()} }
	""".trimMargin()

	is UnificationNode -> child?.getLatexRec2() ?: """\hypo{ ${sequent.toLatex()} }"""
}

fun INode.getBussproofsLatex(): String = """\documentclass[preview,varwidth=\maxdimen,border=10pt]{standalone}
	|\usepackage{bussproofs}
	|\begin{document}
	|\begin{prooftree}
	|\renewcommand{\fCenter}{\ \mbox{$\vdash$}\ }
	|${getLatexRec()}
	|\end{prooftree}
	|\end{document}
	|
""".trimMargin()

fun INode.getEbproofLatex(): String = """\documentclass[preview,varwidth=\maxdimen,border=10pt]{standalone}
	|\usepackage{ebproof}
	|\begin{document}
	|\begin{prooftree}
	|${getLatexRec2().replace("""\fCenter""", """ &\vdash""")}
	|\end{prooftree}
	|\end{document}
	|
""".trimMargin()

tailrec fun List<INode>.printProof() {
	println("-----------------------")
	if (this.isEmpty()) {
		println("Proof is completed!")
		return
	}
	this.map { it.sequent }.forEach { println(it) }
	when (val node = this.first()) {
		is AxiomNode -> {
			println("Axiom")
			this.drop(1).printProof()
		}

		is UnaryNode -> {
			println(node.tactic)
			(listOf(node.child) + this.drop(1)).printProof()
		}

		is BinaryNode -> {
			println(node.tactic)
			(listOf(node.leftChild, node.rightChild) + this.drop(1)).printProof()
		}

		is FreshVarNode -> {
			println(node.tactic)
			(listOf(node.child) + this.drop(1)).printProof()
		}

		is TermNode -> {
			println(node.tactic)
			(listOf(node.child) + this.drop(1)).printProof()
		}

		is UnificationNode -> {
			println("UnProvable")
			this.drop(1).printProof()
		}
	}
}

enum class ProofState {
	Provable, Unprovable, TooManyTerms;

	override fun toString(): String = when (this) {
		Provable -> "Provable."
		Unprovable -> "Unprovable."
		TooManyTerms -> "Proof Failed: Too many unification terms."
	}
}
