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

fun INode.getLatex(): String = """\documentclass[preview,varwidth=\maxdimen,border=10pt]{standalone}
	|\usepackage{bussproofs}
	|\begin{document}
	|\begin{prooftree}
	|\renewcommand{\fCenter}{\ \mbox{$\vdash$}\ }
	|${getLatexRec()}
	|\end{prooftree}
	|\end{document}
	|
""".trimMargin()

fun INode.getLatex2(): String = """\documentclass[preview,varwidth=\maxdimen,border=10pt]{standalone}
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

/*
data class Node(
	var sequentToBeApplied: Sequent,
	val siblingLabel: Int? = null,
	var applyData: IApplyData? = null,
	var child: Node? = null,
	var leftChild: Node? = null,
	var rightChild: Node? = null
)

data class IndependentNode(val sequentToBeApplied: Sequent, val applyData: IApplyData?)

fun Node.toIndependentNode(): IndependentNode = IndependentNode(sequentToBeApplied, applyData)

fun Node.completeProof(substitution: Substitution) {
	if (AXIOM.canApply(sequentToBeApplied)) {
		applyData = AXIOM.ApplyData
		child = null
	}
	when (val oldApplyData = applyData) {
		AXIOM.ApplyData, null -> {}
		is UnaryTactic.ApplyData -> {
			val newFml = (sequentToBeApplied.assumptions + sequentToBeApplied.conclusions).firstOrNull {
				it == oldApplyData.fml.replace(substitution)
			} ?: throw IllegalTacticException()
			val newApplyData = oldApplyData.copy(fml = newFml)
			applyData = newApplyData
			child!!.sequentToBeApplied = newApplyData.applyTactic(sequentToBeApplied)
			child!!.completeProof(substitution)
		}

		is BinaryTactic.ApplyData -> {
			val newFml = (sequentToBeApplied.assumptions + sequentToBeApplied.conclusions).firstOrNull {
				it == oldApplyData.fml.replace(substitution)
			} ?: throw IllegalTacticException()
			val newApplyData = oldApplyData.copy(fml = newFml)
			applyData = newApplyData
			leftChild!!.sequentToBeApplied = newApplyData.applyTactic(sequentToBeApplied).first
			rightChild!!.sequentToBeApplied = newApplyData.applyTactic(sequentToBeApplied).second
			leftChild!!.completeProof(substitution)
			rightChild!!.completeProof(substitution)
		}

		is FreshVarTactic.ApplyData -> {
			val newFml =
				(sequentToBeApplied.assumptions + sequentToBeApplied.conclusions).filterIsInstance<Quantified>()
					.firstOrNull { it == oldApplyData.fml.replace(substitution) } ?: throw IllegalTacticException()
			val newApplyData = oldApplyData.copy(fml = newFml)
			applyData = newApplyData
			child!!.sequentToBeApplied = newApplyData.applyTactic(sequentToBeApplied)
			child!!.completeProof(substitution)
		}

		is TermTactic.ApplyData -> {
			val unificationTerm = oldApplyData.term
			val term = substitution[unificationTerm] ?: unificationTerm
			val newFml =
				(sequentToBeApplied.assumptions + sequentToBeApplied.conclusions).filterIsInstance<Quantified>()
					.firstOrNull { it == oldApplyData.fml.replace(substitution) } ?: throw IllegalTacticException()
			val newApplyData = TermTactic.ApplyData(newFml, term)
			applyData = newApplyData
			child!!.sequentToBeApplied = newApplyData.applyTactic(sequentToBeApplied)
			child!!.completeProof(substitution)
		}
	}
}

/*
private fun Node.getProof(): List<IApplyData> = listOf(applyData!!) + when(applyData!!) {
	AXIOM.ApplyData -> emptyList()
	is UnaryTactic.ApplyData, is FreshVarInstantiationTactic.ApplyData, is TermInstantiationTactic.ApplyData -> child!!.getProof()
	is BinaryTactic.ApplyData -> leftChild!!.getProof() + rightChild!!.getProof()
}
fun Node.printProof() {
	val proof = getProof()
	val sequents = mutableListOf(this.sequentToBeApplied)
	for (data in proof) {
		sequents.forEach { println(it) }
		when(data) {
			AXIOM.ApplyData -> sequents.removeFirst()
			is UnaryTactic.ApplyData -> sequents[0] = data.applyTactic(sequents[0])
			is BinaryTactic.ApplyData -> {
				val newSequents = data.applyTactic(sequents[0])
				sequents[0] = newSequents.first
				sequents.add(1, newSequents.second)
			}
			is FreshVarInstantiationTactic.ApplyData -> sequents[0] = data.applyTactic(sequents[0])
			is TermInstantiationTactic.ApplyData -> sequents[0] = data.applyTactic(sequents[0])
		}
		println(">>> ${data.tactic}")
	}
	if (sequents.isNotEmpty()) throw IllegalArgumentException()
}
 */

private fun Node.getReversedProof(): List<IndependentNode> = listOf(toIndependentNode()) + when (applyData) {
	AXIOM.ApplyData, null -> emptyList()
	is UnaryTactic.ApplyData, is TermTactic.ApplyData, is FreshVarTactic.ApplyData -> child!!.getReversedProof()
	is BinaryTactic.ApplyData -> rightChild!!.getReversedProof() + leftChild!!.getReversedProof()
}

fun Node.getProofTree(): String = getReversedProof().reversed().joinToString(separator = "\n") {
	when (it.applyData) {
		null -> "\\Axiom$${it.sequentToBeApplied.toLatex()}$"
		AXIOM.ApplyData -> "\\AxiomC{}\n\\RightLabel{\\scriptsize ${it.applyData.tactic.toLatex()}}\n\\UnaryInf$${it.sequentToBeApplied.toLatex()}$"
		is UnaryTactic.ApplyData, is FreshVarTactic.ApplyData, is TermTactic.ApplyData -> "\\RightLabel{\\scriptsize ${it.applyData.tactic.toLatex()}}\n\\UnaryInf$${it.sequentToBeApplied.toLatex()}$"
		is BinaryTactic.ApplyData -> "\\RightLabel{\\scriptsize ${it.applyData.tactic.toLatex()}}\n\\BinaryInf$${it.sequentToBeApplied.toLatex()}$"
	}
}

fun Node.getLatexOutput(proofState: ProofState): String =
	"\\documentclass[preview,varwidth=10000px,border=3mm]{standalone}\n" + "\\usepackage{bussproofs}\n" + "\\begin{document}\n" + "\$${
		sequentToBeApplied.toLatex().replace("\\fCenter", "\\vdash").replace("""^\s\\\s""".toRegex(), "")
	}\$\\par\n" + "$proofState\n" + "\\begin{prooftree}\n" + "\\def\\fCenter{\\mbox{\$\\vdash\$}}\n" + getProofTree() + "\n" + "\\end{prooftree}\n" + "\\rightline{@sequent\\_bot}\n" + "\\end{document}\n"

/*
	val latexProof: String
	print("Latex Start...")
	val getLatexProofTime = measureTimeMillis{
		latexProof = this.getProofTree()
	}
	println("Completed in $getLatexProofTime ms")
 */

fun Node.checkProof(): Boolean {
	TODO()
}

/*
fun Node.checkCorrectness(): Boolean = try {
	when(val applyDataWithNode = applyDataWithNode) {
		null -> false
		AxiomApplyData 						-> AXIOM.canApply(sequentToBeApplied)
		is UnaryApplyDataWithNode 			-> applyDataWithNode.applyData.applyTactic(sequentToBeApplied) == applyDataWithNode.node.sequentToBeApplied && applyDataWithNode.node.checkCorrectness()
		is BinaryApplyDataWithNodes 		-> applyDataWithNode.applyData.applyTactic(sequentToBeApplied) == applyDataWithNode.leftNode.sequentToBeApplied to applyDataWithNode.rightNode.sequentToBeApplied && applyDataWithNode.leftNode.checkCorrectness() && applyDataWithNode.rightNode.checkCorrectness()
		is UnificationTermApplyDataWithNode -> applyDataWithNode.applyData.applyTactic(sequentToBeApplied) == applyDataWithNode.node.sequentToBeApplied && applyDataWithNode.node.checkCorrectness()
		is TermApplyDataWithNode 			-> applyDataWithNode.applyData.applyTactic(sequentToBeApplied) == applyDataWithNode.node.sequentToBeApplied && applyDataWithNode.node.checkCorrectness()
}
} catch (e: IllegalTacticException) {
	false
 */
*/

enum class ProofState {
	Provable, Unprovable, TooManyTerms;

	override fun toString(): String = when (this) {
		Provable -> "Provable."
		Unprovable -> "Unprovable."
		TooManyTerms -> "Proof Failed: Too many unification terms."
	}
}
