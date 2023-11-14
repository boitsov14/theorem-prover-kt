package sequentProver

import core.Formula.*
import core.Substitution
import core.Term
import core.Term.UnificationTerm
import core.getSubstitution
import core.normalize
import kotlinx.coroutines.async
import kotlinx.coroutines.coroutineScope
import sequentProver.ProofState.*

const val ASYNC_DEPTH = 4

/**
 * tries to make a proof tree without unification
 *
 * @property sequent the sequent to be proved.
 * @return the pair of the created node and the nodes waiting for unification
 */
suspend fun makeTree(
	sequent: Sequent, asyncDepth: Int = ASYNC_DEPTH
): Pair<INode, UnificationNodes> {

	//println(sequent)
	//println("Tries to make a tree")

	// AXIOM
	if (AXIOM.canApply(sequent)) {
		return AxiomNode(sequent) to emptyList()
	}

	// Unary Tactic
	for (tactic in UnaryTactic.entries) {
		val fml = tactic.getFml(sequent) ?: continue
		val newSequent = tactic.apply(sequent, fml)
		val (child, nodes) = makeTree(newSequent, asyncDepth)
		return UnaryNode(sequent, tactic, fml, child) to nodes
	}

	// Fresh Var Tactic
	for (tactic in FreshVarTactic.entries) {
		val fml = tactic.getFml(sequent) ?: continue
		val freshVar = fml.bddVar.getFreshVar(sequent.freeVars)
		val newSequent = tactic.apply(sequent, fml, freshVar)
		val (child, nodes) = makeTree(newSequent, asyncDepth)
		return FreshVarNode(sequent, tactic, fml, freshVar, child) to nodes
	}

	// Binary Tactic
	for (tactic in BinaryTactic.entries) {
		val fml = tactic.getFml(sequent) ?: continue
		val (leftSequent, rightSequent) = tactic.apply(sequent, fml)
		val (left, right) = if (asyncDepth == 0) makeTree(leftSequent, 0) to makeTree(rightSequent, 0)
		else coroutineScope {
			val deferredLeft = async { makeTree(leftSequent, asyncDepth - 1) }
			val deferredRight = async { makeTree(rightSequent, asyncDepth - 1) }
			deferredLeft.await() to deferredRight.await()
		}
		val (leftChild, leftNodes) = left
		val (rightChild, rightNodes) = right
		return BinaryNode(
			sequent, tactic, fml, leftChild, rightChild
		) to leftNodes + rightNodes
	}

	// Waits for unification
	val node = UnificationNode(sequent)
	return node to listOf(node)
}

suspend fun Sequent.prove(): Pair<ProofState, INode> {
	val (node, nodes) = makeTree(this)
	if (nodes.isEmpty()) return Provable to node
	if (nodes.any {
			it.sequent.assumptions.filterIsInstance<ALL>()
				.isEmpty() && it.sequent.conclusions.filterIsInstance<EXISTS>().isEmpty()
		}) return Unprovable to node
	val substitution = makeTreeWithUnificationBase(nodes) ?: return TooManyTerms to node
	return Provable to node.complete(substitution.normalize(), this)
}

private suspend fun makeTreeWithUnificationBase(nodes: UnificationNodes): Substitution? =
	emptyMap<UnificationTerm, Term>().makeTreeWithUnificationBase(nodes.iterator(), 0)

const val LIMIT = 4

private tailrec suspend fun Substitution.makeTreeWithUnificationBase(
	nodes: Iterator<UnificationNode>, index: Int
): Substitution? {
	if (!nodes.hasNext()) return this
	val substitution = makeTreeWithUnification(listOf(nodes.next()), index to 0, LIMIT) ?: return null
	return (this + substitution).makeTreeWithUnificationBase(nodes, index + 1)
}

private tailrec suspend fun makeTreeWithUnification(
	nodes: UnificationNodes, id: Pair<Int, Int>, limit: Int
): Substitution? {
	for (node in nodes) {
		//println("Tries term tactic")
		val (tactic, fml, term) = getTermTacticInfo(node.sequent, node.fmls, id) ?: continue
		val newSequent = tactic.apply(node.sequent, fml, term)
		val (child, newNodes) = makeTree(newSequent)
		node.child = TermNode(node.sequent, tactic, fml, term, child)
		for (newNode in newNodes) {
			newNode.fmls = node.fmls + fml
		}
		val leaves = nodes - node + newNodes
		//println("Tries unification")
		return leaves.map { it.sequent }.toSet().map { it.getSubstitutions() }.sortedBy { it.size }.getSubstitution()
			?: return makeTreeWithUnification(
				leaves, id.first to id.second + 1, limit
			)
	}
	if (limit == 0) return null
	//println("Cleans fmls")
	for (node in nodes) {
		node.fmls = emptySet()
	}
	return makeTreeWithUnification(nodes, id, limit - 1)
}

private fun getTermTacticInfo(
	sequent: Sequent, fmls: Set<Quantified>, id: Pair<Int, Int>
): Triple<TermTactic, Quantified, Term>? {
	for (tactic in TermTactic.entries) {
		val fml = tactic.getFml(sequent, fmls) ?: continue
		val availableVars = sequent.freeVars.ifEmpty { setOf(fml.bddVar) }
		val term = UnificationTerm(id, availableVars)
		return Triple(tactic, fml, term)
	}
	return null
}
