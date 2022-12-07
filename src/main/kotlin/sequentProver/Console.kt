package sequentProver

import core.Formula.*
import core.Term
import core.Term.*
import core.*
import sequentProver.ProofState.*

/**
 * tries to make a proof tree without unification
 *
 * @property sequent the sequent to be proved.
 * @return the pair of the created node and the nodes waiting for unification
 */
fun makeTree(
	sequent: Sequent
): Pair<INode, UnificationNodes> {

	//println(sequent)
	//println("Tries to make a tree")

	// AXIOM
	if (AXIOM.canApply(sequent)) {
		return AxiomNode(sequent) to emptyList()
	}

	// Unary Tactic
	for (tactic in UnaryTactic.values()) {
		val fml = tactic.getFml(sequent) ?: continue
		val newSequent = tactic.apply(sequent, fml)
		val (child, nodes) = makeTree(newSequent)
		return UnaryNode(sequent, tactic, fml, child) to nodes
	}

	// Fresh Var Tactic
	for (tactic in FreshVarTactic.values()) {
		val fml = tactic.getFml(sequent) ?: continue
		val freshVar = fml.bddVar.getFreshVar(sequent.freeVars)
		val newSequent = tactic.apply(sequent, fml, freshVar)
		val (child, nodes) = makeTree(newSequent)
		return FreshVarNode(sequent, tactic, fml, freshVar, child) to nodes
	}

	// Binary Tactic
	for (tactic in BinaryTactic.values()) {
		val fml = tactic.getFml(sequent) ?: continue
		val (leftSequent, rightSequent) = tactic.apply(sequent, fml)
		val (leftChild, leftNodes) = makeTree(leftSequent)
		val (rightChild, rightNodes) = makeTree(rightSequent)
		return BinaryNode(
			sequent, tactic, fml, leftChild, rightChild
		) to leftNodes + rightNodes
	}

	// Waits for unification
	val node = UnificationNode(sequent)
	return node to listOf(node)
}

suspend fun UnificationNode.prove(): ProofState {
	val (node, nodes) = makeTree(this.sequent)
	this.child = node

	if (nodes.isEmpty()) return Provable

	if (nodes.any {
			it.sequent.assumptions.filterIsInstance<ALL>()
				.isEmpty() && it.sequent.conclusions.filterIsInstance<EXISTS>().isEmpty()
		}) return Unprovable

	val substitution = makeTreeWithUnificationBase(nodes) ?: return TooManyTerms

	println(substitution)

	// TODO: 2022/12/06 ここでsubstitutionをcompleteし，それをもとにnode全体をcompleteする

	return Provable
}

private suspend fun makeTreeWithUnificationBase(nodes: UnificationNodes): Substitution? =
	emptyMap<UnificationTerm, Term>().makeTreeWithUnificationBase(nodes.iterator(), 0)

const val LIMIT = 4

private tailrec suspend fun Substitution.makeTreeWithUnificationBase(
	nodes: Iterator<UnificationNode>,
	index: Int
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
		return leaves.map { it.sequent }.toSet().tryUnification() ?: return makeTreeWithUnification(
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

private suspend fun Set<Sequent>.tryUnification(): Substitution? {
	val substitutionsList = this.map { it.getSubstitutions() }.sortedBy { it.size }.map { it.asReversed() }
	// TODO: 2022/12/06 この行は必要なのか
	if (substitutionsList.any { it.isEmpty() }) return null
	return getSubstitution(substitutionsList)
}

private fun getTermTacticInfo(
	sequent: Sequent, fmls: Set<Quantified>, id: Pair<Int, Int>
): Triple<TermTactic, Quantified, Term>? {
	for (tactic in TermTactic.values()) {
		val fml = tactic.getFml(sequent, fmls) ?: continue
		val availableVars = sequent.freeVars.ifEmpty { setOf(fml.bddVar) }
		val term = UnificationTerm(id, availableVars)
		return Triple(tactic, fml, term)
	}
	return null
}

/*
suspend fun Node.prove(
	printTimeInfo: Boolean = false,
	printUnificationInfo: Boolean = false,
	printTacticInfo: Boolean = false,
	printSequents: Boolean = false,
	unificationTermInstantiationMaxCountMax: Int = 4,
): ProofState {
	val start = System.currentTimeMillis()
	var count = 0
	var unificationTermInstantiationMaxCount = 0
	var unificationTermIndex = 0
	var totalUnificationTime = 0L

	val nodes = mutableListOf(this)
	val substitution = mutableMapOf<UnificationTerm, Term>()
	val allUnificationTerms = mutableSetOf<UnificationTerm>()
	val proofState: ProofState

	val nodesForUnification = mutableListOf<Node>()

	loop@ while (true) {
		count++
		if (printSequents) nodes.asReversed().forEach { println(it.sequentToBeApplied) }

		if (nodes.isEmpty()) {
			proofState = Provable
			break
		}

		val node = nodes.removeLast()

		val sequentToBeApplied = node.sequentToBeApplied

		//AXIOM
		if (AXIOM.canApply(sequentToBeApplied)) {
			if (printTacticInfo) println(">>> $AXIOM")
			continue@loop
		}

		//Unary Tactic
		for (tactic in UnaryTactic.values()) {
			val fml = tactic.getFml(sequentToBeApplied) ?: continue
			val applyData = UnaryTactic.ApplyData(tactic, fml)
			val sequent = applyData.applyTactic(sequentToBeApplied)
			val newNode = Node(sequent, node.siblingLabel)
			node.applyData = applyData
			node.child = newNode
			nodes.add(newNode)
			if (printTacticInfo) println(">>> $tactic")
			continue@loop
		}

		//Fresh Var Instantiation Tactic
		for (tactic in FreshVarTactic.values()) {
			val fml = tactic.getFml(sequentToBeApplied) ?: continue
			val freshVar = fml.bddVar.getFreshVar(sequentToBeApplied.freeVars)
			val applyData = FreshVarTactic.ApplyData(fml, freshVar)
			val sequent = applyData.applyTactic(sequentToBeApplied)
			val newNode = Node(sequent, node.siblingLabel)
			node.applyData = applyData
			node.child = newNode
			nodes.add(newNode)
			if (printTacticInfo) println(">>> $tactic")
			continue@loop
		}

		//Binary Tactic
		for (tactic in BinaryTactic.values()) {
			val fml = tactic.getFml(sequentToBeApplied) ?: continue
			val applyData = BinaryTactic.ApplyData(tactic, fml)
			val leftSequent = applyData.applyTactic(sequentToBeApplied).first
			val rightSequent = applyData.applyTactic(sequentToBeApplied).second
			val leftNode = Node(leftSequent, node.siblingLabel)
			val rightNode = Node(rightSequent, node.siblingLabel)
			node.applyData = applyData
			node.leftChild = leftNode
			node.rightChild = rightNode
			nodes.add(rightNode)
			nodes.add(leftNode)
			if (printTacticInfo) println(">>> $tactic")
			continue@loop
		}

		nodesForUnification.add(node)

		if (printTacticInfo) println(">>> move")

		if (nodes.isNotEmpty()) continue@loop

		if (unificationTermInstantiationMaxCount == 0 && nodesForUnification.any {
				it.sequentToBeApplied.assumptions.filterIsInstance<ALL>()
					.isEmpty() && it.sequentToBeApplied.conclusions.filterIsInstance<EXISTS>().isEmpty()
			}) {
			proofState = Unprovable
			break
		}

		if (nodesForUnification.groupBy { it.sequentToBeApplied }.values.any { it.size > 1 }) {
			println("duplicated!!!")
		}

		//try unification
		val siblingNodesList = nodesForUnification.groupBy { it.siblingLabel }.minus(null).values
		for (siblingNodes in siblingNodesList) {
			val siblingSubstitutionsList =
				siblingNodes.map { it.sequentToBeApplied }.map { it.getSubstitutions() }.sortedBy { it.size }
			if (siblingSubstitutionsList.any { it.isEmpty() }) continue
			val siblingSubstitution: Substitution?
			val unificationTime = measureTimeMillis {
				siblingSubstitution = getSubstitution(siblingSubstitutionsList)
			}
			if (printUnificationInfo) println("Unification try: $unificationTime ms")
			totalUnificationTime += unificationTime
			if (siblingSubstitution == null) continue
			substitution.putAll(siblingSubstitution)
			nodesForUnification.removeAll(siblingNodes.toSet())
			if (printUnificationInfo) {
				println("node size: ${siblingNodes.size}")
				siblingSubstitution.forEach { println(it) }
			}
		}

		//make new unification term
		while (true) {
			for (nodeForUnification in nodesForUnification.asReversed()) {
				val sequentToBeAppliedForUnification = nodeForUnification.sequentToBeApplied
				val fml = TermTactic.ALL_LEFT.getAvailableFml(
					sequentToBeAppliedForUnification, unificationTermInstantiationMaxCount
				) ?: TermTactic.EXISTS_RIGHT.getAvailableFml(
					sequentToBeAppliedForUnification, unificationTermInstantiationMaxCount
				) ?: continue
				val availableVars = sequentToBeAppliedForUnification.freeVars.ifEmpty { setOf(fml.bddVar) }
				val unificationTerm = UnificationTerm(unificationTermIndex, availableVars)
				val applyData = TermTactic.ApplyData(fml, unificationTerm)
				val sequent = applyData.applyTactic(sequentToBeAppliedForUnification)
				val siblingLabel = nodeForUnification.siblingLabel ?: unificationTerm.id
				val newNode = Node(sequent, siblingLabel)
				nodeForUnification.applyData = applyData
				nodeForUnification.child = newNode
				nodesForUnification.remove(nodeForUnification)
				nodes.add(newNode)
				unificationTermIndex++
				allUnificationTerms.add(unificationTerm)
				if (printTacticInfo) println(">>> ${applyData.tactic}")
				continue@loop
			}

			if (unificationTermInstantiationMaxCount == unificationTermInstantiationMaxCountMax) {
				proofState = UnificationTermInstantiationCountFail
				break@loop
			}

			if (nodes.isEmpty() && nodesForUnification.isNotEmpty()) {
				unificationTermInstantiationMaxCount++
				if (printTacticInfo) println(">>> unificationTermMax: $unificationTermInstantiationMaxCount")
			} else {
				break
			}

		}
	}

	print(proofState)

	val end = System.currentTimeMillis()
	val time = end - start

	if (proofState == Provable || proofState == Unprovable) {
		print(" Completed in ${time / 1000.0}s.")
	}

	if (printTimeInfo) {
		println()
		println("Completed in $time ms")
		println("unification time: $totalUnificationTime ms")
		println("other time: ${time - totalUnificationTime} ms")
		println("loop count: $count")
	}

	val completeProofTime = measureTimeMillis {
		val remainedSubstitution = allUnificationTerms.subtract(substitution.keys).associateWith { Dummy }
		val completeSubstitution = if (nodes.isEmpty()) {
			(substitution + remainedSubstitution).getCompleteSubstitution()
		} else {
			substitution.getCompleteSubstitution()
		}
		this.completeProof(completeSubstitution)
		if (printUnificationInfo) completeSubstitution.forEach { println(it) }
	}
	if (printTimeInfo) println("Proof formatted in $completeProofTime ms")

	if (printTimeInfo) println(">>>>>>>>>>>>> $time ms")

	return proofState

	/*
	if (nodes.isEmpty()) {
		print("Show Console Output? (y/n) >>> ")
		if (readLine()!! == "y") {
			println("-----------------------------------")
			rootNode.printProof()
			println("-----------------------------------")
		}
	}
	 */
}
*/
