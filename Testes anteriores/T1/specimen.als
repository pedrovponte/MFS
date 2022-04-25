/*abstract sig A, B {}

one sig A1, A2, A3 extends A {}

one sig B1, B2 extends B {}*/

/*one sig R {
	r : A some -> lone B
} {
	r[A1] = r[A2] && r[A1] = B1
}*/

/*one sig R {
	r : A lone -> lone B
} {
	r.B1 = r.B2
}*/

/*one sig R {
	r : A some -> some B
} {
	r.B1 = r.B2
}*/

/*one sig R {
	r : A lone -> some B
} {}*/

/*one sig R {
	r : A lone -> B
} {
	r[A1] = r[A2] && r[A1] = B1 -- (A1, B1) and (A2, B1)
}*/

/*one sig R {
	r : A some -> lone B
} {
	r.B1 = r.B2
}*/ 

// run {} for 4


----------------------------------------------------------------------------------------------------------------------

/*sig Node {}

sig DAG {
	edge : Node -> Node
}

pred add (g, gf : DAG, e : Node -> Node) {
	one e
	gf.edge = g.edge + e
}

fact acyclic {
	all g : DAG | no n : Node | n in n.^(g.edge)
}

run add for 3 but 2 DAG*/


-----------------------------------------------------------------------------------------------------------------

/*sig Tree {
	root : lone Node
}

sig Node {
	left, right : lone Node,
	value : one Int
}

fun parent : Node -> Node {
	all n1, n2 : Node | n1 -> n2 in (left + right) => n1 in left.n2 or n1 in right.n2
}

pred wellFormedTree {
	all n : Node | some n.left + n.right => n.left != n.right
	no iden & ^parent
	all n : Node - Tree.root | one n.parent
	all n : Node | all lv : leftValues[n], rv : rightValues[n] | lv.value < n.value and rv.value > n.value
	all disj n1, n2 : Node | n1.value != n2.value
	all n : Node | (#(leftValues[n])).minus[#rightValues[n]] <= 1
}

fun leftValues [n : Node]: set Node {
	{nodesOnSubTree[n.left]}
}

fun rightValues [n : Node]: set Node {
	{nodesOnSubTree[n.right]}
}

fun nodesOnSubTree [n : Node]: set Node {
	n.*left + n.*right
}*/


---------------------------------------------------------------------------------------------------------------------

open util/ordering[Time]

sig Time {}

one sig List {
	head :  Node lone -> Time
}

sig Node {
	next : Node lone -> Time,
	value : Int
}

pred init [t : Time] {
	no List.head.t
}

fun nodeBefore[n: Node, t: Time] : Node{
	{(next.t).n}
}

fun nodesAfter[n: Node, t: Time]: set Node{
	{(n.*(next.t))}
}

pred delete[n: Node, t, t2: Time]{
	--pre-conditions
	n in nodesAfter[List.head.t, t]

	--post-conditions
	(n = List.head.t) implies (List.head.t2 = n.next.t) else (nodeBefore[n,t].next.t = n.next.t)
	nodesAfter[List.head.t2, t2] = nodesAfter[List.head.t, t] - n
	all disj n1, n2: Node - n | n1 in nodesAfter[n2, t] implies n1 in nodesAfter[n2, t2]
	
}

fact traces {
	all t : Time - last | let t2 = t.next | some n : Node | delete [n, t, t2] or insert [n]
}

pred insert [n : Node] {

}

fact sortedList {
	all disj n1, n2 : Node, t : Time | n1 in nodesAfter [n2, t] implies n1.value > n2.value
}

run {} for 6 but 4 Time






