open util/ordering[Node]

sig Node {
	succ: one Node,
	var inbox : set Node
}

fun Elected : set Node {
	{n : Node | once (n not in n.inbox and once (n in n.inbox))}
}

fact {
	// all nodes reachable from each node
	all n : Node | Node in n.^succ
	// at least one node
	some Node	
}

fact init {
	no inbox
}

fact events {
	always (
		stutter or
		some n : Node | initiate[n] or
		some n : Node, i : Node | process[n, i]
	)
}

pred initiate [n : Node] {
	/* // guards
	historically n.id not in n.outbox

	// effects
	n.outbox' = n.outbox + n.id
	
	// frame conditions
	all m : Node - n | m.outbox' = m.outbox
	all m : Node | m.inbox' = m.inbox
	Elected' = Elected*/

	// effects
	inbox' = inbox + n.succ -> n
}

pred process [n : Node, i : Node] {
	/*// guards
	i in n.inbox

	// effects
	inbox' = inbox - n -> i
	gt[i, n.id] -> outbox' = outbox + n -> i
			else outbox' = outbox
	i = n.id -> Elected' = Elected + n
		    else Elected' = Elected*/

	// guards
	i in n.inbox

	// effects
	inbox' = inbox - n -> i + n.succ -> (i & n.nexts)
}

/*pred nop {
	// guards
	no inbox and no outbox
	all n : Node | once initiate[n]

	// frame conditions
	outbox' = outbox
	inbox' = inbox
	Elected' = Elected
}*/

pred stutter {
	// frame conditions
	inbox' = inbox
}

pred fairness {
	all n : Node, i : Node {
		eventually always (historically n not in n.succ.inbox)
		implies
		always eventually initiate[n]

		eventually always (i in n.inbox)
		implies
		always eventually process[n, i]
	}
}

assert AtMostOneLeader {
	always (lone Elected)
}

check AtMostOneLeader for 3 but 20 steps

assert AtLeastOneLeader {
	fairness implies eventually (some Elected)
}

check AtLeastOneLeader for 3 but 20 steps

assert LeaderStaysLeader {
	always (all n : Elected | always n in Elected)
}

check LeaderStaysLeader for 3 but 20 steps

run example {} for exactly 4 Node
