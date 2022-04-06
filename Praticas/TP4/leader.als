open util/ordering[Id]

sig Id {}

sig Node {
	succ: one Node,
	id: one Id,
	var inbox : set Id,
	var outbox : set Id
}

var sig Elected in Node {}

fact {
	// all nodes reachable from each node
	all n : Node | Node in n.^succ
	// at least one node
	some Node
	// ids are unique
	all i : Id | lone id.i	
}

fact init {
	no inbox
	no outbox
	no Elected
}

fact events {
	always (
		stutter or
		some n : Node | initiate[n] or
		some n : Node, i : Id | send[n, i] or
		some n : Node, i : Id | process[n, i]
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

	// guards
	historically n.id not in n.outbox

	// effects
	outbox' = outbox + n -> n.id

	// frame conditions
	inbox' = inbox
	Elected' = Elected
}

pred send [n : Node, i : Id] {
	//guards
	i in n.outbox

	// effects
	outbox' = outbox - n -> i
	inbox' = inbox + n.succ -> i

	// frame conditions
	Elected' = Elected
}

pred process [n : Node, i : Id] {
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
	inbox' = inbox - n -> i
	outbox' = outbox + n -> (i & n.id.nexts)
	Elected' = Elected + (n & id.i)
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
	outbox' = outbox
	inbox' = inbox
	Elected' = Elected	
}

assert AtMostOneLeader {
	always (lone Elected)
}

check AtMostOneLeader for 3 but 20 steps

assert AtLeastOneLeader {
	eventually (some Elected)
}

check AtLeastOneLeader for 3 but 20 steps

assert LeaderStaysLeader {
	always (all n : Elected | always n in Elected)
}

check LeaderStaysLeader for 3 but 20 steps

run example {}
