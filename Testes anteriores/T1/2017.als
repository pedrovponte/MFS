// enum Ocean {Artic, Atlantic, Indian, Pacific, Southern}

/*abstract sig Ocean{} 
one sig Artic, Atlantic, Indian, Pacific, Southern extends Ocean{}*/

/*one sig Ocean{} 
sig Artic, Atlantic, Indian, Pacific, Southern extends Ocean{}*/

/*sig Ocean{}{#Ocean = 5}
one sig Artic, Atlantic, Indian, Pacific, Southern extends Ocean{}*/

------------------------------------------------------------------------------------------

/*sig Country {
	neighbors: set Country - this
}*/

/*sig Country {
	neighbors: set Country
} {
	this not in neighbors
}*/

/*sig Country {
	neighbors: set Country
} 

fact {no neighbors & iden}*/

/*sig Country {
	neighbors: disj set Country
}*/

-----------------------------------------------------------------------------------------

open util/ordering[Placement]

sig Place {}

sig Network {
    places : set Place,
    connections : places -> places
} {
    
    -- Connections are bidirectional: if there is a connection from X to Y, then there is
    -- also a connection from Y to X, i.e., the ‘connections’ relation is symmetric.

    connections = ~connections

    -- A place cannot be connected to itself, i.e., the 'connections' relation is anti-reflexive.

    no connections & iden

    -- The network must be connected, that is, there must exist a path between
    -- any two places in the network.

    all p1, p2 : places | p2 in p1.*connections 
}

sig Object {}

sig Placement {
	network : Network,
	objects : set Object,
	-- positions relates objects with places, such that each object has exactly
	-- one place and each place has at most one object
	positions : objects lone -> one Place
} {
	-- The places where objects are positioned must belong to the network.
	positions[objects] in network.places
}

-- Moves an object o to an adjacent place p in a placement t,
-- resulting in a new placement t'.
pred moveObject[t : Placement, o : Object, p : Place, tf : Placement] {
	-- Pre-conditions:
	-- the object (o) must exist in the initial placement (t)
	o in t.objects
	-- the target place (p) must be unnocupied in the initial placement (t)
	no t.positions.p
	-- the target place (p) must be adjacent to the initial place of the object (o)
	t.positions[o] -> p in t.network.connections

	-- post-conditions (one per field of t’)
	tf.network = t.network
	tf.objects = t.objects
	tf.positions = t.positions + o -> p
}

fact {
	all t : Placement | some o : Object, p : Place | moveObject[t, o, p, t.next]
}

one sig x, y, z, w extends Place {}

one sig n extends Network {} {
	places = x + y + z + w
	connections = x->y + y->x + y->z + z->y + y->w + w->y
}

one sig a, b extends Object {}

one sig initial extends Placement {} {
	network = n
	objects = a + b
	positions = a->x + b->y
}

-- Swap objects in a minimal number of steps (6 moves, 7 Placements)
run success {
	first = initial and last.positions = a->y + b->x
} for 7 but exactly 1 Network, 2 Object, 4 Place

-- Trying to swap objects in fewer steps should fail
run failure {
	first = initial and last.positions = a->y + b->x
} for 6 but exactly 1 Network, 2 Object, 4 Place

