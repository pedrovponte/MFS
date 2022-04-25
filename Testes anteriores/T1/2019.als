open util/ordering[ProjectState]

sig Task {}

sig Worker {}

sig Project {
	tasks : some Task, -- a project has one or more tasks
	workers : some Worker, -- a project has one or more workers
	dependencies : tasks -> tasks -- pairs (t1,t2), meaning that t1 cannot start before t2 finishes
} {
	-- dependencies are acyclic
	no ^dependencies & iden
}

sig ProjectState {
	project : Project,
	finished : set Task,
	ongoing : Task lone -> lone Worker -- pairs (t,w), meaning that t is being carried out by w
} {
	-- a) finished and ongoing tasks must belong to the project
	finished + ongoing.Worker in project.tasks

	-- b) finished and ongoing tasks must be disjoint
	no finished & ongoing.Worker

	-- c) dependencies of ongoing tasks must be finished
	no project.dependencies[ongoing.Worker] & finished

	-- d) workers of ongoing tasks must belong to the project
	Task.ongoing in project.workers
}

-- Task t is started by worker w, changing project state from s to s'.
pred startTask [s, sf : ProjectState, t : Task, w : Worker] {
	-- pre-conditions
	t in s.project.tasks -- a)
	t not in s.finished + s.ongoing.Worker -- b)
	Task -> w not in s.ongoing -- c)
	s.project.dependencies[t] in s.finished -- d)

	-- post-conditions
	sf.project = s.project and sf.finished = s.finished
	sf.ongoing = s.ongoing + t -> w
}

pred finishTask [s, sf : ProjectState, t : Task, w : Worker] {
	-- pre and post-conditions
	t -> w in s.ongoing -- a)
	sf.project = s.project -- b)
	sf.finished = s.finished + t -- c)
	sf.ongoing = t <: s.ongoing :> w -- d)
}

-- The ordered instances of ProjectState must represent a valid execution of a project
fact validOrdering {
	-- a) in the first state, there are no finished tasks
	no first.finished
	
	-- b) in the first state, there are no ongoing tasks
	no first.ongoing

	-- c) consecutive states are related by startTask or finishTask
	all s : ProjectState, sf  : s.next | some t : Task, w : Worker | startTask [s, sf, t, w] or finishTask [s, sf, t, w]

	-- d) in the last state, all tasks are finished
	all last.finished
}

