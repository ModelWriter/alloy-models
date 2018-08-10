open util/relation

// Machines have states
abstract sig State { }

// Machine consists of states. Some states are terminal states. Some states are start states.
// Start and end states are disjoint
one sig Machine {
  start: some State,
  terminal: some State,
  transition: set (State set -> set State)
} {
  // Start and terminal states are disjoint
  no start & terminal
  // Start must be in the transition map
  start in (dom[transition] + ran[transition])
  // Terminal must be in the transition map
  terminal in (dom[transition] + ran[transition])
}

// Deterministic machines have at most one successor for each state
pred deterministic(m: Machine) { all s: State | lone m.transition[s] }

// Inverting the above predicate gives us non-deterministic machines
pred nonDeterministic(m: Machine) { !deterministic[m] }

// Unreachable states means we can't get to it from any start position
pred unreachable(m: Machine) { some s: State | s not in (^(m.transition)[m.start] + m.start) }

// If everything is reachable then that is just inverse of the above
pred reachable(m: Machine) { !unreachable[m] }

// Connected machine means for every pair of states there is an edge between them. This doesn't necessarily
// mean that every state is reachable because they could be unreachable from the start positions so if we
// want connected and every state to be reachable then we need to combine these two predicates
pred connected(m: Machine) {
  all disj s, s': State | s in ^(m.transition)[s'] || s' in ^(m.transition)[s]
}

// Deadlock means there is a reachable state with no outgoing edges
pred deadlock(m: Machine) {
  some s: State | s in ^(m.transition)[m.start] && no s': State | (s -> s') in m.transition
}

// It's unclear to me how to express the livelock condition because it basically means there is a state
// that is dangling outside of some loop so this is the best I can do
pred livelock(m: Machine) {
  one s: State {
    s in ^(m.transition)[m.start]
    no s': State | (s -> s') in m.transition
    all s': State - s | s' in ^(m.transition)[m.start]
  }
}
