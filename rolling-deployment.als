open util/ordering[State]

// We'll be working with machines
some sig Machine { }

// State is defined by the aggregate state of the machines
sig State {
  old: set Machine,
  new: set Machine,
  undefined: set Machine
} {
  // The state must have all the machines at all times
  Machine = old + new + undefined
  // There must always be at least 1 machine in the old or new states
  some (old + new)
  // The machines can't be in multiple states at once
  disj[old, new, undefined]
}

// How do we transition from one valid state to another when we
// are performing a rolling deployment? This predicate spells out
// those details
pred transition(s, s': State) {
  some s.undefined => {
    // If there is some machine in an undefined state then in the next state
    // it must be in a defined state
    one m: s.undefined | m in (s'.old + s'.new)
    // The previous state machines must be preserved
    s.old in s'.old
    s.new in s'.new
  } else {
    // There are no machines in an undefined state so pick one from the defined
    // state and move it to an undefined state
    one m: (s.old + s.new) {
      m in s'.undefined
      // All other machines except m must preserve their state
      m in s.old => { s'.new = s.new } else { s'.old = s.old }
    }
  }
}

run {
  first.old = Machine
  last.new = Machine
  all s: State, s': s.next | transition[s, s']
} for 5 State, 2 Machine
