open util/ordering[State]

// We'll be working with machines
some sig Machine { }

// State is defined by the aggregate state of the machines
sig State {
  old: set Machine,
  new: set Machine,
  undefined: set Machine
} {
  // Machines can't randomly disappear
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
  // New machine stay where they are. This essentially pins new machines
  s.new in s'.new
  // Old machines can't magically become new machines
  no (s.old & s'.new)
  // Now we think about what to do with machines in the old and undefined states
  some s.undefined => {
    // If there are machines in an undefined state then they must move to the new state
    // but they don't all have to move together
    some (s.undefined & s'.new)
  } else {
    // There are no machines in an undefined state so pick some from old ones
    // and move them to an undefined state
    some (s.old & s'.undefined)
  }
}

run {
  first.old = Machine
  last.new = Machine
  all s: State, s': s.next | transition[s, s']
} for 4 State, exactly 3 Machine
