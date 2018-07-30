// https://dev.to/davidk01/river-crossing-puzzle-with-alloy-415o
// The states are ordered so that we can talk about transitions
open util/ordering[State]

// The farmer, cabbage, goat, and wolf
abstract sig Entity { }
one sig Farmer, Cabbage, Goat, Wolf extends Entity { }

// If the farmer is not around then X - eats -> Y
let eats = (Goat -> Cabbage) + (Wolf -> Goat)

// State consists of a left and right entity sets modeling
// the banks of the river. The banks are disjoint and together
// they include all the entities
sig State {
  left, right: set Entity
} {
  // The combination of left and right must include all entities
  Entity = left + right
  // The left and right banks must be disjoint
  no left & right
  // NOTE: Try removing one of the conditions and running the model to see what
  // happens. It's actually interesting
}

// The entities on the bank are valid if the farmer is there or
// there are no eating combinations
pred validSubState(s: set Entity) {
  Farmer in s || no (s & s.eats)
}

// Valid state means both banks are valid
pred validState(s: State) {
  validSubState[s.left] && validSubState[s.right]
}

// Now we specify a valid transition from s to s' = s.next
pred transition(s: State, s': State) {
  // This is redundant but doesn't hurt to have it
  s' = s.next
  // The transition can move at most one item along with the Farmer. Since
  // we don't exclude e from being the Farmer it could be that the Farmer
  // is the only thing that moves from one bank to the next when e = Farmer
  one e: Entity {
    Farmer in s.left => {
      e in s.left && s'.right = s.right + Farmer + e
    } else {
      e in s.right && s'.left = s.left + Farmer + e
    }
  }
  // The pre and post states must be valid. Although technically if we start
  // with a valid state then we can never end up in an invalid state so checking
  // that the initial state is valid is redundant
  validState[s] && validState[s']
}

// We are done when everything is on the right bank
pred done(s: State) { Entity = s.right }

// We start with everything on the left bank
pred init(s: State) { Entity = s.left }

// Make sure the first and last state are what we want and that we can transition
// from the first state to the last state
run {
  init[first]
  all s: State, s': s.next | transition[s, s']
  done[last]
} for 8 State
