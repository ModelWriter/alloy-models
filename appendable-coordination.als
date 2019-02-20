// We will be dealing with sequences of events and states indexed by time
open util/ordering[Time]

// Events and states will be ordered/indexed by Time
some sig Time { }

// An event happens at a point in time and is related to some nodes
abstract sig Event {
  nodes: Node set -> Time
} {
  // All events must happen before we run out of time
  no nodes.last
}

// There are 2 events sent/created by nodes: Reset, Register
some sig Register extends Event { }
some sig Reset extends Event { }

some sig Node { } {
  // The reset event must happen only once
  one (Reset.nodes[this])
  // Register and reset events don't overlap
  no (Reset.nodes[this] & Register.nodes[this])
  // All register events must happen after the one reset event
  Register.nodes[this] in Reset.nodes[this].nexts
  // There must be at least one point in time where the node registers.
  // This means our nodes are "live"
  some Register.nodes[this]
}

// The state consists of a set of registered nodes at some point in time
some sig State {
  time: Time,
  registrants: Node set -> time
}

// We have 1-1 mapping between State and Time
fact {
  time in State one -> one Time
}

// The transition relations that specifies what happens to the state at
// successive points in time given what events are happening at the
// current time.
pred transition(t, t': Time) {
  some (Reset.nodes.t) => {
    // Reset event clears the registrants at the next point in time
    no State.registrants.t'
  } else {
    // Otherwise there are no reset events at this time so register the nodes
    State.registrants.t' = State.registrants.t + Register.nodes.t
  }
}

fact {
  no State.registrants.first
  all t: Time, t': t.next | transition[t, t']
}

//check {
//  Node in State.registrants.last
//} for exactly 2 Node, 5 Time, 5 State, 5 Event

// Make sure the states are consistent
run {
  Node in State.registrants.last
} for exactly 2 Node, 3 Time, 3 State, 3 Event
