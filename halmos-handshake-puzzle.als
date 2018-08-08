// Don't know why ordering the couples speeds up the solution so much
open util/ordering[Couple]

// There are people and they can shake hands with other people
some sig Person { handshake: set Person }

// Alice and Bob are people
one sig Alice, Bob extends Person { }

// Couples consist of 2 people and each couple consists of disjoint people
abstract sig Couple { a: Person, b: Person } {
  // No one is coupled to themselves
  a != b
  // All the couples are disjoint
  all c': Couple - this | no (a + b) & c'.(@a + @b)
  // Couples don't shake hands with each other
  (a -> b) not in handshake
}

// First couple C1 = Alice and Bob
one sig C1 extends Couple { } {
  a = Alice
  b = Bob
}

// Handshaking is symmetric but not reflexive
fact {
  no iden & handshake
  handshake = ~handshake
}

// Rest of the couples
one sig C2, C3, C4, C5 extends Couple { }

// Statement of the puzzle
pred puzzle() { all disj p, p': (Person - Alice) | #p.handshake != #p'.handshake }

run puzzle for 10 Person, 5 Int
