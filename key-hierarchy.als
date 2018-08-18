some sig Key {
  // Keys can encrypt each other
  encrypts: set Key,
  // Keys can be stored in places in plaintext or encrypted form
  places: set (Property -> set Place)
} {
  // No key encrypts itself
  no (this & encrypts)
}

// Keys are stored in places
some sig Place { }

// Keys have properties associated with places
abstract sig Property { }
// For now a key can be encrypted or in plaintext form
one sig Encrypted extends Property { }
one sig Plaintext extends Property { }

// If a key is encrypted in some place then it is not stored in plaintext at same place
fact {
  all k: Key | no (k.places[Encrypted] & k.places[Plaintext])
}

// If a key encrypts another key then that key must appear encrypted somewhere
fact {
  all disj k, k': Key | (k' in k.encrypts) => some k'.places[Encrypted]
}

// If a key encrypts another key then it can not be stored in plaintext alongside it
fact {
  all disj k, k': Key | (k' in k.encrypts) => no (k.places[Plaintext] & k'.places[Property])
}

// So far we haven't ruled out any cyclic "hierarchies". Seen below we have
// k0 -> k2 -> k1 -> k0 which is a cycle. Theoretically there is nothing
// bad about this but it becomes bad when we introduce "people" into the mix
// that have access to "places" and can get a plaintext version of some key.
// If they have access to enough places then as soon as they have a plaintext
// version of a key they can decrypt anything in the cycle they have access to.
// So cycles inherently seem to be insecure if a person has enough access whereas
// a hierarchical configuration without cycles at least prevents being able to
// decrypt keys higher up the hierarchy even if the person has access to the
// higher place in the hierarchy
//┌────────┬────────┬─────────────────┐
//│this/Key│encrypts│places           │
//├────────┼────────┼──────────┬──────┤
//│Key⁰    │Key²    │Encrypted⁰│Place³│
//├────────┼────────┼──────────┼──────┤
//│Key¹    │Key⁰    │Encrypted⁰│Place³│
//│        ├────────┼──────────┼──────┤
//│        │        │Plaintext⁰│Place⁰│
//│        │        │          ├──────┤
//│        │        │          │Place¹│
//│        │        │          ├──────┤
//│        │        │          │Place²│
//├────────┼────────┼──────────┼──────┤
//│Key²    │Key¹    │Encrypted⁰│Place⁰│
//│        ├────────┤          ├──────┤
//│        │        │          │Place¹│
//│        │        │          ├──────┤
//│        │        │          │Place²│
//└────────┴────────┴──────────┴──────┘
