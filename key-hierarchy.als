abstract sig Key {
  // Keys can encrypt each other
  encrypts: set Key,
  // Keys can be stored in places in plaintext or encrypted form
  places: set (Property -> set Place)
} {
  // No key encrypts itself
  no (this & encrypts)
}

// Keys are stored in places
abstract sig Place { }

// Keys have properties that are associated with a place the key is at
enum Property { Encrypted, Plaintext }

// If a key is encrypted in some place then it is not stored in plaintext at same place
fact {
  all k: Key | no (k.places[Encrypted] & k.places[Plaintext])
}

// If a key encrypts another key then that key must appear encrypted somewhere
fact {
  all k: Key, k': k.encrypts | some k'.places[Encrypted]
}

// If a key encrypts another key then it can not be stored in plaintext alongside it
fact {
  all k: Key, k': k.encrypts | no (k.places[Plaintext] & k'.places[Property])
}

// So now I'm going to add people that have access to places
abstract sig Person {
  // Person has access to places
  access: set Place,
  // They can also have access to keys
  keys: set Key
} {
  // If a person has access to a place then they have access to plaintext keys in that place
  all k: Key | Plaintext in k.places.access => k in keys
}

// Now some more complicated interactions between keys, people, and places. If a person
// has access to a key and that key encrypts another key that is placed somewhere
// the person has access to then that person also has access to that key
fact {
  all p: Person, k: p.keys, k': k.encrypts {
    some k'.places[Property] & p.access => k' in p.keys
  }
}

// Every key must be owned by a person or be in some place
fact {
  all k: Key | (some k.places || some p: Person | k in p.keys)
}

// Now let's spell out some concrete implementations

// These are some places we will be storing keys
one sig Git, Lastpass, Production extends Place { }

// These are some people that will have access to keys and places
one sig InfraPerson, DevPerson extends Person { }

// Now let's specify some keys and their relationships
one sig DevKey, InfraKey,
  InfraKeyPassword, DevKeyPassword,
  LastpassPassword extends Key { }

// Facts about InfraPerson
fact {
  // Infra person has all the infra keys and passwords
  (InfraKey + InfraKeyPassword + LastpassPassword) in InfraPerson.keys
  // InfraPerson can access everything
  Place = InfraPerson.access
}

// Facts about DevPerson
fact {
  // Dev person can access the dev key password
  DevKeyPassword in DevPerson.keys
  // They can access Git and Production
  (Git + Production) = DevPerson.access
}

// Which key encrypts which other key
fact {
  // The infra key password encrypts infra key
  InfraKey = InfraKeyPassword.encrypts
  // Lastpass encrypts infra key password and infra key
  (InfraKeyPassword + InfraKey) = LastpassPassword.encrypts
  // Dev key password encrypts dev key
  DevKey = DevKeyPassword.encrypts
  // Infra key encrypts dev key password
  DevKeyPassword = InfraKey.encrypts
}

// Now we specify where each key is stored
fact {
  // Infra keys are stored in lastpass
  (Encrypted -> Lastpass) = InfraKeyPassword.places
  (Encrypted -> Lastpass) = InfraKey.places
  // Dev keys are stored in git and one of the keys is stored in production in plaintext
  (Encrypted -> Git) = DevKeyPassword.places
  (Encrypted -> Git + Plaintext -> Production) = DevKey.places
}

// Now we have to specify a few more facts about the keys to rule out extraneous models
fact {
  // Dev key does not encrypt any other keys
  no DevKey.encrypts
  // Dev person does not have access to infra keys
  no (InfraKey + InfraKeyPassword + LastpassPassword) & DevPerson.keys
  // Lastpass password is not stored anywhere and is just owned by the infra person
  no LastpassPassword.places
}
