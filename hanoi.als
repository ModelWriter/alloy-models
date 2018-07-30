// https://dev.to/davidk01/solving-tower-of-hanoi-with-alloy-5gn9
// Tower of Hanoi: https://en.wikipedia.org/wiki/Tower_of_Hanoi
open util/ordering[Ring]
open util/ordering[TowerPosition]
open util/ordering[State]

// We are going to work with rings. Rings are ordered by size that is
// why we opened ordering for Ring
sig Ring { }

// Rings appear on towers at specific tower positions so we need the positions
// and the positions must respect the size ordering of the rings so that's why
// we also opened ordering for TowerPosition
sig TowerPosition { }

// Tower maps positions to rings and must preserve ordering and have no gaps
sig Tower {
  rings: set (TowerPosition -> lone Ring)
} {
  let currentPositions = rings.Ring {
    // Verify that there are no gaps because rings don't float on air
    all position: currentPositions | position.prev in currentPositions
    // Verify that rings are in ascending order
    all position: currentPositions, positions': position.nexts {
      positions'.rings in position.rings.nexts
    }
  }
}

// A state consists of (l)eft, (m)iddle, (r)ight tower
sig State {
  l, m, r: one Tower
} {
  // Valid states must include all the rings/disks
  Ring in (l + m + r).rings[TowerPosition]
  // Towers must be disjoint
  let lRings = l.rings[TowerPosition], mRings = m.rings[TowerPosition],
    rRings = r.rings[TowerPosition] {
      no lRings & (mRings + rRings) + mRings & rRings
  }
}

// True only if `r` is a top ring in `t`. Verified in the evaluator as valid
pred topRingInTower(t: Tower, r: Ring) {
  let ringPosition = t.rings.r, nextPosition = ringPosition.next {
    // There is a ring position and there is nothing higher
    (one ringPosition && (no nextPosition || no t.rings[nextPosition]))
  }
}

// All the conditions are required for sensible results. Try removing
// some of the conditions and seeing what happens.
// Two towers `t1`, `t2` are compatible if we can put `r` on top of `t1` and get `t2`
pred ringTowerCompatibility(r: Ring, t1, t2: Tower) {
  // The base case is that `t1` is the empty tower
  no t1.rings => {
    // Then `r` must be the only ring in `t2`
    one t2.rings && one t2.rings.r
  } else { // Otherwise `t1` is not empty
    // `r` must be a new ring
    no t1.rings.r
    // `r` must be a top ring in `t2`
    topRingInTower[t2, r]
    // The ring ordering for `t1` must be in `t2`
    t1.rings in t2.rings
    // `t2` must differ from `t1` by only 1 ring
    t2.rings[TowerPosition] - t1.rings[TowerPosition] = r
  }
}

// Two towers are compatible if they're equal or they are ring compatible
pred towerCompatibility(t1, t2: Tower) {
  t1 = t2 ||
    one r: Ring {
      ringTowerCompatibility[r, t1, t2] ||
      ringTowerCompatibility[r, t2, t1]
    }
}

// True only if `ring` is a top ring in one of the "pegs" of `s`
pred topRing(s: State, ring: Ring) {
  topRingInTower[s.l, ring] ||
  topRingInTower[s.m, ring] ||
  topRingInTower[s.r, ring]
}

// The transition relation basically says two consecutive states
// `s` and `s'` are related if their corresponding towers are compatible.
// It turns out that when all the towers in both states are compatible they
// differ by a single ring/disk move.
pred transition(s, s': State) {
  s' = s.next
  // We can only move 1 ring at a time
  // The transition must preserve compatibility
  towerCompatibility[s.l, s'.l]
  towerCompatibility[s.m, s'.m]
  towerCompatibility[s.r, s'.r]
}

// We will want unequal states to see what is going on
pred equalState(s, s': State) {
  s.l = s'.l && s.m = s'.m && s.r = s'.r
}

// Different towers must have different orderings
fact { all disj t, t': Tower | t.rings != t'.rings }

// Starting state must have everything on the left tower
fact {
  let firstState = first & State {
    Ring in firstState.l.rings[TowerPosition]
  }
}

// Last state must have everything on the right tower
fact {
  let lastState = last & State {
    Ring in lastState.r.rings[TowerPosition]
  }
}

run {
  // Relate the states by transition
  all s: State, s': s.next | transition[s, s']
  // Make sure the states are different
  all disj s, s': State | !equalState[s, s']
} for exactly 3 Ring, exactly 3 TowerPosition,
  exactly 8 Tower, exactly 8 State
