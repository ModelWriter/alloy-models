// We are going to trace through states
open util/ordering[State]

// Rows of the board
enum Row { R1, R2, R3 }

// Columns of the board
enum Col { C1, C2, C3 }

// Players: X, O
enum Player { X, O }

// Board maps positions to marks by a player
sig Board { cells: Row -> Col -> Player } { no cells.X & cells.O }

// State consists of a board and a player that is allowed to make the next move
sig State { board: Board, player: Player }

// Specification for a valid transition
pred transition(s, s': State) {
  let p = s.player, p' = s'.player,
    scells = s.board.cells, scells' = s'.board.cells {
      // Players must alternate
      p != p'
      // Previous cells must be preserved
      scells in scells'
      // Previous players cells must be preserved
      scells.p' = scells'.p'
      // Current player must make 1 move
      one (scells' - scells).p
  }
}

// Initial state consists of an empty board
pred init(s: State) {
  no s.board.cells
}

// Player is a winner if they occupy 3 consecutive positions or diagonals
pred winner(b: Board, p: Player) {
  let positions = b.cells.p {
    // Player occupies a column
    (some c: Col | Row = positions.c) ||
      // Player occupies a row
      (some r: Row | Col = positions[r]) ||
      // Player occupies off diagonal
      (R1 -> C1 + R2 -> C2 + R3 -> C3) in positions ||
      // Player occupies diagonal
      (R3 -> C1 + R2 -> C2 + R1 -> C3) in positions
  }
}

run {
  init[first]
  all s: State, s': s.next | transition[s, s']
  winner[last.board, X]
} for 6 State, 6 Board
