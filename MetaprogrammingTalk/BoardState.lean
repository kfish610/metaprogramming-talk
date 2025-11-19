import Lean
import MetaprogrammingTalk.Board

open Board
open Lean

structure BoardState where
  board : Board
  turn  : Player
deriving ToExpr

namespace BoardState
  def initial : BoardState :=
    { board := Board.empty, turn := .x }

  def move (bs : BoardState) (pos : Fin 9) (_ : bs.board.state[pos] = .empty := by rfl)
    : BoardState :=
      let newCell := Cell.filled bs.turn
      let newBoard := Board.mk (bs.board.state.set pos newCell)
      let nextTurn := match bs.turn with
                      | .x => .o
                      | .o => .x
      { board := newBoard, turn := nextTurn }
end BoardState



--------------------- Problems ↓ ---------------------

-- Create a notation:
-- player <player>:
-- <board>
-- which creates a `BoardState` given a `Player` and `Board`.
-- Make sure it binds strongly enough that it can be used as an argument to a function,
-- and that it binds strongly to the board argument (default argument precedence is `min`).

-- [Your code here]

-- Create an operator:
-- <state> move <pos>
-- which applies `BoardState.move` to the given `BoardState` and position.
-- Make sure that it binds weakly enough to not interfere with `player`,
-- and with the correct associativity for chaining multiple moves.

-- [Your code here]



#eval
  -- player .o:
  ┌─┬─┬─┐
  │ │ │ │
  ├─┼─┼─┤
  │ │x│ │
  ├─┼─┼─┤
  │ │ │o│
  └─┴─┴─┘
  -- move 2
