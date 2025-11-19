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

notation:arg "player" p ":" b:arg => BoardState.mk b p

infixl:min "move" => BoardState.move



#eval
  player .o:
  ┌─┬─┬─┐
  │ │ │ │
  ├─┼─┼─┤
  │ │x│ │
  ├─┼─┼─┤
  │ │ │o│
  └─┴─┴─┘
  move 2
