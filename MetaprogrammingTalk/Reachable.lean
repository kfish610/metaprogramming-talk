import MetaprogrammingTalk.BoardState

open Lean Elab Tactic Qq

inductive Reachable (res : BoardState) : BoardState → Nat → Prop
| eql : Reachable res res 0
| step {n init} (pos: Fin 9) (h : init.board.state[pos] = .empty := by rfl)
    : Reachable res (BoardState.move init pos h) n → Reachable res init (n + 1)



--------------------- Problems ↓ ---------------------

elab "moves" /-argument parser here-/ : tactic => sorry

elab "reachable" : tactic => sorry



example : Reachable
  player .o:
  ┌─┬─┬─┐
  │ │ │x│
  ├─┼─┼─┤
  │ │x│ │
  ├─┼─┼─┤
  │ │ │o│
  └─┴─┴─┘
  BoardState.initial 3 := by
    apply Reachable.step 4
    apply Reachable.step 8
    apply Reachable.step 2
    apply Reachable.eql
    -- moves 4 8 2
    -- reachable
