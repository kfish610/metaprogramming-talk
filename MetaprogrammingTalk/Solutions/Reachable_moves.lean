import Lean
import MetaprogrammingTalk.Solutions.BoardState

open Lean Elab Tactic Qq

inductive Reachable (res : BoardState) : BoardState → Nat → Prop
| eql : Reachable res res 0
| step {n init} (pos: Fin 9) (h : init.board.state[pos] = .empty := by rfl)
    : Reachable res (BoardState.move init pos h) n → Reachable res init (n + 1)



--------------------- Problems ↓ ---------------------

elab "moves" poses:num* : tactic =>
  withMainContext do
    for pos in poses do
      let goal ← getMainGoal

      let step ← `(Reachable.step $pos)
      let expr ← elabTerm step none (mayPostpone := true)

      let res ← goal.apply expr
      replaceMainGoal res
      Term.synthesizeSyntheticMVarsNoPostponing

    let goal ← getMainGoal

    let term ← `(Reachable.eql)
    let expr ← elabTerm term none (mayPostpone := true)

    let res ← goal.apply expr
    replaceMainGoal res
    Term.synthesizeSyntheticMVarsNoPostponing



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
    -- apply Reachable.step 4
    -- apply Reachable.step 8
    -- apply Reachable.step 2
    -- apply Reachable.eql
    moves 4 8 2
    -- reachable
