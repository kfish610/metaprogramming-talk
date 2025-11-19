import Lean
import Batteries
import MetaprogrammingTalk.Solutions.BoardState

open Lean Elab Tactic Qq

inductive Reachable (res : BoardState) : BoardState → Nat → Prop
| eql : Reachable res res 0
| step {n init} (pos: Fin 9) (h : init.board.state[pos] = .empty := by rfl)
    : Reachable res (BoardState.move init pos h) n → Reachable res init (n + 1)



--------------------- Problems ↓ ---------------------

meta def exprToList (e : Q(List Cell)) : MetaM (List Cell) := do
  match e with
  | ~q([]) => return []
  | ~q($head :: $tail) =>
    let rest ← exprToList tail
    match head with
    | ~q(Cell.filled .x) => return Cell.filled .x :: rest
    | ~q(Cell.filled .o) => return Cell.filled .o :: rest
    | ~q(Cell.empty)     => return Cell.empty :: rest
    | _ => throwError "not a Cell"

elab "reachable" : tactic =>
  withMainContext do
    let goal ← getMainGoal
    let goalType : Q(Prop) ← getMainTarget
    match goalType with
    | ~q(Reachable (BoardState.mk (Board.mk (Vector.mk (Array.mk $list) _)) $p) BoardState.initial _) =>
        let cells ← exprToList list
        let pl ← match p with
          | ~q(Player.x) => return Player.x
          | ~q(Player.o) => return Player.o
          | _ => Meta.throwTacticEx `reachable goal m!"Expected Player, got {p.dbgToString}"

        let (xs, os) := (cells.zip (List.range 9)).foldl (fun (xs, os) (c, idx) =>
          match c with
          | .filled .x => (idx :: xs, os)
          | .filled .o => (xs, idx :: os)
          | .empty     => (xs, os)
        ) ([], [])

        if pl == .x && xs.length == os.length || pl == .o && xs.length == os.length + 1 then
          let poses := [xs, os].transpose.flatten.map Syntax.mkNatLit
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
        else
          Meta.throwTacticEx `reachable goal m!"Board is not reachable since the number of moves by each player is not balanced, xs = {xs.length}, os = {os.length}"
    | _ => Meta.throwTacticEx `reachable goal m!"Tactic 'reachable' only works on goals of the form 'Reachable _ BoardState.initial _', got {goalType.dbgToString}"



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
    -- moves 4 8 2
    reachable
