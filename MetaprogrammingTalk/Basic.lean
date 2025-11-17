import Lean
import Qq
open Lean Elab Command Term Meta PrettyPrinter Qq

inductive Player
| x
| o

inductive Cell
| empty
| filled (player : Player)
deriving Inhabited

structure Board where state : Vector Cell 9

def Board.empty : Board := Board.mk (Vector.replicate 9 .empty)

instance : ToExpr Board where
  toExpr b :=
    let x1 := b.state[0]!
    let x2 := b.state[1]!
    let x3 := b.state[2]!
    let x4 := b.state[3]!
    let x5 := b.state[4]!
    let x6 := b.state[5]!
    let x7 := b.state[6]!
    let x8 := b.state[7]!
    let x9 := b.state[8]!
    `(Board.mk #v[$x1,$x2,$x3,$x4,$x5,$x6,$x7,$x8,$x9])

structure BoardState where
  board : Board
  turn  : Player

def BoardState.initial : BoardState :=
  { board := Board.empty, turn := .x }

def BoardState.move (bs : BoardState) (pos : Fin 9) : Option BoardState :=
  match bs.board.state.get pos with
  | .empty =>
      let newCell := Cell.filled bs.turn
      let newBoard := Board.mk (bs.board.state.set pos newCell)
      let nextTurn := match bs.turn with
                      | .x => .o
                      | .o => .x
      some { board := newBoard, turn := nextTurn }
  | .filled _ => none

declare_syntax_cat cell
syntax "│ "      : cell
syntax "│x"      : cell
syntax "│o"      : cell

syntax (name := board)
"\n┌─┬─┬─┐\n"
cell cell cell "│"
"\n├─┼─┼─┤\n"
cell cell cell "│"
"\n├─┼─┼─┤\n"
cell cell cell "│"
"\n└─┴─┴─┘" : term

meta def cellImpl : TSyntax `cell -> MacroM (TSyntax `term)
| `(cell| │x) => `(.filled .x)
| `(cell| │o) => `(.filled .o)
| `(cell| │ ) => `(.empty)
| _ => Macro.throwUnsupported

@[macro board]
meta def boardImpl : Macro
  | `(┌─┬─┬─┐
      $x1$x2$x3│
      ├─┼─┼─┤
      $x4$x5$x6│
      ├─┼─┼─┤
      $x7$x8$x9│
      └─┴─┴─┘) => do
        let cells ← #[x1, x2, x3, x4, x5, x6, x7, x8, x9].mapM cellImpl
        `(Board.mk #v[$cells,*])
  | _ => Macro.throwUnsupported

meta def unexpandCell : TSyntax `term → UnexpandM (TSyntax `cell)
  | `(Cell.filled Player.x) => `(cell| │x)
  | `(Cell.filled Player.o) => `(cell| │o)
  | `(Cell.empty)           => `(cell| │ )
  | _ => throw ()

@[app_unexpander Board.mk]
meta def unexpandMk : Unexpander
  | `($_ #v[ $xs,* ]) => do
      let cells ← xs.getElems.mapM unexpandCell
      `(┌─┬─┬─┐
        $(cells[0]!)$(cells[1]!)$(cells[2]!)│
        ├─┼─┼─┤
        $(cells[3]!)$(cells[4]!)$(cells[5]!)│
        ├─┼─┼─┤
        $(cells[6]!)$(cells[7]!)$(cells[8]!)│
        └─┴─┴─┘)
  | _ => throw ()


#check ({
  board :=  ┌─┬─┬─┐
            │x│x│x│
            ├─┼─┼─┤
            │ │x│o│
            ├─┼─┼─┤
            │ │ │o│
            └─┴─┴─┘,
  turn := Player.o
} : BoardState).move 1
