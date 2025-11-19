import Lean
import Qq

open Lean Qq PrettyPrinter

inductive Player
  | x
  | o
deriving ToExpr, BEq

inductive Cell
  | empty
  | filled (player : Player)
deriving ToExpr

namespace Cell
  declare_syntax_cat cell
  syntax "│ "      : cell
  syntax "│x"      : cell
  syntax "│o"      : cell

  meta def cellImpl : TSyntax `cell -> MacroM (TSyntax `term)
    | `(cell| │x) => `(.filled .x)
    | `(cell| │o) => `(.filled .o)
    | `(cell| │ ) => `(.empty)
    | _ => Macro.throwUnsupported
end Cell

structure Board where state : Vector Cell 9

namespace Board
  def empty : Board := Board.mk (Vector.replicate 9 .empty)

  instance : ToExpr Board where
    toExpr b :=
      let cells : Vector (Q(Cell)) 9 := b.state.map toExpr
      q(Board.mk #v[
        $(cells[0]), $(cells[1]), $(cells[2]),
        $(cells[3]), $(cells[4]), $(cells[5]),
        $(cells[6]), $(cells[7]), $(cells[8])
      ])

    toTypeExpr := q(Board)

  syntax:arg (name := board)
    "\n┌─┬─┬─┐\n"
    cell cell cell "│"
    "\n├─┼─┼─┤\n"
    cell cell cell "│"
    "\n├─┼─┼─┤\n"
    cell cell cell "│"
    "\n└─┴─┴─┘" : term

  @[macro board]
  meta def boardImpl : Macro
    | `(┌─┬─┬─┐
        $x1$x2$x3│
        ├─┼─┼─┤
        $x4$x5$x6│
        ├─┼─┼─┤
        $x7$x8$x9│
        └─┴─┴─┘) => do
          let cells ← #[x1, x2, x3, x4, x5, x6, x7, x8, x9].mapM Cell.cellImpl
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
end Board
