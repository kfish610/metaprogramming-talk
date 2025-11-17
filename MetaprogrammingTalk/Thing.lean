import Lean
open Lean Elab Command Term Meta

declare_syntax_cat            expr
syntax ("true" <|> "false") : expr
syntax num                  : expr
syntax str                  : expr
syntax ident                : expr
syntax "(" expr ")"         : expr

declare_syntax_cat type
syntax "bool"    : type
syntax "int"     : type
syntax "string"  : type

declare_syntax_cat             stmt
syntax expr                  : stmt
syntax type ident " = " expr : stmt
syntax "return " expr        : stmt

declare_syntax_cat       seq
syntax stmt ";" (seq)? : seq

declare_syntax_cat      prog
syntax " end"          : prog
syntax type ident "(" (type ident),* ")" "{" seq "}" prog : prog

inductive Expression where
  | bool (v : Bool)
  | int (v : Int)
  | string (v : String)
  | identifier (name : String)

inductive Ty where
  | bool
  | int
  | string

inductive Sequence where
  | seq

inductive Program where
  | empty
  | function (ret : Ty) (name : String) (params : List (Ty × String)) (body : Sequence)

elab (name := begin) "begin" p:prog : term =>
    match p with
    | `(prog| end) => return .const ``Program.empty []
    | `(prog| $t:type $name:ident ($[$param_t:type $param_n:ident],*) { $content:seq } $rest:prog) => begin $rest

#check begin
  int main() {
    int a = 0;
    return a;
  }
end
