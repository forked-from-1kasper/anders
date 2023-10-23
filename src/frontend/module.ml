open Language.Prelude
open Language.Spec
open Prettyprinter

type syntax =
  | Atom of string
  | Node of char * syntax list

type command =
  | Nope
  | Expr    of exp
  | Action  of string
  | Command of string * exp

type decl =
  | Def   of string * exp option * exp
  | Ext   of string * exp * string
  | Axiom of string * exp

type associativity = Left | Right | Neither
type operator = Infix of associativity | Prefix | Postfix

type line =
  | Operator       of operator * float * string list
  | Import         of string list
  | Plugin         of string
  | Option         of string * string
  | Opaque         of string
  | Variables      of tele list
  | Macrovariables of string list
  | Token          of string list
  | Macro          of bool * syntax * syntax
  | Macroexpand    of syntax
  | Decl           of decl
  | Infer          of exp
  | Eval           of exp
  | Section | End | Skip | Eof

type content = line list
type file = content

let moduleSep = '/'
let getPath = String.concat Filename.dir_sep % String.split_on_char moduleSep

let isBracket ch = ch = '(' || ch = '[' || ch = '<'

let enclosing = function
  | '(' -> ')'
  | '[' -> ']'
  | '<' -> '>'
  | ch  -> ch

let rec showStx = function
  | Node (c, xs) -> Printf.sprintf "%c%s%c" c (showStxs xs) (enclosing c)
  | Atom s       -> s
and showStxs xs = String.concat " " (List.map showStx xs)

let atom s = Atom s
let paren es = Node ('(', es)

let showMany fn xs =
  (if isEmpty xs then "" else " ") ^
  String.concat " " (List.map fn xs)

let showTeles = showMany showTeleExp

let showDecl = function
  | Def (p, Some exp1, exp2) -> Printf.sprintf "def %s : %s := %s" p (showExp exp1) (showExp exp2)
  | Def (p, None, exp) -> Printf.sprintf "def %s := %s" p (showExp exp)
  | Ext (p, t, v) -> Printf.sprintf "def %s : %s :=\nbegin%send" p (showExp t) v
  | Axiom (p, exp) -> Printf.sprintf "axiom %s : %s" p (showExp exp)

let showOperator = function
  | Infix Left    -> "infixl"
  | Infix Right   -> "infixr"
  | Infix Neither -> "infix"
  | Prefix        -> "prefix"
  | Postfix       -> "postfix"

let showUnsafeAttr b = if b then "unsafe " else ""

let showLine = function
  | Operator (op, prec, is) -> Printf.sprintf "%s %f %s" (showOperator op) prec (String.concat " " is)
  | Import p -> Printf.sprintf "import %s" (String.concat " " p)
  | Plugin p -> Printf.sprintf "plugin %s" p
  | Option (opt, value) -> Printf.sprintf "option %s %s" opt value
  | Decl d -> showDecl d
  | Opaque x -> Printf.sprintf "opaque %s" x
  | Section -> "section" | End -> "end"
  | Variables xs -> Printf.sprintf "variables%s" (showTeles xs)
  | Macrovariables is -> Printf.sprintf "macrovariables %s" (String.concat " " is)
  | Token is -> Printf.sprintf "token %s" (String.concat " " is)
  | Macro (b, e1, e2) -> Printf.sprintf "%smacro %s :=\n%s" (showUnsafeAttr b) (showStx e1) (showStx e2)
  | Macroexpand stx -> Printf.sprintf "#macroexpand %s" (showStx stx)
  | Infer e -> Printf.sprintf "#infer %s" (showExp e)
  | Eval e -> Printf.sprintf "#eval %s" (showExp e)
  | Skip | Eof -> ""

let showFile : file -> string = String.concat "\n" % List.map showLine
