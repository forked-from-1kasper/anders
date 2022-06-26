open Language.Prelude
open Language.Spec
open Prettyprinter

type command =
  | Nope
  | Eval    of exp
  | Action  of string
  | Command of string * exp

type decl =
  | Def of string * exp option * exp
  | Data of string * data
  | Ext of string * exp * string
  | Axiom of string * exp

type line =
  | Import of string list
  | Plugin of string
  | Option of string * string
  | Decl of decl
  | Section of line list
  | Variables of tele list

type content = line list
type file = content

let moduleSep = '/'
let getPath = String.split_on_char moduleSep >> String.concat Filename.dir_sep

let showTeles xs =
  (if isEmpty xs then "" else " ") ^
  String.concat " " (List.map showTeleExp xs)

let showCtor (c : ctor) =
  Printf.sprintf "%s%s [%s]" c.name (showTeles c.params) (showSystem showExp c.boundary)

let showCtors cs = if isEmpty cs then "" else ":=\n| " ^ String.concat "\n| " (List.map showCtor cs)

let showData (x : string) (d : data) =
  Printf.sprintf "HIT %s%s : %s %s" x (showTeles d.params) (showExp d.kind) (showCtors d.ctors)

let showDecl : decl -> string = function
  | Def (p, Some exp1, exp2) -> Printf.sprintf "def %s : %s := %s" p (showExp exp1) (showExp exp2)
  | Def (p, None, exp) -> Printf.sprintf "def %s := %s" p (showExp exp)
  | Data (x, d) -> showData x d
  | Ext (p, t, v) -> Printf.sprintf "def %s : %s :=\nbegin%send" p (showExp t) v
  | Axiom (p, exp) -> Printf.sprintf "axiom %s : %s" p (showExp exp)

let rec showLine : line -> string = function
  | Import p -> Printf.sprintf "import %s" (String.concat " " p)
  | Plugin p -> Printf.sprintf "plugin %s" p
  | Option (opt, value) -> Printf.sprintf "option %s %s" opt value
  | Decl d -> showDecl d
  | Section xs -> Printf.sprintf "\nsection\n%s\nend\n" (String.concat "\n" (List.map showLine xs))
  | Variables xs -> Printf.sprintf "variables%s" (showTeles xs)

let showFile : file -> string = String.concat "\n" << List.map showLine
