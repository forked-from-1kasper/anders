open Prettyprinter
open Gen

let traceHole v gma = print_string ("\nHole:\n\n" ^ showGamma gma ^ "\n" ^ String.make 80 '-' ^ "\n" ^ showValue v ^ "\n\n")
let trace x = print_string x; flush_all ()

let traceCheck e t : unit = if !Prefs.trace then
  trace (Printf.sprintf "CHECK: %s : %s\n" (showExp e) (showValue t))

let traceInfer e : unit = if !Prefs.trace then
  trace (Printf.sprintf "INFER: %s\n" (showExp e))

let traceInferV v : unit = if !Prefs.trace then
  trace (Printf.sprintf "INFERV: %s\n" (showValue v))

let traceEval e : unit = if !Prefs.trace then
  trace (Printf.sprintf "EVAL: %s\n" (showExp e))

let traceWeak e : unit = if !Prefs.trace then
  trace (Printf.sprintf "WEAK: %s\n" (showExp e))

let traceRbV v : unit = if !Prefs.trace then
  trace (Printf.sprintf "RBV: %s\n" (showValue v))

let traceClos e p v : unit = if !Prefs.trace then
  trace (Printf.sprintf "CLOSBYVAL: (%s)(%s := %s)\n" (showExp e) (showIdent p) (showValue v))

let traceConv v1 v2 : unit = if !Prefs.trace then
  trace (Printf.sprintf "CONV: %s = %s\n" (showValue v1) (showValue v2))

let traceEqNF v1 v2 : unit = if !Prefs.trace then
  trace (Printf.sprintf "EQNF: %s = %s\n" (showValue v1) (showValue v2))
