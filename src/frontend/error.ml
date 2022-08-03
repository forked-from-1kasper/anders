open Language.Prelude
open Language.Spec
open Prettyprinter
open Parser
open Module
open Prefs

exception Kernel             of error
exception Parser             of int * string * string
exception UnknownOption      of string
exception UnknownOptionValue of string * string
exception UnknownCommand     of string
exception ExtractionError    of string
exception UnknownPrimitive   of string
exception InvalidModuleName  of string * string
exception ProtocolViolation
exception Restart

let rec prettyPrintError : error -> string = function
  | Unknown x                   -> Printf.sprintf "Internal error in kernel: %s\n" x
  | Ineq (e1, e2)               -> Printf.sprintf "Type mismatch:\n  %s\nis not equal to\n  %s\n" (showExp e1) (showExp e2)
  | ExpectedPi x                -> Printf.sprintf "  %s\nexpected to be Pi-type.\n" (showExp x)
  | ExpectedSig x               -> Printf.sprintf "  %s\nexpected to be Sigma-type.\n" (showExp x)
  | ExpectedW x                 -> Printf.sprintf "  %s\nexpected to be W-type.\n" (showExp x)
  | ExpectedType x              -> Printf.sprintf "  %s\nexpected to be universe.\n" (showExp x)
  | ExpectedKan x               -> Printf.sprintf "  %s\nexpected to be fibrant universe.\n" (showExp x)
  | ExpectedPath x              -> Printf.sprintf "“%s” expected to be a path.\n" (showExp x)
  | ExpectedSubtype x           -> Printf.sprintf "  %s\nexpected to be a cubical subtype.\n" (showExp x)
  | ExpectedSystem x            -> Printf.sprintf "  %s\nexpected to be a system.\n" (showExp x)
  | ExpectedFormula x           -> Printf.sprintf "“%s” expected to be a formula.\n" (showExp x)
  | ExpectedIm x                -> Printf.sprintf "“%s” expected to be a modality.\n" (showExp x)
  | ExpectedCoeq x              -> Printf.sprintf "“%s” expected to be a coequalizer.\n" (showExp x)
  | ExpectedInf x               -> Printf.sprintf "“%s” expected to be a unit of modality.\n" (showExp x)
  | ExpectedGlue x              -> Printf.sprintf "“%s” expected to be a Glue-type.\n" (showExp x)
  | ExpectedSup x               -> Printf.sprintf "“%s” expected to be a sup.\n" (showExp x)
  | DNFSolverError (e, d)       -> Printf.sprintf "Cannot solve: %s = %s" (showExp e) (showDir d)
  | AlreadyDeclared p           -> Printf.sprintf "“%s” is already declared.\n" p
  | VariableNotFound p          -> Printf.sprintf "Variable %s was not found\n" (showIdent p)
  | InferError e                -> Printf.sprintf "Cannot infer type of\n  %s\n" (showExp e)
  | InvalidOpt x                -> Printf.sprintf "Unknown option “%s”.\n" x
  | InvalidOptValue (p, x)      -> Printf.sprintf "Unknown value “%s” of option “%s”.\n" p x
  | ExpectedLevel e             -> Printf.sprintf "“%s” expected to be a universe level.\n" (showExp e)
  | ExpectedNonDependent (x, e) -> Printf.sprintf "“%s” cannot depend on “%s”." (showExp e) (showIdent x)
  | Traceback (e, es)           ->
    List.map (fun (e, t) -> Printf.sprintf "When trying to typecheck\n  %s\nAgainst type\n  %s\n" (showExp e) (showExp t)) es
    |> String.concat "" |> flip (^) (prettyPrintError e)

let unknownOption opt = Printf.printf "Unknown option “%s”\n" opt
let unknownOptionValue value opt = Printf.printf "Unknown value “%s” of option “%s”\n" value opt

let prettyPrintExn : exn -> unit = function
  | Kernel err                         -> print_string (prettyPrintError err)
  | Parser (x, buf, filename)          -> Printf.printf "Parsing error at line %d while parsing “%s”: “%s”\n" x filename buf
  | UnknownOption opt                  -> unknownOption opt
  | UnknownOptionValue (opt, value)    -> unknownOptionValue opt value
  | UnknownCommand s                   -> Printf.printf "Unknown command “%s”\n" s
  | ExtractionError s                  -> Printf.printf "Error occured during extraction:\n  %s\n" s
  | UnknownPrimitive x                 -> Printf.printf "Unknown primitive “%s”\n" x
  | InvalidModuleName (name, filename) -> Printf.printf "Module “%s” does not match name of its file: %s\n" name filename
  | ExpectedDir s                      -> Printf.printf "“%s” expected to be “%s” or “%s”" s !zeroPrim !onePrim
  | Sys_error s                        -> print_endline s
  | ProtocolViolation                  -> Printf.printf "Protocol violation\n"
  | InvalidSyntax e                    -> Printf.printf "Invalid syntax:\n  %s\n" (showStx e)
  | ExpectedNode e                     -> Printf.printf "“%s” expected to be a node.\n" (showStx e)
  | ExpectedIdent e                    -> Printf.printf "\n  %s\nexpected to be an ident.\n" (showStx e)
  | OpConflict (e1, e2)                -> Printf.printf "Operator conflict between\n  %s\nand\n  %s\n" (showStxs (takeParens e1)) (showStx e2)
  | UnexpectedInfix x                  -> Printf.printf "Unexpected infix operator “%s” in this position.\n" x
  | UnexpectedPostfix x                -> Printf.printf "Unexpected postfix operator “%s” in this position.\n" x
  | TooFewArguments                    -> Printf.printf "Too few arguments.\n"
  | Restart                            -> raise Restart
  | ex                                 -> Printf.printf "Uncaught exception: %s\n" (Printexc.to_string ex)

let handleErrors (f : 'a -> 'b) (x : 'a) (default : 'b) : 'b =
  try f x with ex -> prettyPrintExn ex; default