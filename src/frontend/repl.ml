open Prettyprinter
open Module
open Error
open Decl

open Radio

let help =
"Available commands:
  <statement>    infer type and normalize statement
  :q             quit
  :r             restart
  :h             display this message

Information about command line options can be found at ‘anders help’."

let banner =
  Printf.sprintf "Anders Proof Assistant version %Ld.%Ld.%Ld
This software is licensed under the ISC License. For more information, see LICENSE file."
    Fuze.year Fuze.month Fuze.patch

let loaded : Files.t ref = ref Files.empty

let main : command -> unit = function
  | Expr e -> let (t, v) = (infer e, eval e) in
    Printf.printf "TYPE: %s\nEVAL: %s\n" (showExp t) (showExp v)
  | Action "q" -> exit 0
  | Action "r" -> loaded := Files.empty; raise Restart
  | Action "h" -> print_endline help
  | Command (s, _) | Action s -> raise (UnknownCommand s)
  | Nope -> ()

let repl () =
  print_endline ("\n" ^ banner ^ "\n\nFor help type ‘:h’.\n");
  try while true do
    print_string "> "; let line = read_line () in
    handleErrors (fun s ->
      match Combinators.runParser Parser.repl (Combinators.ofString s) 0 with
      | Error err -> Printf.printf "Parse error:\n%s\n" err
      | Ok (_, c) -> main c) line ()
  done with End_of_file -> ()
