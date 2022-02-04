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
  :h             display this message"

let banner = "Anders [MLTT][CCHM][HTS][deRham] proof assistant version 1.3.0"

let loaded : Files.t ref = ref Files.empty

let main : command -> unit = function
  | Eval e -> let (t, v) = (infer e, eval e) in
    Printf.printf "TYPE: %s\nEVAL: %s\n" (showExp t) (showExp v)
  | Action "q" -> exit 0
  | Action "r" -> loaded := Files.empty; raise Restart
  | Action "h" -> print_endline help
  | Command (s, _) | Action s -> raise (UnknownCommand s)
  | Nope -> ()

let check filename = loaded := handleErrors (checkFile !loaded) filename !loaded

let repl () =
  print_endline ("\n" ^ banner);
  try while true do
    print_string "> "; let line = read_line () in
    handleErrors (fun x -> main (Reader.parseErr Parser.repl
      (Lexing.from_string x) "<stdin>")) line ()
  done with End_of_file -> ()
