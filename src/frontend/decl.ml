open Language.Prelude
open Language.Spec
open Module
open Error
open Radio

module Files = Set.Make(String)

let checkedFiles = ref Files.empty

let ext x = x ^ ".anders"
let plugExt x = x ^ ".cmxs"

type settings =
  { depth     : int;
    variables : (int * tele) list }

let getVariables conf = List.map snd conf.variables

type plug = string -> exp -> string -> exp
let plugin : (plug option) ref = ref None

let getDeclName = function Def (p, _, _) | Ext (p, _, _) | Axiom (p, _) -> p

let rec checkDecl conf d =
  let ts = getVariables conf in match d with
  | Def (p, Some t, e) -> def p (teles ePi t ts) (teles eLam e ts)
  | Def (p, None, e) -> let e' = teles eLam e ts in assign p (infer e') e'
  | Ext (p, t, v) -> begin match !plugin with
    | Some g -> checkDecl conf (Def (p, Some (teles ePi t ts), g p t v))
    | None -> Printf.printf "external plugin isn’t loaded"
  end
  | Axiom (p, t) -> assume p (teles ePi t ts)

let setBoolVal ptr opt = function
  | "tt" | "true"  -> ptr := true
  | "ff" | "false" -> ptr := false
  | value -> unknownOptionValue opt value

let rec checkLine conf = function
  | Macrovariables is -> Parser.upMacrovars is; conf
  | Token is -> Parser.upTokens is; conf
  | Macro (b, e1, e2) -> Parser.upMacro b e1 e2; conf
  | Macroexpand e -> Printf.printf "MACROEXPAND: %s\n" (showStx (Parser.macroelab e)); flush_all (); conf
  | Infer e -> Printf.printf "INFER: %s\n" (Prettyprinter.showExp (infer e)); flush_all (); conf
  | Eval e -> Printf.printf "EVAL: %s\n" (Prettyprinter.showExp (eval e)); flush_all (); conf
  | Operator (op, prec, is) -> List.iter (fun i -> Parser.operators := Dict.add i (op, prec) !Parser.operators) is; conf
  | Opaque x -> opaque x; conf
  | Decl d ->
    if !Prefs.verbose then begin
      Printf.printf "Checking: %s\n" (getDeclName d); flush_all ()
    end; checkDecl conf d; conf
  | Plugin p ->
    plugin := None;
    Dynlink.loadfile (plugExt p);
    begin match !plugin with
      | Some _ -> ()
      | None   -> Printf.printf "Module “%s” was not initialized." p
    end; conf
  | Option (opt, value) ->
    begin match opt with
      | "girard"    | "irrelevance"
      | "normalize" | "impredicativity" -> set opt value
      | "verbose" -> setBoolVal Prefs.verbose opt value
      | _         -> unknownOption opt
    end; conf
  | Import is -> List.iter (checkFile % ext) is; conf
  | Eof | Skip -> conf
  | Section -> { conf with depth = conf.depth + 1 }
  | End -> { variables = List.filter (fun (n, _) -> n < conf.depth) conf.variables;
             depth     = conf.depth - 1; }
  | Variables ts -> { conf with variables = List.append conf.variables (List.map (fun t -> (conf.depth, t)) ts) }
and checkFile filename =
  if Files.mem filename !checkedFiles then () else
  begin
    Printf.printf "Checking “%s”.\n" filename;
    let chan  = open_in filename in
    let input = Combinators.ofChan chan in

    let conf = ref { variables = []; depth = 0 } in
    let eof = ref false in let pos = ref 0 in

    while not !eof do
      try match Combinators.runParser Parser.cmd input !pos with
      | Error err   -> Printf.printf "Parse error:\n%s\n" err; eof := true
      | Ok (_, Eof) -> eof := true
      | Ok (n, c)   -> pos := n; conf := checkLine !conf c
      with exc -> prettyPrintExn exc; eof := true
    done; close_in chan; checkedFiles := Files.add filename !checkedFiles;
    Printf.printf "File “%s” checked.\n" filename; flush_all ()
  end
