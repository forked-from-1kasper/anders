open Language.Spec
open Module
open Error
open Radio

module Files = Set.Make(String)

let ext x = x ^ ".anders"
let plugExt x = x ^ ".cmxs"

let variables : ((int * tele) list) ref = ref []
let getVariables () = List.map snd !variables

type plug = string -> exp -> string -> exp
let plugin : (plug option) ref = ref None

let getDeclName = function
  | Def (p, _, _) | Ext (p, _, _) | Axiom (p, _) -> p

let rec checkDecl d =
  let ts = getVariables () in match d with
  | Def (p, Some t, e) -> def p (teles ePi t ts) (teles eLam e ts)
  | Def (p, None, e) -> let e' = teles eLam e ts in assign p (infer e') e'
  | Ext (p, t, v) -> begin match !plugin with
    | Some g -> checkDecl (Def (p, Some (teles ePi t ts), g p t v))
    | None -> failwith "external plugin isn’t loaded"
  end
  | Axiom (p, t) -> assume p (teles ePi t ts)

let getBoolVal opt = function
  | "tt" | "true"  -> true
  | "ff" | "false" -> false
  | value -> raise (UnknownOptionValue (opt, value))

let rec checkLine k fs : line -> Files.t = function
  | Decl d ->
    if !Prefs.verbose then begin
      Printf.printf "Checking: %s\n" (getDeclName d); flush_all ()
    end; checkDecl d; fs
  | Plugin p ->
    plugin := None;
    Dynlink.loadfile (plugExt p);
    begin match !plugin with
      | Some _ -> ()
      | None   -> failwith (Printf.sprintf "Module “%s” was not initialized." p)
    end; fs
  | Option (opt, value) ->
    begin match opt with
      | "girard"   | "irrelevance"
      | "pre-eval" | "impredicativity" -> set opt value
      | "verbose" -> Prefs.verbose := getBoolVal opt value
      | _         -> raise (UnknownOption opt)
    end; fs
  | Import xs -> List.fold_left (fun fs x -> let path = ext x in
    if Files.mem path fs then fs else checkFile fs path) fs xs
  | Section xs -> let fs' = List.fold_left (checkLine (k + 1)) fs xs in
    variables := List.filter (fun (n, _) -> n <= k) !variables; fs'
  | Variables teles -> variables := List.append !variables (List.map (fun tele -> (k, tele)) teles); fs
and checkFile fs path =
  let filename = Filename.basename path in

  let chan = open_in path in
  let file = Reader.parseErr Parser.file (Lexing.from_channel chan) path in
  close_in chan; if !Prefs.verbose then begin
    Printf.printf "Parsed “%s” successfully.\n" filename; flush_all ()
  end;

  let res = checkContent (Files.add path fs) file in
  variables := []; print_endline ("File “" ^ filename ^ "” checked."); res
and checkContent fs xs = List.fold_left (checkLine 0) fs xs
