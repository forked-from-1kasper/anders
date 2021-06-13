open Check
open Error
open Ident
open Expr
open Eval

type state = rho * gamma * Files.t
let ext x = x ^ ".anders"

let rec listLast : 'a list -> 'a = function
  | []      -> raise (Failure "listLast")
  | [x]     -> x
  | x :: xs -> listLast xs

let getDeclName : decl -> string = function
  | Annotated (p, _, _)
  | NotAnnotated (p, _) -> p

let checkDecl rho gma d : rho * gamma = match d with
  | Annotated (p, a, e) ->
    let b = infer rho gma a in
    if not (isVSet b) then raise (ExpectedVSet b) else ();
    let a' = eval a rho in
    let gma' = upGlobal gma (Name (p, 0)) a' in
    check rho gma' e a';
    (upDec rho d, gma')
  | NotAnnotated (p, e) ->
    let a = infer rho gma e in
    let gma' = upGlobal gma (Name (p, 0)) a in
    check rho gma' e a;
    (upDec rho d, gma')

let rec checkLine st : line -> state =
  let (rho, gma, checked) = st in function
  | Decl d ->
    let name = getDeclName d in
    Printf.printf "Checking: %s\n" name; flush_all ();
    let (rho', gma') = checkDecl rho gma d in
    (rho', gma', checked)
  | Option (opt, value) ->
    (match opt with
    | "girard" ->
      (match value with
      | "tt" | "true"  -> girard := true
      | "ff" | "false" -> girard := false
      | _ -> raise (UnknownOptionValue (opt, value)))
    | _ -> raise (UnknownOption opt));
    st
  | Import x -> let path = ext x in if Files.mem path checked then st else checkFile st path
and checkFile p path =
  let (rho, gma, checked) = p in
  let filename = Filename.basename path in
  let chan = open_in path in
  let (name, con) = Lexparse.parseErr Parser.file (Lexing.from_channel chan) in
  close_in chan; Printf.printf "Parsed “%s” successfully.\n" filename; flush_all ();
  if ext name = filename then ()
  else raise (InvalidModuleName (name, filename));
  let res = checkContent (rho, gma, Files.add path checked) con in
  Printf.printf "File loaded.\n"; res
and checkContent st xs = List.fold_left checkLine st xs
