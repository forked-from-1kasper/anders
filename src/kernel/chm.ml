open Language.Encode
open Language.Decode
open Language.Spec
open Check
open Elab
open Term
open Rbv

let ctx : ctx ref = ref Env.empty

let getBoolVal opt = function
  | "tt" | "true"  -> true
  | "ff" | "false" -> false
  | value -> raise (Internal (InvalidOptValue (opt, value)))

let getTerm e = if !Prefs.preeval then Value (eval !ctx e) else Exp e
let assign x t e = ctx := Env.add (ident x) (Global, Value t, getTerm e) !ctx

let promote fn = try fn () with exc -> Error (extErr exc)

let proto : req -> resp = function
  | Check (e, t)     -> promote (fun () -> check !ctx e (eval !ctx t); OK)
  | Infer e          -> promote (fun () -> Term (rbV (infer !ctx e)))
  | Eval e           -> promote (fun () -> Term (rbV (eval !ctx e)))
  | Conv (e1, e2)    -> promote (fun () ->
    Bool (conv (eval !ctx e1) (eval !ctx e2)))
  | Def (x, t, e)    -> promote (fun () ->
    if Env.mem (ident x) !ctx then Error (AlreadyDeclared x)
    else (let t' = eval !ctx (freshExp t) in let e' = freshExp e in
      ignore (extSet (inferV t')); check !ctx e' t'; assign x t' e'; OK))
  | Assign (x, t, e) -> promote (fun () ->
    if Env.mem (ident x) !ctx then Error (AlreadyDeclared x)
    else (let t' = eval !ctx (freshExp t) in
      ignore (extSet (inferV t')); assign x t' (freshExp e); OK))
  | Assume (x, e)    -> promote (fun () -> let t = eval !ctx (freshExp e) in
    let y = ident x in if Env.mem y !ctx then Error (AlreadyDeclared x)
    else (ignore (extSet (inferV t)); ctx := Env.add y (Global, Value t, Value (Var (y, t))) !ctx; OK))
  | Erase x          -> ctx := Env.remove (ident x) !ctx; OK
  | Wipe             -> ctx := Env.empty; OK
  | Set (p, x)       ->
  begin match p with
    | "trace"       -> Prefs.trace       := getBoolVal p x; OK
    | "pre-eval"    -> Prefs.preeval     := getBoolVal p x; OK
    | "girard"      -> Prefs.girard      := getBoolVal p x; OK
    | "irrelevance" -> Prefs.irrelevance := getBoolVal p x; OK
    | _             -> Error (InvalidOpt p)
  end
  | Version          -> Version (1L, 3L, 0L)
  | Ping             -> Pong

let () = try while true do
  Serialize.resp (try proto (Deserialize.req ())
    with Invalid_argument xs
       | Decode xs -> Error (Unknown xs));
  flush_all ()
done with End_of_file -> ()