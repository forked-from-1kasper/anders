open Language.Encode
open Language.Decode
open Language.Spec
open Universe
open Check
open Hits
open Elab
open Term
open Rbv

let ctx : ctx = { local = Env.empty; global = ref Env.empty; data = ref Dict.empty }

let getUnitVal opt = function
  | "tt" | "true" -> true
  | value -> raise (Internal (InvalidOptValue (opt, value)))

let getBoolVal opt = function
  | "tt" | "true"  -> true
  | "ff" | "false" -> false
  | value -> raise (Internal (InvalidOptValue (opt, value)))

let getTerm e = if !Prefs.normalize then Value (eval ctx e) else Exp e

let promote fn = try fn () with exc -> Error (extErr exc)

let proto : req -> resp = function
  | Check (e0, t0)     -> promote (fun () -> let t = freshExp t0 in
    isType (infer ctx t); check ctx (freshExp e0) (eval ctx t); OK)
  | Infer e            -> promote (fun () -> Term (rbV (infer ctx (freshExp e))))
  | Eval e             -> promote (fun () -> Term (rbV (eval ctx (freshExp e))))
  | Conv (e1, e2)      -> promote (fun () -> Bool (conv (eval ctx (freshExp e1))
                                                        (eval ctx (freshExp e2))))
  | Data (x, d)        -> promote (fun () -> checkData ctx x (freshData d); OK)
  | Split s            -> promote (fun () -> checkSplit ctx (freshSplit s); OK)
  | Def (x, t0, e0)    -> promote (fun () ->
    let t = freshExp t0 in let e = freshExp e0 in
    isType (infer ctx t); let t' = eval ctx t in
    check ctx e t'; assign ctx x t' (getTerm e); OK)
  | Assign (x, t0, e0) -> promote (fun () ->
    let t = freshExp t0 in isType (infer ctx t);
    assign ctx x (eval ctx t) (getTerm (freshExp e0)); OK)
  | Assume (x, t0)     -> promote (fun () -> let t = freshExp t0 in
    isType (infer ctx t); let t' = eval ctx t in
    assign ctx x t' (Value (Var (ident x, t'))); OK)
  | Erase x            -> ctx.global := Env.remove (ident x) !(ctx.global); OK
  | Wipe               -> ctx.global := Env.empty; OK
  | Set (p, x)         ->
  begin match p with
    | "trace"           -> promote (fun () -> Prefs.trace           := getBoolVal p x; OK)
    | "normalize"       -> promote (fun () -> Prefs.normalize       := getBoolVal p x; OK)
    | "girard"          -> promote (fun () -> Prefs.girard          := getUnitVal p x; OK)
    | "impredicativity" -> promote (fun () -> Prefs.impredicativity := getUnitVal p x; OK)
    | _                 -> Error (InvalidOpt p)
  end
  | Version            -> Version (1L, 4L, 2L)
  | Ping               -> Pong

let () = try while true do
  Serialize.resp (try proto (Deserialize.req ())
    with Invalid_argument xs
       | Failure xs -> Error (Unknown xs));
  flush_all ()
done with End_of_file -> ()
