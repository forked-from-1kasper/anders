open Spec

module type Reader =
sig
  val get  : unit -> char
  val getn : int64 -> string
end

module Decode (R : Reader) =
struct
  let int64 () =
    let n = ref 0L in
    for i = 0 to 7 do
      n := Int64.add !n
        (R.get () |> Char.code |> Int64.of_int
        |> fun n -> Int64.shift_left n (i * 8))
    done; !n

  let string () = R.getn (int64 ())
  let integer () = Z.of_bits (string ())

  let ident () = match R.get () with
    | '\x00' -> Irrefutable
    | '\xFF' -> let xs = string () in let n = int64 () in Ident (xs, n)
    | _      -> failwith "Ident?"

  let dir () = match R.get () with
    | '\x00' -> Zero
    | '\xFF' -> One
    | _      -> failwith "Dir?"

  let face () = let n = int64 () in let mu = ref Env.empty in
    for _ = 1 to Int64.to_int n do
      let i = ident () in let d = dir () in
      mu := Env.add i d !mu
    done; !mu

  let rec exp () = match R.get () with
    | '\x01' -> EHole
    | '\x02' -> EPre (integer ())
    | '\x03' -> EKan (integer ())
    | '\x04' -> EVar (ident ())
    | '\x10' -> let (a, p, b) = clos () in EPi (a, (p, b))
    | '\x11' -> let (a, p, b) = clos () in ELam (a, (p, b))
    | '\x12' -> let f = exp () in let x = exp () in EApp (f, x)
    | '\x13' -> let (a, p, b) = clos () in ESig (a, (p, b))
    | '\x14' -> let (a, b) = exp2 () in EPair (ref None, a, b)
    | '\x15' -> EFst (exp ())
    | '\x16' -> ESnd (exp ())
    | '\x17' -> let e = exp () in let x = string () in EField (e, x)
    | '\x20' -> EId (exp ())
    | '\x21' -> ERef (exp ())
    | '\x22' -> EJ (exp ())
    | '\x23' -> EPathP (exp ())
    | '\x24' -> EPLam (exp ())
    | '\x25' -> let p = exp () in let i = exp () in EAppFormula (p, i)
    | '\x26' -> EI
    | '\x27' -> EDir Zero
    | '\x28' -> EDir One
    | '\x29' -> let (i, j) = exp2 () in EAnd (i, j)
    | '\x2A' -> let (i, j) = exp2 () in EOr (i, j)
    | '\x2B' -> ENeg (exp ())
    | '\x30' -> let (p, i) = exp2 () in ETransp (p, i)
    | '\x31' -> let (t, r, u, u0) = exp4 () in EHComp (t, r, u, u0)
    | '\x32' -> EPartial (exp ())
    | '\x33' -> let (u, r) = exp2 () in EPartialP (u, r)
    | '\x34' -> ESystem (system ())
    | '\x35' -> let (a, i, u) = exp3 () in ESub (a, i, u)
    | '\x36' -> let (t, r) = exp2 () in EInc (t, r)
    | '\x37' -> EOuc (exp ())
    | '\x38' -> EGlue (exp ())
    | '\x39' -> let (r, u, a) = exp3 () in EGlueElem (r, u, a)
    | '\x3A' -> let (r, u, e) = exp3 () in EUnglue (r, u, e)
    | '\x40' -> EEmpty
    | '\x41' -> EIndEmpty (exp ())
    | '\x42' -> EUnit
    | '\x43' -> EStar
    | '\x44' -> EIndUnit (exp ())
    | '\x45' -> EBool
    | '\x46' -> EFalse
    | '\x47' -> ETrue
    | '\x48' -> EIndBool (exp ())
    | '\x49' -> let (a, p, b) = clos () in EW (a, (p, b))
    | '\x4A' -> let (a, b) = exp2 () in ESup (a, b)
    | '\x4B' -> let (a, b, c) = exp3 () in EIndW (a, b, c)
    | '\x50' -> EIm (exp ())
    | '\x51' -> EInf (exp ())
    | '\x52' -> let (t, f) = exp2 () in EIndIm (t, f)
    | '\x53' -> EJoin (exp ())
    | _      -> failwith "Term?"

  and exp2 () = let a = exp () in let b = exp () in (a, b)
  and exp3 () = let a = exp () in let b = exp () in let c = exp () in (a, b, c)
  and exp4 () = let a = exp () in let b = exp () in let c = exp () in let d = exp () in (a, b, c, d)

  and clos () = let a = exp () in let p = ident () in let b = exp () in (a, p, b)

  and system () = let n = int64 () in let ts = ref System.empty in
    for _ = 1 to Int64.to_int n do
      let mu = face () in let e = exp () in
      ts := System.add mu e !ts
    done; !ts
end

module Deserialize = Decode(struct
  let get () = input_char stdin
  let getn n = let m = Int64.to_int n in let bs = Bytes.make m '\x00' in
    for idx = 0 to m - 1 do
      Bytes.set bs idx (get ())
    done; Bytes.to_string bs
end)