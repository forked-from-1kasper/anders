open Spec

module type Writer =
sig
  val put  : char -> unit
  val puts : string -> unit
end

module Encode (W : Writer) =
struct
  (* I think there should be more efficient way to do this *)
  let int64 n =
    for i = 0 to 7 do
      Int64.shift_right n (i * 8)
      |> Int64.logand 255L
      |> Int64.to_int
      |> Char.chr
      |> W.put
    done

  let int n = int64 (Int64.of_int n)
  let string xs = int (String.length xs); W.puts xs
  let integer n = string (Z.to_bits n)

  let ident = function
    | Irrefutable -> W.put '\x00'
    | Ident (xs, n) -> W.put '\xFF'; string xs; int64 n

  let dir = function
    | Zero -> W.put '\x00'
    | One  -> W.put '\xFF'

  let face mu = int (Env.cardinal mu);
    Env.iter (fun i d -> ident i; dir d) mu

  let rec exp = function
    | EHole                -> W.put '\x01'
    | EPre n               -> W.put '\x02'; integer n
    | EKan n               -> W.put '\x03'; integer n
    | EVar x               -> W.put '\x04'; ident x
    | EPi (a, (p, b))      -> clos '\x10' a p b
    | ELam (a, (p, b))     -> clos '\x11' a p b
    | EApp (f, x)          -> W.put '\x12'; exp f; exp x
    | ESig (a, (p, b))     -> clos '\x13' a p b
    | EPair (_, a, b)      -> W.put '\x14'; exp a; exp b
    | EFst e               -> W.put '\x15'; exp e
    | ESnd e               -> W.put '\x16'; exp e
    | EField (e, x)        -> W.put '\x17'; exp e; string x
    | EId e                -> W.put '\x20'; exp e
    | ERef e               -> W.put '\x21'; exp e
    | EJ e                 -> W.put '\x22'; exp e
    | EPathP e             -> W.put '\x23'; exp e
    | EPLam e              -> W.put '\x24'; exp e
    | EAppFormula (p, i)   -> W.put '\x25'; exp p; exp i
    | EI                   -> W.put '\x26'
    | EDir Zero            -> W.put '\x27'
    | EDir One             -> W.put '\x28'
    | EAnd (i, j)          -> W.put '\x29'; exp i; exp j
    | EOr (i, j)           -> W.put '\x2A'; exp i; exp j
    | ENeg e               -> W.put '\x2B'; exp e
    | ETransp (p, i)       -> W.put '\x30'; exp p; exp i
    | EHComp (t, r, u, u0) -> W.put '\x31'; exp t; exp r; exp u; exp u0
    | EPartial e           -> W.put '\x32'; exp e
    | EPartialP (u, r)     -> W.put '\x33'; exp u; exp r
    | ESystem ts           -> W.put '\x34'; system ts
    | ESub (a, i, u)       -> W.put '\x35'; exp a; exp i; exp u
    | EInc (t, r)          -> W.put '\x36'; exp t; exp r
    | EOuc e               -> W.put '\x37'; exp e
    | EGlue t              -> W.put '\x38'; exp t
    | EGlueElem (r, u, a)  -> W.put '\x39'; exp r; exp u; exp a
    | EUnglue (r, u, e)    -> W.put '\x3A'; exp r; exp u; exp e
    | EEmpty               -> W.put '\x40'
    | EIndEmpty t          -> W.put '\x41'; exp t
    | EUnit                -> W.put '\x42'
    | EStar                -> W.put '\x43'
    | EIndUnit t           -> W.put '\x44'; exp t
    | EBool                -> W.put '\x45'
    | EFalse               -> W.put '\x46'
    | ETrue                -> W.put '\x47'
    | EIndBool t           -> W.put '\x48'; exp t
    | EW (a, (p, b))       -> clos '\x49' a p b
    | ESup (a, b)          -> W.put '\x4A'; exp a; exp b
    | EIndW (a, b, c)      -> W.put '\x4B'; exp a; exp b; exp c
    | EIm t                -> W.put '\x50'; exp t
    | EInf e               -> W.put '\x51'; exp e
    | EIndIm (t, f)        -> W.put '\x52'; exp t; exp f
    | EJoin e              -> W.put '\x53'; exp e

  and clos idx a p b = W.put idx; exp a; ident p; exp b

  and system ts = int (System.cardinal ts);
    System.iter (fun mu e -> face mu; exp e) ts
end

module Serialize = Encode(struct
  let put  = print_char
  let puts = print_string
end)