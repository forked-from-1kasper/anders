open Language.Spec
open Term

let rbVAtom : ident * dir -> exp = function
  | (x, Zero) -> ENeg (EVar x)
  | (x, One)  -> EVar x

let rbVAnd t = match Conjunction.elements t with
  | []      -> EDir One
  | x :: xs -> List.fold_left (fun e1 e2 -> EAnd (e1, rbVAtom e2)) (rbVAtom x) xs

let rbVOr t = match Disjunction.elements t with
  | []      -> EDir Zero
  | x :: xs -> List.fold_left (fun e1 e2 -> EOr (e1, rbVAnd e2)) (rbVAnd x) xs

let rbVSumma (n, t) = match Idents.elements t with
  | []      -> ELevelElem n
  | x :: xs -> let e = List.fold_left (fun e1 e2 -> EAdd (e1, EVar e2)) (EVar x) xs in
    if Z.equal n Z.zero then e else EAdd (e, ELevelElem n)

let rbVMaximum t = match Maximum.elements t with
  | []      -> failwith "Level?"
  | x :: xs -> List.fold_left (fun e1 e2 -> EMax (e1, rbVSumma e2)) (rbVSumma x) xs

(* Readback *)
let rec rbV v = match v with
  | VLam (t, g)          -> rbVTele eLam t g
  | VPair (r, u, v)      -> EPair (r, rbV u, rbV v)
  | VLevel               -> ELevel
  | VLevelElem ts        -> rbVMaximum ts
  | VType (c, Finite ts) -> EType (c, Finite (rbVMaximum ts))
  | VType (c, Omega n)   -> EType (c, Omega n)
  | VPi (t, g)           -> rbVTele ePi t g
  | VSig (t, g)          -> rbVTele eSig t g
  | VPLam f              -> EPLam (rbV f)
  | Var (x, _)           -> EVar x
  | VApp (f, x)          -> EApp (rbV f, rbV x)
  | VFst k               -> EFst (rbV k)
  | VSnd k               -> ESnd (rbV k)
  | VHole                -> EHole
  | VPathP v             -> EPathP (rbV v)
  | VPartialP (t, r)     -> EPartialP (rbV t, rbV r)
  | VSystem ts           -> ESystem (System.map rbV ts)
  | VSub (a, i, u)       -> ESub (rbV a, rbV i, rbV u)
  | VTransp (p, i)       -> ETransp (rbV p, rbV i)
  | VHComp (t, r, u, u0) -> EHComp (rbV t, rbV r, rbV u, rbV u0)
  | VAppFormula (f, x)   -> EAppFormula (rbV f, rbV x)
  | VId v                -> EId (rbV v)
  | VRef v               -> ERef (rbV v)
  | VJ v                 -> EJ (rbV v)
  | VI                   -> EI
  | VFormula t           -> rbVOr t
  | VInc (t, r)          -> EInc (rbV t, rbV r)
  | VOuc v               -> EOuc (rbV v)
  | VGlue v              -> EGlue (rbV v)
  | VGlueElem (r, u, a)  -> EGlueElem (rbV r, rbV u, rbV a)
  | VUnglue (r, u, b)    -> EUnglue (rbV r, rbV u, rbV b)
  | VEmpty               -> EEmpty
  | VIndEmpty v          -> EIndEmpty (rbV v)
  | VUnit                -> EUnit
  | VStar                -> EStar
  | VIndUnit v           -> EIndUnit (rbV v)
  | VBool                -> EBool
  | VFalse               -> EFalse
  | VTrue                -> ETrue
  | VIndBool v           -> EIndBool (rbV v)
  | W (t, g)             -> rbVTele eW t g
  | VSup (a, b)          -> ESup (rbV a, rbV b)
  | VIndW e              -> EIndW (rbV e)
  | VIm t                -> EIm (rbV t)
  | VInf v               -> EInf (rbV v)
  | VJoin v              -> EJoin (rbV v)
  | VIndIm (a, b)        -> EIndIm (rbV a, rbV b)
  | VCoeq (f, g)         -> ECoeq (rbV f, rbV g)
  | VIota (f, g, x)      -> EIota (rbV f, rbV g, rbV x)
  | VResp (f, g, x)      -> EResp (rbV f, rbV g, rbV x)
  | VIndCoeq (v, i, r)   -> EIndCoeq (rbV v, rbV i, rbV r)

and rbVTele ctor t (p, g) = let x = Var (p, t) in ctor p (rbV t) (rbV (g x))