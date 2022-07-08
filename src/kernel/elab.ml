open Language.Prelude
open Language.Spec
open Term
open Gen
open Rbv

let extPiG : value -> value * clos = function
  | VPi (t, g) -> (t, g)
  | u          -> raise (Internal (ExpectedPi (rbV u)))

let extSigG : value -> value * clos = function
  | VSig (t, g) -> (t, g)
  | u           -> raise (Internal (ExpectedSig (rbV u)))

let extW : value -> value * clos = function
  | W (t, g) -> (t, g)
  | u        -> raise (Internal (ExpectedW (rbV u)))

let extIm : value -> value = function
  | VIm v -> v
  | v     -> raise (Internal (ExpectedIm (rbV v)))

let extCoeq : value -> value * value = function
  | VCoeq (f, g) -> (f, g)
  | u            -> raise (Internal (ExpectedCoeq (rbV u)))

let extSum : value -> string * value * value list = function
  | VSum (x, t, xs) -> (x, t, xs)
  | v               -> raise (Internal (ExpectedHIT (rbV v)))

let extInf : value -> value = function
  | VInf v -> v
  | v      -> raise (Internal (ExpectedInf (rbV v)))

let extSup : value -> value * value = function
  | VApp (VApp (VSup _, a), f) -> (a, f)
  | v                          -> raise (Internal (ExpectedSup (rbV v)))

let extFormula : value -> disjunction = function
  | VFormula ks -> ks
  | Var (p, _)  -> Disjunction.singleton (Conjunction.singleton (p, One))
  | v           -> raise (Internal (ExpectedFormula (rbV v)))

let isInf : value -> bool = function
  | VInf _ -> true | _ -> false

let isSup : value -> bool = function
  | VApp (VApp (VSup _, _), _) -> true | _ -> false

let join = function
  | VInf v -> v
  | v      -> VJoin v

let inf = function
  | VJoin v -> v
  | v       -> VInf v

let inc t r = function
  | VOuc v -> v
  | v      -> VApp (VInc (t, r), v)

let extPathP = function
  | VApp (VApp (VPathP v, u0), u1) -> (v, u0, u1)
  | v                              -> raise (Internal (ExpectedPath (rbV v)))

let extGlue = function
  | VApp (VApp (VGlue t, r), u) -> (t, r, u)
  | v -> raise (Internal (ExpectedGlue (rbV v)))

let extVar ctx x = match Env.find_opt x ctx with
  | Some (_, _, Value (Var (y, _))) -> y
  | Some (_, _, Exp (EVar y)) -> y
  | _ -> x

let idv t x y = VApp (VApp (VId t, x), y)
let implv a b = VPi (a, (Irrefutable, fun _ -> b))
let prodv a b = VSig (a, (Irrefutable, fun _ -> b))
let pairv a b = VPair (ref None, a, b)

let idp v = VPLam (VLam (VI, (Irrefutable, fun _ -> v)))
let idfun t = VLam (t, (freshName "x", fun x -> x))
let pathv v a b = VApp (VApp (VPathP v, a), b)

let hcompval u = EApp (EApp (u, ezero), ERef eone)

let freshDim () = let i = freshName "ι" in (i, EVar i, Var (i, VI))

let vfst : value -> value = function
  | VPair (_, u, _) -> u
  | v               -> VFst v

let vsnd : value -> value = function
  | VPair (_, _, u) -> u
  | v               -> VSnd v

let eta v = (vfst v, vsnd v)

let rec extByTag p : value -> value option = function
  | VPair (t, fst, snd) ->
  begin match !t with
    | Some q -> if p = q then Some fst else extByTag p snd
    | _      -> extByTag p snd
  end
  | _ -> None

let rec getField p v = function
  | VSig (t, (q, g)) ->
    if matchIdent p q then (vfst v, t)
    else getField p (vsnd v) (g (vfst v))
  | t -> raise (Internal (ExpectedSig (rbV t)))

let rec salt (ns : ident Env.t) : exp -> exp = function
  | ELam (a, (p, b))     -> saltClos eLam ns p a b
  | EType (c, Finite e)  -> EType (c, Finite (salt ns e))
  | EType (c, Omega n)   -> EType (c, Omega n)
  | ELevel               -> ELevel
  | ELevelElem n         -> ELevelElem n
  | ESucc e              -> ESucc (salt ns e)
  | EAdd (e1, e2)        -> EAdd (salt ns e1, salt ns e2)
  | EMax (e1, e2)        -> EMax (salt ns e1, salt ns e2)
  | EPi (a, (p, b))      -> saltClos ePi ns p a b
  | ESig (a, (p, b))     -> saltClos eSig ns p a b
  | EPair (r, a, b)      -> EPair (r, salt ns a, salt ns b)
  | EFst e               -> EFst (salt ns e)
  | ESnd e               -> ESnd (salt ns e)
  | EField (e, p)        -> EField (salt ns e, p)
  | EApp (f, x)          -> EApp (salt ns f, salt ns x)
  | EVar x               -> EVar (freshVar ns x)
  | EHole                -> EHole
  | EId e                -> EId (salt ns e)
  | ERef e               -> ERef (salt ns e)
  | EJ e                 -> EJ (salt ns e)
  | EPathP e             -> EPathP (salt ns e)
  | ETransp (p, i)       -> ETransp (salt ns p, salt ns i)
  | EHComp (t, r, u, u0) -> EHComp (salt ns t, salt ns r, salt ns u, salt ns u0)
  | EPLam e              -> EPLam (salt ns e)
  | EAppFormula (p, i)   -> EAppFormula (salt ns p, salt ns i)
  | EPartial e           -> EPartial (salt ns e)
  | EPartialP (t, r)     -> EPartialP (salt ns t, salt ns r)
  | ESub (a, i, u)       -> ESub (salt ns a, salt ns i, salt ns u)
  | ESystem xs           -> ESystem (saltSystem ns xs)
  | EInc (t, r)          -> EInc (salt ns t, salt ns r)
  | EOuc e               -> EOuc (salt ns e)
  | EI                   -> EI
  | EDir d               -> EDir d
  | EAnd (a, b)          -> EAnd (salt ns a, salt ns b)
  | EOr (a, b)           -> EOr (salt ns a, salt ns b)
  | ENeg e               -> ENeg (salt ns e)
  | EGlue e              -> EGlue (salt ns e)
  | EGlueElem (r, u, a)  -> EGlueElem (salt ns r, salt ns u, salt ns a)
  | EUnglue (r, u, e)    -> EUnglue (salt ns r, salt ns u, salt ns e)
  | EEmpty               -> EEmpty
  | EIndEmpty e          -> EIndEmpty (salt ns e)
  | EUnit                -> EUnit
  | EStar                -> EStar
  | EIndUnit e           -> EIndUnit (salt ns e)
  | EBool                -> EBool
  | EFalse               -> EFalse
  | ETrue                -> ETrue
  | EIndBool e           -> EIndBool (salt ns e)
  | EW (a, (p, b))       -> saltClos eW ns p a b
  | ESup (a, b)          -> ESup (salt ns a, salt ns b)
  | EIndW e              -> EIndW (salt ns e)
  | EIm e                -> EIm (salt ns e)
  | EInf e               -> EInf (salt ns e)
  | EIndIm (a, b)        -> EIndIm (salt ns a, salt ns b)
  | EJoin e              -> EJoin (salt ns e)
  | ECoeq (f, g)         -> ECoeq (salt ns f, salt ns g)
  | EIota (f, g, x)      -> EIota (salt ns f, salt ns g, salt ns x)
  | EResp (f, g, x)      -> EResp (salt ns f, salt ns g, salt ns x)
  | EIndCoeq (e, i, r)   -> EIndCoeq (salt ns e, salt ns i, salt ns r)

and saltClos ctor ns p a b =
  let x = fresh p in ctor x (salt ns a) (salt (Env.add p x ns) b)

and saltSystem ns xs =
  System.fold (fun k v -> System.add (freshFace ns k) (salt ns v)) xs System.empty

let saltTele ns (x, e) = let y = fresh x in (Env.add x y ns, (y, salt ns e))

let saltTeles ns0 ts =
  let ns = ref ns0 in
  let ts' = List.map (fun t0 ->
    let (ns', t) = saltTele !ns t0 in
    ns := ns'; t) ts in
  (!ns, ts')

let saltCtor ns0 (c : ctor) : ctor =
  let (ns, params) = saltTeles ns0 c.params in
  let boundary = saltSystem ns c.boundary in
  { c with params = params; boundary = boundary }

let saltData ns0 (d : data) : data =
  let (ns, params) = saltTeles ns0 d.params in
  let kind = salt ns d.kind in
  let ctors = List.map (saltCtor ns) d.ctors in
  { kind = kind; params = params; ctors = ctors }

let saltBranch ns0 (x, is0, e) =
  let is = List.map fresh is0 in let ns = ref ns0 in
  List.iter2 (fun i0 i -> ns := Env.add i0 i !ns) is0 is;
  (x, is, salt !ns e)

let saltSplit ns0 (s : split) : split =
  let (ns, params) = saltTeles ns0 s.params in
  let signature    = salt ns s.signature in
  let branches     = List.map (saltBranch ns) s.branches in
  { s with params = params; signature = signature; branches = branches }

let freshExp   = salt Env.empty
let freshData  = saltData Env.empty
let freshSplit = saltSplit Env.empty

(* https://github.com/mortberg/cubicaltt/blob/hcomptrans/Eval.hs#L129
   >This increases efficiency as it won’t trigger computation. *)
let swapVar i j k = if i = k then j else k

let swapAtom i j = fun (k, d) -> (swapVar i j k, d)
let swapConjunction i j = Conjunction.map (swapAtom i j)
let swapDisjunction i j = Disjunction.map (swapConjunction i j)

let swapMaximum i j = Maximum.map (fun (n, ts) -> (n, Idents.map (swapVar i j) ts))

let rec swap i j = function
  | VLam (t, (x, g))     -> VLam (swap i j t, (x, g >> swap i j))
  | VPair (r, u, v)      -> VPair (r, swap i j u, swap i j v)
  | VLevel               -> VLevel
  | VLevelElem ts        -> VLevelElem (swapMaximum i j ts)
  | VType (c, Finite ts) -> VType (c, Finite (swapMaximum i j ts))
  | VType (c, Omega n)   -> VType (c, Omega n)
  | VPi (t, (x, g))      -> VPi (swap i j t, (x, g >> swap i j))
  | VSig (t, (x, g))     -> VSig (swap i j t, (x, g >> swap i j))
  | VPLam f              -> VPLam (swap i j f)
  | Var (k, VI)          -> Var (swapVar i j k, VI)
  | Var (x, t)           -> Var (x, swap i j t)
  | VApp (f, x)          -> VApp (swap i j f, swap i j x)
  | VFst k               -> VFst (swap i j k)
  | VSnd k               -> VSnd (swap i j k)
  | VHole                -> VHole
  | VPathP v             -> VPathP (swap i j v)
  | VPartialP (t, r)     -> VPartialP (swap i j t, swap i j r)
  | VSystem ts           -> VSystem (swapSystem i j ts)
  | VSub (t, r, u)       -> VSub (swap i j t, swap i j r, swap i j u)
  | VTransp (p, r)       -> VTransp (swap i j p, swap i j r)
  | VHComp (t, r, u, u0) -> VHComp (swap i j t, swap i j r, swap i j u, swap i j u0)
  | VAppFormula (f, x)   -> VAppFormula (swap i j f, swap i j x)
  | VId v                -> VId (swap i j v)
  | VRef v               -> VRef (swap i j v)
  | VJ v                 -> VJ (swap i j v)
  | VI                   -> VI
  | VFormula t           -> VFormula (swapDisjunction i j t)
  | VInc (t, r)          -> VInc (swap i j t, swap i j r)
  | VOuc v               -> VOuc (swap i j v)
  | VGlue v              -> VGlue (swap i j v)
  | VGlueElem (r, u, a)  -> VGlueElem (swap i j r, swap i j u, swap i j a)
  | VUnglue (r, u, v)    -> VUnglue (swap i j r, swap i j u, swap i j v)
  | VEmpty               -> VEmpty
  | VIndEmpty v          -> VIndEmpty (swap i j v)
  | VUnit                -> VUnit
  | VStar                -> VStar
  | VIndUnit v           -> VIndUnit (swap i j v)
  | VBool                -> VBool
  | VFalse               -> VFalse
  | VTrue                -> VTrue
  | VIndBool v           -> VIndBool (swap i j v)
  | W (t, (x, g))        -> W (swap i j t, (x, g >> swap i j))
  | VSup (a, b)          -> VSup (swap i j a, swap i j b)
  | VIndW e              -> VIndW (swap i j e)
  | VSum (x, t, xs)      -> VSum (x, swap i j t, List.map (swap i j) xs)
  | VCon c               -> VCon (swapCon i j c)
  | VSplit s             -> VSplit (swapElim i j s)
  | VIm v                -> VIm (swap i j v)
  | VInf v               -> VInf (swap i j v)
  | VIndIm (a, b)        -> VIndIm (swap i j a, swap i j b)
  | VJoin v              -> VJoin (swap i j v)
  | VCoeq (f, g)         -> VCoeq (swap i j f, swap i j g)
  | VIota (f, g, x)      -> VIota (swap i j f, swap i j g, swap i j x)
  | VResp (f, g, x)      -> VResp (swap i j f, swap i j g, swap i j x)
  | VIndCoeq (v, k, r)   -> VIndCoeq (swap i j v, swap i j k, swap i j r)

and swapSystem i j ts = System.fold (fun k v -> System.add (mapFace (swapVar i j) k) (swap i j v)) ts System.empty

and swapCon i j (c : con) =
  { c with kind     = swap i j c.kind;
           params   = List.map (swap i j) c.params;
           cparams  = List.map (swap i j) c.cparams;
           boundary = swapSystem i j c.boundary }

and swapElim i j (s : elim) =
  let (t, (x, g)) = s.signature in
  { s with fparams   = List.map (swap i j) s.fparams;
           signature = (swap i j t, (x, g >> swap i j));
           branches  = List.map (swapBranch i j) s.branches }

and swapBranch i j (c, ts, fn) =
  (c, List.map (fun (x, v) -> (x, swap i j v)) ts, fn >> swap i j)

let memAtom y = fun (x, _) -> x = y
let memConjunction y = Conjunction.exists (memAtom y)
let memDisjunction y = Disjunction.exists (memConjunction y)

let memMaximum y = Maximum.exists (fun (_, ts) -> Idents.exists y ts)

let rec mem y = function
  | Var (x, _) -> x = y
  | VLam (t, (x, g)) | VPi (t, (x, g))
  | VSig (t, (x, g)) | W (t, (x, g)) -> memClos y t x g
  | VType (_, Omega _) | VLevel | VHole | VI | VEmpty
  | VUnit | VStar | VBool | VFalse | VTrue -> false
  | VPLam a | VFst a | VSnd a | VPathP a | VId a | VRef a
  | VJ a | VOuc a | VGlue a | VIndEmpty a | VIndUnit a
  | VIndBool a | VIndW a | VIm a | VInf a | VJoin a -> mem y a
  | VApp (a, b) | VPartialP (a, b) | VAppFormula (a, b)
  | VTransp (a, b) | VInc (a, b) | VSup (a, b)
  | VIndIm (a, b) | VPair (_, a, b) | VCoeq (a, b) -> mem y a || mem y b
  | VSub (a, b, c) | VGlueElem (a, b, c) | VUnglue (a, b, c)
  | VIota (a, b, c) | VResp (a, b, c) | VIndCoeq (a, b, c) -> mem y a || mem y b || mem y c
  | VHComp (a, b, c, d) -> mem y a || mem y b || mem y c || mem y d
  | VFormula t -> memDisjunction y t
  | VSystem ts -> memSystem y ts
  | VType (_, Finite ts) | VLevelElem ts -> memMaximum (fun x -> x = y) ts
  | VSum (x, t, xs) -> ident x = y || mem y t || List.exists (mem y) xs
  | VCon c -> memCon y c
  | VSplit s -> memElim y s

and memClos y t x g = if x = y then false else mem y (g (Var (x, t)))

and memSystem y ts = System.exists (fun mu v -> Env.mem y mu || mem y v) ts

and memCon y (c : con) =
     ident c.name = y
  || ident c.cname = y
  || mem y c.kind
  || List.exists (mem y) c.params
  || List.exists (mem y) c.cparams
  || memSystem y c.boundary

and memElim y (s : elim) =
  let (t, (x, g)) = s.signature in
     ident s.fname = y
  || List.exists (mem y) s.fparams
  || memClos y t x g
  || List.exists (memBranch y) s.branches

and memBranch y (c, ts, fn) =
     ident c = y
  || List.exists (fun (x, v) -> x = y || mem y v) ts
  || mem y (fn (List.map (fun (x, v) -> Var (x, v)) ts))

let extErr = function
  | Internal err -> err
  | exc          -> Unknown (Printexc.to_string exc)

let extTraceback = function
  | Traceback (err, es) -> (err, es)
  | err                 -> (err, [])
