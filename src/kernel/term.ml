open Language.Spec

module Product (A : Map.OrderedType) (B : Map.OrderedType) =
struct
  type t = A.t * B.t
  let compare (a1, b1) (a2, b2) =
    let k = B.compare b1 b2 in
    if k = 0 then A.compare a1 a2 else k
end

module Idents = Set.Make(Ident)
module Summa = Product(Z)(Idents)
type summa = Summa.t

module Maximum =
struct
  include Set.Make(Summa)

  let simplify t =
    let ssubset (n, x) (m, y) =
      not (Idents.equal x y && Z.equal n m)
      &&  (Idents.subset x y && Z.leq n m) in
    filter (fun x -> not (exists (ssubset x) t)) t

  let plus n = map (fun (m, xs) -> (Z.add n m, xs))
  let succ = plus Z.one

  let add a b =
    elements b
    |> List.map (fun (n, xs) -> map (fun (m, ys) -> (Z.add n m, Idents.union xs ys)) a)
    |> List.fold_left union empty
    |> simplify

  let adds = List.fold_left add (singleton (Z.zero, Idents.empty))

  let max a b = simplify (union a b)
end

type maximum = Maximum.t

module Atom = Product(Ident)(Dir)

module Conjunction = Set.Make(Atom)
type conjunction = Conjunction.t

module Disjunction = Set.Make(Conjunction)
type disjunction = Disjunction.t

(* Intermediate type checker values *)

type value =
  | VType of cosmos * maximum level
  | VLevel | VLevelElem of maximum
  | Var of ident * value | VHole
  | VPi of value * clos | VLam of value * clos | VApp of value * value
  | VSig of value * clos | VPair of tag * value * value | VFst of value | VSnd of value
  | VId of value | VRef of value | VJ of value
  | VPathP of value | VPLam of value | VAppFormula of value * value
  | VI | VFormula of disjunction
  | VTransp of value * value | VHComp of value * value * value * value
  | VPartialP of value * value | VSystem of value System.t
  | VSub of value * value * value | VInc of value * value | VOuc of value
  | VGlue of value | VGlueElem of value * value * value | VUnglue of value * value * value
  | VEmpty | VIndEmpty of value
  | VUnit | VStar | VIndUnit of value
  | VBool | VFalse | VTrue | VIndBool of value
  | W of value * clos | VSup of value * value | VIndW of value
  | VCoeq of value * value | VIota of value * value * value
  | VResp of value * value * value | VIndCoeq of value * value * value
  | VIm of value | VInf of value | VIndIm of value * value | VJoin of value

and clos = ident * (value -> value)

type term = Exp of exp | Value of value

type ctx =
  { local  : (value * value) Env.t;
    global : (value * term) Env.t ref }

(* Implementation *)

let dim i = Var (i, VI)

let vzero = VFormula Disjunction.empty
let vone  = VFormula (Disjunction.singleton Conjunction.empty)

let dir = function
  | Zero -> vzero
  | One  -> vone

let negDir : dir -> dir = function
  | Zero -> One | One -> Zero

let bot = Disjunction.is_empty
let top = Disjunction.mem Conjunction.empty

let isOne i = VApp (VApp (VId VI, vone), i)
let extFace x e = e (List.map (fun (p, v) -> Var (p, isOne v)) x)

exception Internal of error
exception IncompatibleFaces

let upVar p x ctx = match p with Irrefutable -> ctx | _ -> Env.add p x ctx
let upLocal ctx p t v = { ctx with local = upVar p (t, v) ctx.local }
let upGlobal ctx p t v = ctx.global := upVar p (t, v) !(ctx.global)

let assign ctx x t e =
  if Env.mem (ident x) !(ctx.global)
  then raise (Internal (AlreadyDeclared x))
  else upGlobal ctx (ident x) t e

let freshVar ns n = match Env.find_opt n ns with Some x -> x | None -> n
let mapFace fn phi = Env.fold (fun p d -> Env.add (fn p) d) phi Env.empty
let freshFace ns = mapFace (freshVar ns)

let actVar rho i = match Env.find_opt i rho with
  | Some v -> v
  | None   -> Var (i, VI)