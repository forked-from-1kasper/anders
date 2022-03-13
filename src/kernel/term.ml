open Language.Spec

module Atom =
struct
  type t = ident * dir
  let compare (a, x) (b, y) =
    if a = b then Dir.compare x y else Ident.compare a b
end

module Conjunction = Set.Make(Atom)
type conjunction = Conjunction.t

module Disjunction = Set.Make(Conjunction)
type disjunction = Disjunction.t

type scope = Local | Global

(* Intermediate type checker values *)

type value =
  | VKan of Z.t | VPre of Z.t
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
  | W of value * clos | VSup of value * value | VIndW of value * value * value
  | VIm of value | VInf of value | VIndIm of value * value | VJoin of value

and clos = ident * (value -> value)

type term = Exp of exp | Value of value

and record = scope * term * term

and ctx = record Env.t

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

let upVar p x ctx = match p with Irrefutable -> ctx | _ -> Env.add p x ctx
let upLocal ctx p t v = upVar p (Local, Value t, Value v) ctx
let upGlobal ctx p t v = upVar p (Global, Value t, Value v) ctx

let isGlobal : record -> bool = function Global, _, _ -> false | Local, _, _ -> true
let freshVar ns n = match Env.find_opt n ns with Some x -> x | None -> n
let mapFace fn phi = Env.fold (fun p d -> Env.add (fn p) d) phi Env.empty
let freshFace ns = mapFace (freshVar ns)

exception Internal of error
exception IncompatibleFaces