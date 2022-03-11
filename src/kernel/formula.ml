open Language.Prelude
open Language.Spec
open Term
open Elab
open Rbv

let negDir : dir -> dir = function
  | Zero -> One | One -> Zero

let negAtom = fun (p, d) -> (p, negDir d)

(* simplify removes all conjunctions that are superset of another,
   i. e. xy ∨ x = (x ∧ y) ∨ (x ∧ 1) = x ∧ (y ∨ 1) = x ∧ 1 = x.
   It does not remove conjunctions like (x ∧ −x), because algebra of interval
   is not boolean, it is De Morgan algebra: distributive lattice with De Morgan laws.
   https://ncatlab.org/nlab/show/De+Morgan+algebra *)
let simplify t =
  let super x y = not (Conjunction.equal x y) && Conjunction.subset y x in
  Disjunction.filter (fun x -> not (Disjunction.exists (super x) t)) t

let compatible xs ys =
  Env.merge (fun _ x y -> match x, y with
    | Some d1, Some d2 -> Some (d1 = d2)
    | _,       _       -> Some true) xs ys
  |> Env.for_all (fun _ b -> b)

let leq xs ys =
  Env.for_all (fun k d1 -> match Env.find_opt k ys with
    | Some d2 -> d1 = d2
    | None    -> false) xs

let lt xs ys = not (Env.equal (=) xs ys) && leq xs ys

let comparable xs ys = leq xs ys || leq ys xs

let meet = Env.union (fun _ x y -> if x = y then Some x else raise IncompatibleFaces)

let nubRev xs =
  let ys = ref [] in
  List.iter (fun x ->
    if not (List.mem x !ys) then
      ys := x :: !ys) xs;
  !ys

let meets xs ys =
  let zs = ref [] in
  List.iter (fun x ->
    List.iter (fun y ->
      try zs := meet x y :: !zs
      with IncompatibleFaces -> ()) ys) xs;
  nubRev !zs

let meetss = List.fold_left meets [eps]

let forall i = System.filter (fun mu _ -> not (Env.mem i mu))

let mkSystem xs = System.of_seq (List.to_seq xs)
let unionSystem xs ys = System.union (fun _ _ _ -> raise (Failure "unionSystem")) xs ys (* ??? *)

let sign x = function
  | Zero -> ENeg (EVar x)
  | One  -> EVar x

let getFace xs = Env.fold (fun x d y -> EAnd (y, sign x d)) xs (EDir One)
let getFormula ts = System.fold (fun x _ e -> EOr (getFace x, e)) ts (EDir Zero)

let faceInj p x = Env.add p x Env.empty

let reduceSystem ts x =
  match System.find_opt eps ts with
  | Some v -> v
  | None   -> VApp (VSystem ts, x)

let faceAdd x d mu =
  match Env.find_opt x mu with
  | None    -> Some (Env.add x d mu)
  | Some d' -> if d = d' then Some (Env.add x d mu) else None

let disjZero k = List.map (fun (p, x) -> faceInj p (negDir x)) (Conjunction.elements k)

let disjOne (k : conjunction) : face option =
  Conjunction.elements k
  |> List.fold_left (fun nu (x, d) ->
    Option.bind nu (faceAdd x d)) (Some Env.empty)

let solve k x = match k, x with
  | Var (p, _), _     -> [faceInj p x]
  | VFormula ks, Zero -> meetss (List.map disjZero (Disjunction.elements ks))
  | VFormula ks, One  -> List.filter_map disjOne (Disjunction.elements ks)
  | _, _              -> raise (Internal (DNFSolverError (rbV k, x)))

let bimap f g ts =
  let ts' =
    System.fold (fun mu t ->
      Env.bindings mu
      |> List.rev_map (fun (i, d) -> solve (f i) d)
      |> meetss
      |> List.rev_map (fun nu -> (nu, g nu t))
      |> List.rev_append) ts [] in

  (* ensure incomparability *)
  List.filter (fun (alpha, _) ->
    not (List.exists (fun (beta, _) -> lt beta alpha) ts')) ts'
  |> mkSystem

let intersectionWith f =
  System.merge (fun _ x y ->
    match x, y with
    | Some a, Some b -> Some (f a b)
    | _,      _      -> None)

let unions t1 t2 =
  Disjunction.elements t2
  |> List.map (fun c -> Disjunction.map (Conjunction.union c) t1)
  |> List.fold_left Disjunction.union Disjunction.empty
  |> simplify

let unionss = List.fold_left unions (Disjunction.singleton Conjunction.empty)

let negConjunction : conjunction -> disjunction =
     Conjunction.elements
  >> List.map (negAtom >> Conjunction.singleton)
  >> Disjunction.of_list

let negDisjunction = Disjunction.elements >> List.map negConjunction >> unionss >> simplify

let orFormula v1 v2 = match v1, v2 with
  | Var (x, _), Var (y, _) -> VFormula (Disjunction.of_list [Conjunction.singleton (x, One); Conjunction.singleton (y, One)])
  | Var (x, _), VFormula t | VFormula t, Var (x, _) ->
    if top t then VFormula t
    else VFormula (Disjunction.filter (fun c -> not (Conjunction.mem (x, One) c)) t
                  |> Disjunction.add (Conjunction.singleton (x, One)))
  | VFormula t1, VFormula t2 -> VFormula (simplify (Disjunction.union t1 t2))
  | _, _ -> raise (Internal (ExpectedFormula (EOr (rbV v1, rbV v2))))

let andFormula v1 v2 = match v1, v2 with
  | Var (x, _), Var (y, _) -> VFormula (Disjunction.singleton (Conjunction.of_list [(x, One); (y, One)]))
  | Var (x, _), VFormula t | VFormula t, Var (x, _) ->
    VFormula (simplify (Disjunction.map (Conjunction.add (x, One)) t))
  | VFormula t1, VFormula t2 -> VFormula (unions t1 t2)
  | _, _ -> raise (Internal (ExpectedFormula (EAnd (rbV v1, rbV v2))))

let negFormula : value -> value = function
  | Var (p, _)  -> VFormula (Disjunction.singleton (Conjunction.singleton (p, Zero)))
  | VFormula ks -> VFormula (negDisjunction ks)
  | v           -> raise (Internal (ExpectedFormula (rbV v)))

let getFaceV xs = Env.fold (fun x d -> Conjunction.add (x, d)) xs Conjunction.empty
let getFormulaV ts = VFormula (System.fold (fun x _ -> Disjunction.add (getFaceV x)) ts Disjunction.empty)

let actVar rho i = match Env.find_opt i rho with
  | Some v -> v
  | None   -> Var (i, VI)

let boolNatural = function
  | Zero -> negDisjunction
  | One  -> id

let actConjunction rho k =
  Conjunction.elements k
  |> List.map (fun (p, d) -> boolNatural d (extFormula (actVar rho p)))
  |> unionss

let actDisjunction rho ks =
  VFormula (Disjunction.elements ks
           |> List.map (actConjunction rho)
           |> List.fold_left Disjunction.union Disjunction.empty
           |> simplify)
