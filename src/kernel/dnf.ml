open Language.Prelude
open Language.Spec
open Term
open Elab
open Rbv

let negAtom = fun (p, d) -> (p, negDir d)

(* simplify removes all conjunctions that are superset of another,
   i. e. xy ∨ x = (x ∧ y) ∨ (x ∧ 1) = x ∧ (y ∨ 1) = x ∧ 1 = x.
   It does not remove conjunctions like (x ∧ −x), because algebra of interval
   is not boolean, it is De Morgan algebra: distributive lattice with De Morgan laws.
   https://ncatlab.org/nlab/show/De+Morgan+algebra *)
let simplify t =
  let super x y = not (Conjunction.equal x y) && Conjunction.subset y x in
  Disjunction.filter (fun x -> not (Disjunction.exists (super x) t)) t

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
