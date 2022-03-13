open Language.Spec
open Term
open Rbv

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
