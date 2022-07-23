open Language.Prelude
open Language.Spec
open Term
open Rbv

module Level =
struct
  let succ = function
    | Finite xs -> Finite (Maximum.succ xs)
    | Omega n   -> Omega (Z.succ n)

  let max a b = match a, b with
    | Omega n,   Omega m   -> Omega (Z.max n m)
    | Omega n,   _         -> Omega n
    | _,         Omega m   -> Omega m
    | Finite xs, Finite ys -> Finite (Maximum.max xs ys)

  let equal u v : bool = !Prefs.girard || match u, v with
    | Omega n,   Omega m   -> Z.equal n m
    | Finite xs, Finite ys -> Maximum.equal xs ys
    | _,         _         -> false
end

let imax a b = match a, b with
  | VType (c1, l1), VType (c2, l2) -> VType (Cosmos.max c1 c2, Level.max l1 l2)
  | VType _, _ -> raise (Internal (ExpectedType (rbV b)))
  | _, _ -> raise (Internal (ExpectedType (rbV a)))

let impred a b = match a, b with
  | VType (c1, _), VType (c2, l) -> VType (Cosmos.max c1 c2, l)
  | VType _, _ -> raise (Internal (ExpectedType (rbV b)))
  | _, _ -> raise (Internal (ExpectedType (rbV a)))

let extLevel = function
  | VLevelElem ts -> ts
  | Var (x, _)    -> Maximum.singleton (Z.zero, Idents.singleton x)
  | v             -> raise (Internal (ExpectedLevel (rbV v)))

let levelSucc v    = VLevelElem (Maximum.succ (extLevel v))
let levelMax v1 v2 = VLevelElem (Maximum.max (extLevel v1) (extLevel v2))
let levelAdd v1 v2 = VLevelElem (Maximum.add (extLevel v1) (extLevel v2))

let finite n  = Finite (Maximum.singleton (n, Idents.empty))
let pretype n = VType (Pretype, finite n)
let kan n     = VType (Kan, finite n)

let isType = function
  | VType _ -> ()
  | v       -> raise (Internal (ExpectedType (rbV v)))

let isKan = function
  | VType (Kan, _) -> ()
  | v              -> raise (Internal (ExpectedKan (rbV v)))

let extType = function
  | VType (_, l) -> l
  | v            -> raise (Internal (ExpectedType (rbV v)))

let actIdents rho k =
  Idents.elements k
  |> List.map (extLevel % actVar rho)
  |> Maximum.adds

let actMaximum rho ks =
  Maximum.elements ks
  |> List.map (fun (n, x) -> Maximum.plus n (actIdents rho x))
  |> List.fold_left Maximum.union Maximum.empty
  |> Maximum.simplify
