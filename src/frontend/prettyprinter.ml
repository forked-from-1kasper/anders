open Language.Prelude
open Language.Spec
open Prefs

exception ExpectedDir of string
let getDir x = if x = !zeroPrim then Zero else if x = !onePrim then One else raise (ExpectedDir x)

let showIdent : ident -> string = function
  | Irrefutable -> "_"
  | Ident (p, n) -> if !indices then p ^ "#" ^ Int64.to_string n else p

let showDir : dir -> string = function | Zero -> !zeroPrim | One -> !onePrim

let showFace phi =
  if Env.is_empty phi then "(1 = 1)"
  else Env.bindings phi
       |> List.map (fun (x, d) -> Printf.sprintf "(%s = %s)" (showIdent x) (showDir d))
       |> String.concat " "

let showSystem show xs =
  System.bindings xs
  |> List.map (fun (x, e) -> Printf.sprintf "%s → %s" (showFace x) (show e))
  |> String.concat ", "

let parens b x = if b then "(" ^ x ^ ")" else x

let ppCosmos = function
  | Pretype -> "V"
  | Kan     -> "U"

let rec ppExp paren e = let x = match e with
  | EType (c, Finite (ELevelElem n)) -> ppCosmos c ^ showSubscript false n
  | EType (c, Finite e) -> ppCosmos c ^ " " ^ ppExp true e
  | EType (c, Omega n) -> ppCosmos c ^ "ω" ^ showSubscript false n
  | ELevel -> "L"
  | ELevelElem n -> "L" ^ showSubscript true n
  | ELSucc e -> Printf.sprintf "isucc %s" (ppExp true e)
  | EAdd (e1, e2) -> Printf.sprintf "iadd %s %s" (ppExp true e1) (ppExp true e2)
  | EMax (e1, e2) -> Printf.sprintf "imax %s %s" (ppExp true e1) (ppExp true e2)
  | ELam (a, (p, b)) -> Printf.sprintf "λ %s, %s" (showTeleExp (p, a)) (showExp b)
  | EPi (a, (p, b)) -> showPiExp a p b
  | ESig (a, (p, b)) -> Printf.sprintf "Σ %s, %s" (showTeleExp (p, a)) (showExp b)
  | EPair (_, fst, snd) -> Printf.sprintf "(%s, %s)" (showExp fst) (showExp snd)
  | EFst exp -> ppExp true exp ^ ".1"
  | ESnd exp -> ppExp true exp ^ ".2"
  | EField (exp, field) -> ppExp true exp ^ "." ^ field
  | EApp (f, x) -> Printf.sprintf "%s %s" (showExp f) (ppExp true x)
  | EVar p -> showIdent p
  | EHole -> "?"
  | EPLam (ELam (_, (i, e))) -> Printf.sprintf "<%s> %s" (showIdent i) (showExp e)
  | EPLam _ -> failwith "showExp: unreachable code was reached"
  | EAppFormula (f, x) -> Printf.sprintf "%s @ %s" (ppExp true f) (ppExp true x)
  | ESystem x -> Printf.sprintf "[%s]" (showSystem showExp x)
  | ESub (a, i, u) -> Printf.sprintf "%s[%s ↦ %s]" (ppExp true a) (showExp i) (showExp u)
  | EI -> !intervalPrim | EDir d -> showDir d
  | EAnd (a, b) -> Printf.sprintf "%s ∧ %s" (ppExp true a) (ppExp true b)
  | EOr (a, b) -> Printf.sprintf "%s ∨ %s" (ppExp true a) (ppExp true b)
  | ENeg a -> Printf.sprintf "-%s" (ppExp paren a)
  | ETransp (p, i) -> Printf.sprintf "transp %s %s" (ppExp true p) (ppExp true i)
  | EPathP e -> "PathP " ^ ppExp true e
  | EId e -> Printf.sprintf "Id %s" (ppExp true e)
  | ERef e -> Printf.sprintf "ref %s" (ppExp true e)
  | EJ e -> Printf.sprintf "idJ %s" (ppExp true e)
  | EHComp (t, r, u, u0) -> Printf.sprintf "hcomp %s %s %s %s" (ppExp true t) (ppExp true r) (ppExp true u) (ppExp true u0)
  | EPartial e -> Printf.sprintf "Partial %s" (ppExp true e)
  | EPartialP (t, r) -> Printf.sprintf "PartialP %s %s" (ppExp true t) (ppExp true r)
  | EInc (t, r) -> Printf.sprintf "inc %s %s" (ppExp true t) (ppExp true r)
  | EOuc e -> Printf.sprintf "ouc %s" (ppExp true e)
  | EGlue e -> Printf.sprintf "Glue %s" (ppExp true e)
  | EGlueElem (r, u, a) -> Printf.sprintf "glue %s %s %s" (ppExp true r) (ppExp true u) (ppExp true a)
  | EUnglue (r, u, e) -> Printf.sprintf "unglue %s %s %s" (ppExp true r) (ppExp true u) (ppExp true e)
  | EEmpty -> "𝟎" | EUnit -> "𝟏" | EBool -> "𝟐"
  | EStar -> "★" | EFalse -> "0₂" | ETrue -> "1₂"
  | EN -> "ℕ" | EZero -> "zero" | ESucc -> "succ"
  | EIndEmpty e -> Printf.sprintf "ind₀ %s" (ppExp true e)
  | EIndUnit e  -> Printf.sprintf "ind₁ %s" (ppExp true e)
  | EIndBool e  -> Printf.sprintf "ind₂ %s" (ppExp true e)
  | ENInd e -> Printf.sprintf "ℕ-ind %s" (ppExp true e)
  | EW (a, (p, b)) -> Printf.sprintf "W %s, %s" (showTeleExp (p, a)) (showExp b)
  | ESup (a, b) -> Printf.sprintf "sup %s %s" (ppExp true a) (ppExp true b)
  | EIndW e -> Printf.sprintf "indᵂ %s" (ppExp true e)
  | EIm e -> Printf.sprintf "ℑ %s" (ppExp true e)
  | EInf e -> Printf.sprintf "ℑ-unit %s" (ppExp true e)
  | EJoin e -> Printf.sprintf "ℑ-join %s" (ppExp true e)
  | EIndIm (a, b) -> Printf.sprintf "ind-ℑ %s %s" (ppExp true a) (ppExp true b)
  | ECoeq (f, g) -> Printf.sprintf "coeq %s %s" (ppExp true f) (ppExp true g)
  | EIota (f, g, x) -> Printf.sprintf "iota %s %s %s" (ppExp true f) (ppExp true g) (ppExp true x)
  | EResp (f, g, x) -> Printf.sprintf "resp %s %s %s" (ppExp true f) (ppExp true g) (ppExp true x)
  | EIndCoeq (e, i, r) -> Printf.sprintf "coeq-ind %s %s %s" (ppExp true e) (ppExp true i) (ppExp true r)
  | ETypeof e -> Printf.sprintf "typeof %s" (ppExp true e)
  | EDomainof e -> Printf.sprintf "domainof %s" (ppExp true e)
  in match e with
  | ELevel | ELevelElem _ | EType (_, Omega _) | EType (_, Finite (ELevelElem _))
  | EVar _ | EFst _ | ESnd _ | EI | ESystem _ | EHole | EDir _ | EPair _
  | ENeg _ | EEmpty | EUnit | EBool | EStar | EFalse | ETrue
  | EN     | EZero  | ESucc -> x
  | _ -> parens paren x

and showExp e = ppExp false e
and showTeleExp (p, x) = Printf.sprintf "(%s : %s)" (showIdent p) (showExp x)

and showPiExp a p b = match p with
  | Irrefutable -> Printf.sprintf "%s → %s" (ppExp true a) (showExp b)
  | _           -> Printf.sprintf "Π %s, %s" (showTeleExp (p, a)) (showExp b)
