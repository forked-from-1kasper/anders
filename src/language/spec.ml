type name =
  | Irrefutable
  | Name of string * int

module Name =
struct
  type t = name
  let compare x y =
    match (x, y) with
    | Irrefutable, Irrefutable -> 0
    | Irrefutable, Name _ -> -1
    | Name _, Irrefutable -> 1
    | Name (p, a), Name (q, b) ->
      if p = q then compare a b
      else compare p q
end

module Env = Map.Make(Name)

type dir = Zero | One

module Dir =
struct
  type t = dir
  let compare a b =
    match a, b with
    | One, Zero -> 1
    | Zero, One -> -1
    | _, _      -> 0
end

type face = dir Env.t

module Face =
struct
  type t = face
  let compare = Env.compare Dir.compare
end

module System = Map.Make(Face)

type tag = (string option) ref

(* Language Expressions *)

type exp =
  | EPre of Z.t | EKan of Z.t                                                          (* cosmos *)
  | EVar of name | EHole                                                            (* variables *)
  | EPi of exp * (name * exp) | ELam of exp * (name * exp) | EApp of exp * exp             (* pi *)
  | ESig of exp * (name * exp) | EPair of tag * exp * exp                               (* sigma *)
  | EFst of exp | ESnd of exp | EField of exp * string                    (* simga elims/records *)
  | EId of exp | ERef of exp | EJ of exp                                      (* strict equality *)
  | EPathP of exp | EPLam of exp | EAppFormula of exp * exp                     (* path equality *)
  | EI | EDir of dir | EAnd of exp * exp | EOr of exp * exp | ENeg of exp       (* CCHM interval *)
  | ETransp of exp * exp | EHComp of exp * exp * exp * exp                     (* Kan operations *)
  | EPartial of exp | EPartialP of exp * exp | ESystem of exp System.t      (* partial functions *)
  | ESub of exp * exp * exp | EInc of exp * exp | EOuc of exp                (* cubical subtypes *)
  | EGlue of exp | EGlueElem of exp * exp * exp | EUnglue of exp * exp * exp          (* glueing *)
  | EEmpty | EIndEmpty of exp                                                               (* 𝟎 *)
  | EUnit | EStar | EIndUnit of exp                                                         (* 𝟏 *)
  | EBool | EFalse | ETrue | EIndBool of exp                                                (* 𝟐 *)
  | EW of exp * (name * exp) | ESup of exp * exp | EIndW of exp * exp * exp                 (* W *)
  | EIm of exp | EInf of exp | EIndIm of exp * exp | EJoin of exp      (* Infinitesimal Modality *)

type extension =
  | ECoeq of exp | EIota of exp | EResp of exp | EIndCoeq of exp                  (* Coequalizer *)
  | EDisc of exp | EBase of exp | EHub of exp | ESpoke of exp | EIndDisc of exp          (* Disc *)
