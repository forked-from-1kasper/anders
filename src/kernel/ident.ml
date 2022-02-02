open Language.Spec

let showName : name -> string = function
  | Irrefutable -> "_"
  | Name (p, n) -> if !Prefs.indices then p ^ "#" ^ string_of_int n else p

let keys ts = List.of_seq (Seq.map fst (System.to_seq ts))
let intersectionWith f =
  System.merge (fun _ x y ->
    match x, y with
    | Some a, Some b -> Some (f a b)
    | _,      _      -> None)

module Files = Set.Make(String)

let gidx : int ref = ref 0
let gen () = gidx := !gidx + 1; !gidx

let fresh : name -> name = function
  | Irrefutable -> Irrefutable | Name (p, _) -> Name (p, gen ())

let matchIdent p : name -> bool = function
  | Irrefutable -> false | Name (q, _) -> p = q

let getDigit x = Char.chr (Z.to_int x + 0x80) |> Printf.sprintf "\xE2\x82%c"

let ten = Z.of_int 10

let rec showSubscript x =
  if Z.lt x Z.zero then failwith "showSubscript: expected positive integer"
  else if Z.equal x Z.zero then "" else let (y, d) = Z.div_rem x ten in
    showSubscript y ^ getDigit d

let freshName x = let n = gen () in Name (x ^ showSubscript (Z.of_int n), n)

module Atom =
struct
  type t = name * dir
  let compare (a, x) (b, y) =
    if a = b then Dir.compare x y else Name.compare a b
end

module Conjunction = Set.Make(Atom)
type conjunction = Conjunction.t

module Disjunction = Set.Make(Conjunction)
type disjunction = Disjunction.t

let zeroPrim     = ref "0"
let onePrim      = ref "1"
let intervalPrim = ref "I"

exception ExpectedDir of string
let getDir x = if x = !zeroPrim then Zero else if x = !onePrim then One else raise (ExpectedDir x)
