open Language.Spec
open Prefs

let showIdent : ident -> string = function
  | Irrefutable -> "_"
  | Ident (p, n) -> if !indices then p ^ "#" ^ Int64.to_string n else p

let gidx : int64 ref = ref 0L
let gen () = gidx := Int64.succ !gidx; !gidx

let fresh : ident -> ident = function
  | Irrefutable -> Irrefutable | Ident (p, _) -> Ident (p, gen ())

let matchIdent p : ident -> bool = function
  | Irrefutable -> false | Ident (q, _) -> p = q

let getDigit x = Char.chr (Z.to_int x + 0x80) |> Printf.sprintf "\xE2\x82%c"

let ten = Z.of_int 10

let rec showSubscript x =
  if Z.lt x Z.zero then failwith "showSubscript: expected positive integer"
  else if Z.equal x Z.zero then "" else let (y, d) = Z.div_rem x ten in
    showSubscript y ^ getDigit d

let freshName x = let n = gen () in Ident (x ^ showSubscript (Z.of_int64 n), n)

exception ExpectedDir of string
let getDir x = if x = !zeroPrim then Zero else if x = !onePrim then One else raise (ExpectedDir x)
