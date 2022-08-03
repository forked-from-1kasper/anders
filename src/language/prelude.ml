let id = fun x -> x

let flip f a b = f b a

let curry f x y = f (x, y)
let uncurry f (x, y) = f x y

let (%) f g x = f (g x)

let cutAtBegin s prefix =
  let len1 = String.length prefix in
  let len2 = String.length s in

  let rec loop idx =
    if idx = len1 then Some (prefix, String.sub s len1 (len2 - len1))
    else if String.get prefix idx <> String.get s idx then None
    else loop (idx + 1) in

  if len1 > len2 then None else loop 0

let cutAtEnd s postfix =
  let len1 = String.length postfix in
  let len2 = String.length s in

  let rec loop idx =
    if idx > len1 then Some (postfix, String.sub s 0 (len2 - len1))
    else if String.get postfix (len1 - idx)
         <> String.get s (len2 - idx) then None
    else loop (idx + 1) in

  if len1 > len2 then None else loop 1

let initLast xs =
  let rec func xs = function
    | []      -> failwith "initLast: expected non-empty list"
    | [y]     -> (xs, y)
    | y :: ys -> func (y :: xs) ys in
  let (ys, y) = func [] xs in (List.rev ys, y)

let splitWhile p =
  let rec go xs = function
    | y :: ys when p y -> go (y :: xs) ys
    | ys               -> List.rev xs, ys
  in go []

let splitBy sep =
  let rec go xs ys = function
    | z :: zs when z = sep -> go [] (List.rev xs :: ys) zs
    | z :: zs              -> go (z :: xs) ys zs
    | []                   -> List.rev (List.rev xs :: ys)
  in function [] -> [] | zs -> go [] [] zs

let isEmpty = function
  | [] -> true
  | _  -> false

exception TooFewArguments

let take1 = function
  | x :: xs -> (x, xs)
  | _       -> raise TooFewArguments

let take2 = function
  | x :: y :: ys -> (x, y, ys)
  | _            -> raise TooFewArguments

let take3 = function
  | x :: y :: z :: zs -> (x, y, z, zs)
  | _                 -> raise TooFewArguments

let take4 = function
  | x :: y :: z :: w :: ws -> (x, y, z, w, ws)
  | _                      -> raise TooFewArguments

let singleton value = [value]

(* https://github.com/ocaml/ocaml/blob/trunk/stdlib/list.ml *)
let rec listEqual fn xs ys =
  match xs, ys with
  | [], [] -> true
  | [], _ :: _ | _ :: _, [] -> false
  | x :: xs, y :: ys -> fn x y && listEqual fn xs ys

let rec findMap f = function
  |   []    -> None
  | x :: xs ->
    match f x with
    | None -> findMap f xs
    | y    -> y

let getDigit x = Char.chr (Z.to_int x + 0x80) |> Printf.sprintf "\xE2\x82%c"

let ten = Z.of_int 10

let rec showSubscript printZero x =
  if Z.lt x Z.zero then failwith "showSubscript: expected positive integer"
  else if Z.equal x Z.zero then (if printZero then "₀" else "")
  else let (y, d) = Z.div_rem x ten in showSubscript false y ^ getDigit d

module ListRef =
struct
  exception Failure
  type 'a t = 'a list ref

  let ofList xs : 'a t = ref xs

  let peek ptr =
    match !ptr with
    |   []   -> None
    | x :: _ -> Some x

  let next ptr =
    match !ptr with
    |   []    -> raise Failure
    | x :: xs -> (ptr := xs; x)

  let drop ptr =
    match !ptr with
    |   []    -> ()
    | _ :: xs -> ptr := xs

  let junk ptr = drop ptr; ptr

  let isEmpty ptr =
    match !ptr with
    |   []   -> true
    | _ :: _ -> false

  let takeWhile pred stream =
    let rec loop buf =
      match peek stream with
      | Some t when pred t -> (drop stream; loop (t :: buf))
      | _                  -> List.rev buf
    in loop []
end