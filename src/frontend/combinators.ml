open Language.Prelude

(* https://github.com/leanprover-community/lean/blob/master/library/data/buffer/parser.lean *)

type 'a parserResult =
  | Done of int * 'a
  | Fail of int * string list

type reader =
  { get  : int -> char;
    size : int }

type 'a parser = reader -> int -> 'a parserResult

let pure a = fun _ pos -> Done (pos, a)

let (>>=) x f =
  fun input pos -> match x input pos with
  | Done (pos, a)        -> f a input pos
  | Fail (pos, expected) -> Fail (pos, expected)

let (>>) x y  = x >>= fun _ -> y
let (<<) x y  = x >>= fun r -> y >>= fun _ -> pure r
let (<$>) f x = x >>= fun y -> pure (f y)
let (<*>) p q = p >>= fun f -> q >>= fun x -> pure (f x)

let fail msg = fun _ pos -> Fail (pos, [msg])
let failure  = fun _ pos -> Fail (pos, [])

let (<|>) p q = fun input pos ->
  match p input pos with
  | Fail (pos1, expected1) ->
    begin match q input pos with
    | Fail (pos2, expected2) ->
      if pos1 < pos2 then
        Fail (pos1, expected1)
      else if pos2 < pos1 then
        Fail (pos2, expected2)
      else Fail (pos1, List.append expected1 expected2)
    | ok -> ok
    end
  | ok -> ok

let decorateErrors msgs p =
  fun input pos -> match p input pos with
  | Fail _ -> Fail (pos, msgs)
  | ok     -> ok

let anyChar : char parser =
  fun input pos ->
    if pos < input.size then
      Done (pos + 1, input.get pos)
    else Fail (pos, [])

let sat p : char parser =
  fun input pos ->
    if pos < input.size then
      let c = input.get pos in
      if p c then Done (pos + 1, c) else Fail (pos, [])
    else Fail (pos, [])

let eps = pure ()

let ch c = sat ((=) c) >> eps |> decorateErrors [String.make 1 c]
let token s =
  Seq.fold_left (fun x c -> x >> ch c) eps (String.to_seq s)
  |> decorateErrors [s]

(* https://github.com/inhabitedtype/angstrom/blob/5536d1da71469b49f37076beb5f75d34f448da5e/lib/angstrom.ml#L457-L462 *)
let fix f = let rec p = lazy (f r) and r = fun input pos -> (Lazy.force p) input pos in r

let foldr f p b = fix (fun g -> f <$> p <*> g <|> pure b)

let optional p = p <|> eps

let optional1 p = (Option.some <$> p) <|> (eps >> pure None)

let many  p = foldr List.cons p []
let many1 p = List.cons <$> p <*> many p

let sepBy1 sep p = List.cons <$> p <*> many (sep >> p)
let sepBy  sep p = sepBy1 sep p <|> pure []

let stringOfList = String.of_seq % List.to_seq

let str0 p = stringOfList <$> many  (sat p)
let str  p = stringOfList <$> many1 (sat p)

let guard f p = p >>= fun x -> if f x then pure x else failure

let remaining = fun input pos -> Done (pos, input.size - pos)
let eof = decorateErrors ["<end-of-file>"] (guard ((=) 0) remaining >> eps)

let makeMonospaced = function
  | '\n' -> ' '
  | '\t' -> ' '
  | '\r' -> ' '
  | c    -> c

let mkErrorMsg input pos expected = let width = 10 in
    String.init (2 * width + 1) (fun idx -> makeMonospaced (input.get (pos - width + idx)))
  ^ "\n" ^ String.make width ' ' ^ "^\n" ^ "expected: " ^ String.concat " | " expected

let runParser p input pos = match p input pos with
  | Done (pos, r)        -> Ok (pos, r)
  | Fail (pos, expected) -> Error (mkErrorMsg input pos expected)

let ofString s : reader =
  { size = String.length s;
    get  = fun n -> if n < 0 || n >= String.length s then ' '
                    else String.get s n }

let ofChan ch : reader =
  let size = in_channel_length ch in
  { size = size;
    get  = fun n -> if n < 0 || n >= size then ' '
                    else (seek_in ch n; input_char ch) }
