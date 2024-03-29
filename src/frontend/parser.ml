open Language.Prelude
open Prettyprinter
open Language.Spec
open Combinators
open Module
open Prefs

module Dict = Map.Make(String)
module Set  = Set.Make(String)

let rec replace x e = function
  | Atom y       -> if x = y then e else Atom y
  | Node (c, ys) -> Node (c, List.map (replace x e) ys)

exception InvalidSyntax of syntax
exception ExpectedIdent of syntax
exception ExpectedNode  of syntax

exception OpConflict        of syntax * syntax
exception UnexpectedInfix   of string
exception UnexpectedPostfix of string

let mkIdent = ident

let expandIdent = function
  | Atom x -> ident x
  | e      -> raise (ExpectedIdent e)

let takeParens = function
  | Node ('(', es) -> es
  | e              -> [e]

let traceParser es = Printf.printf "When trying to parse\n  %s\n" (showStxs es)

let expandNode = function
  | Node ('(', es) -> es
  | e              -> raise (ExpectedNode e)

let unpackBinder xs = let (ys, zs) = splitWhile ((<>) (Atom ":")) (expandNode xs) in (ys, List.tl zs)

(* second stage parser *)
let builtinInfix = ["-",   (Prefix,      1000.0); "@",   (Infix Left,  10.0);
                    "∧",   (Infix Right, 20.0);   "∨",   (Infix Right, 30.0);
                    "/\\", (Infix Right, 20.0);   "\\/", (Infix Right, 30.0);
                    "→",   (Infix Right, 40.0);   "×",   (Infix Right, 60.0)]
let operators = ref (Dict.of_seq (List.to_seq builtinInfix))

let isQuantifier s = s = "W" || s = "Π" || s = "Σ" || s = "λ"

let mkApp f x = match f with
  | Node ('(', xs) -> paren (xs @ [x])
  | t              -> paren [t; x]

let getPrecedence = function
  | Atom t -> Dict.find_opt t !operators
  | Node _ -> None

let takeUntilToken stream t = ListRef.takeWhile ((<>) (Atom t)) stream

let mapsto = Atom "↦"

(* https://github.com/gabrielhdt/pratter/blob/master/pratter.ml *)
let rec nud stream = function
  | Node ('<', is)                         -> paren [Node ('<', is); pratter stream]
  | Node ('[', es) when List.mem mapsto es -> let (is, xs) = splitWhile ((<>) mapsto) es in
                                              Node ('[', [prattSigma is; mapsto; prattSigma (List.tl xs)])
  | Node ('[', es)                         -> prattSystem es
  | Node (_,   es)                         -> prattSigma es
  | Atom "let"                             ->
    let i = ListRef.next stream in
    begin match ListRef.next stream with
      | Atom ":"  ->
        let e1 = prattSigma (takeUntilToken stream ":=") in ListRef.drop stream;
        let e2 = prattSigma (takeUntilToken stream "in") in ListRef.drop stream;
        Node ('(', [Atom "let"; i; Atom ":"; e1; Atom ":="; e2; Atom "in"; pratter stream])
      | Atom ":=" ->
        let e0 = prattSigma (takeUntilToken stream "in") in ListRef.drop stream;
        Node ('(', [Atom "let"; i; Atom ":="; e0; Atom "in"; pratter stream])
      | e         -> raise (InvalidSyntax e)
    end
  | Atom x when isQuantifier x             ->
    let xs = List.map prattBinder (takeUntilToken stream ",") in
    paren [paren (Atom x :: xs); Atom ","; pratter (ListRef.junk stream)]
  | Atom x -> match Dict.find_opt x !operators with
    | Some (Prefix, _)  -> paren [Atom x; nud stream (ListRef.next stream)]
    | Some (Infix _, _) -> raise (UnexpectedInfix x)
    | Some (Postfix, _) -> raise (UnexpectedPostfix x)
    | _                 -> Atom x

and prattBinder e = let (is, es) = unpackBinder e in
  paren [paren is; Atom ":"; prattSigma es]

and led assoc bp stream left t =
  let rbp = match assoc with
    | Right          -> bp *. (1. -. epsilon_float)
    | Left | Neither -> bp
  in paren [left; t; expression rbp assoc stream]

and expression rbp rassoc stream =
  let rec loop left =
    match ListRef.peek stream with
    | None | Some (Atom ",") -> left
    | Some t ->
    begin
      match getPrecedence t with
      | Some (Infix lassoc, lbp) ->
        if lbp > rbp || (lbp = rbp && lassoc = Right && rassoc = Right)
        then loop (led lassoc lbp (ListRef.junk stream) left t)
        else if lbp < rbp || (lbp = rbp && lassoc = Left && rassoc = Left)
        then left else raise (OpConflict (left, t))
      | Some (Postfix, lbp) ->
        if lbp > rbp then begin
          let (es, e) = initLast (takeParens left) in
          ListRef.drop stream; loop (paren (es @ [paren [e; t]]))
        end
        else if lbp = rbp then raise (OpConflict (left, t))
        else left
      | Some (Prefix, _) | None ->
        let next = nud stream (ListRef.next stream) in
        loop (mkApp left (prattProj stream next))
    end in
  try loop (paren [prattProj stream (nud stream (ListRef.next stream))])
  with ListRef.Failure -> raise TooFewArguments

and pratter stream = expression neg_infinity Neither stream

and prattProj stream stx =
  match ListRef.peek stream with
  | Some (Atom ".") -> let next = ListRef.next (ListRef.junk stream) in
                       prattProj stream (paren [stx; Atom "."; nud stream next])
  | _               -> stx

and prattSigma xs =
  let rec loop stream =
    let stx = pratter stream in
    match ListRef.peek stream with
    | Some (Atom ",") -> paren [stx; Atom ","; loop (ListRef.junk stream)]
    | Some e          -> raise (InvalidSyntax e)
    | None            -> stx in
  try loop (ListRef.ofList xs)
  with ex -> traceParser xs; raise ex

and prattSystem es =
  let rec loop stream buf =
    if ListRef.isEmpty stream then List.rev buf
    else
      let xs = takeUntilToken stream "→" in
      let e  = pratter (ListRef.junk stream) in
      loop (ListRef.junk stream) (paren [paren xs; e] :: buf)
  in try Node ('[', loop (ListRef.ofList es) [])
  with ex -> traceParser es; raise ex

and unpack = function
  | Node ('(', xs) -> prattSigma xs
  | Node ('[', es) -> prattSystem es
  | t              -> t

let numSubscript =
  ["₀"; "₁"; "₂"; "₃"; "₄"; "₅"; "₆"; "₇"; "₈"; "₉"]
  |> List.mapi (fun idx s -> token s >> pure idx)
  |> List.fold_left (<|>) failure

let ten = Z.of_int 10

let getLevel ns = let m = ref Z.zero in
  List.iter (fun n -> m := Z.add (Z.mul !m ten) (Z.of_int n)) ns; !m

let level = getLevel <$> many numSubscript

let etype x y c =
      (token x >> level >>= fun n -> pure (EType (c, Finite (ELevelElem n))))
  <|> (token y >> level >>= fun n -> pure (EType (c, Omega n)))

let kan     = etype "U" "Uω" Kan
let pretype = etype "V" "Vω" Pretype
let level   = token "L" >> many1 numSubscript >>= fun n -> pure (ELevelElem (getLevel n))
let indexed = (kan <|> pretype <|> level) << eof

let getConstants () = [(!intervalPrim, EI); (!zeroPrim, EDir Zero); (!onePrim, EDir One)]
let getVar x = match List.assoc_opt x (getConstants ()) with Some e -> e | None -> decl x

type prim =
  | Nullary    of exp
  | Unary      of (exp -> exp)
  | Binary     of (exp -> exp -> exp)
  | Ternary    of (exp -> exp -> exp -> exp)
  | Quaternary of (exp -> exp -> exp -> exp -> exp)

let getPrim = function
  | "hcomp"    -> Quaternary (fun e1 e2 e3 e4 -> EHComp (e1, e2, e3, e4))
  | "glue"     -> Ternary    (fun e1 e2 e3    -> EGlueElem (e1, e2, e3))
  | "unglue"   -> Ternary    (fun e1 e2 e3    -> EUnglue (e1, e2, e3))
  | "iota"     -> Ternary    (fun e1 e2 e3    -> EIota (e1, e2, e3))
  | "resp"     -> Ternary    (fun e1 e2 e3    -> EResp (e1, e2, e3))
  | "coeq-ind" -> Ternary    (fun e1 e2 e3    -> EIndCoeq (e1, e2, e3))
  | "transp"   -> Binary     (fun e1 e2       -> ETransp (e1, e2))
  | "PartialP" -> Binary     (fun e1 e2       -> EPartialP (e1, e2))
  | "inc"      -> Binary     (fun e1 e2       -> EInc (e1, e2))
  | "sup"      -> Binary     (fun e1 e2       -> ESup (e1, e2))
  | "coeq"     -> Binary     (fun e1 e2       -> ECoeq (e1, e2))
  | "iadd"     -> Binary     (fun e1 e2       -> EAdd (e1, e2))
  | "imax"     -> Binary     (fun e1 e2       -> EMax (e1, e2))
  | "ind-ℑ"    -> Binary     (fun e1 e2       -> EIndIm (e1, e2))
  | "Id"       -> Unary      (fun e           -> EId e)
  | "ref"      -> Unary      (fun e           -> ERef e)
  | "idJ"      -> Unary      (fun e           -> EJ e)
  | "ouc"      -> Unary      (fun e           -> EOuc e)
  | "PathP"    -> Unary      (fun e           -> EPathP e)
  | "Glue"     -> Unary      (fun e           -> EGlue e)
  | "Partial"  -> Unary      (fun e           -> EPartial e)
  | "ind₀"     -> Unary      (fun e           -> EIndEmpty e)
  | "ind₁"     -> Unary      (fun e           -> EIndUnit e)
  | "ind₂"     -> Unary      (fun e           -> EIndBool e)
  | "ℕ-ind"    -> Unary      (fun e           -> ENInd e)
  | "indᵂ"     -> Unary      (fun e           -> EIndW e)
  | "ℑ"        -> Unary      (fun e           -> EIm e)
  | "ℑ-unit"   -> Unary      (fun e           -> EInf e)
  | "ℑ-join"   -> Unary      (fun e           -> EJoin e)
  | "isucc"    -> Unary      (fun e           -> ELSucc e)
  | "-"        -> Unary      (fun e           -> ENeg e)
  | "typeof"   -> Unary      (fun e           -> ETypeof e)
  | "domainof" -> Unary      (fun e           -> EDomainof e)
  | "𝟎"        -> Nullary    EEmpty
  | "empty"    -> Nullary    EEmpty
  | "𝟏"        -> Nullary    EUnit
  | "unit"     -> Nullary    EUnit
  | "𝟐"        -> Nullary    EBool
  | "bool"     -> Nullary    EBool
  | "★"        -> Nullary    EStar
  | "star"     -> Nullary    EStar
  | "0₂"       -> Nullary    EFalse
  | "false"    -> Nullary    EFalse
  | "1₂"       -> Nullary    ETrue
  | "true"     -> Nullary    ETrue
  | "ℕ"        -> Nullary    EN
  | "nat"      -> Nullary    EN
  | "zero"     -> Nullary    EZero
  | "succ"     -> Nullary    ESucc
  | "L"        -> Nullary    ELevel
  | "?"        -> Nullary    EHole
  | ":="       -> raise      (InvalidSyntax (Atom ":="))
  | x          -> Nullary    (getVar x)

let getInfix = function
  | "∨" | "\\/" -> Some (fun e1 e2 -> EOr (e1, e2))
  | "∧" | "/\\" -> Some (fun e1 e2 -> EAnd (e1, e2))
  | "→"         -> Some (fun e1 e2 -> impl e1 e2)
  | "×"         -> Some (fun e1 e2 -> prod e1 e2)
  | "@"         -> Some (fun e1 e2 -> EAppFormula (e1, e2))
  | _           -> None

let appStx fn es e = List.fold_left eApp e (List.map fn es)

let primExpander fn = function
  | Node ('(', Atom x :: es) ->
  begin match getPrim x with
    | Nullary    e -> Some (appStx fn es e)
    | Unary      g -> let (x, xs)          = take1 es in Some (appStx fn xs (g (fn x)))
    | Binary     g -> let (x, y, ys)       = take2 es in Some (appStx fn ys (g (fn x) (fn y)))
    | Ternary    g -> let (x, y, z, zs)    = take3 es in Some (appStx fn zs (g (fn x) (fn y) (fn z)))
    | Quaternary g -> let (x, y, z, w, ws) = take4 es in Some (appStx fn ws (g (fn x) (fn y) (fn z) (fn w)))
  end
  | Atom x ->
  begin match getPrim x with
    | Nullary e -> Some e
    | _         -> raise TooFewArguments
  end
  | _ -> None

let expandIndexed x =
  match runParser indexed (ofString x) 0 with
  | Ok (_, e) -> Some e
  | Error _   -> None

let cosmosExpander fn = function
  | Node ('(', Atom "U" :: e :: es) -> Some (appStx fn es (EType (Kan,     Finite (fn e))))
  | Node ('(', Atom "V" :: e :: es) -> Some (appStx fn es (EType (Pretype, Finite (fn e))))
  | Node ('(', Atom x :: es)        -> Option.map (appStx fn es) (expandIndexed x)
  | Atom x                          -> expandIndexed x
  | _                               -> None

let infixExpander fn = function
  | Node ('(', [a; Atom x; b]) -> Option.map (fun g -> g (fn a) (fn b)) (getInfix x)
  | _                          -> None

let expandBinder fn = function
  | is :: Atom ":" :: es -> let e = fn (paren es)
    in List.map (fun i -> (expandIdent i, e)) (takeParens is)
  | e                    -> raise (InvalidSyntax (paren e))

let expandBinders fn es = List.concat (List.map (expandBinder fn % expandNode) es)
let expandQuantifier fn c es e = List.fold_right (fun (i, t) -> c i t) (expandBinders fn es) (fn e)

let rec pLam e = function [] -> e | x :: xs -> EPLam (ELam (EI, (x, pLam e xs)))

type formula =
  | Falsehood
  | Equation of ident * dir
  | Truth

let extEquation : formula -> ident * dir = function
  | Equation (x, d) -> (x, d)
  | _               -> raise (Failure "extEquation")

let parseFace xs =
  if List.mem Falsehood xs then None
  else if List.mem Truth xs then Some Env.empty
  else Some (Env.of_seq (Seq.map extEquation (List.to_seq xs)))

let parsePartial xs e = Option.map (fun ys -> (ys, e)) (parseFace xs)

let expandEquation e = match e with
  | Node ('(', [Atom p; Atom "="; Atom d]) ->
  begin match getVar p, getDir d with
    | EDir d1, d2 -> if d1 = d2 then Truth else Falsehood
    | EVar x,  d  -> Equation (x, d)
    | _,       _  -> raise (InvalidSyntax e)
  end
  | e -> raise (InvalidSyntax e)

let expandFace = List.map expandEquation

let expandClause fn = function
  | Node ('(', [Node ('(', fs); e]) -> parsePartial (expandFace fs) (fn e)
  | e                               -> raise (InvalidSyntax e)

let expandSystem fn = System.of_seq % Seq.filter_map (expandClause fn) % List.to_seq

let quantifierExpander fn = function
  | Node ('(', [Atom "let"; i; Atom ":"; e1; Atom ":="; e2; Atom "in"; e3]) -> Some (ELet (Some (fn e1), fn e2, (expandIdent i, fn e3)))
  | Node ('(', [Atom "let"; i; Atom ":="; e1; Atom "in"; e2])               -> Some (ELet (None, fn e1, (expandIdent i, fn e2)))
  | Node ('(', [Node ('<', is); e])                                         -> Some (pLam (fn e) (List.map expandIdent is))
  | Node ('(', [Node ('(', Atom "λ" :: bs); Atom ","; e])                   -> Some (expandQuantifier fn eLam bs e)
  | Node ('(', [Node ('(', Atom "Π" :: bs); Atom ","; e])                   -> Some (expandQuantifier fn ePi  bs e)
  | Node ('(', [Node ('(', Atom "Σ" :: bs); Atom ","; e])                   -> Some (expandQuantifier fn eSig bs e)
  | Node ('(', [Node ('(', Atom "W" :: bs); Atom ","; e])                   -> Some (expandQuantifier fn eW   bs e)
  | _                                                                       -> None

let lowExpander fn = function
  | Node ('(', [e1; Atom ","; e2])                  -> Some (EPair (ref None, fn e1, fn e2))
  | Node ('(', [e; Atom "."; Atom "1"])             -> Some (EFst (fn e))
  | Node ('(', [e; Atom "."; Atom "2"])             -> Some (ESnd (fn e))
  | Node ('(', [e; Atom "."; Atom x])               -> Some (EField (fn e, x))
  | Node ('(', [e; Node ('[', [is; Atom "↦"; t])]) -> Some (ESub (fn e, fn is, fn t))
  | _                                               -> None

let simpleExpander fn = function
  | Node ('(', e :: es) -> Some (appStx fn es (fn e))
  | Node ('[', es)      -> Some (ESystem (expandSystem fn es))
  | _                   -> None

let rec traverseExpanders g e = function
  |   []    -> None
  | f :: fs ->
    match f g e with
    | None -> traverseExpanders g e fs
    | t    -> t

let expanders = [quantifierExpander; lowExpander; infixExpander; cosmosExpander; primExpander; simpleExpander]

let rec expandTerm e =
  try match traverseExpanders expandTerm e expanders with
  | None   -> raise (InvalidSyntax e)
  | Some t -> t
  with ex -> traceParser (takeParens e); raise ex

type macro =
  { variables : Set.t;
    pattern   : syntax;
    value     : syntax }

let rec matchAgainst ns vbs e0 e1 = match e0, e1 with
  | Atom x, _ when Set.mem x vbs   ->
  begin match Dict.find_opt x ns with
    | Some e2 -> if e1 = e2 then Some ns else None
    | None    -> Some (Dict.add x e1 ns)
  end
  | Atom x, Atom y when x = y      -> Some ns
  | Node (c1, xs), Node (c2, ys)   ->
    if c1 <> c2 || List.length xs <> List.length ys then None
    else List.fold_left2 (fun b t0 t1 -> Option.bind b (fun ns0 -> matchAgainst ns0 vbs t0 t1))
                         (Some ns) xs ys
  | _,       _                     -> None

let rec multiSubst ns = function
  | Atom x when Dict.mem x ns -> Dict.find x ns
  | Atom y                    -> Atom y
  | Node (c, xs)              -> Node (c, List.map (multiSubst ns) xs)

let variables = ref Set.empty
let macros    = ref []

let rec collectVariables vbs = function
  | Atom x when Set.mem x !variables -> Set.add x vbs
  | Atom _                           -> vbs
  | Node (_, es)                     -> List.fold_left collectVariables vbs es

let rec findMacro e = function
  | []      -> None
  | m :: ms -> match matchAgainst Dict.empty m.variables m.pattern e with
    | None    -> findMacro e ms
    | Some ns -> Some (multiSubst ns m.value)

let expandExterior e0 =
  match findMacro e0 !macros with
  | Some e -> e
  | None   -> e0

let rec macroexpand e =
  match expandExterior e with
  | Node ('[', ts) -> Node ('[', List.map macroexpandClause ts)
  | Node (c, es)   -> Node (c, List.map macroexpand es)
  | t              -> t

and macroexpandClause = function
  | Node ('(', [f; e]) -> paren [f; macroexpand e]
  | e                  -> e

let upMacro isUnsafe e1 e2 =
  let vbs   = collectVariables Set.empty e1 in
  let value = if isUnsafe then e2 else unpack e2 in
  macros := { variables = vbs; pattern = e1; value = macroexpand value } :: !macros

let upMacrovars = List.iter (fun i -> variables := Set.add i !variables)

let macroelab = macroexpand % unpack
let elab = expandTerm % macroelab

(* first stage parser *)
let negate g = fun x -> not (g x)
let isWhitespace c = c = ' ' || c = '\n' || c = '\t' || c = '\t'

let ws       = str isWhitespace >> eps
let nl       = str (fun c -> c = '\n' || c = '\r') >> eps
let keywords = ["def"; "definition"; "theorem"; "lemma"; "proposition"; "macro"; "import";
                "prefix"; "postfix"; "infixl"; "infixr"; "infix"; "postulate"; "axiom";
                "macrovariables"; "option"; "opaque"; "unsafe"; "variables"; "section"; "end";
                "token"; "#macroexpand"; "#infer"; "#eval"; "--"; "{-"; "-}"]
let reserved = ['('; ')'; '['; ']'; '<'; '>'; '\n'; '\t'; '\r'; ' '; '.'; ',']

let isValidChar  c = not (List.mem c reserved)
let isValidIdent s = not (List.mem s keywords)

let character c = ch c >> pure (Atom (String.make 1 c))

let ident = decorateErrors ["ident"] (guard isValidIdent (str isValidChar))

let inlineComment    = token "--" >> str0 (fun c -> c <> '\r' && c <> '\n') >> nl
let multilineComment = token "{-" >> optional ws >> sepBy ws (guard ((<>) "-}") (str (negate isWhitespace))) >> optional ws >> token "-}"
let comment          = (inlineComment <|> multilineComment) >> pure Skip

let toTokenize = ref ["-"]
let upTokens is = toTokenize := !toTokenize @ is

let tokenize s =
  let rec loopLeft buf s0 =
    match findMap (cutAtBegin s0) !toTokenize with
    | Some (prefix, s) -> loopLeft (prefix :: buf) s
    | None             -> (buf, s0) in
  let rec loopRight buf s0 =
    match findMap (cutAtEnd s0) !toTokenize with
    | Some (postfix, s) -> loopRight (postfix :: buf) s
    | None              -> (buf, s0) in

  let (left, s1) = loopLeft [] s in
  if String.length s1 = 0 then List.rev left
  else let (right, s2) = loopRight [] s1 in
  if String.length s2 = 0 then List.rev_append left right
  else List.rev_append left (s2 :: right)

let syntax = fix (fun p ->
  let special = singleton <$> (character '.' <|> character ',') in
  let atom    = (List.map atom % tokenize) <$> ident in
  let paren   = sat isBracket << optional ws >>= fun c -> many p << ch (enclosing c) >>=
                  fun es -> pure [Node (c, List.concat es)] in
  many comment >> (special <|> atom <|> paren) << many comment << optional ws)

let toplevel c = guard (List.for_all c) syntax >>=
  fun x -> many (guard (List.for_all c) syntax) >>=
    fun xs -> match x @ List.concat xs with
      | []  -> failwith "unreachable code was reached"
      | [y] -> pure y
      | ys  -> pure (paren ys)

let isDefTok t = t = ":=" || t = "≔" || t = "≜" || t = "≝"
let defTok = guard isDefTok ident

let isntDefTok = function
  | Atom x -> not (isDefTok x)
  | _      -> true

let truth = fun _ -> true

let binder = token "(" >> optional ws >> sepBy1 ws (guard ((<>) ":") ident) >>=
  fun is -> optional ws >> token ":" >> optional ws >> toplevel truth >>=
    fun stx -> token ")" >> let e = elab stx in pure (List.map (fun i -> (mkIdent i, e)) is)

let binders = List.concat <$> sepBy (ws <|> eps) binder << optional ws

let debugChar = anyChar >>= fun c -> failwith (Printf.sprintf "DEBUG %c" c)

let defKeyword = token "definition" <|> token "def" <|> token "theorem" <|> token "lemma" <|> token "proposition"

let def =
  defKeyword >> ws >> ident >>= fun i -> ws >> binders >>=
    fun bs -> optional1 (token ":" >> ws >> toplevel isntDefTok) >>=
      fun t0 -> defTok >> optional ws >> toplevel truth >>= fun e ->
        let t = Option.map (fun e -> teles ePi (elab e) bs) t0 in
        pure (Decl (Def (i, t, teles eLam (elab e) bs)))

let tele c tok =
  tok >> ws >> ident >>= fun i -> ws >> binders >>=
    fun bs -> token ":" >> ws >> toplevel c >>=
      fun t -> pure (i, bs, t)

let axm = tele truth (token "axiom" <|> token "postulate") >>=
  fun (i, bs, e) -> let t = teles ePi (elab e) bs in pure (Decl (Axiom (i, t)))

let macro =
  optional1 (token "unsafe" >> ws) >>= fun flag ->
    token "macro" >> ws >> toplevel isntDefTok >>= fun e1 ->
      defTok >> optional ws >> toplevel truth >>= fun e2 ->
        pure (Macro (Option.is_some flag, e1, e2))

let mkOperator assoc tok = token tok >> ws >> ident << ws >>= fun e ->
  sepBy1 ws ident >>= fun is -> pure (Operator (assoc, float_of_string e, is))

let infixl  = mkOperator (Infix Left)    "infixl"
let infixr  = mkOperator (Infix Right)   "infixr"
let infix   = mkOperator (Infix Neither) "infix"
let prefix  = mkOperator Prefix          "prefix"
let postfix = mkOperator Postfix         "postfix"

let operator = infixl <|> infixr <|> infix <|> prefix <|> postfix

let debug ident fn = token ident >> ws >> toplevel truth >>= fun e -> pure (fn e)

let macroexpand    = debug "#macroexpand" (fun e -> Macroexpand e)
let infer          = debug "#infer"       (fun e -> Infer (elab e))
let eval           = debug "#eval"        (fun e -> Eval (elab e))
let macrovariables = token "macrovariables" >> ws >> sepBy1 ws ident >>= fun is -> pure (Macrovariables is)
let tokens         = token "token" >> ws >> sepBy1 ws ident >>= fun is -> pure (Token is)
let variables      = token "variables" >> ws >> binders >>= fun bs -> pure (Variables bs)
let import         = token "import" >> ws >> sepBy1 ws ident >>= fun fs -> pure (Import fs)
let options        = token "option" >> ws >> ident >>= fun i -> ws >> ident >>= fun v -> pure (Option (i, v))
let opaque         = token "opaque" >> ws >> ident >>= fun x -> pure (Opaque x)
let section        = (token "section" >> pure Section) <|> (token "end" >> pure End)

let commands = import <|> variables <|> options <|> opaque <|> operator <|> macroexpand <|> infer <|> eval <|> macrovariables <|> tokens
let cmdeof   = eof >> pure Eof
let cmdline  = def <|> axm <|> macro <|> commands <|> section <|> comment <|> cmdeof
let cmd      = optional ws >> cmdline

let action =
  token ":" >> ident >>= fun i ->
    optional1 (optional ws >> toplevel truth) >>= function
      | None   -> pure (Action i)
      | Some e -> pure (Command (i, elab e))

let eval = toplevel truth >>= fun e -> pure (Expr (elab e))
let repl = optional ws >> (action <|> eval <|> (eps >> pure Nope)) << eof