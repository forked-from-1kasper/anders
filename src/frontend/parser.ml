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
exception TooFewArguments

let mkIdent = ident

let expandIdent = function
  | Atom x -> ident x
  | e      -> raise (ExpectedIdent e)

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

let next = function
  |   []    -> raise TooFewArguments
  | x :: xs -> (x, xs)

let takeWhile pred stream =
  let rec loop buf =
    match Stream.peek stream with
    | Some t when pred t -> (Stream.junk stream; loop (t :: buf))
    | _                  -> List.rev buf
  in loop []

let getPrecedence = function
  | Atom t -> Dict.find_opt t !operators
  | Node _ -> None

let isEmpty = Option.is_none % Stream.peek
let junk stream = Stream.junk stream; stream
let drop stream = if isEmpty stream then stream else junk stream

let mapsto = Atom "↦"

(* https://github.com/gabrielhdt/pratter/blob/master/pratter.ml *)
let rec nud stream = function
  | Node ('<', is)                         -> paren [Node ('<', is); pratter stream]
  | Node ('[', es) when List.mem mapsto es -> let (is, xs) = splitWhile ((<>) mapsto) es in
                                              Node ('[', [prattSigma is; mapsto; prattSigma (List.tl xs)])
  | Node ('[', es)                         -> prattSystem es
  | Node (_,   es)                         -> prattSigma es
  | Atom x when isQuantifier x             ->
    let xs = List.map prattBinder (takeWhile ((<>) (Atom ",")) stream) in
    paren [paren (Atom x :: xs); Atom ","; pratter (junk stream)]
  | Atom x -> match Dict.find_opt x !operators with
    | Some (Prefix, _)  -> paren [Atom x; nud stream (Stream.next stream)]
    | Some (Infix _, _) -> raise (UnexpectedInfix x)
    | Some (Postfix, _) -> raise (UnexpectedPostfix x)
    | _                 -> Atom x

and prattBinder e = let (is, es) = unpackBinder e in
  paren [paren is; Atom ":"; prattSigma es]

and prattSystem es =
  let rec loop stream buf =
    if isEmpty stream then List.rev buf
    else
      let xs = takeWhile ((<>) (Atom "→")) stream in
      let e  = pratter (junk stream) in
      loop (drop stream) (paren [paren xs; e] :: buf)
  in Node ('[', loop (Stream.of_list es) [])

and led assoc bp stream left t =
  let rbp = match assoc with
    | Right          -> bp *. (1. -. epsilon_float)
    | Left | Neither -> bp
  in paren [left; t; expression rbp assoc stream]

and expression rbp rassoc stream =
  let rec loop left =
    match Stream.peek stream with
    | None | Some (Atom ",") -> left
    | Some t ->
    begin
      match getPrecedence t with
      | Some (Infix lassoc, lbp) ->
        if lbp > rbp || (lbp = rbp && lassoc = Right && rassoc = Right)
        then loop (led lassoc lbp (junk stream) left t)
        else if lbp < rbp || (lbp = rbp && lassoc = Left && rassoc = Left)
        then left else raise (OpConflict (left, t))
      | Some (Postfix, lbp) ->
        if lbp > rbp then begin Stream.junk stream; loop (paren [left; t]) end
        else if lbp = rbp then raise (OpConflict (left, t))
        else left
      | Some (Prefix, _) | None ->
        let next = nud stream (Stream.next stream) in
        loop (mkApp left (prattProj stream next))
    end in
  try loop (paren [prattProj stream (nud stream (Stream.next stream))])
  with Stream.Failure -> raise TooFewArguments

and pratter stream = expression neg_infinity Neither stream

and prattProj stream stx =
  match Stream.peek stream with
  | Some (Atom ".") -> let next = Stream.next (junk stream) in
                       prattProj stream (paren [stx; Atom "."; nud stream next])
  | _               -> stx

and prattSigma xs =
  let rec loop stream =
    let stx = pratter stream in
    match Stream.peek stream with
    | Some (Atom ",") -> paren [stx; Atom ","; loop (junk stream)]
    | Some e          -> raise (InvalidSyntax e)
    | None            -> stx in
  loop (Stream.of_list xs)

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

let indexed =
       etype "U" "Uω" Kan <|> etype "V" "Vω" Pretype
  <|> (token "L" >> level >>= fun n -> pure (ELevelElem n))

let getVar x =
  let xs = [(!intervalPrim, EI);
            (!zeroPrim, EDir Zero);
            (!onePrim, EDir One)] in
  match List.assoc_opt x xs with Some e -> e | None -> decl x

let expandVar x =
  match runParser (indexed << eof) (ofString x) 0 with
  | Ok (_, e) -> e
  | Error _   -> getVar x

let expandParens = function
  | Node ('(', es) -> es
  | t              -> [t]

let nullary = function
  | "𝟎"    | "empty" -> Some EEmpty
  | "𝟏"    | "unit"  -> Some EUnit
  | "𝟐"    | "bool"  -> Some EBool
  | "★"    | "star"  -> Some EStar
  | "0₂"   | "false" -> Some EFalse
  | "1₂"   | "true"  -> Some ETrue
  | "ℕ"    | "nat"   -> Some EN
  | "zero"           -> Some EZero
  | "succ"           -> Some ESucc
  | "L"              -> Some ELevel
  | "?"              -> Some EHole
  | x                -> Some (expandVar x)

let unary e = function
  | "Id"      -> Some (EId e)
  | "ref"     -> Some (ERef e)
  | "idJ"     -> Some (EJ e)
  | "ouc"     -> Some (EOuc e)
  | "PathP"   -> Some (EPathP e)
  | "Glue"    -> Some (EGlue e)
  | "Partial" -> Some (EPartial e)
  | "ind₀"    -> Some (EIndEmpty e)
  | "ind₁"    -> Some (EIndUnit e)
  | "ind₂"    -> Some (EIndBool e)
  | "ℕ-ind"   -> Some (ENInd e)
  | "indᵂ"    -> Some (EIndW e)
  | "ℑ"       -> Some (EIm e)
  | "ℑ-unit"  -> Some (EInf e)
  | "ℑ-join"  -> Some (EJoin e)
  | "isucc"   -> Some (ELSucc e)
  | "-"       -> Some (ENeg e)
  | "U"       -> Some (EType (Kan, Finite e))
  | "V"       -> Some (EType (Pretype, Finite e))
  | "typeof"  -> Some (ETypeof e)
  | _         -> None

let binary e1 e2 = function
  | "transp"   -> Some (ETransp (e1, e2))
  | "PartialP" -> Some (EPartialP (e1, e2))
  | "inc"      -> Some (EInc (e1, e2))
  | "sup"      -> Some (ESup (e1, e2))
  | "coeq"     -> Some (ECoeq (e1, e2))
  | "iadd"     -> Some (EAdd (e1, e2))
  | "imax"     -> Some (EMax (e1, e2))
  | "ind-ℑ"    -> Some (EIndIm (e1, e2))
  | _          -> None

let ternary e1 e2 e3 = function
  | "glue"     -> Some (EGlueElem (e1, e2, e3))
  | "unglue"   -> Some (EUnglue (e1, e2, e3))
  | "iota"     -> Some (EIota (e1, e2, e3))
  | "resp"     -> Some (EResp (e1, e2, e3))
  | "coeq-ind" -> Some (EIndCoeq (e1, e2, e3))
  | _          -> None

let quaternary e1 e2 e3 e4 = function
  | "hcomp" -> Some (EHComp (e1, e2, e3, e4))
  | _       -> None

let infix e1 e2 = function
  | "∨" | "\\/" -> Some (EOr (e1, e2))
  | "∧" | "/\\" -> Some (EAnd (e1, e2))
  | "→"         -> Some (impl e1 e2)
  | "×"         -> Some (prod e1 e2)
  | "@"         -> Some (EAppFormula (e1, e2))
  | _           -> None

let appStx fn es e = List.fold_left eApp e (List.map fn es)

let unaryExpander fn = function
  | Node ('(', (Atom x :: e :: es)) -> Option.map (appStx fn es) (unary (fn e) x)
  | _                               -> None

let binaryExpander fn = function
  | Node ('(', (Atom x :: a :: b :: es)) -> Option.map (appStx fn es) (binary (fn a) (fn b) x)
  | _                                    -> None

let ternaryExpander fn = function
  | Node ('(', (Atom x :: a :: b :: c :: es)) -> Option.map (appStx fn es) (ternary (fn a) (fn b) (fn c) x)
  | _                                         -> None

let quaternaryExpander fn = function
  | Node ('(', (Atom x :: a :: b :: c :: d :: es)) -> Option.map (appStx fn es) (quaternary (fn a) (fn b) (fn c) (fn d) x)
  | _                                              -> None

let infixExpander fn = function
  | Node ('(', [a; Atom x; b]) -> infix (fn a) (fn b) x
  | _                          -> None

let expandBinder fn es0 = match es0 with
  | is :: Atom ":" :: es -> let e = fn (paren es)
    in List.map (fun i -> (expandIdent i, e)) (expandParens is)
  | _ -> failwith (Printf.sprintf "expandBinder: %s" (showStxs es0))

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

let face p e d : formula = match getVar p, e, getDir d with
  | EVar x,  "=", d  -> Equation (x, d)
  | EDir d1, "=", d2 -> if d1 = d2 then Truth else Falsehood
  | _,       _,   _  -> failwith "invalid face"

let parseFace xs =
  if List.mem Falsehood xs then None
  else if List.mem Truth xs then Some Env.empty
  else Some (Env.of_seq (Seq.map extEquation (List.to_seq xs)))

let parsePartial xs e = Option.map (fun ys -> (ys, e)) (parseFace xs)

let expandEquation = function
  | Node ('(', [Atom p; Atom e; Atom d]) -> face p e d
  | e                                    -> raise (InvalidSyntax e)

let expandFace = List.map expandEquation

let expandClause fn = function
  | Node ('(', [Node ('(', fs); e]) -> parsePartial (expandFace fs) (fn e)
  | e                               -> raise (InvalidSyntax e)

let expandSystem fn = System.of_seq % Seq.filter_map (expandClause fn) % List.to_seq

let quantifierExpander fn = function
  | Node ('(', [Node ('<', is); e])                       -> Some (pLam (fn e) (List.map expandIdent is))
  | Node ('(', [Node ('(', Atom "λ" :: bs); Atom ","; e]) -> Some (expandQuantifier fn eLam bs e)
  | Node ('(', [Node ('(', Atom "Π" :: bs); Atom ","; e]) -> Some (expandQuantifier fn ePi  bs e)
  | Node ('(', [Node ('(', Atom "Σ" :: bs); Atom ","; e]) -> Some (expandQuantifier fn eSig bs e)
  | Node ('(', [Node ('(', Atom "W" :: bs); Atom ","; e]) -> Some (expandQuantifier fn eW   bs e)
  | _                                                     -> None

let lowExpander fn = function
  | Node ('(', [e1; Atom ","; e2])                  -> Some (EPair (ref None, fn e1, fn e2))
  | Node ('(', [e; Atom "."; Atom "1"])             -> Some (EFst (fn e))
  | Node ('(', [e; Atom "."; Atom "2"])             -> Some (ESnd (fn e))
  | Node ('(', [e; Atom "."; Atom x])               -> Some (EField (fn e, x))
  | Node ('(', [e; Node ('[', [is; Atom "↦"; t])]) -> Some (ESub (fn e, fn is, fn t))
  | _                                               -> None

let simpleExpander fn = function
  | Node ('(', f :: xs)                   -> Some (appStx fn xs (fn f))
  | Node ('[', es)                        -> Some (ESystem (expandSystem fn es))
  | Atom x                                -> nullary x
  | _                                     -> None

let rec traverseExpanders g e = function
  |   []    -> None
  | f :: fs -> match f g e with
    | None -> traverseExpanders g e fs
    | t    -> t

let expanders = [quantifierExpander; lowExpander; infixExpander;
                 unaryExpander; binaryExpander;
                 ternaryExpander; quaternaryExpander;
                 simpleExpander]

let rec expandTerm e =
  match traverseExpanders expandTerm e expanders with
  | None   -> raise (InvalidSyntax e)
  | Some t -> t

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
                "infixl"; "infixr"; "infix"; "postulate"; "axiom"; "macrovariables"; "option";
                "unsafe"; "variables"; "section"; "end"; "#macroexpand"; "#infer"; "#eval";
                "--"; "{-"; "-}"]
let reserved = ['('; ')'; '['; ']'; '<'; '>'; '\n'; '\t'; '\r'; ' '; '.'; ',']

let isValidChar  c = not (List.mem c reserved)
let isValidIdent s = not (List.mem s keywords)

let character c = ch c >> pure (Atom (String.make 1 c))

let ident = decorateErrors ["ident"] (guard isValidIdent (str isValidChar))

let inlineComment    = token "--" >> str0 (fun c -> c <> '\r' && c <> '\n') >> nl
let multilineComment = token "{-" >> optional ws >> sepBy ws (guard ((<>) "-}") (str (negate isWhitespace))) >> optional ws >> token "-}"
let comment          = (inlineComment <|> multilineComment) >> pure Skip

let syntax = fix (fun p ->
  let chars = character '.' <|> character '-' <|> character ',' in
  let atom  = atom <$> ident in
  let paren = sat isBracket << optional ws >>= fun c -> many p << ch (enclosing c) >>= fun es -> pure (Node (c, es)) in
  many comment >> (chars <|> atom <|> paren) << many comment << optional ws)

let toplevel c = guard c syntax >>= fun x -> many (guard c syntax) >>=
  fun xs -> pure (match xs with [] -> x | _ -> paren (x :: xs))

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
let variables      = token "variables" >> ws >> binders >>= fun bs -> pure (Variables bs)
let import         = token "import" >> ws >> sepBy1 ws ident >>= fun fs -> pure (Import fs)
let options        = token "option" >> ws >> ident >>= fun i -> ws >> ident >>= fun v -> pure (Option (i, v))
let section        = (token "section" >> pure Section) <|> (token "end" >> pure End)

let commands = import <|> variables <|> options <|> operator <|> macroexpand <|> infer <|> eval <|> macrovariables
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