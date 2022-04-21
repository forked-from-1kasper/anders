%{ open Language.Spec
   open Prettyprinter
   open Module
   open Prefs

  let getVar x =
    let xs = [(!intervalPrim, EI);
              (!zeroPrim, EDir Zero);
              (!onePrim, EDir One);
              ("𝟎", EEmpty);     ("empty", EEmpty);
              ("𝟏", EUnit);      ("unit", EUnit);
              ("𝟐", EBool);      ("bool", EBool);
              ("★", EStar);      ("star", EStar);
              ("false", EFalse); ("0₂", EFalse);
              ("true", ETrue);   ("1₂", ETrue);
              ("L", ELevel)] in
    match List.assoc_opt x xs with Some e -> e | None -> decl x

  let rec pLam e : ident list -> exp = function [] -> e | x :: xs -> EPLam (ELam (EI, (x, pLam e xs)))

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
    else if List.mem Truth xs then Some eps
    else Some (Env.of_seq (Seq.map extEquation (List.to_seq xs)))

  let parsePartial (xs, e) = Option.map (fun ys -> (ys, e)) (parseFace xs)
%}

%token <string> IDENT
%token <Z.t> KAN
%token <Z.t> PRE
%token <Z.t> LEVEL
%token <Z.t> KANOMEGA
%token <Z.t> PREOMEGA
%token PREPARAM KANPARAM
%token <string> EXT
%token LPARENS RPARENS LSQ RSQ
%token COMMA COLON IRREF EOF HOLE
%token DEFEQ PROD ARROW DOT LAM
%token MODULE WHERE IMPORT DEF AXIOM
%token SIGMA PI OPTION PLUGIN LT GT
%token APPFORMULA PATHP TRANSP HCOMP
%token PARTIAL PARTIALP MAP INC OUC
%token AND OR NEGATE
%token ID REF IDJ
%token GLUE GLUEELEM UNGLUE
%token INDEMPTY INDUNIT INDBOOL
%token W INDW SUP
%token IM INF INDIM JOIN
%token COEQ IOTA RESP INDCOEQ
%token SUCC ADD MAX
%token SECTION END
%token VARIABLES

%left APPFORMULA
%left OR
%left AND
%right ARROW
%right PROD

%nonassoc NEGATE
%nonassoc DOT

%start <Module.file> file
%start <Module.command> repl

%%

ident  : IRREF { Irrefutable } | IDENT { ident $1 }
vars   : ident+ { $1 }
tele   : LPARENS vars COLON exp2 RPARENS { List.map (fun x -> (x, $4)) $2 }
teles  : tele teles { List.append $1 $2 } | tele { $1 }
params : teles { $1 } | { [] }
path   : IDENT { getPath $1 }
face   : LPARENS IDENT IDENT IDENT RPARENS { face $2 $3 $4 }

part : face+ ARROW exp2 { ($1, $3) }
file : MODULE IDENT WHERE line* EOF { ($2, $4) }
repl : COLON IDENT exp2 EOF { Command ($2, $3) } | COLON IDENT EOF { Action $2 } | exp2 EOF { Eval $1 } | EOF { Nope }
exp1 : exp2 COMMA exp1 { EPair (ref None, $1, $3) } | exp2 { $1 }

exp2:
  | LAM teles COMMA exp2 { teles eLam $4 $2 }
  | PI teles COMMA exp2 { teles ePi $4 $2 }
  | SIGMA teles COMMA exp2 { teles eSig $4 $2 }
  | W teles COMMA exp2 { teles eW $4 $2 }
  | LT vars GT exp2 { pLam $4 $2 }
  | exp3 { $1 }

exp3:
  | exp3 APPFORMULA exp3 { EAppFormula ($1, $3) }
  | exp3 ARROW exp3 { impl $1 $3 }
  | exp3 PROD exp3 { prod $1 $3 }
  | exp3 AND exp3 { EAnd ($1, $3) }
  | exp3 OR exp3 { EOr ($1, $3) }
  | exp4 { $1 }

exp4 :
  | exp4 exp6 { EApp ($1, $2) }
  | ID exp6 { EId $2 }
  | REF exp6 { ERef $2 }
  | IDJ exp6 { EJ $2 }
  | INC exp6 exp6 { EInc ($2, $3) }
  | OUC exp6 { EOuc $2 }
  | PATHP exp6 { EPathP $2 }
  | TRANSP exp6 exp6 { ETransp ($2, $3) }
  | HCOMP exp6 exp6 exp6 exp6 { EHComp ($2, $3, $4, $5) }
  | PARTIAL exp6 { EPartial $2 }
  | PARTIALP exp6 exp6 { EPartialP ($2, $3) }
  | GLUE exp6 { EGlue $2 }
  | GLUEELEM exp6 exp6 exp6 { EGlueElem ($2, $3, $4) }
  | UNGLUE exp6 exp6 exp6 { EUnglue ($2, $3, $4) }
  | INDEMPTY exp6 { EIndEmpty $2 }
  | INDUNIT exp6 { EIndUnit $2 }
  | INDBOOL exp6 { EIndBool $2 }
  | SUP exp6 exp6 { ESup ($2, $3) }
  | INDW exp6 { EIndW $2 }
  | IM exp6 { EIm $2 }
  | INF exp6 { EInf $2 }
  | INDIM exp6 exp6 { EIndIm ($2, $3) }
  | COEQ exp6 exp6 { ECoeq ($2, $3) }
  | IOTA exp6 exp6 exp6 { EIota ($2, $3, $4) }
  | RESP exp6 exp6 exp6 { EResp ($2, $3, $4) }
  | INDCOEQ exp6 { EIndCoeq $2 }
  | JOIN exp6 { EJoin $2 }
  | SUCC exp6 { ESucc $2 }
  | ADD exp6 exp6 { EAdd ($2, $3) }
  | MAX exp6 exp6 { EMax ($2, $3) }
  | PREPARAM exp6 { EType (Pretype, Finite $2) }
  | KANPARAM exp6 { EType (Kan, Finite $2) }
  | exp5 { $1 }

exp5:
  | exp6 LSQ exp2 MAP exp2 RSQ { ESub ($1, $3, $5) }
  | exp6 { $1 }

exp6:
  | HOLE { EHole }
  | LEVEL { ELevelElem $1 }
  | PREOMEGA { EType (Pretype, Omega $1) }
  | KANOMEGA { EType (Kan, Omega $1) }
  | PRE { EType (Pretype, Finite (ELevelElem $1)) }
  | KAN { EType (Kan, Finite (ELevelElem $1)) }
  | PREPARAM { EType (Pretype, Finite (ELevelElem Z.zero)) }
  | KANPARAM { EType (Kan, Finite (ELevelElem Z.zero)) }
  | exp6 DOT IDENT { match $3 with | "1" -> EFst $1 | "2" -> ESnd $1 | field -> EField ($1, field) }
  | NEGATE exp6 { ENeg $2 }
  | LSQ separated_list(COMMA, part) RSQ { ESystem (System.of_seq (Seq.filter_map parsePartial (List.to_seq $2))) }
  | LPARENS exp1 RPARENS { $2 }
  | IDENT { getVar $1 }

declarations:
  | DEF IDENT params COLON exp2 DEFEQ exp2 { Def ($2, Some (teles ePi $5 $3), teles eLam $7 $3) }
  | DEF IDENT params COLON exp2 DEFEQ EXT { Ext ($2, teles ePi $5 $3, $7) }
  | DEF IDENT params DEFEQ exp2 { Def ($2, None, teles eLam $5 $3) }
  | AXIOM IDENT params COLON exp2 { Axiom ($2, teles ePi $5 $3) }

line :
  | IMPORT path+ { Import $2 }
  | PLUGIN path { Plugin $2 }
  | OPTION IDENT IDENT { Option ($2, $3) }
  | declarations { Decl $1 }
  | SECTION line+ END { Section $2 }
  | VARIABLES teles { Variables $2 }
