{
  open Parser
  open Lexing

  let next_line lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
      { pos with pos_bol = pos.pos_cnum;
                 pos_lnum = pos.pos_lnum + 1 }
}

let lat1   = [^ '\t' ' ' '\r' '\n' '(' ')' ':' '.' ',' '/' '<' '>']
let beg    = lat1 # '-'
let bytes2 = ['\192'-'\223']['\128'-'\191']
let bytes3 = ['\224'-'\239']['\128'-'\191']['\128'-'\191']
let bytes4 = ['\240'-'\247']['\128'-'\191']['\128'-'\191']['\128'-'\191']

let utf8    = lat1|bytes2|bytes3|bytes4
let ident   = beg utf8*
let ws      = ['\t' ' ']
let nl      = "\r\n"|"\r"|"\n"
let comment = "--" [^ '\n' '\r']* (nl|eof)
let colon   = ':'
let defeq   = ":=" | "\xE2\x89\x94" | "\xE2\x89\x9C" | "\xE2\x89\x9D" (* ≔ | ≜ | ≝ *)
let arrow   = "->" | "\xE2\x86\x92" (* → *)
let lam     = "\\" | "\xCE\xBB"     (* λ *)
let pi      = "pi" | "\xCE\xA0"     (* Π *)
let sigma   = "sigma" | "\xCE\xA3"  (* Σ *)
let def     = "definition" | "def" | "theorem" | "lemma" | "corollary" | "proposition"
let axiom   = "axiom"|"postulate"

let negFormula = "-"
let andFormula = "/\\"|"\xE2\x88\xA7" (* ∧ *)
let orFormula  = "\\/"|"\xE2\x88\xA8" (* ∨ *)

rule main = parse
| nl              { next_line lexbuf; main lexbuf }
| comment         { next_line lexbuf; main lexbuf }
| ws+             { main lexbuf }
| "module"        { MODULE }
| "where"         { WHERE }
| "import"        { IMPORT }
| "option"        { OPTION }
| def             { DEF }
| 'U'             { SET }
| ','             { COMMA }
| '_'             { NO }
| '('             { LPARENS }
| ')'             { RPARENS }
| '/'             { DIRSEP }
| ".1"            { FST }
| ".2"            { SND }
| pi              { PI }
| sigma           { SIGMA }
| "?"             { HOLE }
| "<"             { LT }
| ">"             { GT }
| "PathP"         { PATHP }
| "@"             { APPFORMULA }
| "0"             { ZERO }
| "1"             { ONE }
| negFormula      { NEGATE }
| andFormula      { AND }
| orFormula       { OR }
| axiom           { AXIOM }
| defeq           { DEFEQ }
| lam             { LAM }
| arrow           { ARROW }
| colon           { COLON }
| ['0'-'9']+ as s { NAT (int_of_string s) }
| ident as s      { IDENT s }
| eof             { EOF }