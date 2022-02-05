open Language.Encode
open Language.Decode
open Language.Spec
open Prettyprinter
open Error

module Kernel =
struct
  let chm  = "./_build/install/default/bin/chm"
  let args = Array.make 0 ""
  let env  = Array.make 0 ""

  let (stdout, stdin) = Unix.open_process_args chm args
end

module Request = Encode(struct
  let put  = output_char Kernel.stdin
  let puts = output_string Kernel.stdin
end)

module Response = Decode(struct
  let get () = input_char Kernel.stdout
  let getn n = let m = Int64.to_int n in let bs = Bytes.make m '\x00' in
    for idx = 0 to m - 1 do
      Bytes.set bs idx (get ())
    done; Bytes.to_string bs
end)

module Fuze =
struct
  let (year, month, patch) =
    (* ping-pong *)
    Request.req Ping; flush Kernel.stdin;
    begin match Response.resp () with
      | Pong -> ()
      | _    -> raise ProtocolViolation
    end;
    Request.req Version; flush Kernel.stdin;
    begin match Response.resp () with
      | Version (i, j, k) -> (i, j, k)
      | _                 -> raise ProtocolViolation
    end
end

let trace x xs = Printf.printf "%s: [%s]\n" x (String.concat "; " (List.map showExp xs)); flush_all ()

let traceHole e gma = print_string "\nHole:\n\n";
  List.iter (fun (i, e') -> Printf.printf "%s : %s\n" (showIdent i) (showExp e')) gma;
  print_string ("\n" ^ String.make 80 '-' ^ "\n" ^ showExp e ^ "\n\n")

let rec recvTerm () = match Response.resp () with
  | Term e        -> e
  | Trace (x, xs) -> trace x xs; recvTerm ()
  | Hole (e, gma) -> traceHole e gma; recvTerm ()
  | Error err     -> raise (Kernel err)
  | _             -> raise ProtocolViolation

let rec over () = match Response.resp () with
  | OK            -> ()
  | Trace (x, xs) -> trace x xs; over ()
  | Hole (e, gma) -> traceHole e gma; over ()
  | Error err     -> raise (Kernel err)
  | _             -> raise ProtocolViolation

let eval e  = Request.req (Eval e);  flush Kernel.stdin; recvTerm ()
let infer e = Request.req (Infer e); flush Kernel.stdin; recvTerm ()

let def p t e = Request.req (Def (p, t, e)); flush Kernel.stdin; over ()
let assign p t e = Request.req (Assign (p, t, e)); flush Kernel.stdin; over ()
let assume p t = Request.req (Assume (p, t)); flush Kernel.stdin; over ()

let set p x = Request.req (Set (p, x)); flush Kernel.stdin; over ()

let showResp = function
  | Version (i, j, k) -> Printf.printf "Version (%Ld, %Ld, %Ld)\n" i j k
  | Trace (x, xs)     -> trace x xs
  | Hole (e, gma)     -> traceHole e gma
  | Error err         -> print_string (prettyPrintError err)
  | Bool false        -> print_string "false\n"
  | Bool true         -> print_string "true\n"
  | Term e            -> Printf.printf "%s\n" (showExp e)
  | Pong              -> print_string "pong\n"
  | OK                -> print_string "OK\n"

let receive () =
  while true do
    try showResp (Deserialize.resp ())
    with Invalid_argument _ | Failure _ -> ()
  done
