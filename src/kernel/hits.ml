open Language.Spec
open Universe
open Check
open Elab
open Term

let rec sum w l (ctx, xs) = function
  | []           -> VSum { name = w; kind = eval ctx l; params = List.rev xs }
  | (y, e) :: ys -> let t = eval ctx e in
    VLam (t, (y, fun x -> sum w l (upLocal ctx y t x, x :: xs) ys))

let rec con w1 w2 l ts (ctx, xs, ys) us vs = match us, vs with
  | (p, e) :: us, _  -> let t = eval ctx e in
    VLam (t, (p, fun x -> con w1 w2 l ts (upLocal ctx p t x, x :: xs, ys) us vs))
  | [], (p, e) :: vs -> let t = eval ctx e in
    VLam (t, (p, fun y -> con w1 w2 l ts (upLocal ctx p t y, xs, y :: ys) [] vs))
  | [], []           -> let ts' = evalSystem ctx ts in
    begin match System.find_opt eps ts' with
      | Some v -> v
      | None   -> VCon { parent = { name = w1; kind = eval ctx l; params = List.rev xs };
                         cname = w2; cparams = List.rev ys; boundary = ts' }
    end

let teleCtx = List.fold_left (fun ctx (y, e) -> let t = eval ctx e in upLocal ctx y t (Var (y, t)))

let checkData (ctx : ctx) (x : string) (d : data) =
  let e = teles ePi d.kind d.params in
  isType (infer ctx e); let t = eval ctx e in
  assign ctx x t (Value (sum x d.kind (ctx, []) d.params));

  let t0 = List.fold_left (fun e (y, _) -> EApp (e, EVar y)) (EVar (ident x)) d.params in

  let (ctx1, xs1) = List.fold_left (fun (ctx, ts0) (y, e) -> let t = eval ctx e in
    let y' = Var (y, t) in (upLocal ctx y t y', y' :: ts0)) (ctx, []) d.params in
  let t1 = VSum { name = x; kind = eval ctx1 d.kind; params = List.rev xs1 } in

  List.iter (fun (c : ctor) ->
    let f = teles ePi (teles ePi t0 c.params) d.params in
    isType (infer ctx f); let g = eval ctx f in

    let ctx2 = teleCtx ctx1 c.params in
    System.iter (fun _ e -> check ctx2 e t1) c.boundary;

    let t = con x c.name d.kind c.boundary (ctx, [], []) d.params c.params in
    assign ctx c.name g (Value t)) d.ctors;
    ctx.data := Dict.add x d !(ctx.data)

let checkSplit (ctx : ctx) (s : split) =
  let e = teles ePi s.signature s.params in isType (infer ctx e);
  let t = eval ctx e in let ctx1 = teleCtx ctx s.params in
  let (w, (p, g)) = extPiG (eval ctx1 s.signature) in let s = extSum w in

  ()