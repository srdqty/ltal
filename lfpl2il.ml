open Op;;
open Var;;
open Il;;
open Util;;
open Tclfpl;;

exception Error of string

let rec tp0trans tp = 
  match tp with
    Lfpl.Nat -> Int
  | Lfpl.Bool -> Int
  | Lfpl.Dmnd -> Int
  | Lfpl.Tensor(t1,t2) -> Tensor(tp0trans t1, tp0trans t2)
  | Lfpl.List(t) -> List(tp0trans t)
  | Lfpl.Top -> Int
  | _ -> raise NYI

let argtrans argtys = 
  List.fold_right (fun t u -> Tensor(t,u)) (List.map tp0trans argtys) Int

let tp1trans (Lfpl.Fn (argtys, retty)) =
  Arrow(argtrans argtys,
	tp0trans retty)

let rec zip xs ys = 
  match xs,ys with
    [],[] -> []
  | x::xs,y::ys -> (x,y)::(zip xs ys)
  | _ -> raise (Error "zip: lists of different lengths")

let translate0 e tp = 
  let rec tr_e e tp = 
    match e with
      Lfpl.Var v -> 
	retM (Var v)
    | Lfpl.Op(e1,opr,e2) -> 
	tr_e e1 tp >>= fun e1' ->
        tr_e e2 tp >>= fun e2' ->
	retM (Op(opr,e1',e2'))
    | Lfpl.App(f,es) -> 
	get_sgM >>= fun sg -> 
	let Lfpl.Fn(ts,tp') = lookup_or_fail sg f in
	mapM (fun (x,y) -> tr_e x y) (zip es ts) >>= fun es' -> 
	retM (App (Var f, List.fold_right (fun x y -> Pair(x,y)) es' (IntC 0)))
    | Lfpl.P(p) -> 
	tr_p p tp
    | Lfpl.Match(e,ms) -> 
	Tclfpl.ti_exp e >>= fun tp' -> 
	tr_e e tp' >>= fun e' -> 
	tr_ms e'  ms tp
    | Lfpl.NewDmnd -> retM (IntC 0)
  and tr_ms e' ms tp =
	match ms with
	  [Lfpl.Hole x,e2] -> 
	    tr_e e2 tp >>= fun e2' -> 
	      retM(Let(x,e',e2'))
	| [Lfpl.True,e1;Lfpl.False,e2] -> 
	    tr_e e1 tp >>= fun e1' -> 
	    tr_e e2 tp >>= fun e2' -> 
	    retM (If (NZ,e', e1', e2'))
	| [Lfpl.Pair(Lfpl.Hole x, Lfpl.Hole y),e2] -> 
	    tr_e e2 tp >>= fun e2' -> 
	    retM (LetPair(x,y,e', e2'))
	| [Lfpl.Nil,e1; Lfpl.Cons(d,Lfpl.Hole h,Lfpl.Hole t),e2] ->
	    tr_e e1 tp >>= fun e1' -> 
	    tr_e e2 tp >>= fun e2' -> 
	    retM (Case (e', e1',h,t,e2'))
	| [Lfpl.IntC 0,e1; Lfpl.Hole v,e2] ->
	    tr_e e1 tp >>= fun e1' -> 
	    tr_e e2 tp >>= fun e2' -> 
	    retM (Let(v,e',If (NZ,Var v, e2',e1')))
	| _ -> raise (Error "tr_e: match form NYI")
	      
  and tr_p p tp = 
    match p with
      Lfpl.IntC i -> retM(IntC i)
    | Lfpl.True -> retM (IntC 1)
    | Lfpl.False -> retM (IntC 0)
    | Lfpl.Pair(p1,p2) -> 
	let t1,t2 = Tclfpl.force_pair tp in
	tr_p p1 t1 >>= fun e1 ->
	tr_p p2 t2 >>= fun e2 ->
	retM (Pair(e1,e2))
    | Lfpl.Nil -> retM (Nil)
    | Lfpl.Cons(d,p1,p2) -> 
	let t = force_list tp in
	tr_p p1 t >>= fun e1 ->
	tr_p p2 tp >>= fun e2 ->
	retM (Cons(e1,e2))
    | Lfpl.Hole e ->
	tr_e e tp
    | _ -> raise (Error "tr_p: trees, sums NYI")
  in tr_e e tp

let translate1 (fndecls,e) = 
  let sg = Tclfpl.get_sig (fndecls,e) in
  let tr_fndecl fndecl e' = 
    let t1 = argtrans (List.map (fun (x,_) -> x) fndecl.Lfpl.argtys) in
    let t2 = tp0trans fndecl.Lfpl.rettp in
    let f = rename fndecl.Lfpl.name in
    let x = mkvar "x" in
    let ctx = (Ctx.from_list (List.map (fun (x,y) -> y,x) fndecl.Lfpl.argtys)) in
    let e,_ = translate0 fndecl.Lfpl.body fndecl.Lfpl.rettp sg ctx in
    let e = Ilsubst.subst1_exp fndecl.Lfpl.name (Var f) e in
    let rec bind x argtys e = 
      match argtys with
	[] -> e
      | (ty,arg):: argtys -> 
	  let z = mkvar "z" in
	  LetPair(arg,z,Var x, bind z argtys e)
    in      
    Let(fndecl.Lfpl.name, Fix(f,x,t1,t2,bind x fndecl.Lfpl.argtys e),e')
  in 
  let e',_ = translate0 e Lfpl.Nat sg Ctx.emp in
  List.fold_right tr_fndecl fndecls e'
