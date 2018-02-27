
type var = Var.var
open Var;;
open Il;;
open Util;;
    
let apptp te t1 t2 = 
  Arrow (Tensor(t1,te),t2)
let copytp t = Arrow(t,Tensor(t,t))
let freetp t = Arrow(t,Int)
    
let closuretp t1 t2 = 
  let va = mkvar "A" in
  let tva = TVar va in
  Exists (va, 
  Tensor (tva, 
  Tensor (apptp tva t1 t2, 
  Tensor (copytp tva, freetp tva))))

let forallclosuretp tv t = 
  let vb = mkvar "B" in
  let tvb = TVar vb in
  Exists (vb, 
  Tensor (tvb, 
  Tensor (Forall(tv,Arrow(Tensor(copytp (TVar tv), 
			  Tensor(freetp (TVar tv), tvb)),
			  t)),
  Tensor (copytp tvb, freetp tvb))))


let rec ctxtp ctx = 
  let l = Ctx.dom ctx in
  let rec f l = 
    match l with
      [] -> Absyn.Int
    | (v)::l' -> Absyn.Times (Ctx.lookup ctx v,f l')
  in f l

let rec tp2il t = 
  match t with
    Absyn.Int -> Int
  | Absyn.Times (t1,t2) ->
      let u1 = tp2il t1 in
      let u2 = tp2il t2 in
      Tensor (u1,u2)
  | Absyn.Arrow (t1,t2) ->
      let u1 = tp2il t1 in
      let u2 = tp2il t2 in
      closuretp u1 u2
  | Absyn.List t -> 
      List(tp2il t)
  | Absyn.Forall (tv,t) ->
      let u = tp2il t in 
      forallclosuretp tv u
  | Absyn.TVar v -> TVar v
let do_seq (e1, e2) = 
  let q = mkvar "_" in 
  Let(q,e1,e2)

let do_mkclosure (t, env, app, cp, fr,t') = 
  Pack(t,Pair(env,Pair(app,Pair(cp,fr))),t')

let do_letclosure (c,f) = 
  let tv = mkvar "a" in
  let p0 = mkvar "p" in
  let p1 = mkvar "p" in
  let p2 = mkvar "p" in
  let env = mkvar "env" in
  let ap = mkvar "app" in
  let cp = mkvar "copy" in
  let fr = mkvar "free" in
  LetUnpack(tv,p0,c,
  LetPair(env,p1,Var p0,
  LetPair(ap,p2,Var p1,
  LetPair(cp,fr,Var p2,
  f (TVar tv) (Var env) (Var ap) (Var cp) (Var fr)))))



let do_letpair (e, f) = 
  let x = mkvar "x" in
  let y = mkvar "y" in
  LetPair(x,y,e,f (Var x) (Var y))

let do_let (e, f) = 
  let x = mkvar "x" in
  Let(x,e,f (Var x))

let do_fn (t, f) = 
  let x = mkvar "x" in
  Fn(x,t,f (Var x))

let do_fix (t1,t2,g) = 
  let f = mkvar "f" in
  let x = mkvar "x" in
  Fix(f,x,t1,t2,g (Var f) (Var x))

let do_case (e,e1,f2) = 
  let h = mkvar "h" in
  let t = mkvar "t" in
  Case(e,e1,h,t,f2 (Var h) (Var t))

let rec copyt cfctx t x = 
  match t with
    Absyn.Int -> Pair(x,x)
  | Absyn.Times(t1,t2) -> 
      do_letpair (x,(fun y z -> 
      do_letpair (copyt cfctx t1 y, (fun y1 y2 ->
      do_letpair (copyt cfctx t2 z, (fun z1 z2 -> 
      Pair(Pair(y1, z1),
	      Pair( y2, z2))))))))
  | Absyn.Arrow(t1,t2) ->
      let t1' = tp2il t1 in
      let t2' = tp2il t2 in
      do_letclosure (x, fun ta ev ap cp fr -> 
      do_letpair(App(cp, ev),fun ev1 ev2 -> 
      Pair(do_mkclosure(ta, ev1, ap, cp, fr,closuretp t1' t2'),
	   do_mkclosure(ta, ev2, ap, cp, fr,closuretp t1' t2'))))
  | Absyn.List t' -> 
      let tp = tp2il t in
      App(do_fix(tp, Tensor(tp,tp), fun copy l ->
	  do_case(l,Pair(Nil,Nil), fun x y -> 
	  do_letpair(copyt cfctx t' x, fun h1 h2 ->
	  do_letpair(App(copy, y), fun t1 t2 ->
	  Pair(Cons(h1,t1),Cons(h2,t2)))))),
	x)
  | Absyn.Forall(tv,t) -> 
      let t' = tp2il t in
      do_letclosure (x, fun ta ev ap cp fr -> 
      do_letpair(App(cp, ev),fun ev1 ev2 -> 
      Pair(do_mkclosure(ta, ev1, ap, cp, fr,forallclosuretp tv t'),
	   do_mkclosure(ta, ev2, ap, cp, fr,forallclosuretp tv t'))))
  | Absyn.TVar tv -> 
      let (cp,fr) = Ctx.lookup cfctx tv in
      App(cp,x)

let rec freet cfctx t x = 
  match t with
    Absyn.Int -> top
  | Absyn.Times(t1,t2) -> 
      do_letpair(x, fun y z -> 
      do_seq(freet cfctx t1  y,
	     freet cfctx t2  z))
  | Absyn.Arrow(t1,t2) ->
      do_letclosure
	(x,(fun ta ev ap cp fr -> App (fr, ev)))
  | Absyn.List t' -> 
      App(do_fix(tp2il t, Int, fun free l ->
	  do_case(l,top,fun y z -> 
	  do_seq(freet cfctx t' y, App(free, z)))),
	  x)
  | Absyn.Forall(tv,t) -> 
      do_letclosure
	(x,(fun ta ev ap cp fr -> App (fr, ev)))
  | Absyn.TVar tv -> 
      let (cp,fr) = Ctx.lookup cfctx tv in
      App(fr,x)


let copyt' cfctx t x = Copy(cfctx,t,x)
let freet' cfctx t x = Free(cfctx,t,x)	
	
let min_ctx ctx e = 
  let fvs = Absyn.fv e in
  let cfvs = List.filter (fun x -> List.mem x fvs) (Ctx.dom ctx) in

  let ctx' = Ctx.restrict ctx cfvs in
  ctx'



(* ctx' must be a subsequence of ctx *)
(* given x : ||ctx||, produces y : ||ctx'|| * ||ctx|| *)
let ctx_copy ctx ctx' cfctx e =
  let rec cc d d' e = 
    match d, d' with
      _,[] -> Pair(top, e)
    | v::d1,((w::d2') as d2) ->
	if Var.eq v w 
	then 
	  do_letpair(e,fun x e0 -> 
          do_letpair(copyt' cfctx (Ctx.lookup ctx v) x, fun x1 x2 ->
          do_letpair(cc d1 d2' ( e0), fun e1 e2 ->
          Pair(Pair( x1, e1),Pair( x2, e2)))))
	else 
          do_letpair(e,fun x e0 -> 
          do_letpair(cc d1 d2 ( e0), fun e1 e2 ->
          Pair( e1,Pair( x, e2))))
    | _ -> raise NYI
   in cc (Ctx.dom ctx) (Ctx.dom ctx') e
   
let rec var2ilcf cfctx d v t env =
  (match d with
      (v')::d' -> 
	if (eq v v')
	then 
	  do_letpair(env,fun x env ->
	  do_letpair(copyt' cfctx t x,fun x1 x2 ->
	  Pair( x1,(Pair( x2, env)))))
	else
	  do_letpair(env,fun y env ->
	  do_letpair(var2ilcf cfctx d' v t env,fun x env ->
	  Pair( x,(Pair( y, env)))))
  | [] -> print_string ("couldn't find variable "^(Var.to_string v));
	     raise NYI)

and exp2ilcf tctx ctx cfctx e t env = 
  match (e) with 
    (Absyn.Var v) -> var2ilcf cfctx (Ctx.dom ctx) v t env
  | (Absyn.IntC i) -> Pair(IntC i,env)
  | (Absyn.Op(opr,[e1;e2])) ->
      do_letpair( exp2ilcf tctx ctx cfctx e1 t env, fun x1 env ->
      do_letpair( exp2ilcf tctx ctx cfctx e2 t env, fun x2 env ->
      	Pair(Op(opr, x1, x2),  env)))
  | (Absyn.If(c,e, e1, e2)) -> 
      do_letpair(exp2ilcf tctx ctx cfctx e Absyn.Int env,fun x env ->
      If(c,x,exp2ilcf tctx ctx cfctx e1 t env,
	    exp2ilcf tctx ctx cfctx e2 t env))
  | (Absyn.Pair (e1,e2)) ->
      let (t1,t2) = Tcabsyn.force_times t in
      do_letpair(exp2ilcf tctx ctx cfctx e1 t1 env, fun x1 env -> 
      do_letpair(exp2ilcf tctx ctx cfctx e2 t2 env, fun x2 env -> 
      Pair(Pair( x1,  x2), env)))
  | (Absyn.LetPair (x,y,e1,e2)) -> 
      let t' = Tcabsyn.ti tctx ctx e1 in (* TODO: Save types of subexpressions... *) 
      let (t1,t2) = Tcabsyn.force_times t' in
      do_letpair(exp2ilcf tctx ctx cfctx e1 t' env, fun p env ->
      do_letpair(p, fun x1 x2 ->
      do_letpair(exp2ilcf tctx (Ctx.extend (Ctx.extend ctx x t1) y t2) cfctx e2 t (Pair(x2,Pair(x1,env))), fun r env -> 
      do_letpair(env, fun x1' env -> 
      do_seq(freet' cfctx t1 x1',
      do_letpair(env, fun x2' env ->
      do_seq(freet' cfctx t2 x2',
              Pair(r,env))))))))
      
  | (Absyn.Fst e) ->
      let t' = Tcabsyn.ti tctx ctx e in (* TODO: Save types of subexpressions... *)
      let (t1,t2) = Tcabsyn.force_times t' in
      do_letpair(exp2ilcf tctx ctx cfctx e t' env, fun p env ->
      do_letpair(p, fun x1 x2 ->
      do_seq(freet' cfctx t2 x2, Pair(x1,env))))
  | (Absyn.Snd e) ->
      let t' = Tcabsyn.ti tctx ctx e in (* TODO: Save types of subexpressions... *)
      let (t1,t2) = Tcabsyn.force_times t' in
      do_letpair(exp2ilcf tctx ctx cfctx e t' env, fun p env ->
      do_letpair(p, fun x1 x2 ->
      do_seq(freet' cfctx t1 x1, Pair(x2,env))))
  | (Absyn.Lam (v,t',e')) ->
      let (t1,t2) = Tcabsyn.force_arrow t in
      let ctx' = min_ctx ctx e in
      let ct = ctxtp ctx' in
      let ct' = tp2il ct in
      let t1' = tp2il t1 in
      let t2' = tp2il t2 in
      do_letpair(ctx_copy ctx ctx' cfctx env, fun cenv env ->
      do_let (do_fn(ct', copyt' cfctx ct), fun cp -> 
      do_let (do_fn(ct', freet' cfctx ct), fun fr -> 
      do_let (do_fn(Tensor(t1',ct'),fun env -> 
	      do_letpair(exp2ilcf tctx (Ctx.extend ctx' v t') cfctx e' t2 env, fun r env -> 
	      do_letpair(env, fun x env -> 
	      do_seq(freet' cfctx t1 x,
              do_seq(freet' cfctx ct env,r))))
	      ), fun ap -> 
      Pair(do_mkclosure(ct',cenv,ap,cp, fr,closuretp t1' t2'), env)))))
  | (Absyn.Fix (f,v,t1,t2,e')) ->
      let ctx' = min_ctx ctx e in
      let ct = ctxtp ctx' in
      let ct' = tp2il ct in
      let t1' = tp2il t1 in
      let t2' = tp2il t2 in
      let ft = Absyn.Arrow(t1,t2) in
      do_letpair(ctx_copy ctx ctx' cfctx env,fun cenv env ->
      do_let (do_fn(ct', copyt' cfctx ct), fun cp -> 
      do_let (do_fn(ct', freet' cfctx ct), fun fr -> 
      do_let(do_fix(Tensor(t1',ct'),t2',fun ap env -> 
	     do_let (do_fn(ct', copyt' cfctx ct), fun cp -> 
	     do_let (do_fn(ct', freet' cfctx ct), fun fr -> 
             do_letpair(env,fun x env -> 
             do_letpair(copyt' cfctx ct env, fun cenv env ->
             do_let(Pair(x, Pair(do_mkclosure(ct',cenv,ap,cp,fr,closuretp t1' t2'),env)), fun env ->
	     do_letpair(exp2ilcf tctx 
			  (Ctx.extend (Ctx.extend ctx' f ft) v t1) 
			  cfctx e' t2 (env), fun r env -> 
	     do_letpair(env, fun x env -> 
             do_letpair(env, fun f env -> 
             do_seq(freet' cfctx t1 x,
             do_seq(freet' cfctx ft f, 
             do_seq(freet' cfctx ct env,
             r)))))))))))), fun ap -> 
      Pair(do_mkclosure(ct',cenv,ap,cp,fr,closuretp t1' t2'),env)))))
  | (Absyn.App(e1,e2)) ->
      let t' = Tcabsyn.ti tctx ctx e1 in
      let (t1,t2) = Tcabsyn.force_arrow t' in
      do_letpair(exp2ilcf tctx ctx cfctx e1 t' env,fun c env1 ->
      do_letclosure(c, fun _ cenv ap cp fr -> 
      do_letpair(exp2ilcf tctx ctx cfctx e2 t1 env1, fun x env2 ->
      do_let (App ( ap,Pair ( x,  cenv)), fun r -> 
	  Pair( r, env2)))))
  | Absyn.Nil -> Pair(Nil,env)
  | Absyn.Cons(e1,e2) -> 
      let t' = Tcabsyn.force_list t in
      do_letpair(exp2ilcf tctx ctx cfctx e1 t' env, fun x1 env -> 
      do_letpair(exp2ilcf tctx ctx cfctx e2 t  env, fun x2 env -> 
      Pair(Cons( x1,  x2), env)))
  | Absyn.Case(e,e1,x,y,e2) -> 
      let t' = Tcabsyn.ti tctx ctx e in
      let t'' = Tcabsyn.force_list t' in
      do_letpair(exp2ilcf tctx ctx cfctx e t' env , fun l env -> 
      Case(l,exp2ilcf tctx ctx cfctx e1 t env,
	   x,y,
	   do_letpair(exp2ilcf tctx 
			(Ctx.extend (Ctx.extend ctx x t'') y t') 
			cfctx e2 t 
			(Pair(Var y, Pair(Var x, env))),fun r env -> 
           do_letpair(env, fun tail env ->
	   do_seq(freet' cfctx t' tail,
	   do_letpair(env, fun head env -> 
	   do_seq(freet' cfctx t'' head,
	   	  Pair(r,env))))))))
  | Absyn.Let(x,e1,e2) ->
    let t' = Tcabsyn.ti tctx ctx e1 in
    do_letpair(exp2ilcf tctx 
		 (Ctx.extend ctx x t') 
		 cfctx e2 t 
		 (exp2ilcf tctx ctx cfctx e1 t' env), fun r env' -> 
    do_letpair(env', fun x' env'' -> 
    do_seq(freet' cfctx t' x',
    Pair(r,env''))))
  | Absyn.TLam (tv,e) -> 
      let tv,t0 = Tcabsyn.force_forall t in
      let ctx' = min_ctx ctx e in
      let ct = ctxtp ctx' in
      let ct' = tp2il ct in
      let t0' = tp2il t0 in
      do_letpair(ctx_copy ctx ctx' cfctx env, fun cenv env ->
      do_let (do_fn(ct', copyt' cfctx ct), fun cp -> 
      do_let (do_fn(ct', freet' cfctx ct), fun fr -> 
      do_let (TLam(tv,
              do_fn(Tensor(copytp (TVar tv), 
                    Tensor(freetp (TVar tv),
			   ct')),fun env -> 
	      do_letpair(env, fun cp env -> 
	      do_letpair(env, fun fr env -> 
	      do_letpair(exp2ilcf 
			   (Ctx.extend tctx tv ()) 
			   ctx 
			   (Ctx.extend cfctx tv (cp,fr)) 
			   e t0 env, fun r env -> 
              do_seq(freet' cfctx ct env,r))))
	      )), fun ap -> 
      Pair(do_mkclosure(ct',cenv,ap,cp, fr,forallclosuretp tv t0'), env)))))
  | Absyn.TApp (e,t) -> 
      let t' = tp2il t in
      let tp = Tcabsyn.ti tctx ctx e in
      let tv,tp' = Tcabsyn.force_forall tp in
      do_letpair(exp2ilcf tctx ctx cfctx e tp env, fun c env -> 
      do_letclosure(c,fun tb ev ap cp fr -> 
      do_let(do_fn(t', copyt' cfctx t), fun cp' -> 
      do_let(do_fn(t', freet' cfctx t), fun fr' -> 
      do_let(App(TApp(ap, t'), Pair(cp',Pair(fr',ev))), fun r -> 
      Pair(r,env))))))
  | _ -> raise NYI


let rec ilcf2il e = 
  let h = ilcf2il in
  match e with 
    Var v -> Var v
  | IntC i -> IntC i
  | Op(op,e1,e2) -> Op(op,h e1,h e2)
  | If(c,e,e1,e2) -> If(c,h e,h e1,h e2)
  | Pair(e1,e2) -> Pair(h e1,h e2)
  | LetPair(v1,v2,e1,e2) ->  LetPair(v1,v2,h e1,h e2)
  | Fn(x,t,e) -> Fn(x,t,h e)
  | Fix(f,x,t1,t2,e) -> Fix(f,x,t1,t2,h e)
  | App(e1,e2) -> App(h e1,h e2)
  | Pack(t,e,t') -> Pack(t,h e,t')
  | LetUnpack(tv,v,e1,e2) -> LetUnpack(tv,v,h e1,h e2)
  | TLam (tv,e) -> TLam(tv,h e)
  | TApp(e,t) -> TApp(h e, t)
  | Let(v,e1,e2) -> Let(v,h e1,h e2)
  | Nil -> Nil
  | Cons(e1,e2) -> Cons(h e1,h e2)
  | Case(e,e1,x,y,e2) -> Case(h e,h e1,x,y,h e2)
  | Copy(cfctx,tp,e) -> 
(*      print_string ("Copying "^(Absyn.pp_tp tp)^"\n");*)
      copyt cfctx tp (h e)
  | Free(cfctx,tp,e) -> 
(*      print_string ("Freeing "^(Absyn.pp_tp tp)^"\n");*)
      freet cfctx tp (h e)
;;

let exp2il tctx ctx cfctx e t env = 
  ilcf2il(exp2ilcf tctx ctx cfctx e t env)

