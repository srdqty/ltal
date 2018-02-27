open Op;;
open Ctx;;
open Il;;
open Ilsubst;;
open Util;;

let rec flatten_tp tp = 
  match tp with
    Arrow(t1,t2) -> tp
  | Int -> Int
  | Forall(tv,t) -> Forall(tv,flatten_tp t)
  | t -> Top

let rec is_flat tp = 
  match tp with
    Int -> true
  | Arrow(_,_) -> true
  | Forall(tv,t) -> is_flat t
  | Top -> true
  | _ -> false

let flatten_ctx ctx = Ctx.map (fun v t -> flatten_tp t) ctx

let rec flatten_ctx_var ctx v = 
  let t = Ctx.lookup ctx v in
  (t,Ctx.update ctx v (flatten_tp t))
	  


let unify t1 t2 = 
  let rec unify' l t1 t2 = 
    match (t1,t2) with
      Int,Int -> ()
    | Top, Top -> ()
    | TVar a, TVar b -> 
	if Var.eq a b then () 
	else 
	  (try 
	    let (_,_) = List.find (fun (x,y) -> Var.eq a x && Var.eq b y) l in
	    ()
	  with Not_found -> 
	    tcfail ("type variables "
			  ^(Var.to_string a)^" and "
			  ^(Var.to_string b)^" don't match"))
    | Arrow(t1,t2), Arrow(t1',t2') -> 
	unify' l t1 t1';
	unify' l t2 t2'
    | Tensor (t1,t2), Tensor(t1',t2') -> 
	unify' l t1 t1';
	unify' l t2 t2'
    | Exists (v,t), Exists(v',t') -> 
	unify' ((v,v')::l) t t'
    | Forall (v,t), Forall(v',t') -> 
	unify' ((v,v')::l) t t'
    | List t, List t' ->
	unify' l t t'
    | _,_ -> tcfail ("type constructors "
			    ^(Il.pp_tp t1)^" and "
			    ^(Il.pp_tp t2)^" are incompatible")
  in
  try unify' [] t1 t2
  with TcFail msg  -> 
    tcfail ("types "
		   ^(Il.pp_tp t1)^" and "
		   ^(Il.pp_tp t2)^" failed to unify because\n"^msg)
  

let unify_ctx ctx1 ctx2 = 
  let rec unify' d1 d2 = 
    match d1, d2 with
      [],[] -> ()
    | (v) :: d1, (v')::d2 -> 
	if Var.eq v v' 
	then 
	  try unify (Ctx.lookup ctx1 v) (Ctx.lookup ctx2 v)
	  with TcFail msg -> tcfail ("for variable "^(Var.to_string v)^", ")
	else tcfail ("variables "^(Var.to_string v)^" and "
		     ^(Var.to_string v')^" don't match")
    | _ -> tcfail ("the contexts were of different sizes")
  in 
  try 
    unify' (Ctx.dom ctx1) (Ctx.dom  ctx2)
  with TcFail msg -> tcfail ("Context unification failed because\n"^msg)

let rec retract ctx v = 
  let t = lookup_or_fail ctx v in
  if is_flat(t) 
  then Ctx.remove ctx v
  else tcfail ("linear variable "^(Var.to_string v)^":"^(Il.pp_tp t)^" unused")



let force_int t = 
  match t with
    Int -> ()
  | _ -> tcfail("expected int, not "^(Il.pp_tp t))

let force_tensor t = 
  match t with
    Tensor(t1,t2) -> (t1,t2)
  | _ -> tcfail("expected pair, not "^(Il.pp_tp t))


let force_arrow t = 
  match t with
    Arrow(t1,t2) -> (t1,t2)
  | _ -> tcfail("expected function type, not "^(Il.pp_tp t))


let force_exists t = 
  match t with
    Exists(v,t) -> (v,t)
  | _ -> tcfail ("expected existential type, not "^(Il.pp_tp t))

let force_forall t = 
  match t with
    Forall(v,t) -> (v,t)
  | _ -> tcfail ("expected universal type, not "^(Il.pp_tp t))

let force_list t = 
  match t with
    List(t) -> (t)
  | _ -> tcfail ("expected list type, not "^(Il.pp_tp t))

let flatten_or_fail ctx v = 
  try flatten_ctx_var ctx v
  with Not_found -> tcfail ("Unbound variable " ^ (Var.to_string v))

let rec twf tctx t = 
  match t with
    Int -> ()
  | Top -> ()
  | TVar v -> lookup_or_fail tctx v
  | Arrow(t1,t2) -> twf tctx t1; twf tctx t2
  | Tensor(t1,t2) ->  twf tctx t1; twf tctx t2
  | Forall(v,t) -> twf (extend tctx v ()) t
  | Exists(v,t) -> twf (extend tctx v ()) t
  | List t -> twf tctx t

let rec tc tctx ctx e t :ctx=  
  try 
  match e with
    Var v -> 
      let (t',ctx') = flatten_or_fail ctx v in
      unify t t';
      ctx'
  | IntC i -> 
      force_int t;
      ctx
  | Op(opr,e1,e2) ->
      force_int t;
      let ctx' = tc tctx ctx e1 Int in
      tc tctx ctx' e2 Int
  | If (c,e,e1,e2) -> 
      let ctx' = tc tctx ctx e Int in
      let ctx'' = tc tctx ctx' e1 t in
      let ctx''' = tc tctx ctx' e2 t in
      unify_ctx ctx'' ctx''';
      ctx''
  | Pair(e1,e2) -> 
      let (t1,t2) = force_tensor t in
      let ctx' = tc tctx ctx e1 t1 in
      tc tctx ctx' e2 t2
  | LetPair (v1,v2,e1,e2) -> 
      let (t0,ctx') = (ti tctx ctx e1) in
      let (t1',t2') = force_tensor t0 in
      let ctx'' = tc tctx (extend (extend ctx' v1 t1') v2 t2') e2 t in
      retract (retract ctx'' v2) v1
  | Fn (x,t',e) ->
      let (t1,t2) = force_arrow t in
      unify t' t1;
      let ctx' = tc emp (extend (flatten_ctx ctx) x t') e t2 in
      let _ = retract ctx' x in
      ctx (* restore original ctxt since function didn't affect it *)
  | Fix (f,x,t1',t2',e) ->
      let (t1,t2) = force_arrow t in
      unify t1' t1;
      unify t2' t2;
      let ctx' = tc emp (extend (extend (flatten_ctx ctx) f t) x t1) e t2 in
      let _ = retract (retract ctx' x) f in
      ctx (* restore original ctxt since function didn't affect it *)
  | App (e1,e2) ->
      let (t1,ctx') = ti tctx ctx e1 in 
      let (t1',t2') = force_arrow t1 in
      let ctx'' = tc tctx ctx' e2 t1' in
      unify t t2';
      ctx''
  | Pack(t1,e,t') -> 
      unify t t';
      let (v,t'') = force_exists t in
      tc tctx ctx e (subst1_tp v t1 t'')
      
  | LetUnpack(tv,v,e1,e2) -> 
      twf tctx t;
      let (t1,ctx') = ti tctx ctx e1 in
      let (v',t1') = force_exists t1 in
      let ctx'' = 
	tc (extend tctx tv ()) 
	  (extend ctx' v (subst1_tp v' (TVar tv) t1'))
	  e2 t in
      retract ctx'' v
  | TLam (tv,e) -> 
      let tv',t' = force_forall t in
      tc (extend tctx tv ()) ctx e (subst1_tp tv' (TVar tv) t')
  | TApp (e,t') -> 
      twf tctx t';
      let v,t'' = force_forall t in
      tc tctx ctx e (subst1_tp v t' t'')
  | Let(v,e1,e2) -> 
      let (t1,ctx') = (ti tctx ctx e1) in
      let ctx'' = tc tctx (extend ctx' v t1) e2 t in
      retract ctx'' v
  | Nil -> 
      let _ = force_list t in 
      ctx
  | Cons (e1,e2) -> 
      let t' = force_list t in
      let ctx' = tc tctx ctx e1 t' in
      tc tctx ctx' e2 t
  | Case (e,e1,x,y,e2) ->
      let listtp,ctx' = ti tctx ctx e in
      let elttp = force_list listtp in 
      let ctx1 = tc tctx ctx' e1 t in
      let ctx2 = tc tctx (extend (extend ctx' x elttp) y listtp) e2 t in
      let ctx2' = retract (retract ctx2 y) x in
      unify_ctx ctx1 ctx2';
      ctx2'
  
  | _ -> impos "copy, free not supported"
  with TcFail msg -> print_string("in expression "^(Il.pp_exp' e)^", "^msg);
    raise NYI
      
  and ti tctx ctx e  = 
  try 
    match e with
    Var v -> flatten_or_fail ctx v
  | IntC i -> (Int,ctx)
  | Op(opr, e1,e2) -> 
      let ctx' = tc tctx ctx e1 Int in
      (Int,tc tctx ctx' e2 Int)
  | If(c, e, e1, e2) ->
      let ctx' = tc tctx ctx e Int in
      let (t1,ctx'') = ti tctx ctx' e1 in
      let ctx''' = tc tctx ctx' e2 t1 in
      unify_ctx ctx'' ctx''';
      (t1,ctx'')
  | Pair(e1,e2) ->
      let t1,ctx' = ti tctx ctx e1 in
      let t2,ctx'' = ti tctx ctx' e2 in
      (Tensor(t1,t2),ctx'')
  | LetPair (v1,v2,e1,e2) -> 
      let t0,ctx' = (ti tctx ctx e1) in
      let (t1',t2') = force_tensor t0 in
      let (t,ctx'') = ti tctx (extend (extend ctx' v1 t1') v2 t2') e2 in
      (t, retract (retract ctx'' v2) v1)
  | Fn (x, t1, e) -> 
      let t2, ctx' = ti emp (extend (flatten_ctx ctx) x t1) e in
      let _ = retract ctx' x in (* checks that arg was used *)
      (Arrow (t1,t2), ctx) (* restore original ctxt since call didn't affect it *)
  | Fix (f,x,t1,t2,e) ->
      let t = Arrow(t1,t2) in
      let ctx' = tc emp (extend (extend (flatten_ctx ctx) f t) x t1) e t2 in
      let _ = retract (retract ctx' x) f in
      (t,ctx) (* restore original ctxt since function didn't affect it *)
  | App (e1, e2) ->
      let (t1,ctx') = (ti tctx ctx e1) in 
      let (t1',t2') = force_arrow t1 in 
      let ctx'' = tc tctx ctx' e2 t1' in
      (t2', ctx'')
  | Pack(t1,e,t') -> 
      let (v,t'') = force_exists t' in
      let ctx' = tc tctx ctx e (subst1_tp v t1 t'') in
      (t',ctx')
  | LetUnpack(tv,v,e1,e2) -> 
      let t1, ctx' = (ti tctx ctx e1) in
      let (tv',t1') = force_exists t1 in
      let t',ctx'' = ti (extend tctx tv ()) 
	          (extend ctx' v (subst1_tp tv' (TVar tv) t1'))
	          e2 in
      twf tctx t';
      (t', retract ctx'' v)
  | TLam (tv,e) -> 
      let t,ctx = ti (extend tctx tv ()) ctx e in
      Forall(tv, t),ctx
  | TApp (e,t) -> 
      twf tctx t;
      let t0,ctx = ti tctx ctx e in
      let v,t' = force_forall t0 in
      subst1_tp v t t', ctx
  | Let(v,e1,e2) -> 
      let t1,ctx' = (ti tctx ctx e1) in
      let t2, ctx'' = ti tctx (extend ctx' v t1) e2 in
      (t2, retract ctx'' v)
  | Nil -> List(Int),ctx (* can't do any better without polymorphism *)
  | Cons (e1,e2) -> 
      let t,ctx' = ti tctx ctx e1 in
      let ctx'' = tc tctx ctx' e2 (List t) in
      (List t), ctx''
  | Case (e,e1,x,y,e2) ->
      let listtp,ctx' = ti tctx ctx e in
      let elttp = force_list listtp in 
      let rettp,ctx1 = ti tctx ctx' e1 in
      let ctx2 = tc tctx (extend (extend ctx' x elttp) y listtp) e2 rettp in
      let ctx2' = retract (retract ctx2 y) x in
      unify_ctx ctx1 ctx2';
      rettp,ctx2'
  | _ -> impos "copy, free not supported"
  with TcFail msg -> print_string("in expression "^(Il.pp_exp' e)^", "^msg);
    raise NYI

let tc_closed e tp = 
  let ctx = (tc Ctx.emp Ctx.emp e tp) in
  if Ctx.is_empty ctx
  then ()
  else tcfail ("context "^(Ctx.pp_ctx Il.pp_tp ctx)^" is not used")

let ti_closed e = 
  let tp,ctx = ti Ctx.emp Ctx.emp e in
  if Ctx.is_empty ctx
  then tp
  else tcfail ("context "^(Ctx.pp_ctx Il.pp_tp ctx)^" is not used")
