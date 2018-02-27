
open Op;;
open Ctx;;
open Absyn;;
open Util;;

type var = Ctx.var
type ctx = Absyn.tp Ctx.ctx
type tctx = unit Ctx.ctx

let rec subst1_tp tv t t' = 
  let h = subst1_tp tv t in
  match t' with
    TVar tv' -> if Var.eq tv tv' then t else TVar tv'
  | Forall(tv',t'') -> 
      if Var.eq tv tv' 
      then Forall(tv',t) 
      else Forall(tv',h t'')
  | Int -> Int
  | Times(t1,t2) -> Times(h t1, h t2)
  | Arrow(t1,t2) -> Arrow(h t1, h t2)
  | List(t1) -> List(h t1)
 


let rec unify' ctx t1 t2 = 
  try match (t1,t2) with
    Int,Int -> ()
  | Arrow(t1,t2), Arrow(t1',t2') -> 
      unify' ctx t1 t1';
      unify' ctx t2 t2'
  | Times (t1,t2), Times(t1',t2') -> 
      unify' ctx t1 t1';
      unify' ctx t2 t2'
  | List t, List t' ->
      unify' ctx t t'
  | TVar tv, TVar tv' -> 
      if Var.eq tv tv' then () 
      else if Var.eq (lookup ctx tv) tv' then ()
      else tcfail ""
  | Forall (tv,t), Forall(tv',t') -> 
      unify' (extend ctx tv  tv') t t'
  | _,_ -> tcfail ("")
  with _ -> tcfail ("types "^(Absyn.pp_tp t1)^" and "^(Absyn.pp_tp t2)^" failed to unify")

let unify = unify' Ctx.emp

let force_int t = 
  match t with
    Int -> ()
  | _ -> tcfail ("expected int, not "^(Absyn.pp_tp t))

let force_times t = 
  match t with
    Times(t1,t2) -> (t1,t2)
  | _ -> tcfail ("expected pair, not "^(Absyn.pp_tp t))


let force_arrow t = 
  match t with
    Arrow(t1,t2) -> (t1,t2)
  | _ -> tcfail ("expected function type, not "^(Absyn.pp_tp t))

let force_list t = 
  match t with
    List t' -> t'
  | _ -> tcfail ("expected list type, not "^(Absyn.pp_tp t))

let force_forall t = 
  match t with
    Forall(tv,t) -> tv,t
  | _ -> tcfail ("expected forall type, not "^(Absyn.pp_tp t))

let rec wf_tp tctx t = 
  let h = wf_tp tctx in
  match t with
    Int -> ()
  | Times(t1,t2) -> h t1; h t2
  | Arrow(t1,t2) -> h t1; h t2
  | List(t) -> h t 
  | Forall(tv,t) -> wf_tp (extend tctx tv ()) t
  | TVar tv -> lookup_or_fail tctx tv

let rec tc tctx ctx e t = 
  try
  match e with
    Var v -> unify (lookup_or_fail ctx v) t
  | IntC i -> force_int t
  | Op(opr,[e1;e2]) ->
      force_int t;
      tc tctx ctx e1 Int;
      tc tctx ctx e2 Int
  | Op(opr, _) -> tcfail "wrong number of arguments to int operation"
  | If(c,e,e1,e2) -> 
      tc tctx ctx e Int;
      tc tctx ctx e1 t;
      tc tctx ctx e2 t
  | Pair(e1,e2) -> 
      let (t1,t2) = force_times t in
      tc tctx ctx e1 t1;
      tc tctx ctx e2 t2
  | LetPair(x,y,e1,e2) -> 
      let (t1,t2) = force_times (ti tctx ctx e1) in
      tc tctx (Ctx.extend (Ctx.extend ctx x t1) y t2) e2 t
  | Fst e ->
      let (t1,t2) = force_times (ti tctx ctx e) in 
      unify t1 t;
  | Snd e ->
      let (t1,t2) = force_times (ti tctx ctx e) in 
      unify t2 t;
  | Lam (x,t',e) ->
      let (t1,t2) = force_arrow t in
      unify t' t1;
      tc tctx (extend ctx x t') e t2
  | Fix (f,x,t1',t2',e) ->
      let (t1,t2) = force_arrow t in
      unify t1' t1;
      unify t2' t2;
      tc tctx (extend (extend ctx f (Arrow (t1, t2))) x t1) e t2
  | App (e1,e2) ->
      let (t1,t2) = force_arrow (ti tctx ctx e1) in
      tc tctx ctx e2 t1;
      unify t t2
  | Nil -> 
      let _ = force_list t in ()
  | Cons(e1,e2) -> 
      let t' = force_list t in 
      tc tctx ctx e1 t';
      tc tctx ctx e2 t
  | Case(e,e1,x,y,e2) -> 
      let t' = force_list (ti tctx ctx e) in
      tc tctx ctx e1 t;
      tc tctx (extend (extend ctx x t') y (List t')) e2 t
  | Let(x,e1,e2) -> 
      let t' = ti tctx ctx e1 in
      tc tctx (extend ctx x t') e2 t
  | TLam (tv,e) -> 
      let tv',t' = force_forall t in
      tc (extend tctx tv ()) ctx e (subst1_tp tv' (TVar tv) t')
  | TApp (e,t') -> 
      wf_tp tctx t';
      print_string ((Absyn.pp_tp (t'))^"\n");
      let v,t'' = force_forall t in
      tc tctx ctx e (subst1_tp v t' t'')
  with TcFail msg -> print_string ("in expression "^(Absyn.pp_exp e)^", "^msg); 
    raise NYI

and ti tctx ctx e = 
  try
  match e with
    Var v -> lookup_or_fail ctx v
  | IntC i -> Int
  | Op(opr, [e1;e2]) -> 
      tc tctx ctx e1 Int;
      tc tctx ctx e2 Int;
      Int
  | Op(opr, _) -> tcfail "wrong number of arguments to int operation"
  | If(c, e, e1, e2) ->
      tc tctx ctx e Int;
      let t1 = ti tctx ctx e1 in
      tc tctx ctx e2 t1;
      t1
  | Pair(e1,e2) ->
      let t1 = ti tctx ctx e1 in
      let t2 = ti tctx ctx e2 in
      (Times(t1,t2))
  | LetPair(x,y,e1,e2) -> 
      let (t1,t2) = force_times (ti tctx ctx e1) in
      ti tctx (Ctx.extend (Ctx.extend ctx x t1) y t2) e2
  | Fst e ->
      let (t1,t2) = force_times (ti tctx ctx e) in t1
  | Snd e ->
      let (t1,t2) = force_times (ti tctx ctx e) in t2
  | Lam (x, t, e) -> (Arrow (t, (ti tctx (extend ctx x t) e)))
  | Fix (f,x,t1,t2,e) ->
      tc tctx (extend (extend ctx f (Arrow (t1, t2))) x t1) e t2;
      Arrow(t1,t2)
  | App (e1, e2) ->
      let (t1,t2) = force_arrow (ti tctx ctx e1) in 
      tc tctx ctx e2 t1;
      t2
  | Nil -> List(Int) (* can't handle this right without polymorphism *)
  | Cons(e1,e2) -> 
      let t = ti tctx ctx e1 in
      tc tctx ctx e2 (List t);
      List(t)
  | Case(e,e1,x,y,e2) -> 
      let t' = force_list (ti tctx ctx e) in
      let t = ti tctx ctx e1 in
      tc tctx (extend (extend ctx x t') y (List t')) e2 t;
      t
  | Let(x,e1,e2) -> 
      let t' = ti tctx ctx e1 in
      ti tctx (extend ctx x t') e2
  | TLam (tv,e) -> 
      let t = ti (extend tctx tv ()) ctx e in
      Forall(tv, t)
  | TApp (e,t) -> 
      wf_tp tctx t;
      print_string ((Absyn.pp_tp (t))^"\n");
      let v,t' = force_forall (ti tctx ctx e) in
      subst1_tp v t t'
  with TcFail msg -> print_string ("in expression "^(Absyn.pp_exp e)^", "^msg); 
    raise NYI



