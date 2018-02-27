open Il;;
open Op;;
open Ilsubst;;


(* can we propagate a variable bound to e by a simple let?
 *)

let rec is_effect_free e = 
   match e with
    Var _ -> true
  | IntC _ -> true
  | Op(op,e1,e2) -> is_effect_free e1 && is_effect_free e2
  | If(c,e,e1,e2) -> is_effect_free e && is_effect_free e1 && is_effect_free e2
  | Pair _ -> true
  | Pack _ -> true
  | _ -> false

let rec is_function e = 
  match e with
    Fn _ -> true
  | Fix _ -> true
  | _ -> false
    
let rec copyprop e = 
  (* Search for terms of the form
     let x = e in e' (where e is not fn x => e'')
     let <x,y> = <e1,e2> in e'
     let [a,x] = [t,e] in e'
     Whenever we find one, rewrite it to e' and 
     place all the variable bindings in the substitution. 
     
     Also, for fun, evaluate any constant integer expressions or
     if's whose test is constant.
   *)
  let rec gather d g e =
    match e with
      Var v -> 
	(match fetch g v with
          None -> Var v
	| Some e -> e)
    | IntC i -> IntC i
    | Op(op,e1, e2) -> 
	let e1' = gather d g e1 in
	let e2' = gather d g e2 in
	(match (op,e1',e2') with
	  Plus,IntC i, IntC j -> IntC (i+j)
	| Plus,IntC 0, _ -> e2'
	| Plus, _, IntC 0 -> e1'
	| Minus,IntC i, IntC j -> IntC (i-j)
	| Minus,IntC 0, _ -> e2'
	| Minus, _, IntC 0 -> e1'
	| Times,IntC i, IntC j -> IntC (i*j)
	| Times,IntC 0, _ -> IntC 0
	| Times, _, IntC 0 -> IntC 0
	| Times,IntC 1, _ -> e2'
	| Times, _, IntC 1 -> e1'
	| _ -> Op(op,e1',e2'))
    | If (c,e,e1,e2) -> 
	let e' = gather d g e in
	let e1' = gather d g e1 in
	let e2' = gather d g e2 in
	(match c,e' with
	  NZ,IntC 0 -> e2'
	| NZ,IntC i -> e1'
	| LZ,IntC i -> if i < 0 then e1' else e2'
	| _ -> If(c,e',e1',e2'))
    | Pair(e1,e2) -> Pair(gather d g e1, gather d g e2)
    | LetPair(v1,v2,e1,e2) -> 
        (match gather d g e1 with
	  Pair (e11', e12') -> 
	    gather d (bind (bind g v1 e11') v2 e12') e2
	      (* ill advised *)
	| If(c,e0,e1',e2') as e0' -> 
	    let v1' = Var.rename v1 in
	    let v2' = Var.rename v2 in
	    gather d g (If(c,e0,LetPair(v1,v2,e1',e2),
			   LetPair(v1',v2',e2',
				   subst_exp id (bind (bind id v1 (Var v1')) v2 (Var v2')) 
				     e2)))
	| Case(e0,e1',hv,tv,e2') as e0' -> 
	    let v1' = Var.rename v1 in
	    let v2' = Var.rename v2 in
	    gather d g (Case(e0,LetPair(v1,v2,e1',e2),
			   hv,tv,LetPair(v1',v2',e2',
				   subst_exp id (bind (bind id v1 (Var v1')) v2 (Var v2')) 
				     e2)))
	    
	| e1' -> LetPair(v1,v2,e1',gather d g e2))
    | Pack(t,e,t') -> 
	Pack(subst_tp d t, gather d g e,subst_tp d t')
    | LetUnpack(tv,v,e1,e2) -> 
        (match gather d g e1 with
	  Pack (t', e',_) -> 
	    gather (bind d tv t') (bind g v e') e2
(*	| If(c,e0,e1',e2') -> 
	    gather d g (If(c,e0,LetUnpack(tv,v,e1',e2),
			   LetUnpack(tv,v,e2',e2)))*)
	| e1' -> LetUnpack(tv,v,e1',gather d g e2))
    | App(e1,e2) -> App(gather d g e1, gather d g e2)
    | Fn(v,t,e) -> Fn(v,subst_tp d t, gather d g e)
    | Fix(f,v,t1,t2,e) -> Fix(f,v,subst_tp d t1,subst_tp d t2, gather d g e)
    | Let(v,e1,e2) ->
	let e1' = gather d g e1 in
	if is_effect_free e1' 
	then gather d (bind g v e1') e2
	else Let(v,e1',gather d g e2)
    | Nil -> Nil
    | Cons(e1,e2) -> 
	Cons(gather d g e1, gather d g e2)
    | Case(e,e1,v,w,e2) -> 
	(match gather d g e with
	  Nil -> gather d g e1
	| Cons(e1',e2') -> gather d (bind (bind g v e1') w e2') e2
	| e' -> Case(e',gather d g e1, v, w, gather d g e2))
    | Copy(cfctx,tp, e) -> Copy(cfctx,tp, gather d g e)
    | Free(cfctx,tp, e) -> Free(cfctx,tp, gather d g e)
    | TLam (tv,e) -> 
	(match gather d g e with
	  TApp(e',t) -> 
	    gather (bind d tv t) g e'
	| e' -> TLam(tv,e'))
    | TApp (e,t) -> TApp(gather d g e, subst_tp d t)
    in gather id id e

let id x = x
let compose f g = (fun x -> (f (g x)))
    
let rec denest e = 
  let rec split e = 
    match e with 
      Let(v,e1,e2) -> 
	let (f,e1') = denest' e1 in
	let (g,e2') = split e2 in
	((fun x -> f(Let(v,e1',g x))), e2')
    | LetPair(v1,v2,e1,e2) -> 
	let (f,e1') = denest' e1 in
	let (g,e2') = split e2 in
	((fun x -> f(LetPair(v1,v2,e1',g x))), e2')
    | LetUnpack(tv,v,e1,e2) -> 
	let (f,e1') = denest' e1 in
	let (g,e2') = split e2 in
	((fun x -> f(LetUnpack(tv,v,e1',g x))), e2')
    | e -> denest' e
  and denest' e = 
    match e with
      Var v -> (id, Var v)
    | IntC i -> (id, IntC i)
    | Op(op,e1,e2) ->
	let (f,e1') = denest' e1 in
	let (g,e2') = denest' e2 in
	(compose f g, Op(op,e1',e2'))
    | If(c,e,e1,e2) ->
	let (f,e') = denest' e in
	(f, If(c,e',denest e1, denest e2))
    | Pair(e1,e2) -> 
	let (f,e1') = denest' e1 in
	let (g,e2') = denest' e2 in
	(compose f g, Pair(e1',e2')) 
    | LetPair(v1,v2,e1,e2) -> 
	let (f,e1') = split e1 in
	let (g,e2') = denest' e2 in
	((fun x -> f(LetPair(v1,v2,e1',g x))),e2')
    | Pack(t,e,t') -> 
	let (f,e') = denest' e in
	(f, Pack(t,e',t'))
    | LetUnpack(tv,v,e1,e2) -> 
	let (f,e1') = split e1 in
	let (g,e2') = denest' e2 in
	((fun x -> f(LetUnpack(tv,v,e1',g x))),e2')
    | App(e1,e2) ->
	let (f,e1') = denest' e1 in
	let (g,e2') = denest' e2 in
	(compose f g, App(e1',e2'))  
    | Fn(v,t,e) -> (id, Fn(v,t,denest e))
    | Fix(f,v,t1,t2,e) -> (id, Fix(f,v,t1,t2,denest e))
    | Let(v,e1,e2) ->
	let (f,e1') = split e1 in
	let (g,e2') = denest' e2 in
	((fun x -> f(Let(v,e1',g x))),e2') 
    | Nil -> (id, Nil)
    | Cons(e1,e2) -> 
	let (f,e1') = denest' e1 in
	let (g,e2') = denest' e2 in
	(compose f g, Cons(e1',e2')) 
    | Case(e,e1,x,y,e2) ->
	let (f,e') = denest' e in
	(f, Case(e',denest e1, x, y, denest e2))
    | Copy(cfctx,tp, e) -> 
	let (f,e') = denest' e in
	(f, Copy(cfctx,tp,e'))
    | Free(cfctx,tp, e) -> 
	let (f,e') = denest' e in
	(f, Free(cfctx,tp,e'))
    | TApp(e,t) -> 
	let (f,e') = denest' e in
	(f,TApp(e',t))
    | TLam(tv,e) -> id, TLam(tv,denest e)
  in 
  
   let (f,e') = denest' e 
   in f e'
   



(* Assumes v is in l at most once *)
let rec remove l v = 
  match l with
    [] -> []
  | v'::l' -> if Var.eq v v' then l' else v'::(remove l' v)

let rec contains l v = 
  match l with
    [] -> false
  | v' :: l' -> if Var.eq v v' then true else contains l' v
					       
(* Returns a list of free variables of the subexpression and a 
   modified subexpression.  We ignore
   the posssibility of duplicate variable names. 
   If we see a let-binding of an effect-free thing, we add it to the 
   "query" list.  When we see an occurrence of a variable, we remove it from the
   qlist if it was there and proceed.  *)
let deadcode e = 
  let rec elim ql e = 
    match e with 
      Var v -> (remove ql v,Var v)
    | IntC i -> (ql,IntC i)
    | Op(op,e1,e2) -> 
	let (ql1,e1') = elim ql e1 in
	let (ql2,e2') = elim ql1 e2 in
	(ql2,Op(op,e1',e2'))
    | If(c,e,e1,e2) -> 
	let (ql1,e') = elim ql e in
	let (ql2,e1') = elim ql1 e1 in
	let (ql3,e2') = elim ql2 e2 in
	(ql3,If(c,e,e1',e2'))
    | Pair(e1,e2) -> 
	let (ql1,e1') = elim ql e1 in
	let (ql2,e2') = elim ql1 e2 in
	(ql2,Pair(e1',e2'))
    | LetPair(v1,v2,e1,e2) ->
    	let (ql1,e1') = elim ql e1 in
	let (ql2,e2') = elim ql1 e2 in
	(ql2,LetPair(v1,v2,e1',e2'))
    | Fn(x,t,e) -> 
	let (ql1,e') = elim ql e in
	(ql1,Fn(x,t,e'))
	  (* un-fix things that don't recursively call themselves *)
    | Fix(f,x,t1,t2,e) -> 
	let (ql1,e') = elim (f::ql) e in
	if contains ql1 f 
	then (remove ql1 f, Fn(x,t1,e'))
	else (remove ql1 f, Fix(f,x,t1,t2,e'))
    | App(e1,e2) -> 
	let (ql1,e1') = elim ql e1 in
	let (ql2,e2') = elim ql1 e2 in
	(ql2,App(e1',e2'))
    | Pack(t,e,t') -> 
	let (ql1,e') = elim ql e in
	(ql1,Pack(t,e',t'))
    | LetUnpack(tv,v,e1,e2) -> 
    	let (ql1,e1') = elim ql e1 in
	let (ql2,e2') = elim ql1 e2 in
	(ql2,LetUnpack(tv,v,e1',e2'))
    | Let(v,e1,e2) ->
	let (ql1,e1') = elim ql e1 in
	if(is_effect_free(e1') || is_function(e1')) 
	then 
	  let (ql2,e2') = elim (v::ql1) e2 in
	  if contains ql2 v then (remove ql2 v, e2')
	  else (remove ql2 v, Let(v,e1',e2'))
	else let (ql2,e2') = elim ql1 e2 in
	(ql2,Let(v,e1',e2'))
    | Nil -> (ql,Nil)
    | Cons(e1,e2) -> 
	let (ql1,e1') = elim ql e1 in
	let (ql2,e2') = elim ql1 e2 in
	(ql2,Cons(e1',e2'))
    | Case(e,e1,x,y,e2) -> 
	let (ql1,e') = elim ql e in
	let (ql2,e1') = elim ql1 e1 in
	let (ql3,e2') = elim ql2 e2 in
	(ql3,Case(e,e1',x,y,e2'))
    | Copy(cfctx,tp,e) -> 
	let (ql',e') = elim ql e in
	(ql', Copy(cfctx,tp,e'))
    | Free(cfctx,tp,e) -> 
	let (ql',e') = elim ql e in
	(ql', Free(cfctx,tp,e'))
    | TLam(tv,e) -> 
	let (ql',e') = elim ql e in
	(ql', TLam(tv,e'))
    | TApp(e,t) -> 
	let (ql',e) = elim ql e in
	(ql', TApp(e,t))
  in 
  let (_,e') = elim [] e in
  e'

module VarSet = Set.Make(struct type t = Var.var let compare = Var.compare end)


let cfelim e = 
  let empty = VarSet.empty in
  let mem = VarSet.mem in
  let (||) = VarSet.union in
  let (&&) = VarSet.inter in
  let add = VarSet.add in
  let rec freed e = 
    match e with 
      Var v -> empty
    | IntC i -> empty
    | Op(op,e1,e2) -> freed e1 || freed e2
    | If(c,e,e1,e2) -> freed e || (freed e1 && freed e2)
    | Pair(e1,e2) -> freed e1 || freed e2 
    | LetPair(v1,v2,e1,e2) -> freed e1 || freed e2
    | Fn(x,t,e) -> freed e
    | Fix(f,x,t1,t2,e) -> freed e
    | App(e1,e2) -> freed e1 || freed e2
    | Pack(t,e,t') -> freed e
    | LetUnpack(tv,v,e1,e2) -> freed e1 || freed e2
    | Let(v,e1,e2) -> freed e1 || freed e2
    | Nil -> empty
    | Cons(e1,e2) -> freed e1 || freed e2
    | Case(e,e1,x,y,e2) -> freed e || (freed e1 && freed e2)
    | Copy(cfctx,tp,e) -> freed e
    | Free(cfctx,tp,Var v) -> add v empty
    | Free(cfctx,tp,e) -> freed e 
    | TLam(tv,e) -> freed e 
    | TApp(e,t) -> freed e
  in
  
  let rec felim w e = 
    let h = felim w in
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
    | Let(v,e1,e2) -> Let(v,h e1,h e2)
    | Nil -> Nil
    | Cons(e1,e2) -> Cons(h e1,h e2)
    | Case(e,e1,x,y,e2) -> Case(h e,h e1,x,y,h e2)
    | Copy(cfctx,tp,e) -> Copy(cfctx,tp,h e)
    | Free(cfctx,tp,Var v) -> 
	if Var.eq v w then IntC (-1) else Free(cfctx,tp,Var v)
    | Free(cfctx,tp,e) -> Free(cfctx,tp,h e) 
    | TLam(tv,e) -> TLam(tv, h e)
    | TApp(e,t) -> TApp(h e, t)
  in
  
  let rec celim e = 
    let h = celim in
    match e with 
      Var v -> Var v
    | IntC i -> IntC i
    | Op(op,e1,e2) -> Op(op,h e1,h e2)
    | If(c,e,e1,e2) -> If(c,h e,h e1,h e2)
    | Pair(e1,e2) -> Pair(h e1,h e2)
    | LetPair(v1,v2,Copy(cfctx,tp,e),e2) ->  
	let fdvs = freed e2 in
	(match mem v1 fdvs, mem v2 fdvs with
	  true,_ -> Let(v2,e,felim v1 e2)
	| _,true -> Let(v1,e,felim v2 e2)
	| false, false -> LetPair(v1,v2,Copy(cfctx,tp,h e),h e2)
	) 
    | LetPair(v1,v2,e1,e2) ->  LetPair(v1,v2,h e1,h e2)
    | Fn(x,t,e) -> Fn(x,t,h e)
    | Fix(f,x,t1,t2,e) -> Fix(f,x,t1,t2,h e)
    | App(e1,e2) -> App(h e1,h e2)
    | Pack(t,e,t') -> Pack(t,h e,t')
    | LetUnpack(tv,v,e1,e2) -> LetUnpack(tv,v,h e1,h e2)
    | Let(v,e1,e2) -> Let(v,h e1,h e2)
    | Nil -> Nil
    | Cons(e1,e2) -> Cons(h e1,h e2)
    | Case(e,e1,x,y,e2) -> Case(h e,h e1,x,y,h e2)
    | Copy(cfctx,tp,e) -> Copy(cfctx,tp,h e)
    | Free(cfctx,tp,e) -> Free(cfctx,tp,h e)
    | TLam(tv,e) -> TLam(tv, h e)
    | TApp(e,t) -> TApp(h e, t)
  in 
  celim e

(* TODO: Generalize to inline toplevel polymorphic functions also. *)    
let inline e0 = 
  let rec build_dict e = 
    match e with
      Let(f, Fn(x, t, e), e') -> 
	let (d,e'') = build_dict e' in
	((f,None,x,t,e)::d, e'')
    | Let(f, Fix(g,x,t,t',e), e') -> 
	let (d,e'') = build_dict e' in
	((f,Some (g,t'),x,t,e)::d, e'')
    | e -> ([],e)
  in 
  let rec restore dict e = 
    match dict with
      [] -> e
    | (f,None,x,t,e')::l -> 
	(Let(f, Fn(x, t, e'), restore l e))
    | (f,Some (g,t'),x,t,e')::l -> 
	(Let(f, Fix(g,x, t,t', e'), restore l e))
  in
  let fnlookup f (f',ntopt,_,_,_) = ntopt = None && Var.eq f f' in
  let rec inl' dict e =
    let inl = inl' dict in
    match e with
      Var v -> Var v
    | IntC i -> IntC i
    | Op(op,e1,e2) -> 
	Op(op,inl e1, inl e2)
    | If(c,e,e1,e2) ->
      If(c,inl e, inl e1, inl e2)
    | Pair(e1,e2) ->
	Pair(inl e1, inl e2)
    | LetPair(v1,v2,e1,e2) ->
	LetPair(v1,v2,inl e1,inl e2) 
    | App(Var v, e) -> 
	(let entry = 
	  (try
	    Some (List.find (fnlookup v) dict)
	  with Not_found -> 
	    None) in
	  match  entry with
	    Some(f,None,x,_,e') ->
	      (* Don't further inline the function body... *)
	       rename (Let(x,e, e'))
	  | Some(f,Some(g,_),x,_,e') -> 
	      rename (Let(x,e,Let(g,Var f,  e')))
	  | None -> App(Var v, inl e))
	
    | App(e1,e2) -> (* Should be impossible, but can't hurt *)
	App(inl e1, inl e2)
    | Fn(x,t,e) -> 
	Fn (x,t,inl e)
    | Fix(f,x,t1,t2,e) -> 
	Fix (f,x,t1,t2,inl e)
    | Pack(t,e,t') ->
	Pack(t,inl e, t')
    | LetUnpack(tv,v,e1,e2) -> 
	LetUnpack(tv,v,inl e1, inl e2)
    | Let(v,e,e') ->
	Let(v,inl e, inl e')
    | Nil -> Nil
    | Cons(e1,e2) -> Cons(inl e1, inl e2)
    | Case(e,e1,x,y,e2) ->
	Case(inl e, inl e1, x, y, inl e2)
    | Copy(cfctx,tp,e) -> Copy(cfctx,tp,inl e)
    | Free(cfctx,tp,e) -> Free(cfctx,tp,inl e)
    | TLam(tv,e) -> TLam(tv, inl e)
    | TApp(e,t) -> TApp(inl e, t)
	  
  in
  let rec inl_dict dict d = 
    match d with
      [] -> []
    | (f,ntopt,x,t,e')::d' -> 
	(f,ntopt,x,t, inl' dict e')::(inl_dict dict d') in
    
  let (dict,e') = build_dict e0 in
  let dict = inl_dict dict dict in
  let e'' = inl' dict e' in
  restore dict e''
    
