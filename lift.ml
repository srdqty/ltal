open Var;;
open Il;;
open Util;;

let lift e = 
  let rec subst acc e = 
    match e with
      Var v -> (Var v, acc)
    | IntC i -> (IntC i, acc)
    | Op(op,e1,e2) -> 
	let (e1',acc1) = subst acc e1 in
	let (e2',acc2) = subst acc1 e2 in
	(Op(op,e1',e2'),acc2)
    | If(c,e,e1,e2) -> 
	let (e',acc') = subst acc e in
	let (e1',acc1) = subst acc' e1 in
	let (e2',acc2) = subst acc1 e2 in
	(If(c,e',e1',e2'),acc2)
    | Pair(e1,e2) -> 
	let (e1',acc1) = subst acc e1 in
	let (e2',acc2) = subst acc1 e2 in
	(Pair(e1',e2'),acc2)
    | LetPair(v1,v2,e1,e2) ->
	let (e1',acc1) = subst acc e1 in
	let (e2',acc2) = subst acc1 e2 in
	(LetPair(v1,v2,e1',e2'),acc2)
    | Pack(t,e,t') -> 
	let (e',acc1) = subst acc e in
	(Pack(t,e',t'),acc1)
    | LetUnpack(v1,v2,e1,e2) ->
	let (e1',acc1) = subst acc e1 in
	let (e2',acc2) = subst acc1 e2 in
	(LetUnpack(v1,v2,e1',e2'),acc2)
    | Let(v,e1,e2) ->
	let (e1',acc1) = subst acc e1 in
	let (e2',acc2) = subst acc1 e2 in
	(Let(v,e1',e2'),acc2)
    | App(e1,e2) ->
	let (e1',acc1) = subst acc e1 in
	let (e2',acc2) = subst acc1 e2 in
	(App(e1',e2'),acc2)
    | Nil -> (Nil,acc)
    | Cons(e1,e2) -> 
	let (e1',acc1) = subst acc e1 in
	let (e2',acc2) = subst acc1 e2 in
	(Cons(e1',e2'),acc2)	
    | Case(e,e1,x,y,e2) -> 
	let (e',acc0) = subst acc e in
	let (e1',acc1) = subst acc0 e1 in
	let (e2',acc2) = subst acc1 e2 in
	(Case(e',e1',x,y,e2'),acc2)	
    | Copy(cfctx,tp,e) ->
      let (e',acc0) = subst acc e in
      (Copy(cfctx,tp,e'), acc0)
    | Free(cfctx,tp,e) ->
      let (e',acc0) = subst acc e in
      (Free(cfctx,tp,e'), acc0)
    | TApp(e,t) -> 
	let (e',acc0) = subst acc e in
	(TApp(e',t),acc0)
    | e -> 
	let (e', acc') = grab acc e in
	let f = mkvar "f" in
	(Var f, (f,e')::acc')
  and grab acc e = 
    match e with
      Fn (x,t,e) -> 
	let (e',acc1) = subst acc e in
	(Fn(x,t,e'),acc1) 
    | Fix (f,x,t1,t2,e) -> 
	let (e',acc1) = subst acc e in
	(Fix(f,x,t1,t2,e'), acc1) 
    | TLam (tv,e) -> 
	let (e', acc1) = grab acc e in
	(TLam(tv,e'), acc1)
	
    | e -> impos "grabbing non-function"
	
  in
  let rec bind e' acc = 
    match acc with 
      [] -> e'
    | (f,e)::acc' -> bind (Let(f,e,e')) acc'
  in
  let rec skip e = 
    match e with
      Let(f,Fn(x,t,e),e') -> 
	let e'',acc = subst [] e in
	bind (Let(f,Fn(x,t,e''),skip e')) acc
    | Let(g,Fix(f,x,t,t',e),e') -> 
	let e'',acc = subst [] e in
	bind (Let(g,Fix(f,x,t,t',e''),skip e')) acc
    | e -> 
	let (e',acc) = subst [] e  in
	bind e' acc

  in  
  skip e
