open Il;;
type var = Il.var;;


type 'a subst = 'a Var.map
let id = Var.empty

let bind s v t = Var.add v t s
let rec fetch s v = try Some(Var.find v s)
with Not_found -> None


let rec subst_tp d t = 
  match t with 
    Int -> Int
  | Top -> Top
  | TVar(v) -> 
      (match fetch d v with
        None -> TVar v
      | Some e -> e)
  | Arrow(t1,t2) -> Arrow(subst_tp d t1, subst_tp d t2)
  | Tensor(t1,t2) -> Tensor(subst_tp d t1, subst_tp d t2)
  | Exists(v,t) -> Exists(v,subst_tp d t)
  | Forall(v,t) -> Forall(v,subst_tp d t)
  | List t -> List (subst_tp d t)

let rec subst_exp d g e : Il.exp = 
  let rec h e = 
  match e with
    IntC i -> IntC i
  | Var v -> 
      (match fetch g v with
        None -> Var v
      | Some e -> e)
  | Op(op,e1,e2) -> Op(op, h e1, h e2)
  | If(c,e,e1,e2) -> If (c,h e, h e1, h e2)
  | Pair(e1,e2) -> Pair(h e1, h e2)
  | LetPair(v1,v2,e1,e2) -> LetPair(v1,v2,h e1,h e2)
  | Pack(t,e,t') -> Pack(subst_tp d t, h e, subst_tp d t')
  | LetUnpack(v1,v2,e1,e2) -> LetUnpack(v1,v2,h e1,h e2)
  | TApp(e,t) -> TApp(h e, subst_tp d t)
  | TLam (tv,e) -> TLam (tv, h e)
  | Let(v,e1,e2) -> Let(v,h e1, h e2)
  | App(e1,e2) -> App(h e1, h e2)
  | Fn(v,t,e) -> Fn(v, subst_tp d t, h e)
  | Fix(f,x,t1,t2,e) -> Fix(f,x, subst_tp d t1, subst_tp d t2, h e)
  | Nil -> Nil
  | Cons (e1,e2) -> Cons(h e1, h e2)
  | Case (e,e1,x,y,e2) -> Case(h e, h e1, x, y, h e2)
  | Copy (cfctx,tp,e) -> Copy(Ctx.map' (fun (x,y) -> h x, h y) cfctx, tp, h e)
  | Free (cfctx,tp,e) -> Free(Ctx.map' (fun (x,y) -> h x, h y) cfctx, tp, h e)
  in h e


let subst1_tp v t t' = subst_tp (bind id v t) t'
let subst1_exp v e e' = subst_exp id (bind id v e) e'

(* Todo: rename type variables?  Shouldn't be a problem... *)
let rename e = 
  let rec ren ctx e =
    let h = ren ctx in
    match e with
      Var v -> 
	(try Var (Ctx.lookup ctx v)
	with Not_found -> Var v)
    | IntC i -> IntC i
    | Op(op,e1,e2) -> Op(op,h e1, h e2)
    | If(c,e,e1,e2) -> If(c,h e, h e1, h e2)
    | Pair(e1,e2) -> Pair(h e1, h e2)
    | LetPair(v1,v2,e1,e2) -> 
	let v1' = Var.rename(v1) in
	let v2' = Var.rename(v2) in
	let ctx' = Ctx.extend (Ctx.extend ctx v1 v1') v2 v2' in
	LetPair(v1',v2',h e1, ren ctx' e2)
    | Fn (x,t,e) -> 
	let x' = Var.rename(x) in
	let ctx' = Ctx.extend ctx x x' in
	Fn(x',t,ren ctx e)
    | Fix(f,x,t1,t2,e) -> 	
	let f' = Var.rename(f) in
	let x' = Var.rename(x) in
	let ctx' = Ctx.extend (Ctx.extend ctx f f') x x' in
	Fix(f',x', t1,t2,ren ctx' e)
    | App(e1,e2) -> App(h e1, h e2)
    | Pack(t1,e,t2) -> Pack(t1,h e, t2)
    | LetUnpack(tv,x,e1,e2) -> 
	let x' = Var.rename(x) in
	let ctx' = Ctx.extend ctx x x' in
	LetUnpack(tv,x',h e1, ren ctx' e2)
    | TApp(e,t) -> TApp(h e, t)
    | TLam(tv,e) -> TLam(tv,h e)

    | Let(x,e1,e2) -> 
	let x' = Var.rename(x) in
	let ctx' = Ctx.extend ctx x x' in
	Let(x',h e1, ren ctx' e2)
    | Nil -> Nil
    | Cons(e1,e2) -> Cons(h e1, h e2)
    | Case(e,e1,v1,v2,e2) -> 
	let v1' = Var.rename(v1) in
	let v2' = Var.rename(v2) in
	let ctx' = Ctx.extend (Ctx.extend ctx v1 v1') v2 v2' in
	Case(h e, h e1, v1',v2', ren ctx' e2)
    | Copy(cfctx,tp,e) -> Copy(Ctx.map' (fun (x,y) -> h x, h y) cfctx,tp,h e)
    | Free(cfctx,tp,e) -> Free(Ctx.map' (fun (x,y) -> h x, h y) cfctx,tp,h e)
  in ren Ctx.emp e
