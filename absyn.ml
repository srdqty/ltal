

open Op;;
open Util;;


type 'v tp0 = Int
  | Times of 'v tp0 * 'v tp0
  | Arrow of 'v tp0 * 'v tp0
  | List of 'v tp0
  | Forall of 'v * 'v tp0
  | TVar of 'v


type 'v exp0 = Var of 'v
  | IntC of int
  | Op of Op.op * ('v exp0) list
  | If of cond * 'v exp0 * 'v exp0 * 'v exp0
  | Pair of 'v exp0 * 'v exp0
  | LetPair of 'v * 'v * 'v exp0 * 'v exp0
  | Fst of 'v exp0
  | Snd of 'v exp0
  | Lam of 'v * 'v tp0 * 'v exp0
  | Fix of 'v * 'v * 'v tp0 * 'v tp0 * 'v exp0
  | App of 'v exp0 * 'v exp0
  | Nil
  | Cons of 'v exp0 * 'v exp0
  | Case of 'v exp0 * 'v exp0 * 'v * 'v * 'v exp0
  | Let of 'v * 'v exp0 * 'v exp0
  | TLam of 'v * 'v exp0
  | TApp of 'v exp0 * 'v tp0

type atp = string tp0;;
type tp = Var.var tp0;;
type aexp = string exp0;;
type exp = Var.var exp0

let rec pp_tp0 f t = 
  match t with 
    Int -> "int"
  | Arrow(t1,t2) -> (pp_tp0 f t1) ^ " -> (" ^ (pp_tp0 f t2) ^ ")"
  | Times(t1,t2) -> (pp_tp0 f t1) ^ " * " ^ (pp_tp0 f t2)
  | List(t) -> "("^ (pp_tp0 f t) ^ ") list"
  | TVar v -> f v
  | Forall (tv,t) -> "(forall "^(f tv)^" . "^(pp_tp0 f t)^")"

let pp_tp t = pp_tp0 Var.to_string t
let pp_atp t = pp_tp0 (fun x -> x) t


let pp_exp0 f e = 
  let rec pp i e = 
    match e with
      Var v -> f v
    | IntC i -> string_of_int i
    | Op(op,[e1;e2]) -> "("^(pp i e1) ^") "^(Op.to_string op)^" ("^(pp i e2)^")"
    | If(c,e,e1,e2) -> 
	"(if"^cond_to_string c^" " ^(pp i e) ^ (newline (i+1)) 
	^"then "^ (pp (i+2) e1) ^ (newline (i+1))
	^"else "^ (pp (i+2) e2)^")"
    | Pair(e1,e2) -> "<" ^ (pp i e1) ^ "," ^ (pp i e2) ^ ">"
    | LetPair (x,y,e1,e2) ->
      "(let (<"^(f x)^","^(f y)^"> "^(pp i e1)^") "^(pp i e2)^")"
    | Fst(e) -> "fst "^(pp i e)
    | Snd(e) -> "snd "^(pp i e)
    | App(e1,e2) -> (pp i e1)^" "^(pp i e2)
    | Lam(v,t,e) -> "("^"\\"^(f v)^":"^(pp_tp0 f t)^" =>"
	  ^ (newline(i+1)) ^ (pp (i+1) e)^")"
    | Fix (g,x,t1,t2,e) ->
      "(fix "^(f g)^"("^(f x)^":"^(pp_tp0 f t1)^"):"^(pp_tp0 f t2)^" =>"
	  ^ (newline(i+1)) ^ (pp (i+1) e)^")"
    | Nil -> "nil"
    | Cons (e1,e2) -> (pp i e1) ^"::"^ (pp i e2)
    | Case (e,e1,h,t,e2) ->
	"(case " ^(pp i e) ^ " of " ^ (newline (i+1)) 
	^"  nil -> "^ (pp (i+2) e1) ^ (newline (i+1))
	^"| "^(f h)^"::"^(f t)^" -> "^ (pp (i+2) e2)
    | Let(v1,e1,e2) ->
      "let "^(f v1)^" = "
       ^(newline (i+1)) ^ (pp (i+1) e1) ^ " in"
       ^(newline i) ^ (pp i e2)
    | TLam (tv,e) -> "("^"/\\"^(f tv)^" . "
	  ^ (newline(i+1)) ^ (pp (i+1) e)^")"
    | TApp (e,t) -> "("^(pp i e)^"["^(pp_tp0 f t)^"]"
    | _ -> raise NYI in
  pp 0 e

let pp_exp = pp_exp0 Var.to_string
let pp_aexp = pp_exp0 (fun x -> x)

let lookup ctx v = 
  let (v',t') = List.find (fun (v',t) -> v = v') ctx
  in t'
let extend ctx v v' = (v,v')::ctx

let rec an_tp ctx t = 
  match t with
    Int -> Int
  | Times (t1,t2) -> Times (an_tp ctx t1, an_tp ctx t2)
  | Arrow (t1,t2) -> Arrow(an_tp ctx t1, an_tp ctx t2)
  | List t -> List(an_tp ctx t)
  | Forall (tv,t) -> 
      let tv' = Var.mkvar tv in
      Forall (tv', an_tp (extend ctx tv tv') t)
  | TVar tv -> TVar (lookup ctx tv)

let alpha_convert_tp t = an_tp [] t
  
let alpha_convert e = 
  let rec an tctx ctx e = 
    let h = an tctx ctx in
    match e with
      Var v -> (try Var (lookup ctx v) with Not_found -> print_string (v^" not found\n"); raise Not_found)
    | IntC i -> IntC i
    | Op(op,es) -> Op(op,List.map h es)
    | If(c,e,e1,e2) -> If(c,h e, h e1, h e2)
    | Pair(e1,e2) -> Pair(h e1, h e2)
    | LetPair(x,y,e1,e2) -> 	
	let v1 = Var.mkvar x in
	let v2 = Var.mkvar y in 
	LetPair(v1,v2, h e1, an tctx (extend (extend ctx x v1) y v2) e2)
    | Fst e -> Fst (h e)
    | Snd e -> Snd (h e)
    | Lam (x,t,e) -> 
	let v = Var.mkvar x in
	Lam(v,(an_tp tctx t),
	    an tctx (extend ctx x v) e)
    | Fix (f,x,t1,t2,e) -> 
	let v1 = Var.mkvar f in
	let v2 = Var.mkvar x in
	Fix(v1,v2,
	    (an_tp tctx t1),
	    (an_tp tctx t2),
	    an tctx (extend (extend ctx f v1) x v2) e)
    | App (e1,e2) -> App(h e1, h e2)
    | Nil -> Nil
    | Cons(e1,e2) -> Cons(h e1, h e2)
    | Case(e,e1,v1,v2,e2) -> 
	let w1 = Var.mkvar v1 in
	let w2 = Var.mkvar v2 in
	Case(h e, h e1, w1, w2,
	     an tctx (extend (extend ctx v1 w1) v2 w2) e2)
    | Let (x,e1,e2) -> 
	let v = Var.mkvar x in
	Let(v,h e1,an tctx (extend ctx x v) e2)
    | TLam(tv,e) -> 
	let tv' = Var.mkvar tv in
	TLam(tv', an (extend tctx tv tv') ctx e)
    | TApp(e,t) -> 
	TApp(h e, an_tp tctx t)
  in an [] [] e

module VarSet = Set.Make(struct type t = Var.var let compare = Var.compare end)

let fv e = 
  let (||) = VarSet.union in
  let u = VarSet.union in
  let rec fvs e = 
    match e with
      Var v -> VarSet.singleton v
    | IntC i -> VarSet.empty
    | Op(op,es) -> List.fold_right (u) (List.map fvs es) (VarSet.empty)
    | If(c,e,e1,e2) -> u (fvs e) (u (fvs e1) (fvs e2))
    | Pair(e1,e2) -> u (fvs e1) (fvs e2)
    | LetPair(v,w,e1,e2) -> u (fvs e1) (VarSet.remove v (VarSet.remove w (fvs e2) ))
    | Fst e -> fvs e
    | Snd e -> fvs e
    | Lam (x,t,e) -> VarSet.remove x (fvs e)
    | Let (x,e1,e2) -> (fvs e1) || VarSet.remove x (fvs e2)
    | Fix (f,x,t1,t2,e) -> VarSet.remove f (VarSet.remove x (fvs e))
    | App (e1,e2) -> u (fvs e1) (fvs e2)
    | Nil -> VarSet.empty
    | Cons(e1,e2) -> u (fvs e1) (fvs e2)
    | Case(e,e1,v,w,e2) -> 
	(fvs e) || (fvs e1) || (VarSet.remove v (VarSet.remove w (fvs e2)))
    | TLam(tv,e) -> fvs e 
    | TApp(e,t) -> fvs e
  in VarSet.elements (fvs e)
