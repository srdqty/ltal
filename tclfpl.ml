open Lfpl;;
open Ctx;;
open Util;;

type ctx = tp0 Ctx.ctx;;
type sg = tp1 Ctx.ctx;;

type 'a tcM = sg -> ctx -> 'a * ctx
let get_ctxM = fun sg ctx -> ctx,ctx
let set_ctxM ctx = fun sg _ -> (),ctx
let get_sgM = fun sg ctx -> sg,ctx
let retM a = fun sg ctx -> a,ctx
let (>>=) m f = fun sg ctx -> 
  let a,ctx = m sg ctx in
  f a sg ctx
let (>>) m n = m >>= (fun () -> n)
let rec mapM f l = 
  match l with [] -> retM []
  | x::xs -> 
      f x >>= fun y -> 
      mapM f xs >>= fun ys ->
      retM (y::ys)
let rec iter2M f l1 l2 = 
  match l1,l2 with
    [],[] -> retM ()
  | x::xs,y::ys -> 
      f x y >>
      iter2M f xs ys
  | _ -> raise NYI
let runM m = fun sg ctx -> 
  let x,ctx = m sg ctx in
  x
  
  
let linear tp = 
  match tp with 
    Bool -> false
  | Nat -> false
  | _ -> true

let force_bool tp = 
  match tp with Bool -> ()
  | _ -> tcfail "expected bool";;
let force_int tp = 
  match tp with Nat -> ()
  | _ -> tcfail "expected int";;
let force_dmnd tp = 
  match tp with Dmnd -> ()
  | _ -> tcfail "expected diamond";;
let force_list tp = 
  match tp with List(t) -> t
  | _ -> tcfail "expected list";;
let force_tree tp = 
  match tp with Tree(t) -> t
  | _ -> tcfail "expected list";;
let force_pair tp = 
  match tp with Tensor(t1,t2) -> t1,t2
  | _ -> tcfail "expected pair";;
let force_sum tp = 
  match tp with Sum(t1,t2) -> t1,t2
  | _ -> tcfail "expected pair";;

let rec unify t t' = 
  match t,t' with
    Bool,Bool -> ()
  | Nat,Nat -> ()
  | Dmnd, Dmnd -> ()
  | tp,Top -> ()
  | Top,tp -> ()
  | Tensor(t1,t2), Tensor(t1',t2') -> 
      unify t1 t1';
      unify t2 t2'
  | Sum(t1,t2), Sum(t1',t2') -> 
      unify t1 t1';
      unify t2 t2'
  | List(tp), List(tp') -> unify tp tp'
  | Tree(tp), Tree(tp') -> unify tp tp'
  | _ -> tcfail ("types "^Lfpl.pp_tp0 t^" and "^Lfpl.pp_tp0 t'^" are incompatible")

let intersect ctx1 ctx2 = 
  let l1,l2 = dom ctx1, dom ctx2 in
  let l = List.filter (fun x -> List.mem x l1) l2 in
  Ctx.restrict ctx1 l

let rec mergeM f l sg ctx = 
  match l with 
    [] -> Top,ctx
  | [x] -> f x sg ctx
  | x::xs -> 
      let tp1,ctx1 = f x sg ctx in
      let tp2,ctx2 = mergeM f xs sg ctx in
      unify tp1 tp2; 
      tp1,intersect ctx1 ctx2

(* TODO: Check pattern linearity *)

let rec elab_pat p tp = 
  match p with
    IntC i -> retM (force_int tp)
  | Hole v -> (fun sg ctx -> (),extend ctx v tp)
  | True -> retM(force_bool tp)
  | False -> retM(force_bool tp)
  | Pair (p1,p2) -> 
      let t1,t2 = force_pair tp in
      elab_pat p1 t1 >>
      elab_pat p2 t2
  | Inl p -> 
      let t1,t2 = force_sum tp in
      elab_pat p t1
  | Inr p -> 
      let t1,t2 = force_sum tp in
      elab_pat p t2
  | Nil -> let t = force_list tp in retM ()
  | Cons(d,hd,tl) -> 
      let t = force_list tp in
      elab_pat d Dmnd >>
      elab_pat hd t >>
      elab_pat tl tp
  | Leaf (d,e) -> 
      elab_pat d Dmnd >>
      let t = force_tree tp in
      elab_pat e t
  | Node(d,a,l,r) -> 
      let t = force_tree tp in
      elab_pat d Dmnd >>
      elab_pat a t >>
      elab_pat l tp >>
      elab_pat r tp
;;

let rec tc_pat p tp = 
  ti_pat p >>= fun tp' -> 
  retM (unify tp tp')
and ti_pat p = 
    match p with
      IntC i -> retM Nat
    | Hole e -> ti_exp e
    | True -> retM Bool
    | False -> retM Bool
    | Pair (p1,p2) ->
	ti_pat p1 >>= fun t1 -> 
	ti_pat p2 >>= fun t2 -> 
	retM (Tensor(t1,t2))
    | Inl p -> 
	ti_pat p >>= fun t -> 
	retM (Sum(t,Top))
    | Inr p -> 
	ti_pat p >>= fun t -> 
	retM (Sum(Top,t))
    | Nil -> retM (List(Top))
    | Cons(d,h,t) -> 
	tc_pat d Dmnd >>
	ti_pat h >>= fun tp -> 
	tc_pat t (List tp) >>
	retM (List(tp))
    | Leaf(p1,p2) -> 
	tc_pat p1 Dmnd >>
	ti_pat p2 >>= fun tp -> 
	retM (Tree(tp))
    | Node(d,a,l,r) -> 
	tc_pat d Dmnd >>
	ti_pat a >>= fun tp -> 
	tc_pat l (Tree tp) >>
	tc_pat r (Tree tp) >>
	retM (Tree(tp))
and ti_match tp (p,e)  = 
  get_ctxM >>= fun ctx ->
  elab_pat p tp >>
  ti_exp e >>= fun tp ->
  set_ctxM ctx >>
  retM tp
and tc_exp e tp = 
  ti_exp e >>= fun tp' ->
  retM (unify tp tp')
and ti_exp e = 
  match e with
    Var v -> (fun sg ctx -> 
      let tp = try (lookup_or_fail ctx v) with TcFail msg -> tcfail (msg^" (or linear variable is used more than once)") 
      in
      let ctx' = if linear tp then remove ctx v else ctx in
      retM tp sg ctx')
  | P p -> ti_pat p
  | Match (e,ms) ->  
      ti_exp e >>= fun tp' -> 
      mergeM (ti_match tp') ms
  | Op(e1,opr,e2) -> 
      tc_exp e1 Nat >>
      tc_exp e2 Nat >>
      retM Nat
  | App(f,es) ->
      get_sgM >>= fun sg -> 
      let Fn(ts,tp') = lookup_or_fail sg f in
      (iter2M tc_exp es ts >>
       retM tp')
  | NewDmnd -> 
      retM Dmnd
 
let get_fndecl_tp ctx fndecl = 
  let tp = Fn(List.map (fun (tp,nm) -> tp) fndecl.argtys, fndecl.rettp) in
  extend ctx (fndecl.name) tp


let tc_fndecl sg fndecl = 
  let ctx = Ctx.from_list (List.map (fun (x,y) -> y,x) fndecl.argtys) in
  runM (tc_exp fndecl.body fndecl.rettp) sg ctx
;;
  
  
let get_sig (fns,e) = 
  List.fold_left get_fndecl_tp emp fns

let ti_prog (fns,e) = 
  let sg = get_sig (fns,e) in
  List.iter (tc_fndecl sg) fns;
  runM (ti_exp e) sg emp
;;
let tc_prog (fns,e) tp = 
  let sg = get_sig (fns,e) in
  List.iter (tc_fndecl sg) fns;
  runM (tc_exp e tp) sg emp
;;
