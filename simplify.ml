open Var;;
open Lfpl;;

type tag = Hole_t of var
  | IntC_t of int
  | True_t
  | False_t
  | Pair_t
  | Inl_t
  | Inr_t
  | Nil_t
  | Cons_t
  | Leaf_t
  | Node_t

let tagify (p,e) = 
  match p with
    Hole v -> Hole_t v, [], e
  | IntC i -> IntC_t i, [], e
  | True -> True_t, [], e
  | False -> False_t, [], e
  | Pair(p1,p2) -> Pair_t, [p1;p2], e
  | Inl p -> Inl_t, [p], e
  | Inr p -> Inr_t, [p], e
  | Nil -> Nil_t, [], e
  | Cons(d,h,t) -> Cons_t, [d;h;t], e
  | Leaf(d,a) -> Leaf_t,[d;a],e
  | Node(d,a,l,r) -> Node_t,[d;a;l;r],e

let simplify e = 
  let rec sim_e e = 
    match e with 
      Var v -> Var v
    | App (f,es) -> App(f, List.map sim_e es)
    | Op (e1,op,e2) -> Op(sim_e e1,op,sim_e e2) 
    | Match(e,ms) -> 
	let e' = sim_e e in
	Match(e', sim_ms ms)
    | NewDmnd -> NewDmnd
    | P p -> P(map_pat sim_e p)
  and sim_ms ms = ms 
  in sim_e e
