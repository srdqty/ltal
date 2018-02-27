(* LFPL absyn *)
(* Plan: Translate to LIL *)

open Var;;
open Op;;
open Util;;

type tp0 = 
    Bool
  | Nat 
  | Dmnd
  | Top
  | List of tp0
  | Tree of tp0
  | Tensor of tp0 * tp0
  | Sum of tp0 * tp0

type tp1 = 
  | Fn of tp0 list * tp0

type 'a pat = 
  | Hole of 'a
  | IntC of int
  | True
  | False
  | Pair of 'a pat * 'a pat
  | Inl of 'a pat
  | Inr of 'a pat
  | Nil
  | Cons of 'a pat * 'a pat * 'a pat
  | Leaf of 'a pat * 'a pat
  | Node of 'a pat * 'a pat * 'a pat * 'a pat
  
type exp = 
    Var of var
  | App of var * exp list
  | Op of exp * Op.op * exp
  | Match of exp * (var pat*exp) list 
  | NewDmnd
  | P of exp pat

type fndecl = {rettp : tp0; 
	       name : var;
	       argtys : (tp0 * var) list;
	       body : exp}

type prog = fndecl list * exp


let rec pp_tp0 t = 
  match t with
    Bool -> "B"
  | Nat -> "N"
  | Dmnd -> "<>"
  | Top -> "T"
  | List(tp0) -> "L("^pp_tp0 tp0^")"
  | Tree(tp0) -> "T("^pp_tp0 tp0^")"
  | Tensor(t1,t2) -> "(" ^pp_tp0 t1^ " (X) " ^pp_tp0 t2^ ")"
  | Sum(t1,t2) -> "(" ^pp_tp0 t1^ " (+) " ^pp_tp0 t2^ ")"

let pp_tp1 t = 
  match t with
  | Fn (tps,tp) -> "("^sep pp_tp0 "*" tps^") -> "^(pp_tp0 tp)

let rec ppp f p = 
  match p with
    Hole x -> f x
  | IntC i -> string_of_int i
  | True -> "true"
  | False -> "false"
  | Pair (p1,p2) -> "<"^ppp f p1^","^ppp f p2^">"
  | Inl(p) -> "inl("^ppp f p^")"
  | Inr(p) -> "inr("^ppp f p^")"
  | Nil -> "nil"
  | Cons(p1,p2,p3) -> "cons("^ppp f p1^","^ppp f p2^","^ppp f p3^")"
  | Leaf(p1,p2) -> "leaf("^ppp f p1^","^ppp f p2^")"
  | Node(p1,p2,p3,p4) -> "node("^ppp f p1^","^ppp f p2^","^ppp f p3^","^ppp f p4^")" ;;

let pp_pat = ppp;;

let rec ppe e = 
  match e with 
    Var v -> Var.to_string v
  | App (f,es) -> Var.to_string f ^"("^sep ppe "," es^")"
  | Op (e1,op,e2) -> "("^ppe e1 ^" "^Op.to_string op ^" "^ ppe e2^")"
  | Match (e,matchs) -> "match "^ppe e^" with {"^sep ppm " | " matchs^"}"
  | NewDmnd -> "new"
  | P(pat) -> ppp ppe pat
and ppm ((pat: var pat),exp) =
  (ppp Var.to_string pat) ^" => "^ppe exp;;

let pp_exp = ppe;;

let pp_decl decl = 
  let pp_argty (tp,nm) = pp_tp0 tp ^" "^ Var.to_string nm in
  "def "^pp_tp0 decl.rettp^" "
  ^Var.to_string decl.name
  ^"("^sep pp_argty "," decl.argtys ^") =\n\t"^pp_exp decl.body

let pp_prog (decls, exp) = 
  sep pp_decl "\n\n" decls ^"\n\n"^ pp_exp exp


let rec map_pat f p = 
  let h = map_pat f in
  match p with
    Hole v -> Hole(f v)
  | IntC i -> IntC i
  | True -> True
  | False -> False
  | Pair(p1,p2) -> Pair(h p, h p2)
  | Inl p -> Inl (h p)
  | Inr p -> Inr (h p)
  | Nil -> Nil
  | Cons(d,p1,p2) -> Cons(h d, h p1, h p2)
  | Leaf(d,p) -> Leaf(h d,h p)
  | Node(d,a,l,r) -> Node(h d, h a, h l, h r)
