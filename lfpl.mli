(* LFPL absyn *)
(* Plan: Translate to LIL *)

open Var;;
open Op;;

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
  | Var of var
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

  
val pp_tp0 : tp0 -> string
val pp_tp1 : tp1 -> string

val pp_pat : ('a -> string) -> 'a pat -> string
val pp_exp : exp -> string
val pp_prog : prog -> string

val map_pat : ('a -> 'b) -> 'a pat -> 'b pat

