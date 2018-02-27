
open Op;;

type 'v tp0 = Int
  | Times of 'v tp0 * 'v tp0
  | Arrow of 'v tp0 * 'v tp0
  | List of 'v tp0
  | Forall of 'v * 'v tp0
  | TVar of 'v

type 'v exp0 = Var of 'v
(* Integers *)
  | IntC of int
  | Op of Op.op * ('v exp0) list
  | If of cond * 'v exp0 * 'v exp0 * 'v exp0
(* Pairs *)
  | Pair of 'v exp0 * 'v exp0
  | LetPair of 'v * 'v * 'v exp0 * 'v exp0
  | Fst of 'v exp0
  | Snd of 'v exp0
(* Functions *)
  | Lam of 'v * 'v tp0 * 'v exp0
  | Fix of 'v * 'v * 'v tp0 * 'v tp0 * 'v exp0
  | App of 'v exp0 * 'v exp0
(* Lists *)
  | Nil
  | Cons of 'v exp0 * 'v exp0
  | Case of 'v exp0 * 'v exp0 * 'v * 'v * 'v exp0
(* Let *)
  | Let of 'v * 'v exp0 * 'v exp0 
(* Forall *)
  | TLam of 'v * 'v exp0
  | TApp of 'v exp0 * 'v tp0

(* pre-uniquifying *)
type aexp = string exp0;;
type atp = string tp0;;
(* post-uniquifying *)
type exp = Var.var exp0
type tp = Var.var tp0

val pp_tp0 : ('v -> string) -> 'v tp0 -> string
val pp_atp :  atp -> string
val pp_tp :  tp -> string
val pp_exp0 : ('v -> string) -> 'v exp0 -> string
val pp_aexp : aexp -> string
val pp_exp : exp -> string

val alpha_convert : aexp -> exp
val alpha_convert_tp : atp -> tp

val fv : exp -> Var.var list
