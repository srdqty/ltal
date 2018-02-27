(* Substitution for IL terms.  Assumes no variable clashes.
 Not really capture avoiding but should work for the purpose of optimization
 because if all the variable names are distinct then we only need to rename
 when we unwind a recursive function, and we're not doint htat because we don't
 support recursion yet...
*)

type var = Il.var;;

type 'a subst
val id : 'a subst

val bind : 'a subst -> var -> 'a -> 'a subst
val fetch : 'a subst -> var -> 'a option

val subst1_tp : Il.var -> Il.tp -> Il.tp -> Il.tp
val subst1_exp : Il.var -> Il.exp -> Il.exp -> Il.exp
val subst_tp : Il.tp subst -> Il.tp -> Il.tp
val subst_exp : Il.tp subst -> Il.exp subst -> Il.exp -> Il.exp

(* renames all the bound exp variables in a exp *)
val rename : Il.exp -> Il.exp
