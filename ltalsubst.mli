(* Substitution for IL terms.  Assumes no variable clashes.
 Not really capture avoiding but should work for the purpose of optimization
 because if all the variable names are distinct then we only need to rename
 when we unwind a recursive function, and we're not doint htat because we don't
 support recursion yet...
*)
open Ltal;;

type 'a subst
val id : 'a subst
val bind : 'a subst -> tvar -> 'a -> 'a subst
val fetch : 'a subst -> tvar -> 'a option

val subst1w_dtp : tvar -> wtp -> dtp-> dtp 
val subst1w_wtp : tvar -> wtp -> wtp-> wtp 
val subst1w_mtp : tvar -> wtp -> mtp-> mtp 
val subst1w_rctx : tvar -> wtp -> rctx -> rctx
val subst1m_dtp : tvar -> mtp -> dtp-> dtp 
val subst1m_wtp : tvar -> mtp -> wtp-> wtp 
val subst1m_mtp : tvar -> mtp -> mtp-> mtp 
val subst1m_rctx : tvar -> mtp -> rctx -> rctx

val subst_dtp : wtp subst -> mtp subst ->dtp -> dtp 
val subst_wtp : wtp subst -> mtp subst -> wtp -> wtp 
val subst_mtp : wtp subst -> mtp subst -> mtp -> mtp 
val subst_rctx : wtp subst -> mtp subst -> rctx -> rctx

val rename_dtp : dtp -> dtp 
val rename_wtp : wtp -> wtp
val rename_mtp : mtp -> mtp
val rename_rctx : rctx -> rctx
