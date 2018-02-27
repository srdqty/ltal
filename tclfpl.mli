open Lfpl;;

type sg = tp1 Ctx.ctx
type ctx = tp0 Ctx.ctx
type 'a tcM = sg -> ctx -> 'a * ctx
val (>>) : unit tcM -> 'a tcM -> 'a tcM
val (>>=) : 'a tcM -> ('a -> 'b tcM) -> 'b tcM
val retM : 'a -> 'a tcM
val mapM : ('a -> 'b tcM) -> 'a list -> ('b list) tcM
val get_sgM : sg tcM
val set_ctxM : ctx -> unit tcM
val get_ctxM : ctx tcM

val ti_exp : exp -> tp0 tcM 
val tc_exp : exp -> tp0 -> unit tcM
val tc_prog : prog -> tp0 -> unit
val ti_prog : prog -> tp0
val get_sig : prog -> sg

val force_int : tp0 -> unit
val force_bool : tp0 -> unit
val force_dmnd : tp0 -> unit
val force_pair : tp0 -> tp0 * tp0
val force_sum : tp0 -> tp0 * tp0
val force_list : tp0 -> tp0
val force_tree : tp0 -> tp0
