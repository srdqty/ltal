open Il;;

val tc_closed : Il.exp -> Il.tp -> unit
val ti_closed : Il.exp -> Il.tp
val tc : tctx -> ctx -> Il.exp -> Il.tp -> ctx
val ti : tctx -> ctx -> Il.exp -> Il.tp * ctx
val twf : tctx  -> Il.tp -> unit

val force_int : Il.tp -> unit
val force_tensor : Il.tp -> Il.tp * Il.tp
val force_arrow : Il.tp -> Il.tp * Il.tp
val force_exists : Il.tp -> Il.var * Il.tp
val force_list : Il.tp -> Il.tp
