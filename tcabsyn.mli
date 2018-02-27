
type var = Ctx.var
type ctx = Absyn.tp Ctx.ctx
type tctx = unit Ctx.ctx
val tc : tctx -> ctx -> Absyn.exp -> Absyn.tp -> unit
val ti : tctx -> ctx -> Absyn.exp -> Absyn.tp

val force_int : Absyn.tp -> unit
val force_times : Absyn.tp -> Absyn.tp * Absyn.tp
val force_arrow : Absyn.tp -> Absyn.tp * Absyn.tp
val force_list : Absyn.tp -> Absyn.tp
val force_forall : Absyn.tp -> var * Absyn.tp
