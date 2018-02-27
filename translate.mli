
type var = Var.var

val tp2il : Absyn.tp -> Il.tp

val exp2il :  Tcabsyn.tctx -> Tcabsyn.ctx -> Il.cfctx -> Absyn.exp -> Absyn.tp -> Il.exp -> Il.exp

val exp2ilcf :  Tcabsyn.tctx -> Tcabsyn.ctx -> Il.cfctx -> Absyn.exp -> Absyn.tp -> Il.exp -> Il.exp

val ilcf2il :  Il.exp -> Il.exp
