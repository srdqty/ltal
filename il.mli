open Op;;
type var = Ctx.var

type tp = Int 
  | Top
  | TVar of var
  | Arrow of  tp *  tp
  | Tensor of  tp *  tp
  | Exists of var *  tp
  | Forall of var *  tp
  | List of tp 


type  exp = Var of var
  | IntC of int
  | Op of op * exp * exp
  | If of  cond * exp *  exp *  exp
  | Pair of  exp *  exp
  | LetPair of var * var *  exp *  exp
  | Fn of var * ( tp) *  exp
  | App of  exp *  exp
  | Pack of ( tp) * ( exp) * ( tp)
  | LetUnpack of var * var *  exp *  exp
  | TLam of var * exp
  | TApp of exp * tp
  | Let of var *  exp *  exp
  | Fix of var * var * tp * tp * exp
  | Nil
  | Cons of exp * exp
  | Case of exp * exp * var * var * exp
  | Copy of cfctx * Absyn.tp * exp
  | Free of cfctx * Absyn.tp * exp
and cfctx = (exp * exp) Ctx.ctx

val pp_tp : tp -> string
val pp_exp : exp -> string
val pp_exp' : exp -> string

type ctx = tp Ctx.ctx
type tctx = unit Ctx.ctx

val top : exp
