open Util;;
open Op;;
type var = Var.var;;

type  tp = Int 
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

let rec pp_tp t = 
  match t with 
    Int -> "int"
  | Top -> "unit"
  | Arrow(t1,t2) -> "(" ^ (pp_tp t1) ^ " => " ^ (pp_tp t2) ^ ")"
  | Tensor(t1,t2) -> "(" ^(pp_tp t1) ^ " * " ^ (pp_tp t2)^ ")"
  | Exists(v,t) -> "exists "^ (Var.to_string v) ^ ". ("^ (pp_tp t) ^ ")"
  | Forall(v,t) -> "forall "^ (Var.to_string v) ^ ". ("^ (pp_tp t) ^ ")"
  | TVar v -> Var.to_string v
  | List t -> "("^(pp_tp t) ^") list"

let pp_exp e = 
  let rec pp i e = 
    match e with
      Var v -> Var.to_string v
    | IntC i -> string_of_int i
    | Op(op,e1,e2) -> (pp i e1) ^" "^(Op.to_string op)^" "^(pp i e2)
    | If(c,e,e1,e2) -> 
	(newline (i)) ^ "(if"^cond_to_string c^" " ^(pp i e) ^ (newline (i+1)) 
	^" then "^ (pp (i+1) e1) ^ (newline (i+1))
	^" else "^ (pp (i+1) e2) ^")"
    | Pair(e1,e2) -> "<" ^ (pp i e1) ^ "," ^ (pp i e2) ^ ">"
    | LetPair(v1,v2,e1,e2) ->
      "let <"^(Var.to_string v1)^","^(Var.to_string v2)^"> = "
       ^(newline (i+1)) ^ (pp (i+1) e1) ^ " in"
       ^(newline i) ^ (pp i e2)
    | App(e1,e2) -> (pp i e1)^" "^(pp i e2)
    | Fn(v,t,e) -> "("^"fn "^(Var.to_string v)^" : "^ (pp_tp t)  ^ " =>"
	  ^ (newline(i+1)) ^ (pp (i+1) e)^")"
    | Fix(f,x,t1,t2,e) -> "("^"fix "^(Var.to_string f)^"("^(Var.to_string x)^" : "^(pp_tp t1)^"):"^(pp_tp t2)^" =>"
	^ (newline(i+1)) ^ (pp (i+1) e)^")"
    | Pack(t,e,t') -> "pack [" ^ (pp_tp t)  ^ "," ^ (pp i e) ^ "] as " ^ (pp_tp t')
    | LetUnpack(v1,v2,e1,e2) ->
      "let ["^(Var.to_string v1)^","^(Var.to_string v2)^"] = "
       ^(newline (i+1)) ^ (pp (i+1) e1) ^ " in"
       ^(newline i) ^ (pp i e2)
    | TApp (e,t) -> (pp i e)^"["^(pp_tp t)^"]"
    | TLam (tv,e) -> "(/\\"^(Var.to_string tv)^"."^(pp i e)^")"
    | Let(v1,e1,e2) ->
      "let "^(Var.to_string v1)^" = "
       ^(newline (i+1)) ^ (pp (i+1) e1) ^ " in"
       ^(newline i) ^ (pp i e2)
    | Nil -> "nil"
    | Cons (e1,e2) -> (pp i e1) ^"::"^ (pp i e2)
    | Case (e,e1,h,t,e2) ->
	"(case " ^(pp i e) ^ " of " ^ (newline (i+1)) 
	^"  nil -> "^ (pp (i+2) e1) ^ (newline (i+1))
	^"| "^(Var.to_string h)^"::"^(Var.to_string t)^" -> "^ (pp (i+2) e2)
    | Copy(_,tp,e) -> 
	"(copy["^(Absyn.pp_tp tp)^"] "^(pp i e)^")"
    | Free(_,tp,e) -> 
	"(free["^(Absyn.pp_tp tp)^"] "^(pp i e)^")"
  in pp 0 e

let pp_exp' e = 
  let rec newline i = 
     if i = 0 then "\n"
	 else (newline (i-1))^" "
  in
  let pptp t = "_" in
  let rec pp i e = 
    match e with
      Var v -> Var.to_string v
    | IntC i -> string_of_int i
    | Op(op,e1,e2) -> "("^(pp i e1) ^") "^(Op.to_string op)^" ("^(pp i e2)^")"
    | If(c,e,e1,e2) -> 
	(newline (i)) ^ "(if"^cond_to_string c^" " ^(pp i e) ^ (newline (i+1)) 
	^"then "^ (pp (i+2) e1) ^ (newline (i+1))
	^"else "^ (pp (i+2) e2) ^")"
    | Pair(e1,e2) -> "<" ^ (pp i e1) ^ "," ^ (pp i e2) ^ ">"
    | LetPair(v1,v2,e1,e2) ->
      "let <"^(Var.to_string v1)^","^(Var.to_string v2)^"> = "
       ^ (pp (i+1) e1) ^ " in"
       ^(newline i) ^ (pp i e2)
    | App(e1,e2) -> (pp i e1)^" "^(pp i e2)
    | Fn(v,t,e) -> "("^"fn "^(Var.to_string v)^" : "^(pp_tp t)^" =>"
	  ^ (newline(i+1)) ^ (pp (i+1) e)^")"
    | Fix(f,x,t1,t2,e) -> "("^"fix "^(Var.to_string f)^"("^(Var.to_string x)^") =>"
	  ^ (newline(i+1)) ^ (pp (i+1) e)^")"
    | Pack(t,e,t') -> "pack [" ^ (pptp t)  ^ "," ^ (pp i e) ^ "]"
    | LetUnpack(v1,v2,e1,e2) ->
      "let ["^(Var.to_string v1)^","^(Var.to_string v2)^"] = "
       ^ (pp (i+1) e1) ^ " in"
       ^(newline i) ^ (pp i e2)
    | TApp (e,t) -> (pp i e)^"["^(pp_tp t)^"]"
    | TLam (tv,e) -> "(/\\"^(Var.to_string tv)^"."^(pp i e)^")"
    | Let(v1,e1,e2) ->
      "let "^(Var.to_string v1)^" = "
       ^ (pp (i+1) e1) ^ " in"
       ^(newline i) ^ (pp i e2)
    | Nil -> "nil"
    | Cons (e1,e2) -> (pp i e1) ^"::"^ (pp i e2)
    | Case (e,e1,h,t,e2) ->
	"(case " ^(pp i e) ^ " of " ^ (newline (i+1)) 
	^"  nil -> "^ (pp (i+2) e1) ^ (newline (i+1))
	^"| "^(Var.to_string h)^"::"^(Var.to_string t)^" -> "^ (pp (i+2) e2)
    | Copy(_,tp,e) -> 
	"(copy["^(Absyn.pp_tp tp)^"] "^(pp i e)^")"
    | Free(_,tp,e) -> 
	"(free["^(Absyn.pp_tp tp)^"] "^(pp i e)^")"
  in pp 0 e


type tctx = unit Ctx.ctx
type ctx = tp Ctx.ctx

let top = IntC (-1)
