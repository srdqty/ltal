(* LTAL target language *)
open Op;;

type tvar = Var.var
type reg = Var.var
type lab = Var.var
type clab = Var.var

type sign = Pos | Neg | QForall | QExists
type kind = W | M

type dtp = 
    Forall of tvar * kind * dtp 
  | Word
  | Zero
  | Top
  | Code of rctx

and wtp = 
    DTp of dtp
  | TVar of tvar
  | NRef of mtp
  | Ref of mtp
  | Stack of mtp
  | Exists of tvar * kind * wtp
  | Mu of tvar * wtp (* kind always word *)

and mtp = One 
  | Tensor of wtp * mtp
  | MTVar of tvar

and tctx = (sign*kind) Ctx.ctx
and cctx = dtp Ctx.ctx
and rctx = wtp Ctx.ctx

type operand = 
    RegOp of reg
  | IntOp of int
  | CLabOp of clab

type value = 
    IntV of int
  | Lab of lab
  | CLab of clab

type heap_value = value list


type code_section = block Ctx.ctx

and heap = heap_value Var.map

and register_file = value Ctx.ctx

and instruction = 
    ADD of reg * reg * operand
  | BC of cond * reg * operand
  | LD of reg * reg * int
  | MOV of reg * operand
  | MUL of reg * reg * operand
  | ST of reg * int * reg
  | SUB of reg * reg * operand
  | COMMENT of string
  | PUSH of reg * reg * int
  | POP of reg * reg * int

and end_instruction =  
    JMP of operand
  | HALT
  | FAIL of string

and block = instruction list * end_instruction

type program_state = (code_section * heap * register_file * block)

val pp_kind : kind -> string
val pp_dtp : dtp -> string
val pp_wtp : wtp -> string
val pp_mtp : mtp -> string
val pp_rctx : rctx -> string

val pp_value : value -> string
val pp_operand : operand -> string
val pp_heap_value : heap_value -> string

val pp_instruction : instruction -> string
val pp_block : block -> string
val pp_code : cctx -> code_section -> string
val pp_code_section : code_section -> string
val pp_register_file :  register_file -> string


val wordtp : wtp
val toptp : wtp
val listtp : wtp

val short_code : bool ref
