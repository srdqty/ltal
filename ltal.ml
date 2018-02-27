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
  | Mu of tvar * wtp

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

let short_code = ref false;;

let pp_reg = Var.to_string
let pp_lab = Var.to_string
let pp_clab = Var.to_string

let pp_kind k = 
  match k with 
    W -> "W"
  | M -> "M"


let rec pp_dtp' i dtp = 
  match dtp with 
    Word -> "word"
  | Code rctx -> 
      if !short_code then "code"
      else "code "^(pp_rctx' (i+4) rctx)
  | Forall (tv,k, t) -> "forall "^(Var.to_string tv)^":"^(pp_kind k)^" . "^(pp_dtp' i t)
  | Zero -> "zero"
  | Top -> "top"

and pp_wtp' i  wtp = 
  match wtp with
    DTp dtp-> pp_dtp' i  dtp
  | TVar tv -> Var.to_string tv
  | NRef mtp -> "*["^(pp_mtp' i  mtp)^"]"
  | Ref mtp ->  "@["^(pp_mtp' i  mtp)^"]"
  | Stack mtp ->  "S["^(pp_mtp' i  mtp)^"]"
  | Exists (tv, k, wtp) -> "exists "^(Var.to_string tv)^":"^(pp_kind k)^" . "^(pp_wtp' i  wtp)
  | Mu (tv, wtp) -> "Mu "^(Var.to_string tv)^" . "^(pp_wtp' i  wtp)

and pp_mtp' i  mtp = 
  match mtp with
    One -> "one"
  | Tensor(w,One) -> pp_wtp' i w
  | Tensor(w,m) -> pp_wtp' i w ^" * "^ pp_mtp' i (m)
  | MTVar tv -> Var.to_string tv

and pp_rctx' i  rctx = 
  Ctx.pp_ctx (pp_wtp' i) rctx

let pp_wtp wtp = pp_wtp' 0 wtp
let pp_dtp dtp = pp_dtp' 0 dtp
let pp_mtp mtp = pp_mtp' 0 mtp
let pp_rctx ctx = pp_rctx' 0 ctx


let pp_operand op = 
  match op with
    RegOp r -> pp_reg r
  | IntOp i -> string_of_int i
  | CLabOp f -> pp_clab f

let rec pp_value v = 
  match v with
  | IntV i -> string_of_int i
  | CLab f -> pp_clab f
  | Lab f -> pp_lab f

let pp_heap_value hv = 
  let rec pp hv = 
    match hv with
      [] -> ""
    | [v] -> pp_value v
    | v::vs -> (pp_value v)^","^(pp vs)
  in "(" ^ pp hv ^ ")"


let pp_instruction inst = 
  match inst with
    ADD(r,s,op) -> 
      "add " ^ (pp_reg r) ^","
      ^ (pp_reg s) ^","
      ^ (pp_operand op)
  | BC(c,r,op) -> 
      "b"^cond_to_string c^" " 
      ^ (pp_reg r) ^","
      ^ (pp_operand op)
  | LD(r,s,i) -> 
      "ld " ^ (pp_reg r) ^","
      ^ (pp_reg s) ^"["
      ^ (string_of_int i) ^ "]"

  | MOV(r,op) -> 
      "mov " ^ (pp_reg r) ^","
      ^ (pp_operand op)
  | MUL(r,s,op) -> 
      "mul " ^ (pp_reg r) ^","
      ^ (pp_reg s) ^","
      ^ (pp_operand op)
  | ST(r,i,s) -> 
      "st " ^ (pp_reg r) ^"["
      ^ (string_of_int i) ^ "],"
      ^ (pp_reg s)
  | SUB(r,s,op) -> 
      "sub " ^ (pp_reg r) ^","
      ^ (pp_reg s) ^","
      ^ (pp_operand op)
  | COMMENT(msg) ->
     "/* "^msg^" */"
  | PUSH(r,s,i) -> 
      "push " ^ (pp_reg r) ^","
      ^ (pp_reg s) ^" "
      ^ (string_of_int i)
  | POP(r,s,i) -> 
      "pop " ^ (pp_reg r) ^","
      ^ (pp_reg s) ^","
      ^ (string_of_int i)

let rec pp_block blk = 
  match blk with
    (inst::insts,ei) -> 
      (pp_instruction inst) ^ ";\n" 
      ^ (pp_block (insts,ei))
  | [],JMP op -> "jmp "^ (pp_operand op)
  | [],HALT -> "halt"
  | [],FAIL msg -> "fail \""^msg^"\""


let rec pp_code cctx cs = 
  Ctx.fold (fun l blk rest -> 
    (Var.to_string l) ^": "^(pp_dtp (Ctx.lookup cctx l))^"\n"
    ^ (pp_block blk)^"\n" ^ rest)
    cs ""

let rec pp_code_section cs = 
  Ctx.fold (fun l blk rest -> 
     (Var.to_string l) ^":\n"
      ^ (pp_block blk)^"\n"^ rest)
    cs ""
  

let pp_register_file rf = 
  Ctx.pp_ctx pp_value rf


let wordtp = DTp Word;;
let toptp = DTp Top;;
let list_tv = Var.mkvar "l";;
let listtp = Mu(list_tv,NRef(Tensor(toptp,Tensor(TVar list_tv,One))));;

