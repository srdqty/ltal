open Ltal;;
open Op;;

let stack_max = ref 0;;
let stack_level = ref 0;;

exception TypeError of string
exception Error of string
exception IllegalInstruction

let eval_op rf op = 
  match op with 
    RegOp r -> Ctx.lookup rf r
  | IntOp i -> IntV i
  | CLabOp f -> CLab f

let force_lab v = 
  match v with
    Lab l -> l
  | _ -> raise (TypeError ("expected data label, got "^(pp_value v)))
let force_clab v = 
  match v with
    CLab f -> f
  | _ -> raise (TypeError ("expected code label, got "^(pp_value v)))
let force_int v = 
  match v with
    IntV i -> i
  | _ -> raise (TypeError ("expected integer, got "^(pp_value v)))

let is_cond c v = 
  
  match c, v with
    NZ,IntV v -> v != 0
  | LZ,IntV v -> v < 0
  | _,_ -> true       (* labels are never zero, and don't care whether they are less than zero *)

let rec replace l i v = 
  if (i < 0) then raise (TypeError "negative offsets not allowed")
  else
    match l,i with
      [],_ -> raise (TypeError "offset out of range")
    | _::vs,0 -> v::vs
    | w::vs,n -> w::(replace vs (n-1) v)

let rec push l i = 
  if (i < 0) then raise (TypeError "negative pushes not allowed")
  else
    if i = 0 then l else (IntV (-1))::(push l (i-1))

let rec pop l i = 
  if (i < 0) then raise (TypeError "negative pops not allowed")
  else
    match l,i with
      l,0 -> l
    | _::l,n -> pop l (n-1)
    | [],n -> raise (TypeError "pop out of range")


let eval_instruction inst (cs,hp,rf,blk) = 
  try 
  match inst with
    ADD (r,s,op) -> 
      let i = force_int (Ctx.lookup rf s) in
      let j = force_int (eval_op rf op) in
      let rf' = Ctx.update rf r (IntV (i+j)) in
      (cs,hp,rf',blk)
  | BC (c,r,op) -> 
      if is_cond c (Ctx.lookup rf r) 
      then 
	let f = force_clab (eval_op rf op) in
	let blk' = Ctx.lookup cs f in
	(cs,hp,rf,blk')
      else (cs,hp,rf,blk)
      
  | LD (r,s,i) -> 
      let l = force_lab(Ctx.lookup rf s) in
      let vs = Var.find l hp in
      (cs,hp,Ctx.update rf r (List.nth vs i), blk)
  | MOV (r,op) ->
      let v = eval_op rf op in
      (cs,hp,Ctx.update rf r v,blk)
  | ST (r,i,s) -> 
      let l = force_lab(Ctx.lookup rf r) in
      let v = Ctx.lookup rf s in
      let vs = Var.find l hp in
      let vs' = replace vs i v in
      (cs,Var.add l vs' hp, rf, blk)
  | SUB (r,s,op) -> 
      let i = force_int (Ctx.lookup rf s) in
      let j = force_int (eval_op rf op) in
      let rf' = Ctx.update rf r (IntV (i-j)) in
      (cs,hp,rf',blk)
  | MUL (r,s,op) -> 
      let i = force_int (Ctx.lookup rf s) in
      let j = force_int (eval_op rf op) in
      let rf' = Ctx.update rf r (IntV (i*j)) in
      (cs,hp,rf',blk)
  | POP (r,s,i) -> 
     stack_level := !stack_level - i;
     let l = force_lab(Ctx.lookup rf r) in
     let vs = Var.find l hp in
     let vs' = pop vs i in
     (cs,Var.add l vs' hp, rf, blk)
  | PUSH (r,s,i) -> 
     stack_level := !stack_level + i;
     stack_max := max(!stack_max) (!stack_level);
     let l = force_lab(Ctx.lookup rf r) in
     let vs = Var.find l hp in
     let vs' = push vs i in
     (cs,Var.add l vs' hp, rf, blk)
  | COMMENT msg -> (cs,hp,rf,blk)
  with TypeError msg -> raise (Error("Type error at instruction "^(pp_instruction inst)^": "^msg))

let step (cs,hp,rf,blk) = 
   
  match blk with
    [],HALT -> None
  | [],JMP op -> 
      (try let f = force_clab(eval_op rf op) in
      let blk' = Ctx.lookup cs f in
      Some (cs,hp,rf,blk')
      with TypeError msg -> raise (Error("Type error at instruction "^(pp_block ([],JMP op))^": "^msg)))
  | [],FAIL msg -> raise (Error msg)
  | (inst::insts,ei) -> Some (eval_instruction inst (cs,hp,rf,(insts,ei)))
  

let rec initheap i = 
  if i == 0 then (Var.empty,IntV 0)
  else 
    let (hp,l) = initheap (i-1) in
    let l' = Var.mkvar "l" in
    (Var.add l' [IntV 0; l] hp, Lab l')

let eval (cs,hp,rf) f = 
  let blk = Ctx.lookup cs f in
    let rec steps (hp,rf,blk) = 
      match step (cs,hp,rf,blk) with
	None -> (hp,rf)
      | Some (cs,hp,rf,blk') -> steps (hp,rf,blk')
    in
    steps (hp,rf,blk)

let profile (cs,hp,rf) f = 
  let count = ref 0 in
  let blk = Ctx.lookup cs f in
  let rec steps (hp,rf,blk) = 
    match step (cs,hp,rf,blk) with
      None -> (hp,rf)
    | Some (cs,hp,rf,blk') -> 
	count := (!count)+1;
	steps (hp,rf,blk')
  in
  let (hp,rf) = steps (hp,rf,blk) in
  (hp,rf,!count)
    
  


let rec print_value_wtp hp v tp = 
  match tp with 
    DTp dtp -> print_value_dtp hp v dtp
  | Ref(mtp) -> 
      (match v with 
	Lab l -> 
	  "["^(print_value_mtp hp (Var.find l hp) mtp)^"]"
      | _ -> raise Util.NYI)
  | NRef(mtp) -> 
      (match v with 
	IntV 0 -> "NULL"
      | _ -> print_value_wtp hp v (Ref mtp))
  | Mu(tv,wtp) -> 
      print_value_wtp hp v (Ltalsubst.subst1w_wtp tv (Mu(tv,wtp)) wtp)
  | _ -> "<abstr>"
 
and print_value_dtp hp v dtp = 
  match dtp with 
    Word -> Ltal.pp_value v
  | Zero -> Ltal.pp_value v
  | _ -> "<fn>"

and print_value_mtp hp v mtp = 
  match mtp with 
    One -> ""
  | Tensor(t,One) -> 
      (match v with 
	v::vs -> (print_value_wtp hp v t)
      | _ -> raise Util.NYI)
  | Tensor(t,m) -> 
      (match v with 
	v::vs -> (print_value_wtp hp v t)^", "^(print_value_mtp hp vs m)
      | _ -> raise Util.NYI)
  | _ -> "<abstr>"
  
