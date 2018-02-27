#use "make.ml";;

open Ctx;;
open Ltal;;


let r0 = Var.mkvar "r0";;
let r1 = Var.mkvar "r1";;
let r2 = Var.mkvar "r2";;
let r3 = Var.mkvar "r3";;
let r4 = Var.mkvar "r4";;
let r5 = Var.mkvar "r5";;
let l0 = Var.mkvar "l";;
let l1 = Var.mkvar "l";;
let l2 = Var.mkvar "l";;
let l3 = Var.mkvar "l";;
let a0 = Var.mkvar "a";;
let a1 = Var.mkvar "a";;

let i (inst,(insts,ei)) = (inst::insts,ei)
let ei i = ([],i) 

let cs = Ctx.emp;;
(* l0 *)
let i1 = MOV(r1,IntOp 1);;
let b0 = i(i1,ei(JMP (CLabOp l1)));;
let cs = Ctx.extend cs l0 b0;;
(* l1 *)
let i3 = MUL(r1,r1,IntOp 2);;
let i4 = SUB(r0,r0,IntOp 1);;
let i5 = BC(NZ,r0,CLabOp l1);;
let b1 = i(i3,i(i4,i(i5,ei(JMP(RegOp r3)))));;
let cs = Ctx.extend cs l1 b1;;
(* l2 *)
let i6 = MOV(r0,IntOp 10);;
let i7 = MOV(r3,CLabOp l3);;
let b2 = i(i6,i(i7,ei(JMP(CLabOp l0))));;
let cs = Ctx.extend cs l2 b2;;
(* l3 *)
let b3 = ei HALT;;
let cs = Ctx.extend cs l3 b3;;

let rf = Ctx.emp;;
let rf = Ctx.extend rf r0 (IntV 0);;
let rf = Ctx.extend rf r1 (IntV 0);;
let (hp,hl) = Eval.initheap 200;;
let rf = Ctx.extend rf r2 hl;;
let rf = Ctx.extend rf r3 (IntV 0);;
let rf = Ctx.extend rf r4 (IntV 0);;
let rf = Ctx.extend rf r5 (IntV 0);;

let tv = Var.mkvar "a";;
let wordtp = DTp(Word);;
let listtp = Mu(tv, NRef(Tensor(wordtp, Tensor(TVar tv,One))));;

let rt = Ctx.emp;;
let rt = Ctx.extend rt r0 wordtp;;
let rt = Ctx.extend rt r1 wordtp;;
let rt = Ctx.extend rt r2 listtp;;
let rt'' = Ctx.extend rt r3 wordtp;;
let rt'' = Ctx.extend rt'' r4 (TVar a0);;
let rt'' = Ctx.extend rt'' r5 (TVar a0);;
let rettp = DTp(Code rt'');;
let rt' = Ctx.extend rt r3 rettp;;
let rt' = Ctx.extend rt' r4 (TVar a0);;
let rt' = Ctx.extend rt' r5 (TVar a0);;
let rt''' = Ctx.extend rt r3 wordtp;;
let rt''' = Ctx.extend rt''' r4 (NRef(Tensor(wordtp, Tensor(wordtp,One))));;
let rt''' = Ctx.extend rt''' r5 (NRef(Tensor(wordtp, Tensor(wordtp,One))));;

let cctx = Ctx.emp;;
let cctx = Ctx.extend cctx l0 (Forall (a0,W,Code rt'));;
let cctx = Ctx.extend cctx l1 (Forall (a0,W,Code (rt')));;
let cctx = Ctx.extend cctx l2 (Code rt''');;
let cctx = Ctx.extend cctx l3 (Code rt''');;

let cctc = Tcltal.wf_cctx cctx;;

let cstc = Tcltal.tc_code_section cs cctx;;

let rftc = Tcltal.tc_register_file cctx hp rf rt''';;


