(* Codegen: Generate assembly code from linear IL *)
open Ltal;;
val typetrans : Il.tctx -> Il.tp -> Ltal.wtp

(* translate closed expression in lifted form to LTAL *)
val codegen : Il.exp -> Il.tp -> 
  Ltal.code_section * Ltal.cctx * Ltal.clab

type code_env = {cctx : cctx;
		 cs : code_section;
		 fctx : Il.ctx;
		 lctx : Var.var Ctx.ctx;
		 fp : int}

type block_env = {cenv : code_env;
		  ilist : instruction list;
		  lab : clab;
		  tctx : Ltal.tctx;
		  rctx : Ltal.rctx}
exception BlockFail of string * block_env
exception CodeFail of string * code_env


val rs : reg
val rt : reg
val rr : reg
val rf : reg
val ra : reg

