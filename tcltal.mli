open Ltal;;

val wf_dtp : tctx -> dtp -> unit
val wf_wtp : tctx -> wtp -> unit
val wf_mtp : tctx -> mtp -> unit

val wf_cctx : cctx -> unit

val tc_code_section : code_section -> cctx -> unit

val wf_rctx : tctx -> rctx -> unit

val tc_value : cctx -> heap -> value -> wtp -> heap
val tc_heap_value : cctx -> heap -> heap_value -> mtp -> heap
val tc_register_file : cctx -> heap -> register_file -> rctx -> unit

val ti_operand_dtp : cctx -> tctx -> rctx -> operand -> (tctx*dtp)
val ti_operand : cctx -> tctx -> rctx -> operand -> (wtp*rctx)
val tc_instruction : cctx -> tctx -> rctx -> instruction -> 
                       (tctx*rctx)
val tc_block : cctx -> tctx -> rctx -> block -> unit

val force_pair : mtp -> (wtp*wtp)
val force_codetp : dtp -> (tctx*rctx)
val compress : tctx -> wtp -> tctx * wtp
val mkpair : wtp * wtp -> mtp
