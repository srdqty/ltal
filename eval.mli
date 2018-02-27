(* Evaluation for LTAL programs *)

val step : Ltal.program_state -> Ltal.program_state option

val initheap : int -> (Ltal.heap * Ltal.value)

val eval : (Ltal.code_section* Ltal.heap * Ltal.register_file) -> Ltal.clab -> 
  (Ltal.heap * Ltal.register_file)

val profile : (Ltal.code_section* Ltal.heap * Ltal.register_file) -> 
  Ltal.clab -> 
  (Ltal.heap * Ltal.register_file * int)

val print_value_wtp : Ltal.heap -> Ltal.value -> Ltal.wtp -> string

exception Error of string;;

val stack_max : int ref ;;
