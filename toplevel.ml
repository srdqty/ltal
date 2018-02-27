open Codegen;;

Ltal.short_code := false;;

let parse s = Parser.parse (Lexer.lex) (Lexing.from_string s)

let optimize x = print_string "---optimize---\n";Optimize.denest(Optimize.deadcode(Optimize.inline(Optimize.copyprop(Optimize.denest x))));;
let optimize' x = print_string "---optimize---\n";Optimize.denest(Optimize.cfelim (Optimize.deadcode (Optimize.inline (Optimize.copyprop(Optimize.denest x)))));;

let print_il e = 
  let env = Var.mkvar "env" in
  let r = Var.mkvar "r" in
  let e = (Absyn.alpha_convert e) in
  print_string (Absyn.pp_exp e);
  print_string "Typechecking source... ";
  let t1 = Tcabsyn.ti Ctx.emp Ctx.emp e in
  print_string ("OK ("^(Absyn.pp_tp t1)^")\n");
  print_string "Translating to IL... ";
  let e1 = Translate.exp2il Ctx.emp Ctx.emp Ctx.emp e t1 Il.top in
  print_string "OK\n";
  let e2 = Lift.lift (Il.LetPair(r,env,e1, Il.Var r)) in
  let e3 = Optimize.denest e2 in
  print_string (Il.pp_exp' e3);
  print_string "Typechecking IL... ";
  let tp = Tcil.ti_closed e3 in 
  print_string ("OK ("^(Il.pp_tp tp)^")\n")

let printopt_il e = 
  let env = Var.mkvar "env" in
  let r = Var.mkvar "r" in
  let e = (Absyn.alpha_convert e) in
  print_string (Absyn.pp_exp e);
  print_string "Typechecking source... ";
  let t1 = Tcabsyn.ti Ctx.emp Ctx.emp e in
  print_string ("OK ("^(Absyn.pp_tp t1)^")\n");
  print_string "Translating to IL... ";
  let e1 = Translate.exp2il Ctx.emp Ctx.emp Ctx.emp e t1 Il.top in
  print_string "OK\n";
  let e2 = Lift.lift (Il.LetPair(r,env,e1, Il.Var r)) in
  let e3 = optimize(optimize(optimize(optimize e2))) in
  print_string (Il.pp_exp' e3);
  print_string "Typechecking IL... ";
  let tp = Tcil.ti_closed e3 in 
  print_string ("OK ("^(Il.pp_tp tp)^")\n")
  

let compile e = 
  let e = Absyn.alpha_convert e in
  let env = Var.mkvar "env" in
  let r = Var.mkvar "r" in
  let t1 = Tcabsyn.ti Ctx.emp Ctx.emp e in
  let e1 = Translate.exp2il Ctx.emp Ctx.emp Ctx.emp e t1 Il.top in
  let e2 = Lift.lift (Il.LetPair(r,env,e1, Il.Var r)) in


  let t2 = Tcil.ti_closed (e2) in 
  let e3 = e2 in
      

  let (cs,cctx,l) = 
    try (Codegen.codegen e3 t2)
    with Codegen.BlockFail (msg,benv) -> 
      print_string ("\nError: in block "^(Var.to_string benv.lab)^"\n");
      print_string ("with type "^(Ltal.pp_dtp (Ctx.lookup benv.cenv.cctx benv.lab))^"\n");
      List.iter (fun i -> print_string (Ltal.pp_instruction i);
	print_string "\n") (List.rev benv.ilist);
      print_string msg;
      raise Util.NYI in
  let tp = Codegen.typetrans Ctx.emp t2 in
  let cs = Ctx.restrict cs (List.rev (Ctx.dom cs)) in
  let cctx = Ctx.restrict cctx (List.rev (Ctx.dom cctx)) in
  (cs,cctx,l,t1,tp)


let compile_opt e = 
  let e = Absyn.alpha_convert e in
  let env = Var.mkvar "env" in
  let r = Var.mkvar "r" in
  (*print_string "\n--------------\n";
  print_string (Absyn.pp_exp ( e));
  print_string "\n--------------\n";*)
  let t1 = Tcabsyn.ti Ctx.emp Ctx.emp e in
(*  print_string "\n--------------\n";*)
  let e1 = Translate.exp2ilcf Ctx.emp Ctx.emp Ctx.emp e t1 Il.top in
(*  print_string (Il.pp_exp' (Lift.lift e1));*)
  let e2 = Il.LetPair(r,env,e1, Il.Var r) in
(*  print_string (Il.pp_exp' (Lift.lift e2));
  print_string "\n--------------\n";*)

  let e2' = (optimize' (optimize'(optimize'( Lift.lift e2)))) in
  print_string "\n--------------\n";
  let e2'' = Optimize.copyprop(Optimize.denest(Translate.ilcf2il ( e2' ))) in
  print_string (Il.pp_exp' (e2''));
  print_string "\n--------------\n";
  let e3 = optimize (optimize (optimize (Lift.lift e2''))) in
  print_string (Il.pp_exp' e3);
  
  let t2 = Tcil.ti_closed e3 in 
(*  print_string (Il.pp_tp t2);
  print_string "\n";*)
  let (cs,cctx,l) = 
    try (Codegen.codegen e3 t2)
    with Codegen.BlockFail (msg,benv) -> 
      print_string ("\nError: in block "^(Var.to_string benv.lab)^"\n");
      print_string ("with type "^(Ltal.pp_dtp (Ctx.lookup benv.cenv.cctx benv.lab))^"\n");
      List.iter (fun i -> print_string (Ltal.pp_instruction i);
	print_string "\n") (List.rev benv.ilist);
      print_string msg;
      raise Util.NYI in
  let tp = Codegen.typetrans Ctx.emp t2 in
  let cs = Ctx.restrict cs (List.rev (Ctx.dom cs)) in
  let cctx = Ctx.restrict cctx (List.rev (Ctx.dom cctx)) in
  (cs,cctx,l,t1,tp)
      ;;



let run (cs,cctx,l,stp,tp) i = 
  let mk_machine i = 
    let (hp,l) = Eval.initheap i in
    let regf = Ctx.emp in 
    let regf = Ctx.extend regf Codegen.rs (Ltal.IntV (-1)) in
    let regf = Ctx.extend regf Codegen.rt (Ltal.IntV (-1)) in
    let regf = Ctx.extend regf Codegen.ru (Ltal.IntV (-1)) in
    let regf = Ctx.extend regf Codegen.rr (Ltal.IntV (-1)) in
    let regf = Ctx.extend regf Codegen.rf l                in
    let regf = Ctx.extend regf Codegen.ra (Ltal.IntV (-1)) in
    (hp,regf) in
  let (hp,regf) = mk_machine i in
  let (hp,regf,n) = Eval.profile (cs,hp,regf) l in
  let ans = Ctx.lookup regf ra in
  print_string ((Eval.print_value_wtp hp ans tp)^" : "^(Absyn.pp_tp stp)^"\n");
  print_string ("Instructions executed: "^(string_of_int n)^"\n");;

let print oc (cs,cctx,l,stp,tp) = output_string oc (Ltal.pp_code cctx cs);;


let count_instrs (cs,_,_,_,_) = 
  Ctx.fold (fun _ (instrs,ei) s -> List.length instrs + 1 + s) cs 0;;

let check (cs,cctx,l,stp,tp) = 
  let cctc = try Tcltal.wf_cctx cctx with Util.TcFail msg -> print_string(msg) in
  
  let cstc = try Tcltal.tc_code_section cs cctx with Util.TcFail msg -> print_string(msg) in
  ();;

let main args = 
  let timer = ref 0.0 in
  let start_timer () = 
    timer := Sys.time() in
  let time_msg msg = 
    let diff = Sys.time() -. !timer in
    print_string (msg^" took "^(string_of_float diff)^" s\n");
    flush stdout
  in
  if Array.length args < 3
  then print_string "Usage: ltalc file heapsz\n"
  else 
    let file = Array.get args 1 in
    let sz = (int_of_string (Array.get args 2)) in
    if Sys.file_exists file then
      let ic = open_in file in
      start_timer();
      let e = 
	try 
	Parser.parse Lexer.lex (Lexing.from_channel ic)
	with Parsing.Parse_error -> (print_string ("Parse error near line "^(string_of_int (!Lexer.lineno))^"\n"); raise Parsing.Parse_error) in
      time_msg "Parsing";
      start_timer();
      let p = compile_opt e in
      time_msg "Compiling";
      start_timer();
      let () = check p in 
      time_msg "Checking";
      print_string ("Instruction count: "^(string_of_int (count_instrs p))^"\n");
      start_timer();
      run p sz;
      time_msg "Running";
(*      let oc = open_out (file^".ltal") in
      print oc p;
      close_out oc
*)    else print_string "File not found\n";;

(*main [|"";"tests/foo.ltl";"100"|];;*)

main Sys.argv;;
