#use "make.ml"

open Var;;
open Op;;


open Lfpl;;
let env = mkvar "env";;
let f = mkvar "f";;
let x = mkvar "x";;
let y = mkvar "y";;
let w = mkvar "w";;
let z = mkvar "z";;
let v = mkvar "v";;
let d = mkvar "d";;
let t = mkvar "t";;
let h = mkvar "h";;
let l = mkvar "l";;
let acc = mkvar "acc";;


let rev_aux = mkvar "rev_aux";;
let rev = mkvar "rev";;
let build = mkvar "build";;
let _build = {rettp = List(Nat);
	      name = build;
	      argtys = [Nat,x];
	      body = Match(Var x, 
			   [IntC 0, P(Nil);
			    Hole(y), P(Cons(Hole(NewDmnd), Hole(Op(Var y,Times, Var y)), Hole(App(build,[Op(Var y, Minus, P(IntC 1))]))))])};;

let _rev_aux = {rettp = List(Nat);
	       name = rev_aux;
	       argtys = [List(Nat),l;List(Nat),acc];
	       body = Match(Var l,
			    [Nil,Var acc;
			     Cons(Hole d,  Hole h, Hole t),
			     App(rev_aux,[Var t;
					  P(Cons(Hole(Var d), Hole(Var h), Hole(Var acc)))])])}

let _rev = {rettp = List(Nat);
	    name = rev;
	    argtys = [List(Nat),l];
	    body = App(rev_aux,[Var l;P(Nil)])};;

let hd = mkvar "hd";;
let _hd = {rettp = Nat;
	   name = hd;
	   argtys = [List(Nat),l];
	   body = Match(Var l,
			 [Nil,P(IntC 0);
			  Cons(Hole d, Hole h, Hole t),
			  Var h])};;

let do_build = [_build],App(build,[P(IntC 1000)]);;
let do_rev = [_build;_rev_aux;_rev;_hd], App(hd,[App(rev, [App(build,[P(IntC 500)])])]);;


let dbl = mkvar "double";;
let _dbl = {rettp = Nat;
	   name = dbl;
	   argtys = [Nat,x;Nat,y];
	   body = Op(Var x, Times, Var y)}
let fact = mkvar "fact";;
let _fact = {rettp = Nat;
	     name = fact;
	     argtys = [Nat,x];
	     body = Match(Var x, [IntC 0, P(IntC 1);
				  Hole(y), Op(Var y, Times, App(fact,[Op(Var y, Minus, P(IntC 1))]))])};;

let prog2 = [_dbl;_fact],App(fact,[P(IntC 10)]);;
	   
let optimize x = Optimize.denest(Optimize.deadcode(Optimize.inline(Optimize.copyprop(Optimize.denest x))));;

let test prog = 
  let tp = Tclfpl.ti_prog prog in
  let e = Lfpl2il.translate1 prog in
  let tp' = Lfpl2il.tp0trans tp in
  Tcil.tc_closed e tp';
  let e = optimize e in
  Tcil.tc_closed e tp';
  let tp'' = Codegen.typetrans Ctx.emp tp' in
  let (cs,cc,l) = Codegen.codegen e Il.Int in
  let cs = Ctx.restrict cs (List.rev (Ctx.dom cs)) in
  let cc = Ctx.restrict cc (List.rev (Ctx.dom cc)) in
  (cs,cc,l,tp,tp'');;

let teststk prog = 
  let tp = Tclfpl.ti_prog prog in
  let e = Lfpl2il.translate1 prog in
  let tp' = Lfpl2il.tp0trans tp in
   Tcil.tc_closed e tp';
  let e = optimize e in
  Tcil.tc_closed e tp';
  let tp'' = Codegen.typetrans Ctx.emp tp' in
  let (cs,cc,l) = Stackcodegen.codegen e Il.Int in
  let cs = Ctx.restrict cs (List.rev (Ctx.dom cs)) in
  let cc = Ctx.restrict cc (List.rev (Ctx.dom cc)) in
  (cs,cc,l,tp,tp'');;


let run (cs,cctx,l,tp,tp'') i = 
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
  let ans = Ctx.lookup regf Codegen.ra in
  print_string (Eval.print_value_wtp hp ans tp''^" : "^Lfpl.pp_tp0 tp^"\n");
  print_string ("Instructions executed: "^(string_of_int n)^"\n");;


let stkrun (cs,cctx,l,tp,tp'') i = 
  let mk_machine i = 
    let (hp,l) = Eval.initheap i in
    let stk = Var.mkvar "stk" in
    let hp = Var.add stk [] hp in
    let regf = Ctx.emp in 
    let regf = Ctx.extend regf Stackcodegen.rs (Ltal.Lab stk) in
    let regf = Ctx.extend regf Stackcodegen.rt (Ltal.IntV (-1)) in
(*    let regf = Ctx.extend regf Stackcodegen.ru (Ltal.IntV (-1)) in*)
    let regf = Ctx.extend regf Stackcodegen.rr (Ltal.IntV (-1)) in
    let regf = Ctx.extend regf Stackcodegen.rf l                in
    let regf = Ctx.extend regf Stackcodegen.ra (Ltal.IntV (-1)) in
    (hp,regf) in
  let (hp,regf) = mk_machine i in
  let (hp,regf,n) = Eval.profile (cs,hp,regf) l in
  let ans = Ctx.lookup regf Stackcodegen.ra in
  print_string (Eval.print_value_wtp hp ans tp''^" : "^Lfpl.pp_tp0 tp^"\n");
  print_string ("Instructions executed: "^(string_of_int n)^"\n");
  print_string ("Max stack used: "^(string_of_int (!Eval.stack_max))^"\n");;

let print_prog (cs,cc,_,_,_) = 
  print_string(Ltal.pp_code cc cs);;
