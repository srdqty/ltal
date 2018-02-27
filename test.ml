#use "make.ml"

open Var;;
open Op;;


open Absyn;;
let env = mkvar "env";;
let f = mkvar "f";;
let x = mkvar "x";;
let y = mkvar "y";;
let w = mkvar "w";;
let z = mkvar "z";;
let v = mkvar "v";;

let five = IntC 5;;
let six = IntC 6;;

let i =  (Lam("y", Arrow(Int,Int), Var "y"));;
let plus1 =  (Lam ("w",Int,Op(Plus,[Var "w";IntC 1 ])));;
let plus =  (Lam ("w",Times(Int,Int),Op(Plus,[Fst(Var "w"); Snd(Var "w")])));;
let app =  (Lam("y",Arrow(Int,Int),Lam ("x",Int,App(Var "y",Var "x"))));;
let fact =  (Fix ("fact","x", Int, Int, 
			       If0 (Var "x", IntC 1,
				    Op(Op.Times,
				       [App (Var "fact", Op(Minus,[Var "x";IntC 1]));
					Var "x"]))));;
let fact0 =  (Lam ("x", Int, 
			       If0 (Var "x", IntC 1,
				    Op(Op.Times,
				       [Op(Op.Minus,[Var "x";IntC 1]);
					Var "x"]))));;

let bottom =  (Fix("f","x", Int, Int, 
			       App(Var "f",Var "x")));;

let neg =  (Lam("x", Int,If0 (Var "x", IntC 1, IntC 0)));;

let fplus =  (Fix ("plus","w",Int,Int,Op(Plus,[Var "w";IntC 1 ])));;

let lettest0 =  
    (Let("x",IntC 5,Var "x"));;
let lettest =  
    (Let("x",Lam("w", Int, IntC 5),
     Let("y",Lam("z",Int,Op(Plus,[App(Var "x", Var "z");Var "z"])),
     App(Var "y", IntC 10))));;

let head =  
    (Lam ("y", List(Int), 
	  Case(Var "y", Nil, "h", "t", Cons(Var "h",Nil) )));;

let nil = Nil;;
let cons3 = Cons(IntC 0, Cons(IntC 1, Cons(IntC 2, Nil)));;

let swap = 
    Fix("swap", "p", Times((Int),(Int)), Times(Int,Int),
		     App(Var "swap", Pair(Fst(Var "p"), Snd(Var "p"))));;

let length = Toplevel.parse "(fix f(x:int list):int (case x (nil -> 0) (cons h t -> (+ 1 (f t)))))"

let rev = 
    (Lam ("x", List(Int),
     Let("rev", Fix("f", "l",List(Int), Arrow(List(Int), List(Int)),
		     Lam("acc", List(Int), Case(Var "l", Var "acc", 
			  "h","t", App(App(Var "f", Var "t"), 
				       Cons(Var "h", Var "acc"))))),
	 App(App(Var "rev", Var "x"), Nil))));;

(* ints, ops, if, pair, fst, snd, lam, app all work alone *)
(* but, returning closures does not work, eg k *)


let f =  (App(Lam("x", Arrow(Int,Int),If0(IntC 0,App(Lam("y", Int, five),five),Snd(Pair(six,five)))),Lam ("z", Int, five)));;

let tests = [five;
	     Op(Plus,[five;six]);
	     plus;
	     plus1;
	     App(plus1,five);
	     fact;
	     App(fact,five);
	     i;
	     app;
	     App(app,plus1);
	     App(App(app,plus1),five);
	     lettest0;
	     lettest];;

let do_test e = 
  print_string(Absyn.pp_exp0 (fun x -> x) e); 
  print_string " = ";
  let p = Toplevel.compile e in
  let () = Toplevel.check p in
  try 
    Toplevel.run p 200;
    print_string "\nSuccess!\n"
  with Eval.Error msg -> print_string msg
  

let do_tests () = 
  List.iter do_test tests;;
