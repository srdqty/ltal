open Op;;
open Var;;
open Ctx;;
open Ltal;;
open Util;;

let debug msg = ();;

let rs = mkvar "rs";;
let ra = mkvar "ra";;
let rf = mkvar "rf";;
let rt = mkvar "rt";;
let ru = mkvar "ru";;
let rr = mkvar "rr";;

let retty stackty uty aty = (Code(Ctx.from_list[(rs,stackty);
				    (ra,aty);
				    (rt,toptp);
				    (ru,uty);
				    (rf,listtp);
				    (rr,toptp)]))

let rec tt tctx ctx tp = 
  match tp with
    Il.TVar a -> if bound tctx a then TVar a else lookup ctx a
  | Il.Int -> DTp Word
  | Il.Top -> DTp Top (* for now *)
  | Il.Tensor(t1,t2) -> Ref(Tcltal.mkpair (tt tctx ctx t1, tt tctx ctx t2))
  | Il.Exists (alpha, tp) -> 
      let beta = rename alpha in
      Exists (beta, W, tt tctx (extend ctx alpha (TVar beta)) tp)
  | Il.List t -> 
      let tv = mkvar "list" in
      Mu(tv,NRef(Tcltal.mkpair(tt tctx ctx t, TVar tv)))
  | _ -> DTp(arrowtt tctx ctx tp)

and arrowtt tctx ctx t = 
  match t with
    Il.Forall(alpha,t) -> 
      let beta = Var.rename alpha in
      Forall(beta, W, arrowtt tctx (extend ctx alpha (TVar beta)) t)
  | Il.Arrow(t1,t2) -> 
      let t1' = tt tctx ctx t1 in
      let t2' = tt tctx ctx t2 in
      let stk = mkvar "s" in
      let u = mkvar "u" in
      ( 
	Forall (stk,W,Forall (u,W,
	   Code(Ctx.from_list[(rs,Ref(Tcltal.mkpair(t1',TVar stk)));
			      (ra, toptp);
			      (rt,toptp);
			      (ru,(TVar u));
			      (rf,listtp);
			      (rr,DTp(retty (TVar stk) (TVar u) t2'))]))))
  | _ -> tcfail "expected a function type in forall"

let typetrans tctx tp = tt tctx Ctx.emp tp
let arrowtypetrans tctx t1 t2 = arrowtt tctx Ctx.emp (Il.Arrow (t1,t2))

(* Need to specify the type ty of "the rest of the stack", in most cases 
  alpha *)



type code_env = {cctx : cctx;
		 cs : code_section;
		 fctx : Il.ctx;
		 lctx : var Ctx.ctx}

let get_fctx cenv = cenv.fctx
let get_lctx cenv = cenv.lctx



type block_env = {cenv : code_env;
		  ilist : instruction list;
		  lab : clab;
		  tctx : Ltal.tctx;
		  rctx : Ltal.rctx}
		  
let get_from_cenv f benv = f benv.cenv

exception CodeFail of string * code_env
exception BlockFail of string * block_env

		  

(*
val begin_fn : code_env -> clab -> register_file -> block_env 
val end_fn : block_env -> code_env 
val emit_label : fn_env -> clab -> dtp -> block_env 
val emit       : block_env -> instruction -> block_env -> block_env 
val emit_end   : end_instruction -> block_env -> fn_env
val drop       : reg -> block_env -> block_env
val free       : reg -> block_env -> block_env
val push       : reg -> reg -> block_env -> block_env
val pop        : reg -> reg -> block_env -> block_env
val malloc     : reg -> block_env -> block_env
*)

let do_print y x = (debug y; x)

let (>>) f g x = g(f(x))
let (>>=) f h x = let y = f x  in h y x


let rec mkltp tctx rctx = 
    Ctx.fold (fun t sk dtp -> 
      let k = match sk with _,W -> W | _,M -> M in
      Forall(t,k,dtp)) 
    tctx (Code (rctx))

let current_ltp benv = 
  debug ("Generalizing "^(Ctx.pp_ctx (fun _ -> "") benv.tctx)^"\n");
  (mkltp benv.tctx benv.rctx)

let current_rettp t2 benv = 
  debug ("Generalizing "^(Ctx.pp_ctx (fun _ -> "") benv.tctx)^"\n");
  (try Tcltal.wf_wtp benv.tctx t2
      with TcFail msg -> raise (BlockFail ("while calculating current return type, provided return register type "^(Ltal.pp_wtp t2)^" was ill formed because "^msg,benv)));

  let pop_stack t = 
    match t with
      Ref(Tensor(_,Tensor(t',One))) -> t'
    | _ -> raise (Impos "Expected at least one element on the stack type") in
  let rctx = benv.rctx in
  (* return address register is top *)
  let rctx = update rctx rr toptp in
  (* don't know how list will change *)
  let rctx = update rctx rf listtp in
  (* return value in ra *)
  let rctx = update rctx ra t2 in
  (* argument popped off stack *)
  let rctx = update rctx rs (pop_stack (lookup rctx rs)) in
  (* everything else is the same *)
  mkltp benv.tctx rctx


let current_iftp tp benv = 
  debug ("Generalizing "^(Ctx.pp_ctx (fun _ -> "") benv.tctx)^"\n");
  let rctx = benv.rctx in
  (* set return value *)
  let rctx = update rctx ra tp in
  (* don't know how list will change *)
  let rctx = update rctx rf listtp in
  mkltp benv.tctx rctx


let declare_label l ltp benv = 
  (try Tcltal.wf_dtp emp ltp
  with TcFail msg -> 
    raise (BlockFail ("In block "^(Var.to_string l)
		      ^", type\n"^(Ltal.pp_dtp ltp)
		      ^" is ill formed because "^msg, benv)));
  let cctx' = extend benv.cenv.cctx l ltp in
  {cenv={cctx=cctx';cs=benv.cenv.cs;lctx=benv.cenv.lctx;fctx=benv.cenv.fctx};
   ilist = benv.ilist;
   lab = benv.lab;
   tctx= benv.tctx;
   rctx=benv.rctx}

let emit_label l ltp cenv =
  try 
    let tctx, rctx = Tcltal.force_codetp ltp in
    {cenv = cenv;
     ilist = [];
     lab = l;
     tctx = tctx;
     rctx=rctx}
  with TcFail msg -> raise (CodeFail (msg,cenv))

let ($) l ltp = 
  do_print ("Labeling "^(Var.to_string l)^"\n") >>
  emit_label l ltp

let emit inst benv = 
  try let tctx,rctx = Tcltal.tc_instruction 
      benv.cenv.cctx benv.tctx benv.rctx inst in
  {cenv=benv.cenv; ilist = inst::benv.ilist; lab = benv.lab; 
   tctx = tctx; rctx= rctx}
  with TcFail msg -> raise (BlockFail (msg,benv))

let emit_end ei benv  = 
  try 
    Tcltal.tc_block benv.cenv.cctx benv.tctx benv.rctx ([],ei);
    let l = benv.lab in
    let cenv = benv.cenv in
    let blk = (List.rev benv.ilist), ei in
    let cs' = extend cenv.cs l blk in
    {cctx = cenv.cctx; cs = cs'; fctx = cenv.fctx; lctx = cenv.lctx}
  with TcFail msg -> raise (BlockFail (msg,benv))



let add r s t = (emit (ADD(r,s,RegOp t)))
let sub r s t = (emit (SUB(r,s,RegOp t)))
let mul r s t = (emit (MUL(r,s,RegOp t)))
let bnzl r l = (emit (BC(NZ,r,CLabOp l)))
let bcl c r l = (emit (BC(c,r,CLabOp l)))
let ld r s i = (emit (LD(r,s,i)))
let mov r s = (emit (MOV(r,RegOp s)))
let movi r i = (emit (MOV(r,IntOp i )))
let movl r l = (emit (MOV(r,CLabOp l)))
let st r i s = (emit (ST(r,i,s)))
let comment msg = (emit (COMMENT msg))
let jmpl l = emit_end (JMP (CLabOp l))
let jmp r = emit_end (JMP(RegOp r))
let halt = emit_end HALT
let fail msg = emit_end (FAIL msg)

(* TODO: This could be buggy if wtp has existentials in it; if so, complain *)

let rec coerce_ref_ltp r ltp = 
  let coerce_ref_wtp wtp = 
    match Tcltal.compress emp wtp with 
      tctx,Ref(mtp) -> tctx,Ref(mtp)
    | tctx,NRef(mtp) -> tctx,Ref(mtp)
    | _ -> impos ("expected reference type for "^(Var.to_string r)^" here") in
  match ltp with
    Forall (tv,k,ltp) -> Forall(tv,k,coerce_ref_ltp r ltp) 
  | Code(rctx) -> 
      let rtp = lookup rctx r in
      let tctx,tp' = coerce_ref_wtp rtp in
      mkltp tctx (update rctx r tp')
  | Word -> impos "expected a code type, found word"
  | Zero -> impos "expected a code type, found zero"
  | Top -> impos "expected a code type, found top"

let currently_nonempty r benv = 
  match lookup benv.rctx r with
    Ref(Tensor(_,_)) -> true
  | _ -> false

let case r i1 i2 = 
  (currently_nonempty r >>= fun x -> 
  if x 
  then   
    i2
  else 
  let l = mkvar "l" in
  (current_ltp  >>= (fun ltp -> 
  let ltp' = coerce_ref_ltp r ltp in
  (declare_label l ltp') >>
  (bnzl r l) >>
  i1 >>
  (l $ ltp') >>
  i2)))

let malloc r = 
  case rf (fail "out of memory") ((mov r rf) >> (ld rf r 1))

let check_freeable r benv = 
  match lookup benv.rctx r with
    Ref(mtp) -> 
      (match Tcltal.force_pair mtp with 
	DTp _, DTp _ -> benv
      | tp -> raise (BlockFail ("register "^(Var.to_string r)^" has non-freeable type "^(pp_mtp mtp), benv)))
  | tp -> raise (BlockFail ("register "^(Var.to_string r)^" has non-freeable type "^(pp_wtp tp), benv))

let free r = 
  (check_freeable r) >>
  (st r 1 rf) >>
  (mov rf r)

let push r1 r2 = 
  (malloc rt) >>
  (st rt 0 r2) >>
  (st rt 1 r1) >>
  (mov r1 rt)

let drop r = 
  (ld rt r 1) >>
  (free r) >>
  (mov r rt)

let pop r s = 
  (ld r s 0) >>
  (drop s)
  
let rot r s = 
  (mov rt s) >>
  (ld s rt 1) >>
  (st rt 1 r) >>
  (mov r rt)

let begin_fn lf t1 t2 = (* figure out starting code label type for f *)
  let ltp = (arrowtypetrans emp t1 t2) in
  (lf $ ltp) >>
  (declare_label lf ltp)


let end_fn = (* pop argument storage and return *)
  (drop rs) >> 
  (jmp rr)

let bind_fn f lf t1 t2 cenv = (* bind f to lf in lctx and t1 -> t2 in fctx *)
  let lctx' = extend cenv.lctx f lf in
  {cctx = cenv.cctx;
   cs = cenv.cs;
   fctx = extend cenv.fctx f (Il.Arrow(t1,t2));
   lctx = lctx'}


let begin_program lstart tp = 
  let ltp = (Code(Ctx.from_list[(rs,toptp);
			       (ra,toptp);
			       (rt,toptp);
			       (ru,toptp);
			       (rf,listtp);
			       (rr,toptp (* DTp(retty wordtp tp)*))])) in
  (lstart $ ltp) >>
  (declare_label lstart ltp)


let end_program = 
  halt


let print_rtp r benv = 
  debug("Type of "^(Var.to_string r)^" is "^(Ltal.pp_wtp (lookup benv.rctx ra))^"\n")

let pack_rtp r t benv = 
  debug ("packing\n");
  let rctx' = update benv.rctx r t in
  {cenv=benv.cenv; rctx=rctx';  ilist = benv.ilist; lab = benv.lab; 
   tctx = benv.tctx}

let unpack_rtp r tv benv =
  let rtp = lookup benv.rctx r in
  match rtp with
    Exists (tv',k,tp) -> 
      debug ("unpacking existential "^(Var.to_string tv')^" to "^(Var.to_string tv)^"\n");
      let rctx' = update benv.rctx r (Ltalsubst.subst1w_wtp tv' (TVar tv) tp) in
      {cenv=benv.cenv; rctx=rctx';  ilist = benv.ilist; lab = benv.lab; 
       tctx = extend benv.tctx tv (QForall,k)}
  | _ -> raise (BlockFail ("attempted to unpack non-existential type "^(Ltal.pp_wtp rtp),benv))
      benv

let compress_rtp r benv = 
  let rtp = lookup benv.rctx r in
  let tctx',rtp' = Tcltal.compress benv.tctx rtp in
  let rctx' = update benv.rctx r rtp' in
  {cenv=benv.cenv; rctx=rctx';  ilist = benv.ilist; lab = benv.lab; 
   tctx = tctx'}

let codegen e tp = 
  let lstart = mkvar "start" in 
  let rec codegen_outer e tp = 
    match e with
      Il.Let (f,Il.Fn(x,t1,e1),e2) -> 
	let lf = rename f in
	(get_fctx >>= fun fctx -> 
        let ctx = (extend fctx x t1) in
	let t2,_ = Tcil.ti emp ctx e1 in
	(begin_fn lf t1 t2) >> 
	((codegen_inner emp ctx e1 t2) >>
	(end_fn >>
	((bind_fn f lf t1 t2) >>
	((codegen_outer e2 tp))))))
    | Il.Let (g,Il.Fix(f,x,t1,t2,e1),e2) -> 
	let lf = rename g in
	((bind_fn f lf t1 t2) >> 
	((get_fctx >>= fun fctx -> 
	(let ctx = (extend fctx x t1) in
	((begin_fn lf t1 t2) >>
	((codegen_inner emp ctx e1 t2) >>
	(end_fn >>
	((bind_fn g lf t1 t2) >> 
	((codegen_outer e2 tp))))))))))
    | e -> 
	let tp' = typetrans emp tp in 
	(get_fctx >>= fun fctx -> 
	((begin_program lstart tp') >>
	((codegen_inner emp fctx e tp) >>
	((end_program)))))

  and codegen_var d v = 
    (get_from_cenv(get_lctx) >>= fun lctx -> 
    if bound lctx v 
    then movl ra (lookup lctx v)
    else 
      match d with
	[] -> impos ("unbound variable "^(Var.to_string v))
      | w::d' -> 
	  if Var.eq v w 
	  then ((debug ("Getting variable "^(Var.to_string v));
		((ld ra rs 0)>>
		((print_rtp ra)>>= fun x -> (fun y -> y)))))
	  else
	    (comment "8 pointless instructions") >>
	    (rot ru rs) >>
	    (codegen_var d' v) >>
	    (rot rs ru))
	       


  and codegen_inner tctx ctx e tp = 
    match e with
      Il.Var x -> 
	(comment ("Getting variable "^(Var.to_string x))) >>
	codegen_var (Ctx.dom ctx) x
    | Il.IntC i -> 
	(comment (string_of_int i)) >>
	(movi ra i)
    | Il.Op(Op.Plus,e1,e2) -> 
	(comment ("+")) >>
	(codegen_inner tctx ctx e1 Il.Int) >>
	(push ru ra) >>
	(codegen_inner tctx ctx e2 Il.Int) >>
	(ld rt ru 0) >>
	(add ra rt ra) >>
	(drop ru)
    | Il.Op(Op.Minus,e1,e2) -> 
	(comment ("-")) >>
	(codegen_inner tctx ctx e1 Il.Int) >>
	(push ru ra) >>
	(codegen_inner tctx ctx e2 Il.Int) >>
	(ld rt ru 0) >>
	(sub ra rt ra) >>
	(drop ru)
    | Il.Op(Op.Times,e1,e2) -> 
	(comment ("*")) >>
	(codegen_inner tctx ctx e1 Il.Int) >>
	(push ru ra) >>
	(codegen_inner tctx ctx e2 Il.Int) >>
	(ld rt ru 0) >>
	(mul ra rt ra) >>
	(drop ru)
    | Il.If(c,e,e1,e2) -> 
	(comment "if0") >>
	let l1 = mkvar "l" in
	let l2 = mkvar "l" in
	let _,ctx' = Tcil.ti tctx ctx e in
	(codegen_inner tctx ctx e Il.Int) >>
	(current_ltp >>= (fun ltp -> 
	(declare_label l1 ltp) >>
	(bcl c ra l1) >>
	(codegen_inner tctx ctx' e2 tp) >>
	(current_iftp (typetrans tctx tp) >>= (fun ltp' -> 
	(declare_label l2 ltp') >>
	(jmpl l2) >>
	(l1 $ ltp) >>
	(codegen_inner tctx ctx' e1 tp) >>
	(jmpl l2) >>
	(l2 $ ltp')))))
    | Il.Pair(e1,e2) -> 
	(comment ("pair")) >>
	let t1,ctx' = Tcil.ti tctx ctx e1 in
	let t2,ctx'' = Tcil.ti tctx ctx' e2 in
	(codegen_inner tctx ctx e1 t1) >>
	(push ru ra) >>
	(codegen_inner tctx ctx' e2 t2) >>
	(rot ra ru)
(*	(mov rt ru) >>
	(ld ru rt 1) >>
	(st rt 1 ra) >>
	(mov ra rt)*)
    | Il.LetPair(x1,x2,e1,e2) ->
	(comment ("letpair "^(Var.to_string x1)^","^(Var.to_string x2))) >>
	let t,ctx' = Tcil.ti tctx ctx e1 in
	let t1,t2 = Tcil.force_tensor t in
	(codegen_inner tctx ctx e1 t) >>
        (rot rs ra) >>
	(push rs ra) >>
	(codegen_inner tctx (extend (extend ctx x1 t1) x2 t2) e2 tp) >>
	(drop rs) >>
	(drop rs)
    | Il.Pack(t,e,t') -> 
	(comment  ("pack")) >>
	let (v,t'') = Tcil.force_exists t' in 
	(codegen_inner tctx ctx e (Ilsubst.subst1_tp v t t'')) >>
	(pack_rtp ra (typetrans tctx t'))
    | Il.LetUnpack(tv,x,e1,e2) -> 
	(comment("unpack "^(Var.to_string tv)^","^(Var.to_string x))) >>
	let t,ctx' = Tcil.ti tctx ctx e1 in
	let (v,t'') = Tcil.force_exists t in 
	(codegen_inner tctx ctx e1 t) >>
	(unpack_rtp ra tv) >>
	(push rs ra) >>
	(codegen_inner (extend tctx tv ()) 
	   (extend ctx' x (Ilsubst.subst1_tp v (Il.TVar tv) t''))
	   e2 tp) >>
	(drop rs)
    | Il.Let(x,e1,e2) -> 
	(comment("let "^(Var.to_string x))) >>
	let t,ctx' = Tcil.ti tctx ctx e1 in
	(codegen_inner tctx ctx e1 t) >>
	(push rs ra) >>
	(codegen_inner tctx (extend ctx x t) e2 tp) >>
	(drop rs)
    | Il.Fn(x,t,e) -> impos "fn should never occur in an inner derivation"
    | Il.Fix(f,x,t1,t2,e) -> impos "fix should never occur in an inner derivation"
    | Il.App(Il.Var f, e) -> 
	(comment ("app")) >>
	let t1,t2 = Tcil.force_arrow (lookup ctx f) in
	let lret = mkvar "lret" in
	(codegen_inner tctx ctx e t1) >>
	(push ru ra) >>
	(codegen_var (Ctx.dom ctx) f) >>
	(push rs rr) >>
	(rot rs ru) >>
	((current_rettp (typetrans tctx t2)) >>= fun ltp ->
	(declare_label lret ltp) >>
	(movl rr lret) >>
	(jmp ra) >>
	(lret $ ltp) >>
	(ld rr rs 0) >>
	(drop rs))
	
    | Il.App(_,_) -> impos "all applications must be of variables to expressions"
    | Il.Nil -> 
	(comment "nil") >>
	(movi ra 0)
    | Il.Cons(e1,e2) -> 
	(comment ("cons")) >>
	let tp' = Tcil.force_list tp in
	(codegen_inner tctx ctx e1 tp') >>
	(push ru ra) >>
	(codegen_inner tctx ctx e2 tp) >>
	(mov rt ru) >>
	(ld ru rt 1) >>
	(st rt 1 ra) >>
	(mov ra rt)
(* TODO: Factor out case and if0 into the case used by malloc. *)
    | Il.Case(e,e1,x,y,e2) -> 
	(comment "case") >>
	let l1 = mkvar "l" in
	let l2 = mkvar "l" in
	let tp',ctx' = Tcil.ti tctx ctx e in
	let tp'' = Tcil.force_list tp' in
	(codegen_inner tctx ctx e tp') >>
	(current_ltp >>= (fun ltp -> 
	let ltp' = coerce_ref_ltp ra ltp in
	(declare_label l1 ltp') >>
	(bnzl ra l1) >>
	(codegen_inner tctx ctx' e1 tp) >>
	(current_iftp (typetrans tctx tp) >>= (fun ltp'' -> 
	(declare_label l2 ltp'') >>
	(jmpl l2) >>
	(l1 $ ltp') >>
	(ld rt ra 1) >>
	(st ra 1 rs) >>
	(mov rs ra) >>
	(mov ra rt) >>
	(push rs ra) >>
	(codegen_inner tctx (extend (extend ctx' x tp'') y tp') e2 tp) >>
	(drop rs) >>
	(drop rs) >>
	(jmpl l2) >>
	(l2 $ ltp'')))))
    | _ -> impos "copy/free not handled by codegen"
  in 
  let cenv = codegen_outer e tp {cctx=emp;cs=emp;fctx=emp;lctx=emp} in
  (cenv.cs,cenv.cctx,lstart)


