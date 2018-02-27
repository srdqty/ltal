open Ctx;;
open Ltal;;
open Ltalsubst;;
open Util;;
open Op;;

let debug msg = (*print_string msg;*) ();;


(* Slightly tricky in order to prevent negative occurrences of recursively
 * bound variables *)

let flatten rtp = 
  match rtp with 
    DTp dtp -> rtp
  | rtp -> toptp

let force_word_sign_pos sk = 
  match sk with
    Neg,_ -> tcfail "recursively bound variable occurs in a negative position"
  | _,M -> tcfail "memory kinded variable used as word type"
  | _ -> ()

let force_mem sk = 
  match sk with
    _,W -> tcfail "memory kinded variable used as word type"
  | _ -> ()

let sign_flip (s,k) = 
  (match s with
    Pos -> Neg
  | Neg -> Pos
  | QForall -> QForall
  | QExists -> QExists),k

let tctx_sign_flip tctx = 
    Ctx.map' sign_flip tctx

let rec compress tctx wtp = 
  match wtp with
    Exists(tv,k,wtp') -> 
(*      print_string ("forcing existential "^(Var.to_string tv)^"\n")*)
      compress (extend tctx tv (QExists,k)) wtp'
  | Mu(tv,wtp) -> compress tctx (subst1w_wtp tv (Mu(tv,wtp)) wtp)
  | wtp -> tctx,wtp

let rec force_word dtp = 
  match dtp with
    Word -> ()
  | Zero -> ()
  | _ -> tcfail ("expected type word instead of "^(pp_dtp dtp))

let force_pair mtp = 
  match mtp with 
    Tensor(t1,Tensor(t2,One)) -> t1,t2
  | _ -> tcfail ("expected pair instead of "^(pp_mtp mtp))

let mkpair (t1, t2) = 
  Tensor(t1,Tensor(t2,One))

let rec fetch_nth' mtp n = 
  if n < 0 then tcfail "Negative offsets are not allowed"
  else
    match mtp,n with
      Tensor(wtp,mtp),0 -> wtp, Tensor(flatten wtp,mtp)
    | Tensor(wtp,mtp), n -> 
	let wtp',mtp = fetch_nth' mtp (n-1) in
	wtp', Tensor(wtp,mtp)
    | One,_ -> tcfail ("Offset "^(string_of_int n)^" out of range")
    | MTVar _, _ -> tcfail ("Cannot read from an abstract memory location")

let fetch_nth wtp n = 
  match wtp with 
    Ref(mtp) -> 
      let wtp, mtp = fetch_nth' mtp n in
      wtp, Ref(mtp)
  | Stack(mtp) -> 
      let wtp, mtp = fetch_nth' mtp n in
      wtp, Stack(mtp)
  | _ -> tcfail ("Expected writable reference type, not "^pp_wtp wtp)

let rec put_flat_nth' mtp n wtp = 
  if n < 0 then tcfail "Illegal negative offset"
  else
    match mtp,n with
      Tensor(DTp _ ,mtp),0 -> 
	Tensor(wtp,mtp)
    | Tensor(wtp', mtp),0 -> 
	tcfail ("expected a disposable type, not "^(pp_wtp wtp'))
    | Tensor(wtp',mtp), n -> 
	Tensor(wtp', put_flat_nth' mtp (n-1) wtp)
    | One,_ -> tcfail ("Offset "^(string_of_int n)^" out of range")
    | MTVar _, _ -> tcfail ("Cannot write to an abstract memory location")
	
let put_flat_nth wtp n wtp' =
  match wtp with 
    Ref(mtp) -> 
      Ref(put_flat_nth' mtp n wtp')
  | Stack(mtp) -> 
      Stack(put_flat_nth' mtp n wtp')
  | _ -> tcfail ("Expected writable reference type, not "^pp_wtp wtp)

let rec force_codetp t = 
  match t with 
    Code rctx -> (emp, rctx)
  | Forall (tv,k,t') -> 
      let (tctx, rctx) = force_codetp t' in
      (extend tctx tv (QForall,k), rctx)
  | _ -> tcfail "expected operand to have code type"

let force_dtp tctx wtp = 
  match compress tctx wtp with
    tctx',DTp dtp -> tctx',dtp
  | _ -> tcfail ("expected a disposable type instead of "^(pp_wtp wtp))

let rec force_dctx rctx = 
  Ctx.iter (fun r t -> 
    (context_msg ("in the type of register "^(Var.to_string r)) 
       (fun () -> let _ = force_dtp Ctx.emp t in ()))) rctx

      
      
let force_ref tctx wtp = 
  match compress tctx wtp with
    tctx',Ref mtp -> tctx',Ref mtp
  | tctx',Stack mtp -> tctx',Stack mtp
  | _,wtp -> tcfail ("expected a reference type instead of "^(pp_wtp wtp))

let force_stack tctx wtp = 
  match compress tctx wtp with
    tctx',Stack mtp -> tctx',mtp
  | _,wtp -> tcfail ("expected a stack type instead of "^(pp_wtp wtp))

let rec push_top mtp i = 
  if i = 0 then mtp 
  else Tensor(toptp, push_top mtp (i-1))
  

let rec pop_top mtp i = 
  match mtp,i with
    mtp, 0 -> mtp
  | Tensor(DTp _, mtp), i -> pop_top mtp (i-1)
  | _ -> tcfail ("popped past the top of the stack")
  

  
let rec wf_dtp tctx dtp = 
  match dtp with
    Word -> ()
  | Code rctx -> wf_rctx (tctx_sign_flip tctx) rctx
  | Forall (tv,k,t) -> wf_dtp (extend tctx tv (QForall,k)) t
  | Zero -> ()
  | Top -> ()

and wf_codetp tctx codetp = 
   match codetp with
    Code rctx -> wf_rctx (tctx_sign_flip tctx) rctx
  | Forall (tv,k,t) -> wf_codetp (extend tctx tv (QForall,k)) t
  | _ -> tcfail "only code types are allowed in code context"

and wf_wtp tctx wtp = 
  match wtp with 
    TVar v -> 
      force_word_sign_pos (lookup_or_fail tctx v)
  | DTp dtp -> wf_dtp tctx dtp
  | NRef mtp -> wf_mtp tctx mtp
  | Ref mtp -> wf_mtp tctx mtp
  | Stack mtp -> wf_mtp tctx mtp
  | Exists (tv,k,wtp) -> wf_wtp (extend tctx tv (QExists,k)) wtp
  | Mu (tv,TVar(tv')) -> if Var.eq tv tv' then tcfail "ill-founded recursive type " else wf_wtp tctx (TVar tv')
  | Mu (tv,wtp) -> wf_wtp (extend tctx tv (Pos,W)) wtp

and wf_mtp tctx mtp = 
  match mtp with
    One -> ()
  | Tensor (w,m) -> wf_wtp tctx w; wf_mtp tctx m
  | MTVar tv -> force_mem (lookup_or_fail tctx tv)

and wf_rctx tctx rctx = 
  Ctx.iter (fun _ t -> wf_wtp tctx t) rctx

(* Allows useless types like forall a . word *)

let wf_cctx cctx = 
  Ctx.iter (fun f ct -> 
    try wf_codetp emp ct 
    with TcFail msg -> 
      tcfail ("in type of code label "^(Var.to_string f)^", "^msg)) cctx
    

let pp_sign s = 
  match s with
    QExists -> "E"
  | QForall -> "A"
  | Pos -> "+"
  | Neg -> "-"

  let pp_sk (s,k) = pp_sign s ^ pp_kind k;;

let lookup_qctx ctx v = 
  let rec lookup' d = 
    match d with
      [] -> tcfail ("variable "^(Var.to_string v)^" is unbound in context "^(Ctx.pp_ctx pp_sk ctx))
    | v'::d' -> 
	if Var.eq v v' 
	then d'
	else lookup' d'
  in let d = lookup' (Ctx.dom ctx) in 
  lookup ctx v,restrict ctx d


let rec unpack_rctx tctx rctx = 
  debug "unpack_rctx\n";
  Ctx.fold 
    (fun r t (tctx,rctx) -> 
      let tctx',t' = unpack_wtp tctx t in
      tctx', Ctx.update rctx r t') rctx (tctx,rctx)


and unpack_wtp tctx wtp = 
  match wtp with 
    Exists (tv,k,wtp) ->
      let tv' = Var.rename tv in
      debug("Got E- "^(Var.to_string tv)^" -> "^(Var.to_string tv')^"\n");
      (extend tctx tv' (QForall,k)),(subst1w_wtp tv (TVar tv') wtp)
  | Ref(mtp) -> 
      let tctx,mtp = unpack_mtp tctx mtp in
      tctx,Ref(mtp)
  | NRef(mtp) -> 
      let tctx,mtp = unpack_mtp tctx mtp in
      tctx,Ref(mtp)
  | Stack(mtp) -> 
      let tctx,mtp = unpack_mtp tctx mtp in
      tctx,Stack(mtp)
  | DTp dtp -> 
      let tctx,dtp = unpack_dtp tctx dtp in
      tctx,DTp(dtp)
  | Mu (tv,wtp) -> tctx, Mu(tv,wtp) 
  | TVar tv -> tctx,TVar tv

and unpack_dtp tctx dtp = 
  match dtp with
    Word -> tctx, Word
  | Code rctx -> 
      let tctx,rctx = generalize_rctx tctx rctx in
      tctx,Code(rctx)
  | Forall (tv,k,wtp) -> tctx, Forall(tv,k,wtp)
  | Zero -> tctx, Zero
  | Top -> tctx,Top

and unpack_mtp tctx mtp = 
  match mtp with
    One -> tctx, One
  | Tensor(wtp,mtp) -> 
    let tctx,wtp = unpack_wtp tctx wtp in
    let tctx,mtp = unpack_mtp tctx mtp in
    tctx,Tensor(wtp,mtp) 
  | MTVar tv -> tctx, MTVar tv

and generalize_rctx tctx rctx = 
  debug "gen_rctx\n";
  Ctx.fold 
    (fun r t (tctx,rctx) -> 
      let tctx',t' = generalize_wtp tctx t in
      tctx', Ctx.update rctx r t') rctx (tctx,rctx)

and generalize_wtp tctx wtp = 
  match wtp with 
    Exists(tv,k,wtp) -> tctx, Exists(tv,k,wtp)
  | Ref(mtp) -> 
      let tctx,mtp = generalize_mtp tctx mtp in
      tctx,Ref(mtp)
  | NRef(mtp) -> 
      let tctx,mtp = generalize_mtp tctx mtp in
      tctx,Ref(mtp)
  | Stack(mtp) -> 
      let tctx,mtp = generalize_mtp tctx mtp in
      tctx,Stack(mtp)
  | DTp dtp -> 
      let tctx,dtp = generalize_dtp tctx dtp in
      tctx,DTp(dtp)
  | Mu (tv,wtp) -> tctx, Mu(tv,wtp) 
  | TVar tv -> tctx,TVar tv

and generalize_dtp tctx dtp = 
  match dtp with
    Word -> tctx, Word
  | Code rctx -> 
      let tctx,rctx = unpack_rctx tctx rctx in
      tctx,Code(rctx)
  | Forall (tv,k,dtp) ->
      let tv' = Var.rename tv in
      debug("Got A+ "^(Var.to_string tv)^" -> "^(Var.to_string tv')^"\n");
      (extend tctx tv' (QForall,k)),(subst1w_dtp tv (TVar tv') dtp)
  | Zero -> tctx, Zero
  | Top -> tctx, Top

and generalize_mtp tctx mtp = 
  match mtp with
    One -> tctx, One
  | Tensor(wtp,mtp) -> 
    let tctx,wtp = generalize_wtp tctx wtp in
    let tctx,mtp = generalize_mtp tctx mtp in
    tctx,Tensor(wtp,mtp) 
  | MTVar tv -> tctx, MTVar tv
 

let rec unify_dtp tctx t1 t2 l = 
  debug "unify dtp\n";
  match t1,t2 with
    _, Top -> unify l (* top subsumes everything *)
  | Word, Word -> unify l
  | Zero, Word -> unify l
  | Zero, Zero -> unify l
  
	(* NOTE: It is *important* that these cases are in this order.
	   Otherwise we will get spurious variable escape errors because
	   we chose things too early! *)
  | (t1, Forall (tv,W,t2)) -> 
      let tv' = Var.rename tv in 
      debug("Unpacked A+ "^(Var.to_string tv)^" -> "^(Var.to_string tv')^"\n");
      unify_dtp (extend tctx tv' (QForall,W)) t1 (subst1w_dtp tv (TVar tv') t2) l
 | (t1, Forall (tv,M,t2)) -> 
      let tv' = Var.rename tv in 
      debug("Unpacked A+ "^(Var.to_string tv)^" -> "^(Var.to_string tv')^"\n");
      unify_dtp (extend tctx tv' (QForall,M)) t1 (subst1m_dtp tv (MTVar tv') t2) l
  | (Forall (tv,W,t1), t2) -> 
      let tv' = Var.rename tv in 
      debug("Unpacked A- "^(Var.to_string tv)^" -> "^(Var.to_string tv')^"\n");
      unify_dtp (extend tctx tv' (QExists,W)) (subst1w_dtp tv (TVar tv') t1) t2 l
  | (Forall (tv,M,t1), t2) -> 
      let tv' = Var.rename tv in 
      debug("Unpacked A- "^(Var.to_string tv)^" -> "^(Var.to_string tv')^"\n");
      unify_dtp (extend tctx tv' (QExists,M)) (subst1m_dtp tv (MTVar tv') t1) t2 l
	(* contravariant *)
  | (Code rctx, Code rctx') -> 
      unify_rctx tctx rctx' rctx l
  | (t1,t2) -> tcfail ("types "^(pp_dtp t1)^"\nand   "^(pp_dtp t2)^" are incompatible")



and unify_wtp tctx t1 t2 l = 
  debug ("unify wtp\n");(*^(pp_wtp t1)^"\nand\n"^(pp_wtp t2)^"\nin quantifier context "^(pp_ctx pp_sk tctx)^"\n");*)
  let incompatible() = 
    tcfail ("types "^(pp_wtp t1)
	    ^"\nand   "^(pp_wtp t2)
	    ^"\nare incompatible\ngiven quantifier context "^(pp_ctx pp_sk tctx)) in
  let substitute tv tctx' t = 
    (try wf_wtp tctx' t;
    with TcFail msg -> 
      tcfail ("type "^(pp_wtp t)
	      ^"\nis not a valid substitution for "
	      ^(Var.to_string tv)
	      ^" because a quantified variable escapes scope: "^msg 
	      ^" in tctx "^(pp_ctx pp_sk tctx)^"\n"));
    let sub = subst1w_wtp tv t in
    let l' = List.map (fun (q,x,y) -> 
      if Ctx.bound q tv then q, sub x, sub y
      else q,x,y) l in
    unify l' in
  match t1,t2 with 
    TVar tv, TVar tv' -> 
      if Var.eq tv tv' then unify l 
      else 
	(match lookup_qctx tctx tv, lookup_qctx tctx tv' with
	  ((QExists,W), tctx1),((QExists,W),tctx2) -> 
	    (* figure out which one can be substituted for the other *)
	    if List.length (Ctx.dom tctx1) > List.length (Ctx.dom tctx2) 
	    then substitute tv tctx1 (TVar tv') 
	    else substitute tv' tctx2 (TVar tv)
	| ((QExists,W), tctx1),_ -> 
	    substitute tv tctx1 (TVar tv')
	| _,((QExists,W), tctx2) -> 
	    substitute tv' tctx2 (TVar tv)
	| _,_ -> (* not equal so incompatible *)
	    incompatible())
	
  | TVar tv, _ -> 
      (match lookup_qctx tctx tv with
	(QExists,W), tctx' -> 
	  substitute tv tctx' t2
      | _ -> incompatible())

  | _, TVar tv' -> 
      (match lookup_qctx tctx tv' with
	(QExists,W), tctx' -> 
	  substitute tv' tctx' t1
      | _ -> incompatible())

  | DTp dtp, DTp dtp' -> unify_dtp tctx dtp dtp' l

	(* NOTE: It is *important* that the exists cases are in this order.
	   Otherwise we will get spurious variable escape errors because
	   we chose things too early! *)
  | Exists (tv,M,t), t' -> 
      let tv' = Var.rename tv in 
      debug("Unpacked E- "^(Var.to_string tv)^" -> "^(Var.to_string tv')^"\n");
      unify_wtp (extend tctx tv' (QForall,M)) (subst1m_wtp tv (MTVar tv') t) t' l
  | Exists (tv,W,t), t' -> 
      let tv' = Var.rename tv in 
      debug("Unpacked E- "^(Var.to_string tv)^" -> "^(Var.to_string tv')^"\n");
      unify_wtp (extend tctx tv' (QForall,W)) (subst1w_wtp tv (TVar tv') t) t' l
  | t, Exists (tv,M,t') -> 
      let tv' = Var.rename tv in 
      debug("Unpacked E+ "^(Var.to_string tv)^" -> "^(Var.to_string tv')^"\n");
      unify_wtp (extend tctx tv' (QExists,M)) t (subst1m_wtp tv (MTVar tv') t') l

  | t, Exists (tv,W,t') -> 
      let tv' = Var.rename tv in 
      debug("Unpacked E+ "^(Var.to_string tv)^" -> "^(Var.to_string tv')^"\n");
      unify_wtp (extend tctx tv' (QExists,W)) t (subst1w_wtp tv (TVar tv') t') l

  | Mu (tv,t), Mu(tv',t') -> 
      let tv'' = Var.rename tv in 
      unify_wtp (extend tctx tv' (QForall,W)) (subst1w_wtp tv (TVar tv'') t) (subst1w_wtp tv' (TVar tv'') t') l

        (* Mu on the left can be unrolled, but not on the right *)
  | t, Mu(tv,t') -> 
      unify_wtp tctx t (subst1w_wtp tv (Mu (tv,t')) t') l

  | Stack(mtp), Stack(mtp') -> 
      unify_mtp tctx mtp mtp' l

  | Ref(mtp), Ref(mtp') -> 
      unify_mtp tctx mtp mtp' l

  | NRef(mtp), NRef(mtp') -> 
      unify_mtp tctx mtp mtp' l

(* Can coerce refs to nullable refs *)
  | Ref(mtp), NRef(mtp') -> 
      unify_mtp tctx mtp mtp' l

(* Can coerce zero to (wellformed) nullable ref *)
  | DTp Zero, NRef(mtp') -> 
      wf_mtp tctx mtp';
      unify l


  | _,_ -> incompatible()
	
(* Associate all the things in both rctx1 and rctx2.  
   Error if something in r1 not in r2 also.
   Unify the resulting list of inequations. 
 *)

and unify_mtp tctx t1 t2 l =
  debug "unify mtp\n";
  debug ("unify wtp\n");(*^(pp_wtp t1)^"\nand\n"^(pp_wtp t2)^"\nin quantifier context "^(pp_ctx pp_sk tctx)^"\n");*)
  let incompatible() = 
    tcfail ("types "^(pp_mtp t1)
	    ^"\nand   "^(pp_mtp t2)
	    ^"\nare incompatible\ngiven quantifier context "^(pp_ctx pp_sk tctx)) in
  let substitute tv tctx' t = 
    (try wf_mtp tctx' t;
    with TcFail msg -> 
      tcfail ("type "^(pp_mtp t)
	      ^"\nis not a valid substitution for "
	      ^(Var.to_string tv)
	      ^" because a quantified variable escapes scope: "^msg 
	      ^" in tctx "^(pp_ctx pp_sk tctx)^"\n"));
    let sub = subst1m_wtp tv t in
    let l' = List.map (fun (q,x,y) -> 
      if Ctx.bound q tv then q, sub x, sub y
      else q,x,y) l in
    unify l' in
  match t1,t2 with
    One, One -> unify l
  | Tensor(w1,w2),Tensor(w1',w2') -> 
      unify_mtp tctx w2 w2' ((tctx,w1,w1')::l)
  | MTVar tv, MTVar tv' -> 
      if Var.eq tv tv' then unify l 
      else 
	(match lookup_qctx tctx tv, lookup_qctx tctx tv' with
	  ((QExists,M), tctx1),((QExists,M),tctx2) -> 
	    (* figure out which one can be substituted for the other *)
	    if List.length (Ctx.dom tctx1) > List.length (Ctx.dom tctx2) 
	    then substitute tv tctx1 (MTVar tv') 
	    else substitute tv' tctx2 (MTVar tv)
	| ((QExists,M), tctx1),_ -> 
	    substitute tv tctx1 (MTVar tv')
	| _,((QExists,M), tctx2) -> 
	    substitute tv' tctx2 (MTVar tv)
	| _,_ -> (* not equal so incompatible *)
	    incompatible())
	
  | MTVar tv, _ -> 
      (match lookup_qctx tctx tv with
	(QExists,M), tctx' -> 
	  substitute tv tctx' t2
      | _ -> incompatible())

  | _, MTVar tv' -> 
      (match lookup_qctx tctx tv' with
	(QExists,M), tctx' -> 
	  substitute tv' tctx' t1
      | _ -> incompatible())
  | _ -> incompatible()

and unify_rctx tctx rctx1 rctx2 l =
  debug "unify rctx\n";
  let rec merge c1 c2 = 
    match c1 with
      [] -> [],c2
    | r::c1' -> 
	let t2 = lookup_or_fail c2 r in
	let (b,c2') = merge c1' (remove c2 r) in
	((tctx,(lookup rctx1 r),t2)::b,c2')
  in 
  let rboth, ronly2 = merge (Ctx.dom rctx1) (rctx2) in
  force_dctx ronly2; 
  unify (List.append rboth l) 
  (*with TcFail msg -> tcfail(("while checking that context\n"^(pp_rctx rctx1)^"\nis an instance of \n"^(pp_rctx rctx2)^",\n"^msg))*)

and unify l =  
  match l with 
    [] -> ()
  | (qctx,t,u)::l -> unify_wtp qctx t u l 

let hplookup_or_fail h l = 
  try Var.find l h 
  with Not_found -> tcfail ("unbound heap label "^(Var.to_string l));;
      
let rec tc_value cctx h v wtp = 
  match v,wtp with 
    v, DTp Top -> h
  | IntV 0, DTp Zero -> h
  | CLab f, DTp tp -> unify_dtp Ctx.emp tp (lookup_or_fail cctx f) [];  h
  | Lab l, Ref mtp -> 
      let hv = hplookup_or_fail h l in
      let h' = Var.remove l h in 
      tc_heap_value cctx h' hv mtp
  | IntV 0, NRef _ -> h
  | Lab l, NRef mtp -> 
      let hv = hplookup_or_fail h l in
      let h' = Var.remove l h in 
      tc_heap_value cctx h' hv mtp
  | v, Mu(tv,t) -> tc_value cctx h v (subst1w_wtp tv (Mu(tv,t)) t)
  | _ -> tcfail ("value "^(pp_value v)^" does not have word type "^(pp_wtp wtp))




and tc_heap_value cctx h hv mtp = 
  match hv, mtp with
    [], One -> h
  | v::vs, Tensor(wtp,mtp) -> 
      let h' = tc_value cctx h v wtp in
      tc_heap_value cctx h' vs mtp
  | _,_ -> tcfail ("value "^(pp_heap_value hv)^" does not have memory type "^pp_mtp mtp)


and tc_register_file cctx h rf rctx = 
  let (h',rf') = 
    Ctx.fold (fun r wtp (h,rf) ->
      let v = lookup_or_fail rf r in
      (tc_value cctx h v wtp,remove rf r))
      rctx (h,rf) in
  if Var.is_empty h' 
  then tcfail "orphaned memory cells in heap"
  else 
    if Ctx.is_empty rf'
    then tcfail "register file contains untyped registers"
    else ()

let rec ti_operand_dtp cctx tctx rctx op = 
  context_msg ("in operand "^(pp_operand op))
    ( fun () -> match op with
      RegOp r -> force_dtp tctx (lookup_or_fail rctx r)
    | IntOp 0 -> tctx,Zero
    | IntOp i -> tctx,Word
    | CLabOp f -> tctx,lookup_or_fail cctx f)

and ti_operand cctx tctx rctx op = 
  context_msg ("in operand "^(pp_operand op))
    ( fun () -> 
      match op with 
	RegOp r -> 
	  let rtp = lookup_or_fail rctx r
	  in (rtp, update rctx r (flatten rtp))
      | IntOp 0 -> (DTp Zero, rctx)
      | IntOp i -> (DTp Word, rctx)
      | CLabOp f -> (DTp (lookup_or_fail cctx f), rctx))

and ti_jump_target cctx tctx rctx op = 
  context_msg ("in operand "^(pp_operand op))
    ( fun () -> match op with 
      RegOp r -> 
	let tctx,rtp = force_dtp tctx (lookup_or_fail rctx r)
	in (rtp, tctx,update rctx r toptp)
  | IntOp i -> tcfail "invalid jump target"
  | CLabOp f -> (lookup_or_fail cctx f, tctx,rctx))


and tc_jump_target cctx tctx rctx op = 
  let tctx,dtp = ti_operand_dtp cctx tctx rctx op in
  let dtp = Ltalsubst.rename_dtp dtp in
  let rctx = Ltalsubst.rename_rctx rctx in
  context_msg( ("while checking code target \n"^(Ltal.pp_dtp dtp)^"\nmatches\n"^(Ltal.pp_rctx rctx)^"\n,"))
  (fun () -> 
    try unify_dtp tctx dtp (Code rctx) [];
      tctx
    with TcFail msg  -> 
      let tctx,rctx = unpack_rctx tctx rctx in
      unify_dtp tctx dtp (Code rctx) [];
      tctx)
	

and tc_instruction cctx tctx rctx inst = 
  debug("typechecking instruction "^(pp_instruction inst)^"\n");
  context_msg ("in instruction "^(pp_instruction inst)^",")
    (fun ( )-> let tc_arith_inst cctx tctx rctx r s op = 
      let tctx,_ = force_dtp tctx (lookup_or_fail rctx r) in
      let tctx,dtp = force_dtp tctx (lookup_or_fail rctx s) in
      force_word dtp;
      let tctx,dtp' = ti_operand_dtp cctx tctx rctx op in
      force_word dtp';
      tctx,update rctx r (DTp Word) in
    match inst with
      ADD(r,s,op) -> tc_arith_inst cctx tctx rctx r s op
    | BC(LZ,r,op) -> 
	(match compress tctx (lookup_or_fail rctx r) with
	  tctx,DTp Word -> 
	    let tctx = tc_jump_target cctx tctx rctx op in
	    tctx, rctx
	| tctx,DTp Zero -> 
	    let tctx = tc_jump_target cctx tctx rctx op in
	    tctx, rctx
	| tctx,wtp -> tcfail ("expected word type instead of "^(pp_wtp wtp)^" as argument to blz"))
    | BC(NZ,r,op) -> 
	(match compress tctx (lookup_or_fail rctx r) with
	  tctx,DTp Word -> 
	    let tctx = tc_jump_target cctx tctx rctx op in
	    tctx, rctx
	| tctx,DTp Zero -> 
	    let tctx = tc_jump_target cctx tctx rctx op in
	    tctx, rctx
	| tctx,NRef(mtp) -> 
	    let rctx1 = update rctx r (DTp Word) in
	    let rctx2 = update rctx r (Ref mtp) in
	    let tctx = tc_jump_target cctx tctx rctx2 op in
	    tctx,rctx1
	| tctx,Ref(mtp) -> 
	    let rctx1 = update rctx r (DTp Word) in
	    let rctx2 = update rctx r (Ref mtp) in
	    let tctx = tc_jump_target cctx tctx rctx2 op in
	    tctx,rctx1
	| tctx,wtp -> tcfail ("expected word or ref type instead of "^(pp_wtp wtp)^" as argument to bnz"))
    | LD(r,s,i) -> 
	let tctx,_ = force_dtp tctx (lookup_or_fail rctx r) in
	let tctx,wtp = force_ref tctx (lookup_or_fail rctx s) in
	let wti, wtp = fetch_nth wtp i in
	(tctx,update (update rctx r wti) s wtp)
    | MOV(r,op) -> 
	let tctx,_ = force_dtp tctx (lookup_or_fail rctx r) in
	let (wtp,rctx') = ti_operand cctx tctx rctx op in
	tctx,update rctx' r wtp
    | MUL(r,s,op) -> tc_arith_inst cctx tctx rctx r s op
    | ST(r,i,s) -> 
	let tctx,wtp = force_ref tctx (lookup_or_fail rctx r) in
	let wti' = lookup_or_fail (remove rctx r) s in
	let wtp = put_flat_nth wtp i wti' in
	(tctx,update (update rctx r  wtp) s (flatten wti'))
    | SUB(r,s,op) -> tc_arith_inst cctx tctx rctx r s op
    | COMMENT msg -> (tctx,rctx)
    | PUSH(r,s,i) -> 
	if i < 0 then tcfail "can't push negative offset"
	else 
	let tctx,mtp = force_stack tctx (lookup_or_fail rctx r) in
	let mtp' = push_top mtp i in
	tctx, update (update rctx r toptp) s (Stack mtp')
    | POP (r,s,i) -> 
	if i < 0 then tcfail "can't pop negative offset"
	else 
	let tctx,mtp = force_stack tctx (lookup_or_fail rctx r) in
	let mtp' = pop_top mtp i in
	tctx, update (update rctx r toptp) s (Stack mtp')
    )
  

and tc_block cctx tctx rctx block = 
  match block with
    (inst::insts,ei) -> 
      let tctx',rctx' = tc_instruction cctx tctx rctx inst in
      tc_block cctx tctx' rctx' (insts,ei)
  | [], HALT -> ()
  | [], FAIL msg -> ()
  | [], JMP op -> 
   debug("typechecking instruction "^(pp_block block)^"\n");
    context_msg ("in instruction "^(pp_block block)^",")
	(fun () -> 
	  let _ = tc_jump_target cctx tctx rctx op in
	  ())
	
(* Allows extra code blocks that don't appear in signature, but we can never 
 * call them. *)


let tc_code_section cs cctx = 
  Ctx.iter 
    (fun f ct -> 
      debug ("checking block "^(Var.to_string f)^"\n");
      let block = lookup_or_fail cs f in
      (context_msg ("Block "^(Var.to_string f)^" with type "^(pp_dtp ct)^" and body \n"^(pp_block block)^"\nis ill-formed because")
	 (fun () -> 
	   let tctx, rctx = force_codetp ct in
	   tc_block cctx tctx rctx block));
      debug ("Block "^(Var.to_string f)^" is well-formed\n"))
    cctx
	  
  
    
