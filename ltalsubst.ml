open Ltal;;

type 'a subst = 'a Var.map
let id = Var.empty

let bind s v t = Var.add v t s
let rec fetch s v = try Some(Var.find v s)
    with Not_found -> None
let rec unbind s v = Var.remove v s

let rec subst_dtp s t dtp = 
  match dtp with
    Forall (tv,k,dtp) -> Forall(tv,k,subst_dtp (unbind s tv) (unbind t tv) dtp)
  | Word -> Word
  | Code(rctx) -> Code(subst_rctx s t rctx)
  | Zero -> Zero
  | Top -> Top

and subst_wtp s t wtp = 
  match wtp with
    DTp dtp -> DTp(subst_dtp s t dtp)
  | TVar v -> 
      (match fetch s v with
	Some tp' -> tp'
      | None -> wtp)
  | NRef mtp -> NRef(subst_mtp s t mtp  )
  | Ref mtp -> Ref(subst_mtp s t mtp)
  | Stack mtp -> Stack(subst_mtp s t mtp)
  | Exists (tv,k,wtp) -> Exists(tv,k,subst_wtp (unbind s tv) (unbind t tv) wtp)
  | Mu (tv,wtp) -> Mu(tv,subst_wtp (unbind s tv) (unbind t tv) wtp)

and subst_mtp s t mtp = 
  match mtp with
    One -> One
  | Tensor (wtp,mtp) -> Tensor (subst_wtp s t wtp, subst_mtp s t mtp)
  | MTVar v -> 
      (match fetch t v with
	Some tp' -> tp'
      | None -> mtp)

and subst_rctx s t rctx = 
  Ctx.map (fun r u -> (subst_wtp s t u)) rctx

let subst1w_dtp v t t' = subst_dtp (bind id v t) id t'
let subst1w_wtp v t t' = subst_wtp (bind id v t) id t'
let subst1w_mtp v t t' = subst_mtp (bind id v t) id t'
let subst1w_rctx v t rctx = subst_rctx (bind id v t) id rctx
let subst1m_dtp v t t' = subst_dtp id (bind id v t) t'
let subst1m_wtp v t t' = subst_wtp id (bind id v t) t'
let subst1m_mtp v t t' = subst_mtp id (bind id v t) t'
let subst1m_rctx v t rctx = subst_rctx id (bind id v t) rctx


let rec rename_dtp' ctx dtp = 
  match dtp with 
    Word -> Word
  | Code rctx -> Code (rename_rctx' ctx rctx)
  | Forall(tv,k,dtp) -> 
      let tv' = Var.rename tv in
      Forall(tv', k,rename_dtp' (Ctx.extend ctx tv tv') dtp)
  | Zero -> Zero
  | Top -> Top
      
and rename_wtp' ctx wtp = 
  match wtp with 
    DTp dtp -> DTp (rename_dtp' ctx dtp)
  | TVar tv -> if Ctx.bound ctx tv then TVar(Ctx.lookup ctx tv) else TVar(tv)
  | Exists(tv,k,wtp) -> 
      let tv' = Var.rename tv in
      Exists(tv', k,rename_wtp' (Ctx.extend ctx tv tv') wtp)
  | Mu(tv,wtp) -> 
      let tv' = Var.rename tv in
      Mu(tv', rename_wtp' (Ctx.extend ctx tv tv') wtp)
  | Ref(mtp) -> Ref(rename_mtp' ctx mtp)
  | Stack(mtp) -> Ref(rename_mtp' ctx mtp)
  | NRef(mtp) -> NRef(rename_mtp' ctx mtp)

and rename_mtp' ctx mtp = 
  match mtp with
    One -> One
  | Tensor (wtp,mtp) -> Tensor (rename_wtp' ctx wtp, rename_mtp' ctx mtp)
  | MTVar tv -> if Ctx.bound ctx tv then MTVar(Ctx.lookup ctx tv) else MTVar(tv)

and rename_rctx' ctx rctx = 
  Ctx.map (fun r t -> rename_wtp' ctx t) rctx


let rename_dtp t = rename_dtp' Ctx.emp t
let rename_wtp t = rename_wtp' Ctx.emp t
let rename_mtp t = rename_mtp' Ctx.emp t
let rename_rctx rctx = rename_rctx' Ctx.emp rctx
