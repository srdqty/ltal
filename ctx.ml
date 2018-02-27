
open Var;;
type var = Var.var;;
type 't ctx = (var) list * 't Var.map 

let bound (l,m) v = Var.mem v m

let extend (l,m) v t = ((v)::l, Var.add v t m)
let lookup (l,m) v = 
  Var.find v m


let update (l,m) v t = 
  (l, Var.add v t m)

let rec remove' ctx v = 
  match ctx with
    [] -> []
  | (v')::ctx' -> 
      if Var.eq v v' 
      then ctx' 
      else let ctx'' = remove' ctx' v in (v')::ctx''

let remove (l,m) v = 
  (remove' l v, Var.remove v m)

    
let dom (l,m) = l
let emp = ([],Var.empty)


let pp_ctx f (l,m) = 
  let rec pp ctx = 
    match ctx with
      [] -> ""
    | [v] -> (Var.to_string v)^":"^(f (Var.find v m))
    | v::ctx' -> (pp ctx')^","^(Var.to_string v)^":"^(f (Var.find v m)) 
  in
  "{"^(pp l) ^"}"



let restrict (l,m) vars = 
  let m' = 
    List.fold_right (fun x m' -> Var.add x (Var.find x m) m') vars Var.empty in
  (vars,m')


let map f (l,m) = (l,Var.mapi f m)
let map' f (l,m) = (l, Var.map f m)
let iter f (l,m) = List.iter (fun x -> (f x (Var.find x m))) l
let is_empty (l,m) = l = []
let fold f (l,m) x =  List.fold_right (fun x z -> f x (Var.find x m) z) l x

let from_list l = 
  List.fold_right 
    (fun (x,t) (l,m) -> 
      (x::l, Var.add x t m))
    l ([],Var.empty)

