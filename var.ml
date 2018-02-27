(* var.mli *)
(* Variables: plain strings, and uniquified var's. *)

type var = {name:string;uid:int}

let uniq = ref 0
let mkvar s = let i = !uniq in
               let _ = (uniq := !uniq+1) in
	       {name=s;uid=i}
let mkvar0 () = mkvar "tmp"
let to_string s = s.name ^ "$" ^ (string_of_int s.uid)
let compare v w = w.uid - v.uid
let eq v w = (compare v w) = 0
let rename v = mkvar v.name

module VarMap = Map.Make(struct type t = var let compare = compare end)

type 'a map = 'a VarMap.t
let id = VarMap.empty

let empty = VarMap.empty
let add  = VarMap.add
let find = VarMap.find
let remove = VarMap.remove
let mem = VarMap.mem
let iter = VarMap.iter
let map = VarMap.map
let mapi = VarMap.mapi
let fold = VarMap.fold
let is_empty m = 
  VarMap.fold (fun k v emp -> false) m true
