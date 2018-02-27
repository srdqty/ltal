open Ctx;;
let rec newline i = 
  if i = 0 then "\n"
  else (newline (i-1))^" "

exception NYI
exception UnifyFail of string
exception TcFail of string
exception Impos of string
let tcfail msg = raise (TcFail msg)
let impos msg = raise (Impos msg)
let lookup_or_fail ctx v = 
  try lookup ctx v
  with Not_found -> tcfail ("Unbound variable " ^ (Var.to_string v))

let context_msg msg f = 
  try f() with TcFail msg' -> tcfail (msg ^ " " ^ msg')

let rec sep f s l = 
  match l with
    [] -> ""
  | [x] -> f x
  | x::xs -> f x ^ s ^ sep f s xs
