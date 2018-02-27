(* var.mli *)
(* Variables: plain strings, and uniquified var's. *)

type var


val mkvar : string -> var
val rename : var -> var
val mkvar0 : unit -> var

val compare : var -> var -> int
val eq : var -> var -> bool

val to_string : var -> string

type 'a map 

val empty : 'a map
val add : var -> 'a -> 'a map -> 'a map
val find : var -> 'a map -> 'a
val remove : var -> 'a map -> 'a map
val is_empty : 'a map -> bool
val mem : var -> 'a map -> bool
val iter : (var -> 'a -> unit) -> 'a map -> unit
val map : ('a -> 'b) -> 'a map -> 'b map
val mapi : (var -> 'a -> 'b) -> 'a map -> 'b map
val fold : (var -> 'a -> 'b -> 'b) -> 'a map -> 'b -> 'b

