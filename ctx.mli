
type var = Var.var
type 't ctx (*= (var*'t) list*)


val bound : 't ctx -> var -> bool
val lookup : 't ctx -> var -> 't
val extend : 't ctx -> var -> 't -> 't ctx
val update : 't ctx -> var -> 't -> 't ctx
val remove : 't ctx -> var -> 't ctx
val dom : 't ctx -> var list
val restrict : 't ctx -> var list -> 't ctx
val from_list : (var * 't) list -> 't ctx
val is_empty : 't ctx -> bool

val emp : 't ctx

val pp_ctx : ('a -> string) -> 'a ctx -> string

val map : (var -> 'a -> 'b) -> 'a ctx -> 'b ctx
val map' : ('a -> 'b) -> 'a ctx -> 'b ctx
val iter : (var -> 'a -> unit) -> 'a ctx -> unit
val fold : (var -> 'a -> 'b -> 'b) -> 'a ctx -> 'b -> 'b
