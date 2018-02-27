exception TcFail of string
exception Impos of string
exception NYI

val newline : int -> string
val tcfail : string -> 'a
val impos : string -> 'a
val lookup_or_fail : 'a Ctx.ctx -> Var.var -> 'a
val context_msg : string -> (unit -> 'a) -> 'a
val sep : ('a -> string) -> string -> 'a list -> string
