

type cond = NZ | LZ
type op = Plus | Minus | Times

let to_string op = 
  match op with
    Plus -> "+"
  | Times -> "*"
  | Minus -> "-"

let cond_to_string c = 
  match c with NZ -> "nz" | LZ -> "lz"
