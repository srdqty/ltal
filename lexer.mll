{
open Parser
let lineno = ref 1
}

let alpha = ['A'-'Z' 'a'-'z']
let digit = ['0'-'9']
let name = (alpha|'_')(alpha|digit|'_')*
let ws = [' ' '\t']

rule lex =
  parse
        '/''/'[^'\n']*'\n' { lineno := !lineno + 1; lex lexbuf }
      | ['\n']     { lineno := !lineno + 1; lex lexbuf }
      | ws+        { lex lexbuf }
      | "/\\"       { TLAM }
      | "["        { LBRACK }
      | "]"        { RBRACK }
      | "."        { DOT }
      | "->"       { ARROW }
      | "+"        { PLUS }
      | "-"        { MINUS }
      | "*"        { TIMES }
      | "<"        { LT }
      | ">"        { GT }
      | ":"        { COLON }
      | "forall"   { FORALL }
      | "fun"      { FUN }
      | "list"     { LIST_T }
      | "int"      { INT_T }
      | "fst"      { FST }
      | "snd"      { SND }
      | "fix"      { FIX }
      | "then"     { THEN }
      | "else"     { ELSE }
      | "in"       { IN }
      | "end"      { END }
      | "|"        { BAR }
      | "[]"      { NIL }
      | "::"     { CONS }
      | "case"     { CASE }
      | "of"       { OF }
      | "="        { EQ }
      | "<>"       { NE }
      | "<="       { LE }
      | ">="       { GE }
(*      | "ref"      { REF }
      | "!"        { BANG }
      | ":="       { ASSIGN }*)
      | "("        { LPAREN }
      | ")"        { RPAREN }
(*      | "left"     { LEFT }
      | "right"    { RIGHT }*)
      | "true"       { TRUE }
      | "false"       { FALSE }
      | "not"      { NOT }
      | "andalso"      { AND }
      | "orelse"       { OR }
      | "if"       { IF }
      | "val"      { VAL }
      | "fn"       { FN }
      | "=>"       { FNARROW }
      | "let"      { LET }
(*      | "seq"      { SEQ }*)
      | ","        { COMMA }
      | name+     { VAR(Lexing.lexeme lexbuf) }
      | '~'?digit+ { INT(int_of_string(Lexing.lexeme lexbuf)) }
      | eof        { EOF }

{
}
