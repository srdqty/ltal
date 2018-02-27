%{
open Absyn
open Op
open Util

let tmp = ref 0
let newtmp() = 
  let i = !tmp in
  tmp := i+1;
  "tmp$"^string_of_int i

type pat = VarPat of string
  | PairPat of pat*pat
  | NilPat
  | ConsPat of pat*pat
  | IntPat of int

type bind = ValBind of pat * aexp
  | FunBind of string * (string*atp) list * atp * aexp

let rec do_app e es = 
  match es with 
    [] -> e
  | e3::es' -> do_app (App (e, e3)) es'

let rec do_pat p e e' = 
  match p with
    VarPat v -> Let(v,e,e')
  | PairPat(p1,p2) -> 
      let x = newtmp() in
      let y = newtmp() in
      LetPair(x,y,e,do_pat p1 (Var x) (do_pat p2 (Var y) e'))

let do_fun f vts tp e e' = 
  let v1,t1 = List.hd vts in
  let ts = List.map snd (List.tl vts) in
  let tp' = List.fold_right (fun t t' -> Arrow(t,t')) ts tp in
  let fe = List.fold_right (fun (v,t) e -> Lam(v,t,e)) (List.tl vts) e in
  Let(f,Fix(f,v1,t1,tp',fe),e')

let rec do_let ves e = 
  match ves with
    [] -> e
  | ValBind(p,e')::ves' -> do_pat p e' (do_let ves' e) 
  | FunBind(f,vts,tp,e')::ves' -> do_fun f vts tp e' (do_let ves' e)

let rec do_lam vts e = 
  match vts with
    [] -> e
  | (v,tp)::vts -> Lam(v,tp,do_lam vts e)

let rec do_list l = 
  match l with [] -> Nil
  | e::es -> Cons(e,do_list es)

let rec do_case e mts = 
  match mts with 
    [p,e'] -> do_pat p e e'
  | [NilPat,e1;ConsPat(p1,p2),e2] 
  | [ConsPat(p1,p2),e2;NilPat,e1] -> 
      let x = newtmp() in
      let y = newtmp() in
      Case(e,e1,x,y,do_pat p1 (Var x) (do_pat p2 (Var y) e2))
  | (IntPat i,e)::mts -> 
      If(NZ,Op(Minus,[e;IntC i]),do_case e mts,e)
%}

%token <int> INT
%token <string> VAR
%token PLUS MINUS TIMES LT GT EQ NE LE GE 
%token LPAREN RPAREN LBRACK RBRACK TLAM DOT VAL
%token /*LEFT RIGHT*/ COMMA COLON FNARROW 
%token FN FUN LET IF THEN ELSE IN BAR
%token FST SND FIX
%token CONS NIL CASE OF END
%token INT_T ARROW LIST_T TIMES_T FORALL FORALL_T
%token AND OR NOT TRUE FALSE
/*%token REF BANG ASSIGN SEQ*/
%token EOF APP EXPR

%type <Absyn.aexp> parse
%type <Absyn.aexp> expr

%nonassoc FORALL_T
%right ARROW
%nonassoc FNARROW
%right CONS
%nonassoc LT GT LE GE EQ NE
%left AND
%left OR
%left PLUS MINUS
%left TIMES

%nonassoc LIST_T

%start parse

%%

parse: aexpr EOF           { $1 }


aexpr : FN vartys FNARROW aexpr  { do_lam (List.rev $2) $4 }
      | IF aexpr THEN aexpr ELSE aexpr { If(NZ,$2,$4,$6) }
      | CASE aexpr OF matches 
	  { do_case $2 $4 }
      | LET binds IN aexpr END 
	  { do_let (List.rev $2) $4 } 
      | bexpr {$1}

bexpr : bexpr expr { App($1,$2) }
      | FST expr { Fst( $2) }
      | SND expr  { Snd( $2) }
      | NOT expr          { If(NZ,$2, IntC 0, IntC 1) }
      | expr { $1 }

     
expr : 
       INT               { IntC $1 }
     | VAR               { Var ($1) }
     | TRUE              { IntC 1 }
     | FALSE             { IntC 0 }
     | expr AND expr     { If(NZ,$1, $3, IntC 0) }
     | expr OR expr      { If(NZ,$1, IntC 1, $3) }
     | expr EQ expr      { If(NZ,Op(Minus,[$1;$3]), IntC 0, IntC 1) }
     | expr NE expr      { If(NZ,Op(Minus,[$1;$3]), IntC 1, IntC 0) }
     | expr LT expr      { If(LZ,Op(Minus,[$1;$3]), IntC 0, IntC 1) }
     | expr GE expr      { If(LZ,Op(Minus,[$1;$3]), IntC 1, IntC 0) }
     | expr GT expr      { If(LZ,Op(Minus,[$3;$1]), IntC 0, IntC 1) }
     | expr LE expr      { If(LZ,Op(Minus,[$3;$1]), IntC 1, IntC 0) }
     | expr PLUS expr  { Op(Plus,[$1;$3]) }
     | expr TIMES expr  { Op(Times,[$1;$3]) }
     | expr MINUS expr  { Op(Minus, [$1; $3]) }
     | expr CONS expr { Cons( $1, $3) }
     | NIL {Nil}  
     | LBRACK comma_es RBRACK { do_list (List.rev $2) }
     | LPAREN aexpr COMMA aexpr RPAREN { Pair($2,$4) }
     | LPAREN aexpr RPAREN {$2}
     ;

matches : pat FNARROW bexpr { [($1,$3)] }
     | matches BAR pat FNARROW bexpr { ($3,$5)::$1 }


comma_es:			{ [] }
	| comma_es COMMA expr		{ $3::$1 }
	;

binds :	bind { [$1] }
	| binds bind	{ $2::$1 }
	;

bind : VAL pat EQ aexpr		{ ValBind($2,$4) }
	| FUN VAR vartys COLON tp EQ aexpr {FunBind($2,List.rev $3,$5, $7) }

pat : VAR { VarPat($1) }
	| LPAREN pat COMMA pat RPAREN {PairPat($2,$4)}
	| NIL { NilPat }
	| pat CONS pat { ConsPat($1,$3) }
	| TRUE { IntPat 1 }
	| FALSE { IntPat 0 }

vartys : LPAREN VAR COLON tp RPAREN  { [($2,$4)] }
	| vartys LPAREN VAR COLON tp RPAREN { ($3,$5)::$1 }
	
tp :      INT_T  {Int}
        | tp TIMES tp {Absyn.Times($1,$3)}
	| tp ARROW tp {Arrow($1,$3)}
	| tp LIST_T {List($1)}
        | FORALL VAR DOT tp %prec FORALL_T {Forall ($2, $4)}
	| VAR {TVar $1}
	| LPAREN tp RPAREN {$2}
        ;
