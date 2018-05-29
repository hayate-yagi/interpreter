%{
  open Syntax
  (* ここに書いたものは，ExampleParser.mliに入らないので注意 *)
%}

%token <int>    INT
%token <string> ID
%token <bool>   BOOL
%token MATCH WITH VBER WILD END
%token FUN ARROW
%token LET IN EQ REC AND
%token IF THEN ELSE
%token PLUS MINUS TIMES DIVIDE LESS
%token LPAR RPAR COMMA
%token LBRA RBRA SEMIC CONS
%token EOF EOC

%right CONS
%start main 
%type <Syntax.command> main
%% 

main:
  | command EOC                   { $1 }
  | command EOF                   { $1 }
;

command:
  | expr                                { CExp($1) }
  | LET var EQ expr                     { CLet($2,$4) }
  | LET REC var var EQ expr             { CRLet($3,$4,$6) }
  | LET REC var var EQ expr AND letrec  { CRALet(($3,$4,$6)::$8) }
;

letrec:
  | var var EQ expr AND letrec  { ($1,$2,$4)::$6 }
  | var var EQ expr             { [($1,$2,$4)] }
    

expr:
  | expr CONS expr                             { ECons($1,$3) }  
  | MATCH expr WITH pmatch END                 { EMatch($2,$4) }
  | LET REC var var EQ expr IN expr            { ERLet($3,$4,$6,$8) }
  | LET REC var var EQ expr AND letrec IN expr { ERALet(($3,$4,$6)::$8,$10) }
  | LET var EQ expr IN expr                    { ELet($2,$4,$6) }
  | IF expr THEN expr ELSE expr                { Eif($2,$4,$6) }
  | FUN var ARROW expr                         { EFun($2,($4)) }
  | bool_expr                                  { $1 } 
;

pmatch:
  | pat ARROW expr VBER pmatch              { ($1,$3)::$5 }
  | pat ARROW expr                          { [($1,$3)] }
;

bool_expr:
  | bool_expr LESS arith_expr     { Ebin(OpLe,$1,$3) }
  | bool_expr EQ arith_expr       { Ebin(OpEq,$1,$3) }
  | arith_expr                    { $1 }
;
      
arith_expr:
  | arith_expr PLUS factor_expr   { Ebin(OpAdd,$1,$3) }
  | arith_expr MINUS factor_expr  { Ebin(OpSub,$1,$3) }
  | factor_expr                   { $1 }
;

factor_expr:
  | factor_expr TIMES app_expr    { Ebin(OpMul,$1,$3) }
  | factor_expr DIVIDE app_expr   { Ebin(OpDiv,$1,$3) }
  | app_expr                      { $1 }
;

app_expr:
  | app_expr atomic_expr          { EApp($1,$2) } 
  | atomic_expr                   { $1 }
;

atomic_expr:
  | INT                           { Evalue (VInt $1) }
  | BOOL                          { Evalue (VBool $1) }
  | ID                            { Evar ($1) }
  | LPAR expr RPAR                { $2 }
  | LPAR expr COMMA expr RPAR     { EPair ($2,$4) }
  | LBRA RBRA                     { ENil }
  | LBRA list RBRA                { $2 }
;

list:
  | expr SEMIC list               { ECons($1,$3) }
  | expr                          { ECons($1,ENil) }
;

pat:
  | value                         { Value($1) }
  | var                           { Name($1) }
  | LPAR p_tuple RPAR             { PTuple $2 }
  | LPAR p_list RPAR              { PList $2 }
  | LBRA RBRA                     { PList [] }
  | WILD                          { PWild }
;

p_tuple:
  | pat COMMA p_tuple             { $1::$3 }
  | pat                           { [$1] }
;

p_list:
  | pat CONS p_list               { $1::$3 }
  | pat                           { [$1] }

value:
  | INT                           { VInt $1 }
  | BOOL                          { VBool $1 }
;

var:
  | ID                            { $1 }
;


 

