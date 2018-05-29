type token =
  | INT of (int)
  | ID of (string)
  | BOOL of (bool)
  | MATCH
  | WITH
  | VBER
  | WILD
  | END
  | FUN
  | ARROW
  | LET
  | IN
  | EQ
  | REC
  | AND
  | IF
  | THEN
  | ELSE
  | PLUS
  | MINUS
  | TIMES
  | DIVIDE
  | LESS
  | LPAR
  | RPAR
  | COMMA
  | LBRA
  | RBRA
  | SEMIC
  | CONS
  | EOF
  | EOC

val main :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Syntax.command
