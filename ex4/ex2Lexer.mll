{
  open Ex2Parser
}

let digit = ['0'-'9']
let bool = "true" | "false"
let space = ' ' | '\t' | '\r' | '\n'
let alpha = ['a'-'z' 'A'-'Z' '_']
let ident = alpha (alpha | digit)*

rule token = parse
| space+      { token lexbuf }
| "let"       { LET }
| "rec"       { REC }
| "and"       { AND }
| "in"        { IN }
| "fun"       { FUN }
| "->"        { ARROW }
| "match"     { MATCH }
| "with"      { WITH }
| "end"       { END }
| "if"        { IF }
| "then"      { THEN }
| "else"      { ELSE }
| "="         { EQ }
| '+'         { PLUS }
| '-'         { MINUS }
| '*'         { TIMES }
| '/'         { DIVIDE }
| '<'         { LESS }
| '('         { LPAR }
| ')'         { RPAR }
| ','         { COMMA }
| '['         { LBRA }
| ']'         { RBRA }
| ';'         { SEMIC }
| "::"        { CONS }
| '|'         { VBER }
| '_'         { WILD }
| digit+ as n { INT (int_of_string n) }
| bool as n   { BOOL (bool_of_string n) }
| ident as n  { ID n }
| eof         { EOF }
| ";;"        { EOC }
| _           { failwith ("Unknown Token: " ^ Lexing.lexeme lexbuf)}
