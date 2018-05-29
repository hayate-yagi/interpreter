open Syntax
open Ex2Parser
open Ex2Lexer

let interactive env f =
  try
    (* let channel = open_in Sys.argv.(1) in *)
    print_string "$ "; flush stdout;
    let lexbuf = Lexing.from_channel stdin in 
    let result = Ex2Parser.main Ex2Lexer.token lexbuf in
    let print_command (env,value) =
      print_string "= ";print_value value; print_newline(); f env in
    print_command (command env result)
    
    (* close_in channel *)
      
  with
    (* | Failure s -> *)
    (*    print_endline "Failure!"; f env; *)
    | Parsing.Parse_error -> 
       print_endline "Parse Error!"; f env;
    | Eval_error ->
       print_endline "Eval Error!"; f env;
    | Not_found ->
       print_endline "Unbound value!"; f env;
    | Division_by_zero ->
       print_endline "Division_by_zero!"; f env;
    | Match_failure ->
       print_endline "Match Failure!"; f env;
      
;;

let readfile env =
  try
    let channel = open_in Sys.argv.(1) in  
    
    let lexbuf = Lexing.from_channel channel in 
    let result = Ex2Parser.main Ex2Lexer.token lexbuf in
    let print_command (env,value) =
      print_value value; print_newline(); in
    print_command (command env result);
    
    close_in channel
      
  with 
    | Parsing.Parse_error -> 
       print_endline "Parse Error!"
;;

let rec read_print_loop env =
  interactive env read_print_loop;;




let main () =
  if Array.length Sys.argv > 1
  then readfile []
  else read_print_loop [] ;;
    
    
if !Sys.interactive then 
  ()
else 
  main ()    


    
    
  
  
