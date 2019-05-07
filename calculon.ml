open Calclex;;
open Calcparse;;
open Calceval;;
open Printf;;

(* i'm not familiar with the type of thing I'm seeing *)
(* Great Shatner's ghost! *)
(* That was so terrible I think you gave me cancer! 
OPTIONAL PROBLEM 1 WAS COMPLETED*)

Printexc.record_backtrace true;;                                 (* turn on exception backtraces *)

(* Help string to be printed for the "help" command. *)
let help_string =
  let lines = [
      "CALCULON: a calculator/interpreter with an unholy... ACTING TALENT!";
      "";
      "--SUPPORTED SYNTAX--";
      "  <expr> ;                          : expression evaluation terminated by semicolon ";
      "  def x = <expr> ; in <expr>        : top-level variable bindings";
      "  1 + 2*9 / (4-2)                   : basic arithmetic operators";
      "  let x=<expr> in <expr> ;          : let bindings for locals";
      "  if <expr> then <expr> else <expr> : conditional execution";
      "  @n n*2+4                          : lambda abstraction with parameter n";
      "  def double = @n n*2;              : top-level function binding";
      "  double 4;                         : function application";
      "  def mul = @a @b a*b;              : nested lambdas for multi-arg function";
      "";
      "--BUILTIN COMMANDS--";
      "  help;                             : print this help message";
      "  quit;                             : quit calculon";
      "  whos;                             : show all top-level bindings and their value types";
      "  undef <ident>;                    : remove a global binding";
      "  debug {true|false};               : enable/disabe debug printing of backtraces";
      "  tokens <expr>;                    : show the results of lexing the given <expr>";
      "  parsetree <expr>;                 : show the results of parsing the given <expr>";
      "  show <expr>;                      : show the structure of the evaluated data in <expr> ";
      "";
      "--OPTIONAL COMMANDS--";
      "  source <filename>;                : read command from <filename> as if typed";
      "  save <filename>;                  : save all definitions as binary data in <filename>";
      "  load <filename>;                  : load binary variable defs from <filename>";
      "  opparsetree <expr>;               : show the results of parsing AND optimizing the given <expr>";
      "  optimize {true|false};            : enable/disabe optimization of expressions in normal evaluation";
    ] in
  String.concat "\n" lines 
;;

let quit_now      = ref false;;                          (* set to true to end execution of the program *)
let echo          = ref false;;                          (* command echoing on/off  *)
let debug         = ref false;;                          (* turn on/off debug printing *)
let optimize      = ref false;;                          (* turn on/off automatic expression optimization *)
let global_varmap = ref Calceval.empty_varmap;;          (* global variable map for name/value bindings *)

(* Process a single statment by reading the character data from
   inchan, tokenizing it, the parsing it, then evaluating it. Catches
   exceptions during evaluation to prevent interactive loop  *)
let rec process_statement inchan =
  printf "calculon> %!" ;                                        (* print prompt *)
  let input = read_statement inchan in                           (* reads characters, may throw End_of_file *)
  if !echo then                                                  (* if echoing is on, print the input *)
    printf "%s\n" input;
  begin
    try
      let tokens = Calclex.lex_string input in
      eval_statement tokens;
    with
    | exc ->                                               (* standard exception handling *)
       let excstr = Printexc.to_string exc in
       printf "ERROR: I'm not familiar with the type of thing I'm seeing...\n";
       printf "%s\n" excstr;
       if !debug=true then
         let bt = Printexc.get_backtrace () in
         printf "BACKTRACE:\n%s\n" bt;
  end;

(* Read a single statement from the given input channel and return the
   statement as a string. The statement's closing semicolon is
   included in the returned string.  *)
and read_statement inchan =
  let input_buf = Buffer.create 256 in
  let inchar = ref ' ' in
  while !inchar=' ' || !inchar='\t' || !inchar='\n' do           (* skip leading whitespace in input *)
    inchar := input_char inchan;
  done;
  while !inchar <> ';' do                                        (* read an entire statement *)
    Buffer.add_char input_buf !inchar;
    inchar := input_char inchan;
  done;
  Buffer.add_char input_buf !inchar;
  let input = Buffer.contents input_buf in
  input


and semicolon_only toks =
  match toks with
  | [Semicolon] -> ()
  | _ ->
     printf "WARNING: Great Shatner's ghost!\n";
     printf "WARNING: The following tokens remain and will NOT be evaluated\n";
     printf "%s\n" (Calclex.tokenlist_string toks);

(* Evaluate top-level statements. Includes special cases for recognizing built-ins like 'quit' and 'whos'. *)
and eval_statement tokens =
  match tokens with
  | [] -> ()                                                     (* no input *)

  | [Ident "quit"; Semicolon] ->                                 (* look for builtin's first *)
     quit_now := true;

  | [Ident "help"; Semicolon] ->
     printf "%s\n" help_string;

  | [Ident "whos"; Semicolon] ->                                 (* show variable bindings *)
     let printwho vname vdata =
       printf "%10s : %s\n" vname (data_string vdata)
     in
     Varmap.iter printwho !global_varmap;

  | [Ident "undef"; Ident varname; Semicolon] ->                 (* remove a global variable binding *)
     global_varmap := Varmap.remove varname !global_varmap;

  | [Ident "debug"; BoolTok b; Semicolon] ->                     (* read input from the given filename as if it were typed *)
     debug := b;
     printf "debug now '%b'\n" b;

  | Ident "tokens" :: rest ->                                    (* show how the following expression would tokenize *)
     let token_str = Calclex.tokenlist_string rest in
     printf "Tokens:\n%s\n" token_str;

  | Ident "parsetree" :: rest ->                                 (* show the parse tree for the following expression *)
     let (expr,rest)  = Calcparse.parse_expr rest in
     let exprtree_str = Calcparse.parsetree_string expr in
     printf "Parse tree:\n%s\n" exprtree_str;

  | Ident "show" :: Ident varname :: rest ->                     (* show the structure of the data given *)
     begin
       match Varmap.find_opt varname !global_varmap with
       | Some vardata ->
          printf "%s\n" (Calceval.data_long_string vardata);
       | None ->
          printf "No variable named '%s'\n" varname;
     end;

  | Def :: Ident vname :: Equal :: rest ->                       (* def varname = <expr> ; *)
     let (expr,rest) = Calcparse.parse_expr rest in
     let vdata = eval_expr !global_varmap expr in
     begin
       match vdata with
       | Closure(c) ->
          c.varmap <- Varmap.add vname vdata c.varmap;           (* add definition name to the closure varmap to allow recursion *)
       | _ -> ()
     end;
     printf "%s : %s\n" vname (data_string vdata);
     global_varmap := Varmap.add vname vdata !global_varmap;
     semicolon_only rest;

  | _ ->                                                         (* <expr> ; *)
     let (expr,rest) = Calcparse.parse_expr tokens in            (* parse some tokens out *)
     let vdata = eval_expr !global_varmap expr in                (* evaluate the expression *)
     printf "%s : %s\n" "-" (data_string vdata);
     semicolon_only rest;
;;

(* Options accepted by the program *)
let options = Arg.([
  ("-echo",  Set(echo),  "Turn on command echoing (default: off)");   
  ("-debug", Set(debug), "Turn on debug printing  (default: off)");   
]);;

(* Do nothing with extra command line arguments *)
let handle_extra_args arg = ();;

(* Simple usage message for Arg.parse *)
let usage = sprintf "usage: %s [options]" Sys.argv.(0);;

(* main routine *)
let _ =
  Arg.parse options handle_extra_args usage;    (* parse command line options *)
  begin
    try
      while !quit_now = false do                (* loop until quit command is issued *)
        process_statement stdin;
      done
    with
    | End_of_file -> ()                         (* end of input reached *)
  end;
  printf "\nThat was so terrible I think you gave me cancer!\n";
;;

