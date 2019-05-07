(* calcparse.ml:  
OPTIONAL PROBLEM 1 WAS COMPLETED*)
open Calclex;;
open Printf;;

(* RE-ORDER the production rules to go top-down. Re-arrange the
   calling order between arithmetic and control to allow them to be
   nested. *)

(* exception type for parsing error *)
exception ParseError of {
    msg  : string;
    toks : token list;
  };;

(* type for operations on two integers for expressions that combine
   results from left/right branches. *)
type intop =
  | Add | Sub | Mul | Div
  | Less | Greater | Equal | Remainder
;;

(* PATCH PROBLEM: type for operations on two booleans boolean *)
type boolop =
  | And | Or 
;;


(* algebraic types for expression tree: parsing results *)
type expr =
  | IntExp  of int
  | BoolExp of bool
  | Varname of string                         (* variable name that should be looked up *)
  | Intop   of {op         : intop;           (* binary op on ints like Plus, Minus, Less, etc. *)
                lexpr      : expr;
                rexpr      : expr; }
  | Boolop  of {op         : boolop;          (* PATCH PROBLEM: binary op on booleans like And/Or. *)
                lexpr      : expr;
                rexpr      : expr; }
  | Cond    of {if_expr    : expr;            (* if/then/else, expressions associated with each  *)
                then_expr  : expr;
                else_expr  : expr; }  
  | Letin   of {var_name   : string;          (* let expression binding a new name *)
                var_expr   : expr;
                in_expr    : expr; }
  | Lambda  of {param_name : string;          (* create a function with named parameter *)
                code_expr  : expr; }
  | Apply   of {func_expr  : expr;            (* apply a function to a single parameter *)
                param_expr : expr; }       
;;

(* Create a string version of the given parsed expression tree *)
let parsetree_string expr =
  let buf = Buffer.create 256 in                    (* extensibel character buffer *)
  let indent n =
    for i=1 to n do                           
      Buffer.add_string buf "  ";
    done;
  in
  let rec build expr depth =                        (* recursive helper *)
    indent depth;
    match expr with
    | IntExp(i) ->
       Buffer.add_string buf (sprintf "IntExp(%d)\n" i);
    | BoolExp(b) ->
       Buffer.add_string buf (sprintf "BoolExp(%b)\n" b);
    | Varname(s) ->
       Buffer.add_string buf (sprintf "Varname(%s)\n" s);
    | Intop(o) ->
       let opstr = match o.op with
         | Add -> "Add" | Sub -> "Sub" | Mul -> "Mul" | Div -> "Div"
         | Less -> "Less" | Greater -> "Greater" | Equal -> "Equal" | Remainder -> "Remainder"
       in
       Buffer.add_string buf (sprintf "%s\n" opstr);
       build o.lexpr (depth+1);
       build o.rexpr (depth+1);
    | Boolop(o) ->
       let opstr = match o.op with
         | And -> "And" | Or -> "Or" 
       in
       Buffer.add_string buf (sprintf "%s\n" opstr);
       build o.lexpr (depth+1);
       build o.rexpr (depth+1);
    | Cond(c) ->
       Buffer.add_string buf "Cond\n";
       indent (depth+1);
       Buffer.add_string buf ".if_expr:\n";
       build c.if_expr   (depth+2);
       indent (depth+1);
       Buffer.add_string buf ".then_expr:\n";
       build c.then_expr (depth+2);
       indent (depth+1);
       Buffer.add_string buf ".else_expr:\n";
       build c.else_expr (depth+2);
    | Letin(l) ->
       Buffer.add_string buf (sprintf "Letin( %s )\n" l.var_name);
       indent (depth+1);
       Buffer.add_string buf ".var_expr:\n";
       build l.var_expr   (depth+2);
       indent (depth+1);
       Buffer.add_string buf ".in_expr:\n";
       build l.in_expr (depth+2);
    | Lambda(l) ->
       Buffer.add_string buf (sprintf "Lambda( %s )\n" l.param_name);
       build l.code_expr   (depth+1);
    | Apply(a) ->
       Buffer.add_string buf "Apply\n";
       indent (depth+1);
       Buffer.add_string buf ".func_expr:\n";
       build a.func_expr   (depth+2);
       indent (depth+1);
       Buffer.add_string buf ".param_expr:\n";
       build a.param_expr   (depth+2);
  in
  build expr 0;
  Buffer.contents buf                               (* return string from Buffer *)
;;


(* Top-level entry for recursive descent parser: create an expression
   tree from a series of tokens. Starts a series of mutually recursive
   functions. *)
let rec parse_expr tokens =
  let (expr, rest) as result = parse_or tokens in
  result

and parse_or toks =
  let rec iter lexpr toks = (* Chained expression *)
    match toks with
    | OrTok :: rest -> (* Found an 'Or' token *)
        let (rexpr, rest) = parse_and rest in (* Parse the rest of the expression *)
        iter (Boolop{op=Or;lexpr;rexpr}) rest (* Get Boolop variant *)
    |_ -> (lexpr, toks) (* No cases matched *)
  in
  let (lexpr, rest) = parse_and toks in
  iter lexpr rest

and parse_and toks =
  let rec iter lexpr toks = (* Chained expression *)
    match toks with
    | AndTok :: rest -> (* Found an 'and' token *)
        let (rexpr, rest) = parse_compare rest in (* Parse lower *)
        iter (Boolop{op=And;lexpr;rexpr}) rest (* Create Boolop record *)
    |_ -> (lexpr, toks) (* Not matched *)
  in
  let (lexpr, rest) = parse_compare toks in (* Recurse lower *)
  iter lexpr rest

(* parse a number comparison using <, >, or =. These cannot be chained
   together so are simpler than add/sub. *)
and parse_compare toks =
  let (lexpr, rest) = parse_addsub toks in (* Parse the left-hand expression first *)
  match rest with (* Match the rest of the tokens *)
  | GreatThan :: rest ->  (* left side > rest? *)
      let (rexpr, rest) = parse_addsub rest in (* parse the left hand! *)
      (Intop{op=Greater;lexpr;rexpr}, rest); (* Get intopt variant *)
  | Equal :: rest ->  (* left side = rest? *)
      let (rexpr, rest) = parse_addsub rest in
      (Intop{op=Equal;lexpr;rexpr}, rest);
  | LessThan :: rest -> (* left side < rest? *)
      let (rexpr, rest) = parse_addsub rest in
      (Intop{op=Less;lexpr;rexpr}, rest);
  (* FILL IN CASES for comparison of values *)
  | _ -> (lexpr, rest) (* No cases matched *)

(* parse addition and subtraction, left-associative *)
and parse_addsub toks =
  let rec iter lexpr toks =                            (* loop through adjacent + and - expressions *)
    match toks with
    | Plus :: rest ->                                  (* found + *)
       let (rexpr,rest) = parse_muldiv rest in         (* consume a higher-prec expression *)
       iter (Intop{op=Add;lexpr;rexpr}) rest           (* create an Add tree and iterate again *)
    | Minus :: rest ->                                 (* found - *)
       let (rexpr,rest) = parse_muldiv rest in         (* consume a higher-prec expression *)
       iter (Intop{op=Sub;lexpr;rexpr}) rest           (* create a  Sub tree and iterate again *)
    | _ -> (lexpr, toks)
  in
  let (lexpr, rest) = parse_muldiv toks in             (* create the initial left expression *)
  iter lexpr rest                                      (* start iterating *)

(* parse multiplication and division, same principle as parse_addsub *)
and parse_muldiv toks =
  let rec iter lexpr toks =
    match toks with
    | Times :: rest ->
       let (rexpr,rest) = parse_letin rest in
       iter (Intop{op=Mul;lexpr;rexpr}) rest
    | Slash :: rest ->
       let (rexpr,rest) = parse_letin rest in
       iter (Intop{op=Div;lexpr;rexpr}) rest
    | Mod :: rest ->
      let (rexpr, rest) = parse_letin rest in
      iter (Intop{op=Remainder; lexpr; rexpr}) rest
    | _ -> (lexpr, toks)
  in
  let (lexpr, rest) = parse_letin toks in
  iter lexpr rest

(* parse a let/in expression *)
and parse_letin toks =
  match toks with
  | Let :: Ident var_name :: Equal :: rest ->          (* look for a sequence of 'let name = ...' *)
     begin 
       let (var_expr,rest) = parse_expr rest in        (* parse the rest of the expression *)
       match rest with
       | In :: rest ->                                 (* check that it ends with an 'in' *)
          let (in_expr,rest) = parse_expr rest in      (* parse the 'in <expr>' *)
          (Letin{var_name; var_expr; in_expr}, rest)   (* return result and rest of tokens *)
       | _ -> raise (ParseError{msg="Expected 'in' after 'let'"; toks=rest})
     end
  | _ -> parse_cond toks                               (* didn't find 'let', recurse lower *)

(* parse a conditional if <expr> then <expr> else <expr> *)
and parse_cond toks =
  match toks with
  | If :: rest -> (*look for a sequence of if <expr> then <expr> else <expr>*)
     begin
      let (if_expr, rest) = parse_expr rest in 
      match rest with (*Parse then_expr*)
      |Then :: rest -> 
        begin
          let (then_expr, rest) = parse_expr rest in
          match rest with (*Parse else_expr*)
          |Else :: rest ->
            let (else_expr, rest) = parse_expr rest in
            (Cond{if_expr; then_expr; else_expr}, rest)
          |_ -> raise (ParseError{msg="Expected 'else' "; toks = rest}) (*No else statement results in error*)
        end
      |_ -> raise (ParseError{msg="Expected 'then' "; toks = rest}) (*No then expression results in error*)
      end 
  (* P1: FILL IN CASES to parse if/then/else *)
  | _ -> parse_lambda toks (*Didn't find 'if', recurse lower *)

(* parse a lambda @x <expr> *)
and parse_lambda toks =
  (* P3: Fill in cases to m *)
  match toks with 
  |At :: Ident x :: rest -> (* match with @[varname] <expr> *)
    let (b, rest1)= parse_expr rest in (* compute <expr> first *)
    (Lambda{param_name=x; code_expr = b}, rest1); (* Then set Lambda in tree to evaluation *)
  |At :: _ :: rest -> raise (ParseError{msg="Expected identifier in lambda expression @"; toks = rest})(* Error Case *)
  | _ -> parse_apply toks (* Doesn't match, go on *)

(* Parse a function application which is left-associative. Repeatedly
   matches expressions and applies them in left-to-right order. *)
and parse_apply toks =
  let rec iter lexpr toks =
    match toks with
    | IntTok _ :: rest | BoolTok _ :: rest | Ident _ :: rest | OParen :: rest ->
       let (rexpr,rest) = parse_ident toks in
       iter (Apply{func_expr=lexpr; param_expr=rexpr}) rest
    | _ -> (lexpr,toks)
  in
  let (lexpr, rest) = parse_ident toks in
  iter lexpr rest 

(* parse identifiers, integers, booleans, and open/close parentheses *)
and parse_ident toks =
  match toks with
  | []              -> raise (ParseError {msg="expected an expression"; toks=toks})
  | IntTok n   :: tail -> (IntExp(n),tail)
  | BoolTok b  :: tail -> (BoolExp(b),tail)
  | Ident s :: tail -> (Varname(s),tail)
  | OParen  :: tail ->                                 (* parenthesized expresion *)
     begin
       let (expr,rest) = parse_expr tail in            (* start back at highest precedence *)
       match rest with
       | CParen::tail -> (expr,tail)
       | _ -> raise (ParseError {msg="unclosed parentheses"; toks=tail})
     end
  | _ -> raise (ParseError {msg="syntax error"; toks=toks})
;;
