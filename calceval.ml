(* calceval.ml:  
OPTIONAL PROBLEM 1 WAS COMPLETED*)
open Calclex;;
open Calcparse;;
open Printf;;

(* Module for mapping variable names to variable data. *)
module Varmap = Map.Make(String);;

(* Data type for evaluated expressions; variable names are bound to
   data_t values in variable maps. *)
type data_t =
  | IntDat  of int
  | BoolDat of bool
  | Closure of {param_name: string;
                code_expr:  Calcparse.expr;
                mutable varmap: varmap_t; }

(* Type for a a variable map which maps string to data_t (name to value) *)
and varmap_t = data_t Varmap.t;;

(* Empty variable map. *)
let empty_varmap : varmap_t = Varmap.empty;;

(* Creates a short string version of the a data_t value. *)
let rec data_string data = 
  match data with
  | IntDat(i)  -> sprintf "IntDat(%d)"  i
  | BoolDat(b) -> sprintf "BoolDat(%b)" b
  | Closure(c) -> sprintf "Closure(%s, <fun>)" c.param_name

(* Creates a long string version of the data_t value. *)
and data_long_string data =
  match data with
  | IntDat(i)  -> sprintf "IntDat(%d)"  i
  | BoolDat(b) -> sprintf "BoolDat(%b)" b
  | Closure(c) ->
     sprintf "Closure(param_name: %s, varmap=%s code=\n%s)"
       c.param_name (varmap_string c.varmap) (Calcparse.parsetree_string c.code_expr)
                     
(* Creates a string version of a varmap_t by iterating through all its
   names (keys) and appending string versions of the associated data
   (values) *)
and varmap_string varmap =
  let buf = Buffer.create 256 in                    (* extensibel character buffer *)
  Buffer.add_string buf "{";
  let help vname vdata =
    let str = sprintf "%s: %s, " vname (data_string vdata) in
    Buffer.add_string buf str;
  in
  Varmap.iter help varmap;
  if varmap <> Varmap.empty then
    Buffer.truncate buf ((Buffer.length buf)-2);
  Buffer.add_string buf "}";
  Buffer.contents buf           
;;

(* Exception associated with evaluation errors. All strings to enable
   easier printing when the exception is caught. *)
exception EvalError of {
    msg    : string;
    varmap : string;
    expr   : string
};;

(* Convenience function which stringifies arguments then creates an
   exception. *)
let eval_error msg varmap expr =
  EvalError{msg = msg;
            varmap=varmap_string varmap;
            expr="\n"^(Calcparse.parsetree_string expr); }
;;

(* Evaluation function for expressions. Recursively descends through
   the expression tree evaluating each kind of expression. Parameter
   varmap is a varmap_t with the current variable bindings. *)
let rec eval_expr varmap expr =
  match expr with
  | IntExp i -> IntDat i                                             (* constants are self-evaluating *)

  | BoolExp b -> BoolDat b

  | Varname varname ->                                               (* look up variables in varmap *)
     begin
       match Varmap.find_opt varname varmap with
       | Some d -> d
       | None ->
          let msg = sprintf "No variable '%s' bound" varname in
          raise (eval_error msg varmap expr)
     end 

  | Intop(o) ->                                                      (* integer operations like + - * / *)
     begin
      let ldata = eval_expr varmap o.lexpr in
      let rdata = eval_expr varmap o.rexpr in
      match ldata,rdata with
      | (IntDat li),(IntDat ri) ->
         begin
          match o.op with
          | Add     -> IntDat  (li + ri)
          | Sub     -> IntDat  (li - ri)
          | Remainder -> IntDat (li mod ri)
          | Mul     -> IntDat  (li * ri)
          | Div     -> IntDat  (li / ri)
          | Less    -> BoolDat ((li - ri) < 0) (* Check if difference of left and right is less than 0 to determine less than *)
          | Greater -> BoolDat ((li - ri) > 0) (* Check if difference of left and right is greater than 0 to determine greater than *)
          | Equal   -> BoolDat ((li-ri) = 0) (* Check if difference of left and right is equal to 0 to determine equal *)
        end
      | (IntDat li),rerr ->
         let msg = sprintf "Expect Int for right arithmetic expression, found '%s'" (data_string rerr) in
         raise (eval_error msg varmap expr)
      | lerr,_ ->
         let msg = sprintf "Expect Int for right arithmetic expression, found '%s'" (data_string lerr) in
         raise (eval_error msg varmap expr)
    end

  | Boolop(o) ->                                                     (* boolean operations *)
     begin                                                           (* PATCH PROBLEM *)
       let ldata = eval_expr varmap o.lexpr in (* Evaluate left side *)
       let rdata = eval_expr varmap o.rexpr in (* Evaluate right side *)
       match ldata, rdata with (* Match each evluation *)
       | (BoolDat li), (BoolDat ri) ->
          begin
            match o.op with
            | And -> BoolDat (li && ri) (* Evaluate and expr *)
            | Or  -> BoolDat (li || ri) (* Evaluate or expr *)
          end
       | (BoolDat li), rerr -> (* Error cases *)
            let msg = sprintf "Expect Bool for right arithemetic expression, found '%s'" (data_string rerr) in
            raise (eval_error msg varmap expr)
       | lerr,_ -> 
            let msg = sprintf "Expect Bool for right arithmetic expression, found '%s'" (data_string lerr) in
            raise (eval_error msg varmap expr)
     end

  | Cond(c) ->                                                       (* IMPLEMENT #1: conditionals *)
     begin
       let test = eval_expr varmap c.if_expr in (*Evaluate if expression (recursion)*)
       match test with
       |IntDat i -> (*Integers cannot be evaluated as conditionals*)
        let msg = sprintf "Expected Bool for if(), found '%s'" (data_string test) in
        raise(eval_error msg varmap expr)
       |Closure k-> (*Closures cannot be evaluated as conditionals*)
        let msg = sprintf "Expected Bool for if(), found '%s'" (data_string test) in
        raise(eval_error msg varmap expr)
       |BoolDat b -> (*Booleans are the only ones that can be evaluated as a conditional*)
        match b with 
        |true-> eval_expr varmap c.then_expr (*The if-expression was true -> evaluate the then-expression*)
        |false -> eval_expr varmap c.else_expr (*The if-expression was false -> evaluate the else-expression*)
     end

  | Letin(l) ->                                                      (* let/in expressions *)
     begin
       let var_data = eval_expr varmap l.var_expr in (* Evaluate let expression and store it *)
       match var_data with
       |Closure k -> (* It's a closoure, meaning recursive calls *)
        k.varmap <- Varmap.add l.var_name var_data k.varmap; (* Modify closure's varmap to include let bindings data *)
        eval_expr k.varmap l.in_expr (* Evaluate it with the closure's varmap *)
       |_ -> (* Not recursive, just a regular expression *)
        let new_varmap = Varmap.add l.var_name var_data varmap in (* Create a new varmap by adding the let bindings data to the bigger varmap *)
        eval_expr new_varmap l.in_expr (* Evaluate with the global varmap *)
     end

  | Lambda(l) ->                                                     (* lambda expressions *)
     begin                                                           (* IMPLEMENT #3: Build a Closure *)
       Closure{param_name = l.param_name; code_expr = l.code_expr; varmap=varmap}; (* Build simple closure by taking the paramname and adding it to the current varmap *)
     end

  | Apply(apply) ->                                                  (* function application *)
     begin
       let res = eval_expr varmap apply.func_expr in                 (* Evaluate the func_expr from apply first to check for a closure *)
       match res with
        |Closure k ->                                                (* Closure found! Evaluate the param_expr and record the data in res2 *)
          let res2 = eval_expr varmap apply.param_expr in
          k.varmap <- Varmap.add k.param_name res2 k.varmap;         (* Add bingind to closure's varmap of the param_expr to the current closure *)
          eval_expr k.varmap k.code_expr                             (* Recursively evaluate *)

        |_ -> 
          let msg = sprintf "Expected Closure for application, found '%s'" (data_string res) in (* Error case when not a closure *)
          raise (eval_error msg varmap expr)
     end              
;;

(********************************************************************************)
(* PATCH PROBLEM: Optimizes an expression by evaluating some of the
   constant expressions in it (constant folding and constant
   propagation). Performs only optimizations on left-associative
   expressions. For example, the expression "2+3+n" parses to

   Add (Add (IntExp 2,q
             IntExp 3),
        Varname n)

   and is optimized to

   Add (IntExp 5,
        Varname n)

   However, the expression "n+2+3" parses to

   Add (Add (Varname n,
             IntExp 2),
        IntExp 3)

   and is not optimized/transformed by this function. 

   Optimizes code within coditionals eliminating branches if possible
   and also within lambda code expressions.
*)
let rec optimize_expr varmap expr =
  (* IMPLEMENT THIS FUNCTION to complete the PATCH PROBLEM *)
  failwith "Expression Optimization not yet implemented"
;;
