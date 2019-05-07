open Printf;;

let _ =
  if Array.length Sys.argv < 2 then                      (* handle command line arguments *)
    begin
      printf "usage: %s 'expression'\n" Sys.argv.(0);
      Pervasives.exit 1;
    end;
  let expr_str = Sys.argv.(1) in
  let tokens = Calclex.lex_string expr_str in
  let (expr_tree,_) = Calcparse.parse_expr tokens in
  let tree_string = Calcparse.parsetree_string expr_tree in
  printf "%s" tree_string;
;;
    
