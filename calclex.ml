(* calclex.ml: Lexer and tokenization for calculon. Defines token
   types and provides main lexing function.
   
   OPTIONAL PROBLEM 1 WAS COMPLETED*)

open Printf;;

(* algebraic types for tokens: lexing results *)
type token =
  | Plus | Times | Minus | Slash
  | LessThan | GreatThan | Equal
  | OParen | CParen 
  | If | Then | Else 
  | At | Let | In
  | Def | Semicolon 
  | IntTok of int
  | BoolTok of bool
  | Ident of string 
  | AndTok | OrTok | Mod                                           (* PATCH PROBLEM *)
;;

(* Create a string of a list of tokens *)
let tokenlist_string tokens =
  let buf = Buffer.create 256 in                             (* extensibel character buffer *)
  Buffer.add_string buf "[";
  let toks = ref tokens in
  let count = ref 0 in
  while !toks <> [] do
    if !count > 0  && !count mod 10 = 0 then
      Buffer.add_string buf "\n ";
    let str = match List.hd !toks with
      | Plus       -> "Plus"
      | Times      -> "Times"
      | Minus      -> "Minus"
      | Slash      -> "Slash"
      | Mod        -> "Mod"
      | LessThan   -> "LessThan"
      | GreatThan  -> "GreatThan"
      | Equal      -> "Equal"
      | AndTok     -> "AndTok"
      | OrTok      -> "OrTok"
      | At         -> "At"
      | OParen     -> "OParen"
      | CParen     -> "CParen"
      | If         -> "If"
      | Then       -> "Then"
      | Else       -> "Else "
      | Let        -> "Let"
      | In         -> "In"
      | Def        -> "Def"
      | Semicolon  -> "Semicolon "
      | IntTok(i)  -> sprintf "IntTok(%d)" i
      | BoolTok(b) -> sprintf "BoolTok(%b)" b
      | Ident(s)   -> sprintf "Ident(%s)" s 
    in
    Buffer.add_string buf (sprintf "%s; " str);
    toks := List.tl !toks;
    incr count;
  done;
  if tokens <> [] then
    Buffer.truncate buf ((Buffer.length buf)-2);
  Buffer.add_string buf "]";
  Buffer.contents buf           
;;


(* true if the given character is a digit 0-9 and false otherwise *)
let is_digit c =
  let digits = "0123456789" in
  let loc = String.index_opt digits c in
  loc <> None
;;

(* true if character is letter a-z or A-Z, false otherwise *)
let is_letter c =
  let letters = "abcdefghijklmnopqrstuvwxyz_." in (* include dot for file names *)
  let lower = Char.lowercase_ascii c in
  let loc = String.index_opt letters lower in
  loc <> None
;;

(* Exception associated with lexing problems *)
exception LexError of {
    msg : string;
};;

(* create a list of tokens based on the string given.  *)
let lex_string string =
  let len = String.length string in
  let rec lex pos =                                          (* recursive helper *)
    if pos >= len then                                       (* off end of string ? *)
      []                                                     (* end of input *)
    else                                                     (* more to lex *)
      match string.[pos] with                                (* match a single character *)
      |' ' | '\t' | '\n' -> lex (pos+1)                      (* skip whitespace *)
      |'+' -> Plus      :: (lex (pos+1))                     (* single char ops become operators *)
      |'-' -> Minus     :: (lex (pos+1))        
      |'*' -> Times     :: (lex (pos+1))
      |'/' -> Slash     :: (lex (pos+1))
      |'%' -> Mod       :: (lex (pos+1))
      |'@' -> At        :: (lex (pos+1))
      |'=' -> Equal     :: (lex (pos+1))
      |'<' -> LessThan  :: (lex (pos+1))
      |'>' -> GreatThan :: (lex (pos+1))
      |'(' -> OParen    :: (lex (pos+1))                     (* and open/close parens *)
      |')' -> CParen    :: (lex (pos+1))
      |';' -> Semicolon :: (lex (pos+1))
      | d when is_digit d ->                                 (* see a digit *)
         let stop = ref pos in                               (* scan through until a non-digit is found *)
         while !stop < len && is_digit string.[!stop] do
           incr stop;
         done;
         let numstr = String.sub string pos (!stop - pos) in (* substring is the int *)
         let num = int_of_string numstr in                   (* parse the integer *)
         (IntTok num) :: (lex !stop)                         (* and tack onto the stream of tokens *)
      | a when is_letter a ->                                (* see a letter *)
         let stop = ref pos in                               (* scan through until a non-letter is found *)
         while !stop < len && is_letter string.[!stop] do
           incr stop;
         done;
         let ident = String.sub string pos (!stop - pos) in  (* substring is the identifier *)
         let tok = 
           match ident with
           | "def"   -> Def
           | "let"   -> Let
           | "in"    -> In
           | "true"  -> BoolTok true
           | "false" -> BoolTok false
           | "if"    -> If
           | "then"  -> Then
           | "else"  -> Else
           | "and"   -> AndTok
           | "or"    -> OrTok
           | _ -> Ident(ident)
         in
         tok :: (lex !stop)                                  (* and tack onto the stream of tokens *)
      | _ ->                                                 (* any other characters lead to failures *)
         let msg = sprintf "char '%c' not recognized, at position %d in the input '%s'" string.[pos] pos string in
         raise (LexError{msg})
  in                                                         (* end helper *)
  lex 0                                                      (* call helper *)
;;

