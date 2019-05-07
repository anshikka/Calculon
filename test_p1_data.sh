#!/bin/bash

T=0                             # global test number

((T++))
tnames[T]="regression"
read  -r -d '' input[$T] <<"ENDIN"
help;
def x = 7-4/2;
let y = x*2 in y/5+1;
quit;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> help;
CALCULON: a calculator/interpreter with an unholy... ACTING TALENT!

--SUPPORTED SYNTAX--
  <expr> ;                          : expression evaluation terminated by semicolon 
  def x = <expr> ; in <expr>        : top-level variable bindings
  1 + 2*9 / (4-2)                   : basic arithmetic operators
  let x=<expr> in <expr> ;          : let bindings for locals
  if <expr> then <expr> else <expr> : conditional execution
  @n n*2+4                          : lambda abstraction with parameter n
  def double = @n n*2;              : top-level function binding
  double 4;                         : function application
  def mul = @a @b a*b;              : nested lambdas for multi-arg function

--BUILTIN COMMANDS--
  help;                             : print this help message
  quit;                             : quit calculon
  whos;                             : show all top-level bindings and their value types
  undef <ident>;                    : remove a global binding
  debug {true|false};               : enable/disabe debug printing of backtraces
  tokens <expr>;                    : show the results of lexing the given <expr>
  parsetree <expr>;                 : show the results of parsing the given <expr>
  show <expr>;                      : show the structure of the evaluated data in <expr> 

--OPTIONAL COMMANDS--
  source <filename>;                : read command from <filename> as if typed
  save <filename>;                  : save all definitions as binary data in <filename>
  load <filename>;                  : load binary variable defs from <filename>
  opparsetree <expr>;               : show the results of parsing AND optimizing the given <expr>
  optimize {true|false};            : enable/disabe optimization of expressions in normal evaluation
calculon> def x = 7-4/2;
x : IntDat(5)
calculon> let y = x*2 in y/5+1;
- : IntDat(3)
calculon> quit;

That was so terrible I think you gave me cancer!
ENDOUT

################################################################################
# Lexing tests

((T++))
tnames[T]="tokens-simple-if"
read  -r -d '' input[$T] <<"ENDIN"
tokens if true then 1 else 2;
tokens if false then 9*8/2-1 else 7+3+x*y;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> tokens if true then 1 else 2;
Tokens:
[If; BoolTok(true); Then; IntTok(1); Else ; IntTok(2); Semicolon ]
calculon> tokens if false then 9*8/2-1 else 7+3+x*y;
Tokens:
[If; BoolTok(false); Then; IntTok(9); Times; IntTok(8); Slash; IntTok(2); Minus; IntTok(1); 
 Else ; IntTok(7); Plus; IntTok(3); Plus; Ident(x); Times; Ident(y); Semicolon ]
calculon> 
That was so terrible I think you gave me cancer!
ENDOUT

((T++))
tnames[T]="tokens-if-as-expr"
read  -r -d '' input[$T] <<"ENDIN"
tokens let result = if true then 1 else 2 in result*4;
tokens 5 + if true then 1 else 2;
tokens (if false then 9 else 7)*6+1;
tokens (if true then 9+1 else 6*4) / (if false then 1 else 2);
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> tokens let result = if true then 1 else 2 in result*4;
Tokens:
[Let; Ident(result); Equal; If; BoolTok(true); Then; IntTok(1); Else ; IntTok(2); In; 
 Ident(result); Times; IntTok(4); Semicolon ]
calculon> tokens 5 + if true then 1 else 2;
Tokens:
[IntTok(5); Plus; If; BoolTok(true); Then; IntTok(1); Else ; IntTok(2); Semicolon ]
calculon> tokens (if false then 9 else 7)*6+1;
Tokens:
[OParen; If; BoolTok(false); Then; IntTok(9); Else ; IntTok(7); CParen; Times; IntTok(6); 
 Plus; IntTok(1); Semicolon ]
calculon> tokens (if true then 9+1 else 6*4) / (if false then 1 else 2);
Tokens:
[OParen; If; BoolTok(true); Then; IntTok(9); Plus; IntTok(1); Else ; IntTok(6); Times; 
 IntTok(4); CParen; Slash; OParen; If; BoolTok(false); Then; IntTok(1); Else ; IntTok(2); 
 CParen; Semicolon ]
calculon> 
That was so terrible I think you gave me cancer!
ENDOUT

((T++))
tnames[T]="tokens-nested-if"
read  -r -d '' input[$T] <<"ENDIN"
tokens if true then if false then 1 else 2 else 3;
tokens 
if if true 
      then false 
      else true 
   then if false 
        then 1 
        else 2
   else if false 
        then 3 
        else 4;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> tokens if true then if false then 1 else 2 else 3;
Tokens:
[If; BoolTok(true); Then; If; BoolTok(false); Then; IntTok(1); Else ; IntTok(2); Else ; 
 IntTok(3); Semicolon ]
calculon> tokens 
if if true 
      then false 
      else true 
   then if false 
        then 1 
        else 2
   else if false 
        then 3 
        else 4;
Tokens:
[If; If; BoolTok(true); Then; BoolTok(false); Else ; BoolTok(true); Then; If; BoolTok(false); 
 Then; IntTok(1); Else ; IntTok(2); Else ; If; BoolTok(false); Then; IntTok(3); Else ; 
 IntTok(4); Semicolon ]
calculon> 
That was so terrible I think you gave me cancer!
ENDOUT

################################################################################
# Parse tests

((T++))
tnames[T]="parse-simple-if"
read  -r -d '' input[$T] <<"ENDIN"
parsetree if true then 1 else 2;
parsetree if false then 9*8/2-1 else 7+3+x*y;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> parsetree if true then 1 else 2;
Parse tree:
Cond
  .if_expr:
    BoolExp(true)
  .then_expr:
    IntExp(1)
  .else_expr:
    IntExp(2)

calculon> parsetree if false then 9*8/2-1 else 7+3+x*y;
Parse tree:
Cond
  .if_expr:
    BoolExp(false)
  .then_expr:
    Sub
      Div
        Mul
          IntExp(9)
          IntExp(8)
        IntExp(2)
      IntExp(1)
  .else_expr:
    Add
      Add
        IntExp(7)
        IntExp(3)
      Mul
        Varname(x)
        Varname(y)

calculon> 
That was so terrible I think you gave me cancer!
ENDOUT

((T++))
tnames[T]="parse-if-as-expr"
read  -r -d '' input[$T] <<"ENDIN"
parsetree let result = if true then 1 else 2 in result*4;
parsetree 5 + if true then 1 else 2;
parsetree (if false then 9 else 7)*6+1;
parsetree (if true then 9+1 else 6*4) / (if false then 1 else 2);
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> parsetree let result = if true then 1 else 2 in result*4;
Parse tree:
Letin( result )
  .var_expr:
    Cond
      .if_expr:
        BoolExp(true)
      .then_expr:
        IntExp(1)
      .else_expr:
        IntExp(2)
  .in_expr:
    Mul
      Varname(result)
      IntExp(4)

calculon> parsetree 5 + if true then 1 else 2;
Parse tree:
Add
  IntExp(5)
  Cond
    .if_expr:
      BoolExp(true)
    .then_expr:
      IntExp(1)
    .else_expr:
      IntExp(2)

calculon> parsetree (if false then 9 else 7)*6+1;
Parse tree:
Add
  Mul
    Cond
      .if_expr:
        BoolExp(false)
      .then_expr:
        IntExp(9)
      .else_expr:
        IntExp(7)
    IntExp(6)
  IntExp(1)

calculon> parsetree (if true then 9+1 else 6*4) / (if false then 1 else 2);
Parse tree:
Div
  Cond
    .if_expr:
      BoolExp(true)
    .then_expr:
      Add
        IntExp(9)
        IntExp(1)
    .else_expr:
      Mul
        IntExp(6)
        IntExp(4)
  Cond
    .if_expr:
      BoolExp(false)
    .then_expr:
      IntExp(1)
    .else_expr:
      IntExp(2)

calculon> 
That was so terrible I think you gave me cancer!
ENDOUT

((T++))
tnames[T]="parse-nested-if"
read  -r -d '' input[$T] <<"ENDIN"
parsetree if true then if false then 1 else 2 else 3;
parsetree 
if if true 
      then false 
      else true 
   then if false 
        then 1 
        else 2
   else if false 
        then 3 
        else 4;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> parsetree if true then if false then 1 else 2 else 3;
Parse tree:
Cond
  .if_expr:
    BoolExp(true)
  .then_expr:
    Cond
      .if_expr:
        BoolExp(false)
      .then_expr:
        IntExp(1)
      .else_expr:
        IntExp(2)
  .else_expr:
    IntExp(3)

calculon> parsetree 
if if true 
      then false 
      else true 
   then if false 
        then 1 
        else 2
   else if false 
        then 3 
        else 4;
Parse tree:
Cond
  .if_expr:
    Cond
      .if_expr:
        BoolExp(true)
      .then_expr:
        BoolExp(false)
      .else_expr:
        BoolExp(true)
  .then_expr:
    Cond
      .if_expr:
        BoolExp(false)
      .then_expr:
        IntExp(1)
      .else_expr:
        IntExp(2)
  .else_expr:
    Cond
      .if_expr:
        BoolExp(false)
      .then_expr:
        IntExp(3)
      .else_expr:
        IntExp(4)

calculon> 
That was so terrible I think you gave me cancer!
ENDOUT

################################################################################
# Eval tests

((T++))
tnames[T]="eval-simple-if"
read  -r -d '' input[$T] <<"ENDIN"
if true then 1 else 2;
if false then 1 else 2;
if true then 9*8/2-1 else 7+3+x*y;
def x = 4;
def y = 5;
if false then 9*8/2-1 else 7+3+x*y;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> if true then 1 else 2;
- : IntDat(1)
calculon> if false then 1 else 2;
- : IntDat(2)
calculon> if true then 9*8/2-1 else 7+3+x*y;
- : IntDat(35)
calculon> def x = 4;
x : IntDat(4)
calculon> def y = 5;
y : IntDat(5)
calculon> if false then 9*8/2-1 else 7+3+x*y;
- : IntDat(30)
calculon> 
That was so terrible I think you gave me cancer!
ENDOUT

((T++))
tnames[T]="parse-if-as-expr"
read  -r -d '' input[$T] <<"ENDIN"
let result = if true then 1 else 2 in result*4;
5 + if true then 1 else 2;
(if false then 9 else 7)*6+1;
(if true then 9+1 else 6*4) / (if false then 1 else 2);
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> let result = if true then 1 else 2 in result*4;
- : IntDat(4)
calculon> 5 + if true then 1 else 2;
- : IntDat(6)
calculon> (if false then 9 else 7)*6+1;
- : IntDat(43)
calculon> (if true then 9+1 else 6*4) / (if false then 1 else 2);
- : IntDat(5)
calculon> 
That was so terrible I think you gave me cancer!
ENDOUT

((T++))
tnames[T]="parse-nested-if"
read  -r -d '' input[$T] <<"ENDIN"
if true then if false then 1 else 2 else 3;
 
if if true 
      then false 
      else true 
   then if false 
        then 1 
        else 2
   else if false 
        then 3 
        else 4;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> if true then if false then 1 else 2 else 3;
- : IntDat(2)
calculon> if if true 
      then false 
      else true 
   then if false 
        then 1 
        else 2
   else if false 
        then 3 
        else 4;
- : IntDat(4)
calculon> 
That was so terrible I think you gave me cancer!
ENDOUT
