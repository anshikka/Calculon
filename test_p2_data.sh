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
tnames[T]="tokens-comparisons"
read  -r -d '' input[$T] <<"ENDIN"
tokens 1 > 3;
tokens 5 < 9;
tokens 10 = 2;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> tokens 1 > 3;
Tokens:
[IntTok(1); GreatThan; IntTok(3); Semicolon ]
calculon> tokens 5 < 9;
Tokens:
[IntTok(5); LessThan; IntTok(9); Semicolon ]
calculon> tokens 10 = 2;
Tokens:
[IntTok(10); Equal; IntTok(2); Semicolon ]
calculon> 
That was so terrible I think you gave me cancer!
ENDOUT

((T++))
tnames[T]="tokens-comp-vars"
read  -r -d '' input[$T] <<"ENDIN"
def x = 2;
def y = 10;
tokens x > 3;
tokens 5 < y;
tokens x = y;
tokens x+8 = y;
tokens x*3+1 = y/2-5+x*4;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> def x = 2;
x : IntDat(2)
calculon> def y = 10;
y : IntDat(10)
calculon> tokens x > 3;
Tokens:
[Ident(x); GreatThan; IntTok(3); Semicolon ]
calculon> tokens 5 < y;
Tokens:
[IntTok(5); LessThan; Ident(y); Semicolon ]
calculon> tokens x = y;
Tokens:
[Ident(x); Equal; Ident(y); Semicolon ]
calculon> tokens x+8 = y;
Tokens:
[Ident(x); Plus; IntTok(8); Equal; Ident(y); Semicolon ]
calculon> tokens x*3+1 = y/2-5+x*4;
Tokens:
[Ident(x); Times; IntTok(3); Plus; IntTok(1); Equal; Ident(y); Slash; IntTok(2); Minus; 
 IntTok(5); Plus; Ident(x); Times; IntTok(4); Semicolon ]
calculon> 
That was so terrible I think you gave me cancer!
ENDOUT

((T++))
tnames[T]="tokens-comp-ifs"
read  -r -d '' input[$T] <<"ENDIN"
def x = 2;
def y = 10;
tokens if x > 1 then 2 else 3;
tokens if 5 < y then if x > 1 then 2 else 3 else 4;
tokens if true then x > y else x < y;
tokens if x>1 then if y=0 then x else x/y else x > y;
tokens if x*3+1 = y/2-5+x*4 then x/y > 1 else 1 < y/x ;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> def x = 2;
x : IntDat(2)
calculon> def y = 10;
y : IntDat(10)
calculon> tokens if x > 1 then 2 else 3;
Tokens:
[If; Ident(x); GreatThan; IntTok(1); Then; IntTok(2); Else ; IntTok(3); Semicolon ]
calculon> tokens if 5 < y then if x > 1 then 2 else 3 else 4;
Tokens:
[If; IntTok(5); LessThan; Ident(y); Then; If; Ident(x); GreatThan; IntTok(1); Then; 
 IntTok(2); Else ; IntTok(3); Else ; IntTok(4); Semicolon ]
calculon> tokens if true then x > y else x < y;
Tokens:
[If; BoolTok(true); Then; Ident(x); GreatThan; Ident(y); Else ; Ident(x); LessThan; Ident(y); 
 Semicolon ]
calculon> tokens if x>1 then if y=0 then x else x/y else x > y;
Tokens:
[If; Ident(x); GreatThan; IntTok(1); Then; If; Ident(y); Equal; IntTok(0); Then; 
 Ident(x); Else ; Ident(x); Slash; Ident(y); Else ; Ident(x); GreatThan; Ident(y); Semicolon ]
calculon> tokens if x*3+1 = y/2-5+x*4 then x/y > 1 else 1 < y/x ;
Tokens:
[If; Ident(x); Times; IntTok(3); Plus; IntTok(1); Equal; Ident(y); Slash; IntTok(2); 
 Minus; IntTok(5); Plus; Ident(x); Times; IntTok(4); Then; Ident(x); Slash; Ident(y); 
 GreatThan; IntTok(1); Else ; IntTok(1); LessThan; Ident(y); Slash; Ident(x); Semicolon ]
calculon> 
That was so terrible I think you gave me cancer!
ENDOUT

# ################################################################################
# # Parse tests


((T++))
tnames[T]="parse-comparisons"
read  -r -d '' input[$T] <<"ENDIN"
parsetree 1 > 3;
parsetree 5 < 9;
parsetree 10 = 2;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> parsetree 1 > 3;
Parse tree:
Greater
  IntExp(1)
  IntExp(3)

calculon> parsetree 5 < 9;
Parse tree:
Less
  IntExp(5)
  IntExp(9)

calculon> parsetree 10 = 2;
Parse tree:
Equal
  IntExp(10)
  IntExp(2)

calculon> 
That was so terrible I think you gave me cancer!
ENDOUT

((T++))
tnames[T]="parse-comp-vars"
read  -r -d '' input[$T] <<"ENDIN"
def x = 2;
def y = 10;
parsetree x > 3;
parsetree 5 < y;
parsetree x = y;
parsetree x+8 = y;
parsetree x*3+1 = y/2-5+x*4;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> def x = 2;
x : IntDat(2)
calculon> def y = 10;
y : IntDat(10)
calculon> parsetree x > 3;
Parse tree:
Greater
  Varname(x)
  IntExp(3)

calculon> parsetree 5 < y;
Parse tree:
Less
  IntExp(5)
  Varname(y)

calculon> parsetree x = y;
Parse tree:
Equal
  Varname(x)
  Varname(y)

calculon> parsetree x+8 = y;
Parse tree:
Equal
  Add
    Varname(x)
    IntExp(8)
  Varname(y)

calculon> parsetree x*3+1 = y/2-5+x*4;
Parse tree:
Equal
  Add
    Mul
      Varname(x)
      IntExp(3)
    IntExp(1)
  Add
    Sub
      Div
        Varname(y)
        IntExp(2)
      IntExp(5)
    Mul
      Varname(x)
      IntExp(4)

calculon> 
That was so terrible I think you gave me cancer!
ENDOUT

((T++))
tnames[T]="parse-comp-ifs"
read  -r -d '' input[$T] <<"ENDIN"
def x = 2;
def y = 10;
parsetree if x > 1 then 2 else 3;
parsetree if 5 < y then if x > 1 then 2 else 3 else 4;
parsetree if true then x > y else x < y;
parsetree if x>1 then if y=0 then x else x/y else x > y;
parsetree if x*3+1 = y/2-5+x*4 then x/y > 1 else 1 < y/x ;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> def x = 2;
x : IntDat(2)
calculon> def y = 10;
y : IntDat(10)
calculon> parsetree if x > 1 then 2 else 3;
Parse tree:
Cond
  .if_expr:
    Greater
      Varname(x)
      IntExp(1)
  .then_expr:
    IntExp(2)
  .else_expr:
    IntExp(3)

calculon> parsetree if 5 < y then if x > 1 then 2 else 3 else 4;
Parse tree:
Cond
  .if_expr:
    Less
      IntExp(5)
      Varname(y)
  .then_expr:
    Cond
      .if_expr:
        Greater
          Varname(x)
          IntExp(1)
      .then_expr:
        IntExp(2)
      .else_expr:
        IntExp(3)
  .else_expr:
    IntExp(4)

calculon> parsetree if true then x > y else x < y;
Parse tree:
Cond
  .if_expr:
    BoolExp(true)
  .then_expr:
    Greater
      Varname(x)
      Varname(y)
  .else_expr:
    Less
      Varname(x)
      Varname(y)

calculon> parsetree if x>1 then if y=0 then x else x/y else x > y;
Parse tree:
Cond
  .if_expr:
    Greater
      Varname(x)
      IntExp(1)
  .then_expr:
    Cond
      .if_expr:
        Equal
          Varname(y)
          IntExp(0)
      .then_expr:
        Varname(x)
      .else_expr:
        Div
          Varname(x)
          Varname(y)
  .else_expr:
    Greater
      Varname(x)
      Varname(y)

calculon> parsetree if x*3+1 = y/2-5+x*4 then x/y > 1 else 1 < y/x ;
Parse tree:
Cond
  .if_expr:
    Equal
      Add
        Mul
          Varname(x)
          IntExp(3)
        IntExp(1)
      Add
        Sub
          Div
            Varname(y)
            IntExp(2)
          IntExp(5)
        Mul
          Varname(x)
          IntExp(4)
  .then_expr:
    Greater
      Div
        Varname(x)
        Varname(y)
      IntExp(1)
  .else_expr:
    Less
      IntExp(1)
      Div
        Varname(y)
        Varname(x)

calculon> 
That was so terrible I think you gave me cancer!
ENDOUT

# ################################################################################
# # Eval tests


((T++))
tnames[T]="eval-comparisons"
read  -r -d '' input[$T] <<"ENDIN"
1 > 3;
5 < 9;
10 = 2;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> 1 > 3;
- : BoolDat(false)
calculon> 5 < 9;
- : BoolDat(true)
calculon> 10 = 2;
- : BoolDat(false)
calculon> 
That was so terrible I think you gave me cancer!
ENDOUT

((T++))
tnames[T]="eval-comp-vars"
read  -r -d '' input[$T] <<"ENDIN"
def x = 2;
def y = 10;
x > 3;
5 < y;
x = y;
x+8 = y;
x*3+1 = y/2-5+x*4;
def q = x+8 = y;
def t = x*3+1 < y/2-5+x*4;
def u = x*3+1 > y/2-5+x*4;
q;
t;
u;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> def x = 2;
x : IntDat(2)
calculon> def y = 10;
y : IntDat(10)
calculon> x > 3;
- : BoolDat(false)
calculon> 5 < y;
- : BoolDat(true)
calculon> x = y;
- : BoolDat(false)
calculon> x+8 = y;
- : BoolDat(true)
calculon> x*3+1 = y/2-5+x*4;
- : BoolDat(false)
calculon> def q = x+8 = y;
q : BoolDat(true)
calculon> def t = x*3+1 < y/2-5+x*4;
t : BoolDat(true)
calculon> def u = x*3+1 > y/2-5+x*4;
u : BoolDat(false)
calculon> q;
- : BoolDat(true)
calculon> t;
- : BoolDat(true)
calculon> u;
- : BoolDat(false)
calculon> 
That was so terrible I think you gave me cancer!
ENDOUT

((T++))
tnames[T]="eval-comp-ifs"
read  -r -d '' input[$T] <<"ENDIN"
def x = 2;
def y = 10;
if x > 1 then 2 else 3;
if 5 < y then if x > 1 then 2 else 3 else 4;
if true then x > y else x < y;
if x>1 then if y=0 then x else x/y else x > y;
if x*3+1 = y/2-5+x*4 then x/y > 1 else 1 < y/x ;
def z = let x=5 in x > y/2;
z;
def w = let a= y=10 in if a then y>x else y<x;
w;
if let t=5 in let u=7 in t*u>30 then x=5 else y<12;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> def x = 2;
x : IntDat(2)
calculon> def y = 10;
y : IntDat(10)
calculon> if x > 1 then 2 else 3;
- : IntDat(2)
calculon> if 5 < y then if x > 1 then 2 else 3 else 4;
- : IntDat(2)
calculon> if true then x > y else x < y;
- : BoolDat(false)
calculon> if x>1 then if y=0 then x else x/y else x > y;
- : IntDat(0)
calculon> if x*3+1 = y/2-5+x*4 then x/y > 1 else 1 < y/x ;
- : BoolDat(true)
calculon> def z = let x=5 in x > y/2;
z : BoolDat(false)
calculon> z;
- : BoolDat(false)
calculon> def w = let a= y=10 in if a then y>x else y<x;
w : BoolDat(true)
calculon> w;
- : BoolDat(true)
calculon> if let t=5 in let u=7 in t*u>30 then x=5 else y<12;
- : BoolDat(false)
calculon> 
That was so terrible I think you gave me cancer!
ENDOUT
