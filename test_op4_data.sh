#!/bin/bash

T=0                             # global test number

################################################################################
# exception tests

((T++))
tnames[T]="lex-errors"
read  -r -d '' input[$T] <<"ENDIN"
#;
1+4 & true;
@n if 4*5 > 19 then ( 10! ) else 12$;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> #;
LEX ERROR: char '#' not recognized, at position 0 in the input '#;'
calculon> 1+4 & true;
LEX ERROR: char '&' not recognized, at position 4 in the input '1+4 & true;'
calculon> @n if 4*5 > 19 then ( 10! ) else 12$;
LEX ERROR: char '!' not recognized, at position 24 in the input '@n if 4*5 > 19 then ( 10! ) else 12$;'
calculon> 
That was so terrible I think you gave me cancer!
ENDOUT

((T++))
tnames[T]="parse-errors1"
read  -r -d '' input[$T] <<"ENDIN"
1+2* / 4;
7*(8+2;
@ 5*2;
/ 100 5;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> 1+2* / 4;
PARSE ERROR: syntax error
tokens: [Slash; IntTok(4); Semicolon ]
calculon> 7*(8+2;
PARSE ERROR: unclosed parentheses
tokens: [IntTok(8); Plus; IntTok(2); Semicolon ]
calculon> @ 5*2;
PARSE ERROR: Expected identifier in lambda expression after @
tokens: [At; IntTok(5); Times; IntTok(2); Semicolon ]
calculon> / 100 5;
PARSE ERROR: syntax error
tokens: [Slash; IntTok(100); IntTok(5); Semicolon ]
calculon> 
That was so terrible I think you gave me cancer!
ENDOUT

((T++))
tnames[T]="parse-errors2"
read  -r -d '' input[$T] <<"ENDIN"
let x = 5 if y > 12 then true else false;
if x < y < z then 1 else 2;
let if = 2 in if + 5;
if true then then 1 else 2;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> let x = 5 if y > 12 then true else false;
PARSE ERROR: Expected 'in' after 'let'
tokens: [If; Ident(y); GreatThan; IntTok(12); Then; BoolTok(true); Else ; BoolTok(false); Semicolon ]
calculon> if x < y < z then 1 else 2;
PARSE ERROR: Expected 'then' 
tokens: [LessThan; Ident(z); Then; IntTok(1); Else ; IntTok(2); Semicolon ]
calculon> let if = 2 in if + 5;
PARSE ERROR: syntax error
tokens: [Let; If; Equal; IntTok(2); In; If; Plus; IntTok(5); Semicolon ]
calculon> if true then then 1 else 2;
PARSE ERROR: syntax error
tokens: [Then; IntTok(1); Else ; IntTok(2); Semicolon ]
calculon> 
That was so terrible I think you gave me cancer!
ENDOUT

((T++))
tnames[T]="eval-errors1"
read  -r -d '' input[$T] <<"ENDIN"
1+2+true;
let y = true in 1 * 2 * y;
if 5 then 1 else 2;
let x = 5 in if x then 1 else 2;
5 < false;
let z = false in 5 < z;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> 1+2+true;
EVAL ERROR: Expect Int for right arithmetic expression, found 'BoolDat(true)'
varmap: {}
expression:
Add
  Add
    IntExp(1)
    IntExp(2)
  BoolExp(true)

calculon> let y = true in 1 * 2 * y;
EVAL ERROR: Expect Int for right arithmetic expression, found 'BoolDat(true)'
varmap: {y: BoolDat(true)}
expression:
Mul
  Mul
    IntExp(1)
    IntExp(2)
  Varname(y)

calculon> if 5 then 1 else 2;
EVAL ERROR: Expected Bool for if(), found 'IntDat(5)'
varmap: {}
expression:
Cond
  .if_expr:
    IntExp(5)
  .then_expr:
    IntExp(1)
  .else_expr:
    IntExp(2)

calculon> let x = 5 in if x then 1 else 2;
EVAL ERROR: Expected Bool for if(), found 'IntDat(5)'
varmap: {x: IntDat(5)}
expression:
Cond
  .if_expr:
    Varname(x)
  .then_expr:
    IntExp(1)
  .else_expr:
    IntExp(2)

calculon> 5 < false;
EVAL ERROR: Expect Int for right arithmetic expression, found 'BoolDat(false)'
varmap: {}
expression:
Less
  IntExp(5)
  BoolExp(false)

calculon> let z = false in 5 < z;
EVAL ERROR: Expect Int for right arithmetic expression, found 'BoolDat(false)'
varmap: {z: BoolDat(false)}
expression:
Less
  IntExp(5)
  Varname(z)

calculon> 
That was so terrible I think you gave me cancer!
ENDOUT

((T++))
tnames[T]="eval-errors2"
read  -r -d '' input[$T] <<"ENDIN"
def x = true;
def y = 5;
def f = @n n*y / x;
f 10;
def mul = @a @b a * b;
mul 2 5;
mul 2 false;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> def x = true;
x : BoolDat(true)
calculon> def y = 5;
y : IntDat(5)
calculon> def f = @n n*y / x;
f : Closure(n, <fun>)
calculon> f 10;
EVAL ERROR: Expect Int for right arithmetic expression, found 'BoolDat(true)'
varmap: {f: Closure(n, <fun>), n: IntDat(10), x: BoolDat(true), y: IntDat(5)}
expression:
Div
  Mul
    Varname(n)
    Varname(y)
  Varname(x)

calculon> def mul = @a @b a * b;
mul : Closure(a, <fun>)
calculon> mul 2 5;
- : IntDat(10)
calculon> mul 2 false;
EVAL ERROR: Expect Int for right arithmetic expression, found 'BoolDat(false)'
varmap: {a: IntDat(2), b: BoolDat(false), f: Closure(n, <fun>), mul: Closure(a, <fun>), x: BoolDat(true), y: IntDat(5)}
expression:
Mul
  Varname(a)
  Varname(b)

calculon> 
That was so terrible I think you gave me cancer!
ENDOUT

