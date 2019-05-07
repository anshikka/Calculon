#!/bin/bash

T=0                             # global test number

################################################################################
# Lexing tests

((T++))
tnames[T]="tokens-and-or"
read  -r -d '' input[$T] <<"ENDIN"
tokens true and true;
tokens true or false;
tokens true and true and false;
tokens false or false or true or true;
tokens false or true or false and true or false;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> tokens true and true;
Tokens:
[BoolTok(true); AndTok; BoolTok(true); Semicolon ]
calculon> tokens true or false;
Tokens:
[BoolTok(true); OrTok; BoolTok(false); Semicolon ]
calculon> tokens true and true and false;
Tokens:
[BoolTok(true); AndTok; BoolTok(true); AndTok; BoolTok(false); Semicolon ]
calculon> tokens false or false or true or true;
Tokens:
[BoolTok(false); OrTok; BoolTok(false); OrTok; BoolTok(true); OrTok; BoolTok(true); Semicolon ]
calculon> tokens false or true or false and true or false;
Tokens:
[BoolTok(false); OrTok; BoolTok(true); OrTok; BoolTok(false); AndTok; BoolTok(true); OrTok; BoolTok(false); Semicolon ]
calculon> 
That was so terrible I think you gave me cancer!
ENDOUT

################################################################################
# Parsing tests

((T++))
tnames[T]="parse-and-or"
read  -r -d '' input[$T] <<"ENDIN"
parsetree true and true;
parsetree true or false;
parsetree true and true and false;
parsetree false or false or true or true;
parsetree false or true or false and true or false;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> parsetree true and true;
Parse tree:
And
  BoolExp(true)
  BoolExp(true)

calculon> parsetree true or false;
Parse tree:
Or
  BoolExp(true)
  BoolExp(false)

calculon> parsetree true and true and false;
Parse tree:
And
  And
    BoolExp(true)
    BoolExp(true)
  BoolExp(false)

calculon> parsetree false or false or true or true;
Parse tree:
Or
  Or
    Or
      BoolExp(false)
      BoolExp(false)
    BoolExp(true)
  BoolExp(true)

calculon> parsetree false or true or false and true or false;
Parse tree:
Or
  Or
    Or
      BoolExp(false)
      BoolExp(true)
    And
      BoolExp(false)
      BoolExp(true)
  BoolExp(false)

calculon> 
That was so terrible I think you gave me cancer!
ENDOUT

################################################################################
# Eval tests

((T++))
tnames[T]="eval-and-or"
read  -r -d '' input[$T] <<"ENDIN"
true  and true;
false and false;
false and true;
true  and false;
false or false;
true  or false;
false or true;
true  or true;
true and true and false;
false or false or true or true;
false or true or false and false or true;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> true  and true;
- : BoolDat(true)
calculon> false and false;
- : BoolDat(false)
calculon> false and true;
- : BoolDat(false)
calculon> true  and false;
- : BoolDat(false)
calculon> false or false;
- : BoolDat(false)
calculon> true  or false;
- : BoolDat(true)
calculon> false or true;
- : BoolDat(true)
calculon> true  or true;
- : BoolDat(true)
calculon> true and true and false;
- : BoolDat(false)
calculon> false or false or true or true;
- : BoolDat(true)
calculon> false or true or false and false or true;
- : BoolDat(true)
calculon> 
That was so terrible I think you gave me cancer!
ENDOUT

((T++))
tnames[T]="eval-bool-expr1"
read  -r -d '' input[$T] <<"ENDIN"
def x = true and false;
def y = true or  false;
x;
y;
def z = x or y;
def w = if z and true then 1 else 2;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> def x = true and false;
x : BoolDat(false)
calculon> def y = true or  false;
y : BoolDat(true)
calculon> x;
- : BoolDat(false)
calculon> y;
- : BoolDat(true)
calculon> def z = x or y;
z : BoolDat(true)
calculon> def w = if z and true then 1 else 2;
w : IntDat(1)
calculon> 
That was so terrible I think you gave me cancer!
ENDOUT

((T++))
tnames[T]="eval-bool-expr2"
read  -r -d '' input[$T] <<"ENDIN"
def between = @bot @mid @top  (bot < mid or bot = mid) and (mid = top or mid < top);
show between;
between 1 2 3;
between 5 7 7;
between 5 7 6;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> def between = @bot @mid @top  (bot < mid or bot = mid) and (mid = top or mid < top);
between : Closure(bot, <fun>)
calculon> show between;
Closure(param_name: bot, varmap={between: Closure(bot, <fun>)} code=
Lambda( mid )
  Lambda( top )
    And
      Or
        Less
          Varname(bot)
          Varname(mid)
        Equal
          Varname(bot)
          Varname(mid)
      Or
        Equal
          Varname(mid)
          Varname(top)
        Less
          Varname(mid)
          Varname(top)
)
calculon> between 1 2 3;
- : BoolDat(true)
calculon> between 5 7 7;
- : BoolDat(true)
calculon> between 5 7 6;
- : BoolDat(false)
calculon> 
That was so terrible I think you gave me cancer!
ENDOUT
