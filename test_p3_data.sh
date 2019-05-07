#!/bin/bash

T=0                             # global test number

################################################################################
# Closure parse tests

((T++))
tnames[T]="parse-clos-simple"
read  -r -d '' input[$T] <<"ENDIN"
parsetree @n n;
parsetree @fry fry;
parsetree @n 2*n;
parsetree @n 2*n+3;
parsetree @n let twon=2*n in twon+3;
parsetree @n if n>0 then 100/n else 0;
parsetree @ param if param>0 then 100/param else 0;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> parsetree @n n;
Parse tree:
Lambda( n )
  Varname(n)

calculon> parsetree @fry fry;
Parse tree:
Lambda( fry )
  Varname(fry)

calculon> parsetree @n 2*n;
Parse tree:
Lambda( n )
  Mul
    IntExp(2)
    Varname(n)

calculon> parsetree @n 2*n+3;
Parse tree:
Lambda( n )
  Add
    Mul
      IntExp(2)
      Varname(n)
    IntExp(3)

calculon> parsetree @n let twon=2*n in twon+3;
Parse tree:
Lambda( n )
  Letin( twon )
    .var_expr:
      Mul
        IntExp(2)
        Varname(n)
    .in_expr:
      Add
        Varname(twon)
        IntExp(3)

calculon> parsetree @n if n>0 then 100/n else 0;
Parse tree:
Lambda( n )
  Cond
    .if_expr:
      Greater
        Varname(n)
        IntExp(0)
    .then_expr:
      Div
        IntExp(100)
        Varname(n)
    .else_expr:
      IntExp(0)

calculon> parsetree @ param if param>0 then 100/param else 0;
Parse tree:
Lambda( param )
  Cond
    .if_expr:
      Greater
        Varname(param)
        IntExp(0)
    .then_expr:
      Div
        IntExp(100)
        Varname(param)
    .else_expr:
      IntExp(0)

calculon> 
That was so terrible I think you gave me cancer!
ENDOUT

((T++))
tnames[T]="parse-clos-complex"
read  -r -d '' input[$T] <<"ENDIN"
parsetree @a @b if a>b then a else b;
parsetree @x let twox=2*x in @y if twox = y then x else y;
parsetree @x @y if x>y then @w x*w else @w y*w;
parsetree @x @y @z if y=0 then z else x/y;
parsetree @x @y @z if y then z else x/y;

ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> parsetree @a @b if a>b then a else b;
Parse tree:
Lambda( a )
  Lambda( b )
    Cond
      .if_expr:
        Greater
          Varname(a)
          Varname(b)
      .then_expr:
        Varname(a)
      .else_expr:
        Varname(b)

calculon> parsetree @x let twox=2*x in @y if twox = y then x else y;
Parse tree:
Lambda( x )
  Letin( twox )
    .var_expr:
      Mul
        IntExp(2)
        Varname(x)
    .in_expr:
      Lambda( y )
        Cond
          .if_expr:
            Equal
              Varname(twox)
              Varname(y)
          .then_expr:
            Varname(x)
          .else_expr:
            Varname(y)

calculon> parsetree @x @y if x>y then @w x*w else @w y*w;
Parse tree:
Lambda( x )
  Lambda( y )
    Cond
      .if_expr:
        Greater
          Varname(x)
          Varname(y)
      .then_expr:
        Lambda( w )
          Mul
            Varname(x)
            Varname(w)
      .else_expr:
        Lambda( w )
          Mul
            Varname(y)
            Varname(w)

calculon> parsetree @x @y @z if y=0 then z else x/y;
Parse tree:
Lambda( x )
  Lambda( y )
    Lambda( z )
      Cond
        .if_expr:
          Equal
            Varname(y)
            IntExp(0)
        .then_expr:
          Varname(z)
        .else_expr:
          Div
            Varname(x)
            Varname(y)

calculon> parsetree @x @y @z if y then z else x/y;
Parse tree:
Lambda( x )
  Lambda( y )
    Lambda( z )
      Cond
        .if_expr:
          Varname(y)
        .then_expr:
          Varname(z)
        .else_expr:
          Div
            Varname(x)
            Varname(y)

calculon> 
That was so terrible I think you gave me cancer!
ENDOUT

################################################################################
# Eval tests

((T++))
tnames[T]="eval-clos-simple"
read  -r -d '' input[$T] <<"ENDIN"
@n n;
@fry fry;
@n 2*n;
@n 2*n+3;
@n let twon=2*n in twon+3;
@n if n>0 then 100/n else 0;
@ param if param>0 then 100/param else 0;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> @n n;
- : Closure(n, <fun>)
calculon> @fry fry;
- : Closure(fry, <fun>)
calculon> @n 2*n;
- : Closure(n, <fun>)
calculon> @n 2*n+3;
- : Closure(n, <fun>)
calculon> @n let twon=2*n in twon+3;
- : Closure(n, <fun>)
calculon> @n if n>0 then 100/n else 0;
- : Closure(n, <fun>)
calculon> @ param if param>0 then 100/param else 0;
- : Closure(param, <fun>)
calculon> 
That was so terrible I think you gave me cancer!
ENDOUT

((T++))
tnames[T]="eval-clos-complex"
read  -r -d '' input[$T] <<"ENDIN"
@a @b if a>b then a else b;
@x let twox=2*x in @y if twox = y then x else y;
@x @y if x>y then @w x*w else @w y*w;
@x @y @z if y=0 then z else x/y;
@x @y @z if y then z else x/y;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> @a @b if a>b then a else b;
- : Closure(a, <fun>)
calculon> @x let twox=2*x in @y if twox = y then x else y;
- : Closure(x, <fun>)
calculon> @x @y if x>y then @w x*w else @w y*w;
- : Closure(x, <fun>)
calculon> @x @y @z if y=0 then z else x/y;
- : Closure(x, <fun>)
calculon> @x @y @z if y then z else x/y;
- : Closure(x, <fun>)
calculon> 
That was so terrible I think you gave me cancer!
ENDOUT

((T++))
tnames[T]="eval-clos-def-show"
read  -r -d '' input[$T] <<"ENDIN"
def x = 10;
def addx = @n n+x;
show addx;
def maxx = @b max b x;
show maxx;
undef x;
show addx;
show maxx;
def max = @a @b if a>b then a else b;
show max;
def divxy = @x @y @z if y then z else x/y;
show divxy;
def fact = @n if n=1 then 1 else n*(fact (n-1));
show fact;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> def x = 10;
x : IntDat(10)
calculon> def addx = @n n+x;
addx : Closure(n, <fun>)
calculon> show addx;
Closure(param_name: n, varmap={addx: Closure(n, <fun>), x: IntDat(10)} code=
Add
  Varname(n)
  Varname(x)
)
calculon> def maxx = @b max b x;
maxx : Closure(b, <fun>)
calculon> show maxx;
Closure(param_name: b, varmap={addx: Closure(n, <fun>), maxx: Closure(b, <fun>), x: IntDat(10)} code=
Apply
  .func_expr:
    Apply
      .func_expr:
        Varname(max)
      .param_expr:
        Varname(b)
  .param_expr:
    Varname(x)
)
calculon> undef x;
calculon> show addx;
Closure(param_name: n, varmap={addx: Closure(n, <fun>), x: IntDat(10)} code=
Add
  Varname(n)
  Varname(x)
)
calculon> show maxx;
Closure(param_name: b, varmap={addx: Closure(n, <fun>), maxx: Closure(b, <fun>), x: IntDat(10)} code=
Apply
  .func_expr:
    Apply
      .func_expr:
        Varname(max)
      .param_expr:
        Varname(b)
  .param_expr:
    Varname(x)
)
calculon> def max = @a @b if a>b then a else b;
max : Closure(a, <fun>)
calculon> show max;
Closure(param_name: a, varmap={addx: Closure(n, <fun>), max: Closure(a, <fun>), maxx: Closure(b, <fun>)} code=
Lambda( b )
  Cond
    .if_expr:
      Greater
        Varname(a)
        Varname(b)
    .then_expr:
      Varname(a)
    .else_expr:
      Varname(b)
)
calculon> def divxy = @x @y @z if y then z else x/y;
divxy : Closure(x, <fun>)
calculon> show divxy;
Closure(param_name: x, varmap={addx: Closure(n, <fun>), divxy: Closure(x, <fun>), max: Closure(a, <fun>), maxx: Closure(b, <fun>)} code=
Lambda( y )
  Lambda( z )
    Cond
      .if_expr:
        Varname(y)
      .then_expr:
        Varname(z)
      .else_expr:
        Div
          Varname(x)
          Varname(y)
)
calculon> def fact = @n if n=1 then 1 else n*(fact (n-1));
fact : Closure(n, <fun>)
calculon> show fact;
Closure(param_name: n, varmap={addx: Closure(n, <fun>), divxy: Closure(x, <fun>), fact: Closure(n, <fun>), max: Closure(a, <fun>), maxx: Closure(b, <fun>)} code=
Cond
  .if_expr:
    Equal
      Varname(n)
      IntExp(1)
  .then_expr:
    IntExp(1)
  .else_expr:
    Mul
      Varname(n)
      Apply
        .func_expr:
          Varname(fact)
        .param_expr:
          Sub
            Varname(n)
            IntExp(1)
)
calculon> 
That was so terrible I think you gave me cancer!
ENDOUT
