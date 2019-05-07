#!/bin/bash

T=0                             # global test number

################################################################################
# save/load tests

((T++))
tnames[T]="save-load-simple"
read  -r -d '' input[$T] <<"ENDIN"
def one = 1;
whos;
save one.tmp;
undef one;
whos;
load one.tmp;
whos;
one;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> def one = 1;
one : IntDat(1)
calculon> whos;
       one : IntDat(1)
calculon> save one.tmp;
Saved binary data in 'one.tmp'
calculon> undef one;
calculon> whos;
calculon> load one.tmp;
Loading binary data from 'one.tmp'
calculon> whos;
       one : IntDat(1)
calculon> one;
- : IntDat(1)
calculon> 
That was so terrible I think you gave me cancer!
ENDOUT

((T++))
tnames[T]="save-load-clos"
read  -r -d '' input[$T] <<"ENDIN"
def one = 1;
def always_two = @n 2;
def yes = @a true;
def x = 10 / 2;
whos;
save testdefs.tmp;
undef one;
undef always_two;
undef yes;
undef x;
whos;
load testdefs.tmp;
whos;
show always_two;
show yes;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> def one = 1;
one : IntDat(1)
calculon> def always_two = @n 2;
always_two : Closure(n, <fun>)
calculon> def yes = @a true;
yes : Closure(a, <fun>)
calculon> def x = 10 / 2;
x : IntDat(5)
calculon> whos;
always_two : Closure(n, <fun>)
       one : IntDat(1)
         x : IntDat(5)
       yes : Closure(a, <fun>)
calculon> save testdefs.tmp;
Saved binary data in 'testdefs.tmp'
calculon> undef one;
calculon> undef always_two;
calculon> undef yes;
calculon> undef x;
calculon> whos;
calculon> load testdefs.tmp;
Loading binary data from 'testdefs.tmp'
calculon> whos;
always_two : Closure(n, <fun>)
       one : IntDat(1)
         x : IntDat(5)
       yes : Closure(a, <fun>)
calculon> show always_two;
Closure(param_name: n, varmap={always_two: Closure(n, <fun>), one: IntDat(1)} code=
IntExp(2)
)
calculon> show yes;
Closure(param_name: a, varmap={always_two: Closure(n, <fun>), one: IntDat(1), yes: Closure(a, <fun>)} code=
BoolExp(true)
)
calculon> 
That was so terrible I think you gave me cancer!
ENDOUT

((T++))
tnames[T]="save-load-merge"
read  -r -d '' input[$T] <<"ENDIN"
def one = 1;
def two = @n 2;
def three = 3;
def nine = false;
save onetwo.tmp;
undef one;
undef two;
undef three;
undef nine;
def three = 333;
def two = false;
def four = @n 4;
whos;
load onetwo.tmp;
whos;
show two;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> def one = 1;
one : IntDat(1)
calculon> def two = @n 2;
two : Closure(n, <fun>)
calculon> def three = 3;
three : IntDat(3)
calculon> def nine = false;
nine : BoolDat(false)
calculon> save onetwo.tmp;
Saved binary data in 'onetwo.tmp'
calculon> undef one;
calculon> undef two;
calculon> undef three;
calculon> undef nine;
calculon> def three = 333;
three : IntDat(333)
calculon> def two = false;
two : BoolDat(false)
calculon> def four = @n 4;
four : Closure(n, <fun>)
calculon> whos;
      four : Closure(n, <fun>)
     three : IntDat(333)
       two : BoolDat(false)
calculon> load onetwo.tmp;
Loading binary data from 'onetwo.tmp'
calculon> whos;
      four : Closure(n, <fun>)
      nine : BoolDat(false)
       one : IntDat(1)
     three : IntDat(3)
       two : Closure(n, <fun>)
calculon> show two;
Closure(param_name: n, varmap={one: IntDat(1), two: Closure(n, <fun>)} code=
IntExp(2)
)
calculon> 
That was so terrible I think you gave me cancer!
ENDOUT

((T++))
tnames[T]="save-load-varmap"
read  -r -d '' input[$T] <<"ENDIN"
def one = 1;
def incr = @n n+one;
undef one;
save incr.tmp;
undef incr;
whos;
load incr.tmp;
whos;
incr 3;
incr 9;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> def one = 1;
one : IntDat(1)
calculon> def incr = @n n+one;
incr : Closure(n, <fun>)
calculon> undef one;
calculon> save incr.tmp;
Saved binary data in 'incr.tmp'
calculon> undef incr;
calculon> whos;
calculon> load incr.tmp;
Loading binary data from 'incr.tmp'
calculon> whos;
      incr : Closure(n, <fun>)
calculon> incr 3;
- : IntDat(4)
calculon> incr 9;
- : IntDat(10)
calculon> 
That was so terrible I think you gave me cancer!
ENDOUT

((T++))
tnames[T]="save-load-merge"
read  -r -d '' input[$T] <<"ENDIN"
def octuple_std =
@n
  2*2*2*n;

def addten_std = 
@x
  let a = 2*3 in
  let b = 1*1+1*1+1*2 in
  a+b+x;

def alwaystwo_std = 
@a
  if true then
    2
  else
    a+5;

save testsave.tmp;
undef octuple_std;
undef addten_std;
undef alwaystwo_std;
def addten_std = false;
def four = @n 4;
whos;
load testsave.tmp;
whos;
show addten_std;
addten_std 5;
octuple_std (four 0);
def always_true = @n true;
whos;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> def octuple_std =
@n
  2*2*2*n;
octuple_std : Closure(n, <fun>)
calculon> def addten_std = 
@x
  let a = 2*3 in
  let b = 1*1+1*1+1*2 in
  a+b+x;
addten_std : Closure(x, <fun>)
calculon> def alwaystwo_std = 
@a
  if true then
    2
  else
    a+5;
alwaystwo_std : Closure(a, <fun>)
calculon> save testsave.tmp;
Saved binary data in 'testsave.tmp'
calculon> undef octuple_std;
calculon> undef addten_std;
calculon> undef alwaystwo_std;
calculon> def addten_std = false;
addten_std : BoolDat(false)
calculon> def four = @n 4;
four : Closure(n, <fun>)
calculon> whos;
addten_std : BoolDat(false)
      four : Closure(n, <fun>)
calculon> load testsave.tmp;
Loading binary data from 'testsave.tmp'
calculon> whos;
addten_std : Closure(x, <fun>)
alwaystwo_std : Closure(a, <fun>)
      four : Closure(n, <fun>)
octuple_std : Closure(n, <fun>)
calculon> show addten_std;
Closure(param_name: x, varmap={addten_std: Closure(x, <fun>), octuple_std: Closure(n, <fun>)} code=
Letin( a )
  .var_expr:
    Mul
      IntExp(2)
      IntExp(3)
  .in_expr:
    Letin( b )
      .var_expr:
        Add
          Add
            Mul
              IntExp(1)
              IntExp(1)
            Mul
              IntExp(1)
              IntExp(1)
          Mul
            IntExp(1)
            IntExp(2)
      .in_expr:
        Add
          Add
            Varname(a)
            Varname(b)
          Varname(x)
)
calculon> addten_std 5;
- : IntDat(15)
calculon> octuple_std (four 0);
- : IntDat(32)
calculon> def always_true = @n true;
always_true : Closure(n, <fun>)
calculon> whos;
addten_std : Closure(x, <fun>)
always_true : Closure(n, <fun>)
alwaystwo_std : Closure(a, <fun>)
      four : Closure(n, <fun>)
octuple_std : Closure(n, <fun>)
calculon> 
That was so terrible I think you gave me cancer!
ENDOUT

