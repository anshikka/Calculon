#!/bin/bash

T=0                             # global test number

################################################################################
# Function application tests

((T++))
tnames[T]="eval-func-app1"
read  -r -d '' input[$T] <<"ENDIN"
def double = @n 2*n;
double 5;
double 13;
double (1+2+3);
def six = double 3;
double six;
double (double 1);
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> def double = @n 2*n;
double : Closure(n, <fun>)
calculon> double 5;
- : IntDat(10)
calculon> double 13;
- : IntDat(26)
calculon> double (1+2+3);
- : IntDat(12)
calculon> def six = double 3;
six : IntDat(6)
calculon> double six;
- : IntDat(12)
calculon> double (double 1);
- : IntDat(4)
calculon> 
That was so terrible I think you gave me cancer!
ENDOUT

((T++))
tnames[T]="eval-func-app2"
read  -r -d '' input[$T] <<"ENDIN"
(@n 2*n) 4;
def eight = (@n 2*n) 4;
eight;
def cmp_eight = @x x < eight;
show cmp_eight;
cmp_eight 2;
cmp_eight 9;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> (@n 2*n) 4;
- : IntDat(8)
calculon> def eight = (@n 2*n) 4;
eight : IntDat(8)
calculon> eight;
- : IntDat(8)
calculon> def cmp_eight = @x x < eight;
cmp_eight : Closure(x, <fun>)
calculon> show cmp_eight;
Closure(param_name: x, varmap={cmp_eight: Closure(x, <fun>), eight: IntDat(8)} code=
Less
  Varname(x)
  Varname(eight)
)
calculon> cmp_eight 2;
- : BoolDat(true)
calculon> cmp_eight 9;
- : BoolDat(false)
calculon> 
That was so terrible I think you gave me cancer!
ENDOUT

((T++))
tnames[T]="eval-func-app3"
read  -r -d '' input[$T] <<"ENDIN"
def mul = @a @b a*b;
mul 3 7;
mul 9 2;
def doub = mul 2;
show doub;
doub 4;
doub 7;
def triple = mul 3;
triple 5;
triple 9;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> def mul = @a @b a*b;
mul : Closure(a, <fun>)
calculon> mul 3 7;
- : IntDat(21)
calculon> mul 9 2;
- : IntDat(18)
calculon> def doub = mul 2;
doub : Closure(b, <fun>)
calculon> show doub;
Closure(param_name: b, varmap={a: IntDat(2), doub: Closure(b, <fun>), mul: Closure(a, <fun>)} code=
Mul
  Varname(a)
  Varname(b)
)
calculon> doub 4;
- : IntDat(8)
calculon> doub 7;
- : IntDat(14)
calculon> def triple = mul 3;
triple : Closure(b, <fun>)
calculon> triple 5;
- : IntDat(15)
calculon> triple 9;
- : IntDat(27)
calculon> 
That was so terrible I think you gave me cancer!
ENDOUT

((T++))
tnames[T]="eval-func-app4"
read  -r -d '' input[$T] <<"ENDIN"
def select = @a @b @c if a then b else c;
select true  1 2;
select false 1 2;
select true  true false;
select false true false;
select true  (20/4+3) (30/10-1);
select false (20/4+3) (30/10-1);
def second = select false;
second 1 2;
second false true;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> def select = @a @b @c if a then b else c;
select : Closure(a, <fun>)
calculon> select true  1 2;
- : IntDat(1)
calculon> select false 1 2;
- : IntDat(2)
calculon> select true  true false;
- : BoolDat(true)
calculon> select false true false;
- : BoolDat(false)
calculon> select true  (20/4+3) (30/10-1);
- : IntDat(8)
calculon> select false (20/4+3) (30/10-1);
- : IntDat(2)
calculon> def second = select false;
second : Closure(b, <fun>)
calculon> second 1 2;
- : IntDat(2)
calculon> second false true;
- : BoolDat(true)
calculon> 
That was so terrible I think you gave me cancer!
ENDOUT


((T++))
tnames[T]="eval-func-app5"
read  -r -d '' input[$T] <<"ENDIN"
def doubsum = 
  let doub = @n 2*n in
  @n 
    if n=0 
    then 0
    else (doub n)+(doubsum (n-1));
doubsum 5;
doubsum 8;
def transum = @trans @n 
  if n=0
  then 0
  else (trans n) + (transum trans (n-1));
transum (@x 2*x) 5;
transum (@m m+1) 20;
def fact = @n if n=1 then 1 else n*(fact (n-1));
fact 3;
fact 8;
def compute = @t @x @y if let u=7 in t*u>30 then x=5 else y<12;
compute 5 5 5;
compute 5 6 5;
compute 4 6 5;
def sumboth = 
@m @n 
  if m>0 then 
    if n>0 then 
      let diff = m-n in
      if diff > 0 then
        m+(sumboth (m-n) n) 
      else 
        n+(sumboth m (n-m)) 
    else 0 
  else 0;
sumboth 8 2;
sumboth 8 3;
sumboth 8 4;
sumboth 10 4;
def sumten = sumboth 10;
sumten 60;
sumten 20;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> def doubsum = 
  let doub = @n 2*n in
  @n 
    if n=0 
    then 0
    else (doub n)+(doubsum (n-1));
doubsum : Closure(n, <fun>)
calculon> doubsum 5;
- : IntDat(30)
calculon> doubsum 8;
- : IntDat(72)
calculon> def transum = @trans @n 
  if n=0
  then 0
  else (trans n) + (transum trans (n-1));
transum : Closure(trans, <fun>)
calculon> transum (@x 2*x) 5;
- : IntDat(30)
calculon> transum (@m m+1) 20;
- : IntDat(230)
calculon> def fact = @n if n=1 then 1 else n*(fact (n-1));
fact : Closure(n, <fun>)
calculon> fact 3;
- : IntDat(6)
calculon> fact 8;
- : IntDat(40320)
calculon> def compute = @t @x @y if let u=7 in t*u>30 then x=5 else y<12;
compute : Closure(t, <fun>)
calculon> compute 5 5 5;
- : BoolDat(true)
calculon> compute 5 6 5;
- : BoolDat(false)
calculon> compute 4 6 5;
- : BoolDat(true)
calculon> def sumboth = 
@m @n 
  if m>0 then 
    if n>0 then 
      let diff = m-n in
      if diff > 0 then
        m+(sumboth (m-n) n) 
      else 
        n+(sumboth m (n-m)) 
    else 0 
  else 0;
sumboth : Closure(m, <fun>)
calculon> sumboth 8 2;
- : IntDat(20)
calculon> sumboth 8 3;
- : IntDat(19)
calculon> sumboth 8 4;
- : IntDat(12)
calculon> sumboth 10 4;
- : IntDat(22)
calculon> def sumten = sumboth 10;
sumten : Closure(n, <fun>)
calculon> sumten 60;
- : IntDat(210)
calculon> sumten 20;
- : IntDat(30)
calculon> 
That was so terrible I think you gave me cancer!
ENDOUT
