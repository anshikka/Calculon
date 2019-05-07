#!/bin/bash

T=0                             # global test number

################################################################################
# recursive let application tests

((T++))
tnames[T]="regression"
read  -r -d '' input[$T] <<"ENDIN"
let doub = @n n*2 in
doub 10;
let decr_zero = @x if x>0 then x-1 else 0 in
decr_zero 5;
let div = @a @b if b>0 then a/b else 1 in
div 4 0;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> let doub = @n n*2 in
doub 10;
- : IntDat(20)
calculon> let decr_zero = @x if x>0 then x-1 else 0 in
decr_zero 5;
- : IntDat(4)
calculon> let div = @a @b if b>0 then a/b else 1 in
div 4 0;
- : IntDat(1)
calculon> 
That was so terrible I think you gave me cancer!
ENDOUT

((T++))
tnames[T]="rec-let1"
read  -r -d '' input[$T] <<"ENDIN"
let sumit = @n
  if n=0 
  then 0
  else n + (sumit (n-1))
in
sumit 10;
whos;
let sumit = @n
  if n=0 
  then 0
  else n + (sumit (n-1))
in
sumit 20;
whos;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> let sumit = @n
  if n=0 
  then 0
  else n + (sumit (n-1))
in
sumit 10;
- : IntDat(55)
calculon> whos;
calculon> let sumit = @n
  if n=0 
  then 0
  else n + (sumit (n-1))
in
sumit 20;
- : IntDat(210)
calculon> whos;
calculon> 
That was so terrible I think you gave me cancer!
ENDOUT

((T++))
tnames[T]="rec-let2"
read  -r -d '' input[$T] <<"ENDIN"
def outer_fact =
  let fact =
    @n
      if n=1
      then 1 
      else n*(fact (n-1)) 
  in 
  fact;
show outer_fact;
outer_fact 5;
outer_fact 9;
outer_fact 4;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> def outer_fact =
  let fact =
    @n
      if n=1
      then 1 
      else n*(fact (n-1)) 
  in 
  fact;
outer_fact : Closure(n, <fun>)
calculon> show outer_fact;
Closure(param_name: n, varmap={fact: Closure(n, <fun>), outer_fact: Closure(n, <fun>)} code=
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
calculon> outer_fact 5;
- : IntDat(120)
calculon> outer_fact 9;
- : IntDat(362880)
calculon> outer_fact 4;
- : IntDat(24)
calculon> 
That was so terrible I think you gave me cancer!
ENDOUT

((T++))
tnames[T]="rec-let3"
read  -r -d '' input[$T] <<"ENDIN"
def sum_facts =
  let fact =
    @n
      if n=1
      then 1 
      else n*(fact (n-1)) 
  in 
  @i @stop
    if i > stop
    then 0 
    else let facti = fact i in
         let rest = sum_facts (i+1) stop in
         facti + rest;
sum_facts 10 2;
sum_facts 1 3;
sum_facts 1 5;
sum_facts 5 10;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> def sum_facts =
  let fact =
    @n
      if n=1
      then 1 
      else n*(fact (n-1)) 
  in 
  @i @stop
    if i > stop
    then 0 
    else let facti = fact i in
         let rest = sum_facts (i+1) stop in
         facti + rest;
sum_facts : Closure(i, <fun>)
calculon> sum_facts 10 2;
- : IntDat(0)
calculon> sum_facts 1 3;
- : IntDat(9)
calculon> sum_facts 1 5;
- : IntDat(153)
calculon> sum_facts 5 10;
- : IntDat(4037880)
calculon> 
That was so terrible I think you gave me cancer!
ENDOUT

((T++))
tnames[T]="rec-let4"
read  -r -d '' input[$T] <<"ENDIN"
def transum = 
@trans
  let help = @n
    if n=0 
    then 0
    else (trans n) + (help (n-1))
  in
  help;
def double = @n n*2;
def incr   = @x x+1;
transum double 10;
transum incr 20;
let fib = @n
  if n=0 then 0
  else if n=1 then 1
  else (fib (n-1)) + (fib (n-2))
in
transum fib 8;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> def transum = 
@trans
  let help = @n
    if n=0 
    then 0
    else (trans n) + (help (n-1))
  in
  help;
transum : Closure(trans, <fun>)
calculon> def double = @n n*2;
double : Closure(n, <fun>)
calculon> def incr   = @x x+1;
incr : Closure(x, <fun>)
calculon> transum double 10;
- : IntDat(110)
calculon> transum incr 20;
- : IntDat(230)
calculon> let fib = @n
  if n=0 then 0
  else if n=1 then 1
  else (fib (n-1)) + (fib (n-2))
in
transum fib 8;
- : IntDat(54)
calculon> 
That was so terrible I think you gave me cancer!
ENDOUT


