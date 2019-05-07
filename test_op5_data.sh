#!/bin/bash

T=0                             # global test number

################################################################################
# exception tests

((T++))
tnames[T]="opt-tree-1"
read  -r -d '' input[$T] <<"ENDIN"
optparsetree @n 2*2*2*n;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> optparsetree @n 2*2*2*n;
Optimized Parse tree:
Lambda( n )
  Mul
    IntExp(8)
    Varname(n)

calculon> 
That was so terrible I think you gave me cancer!
ENDOUT


((T++))
tnames[T]="opt-tree-2"
read  -r -d '' input[$T] <<"ENDIN"
optparsetree @x
  let a = 2*3 in
  let b = 1*1+1*1+1*2 in
  a+b+x;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> optparsetree @x
  let a = 2*3 in
  let b = 1*1+1*1+1*2 in
  a+b+x;
Optimized Parse tree:
Lambda( x )
  Add
    IntExp(10)
    Varname(x)

calculon> 
That was so terrible I think you gave me cancer!
ENDOUT

((T++))
tnames[T]="opt-tree-3"
read  -r -d '' input[$T] <<"ENDIN"
optparsetree @a
  if true then
    2
  else
    a+5;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> optparsetree @a
  if true then
    2
  else
    a+5;
Optimized Parse tree:
Lambda( a )
  IntExp(2)

calculon> 
That was so terrible I think you gave me cancer!
ENDOUT

((T++))
tnames[T]="optimize1"
read  -r -d '' input[$T] <<"ENDIN"
optimize true;

def octuple_opt =
@n
  2*2*2*n;

show octuple_opt;
octuple 5;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> optimize true;
optimization now 'true'
calculon> def octuple_opt =
@n
  2*2*2*n;
octuple_opt : Closure(n, <fun>)
calculon> show octuple_opt;
Closure(param_name: n, varmap={octuple_opt: Closure(n, <fun>)} code=
Mul
  IntExp(8)
  Varname(n)
)
calculon> octuple 5;
EVAL ERROR: No variable 'octuple' bound
varmap: {octuple_opt: Closure(n, <fun>)}
expression:
Varname(octuple)

calculon> 
That was so terrible I think you gave me cancer!
ENDOUT

((T++))
tnames[T]="optimize2"
read  -r -d '' input[$T] <<"ENDIN"
optimize true;

def addten_opt = 
@x
  let a = 2*3 in
  let b = 1*1+1*1+1*2 in
  a+b+x;

def alwaystwo_opt = 
@a
  if true then
    2
  else
    a+5;

show addten_opt;
show alwaystwo_opt;

addten_opt 5;

alwaystwo_opt 5;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> optimize true;
optimization now 'true'
calculon> def addten_opt = 
@x
  let a = 2*3 in
  let b = 1*1+1*1+1*2 in
  a+b+x;
addten_opt : Closure(x, <fun>)
calculon> def alwaystwo_opt = 
@a
  if true then
    2
  else
    a+5;
alwaystwo_opt : Closure(a, <fun>)
calculon> show addten_opt;
Closure(param_name: x, varmap={addten_opt: Closure(x, <fun>)} code=
Add
  IntExp(10)
  Varname(x)
)
calculon> show alwaystwo_opt;
Closure(param_name: a, varmap={addten_opt: Closure(x, <fun>), alwaystwo_opt: Closure(a, <fun>)} code=
IntExp(2)
)
calculon> addten_opt 5;
- : IntDat(15)
calculon> alwaystwo_opt 5;
- : IntDat(2)
calculon> 
That was so terrible I think you gave me cancer!
ENDOUT
