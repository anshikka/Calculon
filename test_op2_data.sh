#!/bin/bash

# create some source files to read via source
cat > test_input_a.tmp <<EOF
1+2+3;
let x = 2 in
if x > 1 then
  3
else
  4;
EOF

cat > test_input_b.tmp <<EOF
def one = 1;
def double = @n n*2;
EOF

cat > test_input_c.tmp <<EOF
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
EOF



T=0                             # global test number

################################################################################
# source tests

((T++))
tnames[T]="source-input-a"
read  -r -d '' input[$T] <<"ENDIN"
source test_input_a.tmp;
whos;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> source test_input_a.tmp;
Reading source file 'test_input_a.tmp'
calculon> 1+2+3;
- : IntDat(6)
calculon> let x = 2 in
if x > 1 then
  3
else
  4;
- : IntDat(3)
calculon> 
End of file 'test_input_a.tmp'
calculon> whos;
calculon> 
That was so terrible I think you gave me cancer!
ENDOUT

((T++))
tnames[T]="source-input-b"
read  -r -d '' input[$T] <<"ENDIN"
source test_input_b.tmp;
whos;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> source test_input_b.tmp;
Reading source file 'test_input_b.tmp'
calculon> def one = 1;
one : IntDat(1)
calculon> def double = @n n*2;
double : Closure(n, <fun>)
calculon> 
End of file 'test_input_b.tmp'
calculon> whos;
    double : Closure(n, <fun>)
       one : IntDat(1)
calculon> 
That was so terrible I think you gave me cancer!
ENDOUT

((T++))
tnames[T]="source-input-c"
read  -r -d '' input[$T] <<"ENDIN"
source test_input_c.tmp;
whos;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> source test_input_c.tmp;
Reading source file 'test_input_c.tmp'
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
calculon> 
End of file 'test_input_c.tmp'
calculon> whos;
addten_std : Closure(x, <fun>)
alwaystwo_std : Closure(a, <fun>)
octuple_std : Closure(n, <fun>)
calculon> 
That was so terrible I think you gave me cancer!
ENDOUT


((T++))
tnames[T]="source-b-merge"
read  -r -d '' input[$T] <<"ENDIN"
def double = 4;
def six = 6;
source test_input_b.tmp;
whos;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> def double = 4;
double : IntDat(4)
calculon> def six = 6;
six : IntDat(6)
calculon> source test_input_b.tmp;
Reading source file 'test_input_b.tmp'
calculon> def one = 1;
one : IntDat(1)
calculon> def double = @n n*2;
double : Closure(n, <fun>)
calculon> 
End of file 'test_input_b.tmp'
calculon> whos;
    double : Closure(n, <fun>)
       one : IntDat(1)
       six : IntDat(6)
calculon> 
That was so terrible I think you gave me cancer!
ENDOUT

((T++))
tnames[T]="source-bc-merge"
read  -r -d '' input[$T] <<"ENDIN"
def double = 4;
def six = 6;
def alwaystwo_std = 2;
source test_input_b.tmp;
source test_input_c.tmp;
def one = 0;
source test_input_b.tmp;
whos;
ENDIN
#
read  -r -d '' output[$T] <<"ENDOUT"
calculon> def double = 4;
double : IntDat(4)
calculon> def six = 6;
six : IntDat(6)
calculon> def alwaystwo_std = 2;
alwaystwo_std : IntDat(2)
calculon> source test_input_b.tmp;
Reading source file 'test_input_b.tmp'
calculon> def one = 1;
one : IntDat(1)
calculon> def double = @n n*2;
double : Closure(n, <fun>)
calculon> 
End of file 'test_input_b.tmp'
calculon> source test_input_c.tmp;
Reading source file 'test_input_c.tmp'
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
calculon> 
End of file 'test_input_c.tmp'
calculon> def one = 0;
one : IntDat(0)
calculon> source test_input_b.tmp;
Reading source file 'test_input_b.tmp'
calculon> def one = 1;
one : IntDat(1)
calculon> def double = @n n*2;
double : Closure(n, <fun>)
calculon> 
End of file 'test_input_b.tmp'
calculon> whos;
addten_std : Closure(x, <fun>)
alwaystwo_std : Closure(a, <fun>)
    double : Closure(n, <fun>)
octuple_std : Closure(n, <fun>)
       one : IntDat(1)
       six : IntDat(6)
calculon> 
That was so terrible I think you gave me cancer!
ENDOUT
