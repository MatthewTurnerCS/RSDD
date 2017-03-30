#!/bin/bash

cd src
javac FuzzSMT.java
java FuzzSMT QF_FP > ../out.smt
rm *.class
cd ..

# TODO: need to test on multiple solvers, not just z3
./z3/bin/z3 -smt2 out.smt

rm out.smt
