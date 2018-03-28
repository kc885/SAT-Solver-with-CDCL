#!/bin/bash
rm -f result.txt
for i in {1..999}
do
  var="./Solver benchmarks/uf100-0$i.cnf >> result.txt"
  eval $var
done

