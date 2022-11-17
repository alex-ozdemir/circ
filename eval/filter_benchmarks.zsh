#!/usr/bin/env zsh

set -e

SCRIPT_PATH="${0:A:h}"
CIRC_PATH="$SCRIPT_PATH/../target/release/examples/circ"
IN=all_benchmarks.txt
OUT=benchmarks.txt
rm -f $OUT
touch $OUT

for b in $(cat $IN)
do
    if $CIRC_PATH --verified-r1cs-lowering $b r1cs
    then
        echo $b >> $OUT
    fi
done
