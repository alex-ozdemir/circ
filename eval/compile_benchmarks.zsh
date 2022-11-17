#!/usr/bin/env zsh

set -e

SCRIPT_PATH="${0:A:h}"
CIRC_PATH="$SCRIPT_PATH/../target/release/examples/circ"

IN=benchmarks.txt
OUT=compile_results.csv
rm -f $OUT
touch $OUT

echo "benchmark,verification,seconds,kB,constraints" >> $OUT

for b in $(cat $IN)
do
    for verification in yes no
    do
        case $verification in
            yes)
                compiler_output=$(/usr/bin/time -v $CIRC_PATH --verified-r1cs-lowering $b r1cs |& cat)
                ;;
            no)
                compiler_output=$(/usr/bin/time -v $CIRC_PATH $b r1cs |& cat)
                ;;
            *)
                exit 1
                ;;
        esac
        seconds=$(echo "$compiler_output" | rg 'Elap' | rg -o '\d*\.\d*$')
        mrss=$(echo "$compiler_output" | rg 'Maximum resident' | rg -o '\d+$')
        constraints=$(echo "$compiler_output" | rg 'Final R1cs size:' | rg -o '\d+$')
        echo $b,$verification,$seconds,$mrss,$constraints >> $OUT
    done
done
