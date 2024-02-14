#!/usr/bin/env zsh

set -ex

disable -r time

MODE=release # debug or release
BIN=./target/$MODE/examples/circ
ZK_BIN=./target/$MODE/examples/zk

# Test prove workflow, given an example name
function pf_test {
    for proof_impl in groth16 mirage
    do
        ex_name=$1
        $BIN examples/ir/pf/$ex_name.circir r1cs --action setup --proof-impl $proof_impl
        $ZK_BIN --inputs examples/ZoKrates/pf/$ex_name.zok.pin --action prove --proof-impl $proof_impl
        $ZK_BIN --inputs examples/ZoKrates/pf/$ex_name.zok.vin --action verify --proof-impl $proof_impl
        rm -rf P V pi
    done
}

pf_test 3_plus
