.PHONY: ../target/release/examples/circ

../target/release/examples/circ:
	cd .. && cargo build --release --example circ --features 'r1cs smt zok'

#./benchmarks.txt: ../target/release/examples/circ filter_benchmarks.zsh all_benchmarks.txt
#	zsh filter_benchmarks.zsh

./compile_results.csv: ../target/release/examples/circ compile_benchmarks.zsh benchmarks.txt
	zsh compile_benchmarks.zsh
