analyze: analyze.R data.csv
	Rscript $<

data.csv: collect.zsh xgcd
	time zsh $< | tee $@

xgcd: xgcd.cpp
	g++ -o $@ $< -Wall -Wextra -pedantic -O3 -lntl -lflint

clean:
	rm -f xgcd data.csv
