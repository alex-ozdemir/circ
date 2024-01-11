analyze: analyze.R data.csv
	Rscript $<

data.csv: collect.zsh xgcd-ntl xgcd-flint
	time zsh $< | tee $@

xgcd-ntl: xgcd-ntl.cpp
	g++ -o $@ $< -Wall -Wextra -pedantic -O3 -lntl

xgcd-flint: xgcd-flint.cpp
	g++ -o $@ $< -Wall -Wextra -pedantic -O3 -lflint

clean:
	rm -f xgcd-ntl xgcd-flint data.csv
