.PHONY: main.pdf auto clean sync
main: main.pdf

intro.pdf: main.pdf
	pdfjam $< 1-2 -o $@

main.pdf:
	latexmk -pdf -halt-on-error -interaction=nonstopmode -shell-escape main.tex

auto:
	latexmk -pvc -pdf -halt-on-error -interaction=nonstopmode -shell-escape main.tex

clean:
	latexmk -C main.tex
	rm -rf main.bbl

abstract.md: abstract.tex
	pandoc --verbose -o $@ <(cat $< | sed 's/\\example/replacement/') -f latex

sync:
	git pull -r && git push
