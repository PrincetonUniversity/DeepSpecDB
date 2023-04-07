filename := paper.tex

all:
	latexmk $(filename) -shell-escape -pdf

pdflatex:
	pdflatex --shell-escape $(filename)

loop:
	latexmk $(filename) -shell-escape -pdf -pvc

clean:
	latexmk -bibtex -C
