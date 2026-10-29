REPORT ?= report
# LuaLaTeX находит шрифты CMU в дереве TeX Live сам; XeLaTeX требует, чтобы
# они были установлены в систему (пакет fonts-cmu). Допустимо xelatex или lualatex.
ENGINE ?= lualatex

.PHONY: all data clean dist-clean depext depext-deb

all: $(REPORT).pdf

# Данные для таблиц и графиков из ../bench (результаты compare.py)
data: data/macros.tex

data/macros.tex: data/prepare.py ../bench/results.csv ../bench/samples.json ../bench/full_run.log
	python3 data/prepare.py

$(REPORT).pdf: $(REPORT).tex *.tex *.bib data/macros.tex
	latexmk -$(ENGINE) -synctex=1 -interaction=nonstopmode -file-line-error -shell-escape $<

clean:
	latexmk -c $(REPORT).tex
	@$(RM) *.nav *.snm *.vrb *.synctex.gz _*.data.minted

dist-clean: clean
	latexmk -C $(REPORT).tex

aspell:
	aspell --mode=tex -l ru --home-dir=. --personal=personal_dict.txt  -c $(FILE)

depext: depext-deb

# Не полный список внешних зависимостей
depext-deb:
	sudo apt install fonts-cmu texlive-lang-cyrillic texlive-xetex texlive-luatex texlive-bibtex-extra texlive-science texlive-pictures texlive-plain-generic latexmk --yes
	sudo apt install texlive-fonts-recommended --yes
	sudo apt install hunspell-ru --yes
