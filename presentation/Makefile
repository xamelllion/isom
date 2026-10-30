NAME ?= presentation
# LuaLaTeX находит шрифты CMU в дереве TeX Live сам; XeLaTeX требует, чтобы
# они были установлены в систему (пакет fonts-cmu). Допустимо xelatex или lualatex.
ENGINE ?= lualatex

# Данные для графиков и числа берутся из отчёта (их строит ../report/data/prepare.py)
DATA := macros.tex results_table.tex speedup_points.csv speedup_means.csv \
        scale_rigid.csv scale_cycle.csv scale_brothers.csv scale_ladder.csv

.PHONY: all data clean dist-clean depext depext-deb

all: $(NAME).pdf

data: $(addprefix data/,$(DATA))

data/%: ../report/data/%
	cp $< $@

$(NAME).pdf: $(NAME).tex preamble.tex $(addprefix data/,$(DATA))
	latexmk -$(ENGINE) -synctex=1 -interaction=nonstopmode -file-line-error $(NAME).tex

clean:
	latexmk -c $(NAME).tex
	@$(RM) *.nav *.snm *.vrb *.synctex.gz

dist-clean: clean
	latexmk -C $(NAME).tex

aspell:
	aspell --mode=tex -l ru --home-dir=. --personal=personal_dict.txt  -c $(FILE)

depext: depext-deb

# Не полный список внешних зависимостей
depext-deb:
	sudo apt update
	sudo apt install fonts-cmu texlive-lang-cyrillic texlive-xetex texlive-luatex texlive-latex-extra texlive-pictures texlive-plain-generic latexmk --yes
	sudo apt install hunspell-ru --yes
