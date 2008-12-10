
## targets

default: dvi


## dependencies

include ../Makefile.in

NAME = haskabelle

FILES = $(NAME).tex Thy/document/Haskabelle.tex \
  style.sty ../iman.sty ../extra.sty ../isar.sty \
  ../isabelle.sty ../isabellesym.sty ../pdfsetup.sty \
  ../manual.bib ../proof.sty

dvi: $(NAME).dvi

$(NAME).dvi: $(FILES) isabelle_isar.eps
	$(LATEX) $(NAME)
	$(BIBTEX) $(NAME)
	$(LATEX) $(NAME)
	$(LATEX) $(NAME)

pdf: $(NAME).pdf

$(NAME).pdf: $(FILES) isabelle_isar.pdf
	$(PDFLATEX) $(NAME)
	$(BIBTEX) $(NAME)
	$(PDFLATEX) $(NAME)
	$(PDFLATEX) $(NAME)
	$(FIXBOOKMARKS) $(NAME).out
	$(PDFLATEX) $(NAME)
	$(PDFLATEX) $(NAME)

.PHONY: doc
doc: ../../doc/$(NAME).pdf
../../doc/$(NAME).pdf: $(NAME).pdf
	( cd ../../doc && ln -s ../doc-src/Haskabelle/$(NAME).pdf $(NAME).pdf )
