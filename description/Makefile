TEXFILE=irismswasm
BIBFILES:=$(wildcard *.bib)
DEPENDS=macros.tex 


all: $(TEXFILE).pdf

# Compile main tex file
$(TEXFILE).pdf: $(TEXFILE).tex $(DEPENDS) $(BIBFILES)
	latex $(TEXFILE)
	bibtex $(TEXFILE)
	pdflatex $(TEXFILE)
	pdflatex $(TEXFILE)


bib:
	latex $(TEXFILE)
	bibtex $(TEXFILE)

# Clean up stray files
clean:
	rm -rf $(TEXFILE).pdf
	rm -rf *.aux *.dvi *.bbl *.log

.PHONY: all clean pvc pvc-force full
