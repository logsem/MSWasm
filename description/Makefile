TEXFILE=irismswasm
OUT:=.out
OPTIONS=-pdf -synctex=1 -output-directory=$(OUT)
BIBFILES:=$(wildcard *.bib)
DEPENDS=macros.tex 

BACKLINK:=$(OUT)/$(TEXFILE).pdf

all: $(TEXFILE).pdf

$(BACKLINK):
	mkdir -p $(OUT)
	rm -f $(BACKLINK)
	ln -s '../$(TEXFILE).pdf' $(BACKLINK)

# Compile main tex file
$(TEXFILE).pdf: $(TEXFILE).tex $(BACKLINK) $(DEPENDS) $(BIBFILES)
	latexmk $(OPTIONS) $(TEXFILE)


pvc: $(BACKLINK)
	latexmk $(OPTIONS) $(TEXFILE).tex -pvc

pvc-force: $(BACKLINK)
	latexmk $(OPTIONS) $(TEXFILE).tex -pvc -f -quiet -file-line-error

FULL=full

full:
	latexmk $(OPTIONS) $(FULL).tex

# Clean up stray files
clean:
	latexmk -c
	rm -rf $(TEXFILE).pdf
	rm -rf $(OUT)

.PHONY: all clean pvc pvc-force full
