WORKERS := 4

TLA := docker run --rm -it --workdir /mnt -v ${PWD}:/mnt talex5/tla

.PHONY: all check pdfs tlaps

all: check pdfs tlaps

# Run the TLC model checker
check:
	${TLA} tlc -workers ${WORKERS} vchan.tla -config models/SpecOK.cfg
	${TLA} tlc -workers ${WORKERS} vchan.tla -config models/QubesDB.cfg

# Run the TLAPS proof checker
tlaps:
	${TLA} tlapm -I /usr/local/lib/tlaps vchan.tla

# Generate a PDF file from a .tla file
%.pdf: %.tla
	[ -d metadir ] || mkdir metadir
	${TLA} java tla2tex.TLA -noPcalShade -shade -latexCommand pdflatex -latexOutputExt pdf -metadir metadir $<

pdfs: vchan.pdf
