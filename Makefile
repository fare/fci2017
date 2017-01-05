ae := fci

src = fci.scrbl utils.rkt bibliography.scrbl

#export PLTCOLLECTS:=$(shell pwd):${PLTCOLLECTS}

all: fci.PDF # html # slideshow # PDF
html: ${ae}.html
pdf: ${ae}.pdf
PDF: pdf ${ae}.PDF

install: fci.html fci.pdf
	rsync -av --delete $^ *.js *.css ~/files/fci2017/
	rsync -av --delete ~/files/fci2017/ bespin:files/fci2017/

%.W: %.html
	w3m -T text/html $<

%.wc: %.html
	donuts.pl unhtml < $< | wc

%.PDF: %.pdf
	xpdf -z page -fullscreen $< $${p:-1}

%.pdf: %.scrbl ${src}
	time scribble --dest-name $@ --pdf $<

${ae}.html: ${ae}.scrbl ${src}
%.html: %.scrbl utils.rkt bibliography.scrbl
	time scribble --dest-name $@ --html $<

%.latex: %.scrbl ${src}
	time scribble --latex --dest tmp $<

clean:
	rm -f *.pdf *.html *.tex *.css *.js
	rm -rf tmp

mrproper:
	git clean -xfd

snapl2017.pdf: snapl2017cover.pdf fci.pdf
	pdfjoin -o $@ $^
