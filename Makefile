all: \
  $(shell find *.md *.v | sed 's/\(.*\)/\1.html/') \
  index.html coqdoc.css

clean:
	rm *.html *.glob *.vok *.vos *.vo coqdoc.css

index.html: index.md.html
	cp index.md.html index.html

%.md.html: %.md
	pandoc -s -o $@ $<

%.v.html: %.v
	coqc $<
	coqdoc --short --no-index -o $@ $<
	cp _coqdoc.css coqdoc.css

coqdoc.css: _coqdoc.css
	cp _coqdoc.css coqdoc.css
