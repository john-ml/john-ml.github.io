all: \
  $(shell find content/*.md content/*.v | sed 's/^content\/\(.*\)/\1.html/') \
  index.html coqdoc.css

clean:
	rm *.html *.glob *.vok *.vos *.vo *.v coqdoc.css

index.html: index.md.html
	cp index.md.html index.html
	python3 patch_index_html.py index.html

%.md.html: content/%.md
	pandoc -s -o $@ $< --filter=graphviz_filter.py

%.v.html: content/%.v
	cp content/$*.v $*.v
	coqc $*.v
	coqdoc --light --utf8 --short --no-index -o $@ $*.v
	python3 patch_coqdoc_html.py $@
	cp css/_coqdoc.css coqdoc.css

coqdoc.css: css/_coqdoc.css
	cp css/_coqdoc.css coqdoc.css
