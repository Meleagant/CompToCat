.PHONY: all clean

OCAMLFIND = ocamlfind
MLFILES = \
	category.ml

all:
	dune build joujou.exe
	ln -sf _build/default/joujou.exe joujou

doc:
	$(OCAMLFIND) ocamldoc -html -colorize-code -d docs $(MLFILES)

clean:
	dune clean
	rm -f *~ joujou docs/*.html
