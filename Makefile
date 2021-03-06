DKDEP = ~/Git/dedukti/dkdep.native

SRC = src,src/CiC,src/opentheory

LIB = str,dedukti.kernel,dedukti.parser

FILES = $(shell $(DKDEP) -s sttforall/*.dk | cut -d' ' -f 2-)

OUTPUTFILE = final

OUTPUTFILECOQ = $(OUTPUTFILE:%=coq/%.v)

OUTPUTFILEMATITA = $(OUTPUTFILE:%=matita/%.ma)

OUTPUTFILEOT = $(OUTPUTFILE:%=opentheory/%.art)

COQ = coqc

MATITA = matita

all: main coq

default: main

main:
	ocamlbuild -r -quiet -Is $(SRC) -pkgs $(LIB) main.native

coq: main
	./main.native -to coq $(FILES) -o $(OUTPUTFILECOQ)

leibniz-coq:
	$(COQ) coq/leibniz.v

test-coq: leibniz-coq coq
	$(COQ) -Q coq '' $(OUTPUTFILECOQ)

matita: main
	./main.native -to matita $(FILES) -o $(OUTPUTFILEMATITA)

leibniz-matita:
	$(MATITA) matita/leibniz.ma

test-matita: leibniz-matita matita
	$(MATITA) $(OUTPUTFILEMATITA)

opentheory: main
	./main.native -I sttforall -to opentheory $(FILES) -o $(OUTPUTFILEOT)

test-opentheory: opentheory
	opentheory info $(OUTPUTFILEOT)

test: test-coq test-matita test-opentheory

.PHONY: main coq test-coq leibniz-coq matita test-matita leibniz-matita opentheory

clean:
	ocamlbuild -clean
