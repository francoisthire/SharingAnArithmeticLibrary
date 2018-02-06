DKDEP = ~/Git/dedukti/dkdep.native

SRC = src,src/CiC,src/opentheory

LIB = str,dedukti.kernel,dedukti.parser

FILES = $(shell $(DKDEP) -s sttforall/*.dk | cut -d' ' -f 2-)

OUTPUTFILE = final

OUTPUTFILECOQ = $(OUTPUTFILE:%=coq/%.v)

OUTPUTFILEMATITA = $(OUTPUTFILE:%=matita/%.ma)

COQ = coqc

all: main coq

default: main

main:
	ocamlbuild -r -quiet -Is $(SRC) -pkgs $(LIB) main.native

coq: main
	./main.native -to coq $(FILES) -o $(OUTPUTFILECOQ)

matita: main
	./main.native -to matita $(FILES) -o $(OUTPUTFILEMATITA)

leibniz-coq:
	$(COQ) coq/leibniz.v

test-coq: leibniz-coq coq
	$(COQ) -Q coq '' $(OUTPUTFILECOQ)

.PHONY: main coq test-coq leibniz-coq

clean:
	ocamlbuild -clean
