DKDEP = ~/Git/dedukti/dkdep.native

SRC = src,src/CiC,src/opentheory

LIB = str,dedukti.kernel,dedukti.parser

FILES = $(shell $(DKDEP) -s sttforall/*.dk | cut -d' ' -f 2-)

OUTPUTFILE = final

OUTPUTFILECOQ = $(OUTPUTFILE:%=coq/%.v)

OUTPUTFILEMATITA = $(OUTPUTFILE:%=matita/%.ma)

all: main coq

default: main

main:
	ocamlbuild -r -quiet -Is $(SRC) -pkgs $(LIB) main.native

coq: main
	./main.native -to coq $(FILES) -o $(OUTPUTFILECOQ)

matita: main
	./main.native -to matita $(FILES) -o $(OUTPUTFILEMATITA)

.PHONY: main coq

clean:
	ocamlbuild -clean
