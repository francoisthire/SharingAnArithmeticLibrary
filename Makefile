SRC = src,src/CiC,src/opentheory

LIB = str,dedukti.kernel,dedukti.parser

FILES = $(DKDEP) -s sttforall/*.dk | cut -d' ' -f 2-

all:
	ocamlbuild -r -Is $(SRC) -pkgs $(LIB) main.native

clean:
	ocamlbuild -clean
