DKS=$(wildcard *.dk)

# DKOS need not have the same name that the corresponding Dedukti
# files (modulogic.dk becomes zen.dko) but for each file f.dk, dkdep
# f.dk outputs the name of the produced dko file before the ':'
# character.
DKOS=$(shell cut -d ':' -f 1 .depend)

DKDEP=~/Git/dedukti/dkdep.native
DKCHECK=~/Git/dedukti/dkcheck.native
DKINDENT=~/Git/dedukti/dkindent.native
DKMETA=~/Git/dedukti/dkmeta.native
EDILOH=~/Git/dedukti/ediloh.native
ENIQOC=~/Git/dedukti/eniqoc.native

DIR=hol_lambda_typed
all: $(DKOS)

%.dko:
	$(DKCHECK) -e -nl $<
#	$(DKCHECK) -e -errors-in-snf -nl $<
#	$(DKCHECK) -e -nl $<
#	$(DKMETA) -apply-on-rules -meta-file meta.dk $< > $(DIR)/$<
#	$(DKINDENT) $< > $(DIR)/$<
clean:
	rm -f *.dko .depend

depend: .depend

compile-ot:
	$(EDILOH) connectives.dk matita_basics_logic.dk matita_basics_relations.dk matita_basics_bool.dk matita_arithmetics_nat.dk matita_arithmetics_div_and_mod.dk matita_arithmetics_bigops.dk matita_arithmetics_exp.dk matita_arithmetics_sigma_pi.dk matita_arithmetics_primes.dk matita_arithmetics_permutation.dk matita_arithmetics_gcd.dk matita_arithmetics_congruence.dk matita_arithmetics_factorial.dk matita_arithmetics_fermat.dk > final.art

compile-coq:
	$(ENIQOC) connectives.dk matita_basics_logic.dk matita_basics_relations.dk matita_basics_bool.dk matita_arithmetics_nat.dk matita_arithmetics_div_and_mod.dk matita_arithmetics_bigops.dk matita_arithmetics_exp.dk matita_arithmetics_sigma_pi.dk matita_arithmetics_primes.dk matita_arithmetics_permutation.dk matita_arithmetics_gcd.dk matita_arithmetics_congruence.dk matita_arithmetics_factorial.dk matita_arithmetics_fermat_little_theorem.dk > final.v

compile-matita:
	$(ENIQOC) -printer matita connectives.dk matita_basics_logic.dk matita_basics_relations.dk matita_basics_bool.dk matita_arithmetics_nat.dk matita_arithmetics_div_and_mod.dk matita_arithmetics_bigops.dk matita_arithmetics_exp.dk matita_arithmetics_sigma_pi.dk matita_arithmetics_primes.dk matita_arithmetics_permutation.dk matita_arithmetics_gcd.dk matita_arithmetics_congruence.dk matita_arithmetics_factorial.dk matita_arithmetics_fermat_little_theorem.dk > final.ma

compile-agda:
	$(ENIQOC) connectives.dk matita_basics_logic.dk matita_basics_relations.dk matita_basics_bool.dk matita_arithmetics_nat.dk matita_arithmetics_div_and_mod.dk matita_arithmetics_bigops.dk matita_arithmetics_exp.dk matita_arithmetics_sigma_pi.dk matita_arithmetics_primes.dk matita_arithmetics_permutation.dk matita_arithmetics_gcd.dk matita_arithmetics_congruence.dk matita_arithmetics_factorial.dk matita_arithmetics_fermat_little_theorem.dk > final.agda

.depend:
	$(DKDEP) *.dk > ./.depend

-include .depend
