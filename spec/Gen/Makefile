# Copyright (c) 2017-present,
# Programming Research Laboratory (ROPAS), Seoul National University, Korea
# This software is distributed under the term of the BSD-3 clause license.
INPUT_SRC := $(wildcard $(INPUT)/*.v)
VS := $(filter-out Extract.v, $(wildcard *.v))
COQ_GEN := *.glob *.vo *.v.d

.PHONY:	coq clean

coq: Makefile.coq $(VS)
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(INPUT_SRC)
ifdef INPUT
	rm -f $(COQ_GEN)
	coq_makefile -R ../Basic Basic -R ../$(INPUT) $(INPUT) -R . Gen $(VS) -o Makefile.coq
else
	$(error "The INPUT enrionment should be set to compile.")
endif

ext: coq Extract.v
ifdef INPUT
	coqc -R ../Basic Basic -R ../$(INPUT) $(INPUT) -R . Gen Extract.v
	rm -f ../../analyzer/extract/*.ml*
	mv *.ml* ../../analyzer/extract/
else
	$(error "The INPUT enrionment should be set to compile.")
endif

clean:
	rm -f $(COQ_GEN)
	rm -f Makefile.coq
