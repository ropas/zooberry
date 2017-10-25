# Copyright (c) 2017-present,
# Programming Research Laboratory (ROPAS), Seoul National University, Korea
# This software is distributed under the term of the BSD-3 clause license.
BASIC_OBJ := $(wildcard ../Basic/*.vo)
SPEC_OBJ := $(wildcard ../$(SPEC)Input/*.vo)

.PHONY: all ext clean

all: Makefile.coq Vali.v
	$(MAKE) -f Makefile.coq

$(SPEC).current:
	rm -f *.current
	touch $(SPEC).current

Makefile.coq: Makefile $(BASIC_OBJ) $(SPEC_OBJ) $(SPEC).current
	rm -f $(COQ_GEN)
	coq_makefile INSTALLDEFAULTROOT = .. -R ../Basic Basic \
	  -R ../$(SPEC)Input $(SPEC)Input -R . Gen Vali.v -o Makefile.coq

ext: all Extract.v
	coqc -R ../Basic Basic -R ../$(SPEC)Input $(SPEC)Input -R . Gen \
	  Extract.v
	rm -f ../../analyzer/extract/*.ml*
	mv *.ml* ../../analyzer/extract/

clean:
	rm -f $(COQ_GEN)
