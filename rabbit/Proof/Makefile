# Copyright (c) 2017-present,
# Programming Research Laboratory (ROPAS), Seoul National University, Korea
# This software is distributed under the term of the BSD-3 clause license.
TEMPLATE := MemGCommon.v VeqCommon.v
BASIC_SRC := $(wildcard ../Basic/*.v)
VS := $(filter-out $(TEMPLATE), $(wildcard *.v))
DIR := $(notdir $(shell pwd))
COQ_GEN := *.glob *.vo *.v.d

.PHONY:	coq clean

coq: Makefile.coq $(VS)
	$(MAKE) -f Makefile.coq

Makefile.coq: $(BASIC_SRC)
	rm -f $(COQ_GEN)
	coq_makefile -R ../Basic Basic -R . $(DIR) $(VS) -o Makefile.coq

clean:
	rm -f $(COQ_GEN)
	rm -f Makefile.coq
