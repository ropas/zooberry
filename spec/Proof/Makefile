# Copyright (c) 2017-present,
# Programming Research Laboratory (ROPAS), Seoul National University, Korea
# This software is distributed under the term of the BSD-3 clause license.
BASIC_OBJ := $(wildcard ../Basic/*.vo)
VS := CorFin.v CorInsenLocal.v CorSen.v CorSenLocal.v DenInsenLocal.v \
      DenSenLocal.v DomCon.v DomInsen.v DomSen.v ExtFin.v \
      ExtInsenLocal.v ExtMem.v ExtSenLocal.v GamSen.v GenProof.v \
      SemCommon.v SemCon.v SemInsenLocal.v SemSen.v SemSenLocal.v \
      UserProofType.v

.PHONY: all clean

all: Makefile.coq $(VS)
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(BASIC_OBJ)
	rm -f $(COQ_GEN)
	coq_makefile INSTALLDEFAULTROOT = .. -R ../Basic Basic \
	  -R . Proof $(VS) -o Makefile.coq

clean:
	rm -f $(COQ_GEN)
