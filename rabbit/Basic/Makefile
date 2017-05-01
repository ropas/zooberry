# Copyright (c) 2017-present,
# Programming Research Laboratory (ROPAS), Seoul National University, Korea
# This software is distributed under the term of the BSD-3 clause license.
TEMPLATE := DomMemCommon.v RunInst.v JoinMeetCommon.v RunType.v AlarmType.v
VS := $(filter-out $(TEMPLATE), $(wildcard *.v))
COQ_GEN := *.glob *.vo *.v.d

.PHONY:	coq clean

coq: Makefile.coq $(VS)
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile
	rm -f $(COQ_GEN)
	coq_makefile -R . Basic $(VS) -o Makefile.coq

clean:
	rm -f $(COQ_GEN)
	rm -f Makefile.coq
