# Copyright (c) 2017-present,
# Programming Research Laboratory (ROPAS), Seoul National University, Korea
# This software is distributed under the term of the BSD-3 clause license.
SPECS := Itv Tnt
SPEC_DIRS := ItvInput TntInput
PROOF_DIRS := ItvProof TntProof

PROOF_CMDS := $(addsuffix _proof, $(SPECS))
EXT_CMDS := $(addsuffix _ext, $(SPECS))

COQ_GEN := *.glob *.vo *.v.d .*.aux Makefile.coq*
export COQ_GEN

.PHONY: all basic proof $(SPEC_DIRS) $(PROOF_DIRS) $(PROOF_CMDS) $(EXT_CMDS) clean

all:
	echo "ERROR: `make Itv_proof` or `make Itv_ext`"
	exit(1)

basic:
	$(MAKE) -C Basic

proof:
	$(MAKE) -C Proof

$(SPEC_DIRS): %Input : basic
	$(MAKE) -C $@ SPEC=$*
	$(MAKE) -C Gen SPEC=$*

$(PROOF_DIRS): %Proof : proof %Input
	$(MAKE) -C $@ SPEC=$*

$(PROOF_CMDS): %_proof : %Proof

$(EXT_CMDS): %_ext : %Input
	$(MAKE) -C Gen ext SPEC=$*

clean:
	rm -f $(addprefix */, $(COQ_GEN))
