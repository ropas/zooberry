# Copyright (c) 2017-present,
# Programming Research Laboratory (ROPAS), Seoul National University, Korea
# This software is distributed under the term of the BSD-3 clause license.
INPUTS := $(wildcard *Input)
INPUTS_EXT := $(addsuffix _ext, $(INPUTS))
INPUTS_CLEAN := $(addsuffix _clean, $(INPUTS))
INPUTS_PROOF := $(addsuffix Proof, $(INPUTS))

.PHONY: basic $(INPUTS) $(INPUTS_EXT) $(INPUTS_EXT)

basic:
	$(MAKE) -C Basic

$(INPUTS): % : basic
	$(MAKE) -C $*
	$(MAKE) -C Gen INPUT="$*"

$(INPUTS_EXT): %_ext : %
	$(MAKE) ext -C Gen INPUT="$*"

$(INPUTS_CLEAN): %_clean : clean
	$(MAKE) clean -C $*

proof:
	$(MAKE) -C Proof

$(INPUTS_PROOF): %Proof : % proof
	$(MAKE) -C $@ INPUT="$*"

clean:
	$(MAKE) clean -C Basic
	$(MAKE) clean -C Gen
