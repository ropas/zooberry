# Copyright (c) 2017-present,
# Programming Research Laboratory (ROPAS), Seoul National University, Korea
# This software is distributed under the term of the BSD-3 clause license.
VS := Access.v DBin.v DFMapAVL.v DFSetAVL.v DItv.v DLat.v DList.v \
      DMap.v DMem.v DNList.v DNat.v DPos.v DPow.v DProd.v DStr.v \
      DSum.v DUnit.v DZ.v Fold.v GenFunc.v Global.v InterCfg.v \
      InterNode.v IntraCfg.v IntraNode.v Monad.v Pos.v Syn.v TStr.v \
      UserInputType.v VocabA.v hpattern.v vgtac.v

.PHONY: all clean

all: Makefile.coq $(VS)
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile
	rm -f $(COQ_GEN)
	coq_makefile INSTALLDEFAULTROOT = .. -R . Basic $(VS) -o Makefile.coq

clean:
	rm -f $(COQ_GEN)
