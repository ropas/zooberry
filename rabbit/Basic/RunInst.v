(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
Module RunAccess := Run Acc.MAcc AccMem.

Definition run_access := RunAccess.run.

Module RunOnly := Run MId IdMem.

Definition run_only := RunOnly.run.
