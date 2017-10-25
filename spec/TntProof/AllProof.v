(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
Require Import UserProofType.
Require SemProof AccProof.

Module AllProof : PINPUT.
Include SemProof.
Include AccProof.
End AllProof.
