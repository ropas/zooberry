(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** * Extends relation for Mem *)

Set Implicit Arguments.

Require Import hpattern vgtac.
Require Import UserProofType.

Module Make (Import PInput : PINPUT).

Definition extends_mem (access : PowLoc.t) (m ext_m : Mem.t) : Prop :=
  forall k (Hk : PowLoc.mem k access), Val.eq (Mem.find k m) (Mem.find k ext_m).

End Make.
