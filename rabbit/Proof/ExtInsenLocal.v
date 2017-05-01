(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** * Extends relation for (SenLocal -- InsenLocal) *)

Set Implicit Arguments.

Require Import hpattern vgtac.
Require Import UserProofType Syn Global.
Require Import SemCommon.
Require DomSen DomInsen.
Require ExtMem.

Module Make (Import PInput : PINPUT).

Module Sen := DomSen.Make PInput.

Module Insen := DomInsen.Make PInput.

Include ExtMem.Make PInput.

Definition extends (g : G.t) (amap : access_map)
           (insenl_s : Insen.state_t) (senl_s : Sen.state_t) : Prop :=
  forall n mp calls,
    let access := get_all_access (InterNode.get_pid n) amap in
    extends_mem access (insenl_s (n, mp)) (senl_s (n, mp, calls)).

End Make.
