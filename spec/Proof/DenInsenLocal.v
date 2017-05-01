(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** * Densification function (SenLocal -- InsenLocal) *)

Set Implicit Arguments.

Require Import UserProofType Syn.
Require Import SemCommon.
Require DomSen DomInsen.

Module Make (Import PInput : PINPUT).

Local Open Scope type.

Module Sen := DomSen.Make PInput.
Module Insen := DomInsen.Make PInput.

Definition densify_state (insenl_t : Insen.state_t) : Sen.state_t :=
  fun s =>
    let '(n, p, _) := s in
    insenl_t (n, p).

Local Close Scope type.

End Make.
