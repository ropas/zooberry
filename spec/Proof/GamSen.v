(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** * Gamma relation (Con -- Sen) *)

Set Implicit Arguments.

Require Import UserProofType.
Require DomCon DomSen.

Module Make (Import PInput : PINPUT).

Local Open Scope type.

Module Sen := DomSen.Make PInput.

Definition State_g (con_s : DomCon.state_t) (s : Sen.state_t) : Prop :=
  let '(mempos, (node, step, calls, intra_node_state)) := con_s in
  Mem_g intra_node_state (s (node, mempos, calls)).

Local Close Scope type.

End Make.
