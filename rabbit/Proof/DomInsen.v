(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** * Abstract domain (context-insen) *)

Set Implicit Arguments.

Require Import UserProofType.
Require DomCon.
Require Import SemCommon.

Module Make (Import PInput : PINPUT).

Local Open Scope type.

Definition index_t : Type := InterNode.t * mem_pos.
Definition state_t : Type := index_t -> Mem.t.

Definition node_of_index (idx : index_t) : InterNode.t := fst idx.
Definition pos_of_index (idx : index_t) : mem_pos := snd idx.

Local Close Scope type.

End Make.
