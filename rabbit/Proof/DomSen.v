(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** * Abstract domain (context-sen) *)

Set Implicit Arguments.

Require Import UserProofType.
Require DomCon.
Require Import SemCommon.

Module Make (Import PInput : PINPUT).

Local Open Scope type.

Definition index_t : Type := InterNode.t * mem_pos * list InterNode.t.

Definition state_t : Type := index_t -> Mem.t.

Definition node_of_index (idx : index_t) : InterNode.t := fst (fst idx).

Definition pos_of_index (idx : index_t) : mem_pos := snd (fst idx).

Definition call_nodes_of_index (idx : index_t) : list InterNode.t := snd idx.

Section Wf.

Variable pgm : InterCfg.t.

Definition wf_call (calln : InterNode.t) : Prop :=
  exists retn, Some retn = InterCfg.returnof pgm calln.

Definition wf_calls (calls : list InterNode.t) : Prop :=
  List.Forall wf_call calls.

Definition wf_index (idx : index_t) : Prop :=
  wf_calls (call_nodes_of_index idx).

Definition wf_state (s : state_t) : Prop :=
  forall idx (Hidx : not (wf_index idx)), Mem.eq (s idx) Mem.bot.

End Wf.

Local Close Scope type.

End Make.
