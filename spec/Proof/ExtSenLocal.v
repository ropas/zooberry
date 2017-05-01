(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** * Extends relation for (Sen -- SenLocal) *)

Set Implicit Arguments.

Require Import hpattern vgtac.
Require Import UserProofType Syn Global.
Require Import SemCommon.
Require DomSen.
Require ExtMem.

Module Make (Import PInput : PINPUT).

Module Sen := DomSen.Make PInput.

Include ExtMem.Make PInput.

Definition extends g (amap : access_map) (senl_s sen_s : Sen.state_t) : Prop :=
  forall n mpos calls (Hn : G.node_in_g g n) (Hcalls : G.nodes_in_g g calls)
         (Hidx: InterCfg.reachables (G.icfg g) calls (InterNode.get_pid n)),
    let idx := (n, mpos, calls) in
    let access := get_all_access (InterNode.get_pid n) amap in
    extends_mem access (senl_s idx) (sen_s idx).

End Make.
