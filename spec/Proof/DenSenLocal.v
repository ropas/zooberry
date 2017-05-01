(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** * Densification function (Sen -- SenLocal) *)

Set Implicit Arguments.

Require Import vgtac.
Require Import UserProofType Syn.
Require Import Global SemCommon.
Require DomSen SemSenLocal.

Module Make (Import PInput : PINPUT).

Local Open Scope type.

Module Sen := DomSen.Make PInput.

Module SenLocal := SemSenLocal.Make PInput.

Section Pgm.

Variable g : G.t.

Let pgm : InterCfg.t := G.icfg g.

Variable amap : access_map.

Fixpoint densify_mem senl_t callee calls : Mem.t :=
  match calls with
    | nil => Mem.bot
    | cons calln tl =>
      let access := get_all_access callee amap in
      let call_m := senl_t (calln, Outputof, tl) in
      let densified := Mem.subtract access call_m in
      Mem.join densified (densify_mem senl_t (InterNode.get_pid calln) tl)
  end.

Definition densify_state (senl_t : Sen.state_t) : Sen.state_t :=
  fun idx =>
    let '(node, mempos, calls) := idx in
    Mem.join (senl_t idx)
             (densify_mem senl_t (InterNode.get_pid node) calls).

End Pgm.

Local Close Scope type.

End Make.
