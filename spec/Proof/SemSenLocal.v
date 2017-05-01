(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** * Abstract semantics (context-sen + localized) *)

Set Implicit Arguments.

Require Import hpattern vgtac.
Require Import Global UserProofType DStr Syn.
Require DomCon SemCon DomSen SemSen.
Require Import SemCommon.

Module Make (Import PInput : PINPUT).

Local Open Scope type.

Module Sen := SemSen.Make PInput.

Include Sen.Dom.

Section Sem.

Variable g : G.t.

Let pgm : InterCfg.t := G.icfg g.

Let mode : UserInputType.update_mode := UserInputType.Strong.

Variable amap : access_map.

Definition postfix_cmd (cn : InterNode.t) (calls : list InterNode.t)
          (s : state_t) : Prop :=
  Sen.postfix_cmd g cn calls s.

Definition postfix_intra_edge (cn : InterNode.t) (calls : list InterNode.t)
           (s : state_t) : Prop :=
  Sen.postfix_intra_edge g cn calls s.

Definition postfix_intra_call (cn : InterNode.t) (calls : list InterNode.t)
           (s : state_t) : Prop :=
  forall callee (Hedge : InterCfg.is_succ pgm cn (callee, IntraNode.Entry))
         retn (Hretn : Some retn = InterCfg.returnof pgm cn),
    let access := get_all_access callee amap in
    let m := (s (cn, Outputof, calls)) in
    let m' := Mem.subtract access m in
    Mem.le m' (s (retn, Inputof, calls)).

Definition postfix_inter_call (cn : InterNode.t) (calls : list InterNode.t)
           (s : state_t) : Prop :=
  forall callee (Hedge : InterCfg.is_succ pgm cn (callee, IntraNode.Entry)),
    let access := get_all_access callee amap in
    let m := (s (cn, Outputof, calls)) in
    let m' := Mem.restrict access m in
    Mem.le m' (s ((callee, IntraNode.Entry), Inputof, cn :: calls)).

Definition postfix_inter_ret (cn : InterNode.t) (calls : list InterNode.t)
           (s : state_t) : Prop :=
  Sen.postfix_inter_ret g cn calls s.

Definition postfix (s : state_t) : Prop :=
  forall (cn : InterNode.t) (calls : list InterNode.t),
    postfix_cmd cn calls s
    /\ postfix_intra_edge cn calls s
    /\ postfix_intra_call cn calls s
    /\ postfix_inter_call cn calls s
    /\ postfix_inter_ret cn calls s.

Definition sound_amap_run (s : state_t) :=
  forall cn calls cmd (Hcmd : Some cmd = InterCfg.get_cmd pgm cn),
    Acc.le
      (Acc.get_acc (run_access mode g cn cmd (s (cn, SemCommon.Inputof, calls))))
      (get_access (InterNode.get_pid cn) amap).

Definition sound_amap_reachable :=
  forall f1 f2 (Hr : InterCfg.reachable pgm f1 f2),
    Acc.le (get_access f2 amap) (get_access f1 amap).

Definition sound_amap (s : state_t) :=
  sound_amap_run s /\ sound_amap_reachable.

End Sem.

Local Close Scope type.

End Make.
