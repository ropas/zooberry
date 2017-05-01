(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** * Abstract semantics (context-insen + localized) *)

Set Implicit Arguments.

Require Import hpattern vgtac.
Require Import Global UserProofType DStr Syn Global.
Require DomCon SemCon DomInsen.
Require Import SemCommon.

Module Make (Import PInput : PINPUT).

Local Open Scope type.

Include DomInsen.Make PInput.

Section Sem.

Variable g : G.t.

Let pgm : InterCfg.t := G.icfg g.

Let mode : UserInputType.update_mode := UserInputType.Strong.

Variable amap : access_map.

Definition postfix_cmd (cn : InterNode.t) (s : state_t) : Prop :=
  forall cmd (Hcmd : Some cmd = InterCfg.get_cmd pgm cn),
    let m := s (cn, Inputof) in
    let m' := run_only mode g cn cmd m in
    let m'' := s (cn, Outputof) in
    Mem.le m' m''.

Definition postfix_intra_edge (cn : InterNode.t) (s : state_t) : Prop :=
  let p := InterNode.get_pid cn in
  let n := InterNode.get_node cn in
  forall n' cfg
         (Hcfg : InterCfg.PidMap.MapsTo p cfg (InterCfg.cfgs pgm))
         (Hedge : IntraCfg.is_succ cfg n n')
         (Hcn_cond: not (InterCfg.is_call_node pgm cn)),
    Mem.le (s (cn, Outputof)) (s ((p, n'), Inputof)).

Definition postfix_intra_call (cn : InterNode.t) (s : state_t) : Prop :=
  forall callee (Hedge : InterCfg.is_succ pgm cn (callee, IntraNode.Entry))
         retn (Hretn : Some retn = InterCfg.returnof pgm cn),
    let access := get_all_access callee amap in
    let m := s (cn, Outputof) in
    let m' := Mem.subtract access m in
    Mem.le m' (s (retn, Inputof)).

Definition postfix_inter_call (cn : InterNode.t) (s : state_t) : Prop :=
  forall callee (Hedge : InterCfg.is_succ pgm cn (callee, IntraNode.Entry)),
    let access := get_all_access callee amap in
    let m := s (cn, Outputof) in
    let m' := Mem.restrict access m in
    Mem.le m' (s ((callee, IntraNode.Entry), Inputof)).

Definition postfix_inter_ret (cn : InterNode.t) 
           (s : state_t) : Prop :=
  forall p (Hp : cn = (p, IntraNode.Exit))
         cn' (Hedge : InterCfg.is_succ pgm cn cn')
         calln (Hret: Some cn' = InterCfg.returnof pgm calln),
    Mem.le (s (cn, Outputof)) (s (cn', Inputof)).

Definition postfix (s : state_t) : Prop :=
  forall (cn : InterNode.t)  ,
    postfix_cmd cn s
    /\ postfix_intra_edge cn s
    /\ postfix_intra_call cn s
    /\ postfix_inter_call cn s
    /\ postfix_inter_ret cn s.

Definition sound_amap_run (s : state_t) :=
  forall cn cmd (Hcmd : Some cmd = InterCfg.get_cmd pgm cn),
    Acc.le
      (Acc.get_acc (run_access mode g cn cmd (s (cn, SemCommon.Inputof))))
      (get_access (InterNode.get_pid cn) amap).

Definition sound_amap_reachable :=
  forall f1 f2 (Hr : InterCfg.reachable pgm f1 f2),
    Acc.le (get_access f2 amap) (get_access f1 amap).

Definition sound_amap (s : state_t) : Prop :=
  sound_amap_run s /\ sound_amap_reachable.

End Sem.

Local Close Scope type.

End Make.
