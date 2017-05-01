(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** * Abstract semantics (context-sen) *)

Set Implicit Arguments.

Require Import hpattern vgtac.
Require Import Global UserProofType DStr Syn.
Require DomCon SemCon DomSen.
Require Import SemCommon.

Module Make (Import PInput : PINPUT).

Local Open Scope type.

Module Dom := DomSen.Make PInput.

Include Dom.

Section Sem.

Variable g : G.t.

Let pgm : InterCfg.t := G.icfg g.

Let mode : UserInputType.update_mode := UserInputType.Strong.

Definition postfix_cmd (cn : InterNode.t) (calls : list InterNode.t)
          (s : state_t) : Prop :=
  forall cmd (Hcmd : Some cmd = InterCfg.get_cmd pgm cn),
    let m := s (cn, Inputof, calls) in
    let m' := run_only mode g cn cmd m in
    Mem.le m' (s (cn, Outputof, calls)).

Definition postfix_intra_edge (cn : InterNode.t) (calls : list InterNode.t)
           (s : state_t) : Prop :=
  let p := InterNode.get_pid cn in
  let n := InterNode.get_node cn in
  forall n' cfg
         (Hcfg : InterCfg.PidMap.MapsTo p cfg (InterCfg.cfgs pgm))
         (Hedge : IntraCfg.is_succ cfg n n')
         (Hcn_cond: not (InterCfg.is_call_node pgm cn)),
    Mem.le (s (cn, Outputof, calls)) (s ((p, n'), Inputof, calls)).

Definition postfix_inter_call (cn : InterNode.t) (calls : list InterNode.t)
           (s : state_t) : Prop :=
  forall callee (Hedge : InterCfg.is_succ pgm cn (callee, IntraNode.Entry)),
    Mem.le (s (cn, Outputof, calls))
           (s ((callee, IntraNode.Entry), Inputof, cn :: calls)).

Definition postfix_inter_ret (cn : InterNode.t) (calls : list InterNode.t)
           (s : state_t) : Prop :=
  forall p (Hp : cn = (p, IntraNode.Exit))
         cn' (Hedge : InterCfg.is_succ pgm cn cn')
         calln (Hret: Some cn' = InterCfg.returnof pgm calln),
    Mem.le (s (cn, Outputof, calln :: calls)) (s (cn', Inputof, calls)).

Definition postfix (s : state_t) : Prop :=
  forall (cn : InterNode.t) (calls : list InterNode.t)
         (Hreach : InterCfg.reachables pgm calls (InterNode.get_pid cn)),
    postfix_cmd cn calls s
    /\ postfix_intra_edge cn calls s
    /\ postfix_inter_call cn calls s
    /\ postfix_inter_ret cn calls s.

End Sem.

Local Close Scope type.

End Make.
