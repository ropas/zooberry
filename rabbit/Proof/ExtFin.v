(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** * Extends relation for analysis result *)

Set Implicit Arguments.

Require Import hpattern vgtac.
Require Import UserProofType Syn Global.
Require Import SemCommon.
Require ExtMem.
Require DomInsen.

Module Make (Import PInput : PINPUT).

Local Open Scope type.

Module Insen := DomInsen.Make PInput.

Include ExtMem.Make PInput.

Definition state_find (mempos : mem_pos) (node : InterNode.t)
           (s : Table.t Mem.t * Table.t Mem.t) : Mem.t :=
  let t := match mempos with
             | Inputof => fst s
             | Outputof => snd s
           end in
  table_find node t.

Definition extends (g : G.t) (s : Table.t Mem.t)
           (insenl_s : Insen.state_t) : Prop :=
  forall cfg f n cmd insenl_m
         (Hcfg: InterCfg.PidMap.MapsTo f cfg (InterCfg.cfgs (G.icfg g)))
         (Hcmd: IntraCfg.NodeMap.MapsTo n cmd (IntraCfg.cmds cfg))
         (Hidx_m : insenl_s ((f, n), Inputof) = insenl_m),
    let mode := UserInputType.Strong in
    let '(m', acc_n) :=
        run_access mode g (f, n) cmd (table_find (f, n) s) in
    let uses_n := Acc.useof acc_n in
    extends_mem uses_n (table_find (f, n) s) insenl_m.

Definition extends' (g : G.t)
           (s1 : Table.t Mem.t) (s2 : Table.t Mem.t * Table.t Mem.t) : Prop :=
  forall cfg f n cmd
         (Hcfg: InterCfg.PidMap.MapsTo f cfg (InterCfg.cfgs (G.icfg g)))
         (Hcmd: IntraCfg.NodeMap.MapsTo n cmd (IntraCfg.cmds cfg)),
    let mode := UserInputType.Strong in
    let '(m', acc_n) :=
        run_access mode g (f, n) cmd (table_find (f, n) s1) in
    let uses_n1 := Acc.useof acc_n in
    extends_mem uses_n1 (table_find (f, n) s1)
                (state_find Inputof (f, n) s2).

Definition extends'' (g : G.t)
           (s : Table.t Mem.t * Table.t Mem.t)
           (insenl_s : Insen.state_t) : Prop :=
  forall n mpos, Mem.eq (state_find mpos n s) (insenl_s (n, mpos)).

Lemma extends_trans :
  forall (g : G.t) x y z
     (He1: extends' g x y) (He2: extends'' g y z),
    extends g x z.
Proof.
unfold extends', extends, extends_mem; i.
specialize He1 with cfg f n cmd. 
remember (run_access UserInputType.Strong g (f, n) cmd (table_find (f, n) x))
as x1.
destruct x1 as [v1 acc1]. i.
eapply Val.eq_trans with (Mem.find k (state_find Inputof (f, n) y)).
- by apply He1.
- rewrite <- Hidx_m. by apply He2.
Qed.

Local Close Scope type.

End Make.
