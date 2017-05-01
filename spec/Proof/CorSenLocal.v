(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** * Correctness sub-proof (Sen -- SenLocal *)

Set Implicit Arguments.

Require Import hpattern vgtac Global.
Require SemSen SemSenLocal ExtSenLocal.
Require Import DenSenLocal.
Require Import UserProofType.

Module Make (Import PInput : PINPUT).

Module Sen := SemSen.Make PInput.

Module SenLocal := SemSenLocal.Make PInput.

Module ESenLocal := ExtSenLocal.Make PInput.

Module DSenLocal := DenSenLocal.Make PInput.

Section RunParam.

Variable (g : G.t) (Hg : G.wf g) (amap : access_map).

Let icfg := G.icfg g.

Let mode : UserInputType.update_mode := UserInputType.Strong.

Variable s : Sen.state_t.

Lemma densify_mem_reachables :
  forall ns n pid (Hreachs: InterCfg.reachables icfg (n :: ns) pid)
         (Hamap_reachable: SenLocal.sound_amap_reachable g amap),
    disjoint
      (DSenLocal.densify_mem amap s (InterNode.get_pid n) ns)
      (get_access pid amap).
Proof.
induction ns; s; i.
- by apply disjoint_bot.
- apply disjoint_join.
  + apply disjoint_le with (get_access (InterNode.get_pid n) amap).
    * apply Hamap_reachable. by inversion Hreachs.
    * unfold disjoint. intros l Hacc. by apply Mem.subtract_1.
  + apply IHns; [by inversion Hreachs|by auto].
Qed.

Lemma cor_amap :
  forall cn calls cmd (Hcmd : Some cmd = InterCfg.get_cmd icfg cn)
         (Hr: InterCfg.reachables icfg calls (InterNode.get_pid cn))
         (Hamap_reachable: SenLocal.sound_amap_reachable g amap)
         (Hamap_run: SenLocal.sound_amap_run g amap s),
    disjoint
      (DSenLocal.densify_mem amap s (InterNode.get_pid cn) calls)
      (Acc.get_acc
         (run_access mode g cn cmd (s (cn, SemCommon.Inputof, calls)))).
Proof.
i. apply disjoint_le with (get_access (InterNode.get_pid cn) amap)
   ; [by apply Hamap_run|].
apply densify_mem_reachables; [|by auto]; constructor; [by constructor|by auto].
Qed.

Lemma cor_cmd :
  forall cn calls (Hcmd : SenLocal.postfix_cmd g cn calls s)
         (Hr: InterCfg.reachables icfg calls (InterNode.get_pid cn))
         (Hamap_reachable: SenLocal.sound_amap_reachable g amap)
         (Hamap_run: SenLocal.sound_amap_run g amap s),
    Sen.postfix_cmd g cn calls (DSenLocal.densify_state amap s).
Proof.
unfold SenLocal.postfix_cmd, SenLocal.Sen.postfix_cmd, Sen.postfix_cmd; i.
unfold DSenLocal.densify_state.
eapply Mem.le_trans
; [| apply Mem.join_le
     ; [by apply Hcmd, Hcmd0|by apply Mem.le_refl, Mem.eq_refl]].
do 2 rewrite run_only_access_same. apply Mem.le_refl.
assert (Hcor := run_access_sound g cn cmd). unfold aeqm1 in Hcor.
exploit Hcor; [|intro Hcor'].
- apply cor_amap; [|by apply Hr| |]; by auto.
- match goal with |- context[Acc.get_v ?x] => destruct x end; s.
  match goal with |- context[Acc.get_v ?x] => destruct x end.
  by apply Hcor'.
Qed.

Lemma cor_intra :
  forall cn calls (Hedge : SenLocal.postfix_intra_edge g cn calls s),
    Sen.postfix_intra_edge g cn calls (DSenLocal.densify_state amap s).
Proof.
unfold Sen.postfix_intra_edge, DSenLocal.densify_state; i.
apply Mem.join_le.
- by apply Hedge with (cfg:=cfg).
- apply Mem.le_refl; by apply Mem.eq_refl.
Qed.

Lemma cor_inter_call :
forall cn calls (Hinter : SenLocal.postfix_inter_call g amap cn calls s),
  Sen.postfix_inter_call g cn calls (DSenLocal.densify_state amap s).
Proof.
unfold SenLocal.postfix_inter_call, Sen.postfix_inter_call
; unfold DSenLocal.densify_state; i.
apply Mem.join_lub.
- eapply Mem.le_trans; [apply Mem.le_refl; apply Mem.restrict_subtract_1|].
  apply Mem.join_le; [by apply Hinter|].
  simpl DSenLocal.densify_mem; by apply Mem.join_left.
- simpl DSenLocal.densify_mem.
  eapply Mem.le_trans; [by apply Mem.join_right|].
  by apply Mem.join_right.
Qed.

Lemma cor_inter_ret :
  forall cn calls (Hret : SenLocal.postfix_inter_ret g cn calls s)
         (Hintra : forall cn calls,
                     SenLocal.postfix_intra_call g amap cn calls s),
    Sen.postfix_inter_ret g cn calls (DSenLocal.densify_state amap s).
Proof.
unfold Sen.postfix_inter_ret; i; s.
apply Mem.join_lub.
- eapply Mem.le_trans; [|by apply Mem.join_left].
  by apply Hret with p.
- apply Mem.join_lub.
  + eapply Mem.le_trans; [|by apply Mem.join_left].
    apply Hintra; [|by auto]. subst.
    destruct Hg as [Hg_callof_returnof [_ [Hg_call_edge _]]].
    apply Hg_callof_returnof in Hret0.
    by apply Hg_call_edge with cn'.
  + eapply Mem.le_trans; [|by apply Mem.join_right].
    exploit InterCfg.returnof_same_pid; [apply Hret0 | intro Hpid].
    rewrite Hpid; apply Mem.le_refl; by apply Mem.eq_refl.
Qed.

Lemma correctness :
  forall (Hpostfix : SenLocal.postfix g amap s)
     (Hamap : SenLocal.sound_amap g amap s),
  exists s', Sen.postfix g s' /\ ESenLocal.extends g amap s s'.
Proof.
i; exists (DSenLocal.densify_state amap s); split.
{
unfold SenLocal.postfix in Hpostfix; unfold Sen.postfix; i.
splits.
- apply cor_cmd; [by apply Hpostfix|by auto|by apply Hamap|by apply Hamap].
- apply cor_intra; by apply Hpostfix.
- apply cor_inter_call; by apply Hpostfix.
- apply cor_inter_ret; by apply Hpostfix.
}
{
unfold ESenLocal.extends, ESenLocal.extends_mem. i. s.
eapply Val.eq_trans; [|apply Val.eq_sym; by apply Mem.join_find].
apply Val.le_antisym; [by apply Val.join_left|].
apply Val.join_lub; [apply Val.le_refl; by apply Val.eq_refl|].
apply Val.le_trans with Val.bot; [|by apply Val.bot_prop].
apply Val.le_refl.
assert (disjoint
          (DSenLocal.densify_mem amap s (InterNode.get_pid n) calls)
          (get_access (InterNode.get_pid n) amap))
  as Hdisj.
- apply densify_mem_reachables.
  + constructor; [by constructor|by auto].
  + by apply Hamap.
- by apply Hdisj.
}
Qed.

End RunParam.

End Make.
