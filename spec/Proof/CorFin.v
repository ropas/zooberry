(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** * Correctness sub-proof (InsenLocal -- Valid *)

Set Implicit Arguments.

Require Import VocabA Global.
Require SemInsenLocal ExtFin.
Require Import UserProofType.
Require Import vgtac.

Module Make (Import PInput : PINPUT).

Module InsenLocal := SemInsenLocal.Make PInput.

Module EFin := ExtFin.Make PInput.

Ltac dest_run_access :=
match goal with [H : context [run_access ?prm ?g ?n ?c ?mem] |- _] =>
  let m := fresh "m" in
  let acc := fresh "acc" in
  let f := fresh "x" in
  remember (run_access prm g n c mem) as f; destruct f as [m acc]
end.

Section correctness.

Variables (g : G.t) (Hg : G.wf g)
          (fis_mem: Mem.t) (amap : access_map)
          (orig_inputof inputof outputof : Table.t Mem.t)
          (Hvalid : valid g amap orig_inputof
                          inputof outputof = true).

Let s := fun idx : InsenLocal.index_t =>
           let node := InsenLocal.node_of_index idx in
           let t := match InsenLocal.pos_of_index idx with
                      | SemCommon.Inputof => inputof
                      | SemCommon.Outputof => outputof
                    end in
           table_find node t.

Lemma get_valid_cfgs : valid_cfgs g amap inputof outputof = true.
Proof.
  unfold valid in Hvalid.
  dest_bool. destruct Hvalid as [Hvalid1 _].
  dest_bool. destruct Hvalid1 as [Hvalid1 _].
  dest_bool. destruct Hvalid1 as [Hvalid1 _].
  dest_bool. by destruct Hvalid1.
Qed.

Lemma get_valid_cfg :
  forall f cfg
     (Hfind: Some cfg = InterCfg.PidMap.find f (InterCfg.cfgs (icfg g))),
    valid_cfg g amap inputof outputof f cfg = true.
Proof.
assert (Hvalid_cfgs := get_valid_cfgs). unfold valid_cfgs in Hvalid_cfgs.
i. apply InterCfg.PidMap.for_all_2 with (k:=f) (v:=cfg) in Hvalid_cfgs
; [ by auto
  | i; by subst
  | by apply InterCfg.PidMap.P.F.find_mapsto_iff ].
Qed.

Lemma get_valid_cmds :
  forall f cfg
     (Hfind: Some cfg = InterCfg.PidMap.find f (InterCfg.cfgs (icfg g))),
    valid_cmds g amap inputof outputof f cfg.
Proof.
i. assert (Hcfg := get_valid_cfg _ Hfind).
unfold valid_cfg in Hcfg. dest_bool. by destruct Hcfg.
Qed.

Lemma get_valid_cmd :
  forall cn cmd (Hget_cmd: Some cmd = InterCfg.get_cmd (G.icfg g) cn),
    valid_cmd g amap inputof outputof (InterNode.get_pid cn)
              (InterNode.get_node cn) cmd = true.
Proof.
unfold InterCfg.get_cmd. i. dest_trivial_match.
assert (Hcmds := get_valid_cmds _ Heqcond).
unfold valid_cmds in Hcmds.
apply IntraCfg.NodeMap.for_all_2 with (k:=InterNode.get_node cn) (v:=cmd)
  in Hcmds
; [ by auto
  | i; by inversion Hk
  | by apply IntraCfg.NodeMap.P.F.find_mapsto_iff ].
Qed.

Lemma get_valid_intra_edges :
  forall f cfg
         (Hfind: Some cfg = InterCfg.PidMap.find f (InterCfg.cfgs (icfg g))),
    valid_intra_edges inputof outputof f cfg.
Proof.
i. assert (Hcfg := get_valid_cfg _ Hfind).
unfold valid_cfg in Hcfg. dest_bool. by destruct Hcfg.
Qed.

Lemma get_valid_intra_edge :
  forall f cfg
         (Hmapsto : InterCfg.PidMap.MapsTo f cfg (InterCfg.cfgs (G.icfg g)))
         n n' succs
         (Hsuccs : IntraCfg.NodeMap.MapsTo n succs (IntraCfg.succ cfg))
         (Hn' : IntraCfg.NodeSet.In n' succs),
    valid_intra_edge inputof outputof f cfg n n' = true.
Proof.
i. apply InterCfg.PidMap.P.F.find_mapsto_iff in Hmapsto. symmetry in Hmapsto.
assert (Hvalid_intra_edges := get_valid_intra_edges _ Hmapsto).
unfold valid_intra_edges in Hvalid_intra_edges.
apply IntraCfg.NodeMap.for_all_2 with (k:=n) (v:=succs) in Hvalid_intra_edges
; [|i; by inversion Hk|by auto].
apply IntraCfg.NodeSet.for_all_2 in Hvalid_intra_edges
; [|intros k k' Hk; by inversion Hk].
unfold IntraCfg.NodeSet.For_all in Hvalid_intra_edges.
by apply Hvalid_intra_edges.
Qed.

Lemma get_valid_inter_edges : valid_inter_edges g amap inputof outputof = true.
Proof.
  unfold valid in Hvalid.
  dest_bool. destruct Hvalid as [Hvalid1 _].
  dest_bool. destruct Hvalid1 as [Hvalid1 _].
  dest_bool. destruct Hvalid1 as [_ Hvalid1].
  dest_bool. by destruct Hvalid1.
Qed.

Lemma get_valid_inter_edge :
  forall cn cn' succs
         (Hsuccs: InterCfg.NodeMap.MapsTo cn succs (InterCfg.succ (icfg g)))
         (Hcn' : InterCfg.NodeSet.In cn' succs),
    valid_inter_edge g amap inputof outputof cn cn' = true.
Proof.
i. assert (Hvalid_inter_edges := get_valid_inter_edges).
unfold valid_inter_edges in Hvalid_inter_edges.
apply InterCfg.NodeMap.for_all_2 with (k:=cn) (v:=succs) in Hvalid_inter_edges
; [|i; apply InterNode.eq_inv in Hk; by subst|by auto].
apply InterCfg.NodeSet.for_all_2 in Hvalid_inter_edges
; [|intros k k' Hk; apply InterNode.eq_inv in Hk; by subst].
unfold InterCfg.NodeSet.For_all in Hvalid_inter_edges.
by apply Hvalid_inter_edges.
Qed.

Lemma get_valid_inter_accs : valid_inter_accs g amap = true.
Proof.
unfold valid in Hvalid.
  dest_bool. destruct Hvalid as [Hvalid1 _].
  dest_bool. destruct Hvalid1 as [_ Hvalid1].
  dest_bool. by destruct Hvalid1.
Qed.

Lemma cor_postfix_cmd :
  forall cn, InsenLocal.postfix_cmd g cn s.
Proof.
unfold InsenLocal.postfix_cmd; i.
assert (Hvalid_cmd := get_valid_cmd _ Hcmd).
unfold valid_cmd in Hvalid_cmd.
dest_run_access; dest_if_dec; dest_if.
symmetry in Heqcond; apply Mem.opt_le_prop in Heqcond.
destruct cn; apply Mem.le_trans with m; [|by auto].
apply Mem.le_refl; apply Mem.eq_sym.
rewrite run_only_access_same.
apply Mem.eq_trans with (Acc.get_v (m, acc)); [by apply Mem.eq_refl|].
rewrite Heqx; by apply Mem.eq_refl.
Qed.

Lemma cor_postfix_intra_edge :
  forall cn, InsenLocal.postfix_intra_edge g cn s.
Proof.
unfold InsenLocal.postfix_intra_edge; i.
inversion Hedge; subst.
assert (Hvalid_intra_edge := get_valid_intra_edge Hcfg Hsuccs Hn').
unfold valid_intra_edge in Hvalid_intra_edge.
dest_if
; [ elim Hcn_cond; unfold InterCfg.is_call_node
    ; rewrite (InterCfg.PidMap.find_1 Hcfg); s; rewrite <- Heqcond; reflexivity
  | dest_if; destruct cn; by apply Mem.opt_le_prop ].
Qed.

Lemma cor_postfix_intra_call :
  forall cn, InsenLocal.postfix_intra_call g amap cn s.
Proof.
unfold InsenLocal.postfix_intra_call; i.
destruct Hg as [_ [Hg_call_edge [_ [Hg_call_node [_ Hg_pred_succ]]]]].
assert (Hret_edge := Hg_call_edge _ _ _ Hedge Hretn).
inversion Hret_edge. subst.
assert (Hvalid_inter_edge := get_valid_inter_edge Hsuccs Hn').
unfold valid_inter_edge in Hvalid_inter_edge.
unfold icfg in Hvalid_inter_edge.
rewrite (Hg_call_node callee) in Hvalid_inter_edge.
dest_if. unfold GenFunc.fail_inter_edge_no_callof in *. dest_trivial_match.
assert (Hcn := InterCfg.returnof_1 _ Hg_pred_succ Hretn Heqcond0).
apply InterNode.eq_inv in Hcn; subst.
dest_if. dest_if. by apply Mem.opt_le_prop.
Qed.

Lemma cor_postfix_inter_call :
  forall cn, InsenLocal.postfix_inter_call g amap cn s.
Proof.
unfold InsenLocal.postfix_inter_call; i.
inversion Hedge; subst.
assert (Hvalid_inter_edge := get_valid_inter_edge Hsuccs Hn').
unfold valid_inter_edge in Hvalid_inter_edge.
dest_if; [dest_if; by apply Mem.opt_le_prop|].
destruct Hg as [_ [_ [_ [_ [Hg_call_node _]]]]].
unfold G.is_exit_node in Hvalid_inter_edge.
by rewrite (Hg_call_node cn callee Hedge) in Hvalid_inter_edge.
Qed.

Lemma cor_postfix_inter_ret :
  forall cn, InsenLocal.postfix_inter_ret g cn s.
Proof.
unfold InsenLocal.postfix_inter_ret; i; subst.
inversion Hedge; subst.
assert (Hvalid_inter_edge := get_valid_inter_edge Hsuccs Hn').
unfold valid_inter_edge in Hvalid_inter_edge.
destruct Hg as [_ [_ [_ [Hg_call_node [_ Hg_pred_succ]]]]].
unfold icfg in Hvalid_inter_edge.
rewrite (Hg_call_node p) in Hvalid_inter_edge.
dest_if. unfold GenFunc.fail_inter_edge_no_callof in *. dest_trivial_match.
assert (Hcn := InterCfg.returnof_1 _ Hg_pred_succ Hret Heqcond0).
apply InterNode.eq_inv in Hcn; subst.
dest_if. by apply Mem.opt_le_prop.
Qed.

Lemma cor_amap_run : InsenLocal.sound_amap_run g amap s.
Proof.
  unfold InsenLocal.sound_amap_run; i. destruct cn as [f n].
  unfold InterCfg.get_cmd in Hcmd. dest_trivial_match.
  unfold IntraCfg.get_cmd in Hcmd.
  assert (Hcmds := get_valid_cmds f Heqcond).
  unfold valid_cmds in Hcmds.
  apply IntraCfg.NodeMap.for_all_2 with (k:=n) (v:=cmd) in Hcmds
  ; [| i; by inversion Hk
     | symmetry in Hcmd
       ; by apply IntraCfg.NodeMap.P.F.find_mapsto_iff in Hcmd ].
  unfold valid_cmd in Hcmds. unfold s. s.
  dest_run_access; dest_if_dec; dest_if.
  unfold Syn.pid_t, IntraNode.t in Heqx. rewrite <- Heqx. by apply l.
Qed.

Lemma cor_amap_reachable : InsenLocal.sound_amap_reachable g amap.
Proof.
unfold InsenLocal.sound_amap_reachable. induction 1.
- apply Acc.le_refl. by apply Acc.eq_refl.
- eapply Acc.le_trans; [by apply IHHr|].
  assert (Haccs := get_valid_inter_accs).
  unfold valid_inter_accs in Haccs. inversion Hinter.
  apply InterCfg.NodeMap.for_all_2 with (k:=(p, n)) (v:=succs) in Haccs
  ; [| intros k k' [Hk1 Hk2]; destruct k, k'; simpl in Hk1; simpl in Hk2
       ; inversion Hk1; inversion Hk2; reflexivity
     | by apply Hsuccs ].
  apply InterCfg.NodeSet.for_all_2 in Haccs
  ; [| intros k k' [Hk1 Hk2]; destruct k, k'; simpl in Hk1; simpl in Hk2
       ; inversion Hk1; inversion Hk2; reflexivity ].
  assert (Hacc := Haccs (q, IntraNode.Entry) Hn'). simpl in Hacc.
  unfold valid_inter_acc, InterNode.is_entry_node, IntraNode.is_entry_node
    in Hacc.
  simpl in Hacc.
  dest_if
  ; [| destruct (IntraNode.eq_dec IntraNode.Entry IntraNode.Entry)
       ; [inversion Heqcond|elim f; by apply IntraNode.eq_refl]].
  destruct (Acc.le_dec (get_access q amap) (get_access p amap))
  ; [by auto|by inversion Hacc].
Qed.

Lemma cor_extends' :
  EFin.extends' g orig_inputof (inputof, outputof).
Proof.
unfold valid in Hvalid.
dest_bool. destruct Hvalid as [_ Hdens].
unfold valid_dens in Hdens. unfold EFin.extends'; i.
apply InterCfg.PidMap.for_all_2 with (k:=f) (v:=cfg) in Hdens
; [| intros k k' Hk; subst; reflexivity | by auto ].
unfold valid_dens_cfg in Hdens.
apply IntraCfg.NodeMap.for_all_2 with (k:=n) (v:=cmd) in Hdens
; [| intros k k' Hk; inversion Hk; reflexivity | by auto ].
unfold valid_dens_node in Hdens. unfold EFin.state_find, fst.
unfold InterCfg.PidMap.key, IntraCfg.NodeMap.key. unfold IntraNode.t in Hdens.
match goal with | [|- let '(_, _) := ?x in _] => remember x as p end.
destruct p as [v acc_n]. dest_if.
unfold EFin.extends_mem. intros k Hk.
symmetry in Heqcond. eapply Mem.eq_wrt_1 in Heqcond; [|by apply Hk]. by auto.
Qed.

Lemma cor_extends :
  EFin.extends g orig_inputof s.
Proof.
eapply EFin.extends_trans; [by apply cor_extends'|].
unfold EFin.extends'', EFin.state_find, s; s; i.
by apply Mem.eq_refl.
Qed.

Lemma correctness :
  exists s',
    InsenLocal.postfix g amap s'
    /\ InsenLocal.sound_amap g amap s'
    /\ EFin.extends g orig_inputof s'.
Proof.
i; exists s; split; [|split].
{ repeat split.
  - by apply cor_postfix_cmd.
  - by apply cor_postfix_intra_edge.
  - by apply cor_postfix_intra_call.
  - by apply cor_postfix_inter_call.
  - by apply cor_postfix_inter_ret. }
{ split.
  - by apply cor_amap_run.
  - by apply cor_amap_reachable. }
{ by apply cor_extends. }
Qed.

End correctness.

End Make.
