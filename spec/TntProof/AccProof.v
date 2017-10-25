(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
Set Implicit Arguments.

Require Import vgtac.
Require Import VocabA.
Require Import Monad Global UserInputType UserInput.
Require Import DItv DPos Vali SemProof.
Require Import Morphisms.

Load VeqCommon.

Lemma mem_lookup_access_same :
  forall x m,
    veq (RunOnly.SemEval.SemMem.mem_lookup x m)
        (RunAccess.SemEval.SemMem.mem_lookup x m).
Proof.
i. unfold RunOnly.SemEval.SemMem.mem_lookup
        , RunAccess.SemEval.SemMem.mem_lookup.
apply PowLoc.fold2_3; [|by apply PowLoc.eq_refl|by dest_veq].
i; dest_veq; [by auto|].
i; dest_veq; [|i; by dest_veq].
unfold DomMem.IdMem.mem_find, AccMem.mem_find, veq; s.
by apply DomMem.Mem.find_mor2.
Qed.

Lemma can_strong_update_same :
  forall g l,
    RunOnly.SemMem.can_strong_update Strong g l
    = RunAccess.SemMem.can_strong_update Strong g l.
Proof.
i; unfold RunOnly.SemMem.can_strong_update, RunAccess.SemMem.can_strong_update.
reflexivity.
Qed.

Lemma mem_update_access_same :
  forall g l v m,
    veq (RunOnly.mem_update Strong g l v m)
        (RunAccess.mem_update Strong g l v m).
Proof.
i; unfold RunOnly.mem_update, RunAccess.mem_update
        , RunOnly.SemMem.mem_update, RunAccess.SemMem.mem_update.
rewrite can_strong_update_same.
destruct (RunAccess.SemMem.can_strong_update Strong g l).
- i; unfold RunOnly.SemMem.add, RunAccess.SemMem.add; s.
  by unfold DomMem.IdMem.mem_add, AccMem.mem_add, veq; s.
- i; unfold RunOnly.SemMem.weak_add, RunAccess.SemMem.weak_add; s.
  by unfold DomMem.IdMem.mem_weak_add, AccMem.mem_weak_add, veq; s.
Qed.

Lemma mem_wupdate_access_same :
  forall l v m,
    veq (RunOnly.mem_wupdate Strong l v m) (RunAccess.mem_wupdate Strong l v m).
Proof.
i; unfold RunOnly.mem_wupdate, RunAccess.mem_wupdate
        , RunOnly.SemMem.mem_wupdate, RunAccess.SemMem.mem_wupdate.
apply PowLoc.fold2_4; [|by dest_veq].
i; dest_veq; [by auto|].
i; unfold RunOnly.SemMem.weak_add, RunAccess.SemMem.weak_add; s.
by unfold DomMem.IdMem.mem_weak_add, AccMem.mem_weak_add, veq; s.
Qed.

Section Env.
Variables (g : G.t) (cn : InterNode.t) (cmd : Syn.cmd).

Lemma pow_proc_fold_access_same T :
  forall s f1 f2
     (Hf :
        forall e1 e2 (He : Proc.eq e1 e2) t1 t2 (Ht : veq t1 t2),
          veq (f1 e1 t1) (f2 e2 t2))
     (a1 : MId.m T) (a2 : Acc.MAcc.m T) (Ha : veq a1 a2),
    veq (PowProc.fold f1 s a1) (PowProc.fold f2 s a2).
Proof. i. by eapply PowProc.fold2_3. Qed.

Lemma weak_big_join_access_same :
  forall ls f1 f2
     (Hf :
        forall e1 e2 (He : Proc.eq e1 e2) t1 t2 (Ht : t1 = t2),
          veq (f1 e1 t1) (f2 e2 t2))
     a1 a2 (Ha : veq a1 a2),
    veq (RunOnly.BJProcMem.weak_big_join f1 ls a1)
        (RunAccess.BJProcMem.weak_big_join f2 ls a2).
Proof.
unfold RunOnly.BJProcMem.weak_big_join, RunAccess.BJProcMem.weak_big_join.
i; apply pow_proc_fold_access_same; [|by auto].
i; dest_veq; [by auto|i; by apply Hf].
Qed.

Lemma eval_access_same :
  forall e m, veq (RunOnly.eval Strong cn e m) (RunAccess.eval Strong cn e m)

with eval_lv_access_same :
  forall lv m,
    veq (RunOnly.SemEval.eval_lv Strong cn lv m)
        (RunAccess.SemEval.eval_lv Strong cn lv m)

with resolve_offset_access_same :
 forall o x m,
   veq (RunOnly.SemEval.resolve_offset Strong cn x o m)
       (RunAccess.SemEval.resolve_offset Strong cn x o m).
Proof.
{ induction e; s; i.
- by dest_veq.
- dest_veq; [by apply eval_lv_access_same|i; by apply mem_lookup_access_same].
- by dest_veq.
- by dest_veq.
- by dest_veq.
- by dest_veq.
- by dest_veq.
- dest_veq; [by apply eval_access_same|i; by dest_veq].
- dest_veq; [by apply eval_access_same|].
  i; dest_veq; [by apply eval_access_same|i; by dest_veq].
- dest_veq; [by apply eval_access_same|].
  i; dest_veq; [by apply eval_access_same|].
  i; by dest_veq.
- destruct i; [|by apply eval_access_same].
  dest_veq; [by apply eval_access_same|].
  i; by dest_veq.
- dest_veq; [by apply eval_lv_access_same|].
  i; by dest_veq.
- dest_veq; [by apply eval_lv_access_same|].
  i; by dest_veq. }
{ induction lv; s; i.
dest_veq; [|i; by apply resolve_offset_access_same].
destruct lh; [|by apply eval_access_same].
by dest_veq. }
{ induction o; s; i.
- i; by dest_veq.
- i; by apply IHo.
- i; dest_veq; [by apply mem_lookup_access_same|].
  i; by apply IHo. }
Qed.

Lemma eval_list_access_same :
  forall args m,
    veq (RunOnly.SemEval.eval_list Strong cn args m)
        (RunAccess.SemEval.eval_list Strong cn args m).
Proof.
induction args; s; i.
- by dest_veq.
- dest_veq; [by apply eval_access_same|].
  i; dest_veq; [by apply IHargs|].
  i; by dest_veq.
Qed.

Lemma list_fold2_access_same T U V :
  forall f1 f2 (Hf : forall a u i, veq (f1 a u i) (f2 a u i))
     (l : list T) (x : list U) (i : V),
    veq (RunOnly.SemMem.list_fold2_m f1 l x i)
        (RunAccess.SemMem.list_fold2_m f2 l x i).
Proof.
induction l; destruct x; s; i.
- by dest_veq.
- by dest_veq.
- by dest_veq.
- dest_veq; [by auto|by apply IHl].
Qed.

Lemma bind_args_access_same :
  forall x e1 e2 (He : Proc.eq e1 e2) (t1 t2 : DomMem.Mem.t) (Ht : t1 = t2),
    veq (RunOnly.SemMem.bind_args Strong g x e1 t1)
        (RunAccess.SemMem.bind_args Strong g x e2 t2).
Proof.
i; unfold RunOnly.SemMem.bind_args, RunAccess.SemMem.bind_args.
inversion He; subst.
destruct (InterCfg.get_args (G.icfg g) e2); [|by dest_veq].
by apply list_fold2_access_same.
Qed.

Lemma set_ext_allocsite_access_same :
  forall l a m pos,
  veq
    (RunOnly.set_ext_allocsite Strong cn l a m pos)
    (RunAccess.set_ext_allocsite Strong cn l a m pos).
Proof.
i; unfold RunOnly.set_ext_allocsite, RunAccess.set_ext_allocsite.
dest_veq; [by apply eval_lv_access_same|].
i; dest_veq; [by apply mem_wupdate_access_same|].
i; by apply mem_wupdate_access_same.
Qed.

Lemma list_fold_access_same T U :
  forall (l : list T)
     f1 f2 (Hf : forall e x1 x2 (Hx : veq x1 x2), veq (f1 e x1) (f2 e x2))
     (m1 : MId.m U) (m2 : DomMem.Acc.MAcc.m U) (Hm : veq m1 m2),
    veq (list_fold f1 l m1) (list_fold f2 l m2).
Proof.
unfold list_fold. induction l; i; [by auto|].
s; apply IHl; by apply Hf.
Qed.

Lemma va_arg_joins_access_same :
  forall m args,
    veq (RunOnly.va_arg_joins Strong cn m args)
        (RunAccess.va_arg_joins Strong cn m args).
Proof.
i; unfold RunOnly.va_arg_joins, RunAccess.va_arg_joins.
apply list_fold_access_same; [i|by dest_veq].
dest_veq; [by auto|i].
dest_veq; [by apply eval_access_same|i].
dest_veq; [by apply eval_access_same|i].
by dest_veq.
Qed.

Lemma run_printf_pointer_access_same :
  forall e args m,
    veq (RunOnly.run_printf_pointer Strong cn e args m)
        (RunAccess.run_printf_pointer Strong cn e args m).
Proof.
i; unfold RunOnly.run_printf_pointer, RunAccess.run_printf_pointer.
dest_veq; [by apply eval_access_same|i].
dest_veq; [by apply va_arg_joins_access_same|i].
by apply mem_wupdate_access_same.
Qed.

Lemma run_printf_ppointer_access_same :
  forall e args m,
    veq (RunOnly.run_printf_ppointer Strong cn e args m)
        (RunAccess.run_printf_ppointer Strong cn e args m).
Proof.
i; unfold RunOnly.run_printf_ppointer, RunAccess.run_printf_ppointer.
dest_veq; [by apply eval_access_same|i].
dest_veq; [by apply va_arg_joins_access_same|i].
dest_veq; by apply mem_wupdate_access_same.
Qed.

Lemma run_printf2_access_same :
  forall p args m,
    veq (RunOnly.run_printf2 Strong cn p args m)
        (RunAccess.run_printf2 Strong cn p args m).
Proof.
i; unfold RunOnly.run_printf2, RunAccess.run_printf2.
destruct args; [by auto|].
destruct args; [by auto|].
destruct (is_ppointer_printf p); [by apply run_printf_ppointer_access_same|].
dest_if_dec. by apply run_printf_pointer_access_same.
Qed.

Lemma run_printf3_access_same :
  forall args m,
    veq (RunOnly.run_printf3 Strong cn args m)
        (RunAccess.run_printf3 Strong cn args m).
Proof.
i; unfold RunOnly.run_printf3, RunAccess.run_printf3.
destruct args; [by auto|].
destruct args; [by auto|].
destruct args; [by auto|].
by apply run_printf_pointer_access_same.
Qed.

Lemma run_printf_access_same :
  forall p args m,
    veq (RunOnly.run_printf Strong cn p args m)
        (RunAccess.run_printf Strong cn p args m).
Proof.
i; unfold RunOnly.run_printf, RunAccess.run_printf.
dest_if_dec.
dest_if_dec; [by apply run_printf2_access_same|].
dest_if_dec. by apply run_printf3_access_same.
Qed.

Lemma va_src_val_joins_access_same :
  forall m l,
    veq (RunOnly.va_src_val_joins m l) (RunAccess.va_src_val_joins m l).
Proof.
i; unfold RunOnly.va_src_val_joins, RunAccess.va_src_val_joins.
apply list_fold_access_same; [i|by auto].
dest_veq; [by apply mem_lookup_access_same|i].
dest_veq; [by auto|i].
by dest_veq.
Qed.

Lemma process_dsts_access_same :
  forall pos p l x m,
    veq (RunOnly.process_dsts Strong cn pos p l x m)
        (RunAccess.process_dsts Strong cn pos p l x m).
Proof.
i; unfold RunOnly.process_dsts, RunAccess.process_dsts.
apply list_fold_access_same; [i|by auto].
dest_veq; [by auto|i].
destruct e as [[v y1] y2], y1, y2.
- by apply mem_wupdate_access_same.
- by apply mem_wupdate_access_same.
- dest_veq; [by apply mem_wupdate_access_same|i].
  by apply mem_wupdate_access_same.
- dest_veq; [by apply mem_wupdate_access_same|i].
  by apply mem_wupdate_access_same.
Qed.

Lemma process_ret_access_same :
  forall pos p t ret_opt x0 l x1,
    veq (RunOnly.process_ret Strong cn pos p t ret_opt x0 l x1)
        (RunAccess.process_ret Strong cn pos p t ret_opt x0 l x1).
Proof.
i; unfold RunOnly.process_ret, RunAccess.process_ret.
destruct ret_opt; [|by auto].
dest_veq; [by apply eval_lv_access_same|i].
destruct (StringFun.ret t).
- by apply mem_wupdate_access_same.
- by apply mem_wupdate_access_same.
- destruct alloc; [by apply mem_wupdate_access_same|i].
  dest_veq; [by apply mem_wupdate_access_same|i].
  by apply mem_wupdate_access_same.
- by apply mem_wupdate_access_same.
Qed.

Lemma run_api_access_same :
  forall m ret_opt x pos p t,
    veq (RunOnly.run_api Strong cn ret_opt x pos p t m)
        (RunAccess.run_api Strong cn ret_opt x pos p t m).
Proof.
i; unfold RunOnly.run_api, RunAccess.run_api.
destruct (StringFun.get_dstsrc_list x (StringFun.args t) nil nil).
dest_veq; [by apply va_src_val_joins_access_same|i].
dest_veq; [by apply process_dsts_access_same|i].
dest_veq; [by apply process_ret_access_same|].  
by auto.
Qed.

Lemma run_undef_funcs_access_same :
  forall ret_opt p x m pos,
    veq (RunOnly.run_undef_funcs Strong cn ret_opt p x pos m)
        (RunAccess.run_undef_funcs Strong cn ret_opt p x pos m).
Proof.
i; unfold RunOnly.run_undef_funcs, RunAccess.run_undef_funcs.
unfold RunOnly.run_api_with_name, RunAccess.run_api_with_name.
unfold RunOnly.find_string_api_name, RunAccess.find_string_api_name.
destruct (StringFun.find p ext_api); [by apply run_api_access_same|].
destruct ret_opt; [|by auto].
by apply set_ext_allocsite_access_same.
Qed.

Lemma run_only_access_same :
  forall m, veq (run_only Strong g cn cmd m) (run_access Strong g cn cmd m).
Proof.
unfold run_only, run_access, RunOnly.run, RunAccess.run.
destruct cmd; i.
- destruct lv, lh, o
  ; try (i; dest_veq; [by apply eval_access_same|]
         ; i; by apply mem_update_access_same)
  ; try (dest_veq; [by apply eval_lv_access_same|]
         ; i; dest_veq; [by apply eval_access_same|]
         ; i; by apply mem_wupdate_access_same).
- i; unfold RunOnly.set_ext_allocsite, RunAccess.set_ext_allocsite.
  dest_veq; [by apply eval_lv_access_same|].
  i; dest_veq; [by apply mem_wupdate_access_same|].
  i; by apply mem_wupdate_access_same.
- dest_veq; [by apply eval_lv_access_same|].
  i; by apply mem_wupdate_access_same.
- dest_veq; [by apply eval_lv_access_same|].
  i; dest_veq; [by apply mem_wupdate_access_same|].
  i; by apply mem_wupdate_access_same.
- dest_veq; [by apply eval_lv_access_same|].
  i; by apply mem_wupdate_access_same.
- by auto.
- dest_veq; [by apply eval_list_access_same|].
  i; destruct (G.is_undef_e f g); [destruct (is_printf f)|].
  + by apply run_printf_access_same.
  + by apply run_undef_funcs_access_same.
  + dest_veq; [by apply eval_access_same|].
    i; dest_veq.
    * unfold RunOnly.update_rets, RunAccess.update_rets.
      dest_veq; [|i; by apply mem_wupdate_access_same].
      destruct ret_opt; [by apply eval_lv_access_same|by dest_veq].
    * i; apply weak_big_join_access_same; [|by dest_veq].
      i; by apply bind_args_access_same.
- i; destruct ret_opt; [|by dest_veq].
  dest_veq; [by apply eval_access_same|].
  i; dest_veq; [by apply mem_lookup_access_same|].
  i; by apply mem_wupdate_access_same.
- by dest_veq.
- by dest_veq.
Qed.


(* Morphisms *)

Lemma add_mor :
  Proper (Loc.eq ==> Val.eq ==> Mem.eq ==> Acc.MAcc.eq Mem.zb_eq)
         RunAccess.SemMem.add.
Proof.
intros l1 l2 Hl v1 v2 Hv m1 m2 Hm. split.
- by apply DomMem.Mem.add_mor.
- split; s.
  + apply PowLoc.add_mor; [by auto|by apply PowLoc.eq_refl].
  + by apply PowLoc.eq_refl.
Qed.

Lemma weak_add_mor :
  Proper (Loc.eq ==> Val.eq ==> Mem.eq ==> Acc.MAcc.eq Mem.zb_eq)
         (RunAccess.SemMem.weak_add Strong).
Proof.
intros l1 l2 Hl v1 v2 Hv m1 m2 Hm. split.
- by apply DomMem.Mem.weak_add_mor.
- split; s.
  + apply PowLoc.add_mor; [by auto|by apply PowLoc.eq_refl].
  + apply PowLoc.add_mor; [by auto|by apply PowLoc.eq_refl].
Qed.

Lemma mem_update_mor :
  Proper (Loc.eq ==> Val.eq ==> Mem.eq ==> Acc.MAcc.eq Mem.zb_eq)
         (RunAccess.mem_update Strong g).
Proof.
intros l1 l2 Hl v1 v2 Hv m1 m2 Hm
; unfold RunAccess.mem_update, RunAccess.SemMem.mem_update.
remember (RunAccess.SemMem.can_strong_update Strong g l1) as s1.
remember (RunAccess.SemMem.can_strong_update Strong g l2) as s2.
assert (s1 = s2) as Hs
; [ rewrite Heqs1, Heqs2; by apply RunAccess.SemMem.can_strong_update_mor
  | rewrite Hs ].
destruct s2; [by apply add_mor|by apply weak_add_mor].
Qed.

Lemma mem_wupdate_mor :
  Proper
    (PowLoc.eq ==> Val.eq ==> Mem.eq ==> Acc.MAcc.eq Mem.zb_eq)
    (RunAccess.mem_wupdate Strong).
Proof.
intros l1 l2 Hl v1 v2 Hv m1 m2 Hm
; unfold RunAccess.mem_wupdate, RunAccess.SemMem.mem_wupdate.
apply PowLoc.fold_mor.
+ by apply Acc.MAcc.eq_equiv.
+ i; apply bind_mor with (Hteq:=Mem.zb_eq)
  ; [by auto|intros ? ? ?; by apply weak_add_mor].
+ by auto.
+ by apply ret_mor.
Qed.

Lemma acc_add_mor :
  forall m, Proper (Loc.eq ==> DomMem.Acc.eq ==> DomMem.Acc.eq) (DomMem.Acc.add m).
Proof.
intros m l1 l2 Hl a1 a2 Ha; destruct m; split; s.
- apply PowLoc.add_mor; [by apply Hl|by apply Ha].
- by apply Ha.
- by apply Ha.
- apply PowLoc.add_mor; [by apply Hl|by apply Ha].
- apply PowLoc.add_mor; [by apply Hl|by apply Ha].
- apply PowLoc.add_mor; [by apply Hl|by apply Ha].
Qed.

Lemma mem_find_mor :
  Proper (Loc.eq ==> Mem.eq ==> Acc.MAcc.eq Val.zb_eq) DomMem.AccMem.mem_find.
Proof.
intros l1 l2 Hl m1 m2 Hm; unfold DomMem.AccMem.mem_find.
split; [by apply DomMem.Mem.find_mor|by apply acc_add_mor].
Qed.

Lemma mem_lookup_mor :
  Proper (PowLoc.eq ==> Mem.eq ==> Acc.MAcc.eq Val.zb_eq) RunAccess.mem_lookup.
Proof.
intros l1 l2 Hl m1 m2 Hm
; unfold RunAccess.mem_lookup, RunAccess.SemMem.mem_lookup.
apply PowLoc.fold_mor.
+ by apply Acc.MAcc.eq_equiv.
+ i; apply bind_mor with (Hteq:=Val.zb_eq); [by auto|].
  intros v1 v2 Hv.
  apply bind_mor with (Hteq:=Val.zb_eq); [by apply mem_find_mor|].
  intros ? ? ?; apply ret_mor; by apply Val.join_eq.
+ by auto.
+ by apply Acc.MAcc.eq_equiv.
Qed.

Lemma eval_mor :
  forall e, Proper (Mem.eq ==> Acc.MAcc.eq Val.zb_eq) (RunAccess.eval Strong cn e)

with eval_lv_mor :
  forall l, Proper (Mem.eq ==> Acc.MAcc.eq PowLoc.zb_eq)
               (RunAccess.SemEval.eval_lv Strong cn l)

with resolve_offset_mor :
  forall o,
    Proper (Val.eq ==> Mem.eq ==> Acc.MAcc.eq PowLoc.zb_eq)
           (fun v m => RunAccess.SemEval.resolve_offset Strong cn v o m).
Proof.
{ induction e; simpl RunAccess.eval.
- intros ? ? ?; by apply Acc.MAcc.eq_equiv.
- intros ? ? ?; apply bind_mor with (Hteq:=PowLoc.zb_eq)
  ; [by apply eval_lv_mor|].
  intros ? ? ?; by apply mem_lookup_mor.
- intros ? ? ?. by apply Acc.MAcc.eq_equiv.
- intros ? ? ?. by apply Acc.MAcc.eq_equiv.
- intros ? ? ?. by apply Acc.MAcc.eq_equiv.
- intros ? ? ?. by apply Acc.MAcc.eq_equiv.
- intros ? ? ?. by apply Acc.MAcc.eq_equiv.
- intros ? ? ?; apply bind_mor with (Hteq:=Val.zb_eq); [by apply IHe|].
  intros ? ? ?. apply ret_mor. by apply SemEval.eval_uop_mor.
- intros ? ? ?; apply bind_mor with (Hteq:=Val.zb_eq); [by apply IHe1|].
  intros ? ? ?; apply bind_mor with (Hteq:=Val.zb_eq); [by apply IHe2|].
  intros ? ? ?. apply ret_mor. by apply SemEval.eval_bop_mor.
- intros ? ? ?; apply bind_mor with (Hteq:=Val.zb_eq); [by apply IHe2|].
  intros ? ? ?; apply bind_mor with (Hteq:=Val.zb_eq); [by apply IHe3|].
  intros v1 v2 Hv. by apply ret_mor, Val.join_eq.
- intros m1 m2 Hm. destruct i; [|by apply IHe].
  apply bind_mor with (Hteq:=Val.zb_eq); [by apply IHe|].
  intros ? ? ?; apply ret_mor, DomAbs.modify_array_mor; [by auto|].
  by apply DomArrayBlk.ArrayBlk.cast_array_int_mor, DomAbs.array_of_val_mor.
- intros ? ? ?; apply bind_mor with (Hteq:=PowLoc.zb_eq)
  ; [by apply eval_lv_mor|].
  intros ? ? ?; by apply ret_mor, DomAbs.val_of_pow_loc_mor.
- intros ? ? ?; apply bind_mor with (Hteq:=PowLoc.zb_eq)
  ; [by apply eval_lv_mor|].
  intros ? ? ?; by apply ret_mor, DomAbs.val_of_pow_loc_mor. }
{ induction l; simpl RunAccess.SemEval.eval_lv.
intros ? ? ?; eapply bind_mor with (Hteq:=Val.zb_eq).
- destruct lh; [|by apply eval_mor].
  by apply Acc.MAcc.eq_equiv.
- intros ? ? ?; by apply resolve_offset_mor. }
{ induction o; simpl RunAccess.SemEval.resolve_offset.
- intros ? ? ? ? ? ?; by apply ret_mor, SemEval.deref_of_val_mor.
- intros ? ? ? ? ? ?. apply IHo; [|by auto].
  apply DomAbs.val_of_pow_loc_mor, PowLoc.join_eq.
  + apply pow_loc_append_field_mor
    ; [by apply DomAbs.pow_loc_of_val_mor|by apply Field.eq_refl].
  + apply DomArrayBlk.ArrayBlk.pow_loc_of_struct_w_field_mor
    ; [by apply DomAbs.array_of_val_mor|by apply Field.eq_refl].
- intros ? ? ? ? ? ?.
  apply bind_mor with (Hteq:=Val.zb_eq).
  + apply mem_lookup_mor; [|by auto].
    by apply SemEval.deref_of_val_mor.
  + intros ? ? ?; by apply resolve_offset_mor. }
Qed.

Lemma eval_alloc'_mor :
  Proper Val.eq (RunAccess.SemEval.eval_alloc' cn).
Proof. unfold Proper. by apply Val.eq_refl. Qed.

Lemma eval_alloc_mor :
  forall a, Proper Val.eq (RunAccess.SemEval.eval_alloc Strong cn a).
Proof.
destruct a. simpl RunAccess.SemEval.eval_alloc.
unfold Proper. by apply Val.eq_refl.
Qed.

Lemma run_realloc_mor :
  forall l,
    Proper (SetoidList.eqlistA Val.eq ==> Mem.eq ==> Acc.MAcc.eq Mem.zb_eq)
           (RunAccess.run_realloc Strong cn l).
Proof.
intros l v1 v2 Hv m1 m2 Hm; unfold RunAccess.run_realloc.
inversion Hv; subst; [by apply ret_mor|].
inversion H0; subst; [by apply ret_mor|].
apply bind_mor with (Hteq:=PowLoc.zb_eq); [by apply eval_lv_mor|].
intros ? ? ?. apply bind_mor with (Hteq:=Mem.zb_eq).
- apply mem_wupdate_mor; [by auto|by apply eval_alloc'_mor|by auto].
- intros ? ? ?. apply bind_mor with (Hteq:=Val.zb_eq).
  + apply mem_lookup_mor; [|by auto].
    by apply SemEval.deref_of_val_mor.
  + intros ? ? ?. apply mem_wupdate_mor; [|by auto|by auto].
    apply SemEval.deref_of_val_mor.
    by apply eval_alloc'_mor.
Qed.

Lemma run_strlen_mor :
  forall l, Proper (Mem.eq ==> Acc.MAcc.eq Mem.zb_eq)
               (RunAccess.run_strlen Strong cn l).
Proof.
intros ? m1 m2 Hm; unfold RunAccess.run_strlen.
apply bind_mor with (Hteq:=PowLoc.zb_eq); [by apply eval_lv_mor|].
intros ? ? ?. apply mem_wupdate_mor; [by auto|by apply Val.eq_refl|by auto].
Qed.

Lemma external_value_mor :
  forall a, Proper (DPos.eq ==> DomAbs.Val.eq) (RunAccess.external_value a).
Proof.
intros a ? ? ?. unfold RunAccess.external_value.
destruct (DomBasic.proc_of_allocsite a).
- split; [split; [split|]|]; s.
  + apply PowExtProcPos.singleton_mor; split; by s.
  + by apply PowLoc.eq_refl.
  + by apply DomArrayBlk.ArrayBlk.eq_refl.
  + by apply PowProc.eq_refl.
- split; [split; [split|]|]; s.
  + apply PowExtProcPos.singleton_mor; split; by s.
  + by apply PowLoc.eq_refl.
  + by apply DomArrayBlk.ArrayBlk.eq_refl.
  + by apply PowProc.eq_refl.
Qed.

Lemma set_ext_allocsite_mor :
  forall l a,
    Proper (DPos.eq ==> Mem.eq ==> Acc.MAcc.eq Mem.zb_eq)
           (RunAccess.set_ext_allocsite Strong cn l a).
Proof.
intros ? ? p1 p2 Hp m1 m2 Hm; unfold RunAccess.set_ext_allocsite.
apply bind_mor with (Hteq:=PowLoc.zb_eq); [by apply eval_lv_mor|].
intros ? ? ?. apply bind_mor with (Hteq:=Mem.zb_eq).
- apply mem_wupdate_mor; [by auto| |by auto].
  by apply external_value_mor.
- intros ? ? ?. apply mem_wupdate_mor; [by auto| |by auto].
  by apply external_value_mor.
Qed.

Lemma val_joins_mor :
  Proper (SetoidList.eqlistA Val.eq ==> Val.eq) RunAccess.val_joins.
Proof.
intros vs1 vs2 Hvs. unfold RunAccess.val_joins.
apply list_fold_mor2 with (u_eq:=Val.eq); [|by auto|by apply Val.eq_refl].
intros ? ? ? ? ? ?; by apply Val.join_eq.
Qed.

Lemma val_equiv : Equivalence Val.eq.
Proof.
  constructor.
  - unfold Reflexive; i; by apply Val.eq_refl.
  - unfold Symmetric; i; by apply Val.eq_sym.
  - unfold Transitive; i; eapply Val.eq_trans; by eauto.
Qed.

Lemma dst_equiv : Equivalence StringFun.dst_eq.
Proof.
  constructor.
  - unfold Reflexive; i; by apply (DLat.zb_equiv_refl StringFun.dst_zb_eq).
  - unfold Symmetric; i; by apply (DLat.zb_equiv_sym StringFun.dst_zb_eq).
  - unfold Transitive; i; eapply (DLat.zb_equiv_trans StringFun.dst_zb_eq)
    ; by eauto.
Qed.

Lemma get_dstsrc_list_mor :
  Proper
    (SetoidList.eqlistA Val.eq ==> Logic.eq
                        ==> SetoidList.eqlistA StringFun.dst_eq
                        ==> SetoidList.eqlistA Val.eq
                        ==> DLat.pair_eq (SetoidList.eqlistA StringFun.dst_eq)
                                         (SetoidList.eqlistA Val.eq))
    StringFun.get_dstsrc_list.
Proof.
intros vs1 vs2 Hvs args' args Hargs; subst.
generalize vs1 vs2 Hvs; clear vs1 vs2 Hvs.
induction args.
- i; simpl StringFun.get_dstsrc_list.
  inversion Hvs; subst; by constructor.
- i. simpl StringFun.get_dstsrc_list.
  inversion Hvs; subst; destruct a.
  + destruct va_arg; [by constructor|by apply IHargs].
  + destruct va_arg; [by constructor|by apply IHargs].
  + by constructor.
  + destruct va_arg.
    * intros ? ? ? ? ? ?; apply IHargs; [by auto|by auto|by constructor].
    * intros ? ? ? ? ? ?; apply IHargs; [by auto|by auto|].
      apply SetoidList.eqlistA_app; [by apply val_equiv|by auto|by auto].
  + destruct va_arg.
    * intros ? ? ? ? ? ?; apply IHargs
      ; [by auto|constructor; [by constructor|by auto]|by auto].
    * intros ? ? ? ? ? ?; apply IHargs; [by constructor| |by auto].
      apply SetoidList.eqlistA_app; [by apply dst_equiv| |by auto].
      apply list_map_mor with (t_eq:=Val.eq); [by constructor|by auto].
  + by apply IHargs.
Qed.

Lemma va_src_val_joins_mor :
  Proper (SetoidList.eqlistA Val.eq ==> Mem.eq ==> Acc.MAcc.eq Val.zb_eq)
         RunAccess.va_src_val_joins.
Proof.
intros ? ? Hl ? ? Hm; unfold RunAccess.va_src_val_joins.
apply list_fold_mor2 with (u_eq:=Val.eq)
; [|by auto|by apply ret_mor, Val.eq_refl].
intros ? ? Hv ? ? Ha; apply bind_mor with (Hteq:=Val.zb_eq)
; [apply mem_lookup_mor; [by apply SemEval.deref_of_val_mor|by auto]|].
intros ? ? ?. apply bind_mor with (Hteq:=Val.zb_eq); [by auto|].
intros ? ? ?. apply ret_mor.
apply Val.join_eq; [apply Val.join_eq|]; by auto.
Qed.

Lemma va_arg_joins_mor :
  forall args,
    Proper (Mem.eq ==> Acc.MAcc.eq Val.zb_eq)
           (RunAccess.va_arg_joins Strong cn args).
Proof.
i; intros m1 m2 Hm; unfold RunAccess.va_arg_joins.
apply list_fold_mor; [|by auto|by apply ret_mor, Val.eq_refl].
intros e1 e2 He v1 v2 Hv; subst.
apply bind_mor with (Hteq:=Val.zb_eq); [by auto|].
intros a1 a2 Ha. apply bind_mor with (Hteq:=Val.zb_eq); [by apply eval_mor|].
intros v3 v4 Hv'. apply bind_mor with (Hteq:=Val.zb_eq); [by apply eval_mor|].
intros v5 v6 Hv''; apply ret_mor
; apply Val.join_eq; [by apply Val.join_eq|by auto].
Qed.

Lemma run_printf_pointer_mor :
  forall e args,
    Proper (Mem.eq ==> Acc.MAcc.eq Mem.zb_eq)
           (RunAccess.run_printf_pointer Strong cn e args).
Proof.
i; intros ? ? ?; unfold RunAccess.run_printf_pointer.
apply bind_mor with (Hteq:=Val.zb_eq); [by apply eval_mor|].
intros ? ? ?; apply bind_mor with (Hteq:=Val.zb_eq)
; [by apply va_arg_joins_mor|].
intros ? ? ?; apply mem_wupdate_mor
; [ by apply SemEval.deref_of_val_mor
  | by apply val_of_pow_proc_pos_mor, pow_proc_pos_of_val_mor
  | by auto ].
Qed.

Lemma run_printf_ppointer_mor :
  forall e args,
    Proper (Mem.eq ==> Acc.MAcc.eq Mem.zb_eq)
           (RunAccess.run_printf_ppointer Strong cn e args).
Proof.
i; intros ? ? ?; unfold RunAccess.run_printf_ppointer.
apply bind_mor with (Hteq:=Val.zb_eq); [by apply eval_mor|].
intros ? ? ?; apply bind_mor with (Hteq:=Val.zb_eq)
; [by apply va_arg_joins_mor|].
intros ? ? ?. apply bind_mor with (Hteq:=Mem.zb_eq).
- apply mem_wupdate_mor
  ; [ by apply SemEval.deref_of_val_mor
    | by apply eval_alloc'_mor
    | by auto ].
- intros ? ? ?; apply mem_wupdate_mor
  ; [ by apply SemEval.deref_of_val_mor, eval_alloc'_mor
    | by apply val_of_pow_proc_pos_mor, pow_proc_pos_of_val_mor
    | by auto ].
Qed.

Lemma run_printf1_mor :
  Proper (Mem.eq ==> Acc.MAcc.eq Mem.zb_eq) RunAccess.run_printf1.
Proof. by auto. Qed.

Lemma run_printf2_mor :
  forall p args,
    Proper (Mem.eq ==> Acc.MAcc.eq Mem.zb_eq)
           (RunAccess.run_printf2 Strong cn p args).
Proof.
i; intros ? ? ?; unfold RunAccess.run_printf2.
destruct args; [by auto|].
destruct args; [by auto|].
dest_if_dec; [by apply run_printf_ppointer_mor|].
dest_if_dec; by apply run_printf_pointer_mor.
Qed.

Lemma run_printf3_mor :
  forall args,
    Proper (Mem.eq ==> Acc.MAcc.eq Mem.zb_eq)
           (RunAccess.run_printf3 Strong cn args).
Proof.
i; intros ? ? ?; unfold RunAccess.run_printf3.
destruct args; [by auto|].
destruct args; [by auto|].
destruct args; [by auto|].
by apply run_printf_pointer_mor.
Qed.

Lemma run_printf_mor :
  forall p args,
    Proper (Mem.eq ==> Acc.MAcc.eq Mem.zb_eq)
           (RunAccess.run_printf Strong cn p args).
Proof.
i; intros ? ? ?; unfold RunAccess.run_printf.
dest_if_dec.
dest_if_dec; [by apply run_printf2_mor|].
dest_if_dec; by apply run_printf3_mor.
Qed.

Lemma process_dsts_mor :
  Proper (DPos.eq ==> Logic.eq ==> SetoidList.eqlistA StringFun.dst_eq
                  ==> Val.eq ==> Mem.eq ==> Acc.MAcc.eq Mem.zb_eq)
         (RunAccess.process_dsts Strong cn).
Proof.
intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?; subst; unfold RunAccess.process_dsts.
apply list_fold_mor2 with (u_eq:=StringFun.dst_eq); [|by auto|by apply ret_mor].
intros ? ? ? ? ? ?. apply bind_mor with (Hteq:=Mem.zb_eq); [by auto|].
intros ? ? ?. inversion H0; subst.
destruct a2, s2.
- apply mem_wupdate_mor; [by apply SemEval.deref_of_val_mor|by auto|by auto].
- apply mem_wupdate_mor
  ; [ by apply SemEval.deref_of_val_mor
    | by apply external_value_mor
    | by auto ].
- apply bind_mor with (Hteq:=Mem.zb_eq).
  + apply mem_wupdate_mor
    ; [ by apply SemEval.deref_of_val_mor
      | by apply eval_alloc'_mor
      | by auto ].
  + intros ? ? ?; apply mem_wupdate_mor
    ; [ by apply SemEval.deref_of_val_mor, eval_alloc'_mor
      | by apply val_of_pow_proc_pos_mor, pow_proc_pos_of_val_mor
      | by auto ].
- apply bind_mor with (Hteq:=Mem.zb_eq).
  + apply mem_wupdate_mor
    ; [ by apply SemEval.deref_of_val_mor
      | by apply eval_alloc'_mor
      | by auto ].
  + intros ? ? ?; apply mem_wupdate_mor
    ; [ by apply pow_loc_of_val_mor, eval_alloc'_mor
      | by apply val_of_pow_proc_pos_mor, pow_proc_pos_of_val_mor
           , external_value_mor
      | by auto ].
Qed.

Lemma process_ret_mor :
  Proper (DPos.eq ==> Logic.eq ==> Logic.eq ==> Logic.eq
                  ==> SetoidList.eqlistA StringFun.dst_eq ==> Val.eq
                  ==> Mem.eq ==> Acc.MAcc.eq Mem.zb_eq)
         (RunAccess.process_ret Strong cn).
Proof.
intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?; subst.
unfold RunAccess.process_ret.
destruct y2; [|by apply ret_mor].
apply bind_mor with (Hteq:=PowLoc.zb_eq); [by apply eval_lv_mor|].
intros ? ? ?; destruct (StringFun.ret y1).
- apply mem_wupdate_mor; by auto using Val.eq_refl.
- apply mem_wupdate_mor; [by auto|by apply external_value_mor|by auto].
- destruct alloc; [apply mem_wupdate_mor; by auto|].
  apply bind_mor with (Hteq:=Mem.zb_eq).
  + apply mem_wupdate_mor; [by auto|by apply eval_alloc'_mor|by auto].
  + intros ? ? ?; apply mem_wupdate_mor
    ; [ by auto
      | by apply val_of_pow_proc_pos_mor, pow_proc_pos_of_val_mor
      | by auto ].
- apply mem_wupdate_mor; [by auto| |by auto].
  apply val_joins_mor, list_map_mor with (t_eq:=StringFun.dst_eq); [|by auto].
  intros d1 d2 Hd; inversion Hd; by subst.
Qed.

Lemma run_api_mor :
  Proper
    (Logic.eq ==> SetoidList.eqlistA Val.eq ==> DPos.eq
            ==> Logic.eq ==> Logic.eq ==> Mem.eq ==> Acc.MAcc.eq Mem.zb_eq)
    (RunAccess.run_api Strong cn).
Proof.
intros r1 r2 Hr l1 l2 Hl p1 p2 Hp s1 s2 Hs f1 f2 Hf m1 m2 Hm; subst.
unfold RunAccess.run_api.
remember (StringFun.get_dstsrc_list l1 (StringFun.args f2) nil nil) as p
; destruct p as [dsts1 srcs1].
remember (StringFun.get_dstsrc_list l2 (StringFun.args f2) nil nil) as q
; destruct q as [dsts2 srcs2].
assert (Hds : DLat.pair_eq (SetoidList.eqlistA StringFun.dst_eq)
                           (SetoidList.eqlistA Val.eq)
                           (dsts1, srcs1) (dsts2, srcs2))
; [rewrite Heqp, Heqq; by apply get_dstsrc_list_mor|].
inversion Hds as [? ? Hdsts_eq ? ? Hsrcs_eq]; subst.
apply bind_mor with (Hteq:=Val.zb_eq); [by apply va_src_val_joins_mor|].
intros ? ? ?; apply bind_mor with (Hteq:=Mem.zb_eq)
; [by apply process_dsts_mor|].
intros ? ? ?; apply bind_mor with (Hteq:=Mem.zb_eq)
; [by apply process_ret_mor|].
intros ? ? ?; by apply ret_mor.
Qed.

Lemma run_undef_funcs_mor :
  forall ret_opt p,
    Proper (SetoidList.eqlistA Val.eq ==> DPos.eq ==> Mem.eq
                               ==> Acc.MAcc.eq Mem.zb_eq)
           (RunAccess.run_undef_funcs Strong cn ret_opt p).
Proof.
i. intros vs1 vs2 Hvs p1 p2 Hp m1 m2 Hm. unfold RunAccess.run_undef_funcs.
unfold RunAccess.run_api_with_name.
destruct (RunAccess.find_string_api_name p); [by apply run_api_mor|].
destruct ret_opt; [by apply set_ext_allocsite_mor|].
by apply ret_mor.
Qed.

Lemma list_fold2_m_mor T U V :
  forall (teq : T -> T -> Prop) (ueq : U -> U -> Prop)
     (veq : V -> V -> Prop) (v_zb_eq : DLat.zb_equiv veq),
    Proper ((teq ==> ueq ==> veq ==> Acc.MAcc.eq v_zb_eq)
              ==> SetoidList.eqlistA teq ==> SetoidList.eqlistA ueq ==> veq
              ==> Acc.MAcc.eq v_zb_eq)
           RunAccess.SemMem.list_fold2_m.
Proof.
intros ? ? ? ? f1 f2 Hf ts1 ts2 Hts. induction Hts.
- intros us1 us2 Hus v1 v2 Hv; s.
  inversion Hus; [by apply ret_mor|by apply ret_mor].
- intros us1 us2 Hus v1 v2 Hv; s.
  inversion Hus; [by apply ret_mor|].
  apply bind_mor with (Hteq:=v_zb_eq); [by apply Hf|by apply IHHts].
Qed.

Lemma bind_arg_mor :
  forall f x,
    Proper (Val.eq ==> Mem.eq ==> Acc.MAcc.eq Mem.zb_eq)
           (RunAccess.SemMem.bind_arg Strong f x).
Proof.
intros f x v1 v2 Hv m1 m2 Hm. unfold RunAccess.SemMem.bind_arg.
apply mem_wupdate_mor; [by apply PowLoc.eq_refl|by auto|by auto].
Qed.

Lemma bind_args_mor :
  Proper (SetoidList.eqlistA Val.eq ==> eq ==> Mem.eq
                             ==> Acc.MAcc.eq Mem.zb_eq)
         (RunAccess.SemMem.bind_args Strong g).
Proof.
intros vs1 vs2 Hvs v1 v2 Hv m1 m2 Hm; subst.
unfold RunAccess.SemMem.bind_args; destruct (InterCfg.get_args (G.icfg g) v2)
; [|by apply ret_mor].
apply list_fold2_m_mor with (teq:=eq) (ueq:=Val.eq)
; [|by apply eqlistA_eq_refl|by auto|by auto].
intros ? ? ? ? ? ? ? ? ?; subst. by apply bind_arg_mor.
Qed.

Lemma weak_big_join_mor :
  Proper ((eq ==> Mem.eq ==> Acc.MAcc.eq Mem.zb_eq)
            ==> PowProc.eq ==> Acc.MAcc.eq Mem.zb_eq ==> Acc.MAcc.eq Mem.zb_eq)
         RunAccess.BJProcMem.weak_big_join.
Proof.
intros f1 f2 Hf l1 l2 Hl m1 m2 Hm. unfold RunAccess.BJProcMem.weak_big_join.
apply PowProc.fold_mor; [by apply Acc.MAcc.eq_equiv| |by auto|by auto].
intros; subst. eapply bind_mor; [by apply Hacc|].
intros m1' m2' Hm'. by apply Hf.
Qed.

Lemma SMProcLoc_map_mor :
  Proper ((eq ==> Loc.eq) ==> PowProc.eq ==> PowLoc.eq) SMProcLoc.map.
Proof.
intros f1 f2 Hf p1 p2 Hp. unfold SMProcLoc.map.
apply PowProc.fold_mor
; [by apply PowLoc.zb_eq| |by auto|by apply PowLoc.eq_refl].
intros; subst.
apply PowLoc.add_mor; [by apply Hf|by auto].
Qed.

Lemma update_rets_mor :
  Proper
    (PowProc.eq ==> eq ==> Mem.eq ==> Acc.MAcc.eq Mem.zb_eq)
    (RunAccess.update_rets Strong cn).
Proof.
intros l1 l2 Hl lv1 lv2 Hlv m1 m2 Hm; subst.
unfold RunAccess.update_rets.
apply bind_mor with (Hteq:=PowLoc.zb_eq).
- destruct lv2; [by apply eval_lv_mor|by apply ret_mor].
- intros ret_loc1 ret_loc2 Hret_loc.
  apply mem_wupdate_mor; [|by apply DomAbs.val_of_pow_loc_mor|by auto].
  apply SMProcLoc_map_mor; [|by auto].
  intros ? ? ?; subst. by apply loc_of_proc_mor.
Qed.

Lemma eval_list_mor :
  forall args, Proper (Mem.eq ==> Acc.MAcc.eq list_val_zb_eq)
                  (RunAccess.SemEval.eval_list Strong cn args).
Proof.
induction args; intros ? ? ?.
- split; [by constructor|by apply Acc.eq_refl].
- s. apply bind_mor with (Hteq:=Val.zb_eq).
  + by apply eval_mor.
  + intros ? ? ?. apply bind_mor with (Hteq:=list_val_zb_eq).
    * by apply IHargs.
    * intros ? ? ?. apply ret_mor. by constructor.
Qed.

Ltac mor :=
repeat match goal with
| |- Val.eq ?x ?x => by apply Val.eq_refl
| |- Itv.eq ?x ?x => by apply Itv.eq_refl
| |- Mem.eq ?x ?x => by apply Mem.eq_refl
| |- Allocsite.eq ?x ?x => by apply Allocsite.eq_refl
| H : ?eq ?x ?y |- ?eq ?x ?y => by apply H
| |- Acc.MAcc.eq _ ?x ?x => by apply (DLat.zb_equiv_refl (Acc.MAcc.eq_equiv _))
| |- Proper _ _ => intros ? ? ?
| |- (_ ==> _)%signature _ _ => intros ? ? ?
| H : Val.eq ?y ?x |- Val.eq ?x ?y => apply Val.eq_sym
| |- Acc.MAcc.eq _ (if _ then _ else _) (if _ then _ else _) => apply if_dec_mor
| |- Itv.eq ?x1 ?y1 -> Itv.eq ?x2 ?y2 =>
  let Heq := fresh "Heq" in
  intro Heq; apply Itv.eq_trans with x1
  ; [ apply Itv.eq_sym
    | apply Itv.eq_trans with y1; [by apply Heq|] ]
| |- Acc.MAcc.eq Val.zb_eq (RunAccess.SemEval.eval _ _ _ _)
                (RunAccess.SemEval.eval _ _ _ _) =>
  apply eval_mor
| |- Acc.MAcc.eq Val.zb_eq (RunAccess.eval _ _ _ _)
                (RunAccess.eval _ _ _ _) =>
  apply eval_mor
| |- Acc.MAcc.eq _ (if Sumbool.sumbool_not ?A (?A -> False) ?HA then _ else _)
                (if Sumbool.sumbool_not ?B (?B -> False) ?HB then _ else _) =>
  let Heq := fresh "Heq" in
  let Ha := fresh "Ha" in
  let Hb := fresh "Hb" in
  assert (A <-> B) as Heq
  ; [| destruct (Sumbool.sumbool_not A (~ A) HA) as [Ha | Ha]
              , (Sumbool.sumbool_not B (~ B) HB) as [Hb | Hb]
       ; [|elim Ha; by apply Heq, Hb|elim Hb; by apply Heq, Ha|]
       ; clear Heq ]
| |- _ <-> _ => split
| |- Itv.le _ _ -> Itv.le _ _ =>
  let Htemp := fresh "Htemp" in
  intro Htemp; eapply Itv.le_trans; [eapply Itv.le_trans; [|apply Htemp]|]
| |- Itv.le _ _ => apply Itv.le_refl
| |- Acc.MAcc.eq _ (Acc.MAcc.bind _ _) (Acc.MAcc.bind _ _) =>
  first [ apply bind_mor with (Hteq:=Val.zb_eq)
        | apply bind_mor with (Hteq:=PowLoc.zb_eq)
        | apply bind_mor with (Hteq:=Mem.zb_eq)
        | apply bind_mor with (Hteq:=list_val_zb_eq) ]
| |- Acc.MAcc.eq _ (Acc.MAcc.ret _) (Acc.MAcc.ret _) => apply ret_mor
| |- Val.eq (SemEval.eval_uop _ _) (SemEval.eval_uop _ _) =>
  apply SemEval.eval_uop_mor
| |- Acc.MAcc.eq Val.zb_eq
    (RunAccess.SemEval.SemMem.mem_lookup _ _)
    (RunAccess.SemEval.SemMem.mem_lookup _ _) =>
  apply mem_lookup_mor
| |- Val.eq (SemEval.eval_bop _ _ _) (SemEval.eval_bop _ _ _) =>
  apply SemEval.eval_bop_mor
| |- Val.eq (DomAbs.val_of_pow_proc_pos _) (DomAbs.val_of_pow_proc_pos _) =>
  apply DomAbs.val_of_pow_proc_pos_mor
| |- PowExtProcPos.eq (DomAbs.pow_proc_pos_of_val _) (DomAbs.pow_proc_pos_of_val _) =>
  apply DomAbs.pow_proc_pos_of_val_mor
| |- Val.eq (DomAbs.modify_array _ _) (DomAbs.modify_array _ _) =>
  apply modify_array_mor
| |- DomArrayBlk.ArrayBlk.eq
      (DomArrayBlk.ArrayBlk.cast_array_int _ _)
      (DomArrayBlk.ArrayBlk.cast_array_int _ _) =>
  apply DomArrayBlk.ArrayBlk.cast_array_int_mor
| |- DomArrayBlk.ArrayBlk.eq (DomAbs.array_of_val _) (DomAbs.array_of_val _) =>
  apply DomAbs.array_of_val_mor
| |- Val.eq (DomAbs.val_of_pow_loc _) (DomAbs.val_of_pow_loc _) =>
  apply DomAbs.val_of_pow_loc_mor
| |- PowLoc.eq (DomAbs.pow_loc_of_val _)
              (DomAbs.pow_loc_of_val _) =>
  apply DomAbs.pow_loc_of_val_mor
| |- Acc.MAcc.eq PowLoc.zb_eq
      (RunAccess.SemEval.resolve_offset _ _ _ _ _)
      (RunAccess.SemEval.resolve_offset _ _ _ _ _) =>
  apply resolve_offset_mor
| |- PowLoc.eq (SemEval.deref_of_val _) (SemEval.deref_of_val _) =>
  apply SemEval.deref_of_val_mor
| |- DomArrayBlk.ArrayBlk.eq (DomArrayBlk.ArrayBlk.plus_offset _ _)
                            (DomArrayBlk.ArrayBlk.plus_offset _ _) =>
  apply DomArrayBlk.ArrayBlk.plus_offset_mor
| |- Acc.MAcc.eq Mem.zb_eq (RunAccess.mem_update _ _ _ _ _)
                (RunAccess.mem_update _ _ _ _ _) =>
  apply mem_update_mor
| |- Acc.MAcc.eq Mem.zb_eq (RunAccess.mem_wupdate _ _ _ _)
                (RunAccess.mem_wupdate _ _ _ _) =>
  apply mem_wupdate_mor
| |- PowLoc.eq (PowLoc.singleton _) (PowLoc.singleton _) =>
  apply PowLoc.singleton_mor
| |- context[Loc.eq'] => replace Loc.eq' with Loc.eq by auto
| |- Loc.eq (DomBasic.loc_of_allocsite _) (DomBasic.loc_of_allocsite _) =>
  apply loc_of_allocsite_mor
| |- Val.eq (RunAccess.SemEval.eval_alloc' _ _)
           (RunAccess.SemEval.eval_alloc' _ _) =>
  apply eval_alloc'_mor
| |- Acc.MAcc.eq Val.zb_eq (RunAccess.SemMem.mem_lookup _ _)
                (RunAccess.SemMem.mem_lookup _ _) =>
  apply mem_lookup_mor
| |- Acc.MAcc.eq Val.zb_eq (RunAccess.mem_lookup _ _)
                (RunAccess.mem_lookup _ _) =>
  apply mem_lookup_mor
| |- Acc.MAcc.eq Mem.zb_eq (RunAccess.SemMem.mem_update _ _ _ _ _)
                (RunAccess.SemMem.mem_update _ _ _ _ _) =>
  apply mem_update_mor
| |- Acc.MAcc.eq Mem.zb_eq (RunAccess.mem_update _ _ _ _ _)
                (RunAccess.mem_update _ _ _ _ _) =>
  apply mem_update_mor
| |- Acc.MAcc.eq list_val_zb_eq (RunAccess.SemEval.eval_list _ _ _ _)
                (RunAccess.SemEval.eval_list _ _ _ _) =>
  apply eval_list_mor
| |- Val.eq (Val.join _ _) (Val.join _ _) => apply Val.join_eq
| |- Mem.eq (Mem.join _ _) (Mem.join _ _) => apply Mem.join_eq
| |- Itv.eq (Itv.meet _ _) (Itv.meet _ _) => apply Itv.meet_eq
| |- Itv.eq (Itv.join _ _) (Itv.join _ _) => apply Itv.join_eq
| |- SetoidList.eqlistA Val.eq _ _ => constructor
| H : SetoidList.eqlistA _ ?x ?y |- SetoidList.eqlistA _ ?x ?y =>
  by apply H
end.

(* Soundness *)

Lemma add_access_sound :
  forall e v, aeqm1 (RunAccess.SemMem.add e v).
Proof.
unfold RunAccess.SemMem.add, DomMem.AccMem.mem_add; s; i.
unfold aeqm1; s; i. split; [|by apply Acc.eq_refl].
intro k; destruct (Loc.eq_dec k e).
- eapply Val.eq_trans; [apply Mem.add_same; by apply e0|].
  eapply Val.eq_trans; [|by apply Val.eq_sym, Mem.join_find].
  eapply Val.eq_trans; [by apply Val.join_bot|].
  apply Val.join_eq; [by apply Val.eq_sym, Mem.add_same|].
  apply Val.eq_sym, Hm'.
  by apply Acc.mem_accessof_left, PowLoc.mem_add_1.
- eapply Val.eq_trans; [rewrite Mem.add_diff; [by apply Val.eq_refl|by auto]|].
  eapply Val.eq_trans; [|by apply Val.eq_sym, Mem.join_find].
  eapply Val.eq_trans; [by apply Mem.join_find|].
  apply Val.join_eq; [|by apply Val.eq_refl].
  rewrite Mem.add_diff; [|by auto].
  by apply Val.eq_refl.
Qed.

Lemma weak_add_access_sound :
  forall e v, aeqm1 (RunAccess.SemMem.weak_add Strong e v).
Proof.
unfold RunAccess.SemMem.weak_add, DomMem.AccMem.mem_weak_add; s; i.
unfold aeqm1; s; i. split; [|by apply Acc.eq_refl].
intro k; destruct (Loc.eq_dec k e).
- eapply Val.eq_trans; [apply Val.eq_sym, Mem.weak_add_prop; by auto|].
  eapply Val.eq_trans; [|by apply Val.eq_sym, Mem.join_find].
  eapply Val.eq_trans
  ; [apply Val.join_eq; [by apply Val.eq_refl|by apply Mem.join_find]|].
  eapply Val.eq_trans; [by apply Val.join_assoc|].
  apply Val.join_eq; [|apply Mem.find_mor; [by auto|by apply Mem.eq_refl]].
  by apply Mem.weak_add_prop.
- eapply Val.eq_trans
  ; [rewrite Mem.weak_add_diff; [by apply Val.eq_refl|by auto]|].
  eapply Val.eq_trans; [|by apply Val.eq_sym, Mem.join_find].
  eapply Val.eq_trans; [by apply Mem.join_find|].
  apply Val.join_eq; [|by apply Val.eq_refl].
  rewrite Mem.weak_add_diff; [|by auto].
  by apply Val.eq_refl.
Qed.

Lemma mem_update_access_sound :
  forall k v, aeqm1 (RunAccess.mem_update Strong g k v).
Proof.
unfold RunAccess.mem_update, RunAccess.SemMem.mem_update; i.
destruct (RunAccess.SemMem.can_strong_update Strong g k).
- by apply add_access_sound.
- by apply weak_add_access_sound.
Qed.

Lemma mem_wupdate_access_sound :
  forall k v, aeqm1 (RunAccess.mem_wupdate Strong k v).
Proof.
unfold RunAccess.mem_wupdate, RunAccess.SemMem.mem_wupdate; i.
- remember
    (fun (lv : Loc.t) m_a =>
       DomMem.Acc.MAcc.bind m_a (RunAccess.SemMem.weak_add Strong lv v))
  as f.
  apply ret_mem2, fold_access_sound.
  + subst; i; destruct m; s.
    by apply Acc.join_left.
  + subst; i. apply bind_mmem. by apply weak_add_access_sound.
  + intros e m1 m2 Hm. subst.
    eapply bind_mor; [by apply Hm|].
    intros m1' m2' Hm'.
    apply weak_add_mor; [by apply Loc.eq_refl|by apply Val.eq_refl|by auto].
Qed.

Lemma mem_find_access_sound :
  forall e, aeqv Val.zb_eq (DomMem.AccMem.mem_find e).
Proof.
unfold aeqv, DomMem.AccMem.mem_find; s; i.
split; [|by apply Acc.eq_refl].
eapply Val.eq_trans; [by apply Mem.join_find|].
eapply Val.eq_trans; [|by apply Val.eq_sym, Val.join_bot].
apply Val.join_eq; [by apply Val.eq_refl|].
apply Hm'. by apply Acc.mem_accessof_right, PowLoc.mem_add_1, Loc.eq_refl.
Qed.

Lemma mem_lookup_access_sound :
  forall l, aeqv Val.zb_eq (RunAccess.mem_lookup l).
Proof.
unfold RunAccess.mem_lookup, RunAccess.SemMem.mem_lookup; i.
match goal with
| |- aeqv _ (fun m => ?e _) => apply aeqmv_1 with (f:= fun m => e)
end.
apply fold_access_sound'.
- i. destruct v. s. by apply Acc.join_left.
- i. apply bind_mval. i. apply aeqv_1 with (Hteq:=Val.zb_eq).
  + intros v1 v2 Hv.
    apply ret_mor, Val.join_eq; [by apply Val.eq_refl|by auto].
  + by apply mem_find_access_sound.
- i. intros ? ? ?. apply bind_mor with (Hteq:=Val.zb_eq); [by auto|].
  intros ? ? ?. apply bind_mor with (Hteq:=Val.zb_eq).
  + apply mem_find_mor; [by apply Loc.eq_refl|by apply Mem.eq_refl].
  + intros ? ? ?. apply ret_mor. by apply Val.join_eq.
Qed.

Lemma eval_access_sound : forall e, aeqv Val.zb_eq (RunAccess.eval Strong cn e)

with eval_lv_access_sound :
  forall lv, aeqv PowLoc.zb_eq (RunAccess.SemEval.eval_lv Strong cn lv)

with resolve_offset_sound :
  forall o x, aeqv PowLoc.zb_eq
             (RunAccess.SemEval.resolve_offset Strong cn x o).
Proof.
induction e; simpl RunAccess.eval.
{ by apply aeqv_3. }
{ apply aeqv_2 with (Hteq:=PowLoc.zb_eq)
  ; [by apply mem_lookup_access_sound|by mor|].
  by apply eval_lv_access_sound. }
{ by apply aeqv_3. }
{ by apply aeqv_3. }
{ by apply aeqv_3. }
{ by apply aeqv_3. }
{ by apply aeqv_3. }
{ apply aeqv_2 with (Hteq:=Val.zb_eq); [i|by mor|by apply IHe].
  by apply aeqv_3. }
{ apply aeqv_2 with (Hteq:=Val.zb_eq); [i|by mor|by apply IHe1].
  apply aeqv_2 with (Hteq:=Val.zb_eq); [i|by mor|by apply IHe2].
  by apply aeqv_3. }
{ apply aeqv_2 with (Hteq:=Val.zb_eq); [i|by mor|by apply IHe2].
  apply aeqv_2 with (Hteq:=Val.zb_eq); [i|by mor|by apply IHe3].
  by apply aeqv_3. }
{ destruct i.
  - apply aeqv_2 with (Hteq:=Val.zb_eq); [i|by mor|by apply IHe].
    by apply aeqv_3.
  - by apply IHe. }
{ apply aeqv_1 with (Hteq:=PowLoc.zb_eq); [by mor|].
  by apply eval_lv_access_sound. }
{ apply aeqv_1 with (Hteq:=PowLoc.zb_eq); [by mor|].
  by apply eval_lv_access_sound. }

destruct lv; simpl RunAccess.SemEval.eval_lv.
{ apply aeqv_2 with (Hteq:=Val.zb_eq); [|by mor|].
  - by apply resolve_offset_sound.
  - destruct lh.
    + by apply aeqv_3.
    + by apply eval_access_sound. }

induction o; simpl RunAccess.SemEval.resolve_offset; i.
{ by apply aeqv_3. }
{ by apply IHo. }
{ apply aeqv_2 with (Hteq:=Val.zb_eq)
  ; [i|by mor|by apply mem_lookup_access_sound].
  by apply IHo. }
Qed.

Lemma set_ext_allocsite_access_sound :
  forall lv a p, aeqm1 (RunAccess.set_ext_allocsite
                    Strong cn lv (allocsite_of_ext a) p).
Proof.
i; unfold RunAccess.set_ext_allocsite.
apply bind_val1 with (Ht:=PowLoc.zb_eq)
; [i|by mor|by apply eval_lv_access_sound].
apply bind_mem1; [|by mor|by apply mem_wupdate_access_sound].
by apply mem_wupdate_access_sound.
Qed.

Lemma eval_list_access_sound :
  forall args, aeqv list_val_zb_eq
                (RunAccess.SemEval.eval_list Strong cn args).
Proof.
induction args.
- s. apply aeqv_3.
- s. apply aeqv_2 with (Hteq:=Val.zb_eq); [i|by mor|by apply eval_access_sound].
  apply aeqv_1 with (Hteq:=list_val_zb_eq); [by mor|by apply IHargs].
Qed.

Lemma run_realloc_access_sound :
  forall l v, aeqm1 (RunAccess.run_realloc Strong cn l v).
Proof.
i; unfold RunAccess.run_realloc.
destruct v; [apply ret_mem1; i; by apply Mem.eq_refl|].
destruct v; [apply ret_mem1; i; by apply Mem.eq_refl|].
apply bind_val1 with (Ht:=PowLoc.zb_eq)
; [i|by mor|by apply eval_lv_access_sound].
apply bind_mem1; [i|by mor|by apply mem_wupdate_access_sound].
apply bind_val1 with (Ht:=Val.zb_eq)
; [i|by mor|by apply mem_lookup_access_sound].
by apply mem_wupdate_access_sound.
Qed.

Lemma run_strlen_access_sound :
  forall l, aeqm1 (RunAccess.run_strlen Strong cn l).
Proof.
unfold RunAccess.run_strlen; i.
apply bind_val1 with (Ht:=PowLoc.zb_eq)
; [i|by mor|by apply eval_lv_access_sound].
by apply mem_wupdate_access_sound.
Qed.

Lemma va_src_val_joins_access_sound :
  forall l, aeqv Val.zb_eq (RunAccess.va_src_val_joins l).
Proof.
i; unfold RunAccess.va_src_val_joins.
apply list_fold_access_sound with (u_eq:=Val.eq)
; [by apply Val.zb_eq|i|by mor|by apply aeqv_3|by mor].
eapply aeqv_2 with (Hteq:=Val.zb_eq)
; [i|mor;by apply Hi_mor|by apply mem_lookup_access_sound].
apply aeqv_1 with (Hteq:=Val.zb_eq); [by mor|by auto].
Qed.

Lemma va_arg_joins_access_sound :
  forall args, aeqv Val.zb_eq (RunAccess.va_arg_joins Strong cn args).
Proof.
i; unfold RunAccess.va_arg_joins.
apply list_fold_access_sound with (u_eq:=Logic.eq).
- by apply DLat.logic_zb_eq.
- i. apply aeqv_2 with (Hteq:=Val.zb_eq); [i|by mor|by auto].
  apply aeqv_2 with (Hteq:=Val.zb_eq); [i|by mor|by apply eval_access_sound].
  apply aeqv_2 with (Hteq:=Val.zb_eq); [i|by mor|by apply eval_access_sound].
  by apply aeqv_3.
- mor; subst; by apply eval_mor.
- by apply aeqv_3.
- by mor.
Qed.

Lemma process_dsts_access_sound :
  forall pos p l v, aeqm1 (RunAccess.process_dsts Strong cn pos p l v).
Proof.
i; unfold RunAccess.process_dsts.
apply list_fold_access_sound1; i
; [|apply ret_mem1; i; by apply Mem.eq_refl].
apply bind_mem1
; [|mor; destruct e as [[y1 y3] y2], y3, y2; by mor|by auto].
destruct e as [[y1 y3] y2], y3, y2.
- by apply mem_wupdate_access_sound.
- by apply mem_wupdate_access_sound.
- apply bind_mem1.
  + by apply mem_wupdate_access_sound.
  + by mor.
  + by apply mem_wupdate_access_sound.
- apply bind_mem1.
  + by apply mem_wupdate_access_sound.
  + by mor.
  + by apply mem_wupdate_access_sound.
Qed.

Lemma process_ret_access_sound :
  forall pos p t ret_opt l v,
    aeqm1 (RunAccess.process_ret Strong cn pos p t ret_opt l v).
Proof.
i; unfold RunAccess.process_ret.
destruct ret_opt; [|apply ret_mem1; i; by apply Mem.eq_refl].
apply bind_val1 with (Ht:=PowLoc.zb_eq)
; [| destruct (StringFun.ret t); [| |destruct alloc|]; by mor
   | by apply eval_lv_access_sound ].
destruct (StringFun.ret t); i.
- by apply mem_wupdate_access_sound.
- by apply mem_wupdate_access_sound.
- destruct alloc.
  + by apply mem_wupdate_access_sound.
  + apply bind_mem1; [|by mor|by apply mem_wupdate_access_sound].
    by apply mem_wupdate_access_sound.
- by apply mem_wupdate_access_sound.
Qed.

Lemma run_api_access_sound :
  forall ret_opt v pos p t,
    aeqm1 (RunAccess.run_api Strong cn ret_opt v pos p t).
Proof.
i; unfold RunAccess.run_api.
destruct (StringFun.get_dstsrc_list v (StringFun.args t) nil nil).
apply bind_val1 with (Ht:=Val.zb_eq)
; [ i
  | mor; [apply process_dsts_mor|apply process_ret_mor]
    ; by auto using DPos.eq_refl
         , (DLat.zb_equiv_refl (list_zb_eq StringFun.dst_zb_eq))
  | by apply va_src_val_joins_access_sound ].
apply bind_mem1
; [ i
  | mor; apply process_ret_mor
    ; by auto using DPos.eq_refl
         , (DLat.zb_equiv_refl (list_zb_eq StringFun.dst_zb_eq))
         , Val.eq_refl
  | by apply process_dsts_access_sound].
apply bind_mem1
; [ apply ret_mem1; i; by apply Mem.eq_refl
  | by mor
  | by apply process_ret_access_sound ].
Qed.

Lemma run_printf_pointer_access_sound :
  forall e args, aeqm1 (RunAccess.run_printf_pointer Strong cn e args).
Proof.
i; unfold RunAccess.run_printf_pointer.
apply bind_val1 with (Ht:=Val.zb_eq)
; [i|mor; by apply va_arg_joins_mor|by apply eval_access_sound].
apply bind_val1 with (Ht:=Val.zb_eq)
; [i| |by apply va_arg_joins_access_sound].
- by apply mem_wupdate_access_sound.
- intros v1 v2 Hv m1 m2 Hm.
  apply mem_wupdate_mor; by mor.
Qed.

Lemma run_printf_ppointer_access_sound :
  forall e args, aeqm1 (RunAccess.run_printf_ppointer Strong cn e args).
Proof.
i; unfold RunAccess.run_printf_ppointer.
apply bind_val1 with (Ht:=Val.zb_eq)
; [i|mor; by apply va_arg_joins_mor|by apply eval_access_sound].
apply bind_val1 with (Ht:=Val.zb_eq)
; [i| |by apply va_arg_joins_access_sound].
- apply bind_mem1
  ; [|mor; by apply mem_wupdate_access_sound|by apply mem_wupdate_access_sound].
  by apply mem_wupdate_access_sound.
- intros v1 v2 Hv m1 m2 Hm.
  eapply bind_mor; [apply mem_wupdate_mor; by mor|].
  apply mem_wupdate_mor; by mor.
Qed.

Lemma run_printf1_access_sound :
  aeqm1 RunAccess.run_printf1.
Proof.
unfold RunAccess.run_printf1.
apply ret_mem1; i; by apply Mem.eq_refl.
Qed.

Lemma run_printf2_access_sound :
  forall p args, aeqm1 (RunAccess.run_printf2 Strong cn p args).
Proof.
i; unfold RunAccess.run_printf2.
destruct args; [apply ret_mem1; i; by apply Mem.eq_refl|].
destruct args; [apply ret_mem1; i; by apply Mem.eq_refl|].
dest_if_dec; [|dest_if_dec].
- by apply run_printf_ppointer_access_sound.
- apply ret_mem1; i; by apply Mem.eq_refl.
- by apply run_printf_pointer_access_sound.
Qed.

Lemma run_printf3_access_sound :
  forall args, aeqm1 (RunAccess.run_printf3 Strong cn args).
Proof.
i; unfold RunAccess.run_printf3.
destruct args; [apply ret_mem1; i; by apply Mem.eq_refl|].
destruct args; [apply ret_mem1; i; by apply Mem.eq_refl|].
destruct args; [apply ret_mem1; i; by apply Mem.eq_refl|].
by apply run_printf_pointer_access_sound.
Qed.

Lemma run_printf_access_sound :
  forall p args, aeqm1 (RunAccess.run_printf Strong cn p args).
Proof.
i; unfold RunAccess.run_printf.
dest_if_dec; [by apply run_printf1_access_sound|].
dest_if_dec; [by apply run_printf2_access_sound|].
dest_if_dec; [by apply run_printf3_access_sound|].
apply ret_mem1; i; by apply Mem.eq_refl.
Qed.

Lemma run_undef_funcs_access_sound :
  forall ret_opt p v pos,
    aeqm1 (RunAccess.run_undef_funcs Strong cn ret_opt p v pos).
Proof.
unfold RunAccess.run_undef_funcs, RunAccess.run_api_with_name; i.
destruct (RunAccess.find_string_api_name p)
; [by apply run_api_access_sound|].
destruct ret_opt; [|apply ret_mem1; i; by apply Mem.eq_refl].
by apply set_ext_allocsite_access_sound.
Qed.

Lemma list_fold2_access_sound
      T U (ueq : U -> U -> Prop) (Hueq : DLat.zb_equiv ueq) :
  forall (l : list T) (vs : list U)
     f (Hf : forall t u, aeqm1 (f t u))
     (Hf_mor : forall t, Proper (ueq ==> Mem.eq ==> Acc.MAcc.eq Mem.zb_eq) (f t)),
 aeqm1 (RunAccess.SemMem.list_fold2_m f l vs).
Proof.
induction l; destruct vs.
- s; i. apply ret_mem1; i; by apply Mem.eq_refl.
- s; i. apply ret_mem1; i; by apply Mem.eq_refl.
- s; i. apply ret_mem1; i; by apply Mem.eq_refl.
- s; i. apply bind_mem1; [by apply IHl|mor|by apply Hf].
  apply list_fold2_m_mor with (teq:=eq) (ueq:=ueq)
  ; [ intros ? ? ?; subst; by apply Hf_mor
    | by apply eqlistA_eq_refl
    | by apply (DLat.zb_equiv_refl (list_zb_eq Hueq))
    | by auto ].
Qed.

Lemma bind_arg_access_sound :
  forall f x v, aeqm1 (RunAccess.SemMem.bind_arg Strong f x v).
Proof.
unfold RunAccess.SemMem.bind_arg; i. by apply mem_wupdate_access_sound.
Qed.

Lemma bind_args_access_sound :
  forall vs e, aeqm1 (RunAccess.SemMem.bind_args Strong g vs e).
Proof.
unfold RunAccess.SemMem.bind_args; i.
destruct (InterCfg.get_args (G.icfg g) e)
; [|apply ret_mem1; i; by apply Mem.eq_refl].
apply list_fold2_access_sound with (ueq:=Val.eq).
- by apply Val.zb_eq.
- by apply bind_arg_access_sound.
- by apply bind_arg_mor.
Qed.

Lemma weak_big_join_access_sound :
  forall f (Hf_access_sound : forall e, aeqm1 (f e))
     (Hf_mor :
        forall e, Proper (Mem.eq ==> Acc.MAcc.eq Mem.zb_eq) (f e))
     l,
    aeqm1 (fun m => RunAccess.BJProcMem.weak_big_join f l (Acc.MAcc.ret m)).
Proof. {
unfold RunAccess.BJProcMem.weak_big_join.
i; unfold aeqm1, Acc.MAcc.bind, Acc.MAcc.ret.
intros m m'.
remember (fun (s : TStr.string_t) (acc : Acc.MAcc.m DomMem.Mem.t) =>
            let (x, a1) := acc in
            let (y, a2) := f s x in
            (y, Acc.join a1 a2))
  as f'.
apply PowProc.fold2_4
with (P := fun t q =>
             forall (Hdis : Vali.disjoint m' (Acc.get_acc q)),
               Acc.MAcc.eq Mem.zb_eq t (mem_join q m')).
- subst; i. destruct t1 as [x1 a1], t2 as [x2 a2].
  remember (f e x1) as _m.
  destruct _m as [x1' a1'].
  remember (f e x2) as _m.
  destruct _m as [x2' a2'].
  remember (f e (Mem.join x2 m')) as _m.
  destruct _m as [x3 a3].
  destruct Ht as [Ht1 Ht2]
  ; [eapply disjoint_left; by apply Hdis|simpl in Ht1, Ht2].

  assert (Acc.MAcc.eq Mem.zb_eq
                      (x3, a3) (mem_join (x2', a2') m')) as eq1.
  { rewrite Heq_m1, Heq_m0. apply Hf_access_sound.
    rewrite <- Heq_m0. eapply disjoint_right; by apply Hdis. }
  destruct eq1 as [eq11 eq12]; simpl in eq11, eq12.

  assert (Acc.MAcc.eq Mem.zb_eq (x1', a1') (x3, a3)) as eq2.
  { rewrite Heq_m, Heq_m1. apply Hf_mor. by auto. }
  destruct eq2 as [eq21 eq22]; simpl in eq21, eq22.

  split; s.
  + by apply Mem.eq_trans with x3.
  + apply Acc.join_eq; [by auto|by apply Acc.eq_trans with a3].
- split; s; [by apply Mem.eq_refl|by apply Acc.eq_refl].
} Qed.

Lemma update_rets_access_sound :
  forall v ret_opt,
    aeqm1 (RunAccess.update_rets Strong cn (DomAbs.powProc_of_val v) ret_opt).
Proof.
unfold RunAccess.update_rets; i.
apply bind_val1 with (Ht:=PowLoc.zb_eq).
- i. by apply mem_wupdate_access_sound.
- mor. apply SMProcLoc_map_mor.
  + intros ? ? ?; subst. by apply Loc.eq_refl.
  + by apply PowProc.eq_refl.
- destruct ret_opt.
  + by apply eval_lv_access_sound.
  + by apply aeqv_3.
Qed.

Lemma run_access_sound : aeqm1 (run_access Strong g cn cmd).
Proof.
unfold run_access, RunAccess.run. destruct cmd.
- destruct lv, lh, o
  ; try (apply bind_val1 with (Ht:=PowLoc.zb_eq)
         ; [|by mor|by apply eval_lv_access_sound]
         ; i; apply bind_val1 with (Ht:=Val.zb_eq)
         ; [ by apply mem_wupdate_access_sound
           | by mor
           | by apply eval_access_sound ]).
- by apply set_ext_allocsite_access_sound.
- apply bind_val1 with (Ht:=PowLoc.zb_eq).
  + i; by apply mem_wupdate_access_sound.
  + intros k1 k2 Hk m1 m2 Hm.
    apply mem_wupdate_mor; [by auto| |by auto].
    by apply eval_alloc_mor.
  + by apply eval_lv_access_sound.
- apply bind_val1 with (Ht:=PowLoc.zb_eq).
  + i; apply bind_mem1.
    * by apply mem_wupdate_access_sound.
    * apply mem_wupdate_mor; [by apply PowLoc.eq_refl|by apply Val.eq_refl].
    * by apply mem_wupdate_access_sound.
  + intros l1 l2 Hl m1 m2 Hm. apply bind_mor with (Hteq:=Mem.zb_eq).
    * apply mem_wupdate_mor
      ; [by apply PowLoc.eq_refl|by apply Val.eq_refl|by auto].
    * intros m1' m2' Hm'.
      apply mem_wupdate_mor; [by auto|by apply Val.eq_refl|by auto].
  + by apply eval_lv_access_sound.
- apply bind_val1 with (Ht:=PowLoc.zb_eq).
  + i; by apply mem_wupdate_access_sound.
  + intros l1 l2 Hl m1 m2 Hm.
    apply mem_wupdate_mor; [by auto|by apply Val.eq_refl|by auto].
  + by apply eval_lv_access_sound.
- apply ret_mem1. i; by apply Mem.eq_refl.
- apply bind_val1 with (Ht:=list_val_zb_eq).
  + destruct (G.is_undef_e f g); [destruct (is_printf f)|].
    * i. by apply run_printf_access_sound.
    * i. by apply run_undef_funcs_access_sound.
    * i. apply bind_val1 with (Ht:=Val.zb_eq).
      { i; apply bind_mem1.
        { apply weak_big_join_access_sound
          ; [ i; by apply bind_args_access_sound
            | i; apply bind_args_mor
              ; [by apply (DLat.zb_equiv_refl list_val_zb_eq)|by auto] ]. }
        { intros ? ? ?; apply weak_big_join_mor
          ; [ by apply bind_args_mor, (DLat.zb_equiv_refl list_val_zb_eq)
            | by apply PowProc.eq_refl
            | by apply ret_mor ]. }
        { by apply update_rets_access_sound. } }
      { intros v1 v2 Hv m1 m2 Hm.
        apply bind_mor with (Hteq:=Mem.zb_eq).
        { apply update_rets_mor
          ; [by apply pow_proc_of_val_mor|by auto|by auto]. }
        { intros ? ? ?; apply weak_big_join_mor
          ; [ by apply bind_args_mor, (DLat.zb_equiv_refl list_val_zb_eq)
            | by apply pow_proc_of_val_mor
            | by apply ret_mor ]. } }
      { by apply eval_access_sound. }
  + intros v1 v2 Hv m1 m2 Hm.
    destruct (G.is_undef_e f g); [destruct (is_printf f)|].
    * by apply run_printf_mor.
    * apply run_undef_funcs_mor; [by auto|apply DPos.eq_refl|by auto].
    * apply bind_mor with (Hteq:=Val.zb_eq).
      { by apply eval_mor. }
      { intros v1' v2' Hv'. eapply bind_mor with (Hteq:=Mem.zb_eq).
        { apply update_rets_mor
          ; [by apply pow_proc_of_val_mor|by auto|by auto]. }
        { intros m1' m2' Hm'.
          apply weak_big_join_mor
          ; [ by apply bind_args_mor
            | by apply pow_proc_of_val_mor
            | by apply ret_mor ]. } }
  + by apply eval_list_access_sound.
- destruct ret_opt.
  + apply bind_val1 with (Ht:=Val.zb_eq).
    { i. apply bind_val1 with (Ht:=Val.zb_eq).
      { i. by apply mem_wupdate_access_sound. }
      { intros v1 v2 Hv m1 m2 Hm.
        apply mem_wupdate_mor
        ; [by apply SemEval.deref_of_val_mor|by apply Val.eq_refl|by auto]. }
      { by apply mem_lookup_access_sound. } }
    { intros v1 v2 Hv m1 m2 Hm. apply bind_mor with (Hteq:= Val.zb_eq).
      { by apply mem_lookup_mor. }
      { intros v1' v2' Hv'; apply mem_wupdate_mor
        ; [by apply SemEval.deref_of_val_mor|by auto|by auto]. } }
    { by apply eval_access_sound. }
  + apply ret_mem1; i; by apply Mem.eq_refl.
- apply ret_mem1. i; by apply Mem.eq_refl.
- apply ret_mem1. i; by apply Mem.eq_refl.
Qed.

End Env.
