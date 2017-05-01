(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
Lemma cor_mem_add :
  forall g l l' v v' m m'
     (Happx : approx_one_loc g l' = true)
     (Hl : Loc.eq (Loc_g l) l') (Hv : Val_g v v')
     (Hm : Mem_g' m m')
     (Hwf : SemCon.wf_non_rec_mem g (DomCon.M.add l v m)),
    Mem_g' (DomCon.M.add l v m) (Mem.add l' v' m').
Proof.
i. unfold Mem_g'. i.
rewrite DomCon.M.P.F.add_o in Hcon.
destruct (DomCon.Loc.eq_dec l l0).
{
inversion_clear Hcon. eapply val_g_mor; [reflexivity| |by apply Hv].
apply Val.eq_sym, Mem.add_same.
eapply Loc.eq_trans; [|by apply Hl].
apply loc_g_mor; by apply DomCon.Loc.eq_sym.
}
{
rewrite Mem.add_diff.
- by apply Hm.
- intro; elim n.
  eapply prop_approx_one_loc
  ; [by apply Happx|by apply Hwf|by apply Hl| |by apply FH|].
  + apply DomCon.M.P.F.mem_in_iff.
    apply DomCon.M.P.F.add_eq_b.
    split; [by apply DomCon.VarRegion.eq_refl|by apply DomCon.Fields.eq_refl].
  + apply DomCon.M.P.F.add_neq_in_iff; [by apply n|].
    apply DomCon.M.P.F.in_find_iff. congruence.
}
Qed.

Lemma cor_mem_add' :
  forall g l l' v v' m m'
     (Happx : approx_one_loc g l' = true)
     (Hl : Loc.eq (Loc_g l) l') (Hv : Val_g v v')
     (Hm : Mem_g' m m')
     (Hwf : SemCon.wf_non_rec_mem g m)
     (Hv : DomCon.M.MapsTo l v m),
    Mem_g' m (Mem.add l' v' m').
Proof.
i. unfold Mem_g'. i.
destruct (DomCon.Loc.eq_dec l l0).
{ assert (Some v = Some v0) as Hv_eq; [|inversion Hv_eq; subst].
  { apply DomCon.M.find_1 in Hv0.
    rewrite <- Hv0, Hcon; by apply DomCon.M.P.F.find_o, e. }
  eapply val_g_mor; [reflexivity| |by apply Hv].
  apply Val.eq_sym, Mem.add_same.
  eapply Loc.eq_trans; [|by apply Hl].
  apply loc_g_mor; by apply DomCon.Loc.eq_sym. }
{ rewrite Mem.add_diff.
  - by apply Hm.
  - intro; elim n.
    eapply prop_approx_one_loc.
    + by apply Happx.
    + by apply Hwf.
    + by auto.
    + eapply DomCon.M.mapsto_in; by apply Hv0.
    + by auto.
    + eapply DomCon.M.mapsto_in, DomCon.M.P.F.find_mapsto_iff
      ; symmetry; by apply Hcon. }
Qed.

Lemma cor_mem_weak_add :
  forall l l' v v' m m' (Hl : Loc.eq (Loc_g l) l') (Hv : Val_g v v')
         (Hm : Mem_g' m m'),
    Mem_g' (DomCon.M.add l v m) (Mem.weak_add l' v' m').
Proof.
i. unfold Mem_g'. i.
rewrite DomCon.M.P.F.add_o in Hcon.
destruct (DomCon.Loc.eq_dec l l0).
{
inversion_clear Hcon. eapply val_g_mor; [reflexivity| |].
- apply Mem.weak_add_prop.
  eapply Loc.eq_trans; [|by apply Hl].
  apply loc_g_mor; by apply DomCon.Loc.eq_sym.
- eapply val_g_monotone; [by apply Hv|by apply Val.join_left].
}
{
destruct (Loc.eq_dec (Loc_g l0) l').
- eapply val_g_mor; [reflexivity|by apply Mem.weak_add_prop|].
  eapply val_g_monotone; [|by apply Val.join_right].
  eapply val_g_mor; [reflexivity| |].
  + apply Mem.find_mor; [by apply e|by apply Mem.eq_refl].
  + by apply Hm.
- rewrite Mem.weak_add_diff; [|by auto].
  by eapply Hm.
}
Qed.

Lemma mem_weak_add_ext :
  forall e v x, Mem.le x (Mem.weak_add e v x).
Proof.
i. intro l. destruct (Loc.eq_dec l e).
- eapply Val.le_trans; [|apply Val.le_refl; by apply Mem.weak_add_prop].
  eapply Val.le_trans; [|by apply Val.join_right].
  apply Mem.find_mor'; [by auto|apply Mem.le_refl; by apply Mem.eq_refl].
- rewrite Mem.weak_add_diff; [|by auto].
  apply Val.le_refl; by apply Val.eq_refl.
Qed.

Lemma stack_g_add_loc :
  forall d l v m (Hstk : Stack_g d m),
    Stack_g d (Mem.add (Loc_g l) v m).
Proof.
i. intro; i. eapply val_g_monotone.
- eapply Hstk; by apply Hstack1.
- apply Val.le_refl.
  rewrite Mem.add_diff; [by apply Val.eq_refl|].
  unfold SProc_g, Loc_g; destruct l. by inversion 1.
Qed.

Lemma stack_g_weak_add :
  forall d l v m (Hstk : Stack_g d m),
    Stack_g d (Mem.weak_add l v m).
Proof.
i. intro; i. eapply val_g_monotone.
- eapply Hstk; by apply Hstack1.
- by apply mem_weak_add_ext.
Qed.

Module BJoin := BigJoin Loc PowLoc Mem.

Lemma cor_update :
  forall g cid callee m d l l' v v' abs_m abs_m'
         (Hl : Loc.eq (Loc_g l) l') (Hv : Val_g v v')
         (Hgam : Mem_g (cid, callee, m, d) abs_m)
         (Habs : abs_m' = mem_update Strong g l' v' abs_m)
         m' (Hm' : m' = DomCon.M.add l v m) (Hwf : SemCon.wf_non_rec_mem g m'),
    Mem_g (cid, callee, m', d) abs_m'.
Proof. {
unfold mem_update. i.
remember (can_strong_update Strong g l') as b; destruct b.
- eapply mem_g_mor; [reflexivity| |].
  + subst.
    apply Mem.add_mor
    ; [by apply Loc.eq_sym, Hl|by apply Val.eq_refl|by apply Mem.eq_refl].
  + split.
    * subst; eapply cor_mem_add
      ; [ eapply can_strong_update_1; rewrite Heqb
          ; by apply can_strong_update_mor
        | by apply Loc.eq_refl
        | by apply Hv
        | by apply Hgam
        | by apply Hwf ].
    * destruct Hgam. by apply stack_g_add_loc.
- rewrite Habs. eapply mem_g_monotone.
  + s; split.
    * rewrite Hm'.
      apply cor_mem_weak_add; [by apply Loc.eq_refl|by apply Hv|by apply Hgam].
    * apply stack_g_weak_add. by apply Hgam.
  + apply Mem.weak_add_mor'
    ; [ by auto
      | by apply Val.le_refl, Val.eq_refl
      | by apply Mem.le_refl, Mem.eq_refl ].
} Qed.

Lemma cor_update' :
  forall g cid callee m d l l' v v' abs_m abs_m'
         (Hl : Loc.eq (Loc_g l) l') (Hv : Val_g v v')
         (Hgam : Mem_g (cid, callee, m, d) abs_m)
         (Habs : abs_m' = mem_update Strong g l' v' abs_m)
         (Hm : Some v = DomCon.M.find l m) (Hwf : SemCon.wf_non_rec_mem g m),
    Mem_g (cid, callee, m, d) abs_m'.
Proof. {
unfold mem_update. i.
remember (can_strong_update Strong g l') as b; destruct b.
- eapply mem_g_mor; [reflexivity| |].
  + subst.
    apply Mem.add_mor
    ; [by apply Loc.eq_sym, Hl|by apply Val.eq_refl|by apply Mem.eq_refl].
  + split.
    * subst; eapply cor_mem_add'
      ; [ eapply can_strong_update_1; rewrite Heqb
          ; by apply can_strong_update_mor
        | by apply Loc.eq_refl
        | by apply Hv
        | by apply Hgam
        | by apply Hwf
        | by apply DomCon.M.P.F.find_mapsto_iff ].
    * destruct Hgam. by apply stack_g_add_loc.
- rewrite Habs. eapply mem_g_monotone with abs_m.
  + by apply Hgam.
  + unfold weak_add, DomMem.IdMem.mem_weak_add.
    by apply mem_weak_add_ext.
} Qed.

Lemma mem_update_diff :
  forall g m abs_m abs_l v (Hm : Mem_g' m abs_m)
     (Hl : forall l, ~ Loc.eq (Loc_g l) abs_l),
    Mem_g' m (mem_update Strong g abs_l v abs_m).
Proof.
i. unfold mem_update, MId.bind, MId.ret, add, weak_add, IdMem.mem_add
   , IdMem.mem_weak_add; s.
match goal with [|- context[if ?c then _ else _]] => destruct c end.
- intro; i. rewrite DomMem.Mem.add_diff; [by apply Hm|by apply Hl].
- intro; i. rewrite DomMem.Mem.weak_add_diff; [by apply Hm|by apply Hl].
Qed.

Lemma mem_wupdate_diff :
  forall m abs_m abs_l v (Hm : Mem_g' m abs_m)
     (Hl : forall l, PowLoc.mem (Loc_g l) abs_l = false),
    Mem_g' m (mem_wupdate Strong abs_l v abs_m).
Proof.
i. unfold mem_wupdate, MId.bind, MId.ret, add, weak_add, IdMem.mem_add
   , IdMem.mem_weak_add; s.
apply PowLoc.fold_3; [|by auto].
i. intro; i. rewrite DomMem.Mem.weak_add_diff; [by apply Hx|].
intro. assert (PowLoc.mem (Loc_g l) abs_l = true); [|congruence].
erewrite PowLoc.mem_mor; [by apply He|by apply FH|by apply PowLoc.eq_refl].
Qed.

Section Fold_mem_add.

Variable k : PowLoc.t.
Variable v : Val.t.
Variable m : Mem.t.
Let mem_add lv m := Mem.add lv v m.

Lemma fold_mem_add1 :
  forall l (Hl_k : PowLoc.mem l k = true),
    Val.eq (Mem.find l (PowLoc.fold mem_add k m)) v.
Proof.
i. apply PowLoc.fold_1 with (e:=l).
- by auto.
- i. by apply Mem.add_same, Loc.eq_refl.
- i. destruct (Loc.eq_dec l e').
  + apply  Mem.add_same; by auto.
  + unfold mem_add. rewrite Mem.add_diff; by auto.
- i. eapply Val.eq_trans; [|by apply He0].
  eapply Mem.find_mor; [by apply Loc.eq_refl|].
  unfold mem_add; apply Mem.add_mor
  ; [|by apply Val.eq_refl|by apply Mem.eq_refl].
  by apply Loc.eq_sym.
Qed.

Lemma fold_mem_add3 :
  forall l (Hl_k : PowLoc.mem l k = false),
    Mem.find l (PowLoc.fold mem_add k m) = Mem.find l m.
Proof.
i; apply PowLoc.fold_3.
- i; unfold mem_add; rewrite Mem.add_diff; [by auto|].
  i; rewrite PowLoc.mem_mor in Hl_k; [|by apply FH|by apply PowLoc.eq_refl].
  congruence.
- by auto.
Qed.

Let mem_weak_add lv m := Mem.weak_add lv v m.

Lemma fold_mem_weak_add1 :
  forall l (Hl_k : PowLoc.mem l k = true),
    Val.eq (Mem.find l (PowLoc.fold mem_weak_add k m))
           (Val.join v (Mem.find l m)).
Proof.
i.
apply PowLoc.fold_2_strong
with (e:=l) (P:=fun x => Val.eq (Mem.find l x) (Mem.find l m)).
- by apply Hl_k.
- i; eapply Val.eq_trans
  ; [apply Val.eq_sym, Mem.weak_add_prop; by apply Loc.eq_refl|].
  apply Val.join_eq; [by apply Val.eq_refl|by auto].
- i; unfold mem_weak_add; by rewrite Mem.weak_add_diff.
- i; unfold mem_weak_add; by rewrite Mem.weak_add_diff.
- i; eapply Val.eq_trans; [|by apply He0].
  apply Mem.find_mor; [by apply Loc.eq_refl|].
  apply Mem.weak_add_mor; [|by apply Val.eq_refl|by apply Mem.eq_refl].
  by apply Loc.eq_sym.
- by apply Val.eq_refl.
Qed.

Lemma fold_mem_weak_add2 :
  forall l (Hl_k : PowLoc.mem l k = false),
    Mem.find l (PowLoc.fold mem_weak_add k m) = Mem.find l m.
Proof.
i; apply PowLoc.fold_3.
- i; unfold mem_weak_add; rewrite Mem.weak_add_diff; [by auto|].
  i; rewrite PowLoc.mem_mor in Hl_k; [|by apply FH|by apply PowLoc.eq_refl].
  congruence.
- by auto.
Qed.

End Fold_mem_add.

Lemma mem_add_double :
  forall l k v m,
    let mem_add lv m := Mem.add lv v m in
    Val.eq (Mem.find l (mem_add k m)) (Mem.find l (mem_add k (mem_add k m))).
Proof.
i. unfold mem_add. destruct (Loc.eq_dec l k).
- apply Val.eq_trans with v
  ; [by apply Mem.add_same|by apply Val.eq_sym, Mem.add_same].
- do 3 (rewrite Mem.add_diff; [|by auto]).
  by apply Val.eq_refl.
Qed.

Lemma mem_weak_add_double :
  forall l k v m,
    let mem_weak_add lv m := Mem.weak_add lv v m in
    Val.eq (Mem.find l (mem_weak_add k m))
           (Mem.find l (mem_weak_add k (mem_weak_add k m))).
Proof.
i. unfold mem_weak_add. destruct (Loc.eq_dec l k).
- eapply Val.eq_trans; [by apply Val.eq_sym, Mem.weak_add_prop|].
  eapply Val.eq_trans; [|by apply Mem.weak_add_prop].
  eapply Val.eq_trans
  ; [|apply Val.join_eq; [by apply Val.eq_refl|by apply Mem.weak_add_prop]].
  eapply Val.eq_trans; [|by apply Val.eq_sym, Val.join_assoc].
  apply Val.join_eq; [by apply Val.join_idem|by apply Val.eq_refl].
- do 3 (rewrite Mem.weak_add_diff; [|by auto]).
  by apply Val.eq_refl.
Qed.

Lemma mem_weak_add_double' :
  forall l k v m,
    let mem_weak_add lv m := Mem.weak_add lv v m in
    Val.eq
      (Mem.find l (PowLoc.fold mem_weak_add k m))
      (Mem.find l (PowLoc.fold mem_weak_add k
                               (PowLoc.fold mem_weak_add k m))).
Proof.
i. remember (PowLoc.mem l k) as b.
destruct b
; [| unfold mem_weak_add; apply Val.eq_sym
     ; rewrite fold_mem_weak_add2; [by apply Val.eq_refl|by auto] ].
eapply Val.eq_trans; [by apply fold_mem_weak_add1|].
apply Val.eq_sym; eapply Val.eq_trans; [by apply fold_mem_weak_add1|].
eapply Val.eq_trans; [apply Val.eq_sym; apply Val.join_le_idem|].
+ eapply Val.le_trans
  ; [ by apply Val.join_left
    | by apply Val.le_refl, Val.eq_sym, fold_mem_weak_add1 ].
+ by apply fold_mem_weak_add1.
Qed.

Lemma mem_update_double :
  forall g k v m,
    Mem.eq (mem_update Strong g k v m)
           (mem_update Strong g k v (mem_update Strong g k v m)).
Proof.
i; intro l. unfold mem_update.
destruct (can_strong_update Strong g k).
- unfold MId.bind, MId.ret, add; s. unfold DomMem.IdMem.mem_add, MId.m.
  by apply mem_add_double.
- unfold MId.bind, MId.ret, weak_add; s.
  unfold DomMem.IdMem.mem_weak_add, MId.m.
  by apply mem_weak_add_double.
Qed.

Lemma mem_wupdate_double :
  forall k v m,
    Mem.eq (mem_wupdate Strong k v m)
           (mem_wupdate Strong k v (mem_wupdate Strong k v m)).
Proof.
i; intro l. remember (PowLoc.mem l k) as b.
unfold mem_wupdate, MId.bind, MId.ret.
by apply mem_weak_add_double'.
Qed.

Lemma cor_update2 :
  forall cid d callee m m' l_opt l'
     (Hm : Stack_g d m)
     (Hv : Loc_opt_g l_opt l')
     (Hm'1 : Mem.le m m')
     (Hm'2 :
        Val.le (val_of_pow_loc l') (Mem.find (loc_of_proc callee) m')),
    Stack_g ((callee, l_opt, cid) :: d) m'.
Proof.
unfold Stack_g. i. inversion Hstack1.
- inversion H; subst. clear H.
  eapply val_g_monotone; [|by apply Hm'2].
  inversion Hv; subst. by constructor.
- eapply val_g_monotone; [eapply Hm; by apply H|by apply Hm'1].
Qed.

Lemma cor_wupdate :
  forall cid callee m d l l' v v' abs_m abs_m'
         (Hl : PowLoc.mem (Loc_g l) l' = true) (Hv : Val_g v v')
         (Hgam : Mem_g (cid, callee, m, d) abs_m)
         (Habs : abs_m' = mem_wupdate Strong l' v' abs_m)
         m' (Hm' : m' = DomCon.M.add l v m),
    Mem_g (cid, callee, m', d) abs_m'.
Proof. {
i; rewrite Habs. unfold mem_wupdate.
unfold MId.bind, weak_add, IdMem.mem_weak_add. s.
split.
{
intro; i. destruct (DomCon.Loc.eq_dec l0 l); subst m'.
- rewrite DomCon.M.P.F.add_eq_o in Hcon; [|by apply DomCon.Loc.eq_sym].
  inversion_clear Hcon.
  apply PowLoc.fold_1 with (Loc_g l).
  + by auto.
  + i. eapply val_g_monotone; [by apply Hv|].
    eapply Val.le_trans
    ; [ by apply Val.join_left
      | by apply Val.le_refl, Mem.weak_add_prop, loc_g_mor].
  + intros ? ? Hvalg. eapply val_g_monotone; [by apply Hvalg|].
    destruct (Loc.eq_dec (Loc_g l0) e').
    * eapply Val.le_trans; [|by eapply Val.le_refl, Mem.weak_add_prop].
      eapply Val.le_trans; [|by apply Val.join_right].
      eapply Val.le_refl, Mem.find_mor; [by auto|by apply Mem.eq_refl].
    * rewrite Mem.weak_add_diff; [|by auto].
      by apply Val.le_refl, Val.eq_refl.
  + i. eapply val_g_mor; [reflexivity| |by apply He0].
    apply Mem.find_mor; [by apply Loc.eq_refl|].
    unfold MId.bind, weak_add, IdMem.mem_weak_add. s.
    apply Mem.weak_add_mor; [by auto|by apply Val.eq_refl|by apply Mem.eq_refl].
- rewrite DomCon.M.P.F.add_neq_o in Hcon
  ; [|intro; elim n; by apply DomCon.Loc.eq_sym].
  apply PowLoc.fold_3.
  + i. destruct (Loc.eq_dec (Loc_g l0) e).
    * eapply val_g_monotone; [|by apply Val.le_refl, Mem.weak_add_prop].
      eapply val_g_monotone; [by apply Hx|].
      eapply Val.le_trans; [|by apply Val.join_right].
      apply Val.le_refl, Mem.find_mor; [by auto|by apply Mem.eq_refl].
    * rewrite Mem.weak_add_diff; by auto.
  + by apply Hgam.
}
{
intro; i. apply PowLoc.fold_3.
- i. destruct (Loc.eq_dec (SProc_g pid) e).
  + eapply val_g_monotone; [|by apply Val.le_refl, Mem.weak_add_prop].
    eapply val_g_monotone; [by apply Hx|].
    eapply Val.le_trans; [|by apply Val.join_right].
    apply Val.le_refl, Mem.find_mor; [by auto|by apply Mem.eq_refl].
  + rewrite Mem.weak_add_diff; by auto.
- destruct Hgam as [_ Hgam].
  eapply Hgam; by apply Hstack1.
}
} Qed.

Lemma cor_mem_lookup :
  forall l ls v cid callee m d abs_m
         (Hl : PowLoc.mem (Loc_g l) ls)
         (Hm : DomCon.M.MapsTo l v m)
         (Habs_m : Mem_g (cid, callee, m, d) abs_m),
    Val_g v (mem_lookup ls abs_m).
Proof.
i. unfold mem_lookup, MId.bind, MId.ret. eapply PowLoc.fold_1.
- by apply Hl.
- i. eapply val_g_monotone; [|by apply Val.join_right].
  apply Habs_m. symmetry. by apply DomCon.M.P.F.find_mapsto_iff.
- i. eapply val_g_monotone; [by apply Hx|by apply Val.join_left].
- i. eapply val_g_monotone; [by apply He0|].
  apply Val.le_refl. apply Val.join_eq; [by apply Val.eq_refl|].
  unfold IdMem.mem_find. apply Mem.find_mor; [by auto|by apply Mem.eq_refl].
Qed.

Lemma mem_g_filter1 :
  forall cid cid' opt_ret opt_ret' m f d abs_m
     (Hf : Proper (DomCon.Loc.eq ==> eq) f)
     (Hmem_g : Mem_g (cid, opt_ret, m, d) abs_m),
    Mem_g (cid', opt_ret', DomCon.M.filter f m, d) abs_m.
Proof.
i. constructor.
- intros k v Hfind. apply Hmem_g.
  symmetry in Hfind; apply DomCon.M.filter_3 in Hfind; by auto.
- by apply Hmem_g.
Qed.

Lemma is_not_local_proper :
  forall cn,
    Proper (Loc.eq ==> eq) (fun l => negb (is_local_of (InterNode.get_pid cn) l)).
Proof. intros cn l1 l2 Hl. f_equal. by apply is_local_of_mor. Qed.

Lemma cor_remove_local_variables :
  forall opt_ret opt_ret' cid cid' m m' d abs_m
     (Hmem_g : Mem_g (cid, opt_ret, m, d) abs_m)
     (Hm' : SemCon.remove_locals cid m = m'),
    Mem_g (cid', opt_ret', m', d) abs_m.
Proof. {
i; subst.
unfold SemCon.remove_locals, MId.ret.
eapply mem_g_filter1; [|by apply Hmem_g].
intros [y1 ?] [y2 ?] Hl. inversion Hl; subst.
simpl in H, H0. inversion H; [|by auto].
inversion Heq; [by auto|].
destruct x'0 as [[cidx ?] ?], y'0 as [[cidy ?] ?].
simpl in Heq0; destruct Heq0 as [[Heq1 Heq2] Heq3]; subst; reflexivity.
} Qed.

Lemma weaken_mem_g :
  forall cid m d callee_opt callee retl cid' abs_m
         (Hmem_g : Mem_g (cid, callee_opt, m, (callee, retl, cid') :: d) abs_m),
    Mem_g (cid, callee_opt, m, d) abs_m.
Proof.
destruct 1 as [Hm Hs]. split; [by auto|].
unfold Stack_g. i. eapply Hs.
s. right. apply Hstack1.
Qed.

Module PowLocFold := BigJoin Loc PowLoc Val.

Lemma mem_find_mem_lookup :
  forall l ls m (Hl : PowLoc.mem l ls = true),
    Val.le (Mem.find l m) (mem_lookup ls m).
Proof.
i. unfold mem_lookup.
unfold MId.bind, MId.ret, DomMem.IdMem.mem_find.
eapply Val.le_trans; [|eapply PowLocFold.weak_big_join_1'].
- by apply Val.join_right.
- by auto.
- intros l1 l2 Hloc v1 v2 Hv.
  apply Val.join_lub.
  + eapply Val.le_trans; [by apply Hv|].
    by apply Val.join_left.
  + eapply Val.le_trans; [|by apply Val.join_right].
    eapply Mem.find_mor'; [by auto|by apply Mem.le_refl, Mem.eq_refl].
- i. by apply Val.join_left.
Qed.

Lemma Mem_weak_add_ext :
  forall e v m, Mem.le m (Mem.weak_add e v m).
Proof.
i. intro. destruct (Loc.eq_dec k e).
- eapply Val.le_trans; [|apply Val.le_refl, Mem.weak_add_prop].
  + eapply Val.le_trans; [|apply Val.join_right].
    apply Mem.find_mor'; [by auto|by apply Mem.le_refl, Mem.eq_refl].
  + by auto.
- rewrite Mem.weak_add_diff; [|by auto].
  by apply Val.le_refl, Val.eq_refl.
Qed.

Lemma mem_wupdate_monotone :
  forall l v, Proper (Mem.le ==> Mem.le) (mem_wupdate Strong l v).
Proof.
i. unfold mem_wupdate, MId.bind, MId.ret. intros m1 m2 Hm.
eapply PowLoc.fold2_1.
- by apply Mem.le_trans.
- i. by apply Mem_weak_add_ext.
- i. unfold weak_add, DomMem.IdMem.mem_weak_add. s.
  apply Mem.weak_add_mor'
  ; [by apply Loc.eq_refl|by apply Val.le_refl, Val.eq_refl|by auto].
- by apply Mem.le_refl, Mem.eq_refl.
- by auto.
Qed.

Lemma mem_wupdate_ext :
  forall l v m, Mem.le m (mem_wupdate Strong l v m).
Proof.
i. unfold mem_wupdate, MId.bind, MId.ret.
apply PowLoc.fold_3; [|by apply Mem.le_refl, Mem.eq_refl].
i. unfold weak_add, DomMem.IdMem.mem_weak_add. s.
apply Mem.le_trans with x; [by auto|by apply Mem_weak_add_ext].
Qed.
