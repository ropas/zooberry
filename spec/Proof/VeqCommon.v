(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
Definition veq T (x : MId.m T) (y : Acc.MAcc.m T) : Prop := x = Acc.get_v y.

Lemma bind_veq :
  forall T (x1 : MId.m T) (x2 : Acc.MAcc.m T)
     U (f1 : T -> MId.m U) (f2 : T -> Acc.MAcc.m U)
     (Hx : veq x1 x2) (Hf : forall x, veq (f1 x) (f2 x)),
    veq (MId.bind x1 f1) (Acc.MAcc.bind x2 f2).
Proof.
i; unfold MId.bind, Acc.MAcc.bind.
rewrite Hf, Hx. destruct x2; s. destruct (f2 t); s. by auto.
Qed.

Ltac dest_veq :=
match goal with
| |- veq (MId.bind ?x1 ?f1) (Acc.MAcc.bind ?x2 ?f2) =>
  let Hx := fresh "Hx" in
  let Hf := fresh "Hf" in
  assert (veq x1 x2) as Hx
  ; [| assert (forall x, veq (f1 x) (f2 x)) as Hf
       ; [|eapply bind_veq; [by apply Hx|by apply Hf]] ]
| |- veq (MId.ret ?x1) (Acc.MAcc.ret ?y1) => reflexivity
end.

Definition mem_join (x : Acc.MAcc.m Mem.t) (y : Mem.t) :=
  (Mem.join (Acc.get_v x) y, Acc.get_acc x).

Lemma bind_mor
      T (teq : T -> T -> Prop) (Hteq : DLat.zb_equiv teq)
      U (ueq : U -> U -> Prop) (Hueq : DLat.zb_equiv ueq) :
  Proper (Acc.MAcc.eq Hteq
          ==> (teq ==> Acc.MAcc.eq Hueq)
          ==> Acc.MAcc.eq Hueq)
         (Acc.MAcc.bind (A:=T) (B:=U)).
Proof.
intros t1 t2 Ht u1 u2 Hu. unfold Acc.MAcc.bind, Acc.MAcc.eq.
destruct t1 as [t1 a1], t2 as [t2 a2].
remember (u1 t1) as v1; destruct v1 as [v1 a1'].
remember (u2 t2) as v2; destruct v2 as [v2 a2'].
assert (Acc.MAcc.eq Hueq (v1, a1') (v2, a2')) as Heqv.
{ rewrite Heqv1, Heqv2. by apply Hu, Ht. }
split; [by apply Heqv|apply Acc.join_eq; [by apply Ht|by apply Heqv]].
Qed.

Lemma ret_mor T (teq : T -> T -> Prop) (Hteq : DLat.zb_equiv teq) :
  Proper (teq ==> Acc.MAcc.eq Hteq) (Acc.MAcc.ret (A:=T)).
Proof.
intros x1 x2 Hx. unfold Acc.MAcc.ret, Acc.MAcc.eq.
split; [by auto|by apply Acc.eq_refl].
Qed.

Lemma if_dec_mor
      P (P_dec : sumbool P (~ P)) Q (Q_dec : sumbool Q (~ Q))
      (HPQ1 : P -> Q) (HPQ2 : Q -> P)
      T (teq : T -> T -> Prop) (Hteq : DLat.zb_equiv teq) :
  forall e1 e1' (He1 : Acc.MAcc.eq Hteq e1 e1')
     e2 e2' (He2 : Acc.MAcc.eq Hteq e2 e2'),
    Acc.MAcc.eq Hteq (if P_dec then e1 else e2) (if Q_dec then e1' else e2').
Proof.
i. destruct P_dec; destruct Q_dec.
- by auto.
- elim f. by auto.
- elim f. by auto.
- by auto.
Qed.

Lemma if_dec_not_mor
      P (P_dec : sumbool P (~ P)) Q (Q_dec : sumbool Q (~ Q))
      (HPQ1 : P -> Q) (HPQ2 : Q -> P)
      T (teq : T -> T -> Prop) (Hteq : DLat.zb_equiv teq) :
  forall e1 e1' (He1 : Acc.MAcc.eq Hteq e1 e1')
     e2 e2' (He2 : Acc.MAcc.eq Hteq e2 e2'),
    Acc.MAcc.eq Hteq
                (if Sumbool.sumbool_not P (~ P) P_dec then e1 else e2)
                (if Sumbool.sumbool_not Q (~ Q) Q_dec then e1' else e2').
Proof.
i. unfold Sumbool.sumbool_not.
destruct P_dec; destruct Q_dec.
- by auto.
- elim f. by auto.
- elim f. by auto.
- by auto.
Qed.

Lemma eqlistA_eq_refl T : forall (l : list T), SetoidList.eqlistA eq l l.
Proof. induction l; [by auto|constructor; by auto]. Qed.

Definition list_zb_eq T (teq : T -> T -> Prop) (Hteq : DLat.zb_equiv teq) :
  DLat.zb_equiv (SetoidList.eqlistA teq).
Proof.
constructor.
- induction x.
  + by constructor.
  + constructor; [by apply (DLat.zb_equiv_refl Hteq)|by auto].
- induction 1.
  + by constructor.
  + constructor; [by apply (DLat.zb_equiv_sym Hteq)|by apply IHHeq].
- intros x y z Hxy.
  generalize x y Hxy z; clear x y Hxy z.
  induction 1; inversion 1; subst.
  + by constructor.
  + constructor; [by apply (DLat.zb_equiv_trans Hteq) with x'|by apply IHHxy].
Qed.

Definition list_val_zb_eq : DLat.zb_equiv (SetoidList.eqlistA Val.eq) :=
  list_zb_eq Val.zb_eq.

Definition aeqm1 (f : Mem.t -> Acc.MAcc.m Mem.t) : Prop :=
  forall m m' (Hm' : disjoint m' (Acc.get_acc (f m))),
    Acc.MAcc.eq Mem.zb_eq (f (Mem.join m m')) (mem_join (f m) m').

Definition aeqm2 (f : Mem.t -> Mem.t -> Acc.MAcc.m Mem.t) : Prop :=
  forall m1 m2 m' (Hm' : disjoint m' (Acc.get_acc (f m1 m2))),
    Acc.MAcc.eq Mem.zb_eq
                (f (Mem.join m1 m') (Mem.join m2 m'))
                (mem_join (f m1 m2) m').

Lemma aeqm_deg1 : forall f (Hf : aeqm1 f), aeqm2 (fun m _ => f m).
Proof. unfold aeqm1, aeqm2; i. by apply Hf. Qed.

Lemma aeqm_deg2 : forall f (Hf : aeqm1 f), aeqm2 (fun _ m => f m).
Proof. unfold aeqm1, aeqm2; i. by apply Hf. Qed.

Lemma aeqm2_sym : forall f (Hf : aeqm2 f), aeqm2 (fun m m' => f m' m).
Proof. unfold aeqm2; i. by apply Hf. Qed.

Definition aeqv T (t_eq : T -> T -> Prop) (Ht : DLat.zb_equiv t_eq)
           (f : Mem.t -> Acc.MAcc.m T) : Prop :=
  forall m m' (Hm' : disjoint m' (Acc.get_acc (f m))),
    Acc.MAcc.eq Ht (f (Mem.join m m')) (f m).

Lemma aeqv_1
      T (t_eq : T -> T -> Prop) (Hteq : DLat.zb_equiv t_eq)
      U (u_eq : U -> U -> Prop) (Hueq : DLat.zb_equiv u_eq) :
  forall (f : T -> Acc.MAcc.m U)
     (Hf_mor : Proper (t_eq ==> Acc.MAcc.eq Hueq) f)
     v (Hv : aeqv Hteq v),
    aeqv Hueq (fun m => Acc.MAcc.bind (v m) f).
Proof. {
unfold aeqv; i.
specialize (Hv m m').
remember (v m) as v1; destruct v1 as [v1 a1].
remember (v (Mem.join m m')) as v2; destruct v2 as [v2 a2].
simpl in *.
remember (f v1) as fv1; destruct fv1 as [fv1 fa1].
remember (f v2) as fv2; destruct fv2 as [fv2 fa2].
exploit Hv
; [eapply disjoint_mono; [|by apply Hm']; s; by apply Acc.join_left|].
intros [Hv21 Ha12].
assert (Acc.MAcc.eq Hueq (fv1, fa1) (fv2, fa2)) as Hf.
{ rewrite Heqfv1, Heqfv2. by apply Hf_mor, (DLat.zb_equiv_sym Hteq). }
constructor.
- by apply (DLat.zb_equiv_sym Hueq), Hf.
- apply Acc.join_eq; [by auto|by apply Acc.eq_sym, Hf].
} Qed.

Lemma aeqv_2
      T (t_eq : T -> T -> Prop) (Hteq : DLat.zb_equiv t_eq)
      U (u_eq : U -> U -> Prop) (Hueq : DLat.zb_equiv u_eq) :
  forall (f : Mem.t -> T -> Acc.MAcc.m U)
     (Hf : forall x, aeqv Hueq (fun m => f m x))
     (Hf_mor : Proper (Mem.eq ==> t_eq ==> Acc.MAcc.eq Hueq) f)
     v (Hv : aeqv Hteq v),
    aeqv Hueq (fun m => Acc.MAcc.bind (v m) (f m)).
Proof. {
unfold aeqv; i.
specialize (Hv m m').
remember (v m) as v1; destruct v1 as [v1 a1].
remember (v (Mem.join m m')) as v2; destruct v2 as [v2 a2].
simpl in *.
remember (f m v1) as fv1; destruct fv1 as [fv1 fa1].
remember (f (Mem.join m m') v2) as fv2; destruct fv2 as [fv2 fa2].
exploit Hv
; [eapply disjoint_mono; [|by apply Hm']; s; by apply Acc.join_left|].
intros [Hv21 Ha12].
assert (Acc.MAcc.eq Hueq (fv2, fa2) (fv1, fa1)) as Hf'.
{ rewrite Heqfv1, Heqfv2.
  apply (DLat.zb_equiv_trans (Acc.MAcc.eq_equiv Hueq))
  with (f (Mem.join m m') v1); [apply Hf_mor; [by apply Mem.eq_refl|by auto]|].
  apply Hf.
  rewrite <- Heqfv1; eapply disjoint_right; by apply Hm'. }
constructor.
- by apply Hf'.
- apply Acc.join_eq; [by auto|by apply Hf'].
} Qed.

Lemma aeqv_3 T (t_eq : T -> T -> Prop) (Hteq : DLat.zb_equiv t_eq) :
  forall x, aeqv Hteq (fun _ => x).
Proof.
unfold aeqv; i.
by apply (DLat.zb_equiv_refl (Acc.MAcc.eq_equiv Hteq)).
Qed.

Definition aeqmm (f : Acc.MAcc.m Mem.t -> Acc.MAcc.m Mem.t) : Prop :=
  forall m m' (Hm' : disjoint m' (Acc.get_acc (f m))),
    Acc.MAcc.eq Mem.zb_eq (f (mem_join m m')) (mem_join (f m) m').

Definition aeqmv T (t_eq : T -> T -> Prop) (Ht : DLat.zb_equiv t_eq)
           (f : Mem.t -> Acc.MAcc.m T -> Acc.MAcc.m T) : Prop :=
  forall m m' v (Hm' : disjoint m' (Acc.get_acc (f m v))),
    Acc.MAcc.eq Ht (f (Mem.join m m') v) (f m v).

Lemma aeqmv_1 T (t_eq : T -> T -> Prop) (Ht : DLat.zb_equiv t_eq) :
  forall (f : Mem.t -> Acc.MAcc.m T -> Acc.MAcc.m T) (Hf : aeqmv Ht f) v,
    aeqv Ht (fun m => f m v).
Proof. unfold aeqmv, aeqv; i. by apply Hf, Hm'. Qed.

Lemma aeqm1_1 :
  forall (f : Acc.MAcc.m Mem.t -> Acc.MAcc.m Mem.t) (Hf : aeqmm f)
     g (Hg : forall m m', g (Mem.join m m') = mem_join (g m) m'),
    aeqm1 (fun m => f (g m)).
Proof. {
unfold aeqmm, aeqm1; i.
eapply (DLat.zb_equiv_trans (Acc.MAcc.eq_equiv Mem.zb_eq))
; [|by apply Hf].
rewrite Hg; apply (DLat.zb_equiv_refl (Acc.MAcc.eq_equiv Mem.zb_eq)).
} Qed.

Lemma bind_mem1 :
  forall f (Hf : aeqm1 f)
     (Hf_mor : Proper (Mem.eq ==> Acc.MAcc.eq Mem.zb_eq) f)
     v (Hv : aeqm1 v),
    aeqm1 (fun m => Acc.MAcc.bind (v m) f).
Proof. {
unfold aeqm1; i.
unfold Acc.MAcc.bind.
remember (v (Mem.join m m')) as va1; destruct va1 as [v1 a1].
remember (f v1) as va2; destruct va2 as [v2 a2].
remember (v m) as va1'; destruct va1' as [v1' a1'].
remember (f v1') as va2'; destruct va2' as [v2' a2'].
s in Hm'. rewrite <- Heqva2' in Hm'. s in Hm'.

assert (Acc.MAcc.eq Mem.zb_eq (v1, a1) (mem_join (v1', a1') m')) as Heq1.
{ rewrite Heqva1, Heqva1'. apply Hv.
  rewrite <- Heqva1'. s.
  eapply disjoint_left; by apply Hm'. }
destruct Heq1 as [Heq11 Heq12]. simpl in Heq11, Heq12.

assert (Acc.MAcc.eq Mem.zb_eq (v2, a2) (mem_join (v2', a2') m')) as Heq2.
{ rewrite Heqva2, Heqva2'.
  apply (DLat.zb_equiv_trans (Acc.MAcc.eq_equiv Mem.zb_eq))
  with (f (Mem.join v1' m')).
  - by apply Hf_mor.
  - apply Hf.
    rewrite <- Heqva2'. s.
    eapply disjoint_right; by apply Hm'. }
destruct Heq2 as [Heq21 Heq22]; simpl in Heq21, Heq22.

unfold mem_join. s. split.
- by auto.
- by apply Acc.join_eq.
} Qed.

Lemma bind_mem2 :
  forall f (Hf : aeqm2 f)
     (Hf_mor : Proper (Mem.eq ==> Mem.eq ==> Acc.MAcc.eq Mem.zb_eq) f)
     v (Hv : aeqm1 v),
    aeqm1 (fun m => Acc.MAcc.bind (v m) (fun m' => f m' m)).
Proof. {
unfold aeqm1; i.
unfold Acc.MAcc.bind.
remember (v (Mem.join m m')) as va1; destruct va1 as [v1 a1].
remember (f v1 (Mem.join m m')) as va2; destruct va2 as [v2 a2].
remember (v m) as va1'; destruct va1' as [v1' a1'].
remember (f v1' m) as va2'; destruct va2' as [v2' a2'].
s in Hm'. rewrite <- Heqva2' in Hm'. s in Hm'.

assert (Acc.MAcc.eq Mem.zb_eq (v1, a1) (mem_join (v1', a1') m')) as Heq1.
{ rewrite Heqva1, Heqva1'. apply Hv.
  rewrite <- Heqva1'. s.
  eapply disjoint_left; by apply Hm'. }
destruct Heq1 as [Heq11 Heq12]. simpl in Heq11, Heq12.

assert (Acc.MAcc.eq Mem.zb_eq (v2, a2) (mem_join (v2', a2') m')) as Heq2.
{ rewrite Heqva2, Heqva2'.
  apply (DLat.zb_equiv_trans (Acc.MAcc.eq_equiv Mem.zb_eq))
  with (f (Mem.join v1' m') (Mem.join m m')).
  - apply Hf_mor; [by auto|by apply Mem.eq_refl].
  - apply Hf.
    rewrite <- Heqva2'. s.
    eapply disjoint_right; by apply Hm'. }
destruct Heq2 as [Heq21 Heq22]; simpl in Heq21, Heq22.

unfold mem_join. s. split.
- by auto.
- by apply Acc.join_eq.
} Qed.

Lemma bind_mem3 :
forall (v : Mem.t -> Acc.MAcc.m Mem.t) (f : Mem.t -> Mem.t -> Acc.MAcc.m Mem.t)
   (Hv : aeqm1 v) (Hf : aeqm2 f)
   (Hf_mor : Proper (Mem.eq ==> Mem.eq ==> Acc.MAcc.eq Mem.zb_eq) f),
  aeqm2 (fun m1 m2 => Acc.MAcc.bind (v m1) (fun m3 => f m2 m3)).
Proof.
unfold aeqm1, aeqm2; i.

exploit (Hv m1 m').
{ destruct (v m1). simpl in *.
  destruct (f m2 t). simpl in Hm'.
  eapply disjoint_left. by apply Hm'. }
clear Hv; intro Hv.
remember (v m1). destruct m as [v1 a1].
remember (v (Mem.join m1 m')). destruct m as [v1' a1'].
simpl in *. destruct Hv as [Hvm' Hva'].

exploit (Hf m2 v1 m').
{ destruct (f m2 v1). simpl in *.
  eapply disjoint_right. by apply Hm'. }
clear Hf; intro Hf.
assert (Acc.MAcc.eq Mem.zb_eq (f (Mem.join m2 m') v1') (mem_join (f m2 v1) m'))
  as Hf'.
{ eapply (DLat.zb_equiv_trans (Acc.MAcc.eq_equiv Mem.zb_eq)); [|by apply Hf].
  apply Hf_mor; [by apply Mem.eq_refl|by auto]. }
remember (f m2 v1). destruct m as [v2 a2].
remember (f (Mem.join m2 m') v1'). destruct m as [v2' a2'].
simpl in *. destruct Hf' as [Hfm' Hfa'].

split; [by auto|by apply Acc.join_eq].
Qed.

Lemma bind_val1 T (t_eq : T -> T -> Prop) (Ht : DLat.zb_equiv t_eq):
  forall f (Hf : forall v, aeqm1 (f v))
     (Hf_mor : Proper (t_eq ==> Mem.eq ==> Acc.MAcc.eq Mem.zb_eq) f)
     (v : Mem.t -> Acc.MAcc.m T) (Hv : aeqv Ht v),
    aeqm1 (fun m => Acc.MAcc.bind (v m) (fun v' => f v' m)).
Proof. {

i. unfold aeqm1, Acc.MAcc.eq. i.
remember (v (Mem.join m m')) as va1; destruct va1 as [v1 a1].
remember (v m) as va2; destruct va2 as [v2 a2].
simpl in Hm'. unfold Acc.MAcc.bind at 1.
remember (f v1 (Mem.join m m')) as ma3; destruct ma3 as [m3 a3].
remember (f v2 m) as ma4; destruct ma4 as [m4 a4].
simpl in Hm'. unfold Acc.MAcc.bind at 1.
unfold mem_join. rewrite <- Heqma4. s.

assert (Acc.MAcc.eq Ht (v1, a1) (v2, a2)) as Heq1.
{ rewrite Heqva1, Heqva2. apply Hv.
  rewrite <- Heqva2. s. eapply disjoint_left; by apply Hm'. }
destruct Heq1 as [Heq_v12 Heq_a12].

remember (f v1 m) as ma5; destruct ma5 as [m5 a5].
assert (Acc.MAcc.eq Mem.zb_eq (m5, a5) (m4, a4)) as Heq4.
{ rewrite Heqma5, Heqma4. apply Hf_mor; [by auto|by apply Mem.eq_refl]. }
destruct Heq4 as [Heq_m54 Heq_a54].

assert (Acc.MAcc.eq Mem.zb_eq (m3, a3) (mem_join (m5, a5) m')) as Heq3.
{ rewrite Heqma3, Heqma5. apply Hf.
  rewrite <- Heqma5. s.
  eapply disjoint_mor
  ; [by apply Mem.eq_refl|by apply Acc.eq_sym, Heq_a54|].
  eapply disjoint_right; by apply Hm'. }
destruct Heq3 as [Heq_m35 Heq_a35]; simpl in Heq_m35, Heq_a35.

split.
- eapply Mem.eq_trans; [by apply Heq_m35|].
  apply Mem.join_eq; [by auto|by apply Mem.eq_refl].
- apply Acc.join_eq; [by auto|].
  eapply Acc.eq_trans; [by apply Heq_a35|by auto].
} Qed.

Lemma bind_val2 T (t_eq : T -> T -> Prop) (Ht : DLat.zb_equiv t_eq):
  forall f (Hf : forall v, aeqm2 (f v))
     (Hf_mor : Proper (t_eq ==> Mem.eq ==> Mem.eq ==> Acc.MAcc.eq Mem.zb_eq) f)
     (v : Mem.t -> Acc.MAcc.m T) (Hv : aeqv Ht v),
  aeqm2 (fun m m' : Mem.t => Acc.MAcc.bind (v m) (fun v' => f v' m m')).
Proof. {
i. unfold aeqm2, Acc.MAcc.eq. i.
remember (v (Mem.join m1 m')) as va1; destruct va1 as [v1 a1].
remember (v m1) as va2; destruct va2 as [v2 a2].
simpl in Hm'. unfold Acc.MAcc.bind.
remember (f v1 (Mem.join m1 m') (Mem.join m2 m')) as ma3; destruct ma3 as [m3 a3].
remember (f v2 m1 m2) as ma4; destruct ma4 as [m4 a4].
simpl in Hm'.
unfold mem_join. s.

assert (Acc.MAcc.eq Ht (v1, a1) (v2, a2)) as Heq1.
{ rewrite Heqva1, Heqva2. apply Hv.
  rewrite <- Heqva2. s. eapply disjoint_left; by apply Hm'. }
destruct Heq1 as [Heq_v12 Heq_a12].

remember (f v1 m1 m2) as ma5; destruct ma5 as [m5 a5].
assert (Acc.MAcc.eq Mem.zb_eq (m5, a5) (m4, a4)) as Heq4.
{ rewrite Heqma5, Heqma4.
  apply Hf_mor; [by auto|by apply Mem.eq_refl|by apply Mem.eq_refl]. }
destruct Heq4 as [Heq_m54 Heq_a54].

assert (Acc.MAcc.eq Mem.zb_eq (m3, a3) (mem_join (m5, a5) m')) as Heq3.
{ rewrite Heqma3, Heqma5. apply Hf.
  rewrite <- Heqma5. s.
  eapply disjoint_mor
  ; [by apply Mem.eq_refl|by apply Acc.eq_sym, Heq_a54|].
  eapply disjoint_right; by apply Hm'. }
destruct Heq3 as [Heq_m35 Heq_a35]; simpl in Heq_m35, Heq_a35.

split.
- eapply Mem.eq_trans; [by apply Heq_m35|].
  apply Mem.join_eq; [by auto|by apply Mem.eq_refl].
- apply Acc.join_eq; [by auto|].
  eapply Acc.eq_trans; [by apply Heq_a35|by auto].
} Qed.

Lemma bind_mmem :
  forall f (Hf : aeqm1 f), aeqmm (fun m_a => Acc.MAcc.bind m_a f).
Proof. {
unfold aeqm1, aeqmm; i.
destruct m as [m a]; s. specialize (Hf m m'). s in Hm'.
destruct (f m) as [fm' fa']. simpl in Hf, Hm'.
remember (f (Mem.join m m')) as fmm; destruct fmm as [fmm' fma']; s.
s in Hf.
assert (disjoint m' fa') as Hdis; [eapply disjoint_right; by apply Hm'|].
specialize (Hf Hdis).
destruct Hf as [Hm Ha].
split; [by auto|apply Acc.join_eq; [by apply Acc.eq_refl|by auto]].
} Qed.

Lemma bind_mval T (t_eq : T -> T -> Prop) (Ht : DLat.zb_equiv t_eq) :
  forall (f : T -> Mem.t -> Acc.MAcc.m T) (Hf : forall v, aeqv Ht (f v)),
    aeqmv Ht (fun m acc_a => Acc.MAcc.bind acc_a (fun v => f v m)).
Proof. {
unfold aeqmv, aeqv; i.
unfold Acc.MAcc.bind, Acc.MAcc.ret in *.
destruct v as [v1 a1]. specialize (Hf v1 m m').
remember (f v1 m) as v2; destruct v2 as [v2 a2].
remember (f v1 (Mem.join m m')) as v2'; destruct v2' as [v2' a2'].
exploit Hf; [eapply disjoint_mono; [|by apply Hm']; s; apply Acc.join_right|].
s. intros [Hv Ha]. split; [by apply Hv|].
apply Acc.join_eq; [by apply Acc.eq_refl|by auto].
} Qed.

Lemma ret_mem1 :
  forall x (Hx : forall m m', Mem.eq (x (Mem.join m m')) (Mem.join (x m) m')),
    aeqm1 (fun m => Acc.MAcc.ret (x m)).
Proof. {
unfold Acc.MAcc.ret, aeqm1. i. split; s; [by apply Hx|by apply Acc.eq_refl].
} Qed.

Lemma ret_mem2 :
  forall (f : Acc.MAcc.m Mem.t -> Acc.MAcc.m Mem.t) (Hf : aeqmm f),
    aeqm1 (fun m => f (Acc.MAcc.ret m)).
Proof. i; apply aeqm1_1; by auto. Qed.

Lemma ret_mem3 :
  forall (x : Mem.t -> Mem.t -> Mem.t)
     (Hx : forall m1 m2 m', Mem.eq (x (Mem.join m1 m') (Mem.join m2 m'))
                               (Mem.join (x m1 m2) m')),
    aeqm2 (fun m1 m2 => Acc.MAcc.ret (x m1 m2)).
Proof. {
unfold Acc.MAcc.ret, aeqm2. i. split; s; [by apply Hx|by apply Acc.eq_refl].
} Qed.

Lemma fold_access_sound :
  forall f s (Hf_ext : forall e m, Acc.le (Acc.get_acc m) (Acc.get_acc (f e m)))
     (Hf_access_sound : forall e (He : PowLoc.mem e s = true), aeqmm (f e))
     (Hf_mor : forall e,
         Proper
           (Acc.MAcc.eq Mem.zb_eq ==> Acc.MAcc.eq Mem.zb_eq)
           (f e)),
    aeqmm (PowLoc.fold f s).
Proof.
i. unfold aeqmm. i. generalize Hm'; clear Hm'.
apply PowLoc.fold2_5 with (f1:=f) (f2:=f) (i1:=mem_join m m') (i2:=m); i
; [|by apply (DLat.zb_equiv_refl (Acc.MAcc.eq_equiv Mem.zb_eq))].
apply (DLat.zb_equiv_trans (Acc.MAcc.eq_equiv Mem.zb_eq))
with (f e (mem_join t2 m')).
- apply Hf_mor, Ht.
  eapply disjoint_mono; [by apply Hf_ext|by apply Hm'].
- apply Hf_access_sound; [by auto|by auto].
Qed.

Lemma fold_access_sound' T (t_eq : T -> T -> Prop) (Ht : DLat.zb_equiv t_eq) :
  forall f s (Hf_ext : forall m e v, Acc.le (Acc.get_acc v) (Acc.get_acc (f m e v)))
     (Hf_access_sound : forall e (He : PowLoc.mem e s = true), aeqmv Ht (fun m => f m e))
     (Hf_mor :
        forall m e, Proper (Acc.MAcc.eq Ht ==> Acc.MAcc.eq Ht) (f m e)),
     aeqmv Ht (fun m => PowLoc.fold (f m) s).
Proof.
i; unfold aeqmv; i. generalize Hm'; clear Hm'.
apply PowLoc.fold2_5 with (f1:=f (Mem.join m m')) (f2:=f m) (i1:=v) (i2:=v); i
; [|by apply (DLat.zb_equiv_refl (Acc.MAcc.eq_equiv Ht))].
apply (DLat.zb_equiv_trans (Acc.MAcc.eq_equiv Ht))
with (f (Mem.join m m') e t2).
- apply Hf_mor, Ht0.
  eapply disjoint_mono; [by apply Hf_ext|by apply Hm'].
- apply Hf_access_sound; [by auto|by auto].
Qed.

Lemma list_fold_access_sound
      (T : Type) (t_eq : T -> T -> Prop) (Ht : DLat.zb_equiv t_eq)
      (U : Type) (u_eq : U -> U -> Prop) (Hu : DLat.zb_equiv u_eq) :
  forall (l : list U) f (i : Mem.t -> Acc.MAcc.m T)
     (Hf : forall i (Hi : aeqv Ht i)
              (Hi_mor : Proper (Mem.eq ==> Acc.MAcc.eq Ht) i)
              e,
         aeqv Ht (fun m : Mem.t => f m e (i m)))
     (Hf_mor : Proper (Mem.eq ==> u_eq ==> Acc.MAcc.eq Ht ==> Acc.MAcc.eq Ht) f)
     (Hi : aeqv Ht i) (Hi_mor : Proper (Mem.eq ==> Acc.MAcc.eq Ht) i),
    aeqv Ht (fun m : Mem.t => list_fold (f m) l (i m)).
Proof.
unfold list_fold; induction l; i.
- s. by auto.
- simpl List.fold_left. apply IHl.
  + i; by apply Hf.
  + by auto.
  + by apply Hf.
  + intros m1 m2 Hm; apply Hf_mor
    ; [by auto|by apply (DLat.zb_equiv_refl Hu)|by apply Hi_mor].
Qed.

Lemma list_fold_access_sound1 U :
  forall (l : list U) f
     (Hf : forall i (Hi : aeqm1 i) e, aeqm1 (fun m : Mem.t => f m e (i m)))
     (i : Mem.t -> Acc.MAcc.m Mem.t) (Hi : aeqm1 i),
    aeqm1 (fun m : Mem.t => list_fold (f m) l (i m)).
Proof.
unfold list_fold; induction l; i.
- s. by auto.
- simpl List.fold_left. by apply IHl, Hf.
Qed.
