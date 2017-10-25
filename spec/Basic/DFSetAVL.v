(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(* Wrapper of FSetAVL *)

Require FSetAVL FSetFacts.
Require MSetProperties.
Require Import OrderedType ZArith.
Require Import hpattern vgtac.
Require Import VocabA.
Require Import Morphisms.

Module FSetAVL'.

Module Make (X : OrderedType).

Module OrigS := FSetAVL.Make X.
Include OrigS.
Module SF := FSetFacts.Facts OrigS.
Module MSF := MSetProperties.OrdProperties MSet.

Lemma choose_mor : Proper (eq ==> opt_eq X.eq) choose.
Proof.
unfold opt_eq, choose; intros s1 s2 Hs.
remember (MSet.choose s1) as opt_x. remember (MSet.choose s2) as opt_y.
pose (MSF.choose_equal Hs) as Hchoose.
rewrite <- Heqopt_x in Hchoose. rewrite <- Heqopt_y in Hchoose.
destruct opt_x; destruct opt_y; by auto.
Qed.

Definition choose_only (s : t) : option elt :=
  if eq_nat_dec (cardinal s) 1 then choose s else None.

Lemma choose_only_mor : Proper (eq ==> opt_eq X.eq) choose_only.
Proof.
unfold choose_only, cardinal; intros s1 s2 Hs.
rewrite MSF.P.Equal_cardinal with (s':=s2); [|by auto].
destruct (eq_nat_dec (MSet.cardinal s2) 1); [|by auto].
by apply choose_mor.
Qed.

Lemma mset_raw_cardinal_zero :
  forall s (Hs : MSet.Raw.cardinal s = 0), s = MSet.Raw.Leaf.
Proof. destruct s; [by auto|by inversion 1]. Qed.

Lemma mset_raw_choose_only_1 :
  forall s e (Hse : MSet.Raw.choose s = Some e) (Hs : MSet.Raw.cardinal s = 1),
    MSet.Raw.elements s = cons e nil.
Proof.
destruct s; i.
- inversion Hs.
- simpl in Hs. inversion Hs.
  apply plus_is_O in H0. destruct H0 as [Hs1 Hs2].
  apply mset_raw_cardinal_zero in Hs1.
  apply mset_raw_cardinal_zero in Hs2. subst.
  simpl in Hse. inversion Hse. subst. by auto.
Qed.

Lemma mset_choose_only_1 :
  forall s e (Hse : MSet.choose s = Some e) (Hs : MSet.cardinal s = 1),
    MSet.elements s = cons e nil.
Proof. induction s. i. by apply mset_raw_choose_only_1. Qed.

Lemma choose_only_1 :
  forall s e (Hce : choose_only s = Some e), elements s = cons e nil.
Proof.
unfold choose_only; i.
remember (Nat.eq_dec (cardinal s) 1) as Hcar. destruct Hcar; [|discriminate].
by apply mset_choose_only_1.
Qed.

Lemma choose_only_2 :
  forall l1 l2 l' (Hco : choose_only l' = Some l1) (Hmem : mem l2 l' = true),
    X.eq l1 l2.
Proof.
i. unfold mem in Hmem. rewrite MF.elements_b in Hmem.
apply choose_only_1 in Hco.
unfold elements in Hco. rewrite Hco in Hmem.
inversion Hmem.  apply Bool.orb_true_iff in H0.
elim H0; [i|discriminate].
unfold MF.eqb in H. destruct (MF.eq_dec l2 l1); [|discriminate].
by apply X.eq_sym.
Qed.


Local Open Scope bool.

Definition cond_eq (f g : elt -> bool) : Prop :=
  compat_bool X.eq f /\ (X.eq ==> Logic.eq)%signature f g.

Definition cond_eq_mor :
  forall f g (Hf_mor : compat_bool X.eq f)
         (Hfg_mor : (X.eq ==> Logic.eq)%signature f g),
    compat_bool X.eq g.
Proof.
i. intros x y Hxy.
assert (Hx: g x = f x); [symmetry; apply Hfg_mor; by apply X.eq_refl|].
assert (Hy: g y = f y); [symmetry; apply Hfg_mor; by apply X.eq_refl|].
rewrite Hx, Hy. by apply Hf_mor.
Qed.

Definition for_all_mor : Proper (cond_eq ==> eq ==> Logic.eq)%signature for_all.
Proof.
intros f1 f2 Hf s1 s2 Hs.
destruct Hf as [Hf_mor Hfg_eq].
remember (for_all f1 s1) as b1. remember (for_all f2 s2) as b2.
destruct b1, b2; [by auto| | |by auto].
- symmetry in Heqb1. rewrite Heqb2. symmetry.
  apply SF.for_all_iff in Heqb1; [|by auto].
  apply SF.for_all_iff
  ; [eapply cond_eq_mor; [by apply Hf_mor|by apply Hfg_eq]|].
  intros x Hin. symmetry. assert (Hf: f1 x = true).
  + apply Heqb1. by apply Hs.
  + rewrite <- Hf. apply Hfg_eq. by apply X.eq_refl.
- symmetry in Heqb2. rewrite Heqb1.
  apply SF.for_all_iff in Heqb2
  ; [|eapply cond_eq_mor; [by apply Hf_mor|by apply Hfg_eq]].
  apply SF.for_all_iff; [by auto|].
  intros x Hin. assert (Hg: f2 x = true).
  + apply Heqb2. by apply Hs.
  + rewrite <- Hg. apply Hfg_eq. by apply X.eq_refl.
Qed.

Definition for_all' (print : elt -> unit) (cond : elt -> bool) (m : t) : bool :=
  let add_cond v acc := acc && print_when_false print v cond v in
  fold add_cond m true.

Lemma for_all_raw_false (cond : elt -> bool) :
  forall s, MSet.Raw.fold (fun v acc => acc && cond v) s false = false.
Proof.
induction s.
- by auto.
- s; by rewrite IHs1, Bool.andb_false_intro1.
Qed.

Lemma for_all'_1 (print : elt -> unit) (cond : elt -> bool) (m : t) :
  for_all' print cond m = for_all cond m.
Proof.
unfold for_all, MSet.for_all, for_all', fold, MSet.fold, print_when_false.
induction (MSet.this m).
- by auto.
- s; remember (cond t1) as b; destruct b.
  + remember (MSet.Raw.for_all cond t0_1) as b; destruct b.
    * rewrite IHt0_1; s; rewrite IHt0_2; reflexivity.
    * rewrite IHt0_1; rewrite Bool.andb_false_intro1; [|reflexivity].
      by apply for_all_raw_false.
  + rewrite Bool.andb_false_intro2; [by apply for_all_raw_false|reflexivity].
Qed.

Local Close Scope bool.

Lemma elements_eq :
  forall ls1 ls2 (Heq : Equal ls1 ls2),
    eqlistA X.eq (elements ls1) (elements ls2).
Proof.
i. apply MSF.sort_equivlistA_eqlistA.
- by apply MSet.elements_spec2.
- by apply MSet.elements_spec2.
- constructor; i.
  + apply SF.elements_iff; apply Heq; apply SF.elements_iff; by auto.
  + apply SF.elements_iff; apply Heq; apply SF.elements_iff; by auto.
Qed.

End Make.

End FSetAVL'.
