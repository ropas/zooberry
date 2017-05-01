(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** Lattice constructor: sum of two mem.  *)

Set Implicit Arguments.

Require Import ZArith.
Require Import Setoid.
Require Import Morphisms.
Require Import hpattern vgtac.
Require Import TStr VocabA DLat DFSetAVL.
Require Import DMap DPow.

Module Make (A : KEY) (B : LAT) (PowA : DPow.POW A) <: LAT.

Include Map A B.

Definition subtract (ls : PowA.t) (x : t) :=
  filter (fun k => negb (PowA.mem k ls)) x.

Lemma subtract_1 :
  forall k ls x (Hmem : PowA.mem k ls = true),
    B.eq (find k (subtract ls x)) B.bot.
Proof.
unfold subtract. i. apply filter_2; [|by rewrite Hmem].
intros l1 l2 Hl. f_equal. apply PowA.mem_mor; [by auto|by apply PowA.eq_refl].
Qed.

Lemma subtract_2 :
  forall k ls x (Hmem : PowA.mem k ls = false),
    B.eq (find k (subtract ls x)) (find k x).
Proof.
unfold subtract. i. apply filter_1; [|by rewrite Hmem].
intros l1 l2 Hl. f_equal. apply PowA.mem_mor; [by auto|by apply PowA.eq_refl].
Qed.

Lemma subtract_mor' :
  forall ls, Proper (le ==> le) (subtract ls).
Proof.
unfold subtract; intros ls m1 m2 Hm k.
apply find_mor'; [by apply A.eq_refl|].
apply filter_mor'; [|by auto].
intros l1 l2 Hl. f_equal.
apply PowA.mem_mor; [by auto|by apply PowA.eq_refl].
Qed.

Lemma subtract_mor :
  forall ls, Proper (eq ==> eq) (subtract ls).
Proof.
unfold subtract; intros ls m1 m2 Hm k.
apply find_mor; [by apply A.eq_refl|].
apply filter_mor; [|by auto].
intros l1 l2 Hl. f_equal.
apply PowA.mem_mor; [by auto|by apply PowA.eq_refl].
Qed.

Lemma subtract_mor'_spec :
  forall k ls x y (Hle : B.le (find k x) (find k y)),
    B.le (find k (subtract ls x)) (find k (subtract ls y)).
Proof.
unfold subtract; i.
remember (negb (PowA.mem k ls)) as b; destruct b.
- eapply B.le_trans; [eapply B.le_trans; [|by apply Hle]|].
  + apply B.le_refl; apply filter_1; [|by auto].
    intros l1 l2 Hl; f_equal.
    apply PowA.mem_mor; [by auto|by apply PowA.eq_refl].
  + apply B.le_refl; apply B.eq_sym; apply filter_1; [|by auto].
    intros l1 l2 Hl; f_equal.
    apply PowA.mem_mor; [by auto|by apply PowA.eq_refl].
- apply B.le_trans with B.bot; [|by apply B.bot_prop].
  apply B.le_refl; apply filter_2; [|by auto].
  intros l1 l2 Hl; f_equal.
  apply PowA.mem_mor; [by auto|by apply PowA.eq_refl].
Qed.

Lemma subtract_in :
  forall k ls x (Hin : M.In k (subtract ls x)), PowA.mem k ls = false.
Proof.
unfold subtract, filter, M.filter; i.
apply find_mapsto in Hin.
apply M.P.filter_iff in Hin.
- destruct Hin as [Hmaps Hmem].
  by apply Bool.negb_true_iff in Hmem.
- unfold Proper, respectful; i; f_equal.
  apply PowA.mem_mor; [by auto|by apply PowA.eq_refl].
Qed.

Definition restrict (ls : PowA.t) (x : t) := filter (fun k => PowA.mem k ls) x.

Lemma restrict_1 :
  forall k ls x (Hmem : PowA.mem k ls = true),
    B.eq (find k (restrict ls x)) (find k x).
Proof.
unfold restrict. i. apply filter_1; [|by rewrite Hmem].
intros l1 l2 Hl. apply PowA.mem_mor; [by auto|by apply PowA.eq_refl].
Qed.

Lemma restrict_2 :
  forall k ls x (Hmem : PowA.mem k ls = false),
    B.eq (find k (restrict ls x)) B.bot.
Proof.
unfold restrict. i. apply filter_2; [|by rewrite Hmem].
intros l1 l2 Hl. apply PowA.mem_mor; [by auto|by apply PowA.eq_refl].
Qed.

Lemma restrict_mor' :
  forall ls, Proper (le ==> le) (restrict ls).
Proof.
unfold restrict; intros ls m1 m2 Hm k.
apply find_mor'; [by apply A.eq_refl|].
apply filter_mor'; [|by auto].
intros l1 l2 Hl. apply PowA.mem_mor; [by auto|by apply PowA.eq_refl].
Qed.

Lemma restrict_mor :
  forall ls, Proper (eq ==> eq) (restrict ls).
Proof.
unfold restrict; intros ls m1 m2 Hm k.
apply find_mor; [by apply A.eq_refl|].
apply filter_mor; [|by auto].
intros l1 l2 Hl.
apply PowA.mem_mor; [by auto|by apply PowA.eq_refl].
Qed.

Lemma restrict_mor'_spec :
  forall k ls x y (Hle : B.le (find k x) (find k y)),
    B.le (find k (restrict ls x)) (find k (restrict ls y)).
Proof.
unfold restrict; i.
remember (PowA.mem k ls) as b; destruct b.
- eapply B.le_trans; [eapply B.le_trans; [|by apply Hle]|].
  + apply B.le_refl; apply filter_1; [|by auto].
    intros l1 l2 Hl.
    apply PowA.mem_mor; [by auto|by apply PowA.eq_refl].
  + apply B.le_refl; apply B.eq_sym; apply filter_1; [|by auto].
    intros l1 l2 Hl.
    apply PowA.mem_mor; [by auto|by apply PowA.eq_refl].
- apply B.le_trans with B.bot; [|by apply B.bot_prop].
  apply B.le_refl; apply filter_2; [|by auto].
  intros l1 l2 Hl.
  apply PowA.mem_mor; [by auto|by apply PowA.eq_refl].
Qed.

Lemma restrict_in :
  forall k ls x (Hin : M.In k (restrict ls x)), PowA.mem k ls = true.
Proof.
unfold restrict, filter, M.filter; i.
apply find_mapsto in Hin.
apply M.P.filter_iff in Hin.
- destruct Hin as [Hmaps Hmem]; by auto.
- unfold Proper, respectful; i.
  apply PowA.mem_mor; [by auto|by apply PowA.eq_refl].
Qed.

Lemma powa_mem_mor (ls : PowA.t) :
  Proper (A.eq ==> Logic.eq) (fun k => PowA.mem k ls).
Proof.
intros l1 l2 Hl. apply PowA.mem_mor; [by auto | by apply PowA.eq_refl].
Qed.

Lemma negb_powa_mem_mor (ls : PowA.t) :
  Proper (A.eq ==> Logic.eq) (fun k => negb (PowA.mem k ls)).
Proof.
intros l1 l2 Hl. f_equal.
apply PowA.mem_mor; [by auto | by apply PowA.eq_refl].
Qed.

Lemma restrict_subtract_1 :
  forall ls m, eq m (join (restrict ls m) (subtract ls m)).
Proof.
unfold eq; i.
eapply B.eq_trans; [|apply B.eq_sym; apply join_find].
remember (PowA.mem k ls) as b; destruct b; symmetry in Heqb.
- eapply B.eq_trans; [|by apply B.join_comm_eq].
  eapply B.eq_trans; [|apply B.join_le_idem].
  + apply B.eq_sym; by apply restrict_1.
  + apply B.le_trans with (find k m).
    * unfold subtract. apply filter_le. by apply negb_powa_mem_mor.
    * apply B.le_refl; apply B.eq_sym. by apply restrict_1.
- eapply B.eq_trans; [|apply B.join_le_idem].
  + apply B.eq_sym. by apply subtract_2.
  + apply B.le_trans with (find k m).
    * unfold subtract. apply filter_le. by apply powa_mem_mor.
    * apply B.le_refl; apply B.eq_sym. by apply subtract_2.
Qed.

Definition eq_wrt (wrt : PowA.t) (x y : t) : bool :=
  let eq_wrt' k :=
    if B.eq_dec (find k x) (find k y) then true else false in
  PowA.for_all print eq_wrt' wrt.

Lemma eq_wrt_1 :
  forall k wrt x y (Hk: PowA.mem k wrt) (Heq: eq_wrt wrt x y = true),
    B.eq (find k x) (find k y).
Proof.
unfold eq_wrt. i. apply (PowA.for_all_1 (k:=k)) in Heq.
- dest_if.
- by auto.
- intros k1 k2 Hk'.
  destruct (B.eq_dec (find k1 x) (find k1 y))
  ; destruct (B.eq_dec (find k2 x) (find k2 y)); try reflexivity.
  + elim f.
    eapply B.eq_trans. eapply B.eq_trans; [|by apply e].
    * apply find_mor; [by apply A.eq_sym|by apply eq_refl].
    * apply find_mor; [by auto|by apply eq_refl].
  + elim f.
    eapply B.eq_trans. eapply B.eq_trans; [|by apply e].
    * apply find_mor; [by auto|by apply eq_refl].
    * apply find_mor; [by apply A.eq_sym|by apply eq_refl].
Qed.

End Make.
