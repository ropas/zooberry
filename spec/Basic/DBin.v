(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** Binary lattice *)

Set Implicit Arguments.

Require Import ZArith.
Require Import hpattern vgtac.
Require Import TStr VocabA DLat.

Module Bin <: LAT.

Inductive t' := Bot | Top.
Definition t := t'.

Inductive le' : t -> t -> Prop :=
| le_bot : forall (x : t), le' Bot x
| le_top : forall (x : t), le' x Top.
Definition le : t -> t -> Prop := le'.

Inductive eq' : t -> t -> Prop :=
| eq_bot : eq' Bot Bot
| eq_top : eq' Top Top.
Definition eq : t -> t -> Prop := eq'.

Lemma le_refl : forall (x y : t) (Heq : eq x y), le x y.
Proof. inversion 1; econs; by eauto using le'_refl. Qed.

Lemma le_antisym :
  forall (x y : t) (le1 : le x y) (le2 : le y x), eq x y.
Proof. inversion 1; inversion 1; econs; by eauto using le'_antisym. Qed.

Lemma le_trans :
  forall (x y z : t) (le1 : le x y) (le2 : le y z), le x z.
Proof. inversion 1; inversion 1; econs; by eauto using le'_trans. Qed.

Lemma eq_refl : forall (x : t), eq x x.
Proof. destruct x; econs; by eauto using eq'_refl. Qed.

Lemma eq_sym : forall (x y : t) (Heq : eq x y), eq y x.
Proof. inversion 1; econs; by eauto using eq'_sym. Qed.

Lemma eq_trans :
  forall (x y z : t) (eq1 : eq x y) (eq2 : eq y z), eq x z.
Proof. inversion 1; inversion 1; econs; by eauto using eq'_trans. Qed.

Definition le_dec (x y : t) : {le x y} + {~ le x y}.
refine (match x, y with
          | Bot, y => left (le_bot y)
          | x, Top => left (le_top x)
          | _, _ => right _
        end); inversion 1.
Defined.

Definition eq_dec (x y : t) : {eq x y} + {~ eq x y}.
refine (match x, y with
          | Bot, Bot => left eq_bot
          | Top, Top => left eq_top
          | _, _ => right _
        end); inversion 1.
Defined.

Definition top : t := Top.

Lemma top_prop : forall (x : t), le x top.
Proof. destruct x; vauto. Qed.

Definition bot : t := Bot.

Lemma bot_prop : forall (x : t), le bot x.
Proof. vauto. Qed.

Definition join (x y : t) : t :=
  match x, y with
    | Bot, a
    | a, Bot => a
    | _, _ => Top
  end.

Lemma join_left : forall (x y : t), le x (join x y).
Proof.
  intros; unfold join.
  destruct x, y; constructor.
Qed.

Lemma join_right : forall (x y : t), le y (join x y).
Proof.
  intros; unfold join.
  destruct x, y; constructor.
Qed.

Lemma join_lub : forall (x y u : t) (Hx : le x u) (Hy : le y u), le (join x y) u.
Proof.
  inversion 1; inversion 1; constructor.
Qed.

Definition meet (x y : t) : t :=
  match x, y with
    | Bot, _
    | _, Bot => Bot
    | _, _ => Top
  end.

Lemma meet_left : forall (x y : t), le (meet x y) x.
Proof. destruct x, y; constructor. Qed.

Lemma meet_right : forall (x y : t), le (meet x y) y.
Proof. destruct x, y; constructor. Qed.

Lemma meet_glb : forall (x y l : t) (Hx : le l x) (Hy : le l y), le l (meet x y).
Proof. inversion 1; inversion 1; constructor. Qed.

Definition widen (x y : t) : t := join x y.

Definition narrow (x y : t) : t := meet x y.

Include JoinMeetProp.

End Bin.
