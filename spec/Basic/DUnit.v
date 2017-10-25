(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** Unit key *)

Set Implicit Arguments.

Require Import OrderedType.
Require Import hpattern vgtac.
Require Import DLat.

Module Unit <: KEY.
  Definition t : Type := unit.

  Definition eq (x y : t) : Prop := True.

  Definition lt (x y : t) : Prop := False.

  Lemma eq_refl : forall x : t, eq x x. Proof. econs. Qed.

  Lemma eq_sym : forall x y : t, eq x y -> eq y x. Proof. econs. Qed.

  Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof. econs. Qed.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof. inversion 1. Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof. inversion 1. Qed.

  Definition compare (x y : t) : Compare lt eq x y.
    apply EQ; econs.
  Defined.

  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Proof. left; econs. Defined.

  Definition eqb x y := if eq_dec x y then true else false.

  Definition zb_eq : zb_equiv eq :=
    {| zb_equiv_refl := eq_refl
     ; zb_equiv_sym := eq_sym
     ; zb_equiv_trans := eq_trans |}.
End Unit.
