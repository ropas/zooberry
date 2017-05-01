(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
Set Implicit Arguments.

Require Import Relations.
Require Import Morphisms.
Require Import vgtac DLat.

Module Type Monad.

Axiom m : Type -> Type.

Axiom ret : forall A, A -> m A.

Axiom bind : forall A B, m A -> (A -> m B) -> m B.

Axiom eq :
  forall A (a_eq : relation A) (Ha_eq: zb_equiv a_eq),
    m A -> m A -> Prop.

Axiom eq_equiv :
  forall A (a_eq : relation A) (Ha_eq: zb_equiv a_eq),
    zb_equiv (eq Ha_eq).

Axiom right_unit :
  forall A (a_eq : relation A) (Ha_eq: zb_equiv a_eq) (a: m A),
    eq Ha_eq a (bind a (@ret A)).

Axiom left_unit :
  forall A B (b_eq : relation B) (Hb_eq : zb_equiv b_eq) (a: A) (f : A -> m B),
    eq Hb_eq (f a) (bind (ret a) f).

Axiom assoc :
  forall A B C (c_eq : relation C) (Hc_eq : zb_equiv c_eq)
         (ma: m A) (f: A -> m B) (g: B -> m C),
    eq Hc_eq (bind ma (fun x => bind (f x) g)) (bind (bind ma f) g).

Axiom le :
  forall A (a_eq a_le: relation A) (Ha_le : zb_order a_eq a_le),
    m A -> m A -> Prop.

Axiom le_order :
  forall A (a_eq a_le: relation A) (Ha_eq: zb_equiv a_eq)
         (Ha_le : zb_order a_eq a_le),
    zb_order (eq Ha_eq) (le Ha_le).

Notation "'do' a <- e ; c" :=
  (bind e (fun a => c)) (at level 200, right associativity).

Axiom le_1 :
  forall A B (a_eq a_le: relation A) (Ha_le: zb_order a_eq a_le)
         x (y : m B) f (Hf: forall v, le Ha_le x (f v)),
    le Ha_le x (bind y f).

Axiom le_2 :
  forall A (a_eq a_le: relation A) (Ha_le: zb_order a_eq a_le)
         x f (Hf: forall v, le Ha_le (ret v) (f v)),
    le Ha_le x (bind x f).

Axiom le_3 :
  forall A (a_eq a_le: relation A) (Ha_le: zb_order a_eq a_le)
         x f y (Hx: le Ha_le x y)
         (He: forall v (Hv: le Ha_le (ret v) y), le Ha_le (f v) y),
    le Ha_le (bind x f) y.

Axiom bind_mono :
  forall A (a_eq a_le: relation A) (Ha_le: zb_order a_eq a_le)
         B (b_eq b_le : relation B) (Hb_le: zb_order b_eq b_le),
    Proper (le Ha_le ==> (a_le ==> le Hb_le) ==> le Hb_le)
           (bind (A := A) (B := B)).

Axiom ret_mono :
  forall A (a_eq a_le: relation A) (Ha_le: zb_order a_eq a_le),
    Proper (a_le ==> le Ha_le) (ret (A := A)).

Axiom ret_join_lub :
  forall A (a_eq a_le: relation A) (Ha_le: zb_order a_eq a_le)
         x y z (Hx: le Ha_le (ret x) z) (Hy: le Ha_le (ret y) z) join
         (Hjoin_lub:
            forall x y z (Hx: a_le x z) (Hy: a_le y z), a_le (join x y) z),
    le Ha_le (ret (join x y)) z.

End Monad.

Module MId <: Monad.

Definition m (t: Type) : Type := t.

Definition ret (A : Type) (x : m A) := x.

Definition bind (A B : Type) (x : m A) (f : A -> m B) := f x.

Definition eq (A : Type) (a_eq : relation A) (Ha_eq : zb_equiv a_eq) x y :=
  a_eq x y.

Definition eq_equiv :
  forall A (a_eq : relation A) (Ha_eq : zb_equiv a_eq),
    zb_equiv (eq Ha_eq).
Proof.
constructor.
- unfold eq. by apply (zb_equiv_refl Ha_eq).
- unfold eq. by apply (zb_equiv_sym Ha_eq).
- unfold eq. by apply (zb_equiv_trans Ha_eq).
Qed.

Lemma right_unit :
  forall A (a_eq : relation A) (Ha_eq : zb_equiv a_eq) (a : m A),
    eq Ha_eq a (bind a (@ret A)).
Proof.
unfold bind, ret, eq; intros.
apply (zb_equiv_refl Ha_eq).
Qed.

Lemma left_unit :
  forall A B (b_eq : relation B) (Hb_eq : zb_equiv b_eq) (a : A) (f : A -> m B),
    eq Hb_eq (f a) (bind (ret a) f).
Proof.
unfold bind, ret, eq; intros.
apply (zb_equiv_refl Hb_eq).
Qed.

Lemma assoc :
  forall A B C (c_eq : relation C) (Hc_eq : zb_equiv c_eq)
         (ma : m A) (f : A -> m B) (g : B -> m C),
    eq Hc_eq (bind ma (fun x => bind (f x) g)) (bind (bind ma f) g).
Proof.
unfold bind, ret, eq; intros.
apply (zb_equiv_refl Hc_eq).
Qed.

Definition le A (a_eq a_le : relation A) (Ha_le : zb_order a_eq a_le) x y :=
  a_le x y.

Definition le_order :
  forall A (a_eq a_le : relation A) (Ha_eq : zb_equiv a_eq)
         (Ha_le : zb_order a_eq a_le),
    zb_order (eq Ha_eq) (le Ha_le).
Proof.
constructor.
- unfold le. by apply (zb_order_refl Ha_le).
- unfold le. by apply (zb_order_antisym Ha_le).
- unfold le. by apply (zb_order_trans Ha_le).
Qed.

Lemma le_1 :
  forall A B (a_eq a_le : relation A) (Ha_le : zb_order a_eq a_le)
         x (y : m B) f (Hf : forall v, le Ha_le x (f v)),
    le Ha_le x (bind y f).
Proof. unfold bind. i. apply Hf. Qed.

Lemma le_2 :
  forall A (a_eq a_le : relation A) (Ha_le : zb_order a_eq a_le)
         x f (Hf : forall v, le Ha_le (ret v) (f v)),
    le Ha_le x (bind x f).
Proof. unfold bind. i. apply Hf. Qed.

Lemma le_3 :
  forall A (a_eq a_le : relation A) (Ha_le : zb_order a_eq a_le)
         x f y (Hx : le Ha_le x y)
         (He : forall v (Hv : le Ha_le (ret v) y), le Ha_le (f v) y),
    le Ha_le (bind x f) y.
Proof. unfold bind. i. apply He. apply Hx. Qed.

Lemma bind_mono :
  forall A (a_eq a_le : relation A) (Ha_le : zb_order a_eq a_le)
         B (b_eq b_le : relation B) (Hb_le : zb_order b_eq b_le),
    Proper (le Ha_le ==> (a_le ==> le Hb_le) ==> le Hb_le)
           (bind (A := A) (B := B)).
Proof.
i. intros a1 a2 Ha12 f1 f2 Hf12.
unfold bind. apply Hf12. apply Ha12.
Qed.

Lemma ret_mono :
  forall A (a_eq a_le : relation A) (Ha_le : zb_order a_eq a_le),
    Proper (a_le ==> le Ha_le) (ret (A := A)).
Proof.
i; intros a1 a2 Ha12.
unfold ret. apply Ha12.
Qed.

Lemma ret_join_lub :
  forall A (a_eq a_le : relation A) (Ha_le : zb_order a_eq a_le)
         x y z (Hx : le Ha_le (ret x) z) (Hy : le Ha_le (ret y) z) join
         (Hjoin_lub :
            forall x y z (Hx : a_le x z) (Hy : a_le y z), a_le (join x y) z),
    le Ha_le (ret (join x y)) z.
Proof. i. unfold le, ret. apply Hjoin_lub; [apply Hx|apply Hy]. Qed.

End MId.
