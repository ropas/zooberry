(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** Lattice constructor: cartesian product.  *)

Set Implicit Arguments.

Require Import OrderedTypeEx Morphisms.
Require Import hpattern vgtac.
Require Import VocabA DLat.

Module ProdKey (A : KEY) (B : KEY) <: KEY.
  Include PairOrderedType A B.
  Definition eqb (x y : t) := if eq_dec x y then true else false.
  Definition zb_eq : zb_equiv eq :=
    {| zb_equiv_refl := eq_refl
     ; zb_equiv_sym := eq_sym
     ; zb_equiv_trans := eq_trans |}.
End ProdKey.

Module Prod (A : LAT) (B : LAT) <: LAT.

Definition t : Type := (A.t * B.t)%type.

(** * Lattice operations *)

Local Open Scope sumbool.

Definition le (x y : t) : Prop := A.le (fst x) (fst y) /\ B.le (snd x) (snd y).

Definition eq (x y : t) : Prop := A.eq (fst x) (fst y) /\ B.eq (snd x) (snd y).

Lemma le_refl : forall (x y : t) (Heq : eq x y), le x y.
Proof. inversion 1; econs; by eauto using A.le_refl, B.le_refl. Qed.
Lemma le_antisym : forall (x y : t) (le1 : le x y) (le2 : le y x), eq x y.
Proof.
  inversion 1; inversion 1; econs; by eauto using A.le_antisym, B.le_antisym.
Qed.
Lemma le_trans : forall (x y z : t) (le1 : le x y) (le2 : le y z), le x z.
Proof.
  inversion 1; inversion 1; econs; by eauto using A.le_trans, B.le_trans.
Qed.

Lemma eq_refl : forall (x : t), eq x x.
Proof. destruct x; econs; by eauto using A.eq_refl, B.eq_refl. Qed.
Lemma eq_sym : forall (x y : t) (Heq : eq x y), eq y x.
Proof. inversion 1; econs; by eauto using A.eq_sym, B.eq_sym. Qed.
Lemma eq_trans :
  forall (x y z : t) (eq1 : eq x y) (eq2 : eq y z), eq x z.
Proof.
  inversion 1; inversion 1; econs; by eauto using A.eq_trans, B.eq_trans.
Qed.

Definition le_dec (x y : t) : {le x y} + {~ le x y}.
refine
  ((if physical_eq x y as c return
       physical_eq x y = c -> {le x y} + {~ le x y} then fun Hc => left _
    else fun _ =>
           match x as x', y as y' return
                 x = x' -> y = y' -> {le x y} + {~ le x y} with
             | (x1, x2), (y1, y2) =>
               fun Hx Hy =>
                 if A.le_dec x1 y1 &&& B.le_dec x2 y2 then left _ else right _
           end Logic.eq_refl Logic.eq_refl) Logic.eq_refl); subst.
+ apply physical_eq_prop in Hc; subst; apply le_refl; by apply eq_refl.
+ des; econs; by vauto.
+ des; inversion 1; by vauto.
Qed.

Definition eq_dec (x y : t) : {eq x y} + {~ eq x y}.
refine
  ((if physical_eq x y as c return
       physical_eq x y = c -> {eq x y} + {~ eq x y} then fun Hc => left _
    else fun _ =>
           match x as x', y as y' return
                 x = x' -> y = y' -> {eq x y} + {~ eq x y} with
             | (x1, x2), (y1, y2) =>
               fun Hx Hy =>
                 if A.eq_dec x1 y1 &&& B.eq_dec x2 y2 then left _ else right _
           end Logic.eq_refl Logic.eq_refl) Logic.eq_refl); subst.
+ apply physical_eq_prop in Hc; subst; by apply eq_refl.
+ des; econs; by vauto.
+ des; inversion 1; by vauto.
Qed.

Definition bot : t := (A.bot, B.bot).

Lemma bot_prop : forall (x : t), le bot x.
Proof. i; split; auto using A.bot_prop, B.bot_prop. Qed.

Definition join (x y : t) : t :=
  if le_dec x y then y else
  if le_dec y x then x else
  (A.join (fst x) (fst y), B.join (snd x) (snd y)).

Lemma join_left : forall (x y : t), le x (join x y).
Proof.
  intros;unfold join.
  destruct (le_dec x y);auto.
  destruct (le_dec y x);[apply le_refl;apply eq_refl|].
  unfold le. simpl. split; [apply A.join_left|apply B.join_left].
Qed.

Lemma join_right : forall (x y : t), le y (join x y).
Proof.
  intros;unfold join.
  destruct (le_dec x y);[apply le_refl;apply eq_refl|].
  destruct (le_dec y x);auto.
  unfold le. simpl. split; [apply A.join_right|apply B.join_right].
Qed.

Lemma join_lub : forall (x y u : t) (Hx : le x u) (Hy : le y u), le (join x y) u.
Proof.
  unfold join, le; i; repeat dest_if_dec.
  destruct x, y, u; s.
  split; hdes; auto using A.join_lub, B.join_lub.
Qed.

Definition meet (x y : t) : t :=
  if le_dec x y then x else
  if le_dec y x then y else
    (A.meet (fst x) (fst y), B.meet (snd x) (snd y)).

Lemma meet_left : forall (x y : t), le (meet x y) x.
Proof.
  intros;unfold meet.
  destruct (le_dec x y);[apply le_refl;apply eq_refl|].
  destruct (le_dec y x);auto.
  unfold le. simpl. split; [apply A.meet_left|apply B.meet_left].
Qed.

Lemma meet_right : forall (x y : t), le (meet x y) y.
Proof.
  intros;unfold meet.
  destruct (le_dec x y);auto.
  destruct (le_dec y x);[apply le_refl;apply eq_refl|].
  unfold le. simpl. split; [apply A.meet_right|apply B.meet_right].
Qed.

Lemma meet_glb : forall (x y l : t) (Hx : le l x) (Hy : le l y), le l (meet x y).
Proof.
  unfold meet, le; i; repeat dest_if_dec.
  destruct x, y, l; s.
  split; hdes; auto using A.meet_glb, B.meet_glb.
Qed.

Definition widen (x y : t) : t :=
  if structural_eq x y then x else
  (A.widen (fst x) (fst y), B.widen (snd x) (snd y)).

Definition narrow (x y : t) : t :=
  if structural_eq x y then x else
  (A.narrow (fst x) (fst y), B.narrow (snd x) (snd y)).

Include JoinMeetProp.

End Prod.

(** Modules for generating lookup functions. *)

Module Get2.
  Definition fst {A B : Type} : A * B -> A :=
    Datatypes.fst.
  Definition snd {A B : Type} : A * B -> B :=
    Datatypes.snd.
End Get2.
Module Get3.
  Definition fst {A B C : Type} : A * B * C -> A :=
    Get2.fst <*> Datatypes.fst.
  Definition snd {A B C : Type} : A * B * C -> B :=
    Get2.snd <*> Datatypes.fst.
  Definition thrd {A B C : Type} : A * B * C -> C :=
    Datatypes.snd.
End Get3.
Module Get4.
  Definition fst {A B C D : Type} : A * B * C * D -> A :=
    Get3.fst <*> Datatypes.fst.
  Definition snd {A B C D : Type} : A * B * C * D -> B :=
    Get3.snd <*> Datatypes.fst.
  Definition thrd {A B C D : Type} : A * B * C * D -> C :=
    Get3.thrd <*> Datatypes.fst.
  Definition frth {A B C D : Type} : A * B * C * D -> D :=
    Datatypes.snd.
End Get4.
Module Get5.
  Definition fst {A B C D E : Type} : A * B * C * D * E -> A :=
    Get4.fst <*> Datatypes.fst.
  Definition snd {A B C D E : Type} : A * B * C * D * E -> B :=
    Get4.snd <*> Datatypes.fst.
  Definition thrd {A B C D E : Type} : A * B * C * D * E -> C :=
    Get4.thrd <*> Datatypes.fst.
  Definition frth {A B C D E : Type} : A * B * C * D * E -> D :=
    Get4.frth <*> Datatypes.fst.
  Definition fifth {A B C D E : Type} : A * B * C * D * E -> E :=
    Datatypes.snd.
End Get5.

(** * Cartesian product for multiple lattices *)

Module ProdKey2 (A:KEY) (B:KEY).
  Include ProdKey A B.
  Include Get2.

  Lemma fst_mor : Proper (eq ==> A.eq) fst.
  Proof. unfold eq; intros [x1 y1] [x2 y2] [Hfst Hsnd]; by auto. Qed.
  Lemma snd_mor : Proper (eq ==> B.eq) snd.
  Proof. unfold eq; intros [x1 y1] [x2 y2] [Hfst Hsnd]; by auto. Qed.
End ProdKey2.

Module ProdKey3 (A:KEY) (B:KEY) (C:KEY).
  Module E2 := ProdKey A B.
  Include ProdKey E2 C.
  Include Get3.

  Lemma fst_mor : Proper (eq ==> A.eq) fst.
  Proof.
    unfold eq; intros [[x1 y1] z1] [[x2 y2] z2] [[Hfst Hsnd] Hthrd]. by auto.
  Qed.
  Lemma snd_mor : Proper (eq ==> B.eq) snd.
  Proof.
    unfold eq; intros [[x1 y1] z1] [[x2 y2] z2] [[Hfst Hsnd] Hthrd]. by auto.
  Qed.
  Lemma thrd_mor : Proper (eq ==> C.eq) thrd.
  Proof.
    unfold eq; intros [[x1 y1] z1] [[x2 y2] z2] [[Hfst Hsnd] Hthrd]. by auto.
  Qed.
End ProdKey3.

Module ProdKey4 (A:KEY) (B:KEY) (C:KEY) (D:KEY).
  Module E2 := ProdKey A B.
  Module E3 := ProdKey E2 C.
  Include ProdKey E3 D.
  Include Get4.

  Lemma fst_mor : Proper (eq ==> A.eq) fst.
  Proof.
    unfold eq; intros [[[x1 y1] z1] a1] [[[x2 y2] z2] a2] [[[Hfst Hsnd] Hthrd] Hfrth]. by auto.
  Qed.
  Lemma snd_mor : Proper (eq ==> B.eq) snd.
  Proof.
    unfold eq; intros [[[x1 y1] z1] a1] [[[x2 y2] z2] a2] [[[Hfst Hsnd] Hthrd] Hfrth]. by auto.
  Qed.
  Lemma thrd_mor : Proper (eq ==> C.eq) thrd.
  Proof.
    unfold eq; intros [[[x1 y1] z1] a1] [[[x2 y2] z2] a2] [[[Hfst Hsnd] Hthrd] Hfrth]. by auto.
  Qed.
  Lemma frth_mor : Proper (eq ==> D.eq) frth.
  Proof.
    unfold eq; intros [[[x1 y1] z1] a1] [[[x2 y2] z2] a2] [[[Hfst Hsnd] Hthrd] Hfrth]. by auto.
  Qed.
End ProdKey4.

Module ProdKey5 (A:KEY) (B:KEY) (C:KEY) (D:KEY) (E:KEY).
  Module E2 := ProdKey A B.
  Module E3 := ProdKey E2 C.
  Module E4 := ProdKey E3 D.
  Include ProdKey E4 E.
  Include Get5.

  Lemma fst_mor : Proper (eq ==> A.eq) fst.
  Proof.
    unfold eq; intros [[[[x1 y1] z1] a1] b1] [[[[x2 y2] z2] a2] b2] [[[[Hfst Hsnd] Hthrd] Hfrth] Hfifth]. by auto.
  Qed.
  Lemma snd_mor : Proper (eq ==> B.eq) snd.
  Proof.
    unfold eq; intros [[[[x1 y1] z1] a1] b1] [[[[x2 y2] z2] a2] b2] [[[[Hfst Hsnd] Hthrd] Hfrth] Hfifth]. by auto.
  Qed.
  Lemma thrd_mor : Proper (eq ==> C.eq) thrd.
  Proof.
    unfold eq; intros [[[[x1 y1] z1] a1] b1] [[[[x2 y2] z2] a2] b2] [[[[Hfst Hsnd] Hthrd] Hfrth] Hfifth]. by auto.
  Qed.
  Lemma frth_mor : Proper (eq ==> D.eq) frth.
  Proof.
    unfold eq; intros [[[[x1 y1] z1] a1] b1] [[[[x2 y2] z2] a2] b2] [[[[Hfst Hsnd] Hthrd] Hfrth] Hfifth]. by auto.
  Qed.
  Lemma fifth_mor : Proper (eq ==> E.eq) fifth.
  Proof.
    unfold eq; intros [[[[x1 y1] z1] a1] b1] [[[[x2 y2] z2] a2] b2] [[[[Hfst Hsnd] Hthrd] Hfrth] Hfifth]. by auto.
  Qed.
End ProdKey5.

Module Prod2 (A:LAT) (B:LAT).
  Include Prod A B.
  Include Get2.

  Lemma fst_mor : Proper (eq ==> A.eq) fst.
  Proof. unfold eq; intros [x1 y1] [x2 y2] [Hfst Hsnd]; by auto. Qed.
  Lemma snd_mor : Proper (eq ==> B.eq) snd.
  Proof. unfold eq; intros [x1 y1] [x2 y2] [Hfst Hsnd]; by auto. Qed.
End Prod2.

Module Prod3 (A:LAT) (B:LAT) (C:LAT).
  Module E2 := Prod A B.
  Include Prod E2 C.
  Include Get3.

  Lemma fst_mor : Proper (eq ==> A.eq) fst.
  Proof.
    unfold eq; intros [[x1 y1] z1] [[x2 y2] z2] [[Hfst Hsnd] Hthrd]. by auto.
  Qed.
  Lemma snd_mor : Proper (eq ==> B.eq) snd.
  Proof.
    unfold eq; intros [[x1 y1] z1] [[x2 y2] z2] [[Hfst Hsnd] Hthrd]. by auto.
  Qed.
  Lemma thrd_mor : Proper (eq ==> C.eq) thrd.
  Proof.
    unfold eq; intros [[x1 y1] z1] [[x2 y2] z2] [[Hfst Hsnd] Hthrd]. by auto.
  Qed.
End Prod3.

Module Prod4 (A:LAT) (B:LAT) (C:LAT) (D:LAT).
  Module E2 := Prod A B.
  Module E3 := Prod E2 C.
  Include Prod E3 D.
  Include Get4.

  Lemma fst_mor : Proper (eq ==> A.eq) fst.
  Proof.
    unfold eq; intros [[[x1 y1] z1] a1] [[[x2 y2] z2] a2] [[[Hfst Hsnd] Hthrd] Hfrth]. by auto.
  Qed.
  Lemma snd_mor : Proper (eq ==> B.eq) snd.
  Proof.
    unfold eq; intros [[[x1 y1] z1] a1] [[[x2 y2] z2] a2] [[[Hfst Hsnd] Hthrd] Hfrth]. by auto.
  Qed.
  Lemma thrd_mor : Proper (eq ==> C.eq) thrd.
  Proof.
    unfold eq; intros [[[x1 y1] z1] a1] [[[x2 y2] z2] a2] [[[Hfst Hsnd] Hthrd] Hfrth]. by auto.
  Qed.
  Lemma frth_mor : Proper (eq ==> D.eq) frth.
  Proof.
    unfold eq; intros [[[x1 y1] z1] a1] [[[x2 y2] z2] a2] [[[Hfst Hsnd] Hthrd] Hfrth]. by auto.
  Qed.
End Prod4.

Module Prod5 (A:LAT) (B:LAT) (C:LAT) (D:LAT) (E:LAT).
  Module E2 := Prod A B.
  Module E3 := Prod E2 C.
  Module E4 := Prod E3 D.
  Include Prod E4 E.
  Include Get5.

  Lemma fst_mor : Proper (eq ==> A.eq) fst.
  Proof.
    unfold eq; intros [[[[x1 y1] z1] a1] b1] [[[[x2 y2] z2] a2] b2] [[[[Hfst Hsnd] Hthrd] Hfrth] Hfifth]. by auto.
  Qed.
  Lemma snd_mor : Proper (eq ==> B.eq) snd.
  Proof.
    unfold eq; intros [[[[x1 y1] z1] a1] b1] [[[[x2 y2] z2] a2] b2] [[[[Hfst Hsnd] Hthrd] Hfrth] Hfifth]. by auto.
  Qed.
  Lemma thrd_mor : Proper (eq ==> C.eq) thrd.
  Proof.
    unfold eq; intros [[[[x1 y1] z1] a1] b1] [[[[x2 y2] z2] a2] b2] [[[[Hfst Hsnd] Hthrd] Hfrth] Hfifth]. by auto.
  Qed.
  Lemma frth_mor : Proper (eq ==> D.eq) frth.
  Proof.
    unfold eq; intros [[[[x1 y1] z1] a1] b1] [[[[x2 y2] z2] a2] b2] [[[[Hfst Hsnd] Hthrd] Hfrth] Hfifth]. by auto.
  Qed.
  Lemma fifth_mor : Proper (eq ==> E.eq) fifth.
  Proof.
    unfold eq; intros [[[[x1 y1] z1] a1] b1] [[[[x2 y2] z2] a2] b2] [[[[Hfst Hsnd] Hthrd] Hfrth] Hfifth]. by auto.
  Qed.
End Prod5.
