(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** Lattice constructor: sum.  *)

Set Implicit Arguments.

Require Import OrderedType.
Require Import hpattern vgtac.
Require Import VocabA DLat.
Require Import TStr. 

Axiom sum_narrow_msg : string_t.
Extract Constant sum_narrow_msg => """narrow small big""".

Module SumKey (A : KEY) (B : KEY) <: KEY.

Inductive t' :=
| Inl (a : A.t)
| Inr (b : B.t).
Definition t := t'.

Inductive eq' : t -> t -> Prop :=
| eq_inl : forall (x' y' : A.t) (Heq: A.eq x' y'), eq' (Inl x') (Inl y')
| eq_inr : forall (x' y' : B.t) (Heq: B.eq x' y'), eq' (Inr x') (Inr y').

Definition eq : t -> t -> Prop := eq'.

Inductive lt' : t -> t -> Prop :=
| lt_inl : forall (x' y' : A.t) (Hlt: A.lt x' y'), lt' (Inl x') (Inl y')
| lt_inlr : forall (x' : A.t) (y' : B.t), lt' (Inl x') (Inr y')
| lt_inr : forall (x' y' : B.t) (Hlt: B.lt x' y'), lt' (Inr x') (Inr y').

Definition lt : t -> t -> Prop := lt'.

Lemma eq_refl : forall x : t, eq x x.
Proof. destruct x; econs; auto. Qed.
Lemma eq_sym : forall x y : t, eq x y -> eq y x.
Proof. inversion 1; econs; auto. Qed.
Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
Proof. inversion 1; inversion 1; econs; eauto. Qed.

Definition zb_eq : zb_equiv eq :=
  {| zb_equiv_refl := eq_refl
   ; zb_equiv_sym := eq_sym
   ; zb_equiv_trans := eq_trans |}.

Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
Proof. inversion 1; inversion 1; econs; eauto. Qed.
Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
Proof.
inversion 1; inversion 1; [eapply A.lt_not_eq|eapply B.lt_not_eq]; eauto.
Qed.

Definition compare (x y : t) : Compare lt eq x y :=
  match x, y with
    | Inl x', Inl y' =>
      match A.compare x' y' with
        | LT l => LT (lt_inl l)
        | EQ l => EQ (eq_inl l)
        | GT l => GT (lt_inl l)
      end
    | Inl x', Inr y' => LT (lt_inlr x' y')
    | Inr x', Inl y' => GT (lt_inlr y' x')
    | Inr x', Inr y' =>
      match B.compare x' y' with
        | LT l => LT (lt_inr l)
        | EQ l => EQ (eq_inr l)
        | GT l => GT (lt_inr l)
      end
  end.

Definition eq_dec (x y : t) : {eq x y} + {~ eq x y}.
refine match x, y with
         | Inl x', Inl y' =>
           match A.eq_dec x' y' with
             | left e => left (eq_inl e)
             | right _ => right _
           end
         | Inr x', Inr y' =>
           match B.eq_dec x' y' with
             | left e => left (eq_inr e)
             | right _ => right _
           end
         | _, _ => right _
       end; i; inv FH.
Qed.
Definition eqb x y := if eq_dec x y then true else false.

End SumKey.

Module Sum (A : LAT) (B : LAT) <: LAT.

Inductive t' :=
| Top
| Inl (a : A.t)
| Inr (b : B.t)
| Bot.

Definition t := t'.

Inductive le' : t -> t -> Prop :=
| le_top : forall (x : t), le' x Top
| le_bot : forall (x : t), le' Bot x
| le_inl : forall (x y : A.t) (Hle : A.le x y), le' (Inl x) (Inl y)
| le_inr : forall (x y : B.t) (Hle : B.le x y), le' (Inr x) (Inr y).

Definition le : t -> t -> Prop := le'.

Inductive eq' : t -> t -> Prop :=
| eq_top : eq' Top Top
| eq_bot : eq' Bot Bot
| eq_inl : forall (x y : A.t) (Heq : A.eq x y), eq' (Inl x) (Inl y)
| eq_inr : forall (x y : B.t) (Heq : B.eq x y), eq' (Inr x) (Inr y).

Definition eq : t -> t -> Prop := eq'.

Lemma le_refl : forall x y : t, eq x y -> le x y.
Proof. inversion 1; econs; auto using A.le_refl, B.le_refl. Qed.
Lemma le_antisym : forall x y : t, le x y -> le y x -> eq x y.
Proof.
inversion 1; inversion 1; econs; auto using A.le_antisym, B.le_antisym.
Qed.
Lemma le_trans : forall x y z : t, le x y -> le y z -> le x z.
Proof.
inversion 1; inversion 1; econs; eauto using A.le_trans, B.le_trans.
Qed.

Lemma eq_refl : forall x : t, eq x x.
Proof. destruct x; econs; auto using A.eq_refl, B.eq_refl. Qed.
Lemma eq_sym : forall x y : t, eq x y -> eq y x.
Proof. inversion 1; econs; auto using A.eq_sym, B.eq_sym. Qed.
Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
Proof.
inversion 1; inversion 1; econs; eauto using A.eq_trans, B.eq_trans.
Qed.

Definition le_dec (x y : t) : {le x y} + {~ le x y}.
refine
  ((if physical_eq x y as c return
       physical_eq x y = c -> {le x y} + {~ le x y} then fun Hc => left _
    else fun _ =>
           match x, y with
             | _, Top => left (le_top _)
             | Bot, _ => left (le_bot _)
             | Inl x', Inl y' =>
               match A.le_dec x' y' with
                 | left l => left (le_inl l)
                 | right _ => right _
               end
             | Inr x', Inr y' =>
               match B.le_dec x' y' with
                 | left l => left (le_inr l)
                 | right _ => right _
               end
             | _, _ => right _
           end) Logic.eq_refl); try (inversion 1; tauto).
+ apply physical_eq_prop in Hc; subst; apply le_refl; by apply eq_refl.
Qed.

Definition eq_dec (x y : t) : {eq x y} + {~ eq x y}.
refine
  ((if physical_eq x y as c return
       physical_eq x y = c -> {eq x y} + {~ eq x y} then fun Hc => left _
    else fun _ =>
           match x, y with
             | Top, Top => left eq_top
             | Bot, Bot => left eq_bot
             | Inl x', Inl y' =>
               match A.eq_dec x' y' with
                 | left l => left (eq_inl l)
                 | right _ => right _
               end
             | Inr x', Inr y' =>
               match B.eq_dec x' y' with
                 | left l => left (eq_inr l)
                 | right _ => right _
               end
             | _, _ => right _
           end) Logic.eq_refl); try (inversion 1; tauto).
+ apply physical_eq_prop in Hc; subst; by apply eq_refl.
Qed.

Definition top : t := Top.
Definition bot : t := Bot.
Lemma top_prop : forall x : t, le x top.
Proof. by econs. Qed.
Lemma bot_prop : forall x : t, le bot x.
Proof. by econs. Qed.

Definition join (x y : t) : t :=
  match x, y with
    | Top, _
    | _, Top => Top
    | Bot, a
    | a, Bot => a
    | Inl x', Inl y' => Inl (A.join x' y')
    | Inr x', Inr y' => Inr (B.join x' y')
    | _, _ => Top
  end.

Lemma join_left : forall (x y : t), le x (join x y).
Proof.
  i; unfold join ; destruct x, y
  ; try apply top_prop; try apply bot_prop
  ; try (apply le_refl; apply eq_refl)
  ; constructor; auto using A.join_left, B.join_left.
Qed.

Lemma join_right : forall (x y : t), le y (join x y).
Proof.
  i; unfold join ; destruct x, y
  ; try apply top_prop; try apply bot_prop
  ; try (apply le_refl; apply eq_refl)
  ; constructor; auto using A.join_right, B.join_right.
Qed.

Lemma join_lub : forall (x y u : t) (Hx : le x u) (Hy : le y u), le (join x y) u.
Proof.
  destruct x, y, u; intros H1 H2; unfold join
  ; try (apply le_refl; apply eq_refl)
  ; try (apply bot_prop); try (apply top_prop)
  ; try inversion H1; try inversion H2
  ; try (constructor; by auto using A.join_lub, B.join_lub).
Qed.

Definition meet (x y : t) : t :=
  match x, y with
    | Top, a
    | a, Top => a
    | Bot, _
    | _, Bot => Bot
    | Inl x', Inl y' => Inl (A.meet x' y')
    | Inr x', Inr y' => Inr (B.meet x' y')
    | _, _ => Bot
  end.

Lemma meet_left : forall (x y : t), le (meet x y) x.
Proof.
  intros. unfold meet.
  destruct x,y; 
  try (apply le_refl;apply eq_refl);try (apply bot_prop);
  try (apply top_prop).
  apply le_inl; apply A.meet_left.
  apply le_inr; apply B.meet_left.
Qed.

Lemma meet_right : forall (x y : t), le (meet x y) y.
Proof.
  intros. unfold meet.
  destruct x,y; try (apply le_refl;apply eq_refl);try (apply bot_prop);
  try (apply top_prop).
  apply le_inl; apply A.meet_right.
  apply le_inr; apply B.meet_right.
Qed.

Lemma meet_glb : forall (x y l : t) (Hx : le l x) (Hy : le l y), le l (meet x y).
Proof.
  destruct x, y, l; intros H1 H2; unfold meet 
  ; try (apply le_refl; apply eq_refl)
  ; try (apply bot_prop); try (apply top_prop)
  ; try inversion H1; try inversion H2
  ; try (constructor; by auto using A.meet_glb, B.meet_glb).
Qed.

Definition widen (x y : t) : t :=
  match x, y with
    | _, Top
    | Top, _ => Top
    | Bot, a
    | a, Bot => a
    | Inl a, Inl b => Inl (A.widen a b)
    | Inr a, Inr b => Inr (B.widen a b)
    | _, _ => Top
  end.

Definition narrow (x y : t) : t :=
  if structural_eq x y then x else
  match x, y with
    | Top, a => a
    | _, Bot => Bot
    | Inl a, Inl b => Inl (A.narrow a b)
    | Inr a, Inr b => Inr (B.narrow a b)
    | _, _ => invalid_arg sum_narrow_msg
  end.

Include JoinMeetProp.

End Sum.

(** * Sum for multiple lattices *)

Module SumKey2 (A:KEY) (B:KEY).
  Include SumKey A B.
End SumKey2.

Module SumKey3 (A:KEY) (B:KEY) (C:KEY).
  Module E2 := SumKey A B.
  Include SumKey E2 C.
End SumKey3.

Module SumKey4 (A:KEY) (B:KEY) (C:KEY) (D:KEY).
  Module E2 := SumKey A B.
  Module E3 := SumKey E2 C.
  Include SumKey E3 D.
End SumKey4.

Module SumKey5 (A:KEY) (B:KEY) (C:KEY) (D:KEY) (E:KEY).
  Module E2 := SumKey A B.
  Module E3 := SumKey E2 C.
  Module E4 := SumKey E3 D.
  Include SumKey E4 E.
End SumKey5.

Module Sum2 (A:LAT) (B:LAT).
  Include Sum A B.
End Sum2.

Module Sum3 (A:LAT) (B:LAT) (C:LAT).
  Module E2 := Sum A B.
  Include Sum E2 C.
End Sum3.

Module Sum4 (A:LAT) (B:LAT) (C:LAT) (D:LAT).
  Module E2 := Sum A B.
  Module E3 := Sum E2 C.
  Include Sum E3 D.
End Sum4.

Module Sum5 (A:LAT) (B:LAT) (C:LAT) (D:LAT) (E:LAT).
  Module E2 := Sum A B.
  Module E3 := Sum E2 C.
  Module E4 := Sum E3 D.
  Include Sum E4 E.
End Sum5.
