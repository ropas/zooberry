(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** Key constructor: Finite list.  *)

Set Implicit Arguments.

Require Import OrderedType.
Require Import hpattern vgtac.
Require Import VocabA DLat.

Definition size : nat := 6.

Extract Constant size => "try int_of_string (Sys.getenv ""NLISTSIZE"") with _ -> 6".

Module NListKey (A : KEY) <: KEY.

Module F := OrderedTypeFacts (A).

Inductive t' :=
| nil
| cons (hd : A.t) (tl : t').

Definition t := t'.

Fixpoint app l x :=
  match l with
    | nil => cons x nil
    | cons h t => cons h (app t x)
  end.

Inductive eq' : nat -> t -> t -> Prop :=
| eq_zero : forall x1 x2, eq' O x1 x2
| eq_nil : forall s, eq' s nil nil
| eq_cons : forall (hd1 hd2 : A.t) (Hhd: A.eq hd1 hd2)
                   s (tl1 tl2 : t) (Htl: eq' s tl1 tl2),
              eq' (S s) (cons hd1 tl1) (cons hd2 tl2).

Definition eq : t -> t -> Prop := eq' size.

Lemma app_mor' : forall n, Proper (eq' n ==> A.eq ==> eq' n) app.
Proof.
induction 1; intros y1 y2 Hy; s.
- by constructor.
- destruct s; [by constructor|constructor; [by auto|by constructor]].
- constructor; [by auto|by apply IHeq'].
Qed.

Lemma app_mor : Proper (eq ==> A.eq ==> eq) app.
Proof. by apply app_mor'. Qed.

Inductive lt' : nat -> t -> t -> Prop :=
| lt_nil : forall s (hd_x : A.t) (tl_x : t) (Hs : s <> O),
             lt' s nil (cons hd_x tl_x)
| lt_cons1 : forall (hd1 hd2 : A.t) (Hhd : A.eq hd1 hd2)
                    s (tl1 tl2 : t) (Htl : lt' s tl1 tl2),
               lt' (S s) (cons hd1 tl1) (cons hd2 tl2)
| lt_cons2 : forall s (hd1 hd2 : A.t) (Hhd : A.lt hd1 hd2)
                    (tl1 tl2 : t),
               lt' (S s) (cons hd1 tl1) (cons hd2 tl2).

Definition lt : t -> t -> Prop := lt' size.

Lemma eq'_refl : forall (x : t) s, eq' s x x.
Proof.
induction x; [by econs|].
destruct s; econs; [apply A.eq_refl|apply IHx].
Qed.

Lemma eq_refl : forall x : t, eq x x.
Proof. i; apply eq'_refl. Qed.

Lemma eq_sym : forall x y : t, eq x y -> eq y x.
Proof.
unfold eq. induction 1; [by econs|by econs|].
econs; auto.
Qed.

Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
Proof.
unfold eq. i; depgen z; induction H; [econs|inversion 1; by econs|].
inversion 1; subst; econs; [by eauto using A.eq_trans|].
by apply IHeq'.
Qed.

Definition zb_eq : zb_equiv eq :=
  {| zb_equiv_refl := eq_refl
   ; zb_equiv_sym := eq_sym
   ; zb_equiv_trans := eq_trans |}.

Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
Proof.
unfold lt. i; depgen z; induction H; [inversion 1; by econs| |].
+ inversion 1; subst.
  - apply lt_cons1; [eauto using A.eq_trans|]; by apply IHlt'.
  - apply lt_cons2; by eauto using F.lt_eq.
+ inversion 1; subst.
  - apply lt_cons2; by eauto using F.eq_lt.
  - apply lt_cons2; by eauto using A.lt_trans.
Qed.

Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
Proof.
unfold lt, eq. induction 1; inversion 1; [congruence|tauto|].
subst; eapply A.lt_not_eq; eauto.
Qed.

Fixpoint compare' s (x y : t) : Compare (lt' s) (eq' s) x y :=
  match s with
    | O => EQ (eq_zero x y)
    | S s' =>
      match x, y with
        | nil, nil => EQ (eq_nil (S s'))
        | nil, cons ty y' => LT (lt_nil ty y' (not_eq_sym (O_S s')))
        | cons tx x', nil => GT (lt_nil tx x' (not_eq_sym (O_S s')))
        | cons tx x', cons ty y' =>
          match A.compare tx ty with
            | LT l => LT (lt_cons2 s' l x' y')
            | EQ e =>
              match compare' s' x' y' with
                | LT l => LT (lt_cons1 e l)
                | EQ e0 => EQ (eq_cons e e0)
                | GT l => GT (lt_cons1 (A.eq_sym e) l)
              end
            | GT l => GT (lt_cons2 s' l y' x')
          end
      end
  end.
    
Definition compare (x y : t) : Compare lt eq x y := compare' size x y.
  
Fixpoint eq_dec' s (x y : t) : {eq' s x y} + {~ eq' s x y}.
refine
  match s with
    | O => left (eq_zero x y)
    | S s' =>
      match x, y with
        | nil, nil => left _
        | cons hd1 tl1, cons hd2 tl2 =>
          match A.eq_dec hd1 hd2 with
            | left _ =>
              match eq_dec' s' tl1 tl2 with
                | left _ => left _
                | right _ => right _
              end
            | right _ => right _
          end
        | _, _ => right _
      end
  end; try (by inversion 1).
- apply eq_nil.
- apply eq_cons; auto.
Qed.

Definition eq_dec (x y : t) : {eq x y} + {~ eq x y}.
refine
  ((if physical_eq x y as c return
       physical_eq x y = c -> {eq x y} + {~ eq x y} then fun Hc => left _
    else fun _ => eq_dec' size x y) Logic.eq_refl).
apply physical_eq_prop in Hc; subst; by apply eq_refl.
Qed.

Definition eqb x y := if eq_dec x y then true else false.

End NListKey.
