(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** Key constructor: List.  *)

Set Implicit Arguments.

Require Import OrderedType.
Require Import hpattern vgtac.
Require Import VocabA DLat.

Module ListKey (A : KEY) <: KEY.

Module F := OrderedTypeFacts (A).

Inductive t' :=
| nil
| cons (hd_x : A.t) (tl_x : t').
Definition t := t'.

Fixpoint app x y :=
  match x with
    | nil => y
    | cons hd_x tl_x => cons hd_x (app tl_x y)
  end.

Inductive eq' : t -> t -> Prop :=
| eq_nil : eq' nil nil
| eq_cons : forall (hd1 hd2 : A.t) (Hhd: A.eq hd1 hd2)
                   (tl1 tl2 : t) (Htl: eq' tl1 tl2),
              eq' (cons hd1 tl1) (cons hd2 tl2).

Definition eq : t -> t -> Prop := eq'.

Inductive lt' : t -> t -> Prop :=
| lt_nil : forall (hd : A.t) (tl : t), lt' nil (cons hd tl)
| lt_cons1 : forall (hd1 hd2 : A.t) (Hhd : A.eq hd1 hd2)
                    (tl1 tl2 : t) (Htl : lt' tl1 tl2),
               lt' (cons hd1 tl1) (cons hd2 tl2)
| lt_cons2 : forall (hd1 hd2 : A.t) (Hhd : A.lt hd1 hd2) (tl1 tl2 : t),
               lt' (cons hd1 tl1) (cons hd2 tl2).

Definition lt : t -> t -> Prop := lt'.

Lemma eq_refl : forall x : t, eq x x.
Proof. induction x; econs; by auto using A.eq_refl. Qed.

Lemma eq_sym : forall x y : t, eq x y -> eq y x.
Proof. induction 1; econs; by eauto using A.eq_sym. Qed.

Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
Proof.
i; depgen z; induction H; [inversion 1; by econs|].
inversion 1; subst; econs; [by eauto using A.eq_trans|].
by apply IHeq'.
Qed.

Definition zb_eq : zb_equiv eq :=
  {| zb_equiv_refl := eq_refl
   ; zb_equiv_sym := eq_sym
   ; zb_equiv_trans := eq_trans |}.

Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
Proof.
i; depgen z; induction H; [inversion 1; by econs| |].
+ inversion 1; subst.
  - apply lt_cons1; [eauto using A.eq_trans|]; by apply IHlt'.
  - apply lt_cons2; by eauto using F.lt_eq.
+ inversion 1; subst.
  - apply lt_cons2; by eauto using F.eq_lt.
  - apply lt_cons2; by eauto using A.lt_trans.
Qed.

Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
Proof.
induction 1; [by inversion 1|by inversion 1|].
inversion 1; subst; eapply A.lt_not_eq; eauto.
Qed.

Fixpoint compare (x y : t) : Compare lt eq x y.
refine  match x, y with
          | nil, nil => EQ eq_nil
          | nil, cons hd_x tl_x => LT (lt_nil hd_x tl_x)
          | cons hd_x tl_x, nil => GT (lt_nil hd_x tl_x)
          | cons hd1 tl1, cons hd2 tl2 =>
            match A.compare hd1 hd2 with
              | LT l => LT (lt_cons2 l tl1 tl2)
              | EQ _ =>
                match compare tl1 tl2 with
                  | LT _ => LT _
                  | EQ _ => EQ _
                  | GT _ => GT _
                end
              | GT l => GT (lt_cons2 l tl2 tl1)
            end
        end.
+ apply lt_cons1; done.
+ apply eq_cons; done.
+ apply lt_cons1; [by apply A.eq_sym|done].
Defined.

Fixpoint eq_dec (x y : t) : {eq x y} + {~ eq x y}.
refine
  ((if physical_eq x y as c return
      physical_eq x y = c -> {eq x y} + {~ eq x y} then fun Hc => left _
   else fun _ =>
          match x, y with
            | nil, nil => left eq_nil
            | cons hd1 tl1, cons hd2 tl2 =>
              match A.eq_dec hd1 hd2 with
                | left _ =>
                  match eq_dec tl1 tl2 with
                    | left _ => left _
                    | right _ => right _
                  end
                | right _ => right _
              end
            | _, _ => right _
          end) Logic.eq_refl); try (by inversion 1).
+ apply physical_eq_prop in Hc; subst; by apply eq_refl.
+ econs; done.
Qed.
Definition eqb x y := if eq_dec x y then true else false.

End ListKey.
