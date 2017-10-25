(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** * Intra Node of Program.  *)

Set Implicit Arguments.

Require Import ZArith OrderedType OrderedTypeEx.
Require Import hpattern vgtac.
Require Import VocabA DFSetAVL DFMapAVL TStr.
Require Import Syn.

Local Open Scope bool.

Inductive t' :=
| Entry
| Exit
| Node (i : Z).

Definition t : Type := t'.

Inductive eq' : t -> t -> Prop :=
| eq_entry : eq' Entry Entry
| eq_exit : eq' Exit Exit
| eq_node : forall i, eq' (Node i) (Node i).

Definition eq : t -> t -> Prop := eq'.

Inductive lt' : t -> t -> Prop :=
| lt_entry_exit : lt' Entry Exit
| lt_entry : forall (i : Z), lt' Entry (Node i)
| lt_exit : forall (i : Z), lt' (Node i) Exit
| lt_node : forall (i j : Z) (Hlt : (i < j)%Z), lt' (Node i) (Node j).

Definition lt : t -> t -> Prop := lt'.

Lemma eq_refl : forall x : t, eq x x.
Proof. destruct x; by econs. Qed.
Lemma eq_sym : forall x y : t, eq x y -> eq y x.
Proof. inversion 1; by econs. Qed.
Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
Proof. inversion 1; inversion 1; by econs. Qed.

Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
Proof. inversion 1; inversion 1; econs; omega. Qed.
Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
Proof. inversion 1; inversion 1; omega. Qed.

Definition compare (x y : t) : Compare lt eq x y.
  refine match x, y with
           | Entry, Entry => EQ _
           | Exit, Exit => EQ _
           | Entry, _ => LT _
           | _, Entry => GT _
           | _, Exit => LT _
           | Exit, _ => GT _
           | Node i, Node j =>
             match Z.compare i j as ij return
                   Z.compare i j = ij -> Compare lt eq (Node i) (Node j) with
               | Datatypes.Eq => fun Hij => EQ _
               | Datatypes.Lt => fun Hij => LT _
               | Datatypes.Gt => fun Hij => GT _
             end Logic.eq_refl
         end; try econs.
  + apply Z.compare_eq_iff in Hij; subst; vauto.
  + apply Z.compare_lt_iff in Hij; subst; vauto.
  + apply Z.compare_gt_iff in Hij; subst; vauto.
Defined.

Definition eq_dec (x y : t) : {eq x y} + {~ eq x y}.
Proof.
  refine ((if physical_eq x y as c return
              physical_eq x y = c -> {eq x y} + {~ eq x y} then
             fun Hc => left _
           else
             fun _ =>
               match x, y with
                 | Entry, Entry => left _
                 | Exit, Exit => left _
                 | Node i, Node j =>
                   match Z_eq_dec i j with
                     | left _ => left _
                     | right _ => right _
                   end
                 | _, _ => right _
               end) Logic.eq_refl)
  ; subst; try econs; try inversion 1; try tauto.
  + apply physical_eq_prop in Hc; subst; by apply eq_refl.
Defined.

Definition eqb x y := if eq_dec x y then true else false.

Definition is_entry_node (node : t) : bool :=
  if eq_dec node Entry then true else false.

Definition is_exit_node (node : t) : bool :=
  if eq_dec node Exit then true else false.
