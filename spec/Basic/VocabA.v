(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** Vocabularies *)

Set Implicit Arguments.

Require Import Relations Morphisms.
Require Import Sumbool.
Require List.
Require Import ZArith.
Require Import hpattern vgtac.
Require Import TStr.

Notation "A &&& B" := (sumbool_and _ _ _ _ A B)
                        (at level 80, right associativity) : sumbool.
Notation "A ||| B" := (sumbool_or _ _ _ _ A B)
                        (at level 85, right associativity) : sumbool.
Notation "~~ A" := (sumbool_not _ _ A)
                        (at level 75, right associativity) : sumbool.

Definition default {A : Type} (def : A) (opt_v : option A) : A :=
  match opt_v with
    | Some v => v
    | None => def
  end.

Definition opt_eq {A : Type} (req : relation A) : relation (option A) :=
  fun opt_x opt_y =>
    match opt_x, opt_y with
      | Some x, Some y => req x y
      | None, None => True
      | _, _ => False
    end.

Definition list_fold {A C : Type} (f : A -> C -> C) (l : list A) (acc : C)
           : C :=
  List.fold_left (fun acc x => f x acc) l acc.

Fixpoint list_fold2_def {A B C : Type} (f : A -> B -> C -> C)
         (l1 : list A) (l2 : list B) (acc default : C) : C :=
  match l1, l2 with
    | nil, nil => acc
    | (a :: l1')%list, (b :: l2')%list =>
      list_fold2_def f l1' l2' (f a b acc) default
    | _, _ => default
  end.

Fixpoint list_fold2 {A B C : Type} (f : A -> B -> C -> C)
         (l1 : list A) (l2 : list B) (acc : C) : C :=
  match l1, l2 with
    | nil, nil => acc
    | (a :: l1')%list, (b :: l2')%list =>
      list_fold2 f l1' l2' (f a b acc)
    | _, _ => acc
  end.

Definition nat_eqb x y := if eq_nat_dec x y then true else false.

Definition print {A : Type} (_ : A) : unit := tt.
Extract Constant print => "fun _ -> ()".

Definition print2 {A B : Type} (_ : A) (_ : B) : unit := tt.
Extract Constant print2 => "fun _ _ -> ()".

Definition print_when_false {A B : Type} (print : A -> unit) (print_arg : A)
           (step : B -> bool) (arg : B) : bool := step arg.
Extract Constant print_when_false =>
"fun print print_arg step arg ->
 if step arg then true else (print print_arg; false)".

Definition small_step {A B : Type} (f : A -> B) (arg : A) : B := f arg.

Axiom physical_eq : forall (A : Type) (x y : A), bool.
Extract Constant physical_eq => "( == )".
Axiom physical_eq_prop :
  forall A (x y : A) (Heq : physical_eq x y = true), x = y.
Axiom structural_eq : forall {A : Type} (x y : A), bool.
Extract Constant structural_eq => "( = )".
Axiom structural_eq_prop :
  forall A (x y : A) (Heq : structural_eq x y = true), x = y.
Axiom invalid_arg : forall {A : Type} (msg : string_t), A.
Extract Constant invalid_arg => "invalid_arg".

Definition string_lengthZ s := Z.of_nat (S (String.length s)).

Ltac dest_if_dec :=
match goal with
  | [H : context [if ?x then _ else _] |- _] => destruct x; try by auto
  | [ |- context [if ?x then _ else _] ] => destruct x; try by auto
end.

Ltac dest_if :=
match goal with
  | [H : context [if ?cond then _ else _] |- _] =>
    let cond' := fresh "cond" in
    remember cond as cond'; destruct cond'; try by auto
end.

Ltac dest_bool :=
  repeat match goal with
           | [H: andb _ _ = true |- _] => apply Bool.andb_true_iff in H
         end.

Ltac dest_trivial_match :=
match goal with
  | [H: Some _ = match ?x with None => None | _ => _ end |- _ ] =>
    let cond := fresh "cond" in
    remember x as cond; destruct cond; try by auto
  | [H: match ?x with Some _ => _ | None => False end |- _ ] =>
    let cond := fresh "cond" in
    remember x as cond; destruct cond; try by auto
  | [H: match ?x with Some _ => _ | None => false end = true |- _ ] =>
    let cond := fresh "cond" in
    remember x as cond; destruct cond; try by auto
end.

Definition monotone (C A : Type) le gamma :=
  forall (c: C) (x y: A) (Hx: gamma c x) (Hle: le x y), gamma c y.

Definition c_div (x y : Z) : Z :=
  (if Z_ge_dec x 0 then x / y else (- (-x / y)))%Z.

Lemma c_div_monotone :
  forall l u (Hlu : (l <= u)%Z) x (Hx : (0 <= x)%Z), (c_div l x <= c_div u x)%Z.
Proof.
i. unfold c_div.
destruct (Z_eq_dec x 0); [|assert (0 < x)%Z as Hx'; [omega|]]; subst.
- do 4 rewrite Zdiv_0_r; s.
  destruct (Z_ge_dec l 0); destruct (Z_ge_dec u 0); by auto.
- destruct (Z_ge_dec l 0).
  + destruct (Z_ge_dec u 0); [|omega].
    apply Z_div_le; omega.
  + destruct (Z_ge_dec u 0).
    * apply Z.le_trans with 0%Z.
      { apply Z.opp_le_mono; rewrite Z.opp_involutive; s.
        apply Z_div_pos; omega. }
      { apply Z_div_pos; omega. }
    * apply Z.opp_le_mono. do 2 rewrite Z.opp_involutive.
      apply Z_div_le; omega.
Qed.

Lemma list_fold_mor T (t_eq : T -> T -> Prop) U :
  Proper
    ((@Logic.eq U ==> t_eq ==> t_eq) ==> @Logic.eq (list U) ==> t_eq ==> t_eq)
    list_fold.
Proof.
intros f1 f2 Hf l1 l2 Hl i1 i2 Hi; unfold list_fold; subst.
generalize i1 i2 Hi.
induction l2.
- by auto.
- simpl List.fold_left; i; apply IHl2.
  by apply Hf.
Qed.

Lemma list_fold_mor2 T (t_eq : T -> T -> Prop) U (u_eq : U -> U -> Prop) :
  Proper
    ((u_eq ==> t_eq ==> t_eq) ==> SetoidList.eqlistA u_eq ==> t_eq ==> t_eq)
    list_fold.
Proof.
intros f1 f2 Hf l1 l2 Hl i1 i2 Hi; unfold list_fold; subst.
generalize i1 i2 Hi; clear i1 i2 Hi.
induction Hl.
- i; by s.
- simpl List.fold_left; i. apply IHHl.
  by apply Hf.
Qed.

Lemma list_map_mor T U (t_eq : T -> T -> Prop) (u_eq : U -> U -> Prop) :
  Proper
    ((t_eq ==> u_eq) ==> SetoidList.eqlistA t_eq ==> SetoidList.eqlistA u_eq)
    (@List.map T U).
Proof.
intros f1 f2 Hf l1 l2 Hl.
induction Hl.
- s. by constructor.
- s. constructor; [by apply Hf|by auto].
Qed.
