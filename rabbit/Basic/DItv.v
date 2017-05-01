(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(* Interval lattice *)

Set Implicit Arguments.

Require Import Morphisms ZArith.
Require Import hpattern vgtac.
Require Import TStr VocabA DLat.

Delimit Scope interval_scope with itv.

Module Itv <: LAT.

Definition not_and1 : forall (A B : Prop), ~ A -> ~ (A /\ B). Proof. tauto. Qed.
Definition not_and2 : forall (A B : Prop), ~ B -> ~ (A /\ B). Proof. tauto. Qed.

(* Widening threshold. *)

Definition threshold : list Z := [0; 64]%Z.

(* Auxiliary type [t'] (integer + [+oo] + [-oo]) *)

Inductive t' :=
  | Int (i : Z)
  | PInf
  | MInf.

Definition opp' (x : t') :=
  match x with
  | Int i => Int (Z.opp i)
  | PInf => MInf
  | MInf => PInf
  end.

Inductive le' : t' -> t' -> Prop :=
| le'_minf : forall (x : t'), le' MInf x
| le'_pinf : forall (x : t'), le' x PInf
| le'_int : forall (i j : Z) (Z_le : (i <= j)%Z), le' (Int i) (Int j).

Definition le'_dec (x y : t') : {le' x y} + {~ le' x y}.
refine (match x, y with
          | MInf, y => left (le'_minf y)
          | x, PInf => left (le'_pinf x)
          | Int i, Int j =>
            match Z_le_dec i j with
              | left H => left (le'_int H)
              | right H => right _
            end
          | _, _ => right _
        end); (inversion 1; done).
Qed.

Definition eq' : t' -> t' -> Prop := eq.

Definition eq'_dec (x y : t') : {eq' x y} + {~ eq' x y}.
refine (match x, y with
          | MInf, MInf => left _
          | PInf, PInf => left _
          | Int i, Int j =>
            match Z_eq_dec i j with
              | left H => left _
              | right H => right _
            end
          | _, _ => right _
        end); try (inversion 1; done).
- by subst.
- by auto.
- by auto.
Qed.

Lemma le'_refl : forall (x y : t') (Heq : eq' x y), le' x y.
Proof.
i. rewrite Heq. destruct y.
- apply le'_int; omega.
- by apply le'_pinf.
- by apply le'_minf.
Qed.

Lemma le'_antisym :
  forall (x y : t') (le1 : le' x y) (le2 : le' y x), eq' x y.
Proof.
destruct 1; inversion 1.
- by auto.
- by auto.
- assert (i = j); [omega|by subst].
Qed.

Lemma le'_trans :
  forall (x y z : t') (le1 : le' x y) (le2 : le' y z), le' x z.
Proof. destruct 1; inversion 1; auto using le'. apply le'_int; omega. Qed.

Lemma le'_neg : forall x y (Hle : ~ le' x y), le' y x.
Proof.
destruct x, y; try constructor.
- destruct (Z_le_dec i i0); [elim Hle; by constructor|omega].
- i. elim Hle; by constructor.
- i. elim Hle; by constructor.
- i. elim Hle; by constructor.
Qed.

Ltac le'_auto :=
repeat match goal with
         | |- context [le'_dec ?x ?y] => destruct (le'_dec x y)
         | |- le' _ _ => econs; omega
         | H : ~ le' _ _ |- _ => elim H; econs; omega
         | H : le' _ _ |- _ => by inv H
         | |- _ => done
       end.

Lemma eq'_refl : forall (x : t'), eq' x x.
Proof. i; by apply eq_refl. Qed.

Lemma eq'_sym : forall (x y : t') (Heq : eq' x y), eq' y x.
Proof. i. by rewrite Heq. Qed.

Lemma eq'_trans :
  forall (x y z : t') (eq1 : eq' x y) (eq2 : eq' y z), eq' x z.
Proof. i. by rewrite eq1, eq2. Qed.

Lemma le'_mor : Proper (eq' ==> eq' ==> Basics.impl) le'.
Proof.
intros x1 x2 Hx y1 y2 Hy Hle.
eapply le'_trans; [by apply le'_refl, eq'_sym, Hx|].
eapply le'_trans; [by apply Hle|].
by apply le'_refl.
Qed.

Ltac eq'_auto :=
repeat match goal with
         | |- eq' _ _ => by econs
         | H : ~ eq' _ _ |- _ => elim H; by econs
         | |- _ => done
       end.

Lemma opp'_le' : forall x y (Hle : le' x y), le' (opp' y) (opp' x).
Proof.
inversion 1; subst; [by constructor|by constructor|constructor; omega].
Qed.

Lemma opp'_le'_zero : forall x (Hle : le' x (Int 0)), le' (Int 0) (opp' x).
Proof. i. apply opp'_le' in Hle. by apply Hle. Qed.

Lemma opp'_itv :
  forall x l u (Hitv : le' l x /\ le' x u),
    le' (opp' u) (opp' x) /\ le' (opp' x) (opp' l).
Proof. intros x l u [Hl Hu]; split; by apply opp'_le'. Qed.

Lemma opp'_eq' : forall x y (Heq : eq' x y), eq' (opp' x) (opp' y).
Proof.
i. apply le'_antisym.
- by apply opp'_le', le'_refl, eq'_sym.
- by apply opp'_le', le'_refl.
Qed.

Lemma opp'_double : forall x, eq' (opp' (opp' x)) x.
Proof.
destruct x; s
; [rewrite Z.opp_involutive; by constructor|by constructor|by constructor].
Qed.

Definition min' (x y : t') : t' := if le'_dec x y then x else y.

Lemma min'_mor : Proper (eq' ==> eq' ==> eq') min'.
Proof. inversion 1; inversion 1; subst. by apply eq'_refl. Qed.

Lemma min'1 : forall (x y : t'), le' (min' x y) x.
Proof.
destruct x, y; unfold min'; le'_auto.
destruct (Z_le_dec i0 i); le'_auto.
Qed.

Lemma min'2 : forall (x y : t'), le' (min' x y) y.
Proof. destruct x, y; unfold min'; le'_auto. Qed.

Lemma min'3 : forall (m x y : t'), le' m x -> le' m y -> le' m (min' x y).
Proof. destruct m, x, y;unfold min'; le'_auto. Qed.

Lemma le'_false : forall x y, ~ le' x y -> le' y x.
Proof.
destruct x, y; intros
; try (elim H; by constructor)
; try (by constructor).
+ destruct (Z_le_dec i0 i); [constructor; auto|].
  elim H; constructor; omega.
Qed.

Lemma min'_comm_sub : forall x y, le' (min' x y) (min' y x).
Proof.
intros x y; unfold min' at 2.
destruct (le'_dec y x); auto using min'2, min'1.
Qed.

Lemma min'_comm : forall (x y : t'), eq' (min' x y) (min' y x).
Proof. intros x y; apply le'_antisym; auto using min'_comm_sub. Qed.

Definition max' (x y : t') : t' := if le'_dec x y then y else x.

Lemma max'_mor : Proper (eq' ==> eq' ==> eq') max'.
Proof. inversion 1; inversion 1; subst. by apply eq'_refl. Qed.

Lemma max'1 : forall (x y : t'), le' x (max' x y).
Proof. destruct x, y; unfold max'; le'_auto. Qed.

Lemma max'2 : forall (x y : t'), le' y (max' x y).
Proof.
destruct x, y; unfold max'; le'_auto.
destruct (Z_le_dec i0 i); le'_auto.
Qed.

Lemma max'3 : forall (m x y : t'), le' x m -> le' y m -> le' (max' x y) m.
Proof. destruct m, x, y;unfold max'; le'_auto. Qed.

Lemma max'_comm_sub : forall x y, le' (max' x y) (max' y x).
Proof.
intros x y; unfold max' at 1.
destruct (le'_dec x y); auto using max'2, max'1.
Qed.

Lemma max'_comm : forall (x y : t'), eq' (max' x y) (max' y x).
Proof. intros x y; apply le'_antisym; auto using max'_comm_sub. Qed.

Lemma opp'_min' : forall x y, eq' (opp' (min' x y)) (max' (opp' x) (opp' y)).
Proof.
i. unfold min', max'. dest_if_dec; dest_if_dec.
- apply le'_antisym; [by auto|by apply opp'_le'].
- elim f0. apply opp'_le'. by apply le'_neg.
Qed.

Lemma opp'_max' : forall x y, eq' (opp' (max' x y)) (min' (opp' x) (opp' y)).
Proof.
i. unfold min', max'. dest_if_dec; dest_if_dec.
- apply le'_antisym; [by apply opp'_le'|by auto].
- elim f0. apply opp'_le'. by apply le'_neg.
Qed.

Definition lower_widen' (x y : t') : t' :=
  if le'_dec y x  then
    if eq'_dec y x then y else
      let filtered := List.filter
        (fun k => if le'_dec (Int k) y then true else false) threshold in
      list_fold (fun k m => max' (Int k) m) filtered MInf
  else x.

Definition upper_widen' (x y : t') : t' :=
  if le'_dec x y  then
    if eq'_dec x y then y else
      let filtered := List.filter
        (fun k => if le'_dec y (Int k) then true else false) threshold in
      list_fold (fun k m => min' (Int k) m) filtered PInf
  else x.

Axiom lower_narrow_msg : string_t.
Extract Constant lower_narrow_msg => """lower_narrow x y when x > y""".

Definition lower_narrow' (x y : t') : t' :=
  if le'_dec x y then y
  else invalid_arg lower_narrow_msg.

Axiom upper_narrow_msg : string_t.
Extract Constant upper_narrow_msg => """upper_narrow x y when y > x""".

Definition upper_narrow' (x y : t') : t' :=
  if le'_dec y x then y
  else invalid_arg upper_narrow_msg.

Definition plus' (x y : t')
           (pinf_minf: ~ (eq' x PInf /\ eq' y MInf))
           (minf_pinf: ~ (eq' x MInf /\ eq' y PInf)) : t'.
refine (match x as x', y as y' return (x = x') -> (y = y') -> t' with
          | Int n1, Int n2 => fun _ _ => Int (n1 + n2)
          | PInf, MInf => fun Hx Hy => _
          | MInf, PInf => fun Hx Hy => _
          | PInf, _
          | _, PInf => fun _ _ => PInf
          | MInf, _
          | _, MInf => fun _ _ => MInf
        end eq_refl eq_refl).
- subst; elim pinf_minf; by split.
- subst; elim minf_pinf; by split.
Defined.

Lemma plus'_mor :
  forall x1 y1 x2 y2 (Hx : eq' x1 x2) (Hy : eq' y1 y2)
     (Hpm1 : ~ (eq' x1 PInf /\ eq' y1 MInf))
     (Hmp1 : ~ (eq' x1 MInf /\ eq' y1 PInf))
     (Hpm2 : ~ (eq' x2 PInf /\ eq' y2 MInf))
     (Hmp2 : ~ (eq' x2 MInf /\ eq' y2 PInf)),
    eq' (plus' Hpm1 Hmp1) (plus' Hpm2 Hmp2).
Proof.
i; destruct x1, x2; try inversion Hx; subst
; destruct y1, y2; try inversion Hy; subst.
- by apply eq'_refl.
- by apply eq'_refl.
- by apply eq'_refl.
- by apply eq'_refl.
- by apply eq'_refl.
- elim Hpm1. split; by apply eq'_refl.
- by apply eq'_refl.
- elim Hmp1. split; by apply eq'_refl.
- by apply eq'_refl.
Qed.

Definition plus'_one (x : t') : t'.
refine (@plus' x (Int 1) _ _); i; des; inv FH0.
Defined.

Lemma plus'_one_mor : Proper (eq' ==> eq') plus'_one.
Proof. intros ? ? ?; unfold plus'_one. by apply plus'_mor. Qed.

Lemma cor_plus'_lb :
  forall z1 z2 lb1 lb2
     (Hlb1 : ~ eq' lb1 PInf) (Hlb2 : ~ eq' lb2 PInf)
     (Hle1 : le' lb1 (Int z1)) (Hle2 : le' lb2 (Int z2)),
    le' (plus' (not_and1 Hlb1) (not_and2 Hlb2)) (Int (z1 + z2)).
Proof.
i. inversion Hle1; inversion Hle2; subst.
- by constructor.
- by constructor.
- by constructor.
- constructor; omega.
Qed.

Lemma cor_plus'_ub :
  forall z1 z2 ub1 ub2
     (Hub1 : ~ eq' ub1 MInf) (Hub2 : ~ eq' ub2 MInf)
     (Hle1 : le' (Int z1) ub1) (Hle2 : le' (Int z2) ub2),
    le' (Int (z1 + z2)) (plus' (not_and2 Hub2) (not_and1 Hub1)).
Proof.
i. inversion Hle1; inversion Hle2; subst.
- by constructor.
- by constructor.
- by constructor.
- constructor; omega.
Qed.

Definition minus' (x y : t')
           (pinf_pinf: ~ (eq' x PInf /\ eq' y PInf))
           (minf_minf: ~ (eq' x MInf /\ eq' y MInf)) : t'.
refine (match x as x', y as y' return (x = x') -> (y = y') -> t' with
          | Int n1, Int n2 => fun _ _ => Int (n1 - n2)
          | PInf, PInf => fun Hx Hy => _
          | MInf, MInf => fun Hx Hy => _
          | PInf, _ => fun _ _ => PInf
          | MInf, _ => fun _ _ => MInf
          | _, PInf => fun _ _ => MInf
          | _, MInf => fun _ _ => PInf
        end eq_refl eq_refl).
- subst; elim pinf_pinf; by split.
- subst; elim minf_minf; by split.
Defined.

Definition minus'_one (x : t') : t'.
refine (@minus' x (Int 1) _ _); i; des; inv FH0.
Defined.

Lemma minus'_mor :
  forall x1 y1 x2 y2 (Hx : eq' x1 x2) (Hy : eq' y1 y2)
     (Hpp1 : ~ (eq' x1 PInf /\ eq' y1 PInf))
     (Hmm1 : ~ (eq' x1 MInf /\ eq' y1 MInf))
     (Hpp2 : ~ (eq' x2 PInf /\ eq' y2 PInf))
     (Hmm2 : ~ (eq' x2 MInf /\ eq' y2 MInf)),
    eq' (minus' Hpp1 Hmm1) (minus' Hpp2 Hmm2).
Proof.
i; destruct x1, x2; try inversion Hx; subst
; destruct y1, y2; try inversion Hy; subst.
- by apply eq'_refl.
- by apply eq'_refl.
- by apply eq'_refl.
- by apply eq'_refl.
- elim Hpp1. split; by apply eq'_refl.
- by apply eq'_refl.
- by apply eq'_refl.
- by apply eq'_refl.
- elim Hmm1. split; by apply eq'_refl.
Qed.

Lemma minus'_one_mor : Proper (eq' ==> eq') minus'_one.
Proof. intros ? ? ?; unfold minus'_one. by apply minus'_mor. Qed.

Lemma cor_minus'_lb :
  forall z1 z2 lb1 ub2
     (Hlb1 : ~ eq' lb1 PInf) (Hub2 : ~ eq' ub2 MInf)
     (Hle1 : le' lb1 (Int z1)) (Hle2 : le' (Int z2) ub2),
    le' (minus' (not_and1 Hlb1) (not_and2 Hub2)) (Int (z1 - z2)).
Proof.
i. inversion Hle1; inversion Hle2; subst.
- by constructor.
- by constructor.
- by constructor.
- constructor; omega.
Qed.

Lemma cor_minus'_ub :
  forall z1 z2 ub1 lb2
     (Hub1 : ~ eq' ub1 MInf) (Hlb2 : ~ eq' lb2 PInf)
     (Hle1 : le' (Int z1) ub1) (Hle2 : le' lb2 (Int z2)),
    le' (Int (z1 - z2)) (minus' (not_and2 Hlb2) (not_and1 Hub1)).
Proof.
i. inversion Hle1; inversion Hle2; subst.
- by constructor.
- by constructor.
- by constructor.
- constructor; omega.
Qed.

Definition times' (x y : t') : t' :=
  match x, y with
    | Int n1, Int n2 => Int (n1 * n2)
    | PInf, PInf
    | MInf, MInf => PInf
    | PInf, MInf
    | MInf, PInf => MInf
    | PInf, Int n
    | Int n, PInf =>
      if Z_lt_dec n 0 then MInf else
      if Z_gt_dec n 0 then PInf else
        Int 0
    | MInf, Int n
    | Int n, MInf =>
      if Z_lt_dec n 0 then PInf else
      if Z_gt_dec n 0 then MInf else
        Int 0
  end.

Lemma times'_mor : Proper (eq' ==> eq' ==> eq') times'.
Proof. inversion 1; inversion 1; subst. by apply eq'_refl. Qed.

Definition times'_comm : forall x y, eq' (times' x y) (times' y x).
Proof.
destruct x, y; try constructor.
s. rewrite Z.mul_comm. by constructor.
Qed.

Definition opp'_times'1 :
  forall x y, eq' (opp' (times' x y)) (times' (opp' x) y).
Proof.
destruct x, y; try constructor.
- s. rewrite Z.mul_opp_l. by constructor.
- s. dest_if_dec.
  + dest_if_dec; [omega|].
    dest_if_dec; omega.
  + dest_if_dec.
    * dest_if_dec; omega.
    * dest_if_dec; [omega|].
      dest_if_dec; omega.
- s. dest_if_dec.
  + dest_if_dec; [omega|].
    dest_if_dec; omega.
  + dest_if_dec.
    * dest_if_dec; omega.
    * dest_if_dec; [omega|].
      dest_if_dec; omega.
- s. dest_if_dec.
  dest_if_dec; by constructor.
- s. dest_if_dec.
  dest_if_dec; by constructor.
Qed.

Definition opp'_times'2 :
  forall x y, eq' (opp' (times' x y)) (times' x (opp' y)).
Proof.
i. eapply eq'_trans; [apply opp'_eq'; by apply times'_comm|].
eapply eq'_trans; [by apply opp'_times'1|].
by apply times'_comm.
Qed.

Lemma times'_opp'_opp' : forall x y, eq' (times' (opp' x) (opp' y)) (times' x y).
Proof.
i. rewrite <- opp'_double, opp'_times'1, opp'_times'2, opp'_double, opp'_double.
by apply eq'_refl.
Qed.

Lemma times'_zero1 : forall x, eq' (times' x (Int 0)) (Int 0).
Proof.
destruct x; s.
- rewrite Z.mul_0_r; by constructor.
- by constructor.
- by constructor.
Qed.

Lemma times'_zero2 : forall x, eq' (times' (Int 0) x) (Int 0).
Proof.
i. eapply eq'_trans; [by apply times'_comm|by apply times'_zero1].
Qed.

Lemma times'_monotone1 :
  forall x y a (Hle : le' (Int 0) a) (Hxy : le' x y), le' (times' x a) (times' y a).
Proof.
inversion 1; subst.
- inversion 1; subst.
  + by constructor.
  + by constructor.
  + s. dest_if_dec; [by constructor|].
    dest_if_dec.
    * dest_if_dec; [omega|].
      dest_if_dec; [by constructor|omega].
    * dest_if_dec; [omega|].
      dest_if_dec; by constructor.
- inversion 1; subst.
  + s. dest_if_dec; [omega|].
    dest_if_dec; [by constructor|].
    assert (j = 0%Z); [omega|subst].
    by apply le'_refl, eq'_sym, times'_zero1.
  + s. dest_if_dec; [omega|].
    dest_if_dec; [by constructor|].
    assert (j = 0%Z); [omega|subst].
    by apply le'_refl, times'_zero1.
  + s. constructor. by apply Zmult_le_compat_r.
Qed.

Lemma times'_monotone2 :
  forall x y a (Hle : le' a (Int 0)) (Hxy : le' x y), le' (times' y a) (times' x a).
Proof.
i. apply opp'_le' in Hle. simpl in Hle.
rewrite <- (opp'_double (times' y a)), <- (opp'_double (times' x a)).
apply opp'_le'.
rewrite opp'_times'2, opp'_times'2.
by apply times'_monotone1.
Qed.

Definition divide' (x y : t') (Hz : ~ eq' y (Int 0)) : t' :=
  match x, y with
    | _, PInf
    | _, MInf => Int 0
    | Int n1, Int n2 => Int (c_div n1 n2)
    | MInf, Int n => if Z_lt_dec 0 n then MInf else PInf
    | PInf, Int n => if Z_lt_dec 0 n then PInf else MInf
  end.

Lemma divide'_monotone :
  forall l u (Hle : le' l u) x1 x2 (Hxeq : eq' x1 x2) (Hlex1 : le' (Int 0) x1)
     (Hlex1' : ~ eq' x1 (Int 0)) (Hlex2' : ~ eq' x2 (Int 0)),
    le' (@divide' l x1 Hlex1') (@divide' u x2 Hlex2').
Proof.
inversion 1; subst.
- inversion 1; inversion 1; subst.
  + s; i. destruct u; s; by apply le'_refl, eq'_refl.
  + s; i. dest_if_dec; [by constructor|].
    elim Hlex1'. assert (j = 0)%Z; [omega|subst; by apply eq'_refl].
- inversion 1; inversion 1; subst.
  + s; i. destruct l; s; by apply le'_refl, eq'_refl.
  + s; i. dest_if_dec; [by constructor|].
    elim Hlex1'. assert (j = 0)%Z; [omega|subst; by apply eq'_refl].
- inversion 1; inversion 1; subst.
  + s; i. by apply le'_refl, eq'_refl.
  + s; i. constructor. by apply c_div_monotone.
Qed.

Lemma divide'_mor :
  forall x1 x2 (Heq1 : eq' x1 x2) y1 y2 (Heq2 : eq' y1 y2)
     (Hy1 : ~ (eq' y1 (Int 0))) (Hy2 : ~ (eq' y2 (Int 0))),
    eq' (divide' x1 Hy1) (divide' x2 Hy2).
Proof.
i. inversion_clear Heq1; inversion Heq2; subst. unfold divide'.
by apply eq'_refl.
Qed.

Lemma inv_divide'_p :
  forall x y (Hy : ~ (eq' y (Int 0))) (Hp : le' (Int 0) y)
     (Hdiv : divide' x Hy = PInf),
    x = PInf.
Proof.
destruct x; [|by auto|].
- destruct y; s; by inversion 2.
- destruct y; s; [|by inversion 2|by inversion 2].
  destruct (Z_lt_dec 0 i); [by inversion 2|].
  i. elim n; inversion Hp; subst.
  destruct (Z_le_lt_eq_dec _ _ Z_le); [by auto|].
  elim Hy; subst; by apply eq'_refl.
Qed.

Lemma inv_divide'_m :
  forall x y (Hy : ~ (eq' y (Int 0))) (Hp : le' (Int 0) y)
     (Hdiv : divide' x Hy = MInf),
    x = MInf.
Proof.
destruct x; [| |by auto].
- destruct y; s; by inversion 2.
- destruct y; s; [|by inversion 2|by inversion 2].
  destruct (Z_lt_dec 0 i); [by inversion 2|].
  i. elim n; inversion Hp; subst.
  destruct (Z_le_lt_eq_dec _ _ Z_le); [by auto|].
  elim Hy; subst; by apply eq'_refl.
Qed.

Definition min4' (x y z w : t') : t' := min' (min' x y) (min' z w).

Lemma min4'_mor : Proper (eq' ==> eq' ==> eq' ==> eq' ==> eq') min4'.
Proof.
intros x1 x2 Hx y1 y2 Hy z1 z2 Hz w1 w2 Hw.
apply min'_mor; by apply min'_mor.
Qed.

Lemma min4'_comm1 : forall a b c d, eq' (min4' a b c d) (min4' b a c d).
Proof. i. apply min'_mor; [by apply min'_comm|by apply eq'_refl]. Qed.

Lemma min4'_comm2 : forall a b c d, eq' (min4' a b c d) (min4' a c b d).
Proof.
i. apply le'_antisym; apply min'3; apply min'3.
eapply le'_trans; [by apply min'1|by apply min'1].
eapply le'_trans; [by apply min'2|by apply min'1].
eapply le'_trans; [by apply min'1|by apply min'2].
eapply le'_trans; [by apply min'2|by apply min'2].
eapply le'_trans; [by apply min'1|by apply min'1].
eapply le'_trans; [by apply min'2|by apply min'1].
eapply le'_trans; [by apply min'1|by apply min'2].
eapply le'_trans; [by apply min'2|by apply min'2].
Qed.

Lemma min4'_comm3 : forall a b c d, eq' (min4' a b c d) (min4' a b d c).
Proof. i. apply min'_mor; [by apply eq'_refl|by apply min'_comm]. Qed.

Definition max4' (x y z w : t') : t' := max' (max' x y) (max' z w).

Lemma max4'_mor : Proper (eq' ==> eq' ==> eq' ==> eq' ==> eq') max4'.
Proof.
intros x1 x2 Hx y1 y2 Hy z1 z2 Hz w1 w2 Hw.
apply max'_mor; by apply max'_mor.
Qed.

Lemma max4'_comm1 : forall a b c d, eq' (max4' a b c d) (max4' b a c d).
Proof. i. apply max'_mor; [by apply max'_comm|by apply eq'_refl]. Qed.

Lemma max4'_comm2 : forall a b c d, eq' (max4' a b c d) (max4' a c b d).
Proof.
i. apply le'_antisym; apply max'3; apply max'3.
eapply le'_trans; [by apply max'1|by apply max'1].
eapply le'_trans; [by apply max'1|by apply max'2].
eapply le'_trans; [by apply max'2|by apply max'1].
eapply le'_trans; [by apply max'2|by apply max'2].
eapply le'_trans; [by apply max'1|by apply max'1].
eapply le'_trans; [by apply max'1|by apply max'2].
eapply le'_trans; [by apply max'2|by apply max'1].
eapply le'_trans; [by apply max'2|by apply max'2].
Qed.

Lemma max4'_comm3 : forall a b c d, eq' (max4' a b c d) (max4' a b d c).
Proof. i. apply max'_mor; [by apply eq'_refl|by apply max'_comm]. Qed.

Lemma opp'_min4' :
  forall x y z w,
    eq' (opp' (min4' x y z w)) (max4' (opp' x) (opp' y) (opp' z) (opp' w)).
Proof.
i. unfold min4'. rewrite opp'_min', opp'_min', opp'_min'. by apply eq'_refl.
Qed.

Lemma opp'_max4' :
  forall x y z w,
    eq' (opp' (max4' x y z w)) (min4' (opp' x) (opp' y) (opp' z) (opp' w)).
Proof.
i. unfold max4'. rewrite opp'_max', opp'_max', opp'_max'. by apply eq'_refl.
Qed.

(* Main definitions of interval *)

Inductive t'' :=
| V (lb ub : t') (Hlb : ~ eq' lb PInf) (Hub : ~ eq' ub MInf) (Hle : le' lb ub)
| Bot.

Definition t := t''.

Inductive gamma : Z -> t -> Prop :=
| gamma' : forall z lb ub (lb_c : ~ eq' lb PInf) (ub_c : ~ eq' ub MInf)
                  c (Hle1: le' lb (Int z)) (Hle2: le' (Int z) ub),
             gamma z (V lb_c ub_c c).

Inductive le'' : t -> t -> Prop :=
| le_bot : forall (x : t), le'' Bot x
| le_int :
    forall (lb1 ub1 : t') (Hlb1 : ~ eq' lb1 PInf) (Hub1 : ~ eq' ub1 MInf)
           (Hle1 : le' lb1 ub1)
           (lb2 ub2 : t') (Hlb2 : ~ eq' lb2 PInf) (Hub2 : ~ eq' ub2 MInf)
           (Hle2 : le' lb2 ub2)
           (Hlb : le' lb2 lb1) (Hub : le' ub1 ub2),
      le'' (V Hlb1 Hub1 Hle1) (V Hlb2 Hub2 Hle2).

Definition le : t -> t -> Prop := le''.

Inductive eq'' : t -> t -> Prop :=
| eq_bot : eq'' Bot Bot
| eq_int :
    forall (lb1 ub1 : t') (Hlb1 : ~ eq' lb1 PInf) (Hub1 : ~ eq' ub1 MInf)
           (Hle1 : le' lb1 ub1)
           (lb2 ub2 : t') (Hlb2 : ~ eq' lb2 PInf) (Hub2 : ~ eq' ub2 MInf)
           (Hle2 : le' lb2 ub2)
           (Hlb : eq' lb2 lb1) (Hub : eq' ub1 ub2),
      eq'' (V Hlb1 Hub1 Hle1) (V Hlb2 Hub2 Hle2).

Definition eq : t -> t -> Prop := eq''.

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

Lemma le_eq : forall (x y : t), le x y -> le y x -> eq x y /\ eq y x.
Proof. auto using le_antisym. Qed.

Definition le_dec (x y : t) : {le x y} + {~ le x y}.
refine ((if physical_eq x y as c return
            physical_eq x y = c -> {le x y} + {~ le x y} then fun Hc => left _
         else fun _ =>
                match x, y with
                  | Bot, _ => left (le_bot y)
                  | _, Bot => right _
                  | @V l1 u1 _ _ _, @V l2 u2 _ _ _ =>
                    match le'_dec l2 l1, le'_dec u1 u2 with
                      | left H1, left H2 => left (le_int _ _ _ _ _ _ H1 H2)
                      | _, _ => right _
                    end
                end) Logic.eq_refl); try (inversion 1; tauto).
+ apply physical_eq_prop in Hc; subst; apply le_refl; by apply eq_refl.
Qed.

Definition eq_dec (x y : t) : {eq x y} + {~ eq x y}.
refine ((if physical_eq x y as c return
            physical_eq x y = c -> {eq x y} + {~ eq x y} then fun Hc => left _
         else fun _ =>
                match x, y with
                  | Bot, Bot => left eq_bot
                  | @V l1 u1 _ _ _, @V l2 u2 _ _ _ =>
                    match eq'_dec l2 l1, eq'_dec u1 u2 with
                      | left H1, left H2 => left (eq_int _ _ _ _ _ _ H1 H2)
                      | _, _ => right _
                    end
                  | _, _ => right _
                end) Logic.eq_refl); try (inversion 1; tauto).
+ apply physical_eq_prop in Hc; subst; by apply eq_refl.
Qed.

Lemma le_mor : Proper (eq ==> eq ==> Basics.impl) le.
Proof.
inversion_clear 1; inversion_clear 1; intro Hle; subst.
- by constructor.
- by constructor.
- by inversion Hle.
- inversion_clear Hle. constructor.
  + by rewrite Hlb4, Hlb.
  + by rewrite <- Hub4, <- Hub.
Qed.

Definition top : t.
refine (@V MInf PInf _ _ _).
- by inversion 1.
- by inversion 1.
- by vauto.
Defined.

Lemma top_prop : forall (x : t), le x top.
Proof. destruct x as [lb ub Hlb Hub H|]; vauto. Qed.

Lemma cor_itv_top : forall z, gamma z top.
Proof. constructor; by constructor. Qed.

Definition bot : t := Bot.

Lemma bot_prop : forall (x : t), le bot x. Proof. vauto. Qed.

Lemma gamma_monotone : monotone le gamma.
Proof.
intros v x y. inversion 1; i. inversion Hle. apply gamma'.
apply le'_trans with lb; by auto.
apply le'_trans with ub; by auto.
Qed.

Lemma gamma_mor : Proper (Logic.eq ==> eq ==> Basics.impl) gamma.
Proof.
intros z1 z2 Hz i1 i2 Hi Hleft; subst.
eapply gamma_monotone; [by apply Hleft|by apply le_refl].
Qed.

Lemma non_bot : forall z i (Hz : gamma z i), ~ eq i bot.
Proof.
i. assert (gamma z bot) as Hinv; [|by inversion Hinv].
eapply gamma_mor; [reflexivity|by apply FH|by auto].
Qed.

Definition of_int (i : Z) : t.
refine (@V (Int i) (Int i) _ _ _); try inversion 1.
econs; omega.
Defined.

Lemma cor_of_int : forall z, gamma z (of_int z).
Proof. constructor; by apply le'_refl, eq'_refl. Qed.

Definition of_ints (i j : Z) : t.
refine (match Z_le_dec i j with
          | left _ => (@V (Int i) (Int j) _ _ _)
          | right _ => Bot
        end); try inversion 1; by econs.
Defined.

Definition of_lb (i : Z) : t.
refine (@V (Int i) PInf _ _ _); try inversion 1; by econs.
Defined.
Definition of_ub (i : Z) : t.
refine (@V MInf (Int i) _ _ _); try inversion 1; by econs.
Defined.

Definition zero : t := of_int 0.

Definition false_itv : t := zero.

Lemma false_itv_prop : gamma 0 false_itv.
Proof. constructor; constructor; omega. Qed.

Lemma false_itv1 : forall i (Hi : gamma 0 i), le false_itv i.
Proof. inversion 1; subst. by constructor. Qed.

Definition true_itv : t := of_int 1.

Lemma true_itv_prop : gamma 1 true_itv.
Proof. constructor; constructor; omega. Qed.

Definition unknown_bool : t := of_ints 0 1.

Lemma unknown_bool_prop0 : gamma 0 unknown_bool.
Proof. constructor; constructor; omega. Qed.

Lemma unknown_bool_prop1 : gamma 1 unknown_bool.
Proof. constructor; constructor; omega. Qed.

Definition pos : t := of_lb 1.
Definition neg : t := of_ub (-1).
Definition zero_pos : t := of_lb 0.

Definition join (x y : t) : t.
refine (
  if le_dec x y then y else
  if le_dec y x then x else
  match x, y with
    | Bot, a
    | a, Bot => a
    | @V l1 u1 lb_c1 ub_c1 p1, @V l2 u2 lb_c2 ub_c2 p2 =>
      (@V (min' l1 l2) (max' u1 u2) _ _ _)
  end
).
+ unfold min'; le'_auto.
+ unfold max'; le'_auto.
+ apply le'_trans with l1; [by apply min'1|].
  apply le'_trans with u1; [vauto|by apply max'1].
Defined.

Lemma join_left : forall (x y : t), le x (join x y).
Proof.
  intros; unfold join.
  destruct (le_dec x y); [auto|].
  destruct (le_dec y x); [apply le_refl; apply eq_refl|].
  destruct x; [|apply bot_prop].
  destruct y; [|apply le_refl; apply eq_refl].
  apply le_int; [apply min'1|apply max'1].
Qed.

Lemma join_right : forall (x y : t), le y (join x y).
Proof.
  intros; unfold join.
  destruct (le_dec x y); [apply le_refl; apply eq_refl|].
  destruct (le_dec y x); [auto|].
  destruct x; [|apply le_refl; apply eq_refl].
  destruct y; [|apply bot_prop].
  apply le_int; [apply min'2|apply max'2].
Qed.

Lemma join_lub : forall (x y u : t) (Hx : le x u) (Hy : le y u), le (join x y) u.
Proof.
  i; unfold join.
  destruct (le_dec x y); [done|].
  destruct (le_dec y x); [done|].
  destruct x, y, u; inversion Hx; inversion Hy; auto.
  econs; auto using min'3, max'3.
Qed.

Definition gen_itv (l u : t') : t.
refine (match le'_dec l u with
          | left b =>
            match l as l', u as u' return l = l' -> u = u' -> t with
              | PInf, _ => fun _ _ => Bot
              | _, MInf => fun _ _ => Bot
              | _, _ => fun Hl Hu => (@V l u _ _ b)
            end Logic.eq_refl Logic.eq_refl
          | right _ => Bot
        end); subst; by inversion 1.
Defined.

Lemma gen_itv_mor : Proper (eq' ==> eq' ==> eq) gen_itv.
Proof. inversion 1; inversion 1. subst. by apply eq_refl. Qed.

Lemma le_gen_itv_left :
  forall (lb ub lb' ub': t')
     (Hlb : eq' lb PInf -> False) (Hub : eq' ub MInf -> False) (Hle : le' lb ub),
    le' lb lb' -> le' ub' ub ->
    le (gen_itv lb' ub') (V Hlb Hub Hle).
Proof.
  intros. unfold gen_itv.
  destruct (le'_dec lb' ub');[|apply le_bot].
  destruct lb',ub'; constructor; auto.
Qed.

Lemma le_gen_itv_right :
  forall (lb ub lb' ub': t')
     (Hlb : eq' lb PInf -> False) (Hub : eq' ub MInf -> False) (Hle : le' lb ub),
    le' lb' lb -> le' ub ub' ->
    le (V Hlb Hub Hle) (gen_itv lb' ub').
Proof.
  intros. unfold gen_itv.
  destruct (le'_dec lb' ub').
  destruct lb',ub'; try (constructor;auto); try (inversion l).
  inversion H;subst; elim Hlb; eq'_auto.
  inversion H0;subst; elim Hub; eq'_auto.
  elim f. apply le'_trans with lb; auto. apply le'_trans with ub; auto.
Qed.

Definition meet (x y : t) : t :=
  if le_dec x y then x else
  if le_dec y x then y else
  match x, y with
    | Bot, _
    | _, Bot => Bot
    | @V l1 u1 _ _ _, @V l2 u2 _ _ _ => gen_itv (max' l1 l2) (min' u1 u2)
  end.

Lemma meet_left : forall (x y : t), le (meet x y) x.
Proof.
  intros; unfold meet.
  destruct (le_dec x y); [apply le_refl; apply eq_refl|].
  destruct (le_dec y x); [auto|].
  destruct x; [|apply bot_prop].
  destruct y; [|apply bot_prop].
  apply le_gen_itv_left. apply max'1. apply min'1.
Qed.

Lemma meet_right : forall (x y : t), le (meet x y) y.
Proof.
  intros; unfold meet.
  destruct (le_dec x y); [auto|].
  destruct (le_dec y x); [apply le_refl; apply eq_refl|].
  destruct x; [|apply bot_prop].
  destruct y; [|apply bot_prop].
  apply le_gen_itv_left. apply max'2. apply min'2.
Qed.

Lemma meet_glb : forall (x y l : t) (Hx : le l x) (Hy : le l y), le l (meet x y).
Proof.
  i; unfold meet.
  destruct (le_dec x y); [done|].
  destruct (le_dec y x); [done|].
  destruct x, y, l; inversion Hx; inversion Hy; auto
  ; [|apply bot_prop].
  apply le_gen_itv_right; auto using min'3, max'3.
Qed.

Definition widen (x y : t) : t :=
  if structural_eq x y then x else
  match x, y with
    | Bot, _ => y
    | _, Bot => x
    | @V l1 u1 _ _ _, @V l2 u2 _ _ _ => gen_itv (lower_widen' l1 l2) (upper_widen' u1 u2)
  end.

Axiom narrow_msg : string_t.
Extract Constant narrow_msg => """narrow bot _""".

Definition narrow (x y : t) : t :=
  if structural_eq x y then x else
  match x, y with
    | _, Bot => Bot
    | Bot, _ => invalid_arg narrow_msg
    | @V l1 u1 _ _ _, @V l2 u2 _ _ _ => gen_itv (lower_narrow' l1 l2) (upper_narrow' u1 u2)
  end.

Include JoinMeetProp.

(* Auxiliary functions for interval *)

Definition is_const (x : t) : bool :=
  match x with
    | @V (Int i1) (Int i2) _ _ _ => if (eq'_dec (Int i1) (Int i2)) then true else false
    | _ => false
  end.

Definition diff (x : t) : Z :=
  match x with
    | @V (Int i1) (Int i2) _ _ _ => (i2 - i1)%Z
    | _ => 0%Z
  end.

(* Binary/Unary operations for interval *)

Definition plus (x y : t) : t.
refine (match x as x', y as y' return x = x' -> y = y' -> t with
          | Bot, _
          | _, Bot => fun _ _ => Bot
          | @V l1 u1 lb_c1 ub_c1 le1, @V l2 u2 lb_c2 ub_c2 le2 =>
            fun Hx Hy =>
              (@V (@plus' l1 l2 (not_and1 lb_c1) (not_and2 lb_c2))
                  (@plus' u1 u2 (not_and2 ub_c2) (not_and1 ub_c1)) _ _ _)
        end Logic.eq_refl Logic.eq_refl).
- destruct l1, l2; s; try by inversion 1.
  + by elim lb_c1.
  + by elim lb_c2.
- destruct u1, u2; s; try by inversion 1.
  + by elim ub_c2.
  + by elim ub_c1.
- destruct l1, l2; s;
  try (by constructor); try (by elim lb_c1); try (by elim lb_c2).
  destruct u1, u2; s;
  try (by constructor); try (by elim ub_c1); try (by elim ub_c2).
  constructor; inversion le1; inversion le2; omega.
Defined.

Lemma plus_mor : Proper (eq ==> eq ==> eq) plus.
Proof.
inversion_clear 1; inversion_clear 1.
- by apply eq_refl.
- s. by apply eq_refl.
- s. by apply eq_refl.
- constructor; by apply plus'_mor.
Qed.

Lemma cor_plus :
  forall z1 z2 i1 i2 (Hz1 : gamma z1 i1) (Hz2 : gamma z2 i2),
    gamma (z1 + z2) (plus i1 i2).
Proof.
i. unfold plus.
destruct i1; [destruct i2|]; [constructor|by inversion Hz2|by inversion Hz1].
- inversion_clear Hz1; inversion_clear Hz2. by apply cor_plus'_lb.
- inversion_clear Hz1; inversion_clear Hz2. by apply cor_plus'_ub.
Qed.

Lemma plus_non_bot :
  forall (i j : t) (Hi : ~ eq i bot) (Hj : ~ eq j bot), ~ eq (plus i j) bot.
Proof. destruct i, j; [inversion 3| | |]; by done. Qed.

Definition minus (x y : t) : t.
refine (match x as x', y as y' return x = x' -> y = y' -> t with
          | Bot, _
          | _, Bot => fun _ _ => Bot
          | @V l1 u1 lb_c1 ub_c1 le1, @V l2 u2 lb_c2 ub_c2 le2 =>
            fun Hx Hy =>
              (@V (@minus' l1 u2 (not_and1 lb_c1) (not_and2 ub_c2))
                  (@minus' u1 l2 (not_and2 lb_c2) (not_and1 ub_c1)) _ _ _)
        end Logic.eq_refl Logic.eq_refl).
- destruct l1, u2; s;
  try (by constructor); try (by elim lb_c1); try (by elim ub_c2)
  ; try (by inversion 1).
- destruct u1, l2; s;
  try (by constructor); try (by elim ub_c1); try (by elim lb_c2)
  ; try (by inversion 1).
- destruct l1, u2; s;
  try (by constructor); try (by elim lb_c1); try (by elim ub_c2)
  ; try (by inversion 1).
  destruct u1, l2; s;
  try (by constructor); try (by elim ub_c1); try (by elim lb_c2)
  ; try (by inversion 1).
  constructor; inversion le1; inversion le2; omega.
Defined.

Lemma minus_mor : Proper (eq ==> eq ==> eq) minus.
Proof.
inversion_clear 1; inversion_clear 1.
- by apply eq_refl.
- s. by apply eq_refl.
- s. by apply eq_refl.
- constructor; by apply minus'_mor.
Qed.

Lemma cor_minus :
  forall z1 z2 i1 i2 (Hz1 : gamma z1 i1) (Hz2 : gamma z2 i2),
    gamma (z1 - z2) (minus i1 i2).
Proof.
i. unfold minus.
destruct i1; [destruct i2|]; [constructor|by inversion Hz2|by inversion Hz1].
- inversion_clear Hz1; inversion_clear Hz2. by apply cor_minus'_lb.
- inversion_clear Hz1; inversion_clear Hz2. by apply cor_minus'_ub.
Qed.

Lemma minus_non_bot :
  forall (i j : t) (Hi : ~ eq i bot) (Hj : ~ eq j bot), ~ eq (minus i j) bot.
Proof. destruct i, j; [inversion 3| | |]; by done. Qed.

Lemma min_pinf1 : forall {x y} (H : ~ eq' x PInf), ~ eq' (min' x y) PInf.
Proof. destruct x, y; unfold min'; le'_auto; intros _ H; inv H. Qed.

Lemma min_pinf2 : forall {x y} (H : ~ eq' y PInf), ~ eq' (min' x y) PInf.
Proof. destruct x, y; unfold min'; le'_auto; intros _ H; inv H. Qed.

Lemma max_minf1 : forall {x y} (H : ~ eq' x MInf), ~ eq' (max' x y) MInf.
Proof. destruct x, y; unfold max'; le'_auto; intros _ H; inv H. Qed.

Lemma max_minf2 : forall {x y} (H : ~ eq' y MInf), ~ eq' (max' x y) MInf.
Proof. destruct x, y; unfold max'; le'_auto; intros _ H; inv H. Qed.

Lemma min4'_le'_max4':
  forall {x y z w}, le' (min4' x y z w) (max4' x y z w).
Proof.
  i; eapply le'_trans; [by apply min'1|].
  eapply le'_trans; [by apply min'1|].
  eapply le'_trans; [by apply max'1|by apply max'1].
Qed.

Ltac min4'_max4'_auto H1 H2 :=
  repeat match goal with
           | |- _ => apply H1; apply H1; by inversion 1
           | |- _ => apply H1; apply H2; by inversion 1
           | |- _ => apply H2; apply H1; by inversion 1
           | |- _ => apply H2; apply H2; by inversion 1
           | H : ~ eq' _ _ |- _ => elim H; by econs
           | x := if ?e then _ else _ |- _ => destruct e
         end.

Definition times (x y : t) : t.
refine match x, y with
         | Bot, _
         | _, Bot => Bot
         | @V l1 u1 lb_c1 ub_c1 le1, @V l2 u2 lb_c2 ub_c2 le2 =>
           let x1 := times' l1 l2 in
           let x2 := times' l1 u2 in
           let x3 := times' u1 l2 in
           let x4 := times' u1 u2 in
           @V (min4' x1 x2 x3 x4) (max4' x1 x2 x3 x4) _ _ min4'_le'_max4'
       end.
+ destruct l1, l2, u1, u2; simpl times' in *
  ; min4'_max4'_auto @min_pinf1 @min_pinf2.
+ destruct l1, l2, u1, u2; simpl times' in *
  ; min4'_max4'_auto @max_minf1 @max_minf2.
Defined.

Lemma times_mor : Proper (eq ==> eq ==> eq) times.
Proof.
inversion_clear 1; inversion_clear 1; subst.
- by apply eq_refl.
- by apply eq_refl.
- by apply eq_refl.
- constructor.
  + apply min4'_mor; by apply times'_mor.
  + apply max4'_mor; by apply times'_mor.
Qed.

Lemma times_prop_pp :
  forall z1 z2 l1 u1 l2 u2
     (Hz1 : (0 <= z1)%Z) (Hle1 : le' l1 (Int z1) /\ le' (Int z1) u1)
     (Hz2 : (0 <= z2)%Z) (Hle2 : le' l2 (Int z2) /\ le' (Int z2) u2)
     (x1 := times' l1 l2) (x2 := times' l1 u2)
     (x3 := times' u1 l2) (x4 := times' u1 u2),
    le' (min4' x1 x2 x3 x4) (Int (z1 * z2))
    /\ le' (Int (z1 * z2)) (max4' x1 x2 x3 x4).
Proof.
i. split; [destruct (le'_dec (Int 0) l1); [destruct (le'_dec (Int 0) l2)|]|].
- eapply le'_trans; [apply min'1|].
  eapply le'_trans; [apply min'1|].
  subst x1 x2 x3 x4.
  eapply le'_trans with (times' (Int z1) (Int z2))
  ; [|by apply le'_refl, eq'_refl].
  eapply le'_trans with (times' (Int z1) l2)
  ; [apply times'_monotone1; [by auto|by apply Hle1]|].
  rewrite times'_comm, (times'_comm (Int z1) (Int z2)).
  apply times'_monotone1
  ; [eapply le'_trans; [by apply l|by apply Hle1]|by apply Hle2].
- apply le'_false in f.
  apply le'_trans with (Int 0); [|constructor; by apply Z.mul_nonneg_nonneg].
  eapply le'_trans; [by apply min'2|].
  eapply le'_trans; [by apply min'1|].
  subst x1 x2 x3 x4.
  eapply le'_trans; [|by apply le'_refl, times'_zero2].
  apply times'_monotone2
  ; [by auto|eapply le'_trans; [|apply Hle1]; by constructor].
- apply le'_false in f. 
  apply le'_trans with (Int 0); [|constructor; by apply Z.mul_nonneg_nonneg].
  eapply le'_trans; [by apply min'1|].
  eapply le'_trans; [by apply min'2|].
  subst x1 x2 x3 x4.
  eapply le'_trans; [|by apply le'_refl, times'_zero2].
  rewrite times'_comm.
  apply times'_monotone2
  ; [by auto|eapply le'_trans; [|apply Hle2]; by constructor].
- eapply le'_trans; [|by apply max'2].
  eapply le'_trans; [|by apply max'2].
  subst x1 x2 x3 x4.
  eapply le'_trans
  ; [| apply times'_monotone1
       ; [eapply le'_trans; [|apply Hle2]; by constructor|by apply Hle1] ].
  eapply le'_trans
  ; [| rewrite times'_comm;
       apply times'_monotone1; [by constructor|by apply Hle2] ].
  rewrite times'_comm. by apply le'_refl, eq'_refl.
Qed.

Lemma times_prop_pn :
  forall z1 z2 l1 u1 l2 u2
     (Hz1 : (0 <= z1)%Z) (Hle1 : le' l1 (Int z1) /\ le' (Int z1) u1)
     (Hz2 : (z2 <= 0)%Z) (Hle2 : le' l2 (Int z2) /\ le' (Int z2) u2)
     (x1 := times' l1 l2) (x2 := times' l1 u2)
     (x3 := times' u1 l2) (x4 := times' u1 u2),
    le' (min4' x1 x2 x3 x4) (Int (z1 * z2))
    /\ le' (Int (z1 * z2)) (max4' x1 x2 x3 x4).
Proof.
i. assert (0 <= - z2)%Z as Hz2'; [omega|clear Hz2].
apply opp'_itv in Hle2.
exploit times_prop_pp.
- by apply Hz1.
- by apply Hle1.
- by apply Hz2'.
- by apply Hle2.
- intros Hr. apply opp'_itv in Hr. destruct Hr as [Hr1 Hr2]. split.
  + eapply le'_mor; [| |by apply Hr1].
    * rewrite opp'_max4', min4'_comm1, min4'_comm3.
      apply min4'_mor; by rewrite opp'_times'2, opp'_double.
    * s. rewrite Zopp_mult_distr_r, Z.opp_involutive.
      by apply eq'_refl.
  + eapply le'_mor; [| |by apply Hr2].
    * s. rewrite Zopp_mult_distr_r, Z.opp_involutive.
      by apply eq'_refl.
    * rewrite opp'_min4', max4'_comm1, max4'_comm3.
      apply max4'_mor; by rewrite opp'_times'2, opp'_double.
Qed.

Lemma times_prop_np :
  forall z1 z2 l1 u1 l2 u2
     (Hz1 : (z1 <= 0)%Z) (Hle1 : le' l1 (Int z1) /\ le' (Int z1) u1)
     (Hz2 : (0 <= z2)%Z) (Hle2 : le' l2 (Int z2) /\ le' (Int z2) u2)
     (x1 := times' l1 l2) (x2 := times' l1 u2)
     (x3 := times' u1 l2) (x4 := times' u1 u2),
    le' (min4' x1 x2 x3 x4) (Int (z1 * z2))
    /\ le' (Int (z1 * z2)) (max4' x1 x2 x3 x4).
Proof.
i. exploit times_prop_pn.
- by apply Hz2.
- by apply Hle2.
- by apply Hz1.
- by apply Hle1.
- intros [Hmin Hmax]. subst x1 x2 x3 x4. split.
  + eapply le'_mor; [| |by apply Hmin].
    * rewrite min4'_comm2. apply min4'_mor; by apply times'_comm.
    * rewrite Z.mul_comm. by apply eq'_refl.
  + eapply le'_mor; [| |by apply Hmax].
    * rewrite Z.mul_comm. by apply eq'_refl.
    * rewrite max4'_comm2. apply max4'_mor; by apply times'_comm.
Qed.

Lemma times_prop_nn :
  forall z1 z2 l1 u1 l2 u2
     (Hz1 : (z1 <= 0)%Z) (Hle1 : le' l1 (Int z1) /\ le' (Int z1) u1)
     (Hz2 : (z2 <= 0)%Z) (Hle2 : le' l2 (Int z2) /\ le' (Int z2) u2)
     (x1 := times' l1 l2) (x2 := times' l1 u2)
     (x3 := times' u1 l2) (x4 := times' u1 u2),
    le' (min4' x1 x2 x3 x4) (Int (z1 * z2))
    /\ le' (Int (z1 * z2)) (max4' x1 x2 x3 x4).
Proof.
i. assert (0 <= - z1)%Z as Hz1'; [omega|clear Hz1].
assert (0 <= - z2)%Z as Hz2'; [omega|clear Hz2].
apply opp'_itv in Hle1; simpl in Hle1.
apply opp'_itv in Hle2; simpl in Hle2.
exploit times_prop_pp.
- by apply Hz1'.
- by apply Hle1.
- by apply Hz2'.
- by apply Hle2.
- intros [Hmin Hmax]. subst x1 x2 x3 x4. split.
  + eapply le'_mor; [| |by apply Hmin].
    * do 4 rewrite times'_opp'_opp'.
      rewrite min4'_comm3, min4'_comm2, min4'_comm1.
      rewrite min4'_comm3, min4'_comm2.
      rewrite min4'_comm3.
      by apply eq'_refl.
    * rewrite Z.mul_opp_opp. by apply eq'_refl.
  + eapply le'_mor; [| |by apply Hmax].
    * rewrite Z.mul_opp_opp. by apply eq'_refl.
    * do 4 rewrite times'_opp'_opp'.
      rewrite max4'_comm3, max4'_comm2, max4'_comm1.
      rewrite max4'_comm3, max4'_comm2.
      rewrite max4'_comm3.
      by apply eq'_refl.
Qed.

Lemma times_prop :
  forall z1 z2 x1 x2 (H1: gamma z1 x1) (H2: gamma z2 x2),
    gamma (z1 * z2)%Z (times x1 x2).
Proof.
inversion_clear 1; inversion_clear 1; subst.
destruct (Z_le_dec 0%Z z1), (Z_le_dec 0%Z z2).
- exploit times_prop_pp.
  + by apply l.
  + split; [by apply Hle1|by apply Hle2].
  + by apply l0.
  + split; [by apply Hle0|by apply Hle3].
  + intros [H1 H2]. constructor; [by apply H1|by apply H2].
- exploit times_prop_pn.
  + apply l.
  + split; [by apply Hle1|by apply Hle2].
  + assert (z2 <= 0)%Z as n'; [omega|by apply n'].
  + split; [by apply Hle0|by apply Hle3].
  + intros [H1 H2]. constructor; [by apply H1|by apply H2].
- exploit times_prop_np.
  + assert (z1 <= 0)%Z as n'; [omega|by apply n'].
  + split; [by apply Hle1|by apply Hle2].
  + apply l.
  + split; [by apply Hle0|by apply Hle3].
  + intros [H1 H2]. constructor; [by apply H1|by apply H2].
- exploit times_prop_nn.
  + assert (z1 <= 0)%Z as n'; [omega|by apply n'].
  + split; [by apply Hle1|by apply Hle2].
  + assert (z2 <= 0)%Z as n'; [omega|by apply n'].
  + split; [by apply Hle0|by apply Hle3].
  + intros [H1 H2]. constructor; [by apply H1|by apply H2].
Qed.

Lemma times_non_bot :
  forall (i j : t) (Hi : ~ eq i bot) (Hj : ~ eq j bot), ~ eq (times i j) bot.
Proof. destruct i, j; [inversion 3| | |]; by done. Qed.

Lemma not_zero1 :
  forall (lb ub : t') (x : t) (lb_c : ~ eq' lb PInf) (ub_c : ~ eq' ub MInf)
         (Hle : le' lb ub) (Hzero : ~ le zero x) (Hx : x = V lb_c ub_c Hle),
    ~ eq' lb (Int 0).
Proof.
  i; subst; apply Hzero; econs; by eauto using le'_refl, le'_trans, eq'_sym.
Qed.

Lemma not_zero2 :
  forall (lb ub : t') (x : t) (lb_c : ~ eq' lb PInf) (ub_c : ~ eq' ub MInf)
         (Hle : le' lb ub) (Hzero : ~ le zero x) (Hx : x = V lb_c ub_c Hle),
    ~ eq' ub (Int 0).
Proof.
  i; subst; apply Hzero; econs; by eauto using le'_refl, le'_trans, eq'_sym.
Qed.

Definition divide (x y : t) : t.
refine
  (match x, y as y' return y = y' -> t with
   | Bot, _
   | _, Bot => fun _ => Bot
   | @V l1 u1 _ _ _, @V l2 u2 _ _ _ =>
     fun Hy =>
       match le_dec zero y with
       | left _ => top
       | right Hzero =>
         match eq'_dec l2 u2 with
         | left _ =>
           match le'_dec (Int 0) l2 with
           | left _ =>
             let l1' := @divide' l1 l2 (not_zero1 Hzero Hy) in
             let u1' := @divide' u1 l2 (not_zero1 Hzero Hy) in
             gen_itv l1' u1'
           | right _ => top
           end
         | right _ => top
         end
       end
   end Logic.eq_refl).
Defined.

Lemma divide'_c_div :
  forall z1 z2 (Hz2 : ~ eq' (Int z2) (Int 0)),
    Int (c_div z1 z2) = divide' (Int z1) Hz2.
Proof. by auto. Qed.

Lemma divide_prop :
  forall z1 z2 x1 x2 (H1: gamma z1 x1) (H2: gamma z2 x2),
    gamma (c_div z1 z2)%Z (divide x1 x2).
Proof.
inversion_clear 1; inversion_clear 1.
unfold divide.
destruct (le_dec zero (V lb_c0 ub_c0 c0)); [by apply cor_itv_top|].
destruct (eq'_dec lb0 ub0); [|by apply cor_itv_top].
destruct (le'_dec (Int 0) lb0); [|by apply cor_itv_top].
assert (~ eq' (Int z2) (Int 0)) as Hz2
; [ i; elim f; constructor
    ; [ eapply le'_trans; [by apply Hle0|by apply le'_refl]
      | eapply le'_trans; [|by apply Hle3]; by apply le'_refl, eq'_sym ] |].
assert (eq' lb0 (Int z2)) as Heql
; [ apply le'_antisym
    ; [by auto|eapply le'_trans; [by apply Hle3|by apply le'_refl, eq'_sym]]
  | unfold eq' in Heql; subst ].
unfold eq' in e; subst. clear Hle0 Hle3.
unfold gen_itv.
destruct (le'_dec (divide' lb _) (divide' ub _))
; [|elim f0; by apply divide'_monotone].
remember (divide' lb _) as l'; destruct l'.
- remember (divide' ub _) as u'; destruct u'.
  + constructor.
    * rewrite Heql', divide'_c_div with (Hz2 := Hz2).
      eapply divide'_monotone; [by auto|by apply eq'_refl|by auto].
    * rewrite Hequ', divide'_c_div with (Hz2 := Hz2).
      eapply divide'_monotone; [by auto|by apply eq'_refl|by auto].
  + constructor; [|by constructor].
    rewrite Heql', divide'_c_div with (Hz2 := Hz2).
      eapply divide'_monotone; [by auto|by apply eq'_refl|by auto].
  + symmetry in Hequ'; apply inv_divide'_m in Hequ'; [subst|by auto].
    by inversion l0.
- symmetry in Heql'; apply inv_divide'_p in Heql'; [subst|by auto].
  elim lb_c; by apply eq'_refl.
- symmetry in Heql'; apply inv_divide'_m in Heql'; [subst|by auto].
  remember (divide' ub _) as u'; destruct u'.
  + constructor; [by constructor|].
    rewrite Hequ', divide'_c_div with (Hz2 := Hz2).
    eapply divide'_monotone; [by auto|by apply eq'_refl|by auto].
  + constructor; by constructor.
  + symmetry in Hequ'; apply inv_divide'_m in Hequ'; [subst|by auto].
    elim ub_c; by apply eq'_refl.
Qed.

Lemma divide_mor : Proper (eq ==> eq ==> eq) divide.
Proof.
inversion_clear 1; inversion_clear 1
; [by apply eq_refl|by apply eq_refl|by apply eq_refl|].
unfold divide.
unfold eq' in Hlb4, Hub4; subst.
destruct (le_dec zero (V Hlb0 Hub0 Hle0)).
- destruct (le_dec zero (V Hlb3 Hub3 Hle3))
  ; [| elim f
       ; eapply le_mor; [| |by apply l]; [by apply eq_refl|by constructor] ].
  by apply eq_refl.
- destruct (le_dec zero (V Hlb3 Hub3 Hle3))
  ; [ elim f
      ; eapply le_mor; [| |by apply l]; [by apply eq_refl|by constructor] |].
  destruct (eq'_dec lb0 ub3); [|by apply eq_refl].
  destruct (le'_dec (Int 0) lb0); [|by apply eq_refl].
  apply gen_itv_mor ; apply divide'_mor; by auto.
Qed.

Local Open Scope sumbool.

Definition and_itv (x y : t) : t :=
  if eq_dec x Bot ||| eq_dec y Bot then Bot else
  if eq_dec x false_itv ||| eq_dec y false_itv then false_itv else
  if ~~ le_dec false_itv x &&& ~~ le_dec false_itv y then true_itv else
    unknown_bool.

Lemma and_itv_mor : Proper (eq ==> eq ==> eq) and_itv.
Proof.
unfold and_itv; intros x1 x2 Hx y1 y2 Hy.
destruct (eq_dec x1 Bot ||| eq_dec y1 Bot), (eq_dec x2 Bot ||| eq_dec y2 Bot)
; [ by apply eq_refl
  | elim o; intro; destruct a as [a1 a2]; [elim a1|elim a2]
    ; by eauto using eq_trans, eq_sym
  | elim o; intro; destruct a as [a1 a2]; [elim a1|elim a2]
    ; by eauto using eq_trans, eq_sym |].
destruct (eq_dec x1 false_itv ||| eq_dec y1 false_itv)
       , (eq_dec x2 false_itv ||| eq_dec y2 false_itv)
; [ by apply eq_refl
  | elim o; intro; destruct a1 as [a1 a2]; [elim a1|elim a2]
    ; by eauto using eq_trans, eq_sym
  | elim o; intro; destruct a1 as [a1 a2]; [elim a1|elim a2]
    ; by eauto using eq_trans, eq_sym |].
destruct (~~ le_dec false_itv x1 &&& ~~ le_dec false_itv y1)
       , (~~ le_dec false_itv x2 &&& ~~ le_dec false_itv y2)
; [ by apply eq_refl | | | by apply eq_refl ].
- elim o; intro.
  + destruct a3 as [a3 _]; elim a3. by eauto using le_trans, le_refl, eq_sym.
  + destruct a3 as [_ a3]; elim a3. by eauto using le_trans, le_refl, eq_sym.
- elim o; intro.
  + destruct a3 as [a3 _]; elim a3. by eauto using le_trans, le_refl, eq_sym.
  + destruct a3 as [_ a3]; elim a3. by eauto using le_trans, le_refl, eq_sym.
Qed.

Definition or_itv (x y : t) : t :=
  if eq_dec x Bot ||| eq_dec y Bot then Bot else
  if eq_dec x false_itv &&& eq_dec y false_itv then false_itv else
  if ~~ le_dec false_itv x ||| ~~ le_dec false_itv y then true_itv else
    unknown_bool.

Lemma or_itv_mor : Proper (eq ==> eq ==> eq) or_itv.
Proof.
unfold or_itv; intros x1 x2 Hx y1 y2 Hy.
destruct (eq_dec x1 Bot ||| eq_dec y1 Bot), (eq_dec x2 Bot ||| eq_dec y2 Bot)
; [ by apply eq_refl
  | elim o; intro; destruct a as [a1 a2]; [elim a1|elim a2]
    ; by eauto using eq_trans, eq_sym
  | elim o; intro; destruct a as [a1 a2]; [elim a1|elim a2]
    ; by eauto using eq_trans, eq_sym |].
destruct (eq_dec x1 false_itv &&& eq_dec y1 false_itv)
       , (eq_dec x2 false_itv &&& eq_dec y2 false_itv)
; [ by apply eq_refl
  | elim o; intro Heq; destruct a1 as [a1 a2]; elim Heq
    ; by eauto using eq_trans, eq_sym
  | elim o; intro Heq; destruct a1 as [a1 a2]; elim Heq
    ; by eauto using eq_trans, eq_sym |].
destruct (~~ le_dec false_itv x1 ||| ~~ le_dec false_itv y1)
       , (~~ le_dec false_itv x2 ||| ~~ le_dec false_itv y2)
; [ by apply eq_refl | | | by apply eq_refl ].
- elim o1; intro Heq; elim Heq.
  + destruct a1 as [a1 _]; by eauto using le_trans, le_refl, eq_sym.
  + destruct a1 as [_ a1]; by eauto using le_trans, le_refl, eq_sym.
- elim o1; intro Heq; elim Heq.
  + destruct a1 as [a1 _]; by eauto using le_trans, le_refl, eq_sym.
  + destruct a1 as [_ a1]; by eauto using le_trans, le_refl, eq_sym.
Qed.

Definition eq_itv (x y : t) : t :=
  match x, y with
    | Bot, _
    | _, Bot => Bot
    | @V l1 u1 lb_c1 ub_c1 le1, @V l2 u2 lb_c2 ub_c2 le2 =>
      if eq'_dec l1 u1 &&& eq'_dec u1 l2 &&& eq'_dec l2 u2 then true_itv else
      if ~~ le'_dec l2 u1 then false_itv else
      if ~~ le'_dec l1 u2 then false_itv else
        unknown_bool
  end.

Lemma eq_itv_mor : Proper (eq ==> eq ==> eq) eq_itv.
Proof.
unfold eq_itv; intros x1 x2 Hx y1 y2 Hy.
destruct x1, x2; [|by inversion Hx|by inversion Hx|by apply eq_refl].
destruct y1, y2; [|by inversion Hy|by inversion Hy|by apply eq_refl].
destruct (eq'_dec lb ub &&& eq'_dec ub lb1 &&& eq'_dec lb1 ub1)
       , (eq'_dec lb0 ub0 &&& eq'_dec ub0 lb2 &&& eq'_dec lb2 ub2).
- by apply eq_refl.
- elim o; [|intro o'; elim o']; intro a'; elim a'
  ; inversion Hx; inversion Hy; subst.
  + apply eq'_trans with lb; [by auto using eq'_sym|].
    apply eq'_trans with ub; [|by auto using eq'_sym].
    by apply a.
  + apply eq'_trans with ub; [by auto using eq'_sym|].
    apply eq'_trans with lb1; [|by auto using eq'_sym].
    by apply a.
  + apply eq'_trans with lb1; [by auto using eq'_sym|].
    apply eq'_trans with ub1; [|by auto using eq'_sym].
    by apply a.
- elim o; [|intro o'; elim o']; intro a'; elim a'
  ; inversion Hx; inversion Hy; subst.
  + apply eq'_trans with lb0; [by auto using eq'_sym|].
    apply eq'_trans with ub0; [|by auto using eq'_sym].
    by apply a.
  + apply eq'_trans with ub0; [by auto using eq'_sym|].
    apply eq'_trans with lb2; [|by auto using eq'_sym].
    by apply a.
  + apply eq'_trans with lb2; [by auto using eq'_sym|].
    apply eq'_trans with ub2; [|by auto using eq'_sym].
    by apply a.
- destruct (le'_dec lb1 ub), (le'_dec lb2 ub0); s
  ; [| elim f; inversion Hx; inversion Hy; subst
      ; apply le'_trans with lb1; [|apply le'_trans with ub]
      ; by auto using le'_refl, eq'_sym
    | elim f; inversion Hx; inversion Hy; subst
      ; apply le'_trans with lb2; [|apply le'_trans with ub0]
      ; by auto using le'_refl, eq'_sym
    | by apply eq_refl ].
  destruct (le'_dec lb ub1), (le'_dec lb0 ub2); s
  ; [ by apply eq_refl
    | elim f; inversion Hx; inversion Hy; subst
      ; apply le'_trans with lb; [|apply le'_trans with ub1]
      ; by auto using le'_refl, eq'_sym
    | elim f; inversion Hx; inversion Hy; subst
      ; apply le'_trans with lb0; [|apply le'_trans with ub2]
      ; by auto using le'_refl, eq'_sym
    | by apply eq_refl ].
Qed.

Lemma cor_eq1 :
  forall z i1 i2 (Hz1 : gamma z i1) (Hz2 : gamma z i2), gamma 1 (eq_itv i1 i2).
Proof.
i. unfold eq_itv.
destruct i1; [destruct i2|]; s; [|by inversion Hz2|by inversion Hz1].
dest_if_dec; [|dest_if_dec; [|dest_if_dec]].
- by apply true_itv_prop.
- inversion Hz1; inversion Hz2; subst.
  elim f. eapply le'_trans; [by apply Hle3|by auto].
- inversion Hz1; inversion Hz2; subst.
  elim f. eapply le'_trans; [by apply Hle1|by auto].
- by apply unknown_bool_prop1.
Qed.

Lemma cor_eq0 :
  forall z1 z2 i1 i2 (Hne : z1 <> z2) (Hz1 : gamma z1 i1) (Hz2 : gamma z2 i2),
    gamma 0 (eq_itv i1 i2).
Proof.
i. unfold eq_itv.
destruct i1; [destruct i2|]; s; [|by inversion Hz2|by inversion Hz1].
dest_if_dec; [|dest_if_dec; [|dest_if_dec]].
- assert (eq' (Int z1) (Int z2)) as Hinv; [|inversion Hinv; omega].
  destruct a as [a1 [a2 a3]]. inversion Hz1; inversion Hz2; subst.
  eapply eq'_trans; [eapply eq'_trans; [|by apply a2]|].
  + apply le'_antisym; [by auto|].
    eapply le'_trans; [|by apply Hle1].
    by apply le'_refl, eq'_sym.
  + apply le'_antisym; [by auto|].
    eapply le'_trans; [by apply Hle4|].
    by apply le'_refl, eq'_sym.
- by apply false_itv_prop.
- by apply false_itv_prop.
- by apply unknown_bool_prop0.
Qed.

Definition ne_itv (x y : t) : t :=
  match x, y with
    | Bot, _
    | _, Bot => Bot
    | @V l1 u1 lb_c1 ub_c1 le1, @V l2 u2 lb_c2 ub_c2 le2 =>
      if eq'_dec l1 u1 &&& eq'_dec u1 l2 &&& eq'_dec l2 u2 then false_itv else
      if ~~ le'_dec l2 u1 then true_itv else
      if ~~ le'_dec l1 u2 then true_itv else
        unknown_bool
  end.

Lemma ne_itv_mor : Proper (eq ==> eq ==> eq) ne_itv.
Proof.
unfold ne_itv; intros x1 x2 Hx y1 y2 Hy.
destruct x1, x2; [|by inversion Hx|by inversion Hx|by apply eq_refl].
destruct y1, y2; [|by inversion Hy|by inversion Hy|by apply eq_refl].
destruct (eq'_dec lb ub &&& eq'_dec ub lb1 &&& eq'_dec lb1 ub1)
       , (eq'_dec lb0 ub0 &&& eq'_dec ub0 lb2 &&& eq'_dec lb2 ub2).
- by apply eq_refl.
- elim o; [|intro o'; elim o']; intro a'; elim a'
  ; inversion Hx; inversion Hy; subst.
  + apply eq'_trans with lb; [by auto using eq'_sym|].
    apply eq'_trans with ub; [|by auto using eq'_sym].
    by apply a.
  + apply eq'_trans with ub; [by auto using eq'_sym|].
    apply eq'_trans with lb1; [|by auto using eq'_sym].
    by apply a.
  + apply eq'_trans with lb1; [by auto using eq'_sym|].
    apply eq'_trans with ub1; [|by auto using eq'_sym].
    by apply a.
- elim o; [|intro o'; elim o']; intro a'; elim a'
  ; inversion Hx; inversion Hy; subst.
  + apply eq'_trans with lb0; [by auto using eq'_sym|].
    apply eq'_trans with ub0; [|by auto using eq'_sym].
    by apply a.
  + apply eq'_trans with ub0; [by auto using eq'_sym|].
    apply eq'_trans with lb2; [|by auto using eq'_sym].
    by apply a.
  + apply eq'_trans with lb2; [by auto using eq'_sym|].
    apply eq'_trans with ub2; [|by auto using eq'_sym].
    by apply a.
- destruct (le'_dec lb1 ub), (le'_dec lb2 ub0); s
  ; [| elim f; inversion Hx; inversion Hy; subst
      ; apply le'_trans with lb1; [|apply le'_trans with ub]
      ; by auto using le'_refl, eq'_sym
    | elim f; inversion Hx; inversion Hy; subst
      ; apply le'_trans with lb2; [|apply le'_trans with ub0]
      ; by auto using le'_refl, eq'_sym
    | by apply eq_refl ].
  destruct (le'_dec lb ub1), (le'_dec lb0 ub2); s
  ; [ by apply eq_refl
    | elim f; inversion Hx; inversion Hy; subst
      ; apply le'_trans with lb; [|apply le'_trans with ub1]
      ; by auto using le'_refl, eq'_sym
    | elim f; inversion Hx; inversion Hy; subst
      ; apply le'_trans with lb0; [|apply le'_trans with ub2]
      ; by auto using le'_refl, eq'_sym
    | by apply eq_refl ].
Qed.

Lemma cor_ne1 :
  forall z1 z2 i1 i2 (Hne : z1 <> z2) (Hz1 : gamma z1 i1) (Hz2 : gamma z2 i2),
    gamma 1 (ne_itv i1 i2).
Proof.
i. unfold ne_itv.
destruct i1; [destruct i2|]; s; [|by inversion Hz2|by inversion Hz1].
dest_if_dec; [|dest_if_dec; [|dest_if_dec]].
- assert (eq' (Int z1) (Int z2)) as Hinv; [|inversion Hinv; omega].
  destruct a as [a1 [a2 a3]]. inversion Hz1; inversion Hz2; subst.
  eapply eq'_trans; [eapply eq'_trans; [|by apply a2]|].
  + apply le'_antisym; [by auto|].
    eapply le'_trans; [|by apply Hle1].
    by apply le'_refl, eq'_sym.
  + apply le'_antisym; [by auto|].
    eapply le'_trans; [by apply Hle4|].
    by apply le'_refl, eq'_sym.
- by apply true_itv_prop.
- by apply true_itv_prop.
- by apply unknown_bool_prop1.
Qed.

Lemma cor_ne0 :
  forall z i1 i2 (Hz1 : gamma z i1) (Hz2 : gamma z i2), gamma 0 (ne_itv i1 i2).
Proof.
i. unfold ne_itv.
destruct i1; [destruct i2|]; s; [|by inversion Hz2|by inversion Hz1].
dest_if_dec; [|dest_if_dec; [|dest_if_dec]].
- by apply false_itv_prop.
- inversion Hz1; inversion Hz2; subst.
  elim f. eapply le'_trans; [by apply Hle3|by auto].
- inversion Hz1; inversion Hz2; subst.
  elim f. eapply le'_trans; [by apply Hle1|by auto].
- by apply unknown_bool_prop0.
Qed.

Definition lt_itv (x y : t) : t :=
  match x, y with
    | Bot, _
    | _, Bot => Bot
    | @V l1 u1 lb_c1 ub_c1 le1, @V l2 u2 lb_c2 ub_c2 le2 =>
      if ~~ le'_dec l2 u1 then true_itv else
      if le'_dec u2 l1 then false_itv else
        unknown_bool
  end.

Lemma lt_itv_mor : Proper (eq ==> eq ==> eq) lt_itv.
Proof.
unfold lt_itv; intros x1 x2 Hx y1 y2 Hy.
destruct x1, x2; [|by inversion Hx|by inversion Hx|by apply eq_refl].
destruct y1, y2; [|by inversion Hy|by inversion Hy|by apply eq_refl].
destruct (le'_dec lb1 ub), (le'_dec lb2 ub0); s
; [| elim f; inversion Hx; inversion Hy; subst
     ; apply le'_trans with lb1; [by auto using le'_refl, eq'_sym|]
     ; apply le'_trans with ub; by auto using le'_refl, eq'_sym
   | elim f; inversion Hx; inversion Hy; subst
     ; apply le'_trans with lb2; [by auto using le'_refl, eq'_sym|]
     ; apply le'_trans with ub0; by auto using le'_refl, eq'_sym
   | by apply eq_refl ].
destruct (le'_dec ub1 lb), (le'_dec ub2 lb0)
; [ by apply eq_refl
  | elim f; inversion Hx; inversion Hy; subst
    ; apply le'_trans with ub1; [by auto using le'_refl, eq'_sym|]
    ; apply le'_trans with lb; by auto using le'_refl, eq'_sym
  | elim f; inversion Hx; inversion Hy; subst
    ; apply le'_trans with ub2; [by auto using le'_refl, eq'_sym|]
    ; apply le'_trans with lb0; by auto using le'_refl, eq'_sym
  | by apply eq_refl ].
Qed.

Lemma cor_lt1 :
  forall z1 z2 i1 i2 (Hlt : (z1 < z2)%Z) (Hz1 : gamma z1 i1) (Hz2 : gamma z2 i2),
    gamma 1 (lt_itv i1 i2).
Proof.
i; unfold lt_itv.
destruct i1; [destruct i2|]; s; [|by inversion Hz2|by inversion Hz1].
dest_if_dec; [|dest_if_dec].
- by apply true_itv_prop.
- inversion Hz1; inversion Hz2; subst.
  assert (le' (Int z2) (Int z1)) as Hinv; [|inversion Hinv; omega].
  eapply le'_trans; [by apply Hle4|].
  eapply le'_trans; [by apply l0|by auto].
- by apply unknown_bool_prop1.
Qed.

Lemma cor_lt0 :
  forall z1 z2 i1 i2 (Hlt : ~ (z1 < z2)%Z) (Hz1 : gamma z1 i1) (Hz2 : gamma z2 i2),
    gamma 0 (lt_itv i1 i2).
Proof.
i; unfold lt_itv.
destruct i1; [destruct i2|]; s; [|by inversion Hz2|by inversion Hz1].
dest_if_dec; [|dest_if_dec].
- inversion Hz1; inversion Hz2; subst.
  assert (le' (Int z2) (Int z1)) as Hinv
  ; [constructor; apply Znot_lt_ge in Hlt; omega|].
  elim f.
  eapply le'_trans; [by apply Hle3|].
  eapply le'_trans; [by apply Hinv|by auto].
- by apply false_itv_prop.
- by apply unknown_bool_prop0.
Qed.

Definition le_itv (x y : t) : t :=
  match x, y with
    | Bot, _
    | _, Bot => Bot
    | @V l1 u1 lb_c1 ub_c1 le1, @V l2 u2 lb_c2 ub_c2 le2 =>
      if le'_dec u1 l2 then true_itv else
      if ~~ le'_dec l1 u2 then false_itv else
        unknown_bool
  end.

Lemma le_itv_mor : Proper (eq ==> eq ==> eq) le_itv.
Proof.
unfold le_itv; intros x1 x2 Hx y1 y2 Hy.
destruct x1, x2; [|by inversion Hx|by inversion Hx|by apply eq_refl].
destruct y1, y2; [|by inversion Hy|by inversion Hy|by apply eq_refl].
destruct (le'_dec ub lb1), (le'_dec ub0 lb2)
; [ by apply eq_refl
  | elim f; inversion Hx; inversion Hy; subst
    ; apply le'_trans with ub; [by auto using le'_refl, eq'_sym|]
    ; apply le'_trans with lb1; by auto using le'_refl, eq'_sym
  | elim f; inversion Hx; inversion Hy; subst
    ; apply le'_trans with ub0; [by auto using le'_refl, eq'_sym|]
    ; apply le'_trans with lb2; by auto using le'_refl, eq'_sym |].
destruct (le'_dec lb ub1), (le'_dec lb0 ub2); s
; [ by apply eq_refl
  | elim f1; inversion Hx; inversion Hy; subst
    ; apply le'_trans with lb; [by auto using le'_refl, eq'_sym|]
    ; apply le'_trans with ub1; by auto using le'_refl, eq'_sym
  | elim f1; inversion Hx; inversion Hy; subst
    ; apply le'_trans with lb0; [by auto using le'_refl, eq'_sym|]
    ; apply le'_trans with ub2; by auto using le'_refl, eq'_sym
  | by apply eq_refl ].
Qed.

Lemma cor_le1 :
  forall z1 z2 i1 i2 (Hle : (z1 <= z2)%Z) (Hz1 : gamma z1 i1) (Hz2 : gamma z2 i2),
    gamma 1 (le_itv i1 i2).
Proof.
i; unfold le_itv.
destruct i1; [destruct i2|]; s; [|by inversion Hz2|by inversion Hz1].
dest_if_dec; [|dest_if_dec].
- by apply true_itv_prop.
- inversion Hz1; inversion Hz2; subst.
  elim f0.
  eapply le'_trans; [by apply Hle2|].
  eapply le'_trans; [|by apply Hle5].
  by constructor.
- by apply unknown_bool_prop1.
Qed.

Lemma cor_le0 :
  forall z1 z2 i1 i2 (Hle : ~ (z1 <= z2)%Z) (Hz1 : gamma z1 i1) (Hz2 : gamma z2 i2),
    gamma 0 (le_itv i1 i2).
Proof.
i; unfold le_itv.
destruct i1; [destruct i2|]; s; [|by inversion Hz2|by inversion Hz1].
dest_if_dec; [|dest_if_dec].
- inversion Hz1; inversion Hz2; subst.
  assert (le' (Int z1) (Int z2)) as Hinv; [|by inversion Hinv].
  eapply le'_trans; [by apply Hle3|].
  eapply le'_trans; [by apply l|by auto].
- by apply false_itv_prop.
- by apply unknown_bool_prop0.
Qed.

Definition gt_itv (x y : t) : t := lt_itv y x.

Lemma gt_itv_mor : Proper (eq ==> eq ==> eq) gt_itv.
Proof. unfold gt_itv. intros x1 x2 Hx y1 y2 Hy. by apply lt_itv_mor. Qed.

Definition ge_itv (x y : t) : t := le_itv y x.

Lemma ge_itv_mor : Proper (eq ==> eq ==> eq) ge_itv.
Proof. unfold ge_itv. intros x1 x2 Hx y1 y2 Hy. by apply le_itv_mor. Qed.

Definition not_itv (x : t) : t :=
  if eq_dec x Bot then Bot else
  if eq_dec x false_itv then true_itv else
  if le_dec false_itv x then unknown_bool else
    false_itv.

Lemma not_itv_prop1 :
  forall z i (Hz : z <> 0%Z) (Hi : gamma z i), gamma 0 (not_itv i).
Proof.
i. unfold not_itv.
destruct (eq_dec i Bot)
; [| destruct (eq_dec i false_itv); [|destruct (le_dec false_itv i)] ].
- inversion Hi; subst. by inversion e.
- inversion Hi; subst. inversion e; subst.
  assert (eq' (Int z) (Int 0)) as Hinv; [|inversion Hinv; omega].
  apply le'_antisym.
  + eapply le'_trans; [by apply Hle2|by apply le'_refl].
  + eapply le'_trans; [by apply le'_refl, Hlb|by apply Hle1].
- constructor; constructor; omega.
- constructor; constructor; omega.
Qed.

Lemma not_itv_prop2 : forall i (Hi : gamma 0 i), gamma 1 (not_itv i).
Proof.
i. unfold not_itv.
destruct (eq_dec i Bot)
; [| destruct (eq_dec i false_itv); [|destruct (le_dec false_itv i)] ].
- inversion Hi; subst. by inversion e.
- constructor; by apply le'_refl, eq'_refl.
- constructor; constructor; omega.
- elim f1. inversion Hi; subst. constructor; by auto.
Qed.

Lemma not_itv_mor : Proper (eq ==> eq) not_itv.
Proof.
unfold not_itv; intros x y Heq.
destruct (eq_dec x Bot), (eq_dec y Bot)
; [ by apply eq_refl
  | elim f; by eauto using eq_trans, eq_sym
  | elim f; by eauto using eq_trans, eq_sym |].
destruct (eq_dec x false_itv), (eq_dec y false_itv)
; [ by apply eq_refl
  | elim f1; by eauto using eq_trans, eq_sym
  | elim f1; by eauto using eq_trans, eq_sym |].
destruct (le_dec false_itv x), (le_dec false_itv y)
; [ by apply eq_refl
  | elim f3; by eauto using le_trans, le_refl, eq_sym
  | elim f3; by eauto using le_trans, le_refl, eq_sym |].
by apply eq_refl.
Qed.

Definition unknown_binary (x y : t) : t :=
  if eq_dec x Bot ||| eq_dec y Bot then Bot else top.

Lemma unknown_binary_prop :
  forall z x y (Hx : ~ eq x bot) (Hy : ~ eq y bot), gamma z (unknown_binary x y).
Proof.
i. unfold unknown_binary.
dest_if_dec; [destruct o; tauto|by apply cor_itv_top].
Qed.

Lemma unknown_binary_mor : Proper (eq ==> eq ==> eq) unknown_binary.
Proof.
unfold unknown_binary; intros x1 x2 Hx y1 y2 Hy.
destruct (eq_dec x1 Bot), (eq_dec x2 Bot).
- destruct (eq_dec y1 Bot), (eq_dec y2 Bot).
  + by apply eq_refl.
  + elim f. eapply eq_trans; [|by apply e1]. by apply eq_sym.
  + elim f; eapply eq_trans; [by apply Hy|by auto].
  + by apply eq_refl.
- elim f; eapply eq_trans; [|by apply e]. by apply eq_sym.
- elim f; eapply eq_trans; [by apply Hx|by auto].
- destruct (eq_dec y1 Bot), (eq_dec y2 Bot).
  + by apply eq_refl.
  + elim f1. eapply eq_trans; [|by apply e]. by apply eq_sym.
  + elim f1; eapply eq_trans; [by apply Hy|by auto].
  + by apply eq_refl.
Qed.

Definition unknown_unary (x : t) : t := if eq_dec x Bot then Bot else top.

Lemma unknown_unary_prop : forall z i (Hi : ~ eq i Bot), gamma z (unknown_unary i).
Proof.
i. unfold unknown_unary.
destruct (eq_dec i Bot); [by auto|by apply cor_itv_top].
Qed.

Lemma unknown_unary_mor : Proper (eq ==> eq) unknown_unary.
Proof.
unfold unknown_unary; intros x1 x2 Hx.
destruct (eq_dec x1 Bot), (eq_dec x2 Bot).
- by apply eq_refl.
- elim f. apply eq_trans with x1; by auto using eq_sym.
- elim f. apply eq_trans with x2; by auto using eq_sym.
- by apply eq_refl.
Qed.

Definition l_shift_itv (x y : t) : t := unknown_binary x y.

Lemma l_shift_itv_mor : Proper (eq ==> eq ==> eq) l_shift_itv.
Proof. by apply unknown_binary_mor. Qed.

Definition r_shift_itv (x y : t) : t := unknown_binary x y.

Lemma r_shift_itv_mor : Proper (eq ==> eq ==> eq) r_shift_itv.
Proof. by apply unknown_binary_mor. Qed.

Definition b_xor_itv (x y : t) : t := unknown_binary x y.

Lemma b_xor_itv_mor : Proper (eq ==> eq ==> eq) b_xor_itv.
Proof. by apply unknown_binary_mor. Qed.

Definition b_or_itv (x y : t) : t := unknown_binary x y.

Lemma b_or_itv_mor : Proper (eq ==> eq ==> eq) b_or_itv.
Proof. by apply unknown_binary_mor. Qed.

Definition b_and_itv (x y : t) : t := unknown_binary x y.

Lemma b_and_itv_mor : Proper (eq ==> eq ==> eq) b_and_itv.
Proof. by apply unknown_binary_mor. Qed.

Definition mod_itv (x y : t) : t := unknown_binary x y.

Lemma mod_itv_mor : Proper (eq ==> eq ==> eq) mod_itv.
Proof. by apply unknown_binary_mor. Qed.

Definition b_not_itv (x : t) : t := unknown_unary x.

Lemma b_not_itv_mor : Proper (eq ==> eq) b_not_itv.
Proof. by apply unknown_unary_mor. Qed.

Local Close Scope sumbool.

End Itv.
