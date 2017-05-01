(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
Require Import vgtac.
Require Import Relations Morphisms.
Require Import VocabA.
Require Import Monad.
Require Import DLat DPow DProd.

Set Implicit Arguments.

Module Make (Loc : KEY) (PowLoc : POW Loc) <: LAT.

Include Prod2 PowLoc PowLoc.

Inductive access_mode := DEF | USE | ALL.

Definition defof : t -> PowLoc.t := fst.

Definition useof : t -> PowLoc.t := snd.

Definition accessof (a : t) : PowLoc.t := PowLoc.join (defof a) (useof a).

Lemma accessof_mor' : Morphisms.Proper (le ==> PowLoc.le) accessof.
Proof.
unfold le, accessof; intros a1 a2 [Ha1 Ha2].
by apply PowLoc.join_le.
Qed.

Lemma accessof_mor : Morphisms.Proper (eq ==> PowLoc.eq) accessof.
Proof.
intros a1 a2 Ha; apply PowLoc.le_antisym.
- apply accessof_mor'; by apply le_refl.
- apply accessof_mor'; apply le_refl; by apply eq_sym.
Qed.

Lemma accessof_left : forall x y, PowLoc.le x (accessof (x, y)).
Proof. unfold accessof; s; i. by apply PowLoc.join_left. Qed.

Lemma accessof_right : forall x y, PowLoc.le y (accessof (x, y)).
Proof. unfold accessof; s; i. by apply PowLoc.join_right. Qed.

Lemma mem_accessof_left :
  forall l x y (Hx : PowLoc.mem l x), PowLoc.mem l (accessof (x, y)).
Proof.
i; eapply PowLoc.le_mem_true; [|by apply Hx].
by apply accessof_left.
Qed.

Lemma mem_accessof_right :
  forall l x y (Hy : PowLoc.mem l y), PowLoc.mem l (accessof (x, y)).
Proof.
i; eapply PowLoc.le_mem_true; [|by apply Hy].
by apply accessof_right.
Qed.

Definition empty : t := bot.

Definition add (m : access_mode) (l : PowLoc.elt) (a : t) : t :=
  match m with
    | DEF => (PowLoc.add l (defof a), useof a)
    | USE => (defof a, PowLoc.add l (useof a))
    | ALL => (PowLoc.add l (defof a), PowLoc.add l (useof a))
  end.

Lemma add_mor :
  forall m, Proper (Loc.eq ==> eq ==> eq) (add m).
Proof.
intros m l1 l2 Hl a1 a2 Ha; destruct m; split; s.
- apply PowLoc.add_mor; [by apply Hl|by apply Ha].
- by apply Ha.
- by apply Ha.
- apply PowLoc.add_mor; [by apply Hl|by apply Ha].
- apply PowLoc.add_mor; [by apply Hl|by apply Ha].
- apply PowLoc.add_mor; [by apply Hl|by apply Ha].
Qed.

Definition add_set (m : access_mode) (ls : PowLoc.t) (a : t) : t :=
  match m with
    | DEF => (PowLoc.join (defof a) ls, useof a)
    | USE => (defof a, PowLoc.join (useof a) ls)
    | ALL => (PowLoc.join (defof a) ls, PowLoc.join (useof a) ls)
  end.

Definition singleton (m : access_mode) (l : PowLoc.elt) : t :=
  match m with
    | DEF => pair (PowLoc.singleton l) PowLoc.empty
    | USE => pair PowLoc.empty (PowLoc.singleton l)
    | ALL => pair (PowLoc.singleton l) (PowLoc.singleton l)
  end.

Definition from_set (m : access_mode) (ls : PowLoc.t) : t :=
  match m with
    | DEF => (ls, PowLoc.empty)
    | USE => (PowLoc.empty, ls)
    | ALL => (ls, ls)
  end.

Definition mem (l : PowLoc.elt) (a : t) : bool :=
  (PowLoc.mem l (defof a) || PowLoc.mem l (useof a))%bool.

Definition remove (l : PowLoc.elt) (a : t) : t :=
  (PowLoc.remove l (defof a), PowLoc.remove l (useof a)).

Definition remove_set (ls : PowLoc.t) (a : t) : t :=
  (PowLoc.diff (defof a) ls, PowLoc.diff (useof a) ls).

Definition add_list (m : access_mode) (ls : list PowLoc.elt) (a : t) : t :=
  list_fold (add m) ls a.

Definition union (a b : t) : t :=
  (PowLoc.join (defof a) (defof b), PowLoc.join (useof a) (useof b)).

Definition restrict (ls : PowLoc.t) (a : t) : t :=
  (PowLoc.meet (defof a) ls, PowLoc.meet (useof a) ls).

Definition filter_out (ls : PowLoc.t) (a : t) : t :=
  (PowLoc.diff (defof a) ls, PowLoc.diff (useof a) ls).

Lemma defof_monotone :
  forall a1 a2 (Hle : le a1 a2), PowLoc.le (defof a1) (defof a2).
Proof.
destruct a1 as [d1 u1], a2 as [d2 u2]; unfold defof, le; s; i. tauto.
Qed.

Lemma useof_monotone :
  forall a1 a2 (Hle : le a1 a2), PowLoc.le (useof a1) (useof a2).
Proof.
destruct a1 as [d1 u1], a2 as [d2 u2]; unfold useof, le; s; i. tauto.
Qed.

Lemma mem_join_false :
  forall l a1 a2 (Hjoin : PowLoc.mem l (accessof (join a1 a2)) = false),
    PowLoc.mem l (accessof a1) = false /\ PowLoc.mem l (accessof a2) = false.
Proof.
unfold accessof; i.
apply PowLoc.mem_join_false in Hjoin; destruct Hjoin as [Hd Hu].
split.
- apply PowLoc.mem_join_false_inv.
  + eapply PowLoc.le_mem_false; [|by apply Hd].
    apply defof_monotone; by apply join_left.
  + eapply PowLoc.le_mem_false; [|by apply Hu].
    apply useof_monotone; by apply join_left.
- apply PowLoc.mem_join_false_inv.
  + eapply PowLoc.le_mem_false; [|by apply Hd].
    apply defof_monotone; by apply join_right.
  + eapply PowLoc.le_mem_false; [|by apply Hu].
    apply useof_monotone; by apply join_right.
Qed.

Lemma mem_join_left :
  forall l x y (Hx : PowLoc.mem l (accessof x) = true),
    PowLoc.mem l (accessof (join x y)) = true.
Proof.
i; eapply PowLoc.le_mem_true; [|apply Hx].
apply accessof_mor'; by apply join_left.
Qed.

Lemma mem_join_right :
  forall l x y (Hx : PowLoc.mem l (accessof y) = true),
    PowLoc.mem l (accessof (join x y)) = true.
Proof.
i; eapply PowLoc.le_mem_true; [|apply Hx].
apply accessof_mor'; by apply join_right.
Qed.

Lemma le_mem_false :
  forall l acc acc' (Hle : le acc acc')
         (Hmem : PowLoc.mem l (accessof acc') = false),
    PowLoc.mem l (accessof acc) = false.
Proof.
i; eapply PowLoc.le_mem_false; [|by apply Hmem].
by apply accessof_mor'.
Qed.

Lemma le_mem_true :
  forall l acc acc' (Hle : le acc acc')
         (Hmem : PowLoc.mem l (accessof acc) = true),
    PowLoc.mem l (accessof acc') = true.
Proof.
i; eapply PowLoc.le_mem_true; [|by apply Hmem].
by apply accessof_mor'.
Qed.

Lemma mem_accessof_false :
  forall l r w (Hl : PowLoc.mem l (accessof (r, w)) = false),
    PowLoc.mem l r = false /\ PowLoc.mem l w = false.
Proof. unfold accessof. by eauto using PowLoc.mem_join_false. Qed.

(* Access monad definitions *)

Module MAcc <: Monad.

Definition m (T : Type) := (T * t)%type.

Definition ret (A : Type) (x : A) := (x, bot).

Definition bind (A B : Type) (x_a : m A) (f : A -> m B) :=
  let (x, a1) := x_a in
  let (y, a2) := f x in
  (y, join a1 a2).

Definition eq (A : Type) (a_eq : relation A) (Ha_eq : zb_equiv a_eq)
           (x y : m A) :=
  let (x_v, x_acc) := x in
  let (y_v, y_acc) := y in
  a_eq x_v y_v /\ Make.eq x_acc y_acc.

Definition eq_equiv :
  forall A (a_eq : relation A) (Ha_eq : zb_equiv a_eq),
    zb_equiv (eq Ha_eq).
Proof.
constructor.
- destruct x as [x acc]; unfold eq.
  split; [by apply (zb_equiv_refl Ha_eq)|by apply Make.eq_refl].
- destruct x as [x xacc], y as [y yacc]; unfold eq; intros [Hxy Hacc].
  split; [by apply (zb_equiv_sym Ha_eq)|by apply Make.eq_sym].
- destruct x as [x xacc], y as [y yacc], z as [z zacc]; unfold eq
  ; intros [Hxy Hxyacc] [Hyz Hyzacc]; split.
  + eapply (zb_equiv_trans Ha_eq); [by apply Hxy|by apply Hyz].
  + eapply Make.eq_trans; [by apply Hxyacc|by apply Hyzacc].
Qed.

Lemma right_unit :
  forall A (a_eq : relation A) (Ha_eq : zb_equiv a_eq) (a : m A),
    eq Ha_eq a (bind a (@ret A)).
Proof.
i; destruct a; split; [by apply (zb_equiv_refl Ha_eq)|by apply join_bot].
Qed.

Lemma left_unit :
  forall A B (b_eq : relation B) (Hb_eq : zb_equiv b_eq) (a : A) (f : A -> m B),
    eq Hb_eq (f a) (bind (ret a) f).
Proof.
unfold bind, ret, eq; i; destruct (f a).
split; [by apply (zb_equiv_refl Hb_eq)|].
eapply Make.eq_trans; [by apply join_bot|by apply join_comm_eq].
Qed.

Lemma assoc :
  forall A B C (c_eq : relation C) (Hc_eq : zb_equiv c_eq)
         (ma : m A) (f : A -> m B) (g : B -> m C),
    eq Hc_eq (bind ma (fun x => bind (f x) g)) (bind (bind ma f) g).
Proof.
unfold bind, ret, eq; i.
destruct ma as [x xacc], (f x) as [v1 vacc1], (g v1) as [v2 vacc2]; split.
- by apply (zb_equiv_refl Hc_eq).
- by apply join_assoc.
Qed.

Definition le A (a_eq a_le : relation A) (Ha_le : zb_order a_eq a_le)
           (x y : m A) :=
  let (x_v, x_acc) := x in
  let (y_v, y_acc) := y in
  a_le x_v y_v /\ Make.le x_acc y_acc.

Definition le_order :
  forall A (a_eq a_le : relation A) (Ha_eq : zb_equiv a_eq)
         (Ha_le : zb_order a_eq a_le),
    zb_order (eq Ha_eq) (le Ha_le).
Proof.
unfold eq, le; constructor; i.
- destruct x, y, Heq as [Heq Hacceq]. split.
  + by apply (zb_order_refl Ha_le).
  + by apply Make.le_refl.
- destruct x, y, le1 as [le1 accle1], le2 as [le2 accle2]. split.
  + by apply (zb_order_antisym Ha_le).
  + by apply Make.le_antisym.
- destruct x, y, z, le1 as [le1 accle1], le2 as [le2 accle2]. split.
  + eapply (zb_order_trans Ha_le); [by apply le1|by apply le2].
  + eapply Make.le_trans; [by apply accle1|by apply accle2].
Qed.

Lemma le_1 :
  forall A B (a_eq a_le : relation A) (Ha_le : zb_order a_eq a_le)
         x (y : m B) f (Hf : forall v, le Ha_le x (f v)),
    le Ha_le x (bind y f).
Proof.
unfold bind. i.
destruct x as [vx accx], y as [vy accy].
assert (Hf' := Hf vy). destruct (f vy) as [vf accf].
destruct Hf' as [Hf' Haccf']. split.
- by auto.
- eapply Make.le_trans; [by apply Haccf'|by apply Make.join_right].
Qed.

Lemma le_2 :
  forall A (a_eq a_le : relation A) (Ha_le : zb_order a_eq a_le)
         x f (Hf : forall v, le Ha_le (ret v) (f v)),
    le Ha_le x (bind x f).
Proof.
unfold bind, ret. i.
destruct x as [vx accx].
assert (Hf' := Hf vx). destruct (f vx) as [vf accf].
destruct Hf' as [Hf' Haccf']. split.
- by auto.
- by apply Make.join_left.
Qed.

Lemma le_3 :
  forall A (a_eq a_le : relation A) (Ha_le : zb_order a_eq a_le)
         x f y (Hx : le Ha_le x y)
         (He : forall v (Hv : le Ha_le (ret v) y), le Ha_le (f v) y),
    le Ha_le (bind x f) y.
Proof.
unfold bind. i.
destruct x as [vx accx], y as [vy accy].
assert (He' := He vx). destruct (f vx) as [vf accf].
split.
- apply He'. split; [by apply Hx|by apply bot_prop].
- apply join_lub.
  + by apply Hx.
  + apply He'. split; [by apply Hx|by apply bot_prop].
Qed.

Lemma bind_mono :
  forall A (a_eq a_le : relation A) (Ha_le : zb_order a_eq a_le)
         B (b_eq b_le : relation B) (Hb_le : zb_order b_eq b_le),
    Proper (le Ha_le ==> (a_le ==> le Hb_le) ==> le Hb_le)
           (bind (A := A) (B := B)).
Proof.
i. intros [x1 acc1] [x2 acc2] [Hx Haccx] f1 f2 Hf. unfold bind.
assert (Hf' := Hf x1 x2 Hx).
remember (f1 x1) as v1. destruct v1 as [v1 accv1].
remember (f2 x2) as v2. destruct v2 as [v2 accv2].
destruct Hf' as [Hf' Haccf']. split; [by auto|apply join_le; by auto].
Qed.

Lemma ret_mono :
  forall A (a_eq a_le : relation A) (Ha_le : zb_order a_eq a_le),
    Proper (a_le ==> le Ha_le) (ret (A := A)).
Proof.
i. intros x1 x2 Hx. split; [by auto|apply Make.le_refl; by apply Make.eq_refl].
Qed.

Lemma ret_join_lub :
  forall A (a_eq a_le : relation A) (Ha_le : zb_order a_eq a_le)
         x y z (Hx : le Ha_le (ret x) z) (Hy : le Ha_le (ret y) z) join
         (Hjoin_lub :
            forall x y z (Hx : a_le x z) (Hy : a_le y z), a_le (join x y) z),
    le Ha_le (ret (join x y)) z.
Proof.
unfold le, ret; i. destruct z as [z_v z_acc].
split; [|by apply bot_prop].
apply Hjoin_lub; [by apply Hx|by apply Hy].
Qed.

End MAcc.

Definition get_v T (x : MAcc.m T) : T := fst x.

Definition get_acc T (x : MAcc.m T) : t := snd x.

Lemma get_acc_mono
      T (teq : relation T) (tle : relation T) (Ht : zb_order teq tle) :
  forall x y (Hle : MAcc.le Ht x y), le (get_acc x) (get_acc y).
Proof. unfold MAcc.le; destruct x, y. s; intros [_ Hle]; by auto. Qed.

Definition mono T T' U f :=
  forall (va : MAcc.m T) (va' : MAcc.m T') (e : U) (Happ : va' = f va e),
    le (get_acc va) (get_acc va').

Lemma mono_list T U f :
  forall (es : list U) (va va': MAcc.m T) (Hfmono : mono f)
         (Hfold : va' = List.fold_left f es va),
    le (get_acc va) (get_acc va').
Proof.
induction es; i.
- inversion Hfold. apply le_refl; by apply eq_refl.
- simpl in Hfold.
  eapply le_trans; [eapply Hfmono; reflexivity|].
  eapply IHes; by eauto.
Qed.

Definition mono2 T T' U U' f :=
  forall (e1 : U) (e2 : U') (va : MAcc.m T) (va' : MAcc.m T')
         (Happ : va' = f e1 e2 va),
    le (get_acc va) (get_acc va').

Lemma mono2_list T U U' f :
  forall (es1 : list U) (es2 : list U') (va va' : MAcc.m T) (Hfmono : mono2 f)
         (Hfold : va' = VocabA.list_fold2 f es1 es2 va),
    le (get_acc va) (get_acc va').
Proof.
induction es1; destruct es2; i.
- inversion Hfold. apply le_refl; by apply eq_refl.
- inversion Hfold. apply le_refl; by apply eq_refl.
- inversion Hfold. apply le_refl; by apply eq_refl.
- simpl in Hfold.
  eapply le_trans; [eapply Hfmono; reflexivity|].
  eapply IHes1; by eauto.
Qed.

End Make.
