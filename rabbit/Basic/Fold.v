(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
Set Implicit Arguments.

Require Import Morphisms.
Require Import vgtac.
Require Import Monad.
Require Import DLat DPow.

Module Type FOLDABLE (A : KEY).

Axiom t : Type.

Axiom empty : t.

Axiom mem : A.t -> t -> bool.

Axiom empty_1 : forall e, mem e empty = false.

Axiom add : A.t -> t -> t.

Axiom mem_add_1 : forall l1 l2 s (Hl : A.eq l1 l2), mem l1 (add l2 s) = true.

Axiom mem_add_2 :
  forall l1 l2 s (Hl : not (A.eq l1 l2)), mem l1 (add l2 s) = mem l1 s.

Axiom fold : forall T (f : A.t -> T -> T) (s : t) (init : T), T.

Axiom fold_1 :
  forall (T : Type) (P : T -> Prop) f e s (Hmem : mem e s = true)
     (He : forall (x : T), P (f e x))
     (Hf_mono : forall e' (x : T) (Hx : P x), P (f e' x))
     (Hf_eq : forall e1 e2 (He1 : A.eq e1 e2) (x : T) (He1 : P (f e1 x)),
         P (f e2 x))
     (x : T),
    P (fold f s x).

Axiom fold_3  :
  forall (T : Type) (P : T -> Prop) f s
     (Hf_mono : forall e x (He : mem e s = true) (Hx : P x), P (f e x))
     (x : T) (Hx : P x),
    P (fold f s x).

Axiom fold2_1 :
  forall T (P : T -> T -> Prop) (P_trans : forall x y z, P x y -> P y z -> P x z)
         f f' i
         (Hf_ext : forall e x, P x (f e x))
         (Hff' : forall e x1 x2 (Hi : P i x1) (Hx : P x1 x2),
                   P (f e x1) (f' e x2))
         s (x1 x2 : T) (Hi : P i x1) (Hx : P x1 x2),
    P (fold f s x1) (fold f' s x2).

End FOLDABLE.

Module SetMap (K1 : KEY) (A : FOLDABLE K1) (K2 : KEY) (B : FOLDABLE K2).

Definition map f s := A.fold (fun e acc => B.add (f e) acc) s B.empty.

Lemma map_1 :
  forall f s e (Hf: Proper (K1.eq ==> K2.eq) f) (Hmem : A.mem e s = true),
    B.mem (f e) (map f s) = true.
Proof.
i. unfold map. eapply A.fold_1.
- apply Hmem.
- i. apply B.mem_add_1. apply K2.eq_refl.
- i. elim (K2.eq_dec (f e) (f e')); i.
  + by apply B.mem_add_1.
  + rewrite B.mem_add_2; by auto.
- i. elim (K2.eq_dec (f e) (f e2)); i.
  + apply B.mem_add_1. by auto.
  + rewrite B.mem_add_2; [|by auto].
    rewrite B.mem_add_2 in He0; [by auto|].
    intro. elim b. apply K2.eq_trans with (f e1); [by auto|by apply Hf].
Qed.

Lemma map_diff :
  forall f s e (Hf : forall e', ~ K2.eq e (f e')), B.mem e (map f s) = false.
Proof.
i. unfold map. eapply A.fold_3; [|by apply B.empty_1].
i. rewrite B.mem_add_2; [by auto|].
intro Hinv. eapply Hf. by apply Hinv.
Qed.

End SetMap.

Module BigJoin (K : KEY) (A : FOLDABLE K) (B : LAT).

(* Set comprehension style 1

big_join { f e x | e \in s }

- Type of f is (Foldable.elt -> T.t -> T.t)
- T is a lattice module
*)

Definition big_join f s x :=
  A.fold (fun s acc => B.join acc (f s x)) s x.

Lemma big_join_1' :
  forall f e s x (Ha : A.mem e s = true)
         (Hf: Proper (K.eq ==> B.eq ==> B.eq) f),
    B.le (f e x) (A.fold (fun s acc => B.join acc (f s x)) s x).
Proof.
i. unfold big_join.
apply A.fold_1 with e.
- by apply Ha.
- i; by apply B.join_right.
- i; eapply B.le_trans; [by apply Hx|by apply B.join_left].
- i. eapply B.le_trans; [by apply He0|].
  apply B.join_le; [apply B.le_refl; by apply B.eq_refl|].
  apply B.le_refl. apply Hf; [by apply He1|by apply B.eq_refl].
Qed.

Lemma big_join_1 :
  forall f e s x (Ha : A.mem e s = true)
         (Hf: Proper (K.eq ==> B.eq ==> B.eq) f),
    B.le (f e x) (big_join f s x).
Proof. by apply big_join_1'. Qed.

Definition weak_big_join (f : K.t -> B.t -> B.t) s x := A.fold f s x.

Lemma weak_big_join_1' :
  forall f e s x (Ha : A.mem e s = true)
         (Hf_mono: Proper (K.eq ==> B.le ==> B.le) f)
         (Hf_ext: forall e x, B.le x (f e x)),
    B.le (f e x) (A.fold f s x).
Proof.
i. eapply B.le_trans; [apply big_join_1; [by apply Ha|]|].
- intros k1 k2 Hk v1 v2 Hv. apply B.le_antisym.
  + apply Hf_mono; by auto using B.le_refl.
  + apply Hf_mono; by auto using K.eq_sym, B.le_refl, B.eq_sym.
- unfold big_join. eapply A.fold2_1.
  + by apply B.le_trans.
  + i. by apply B.join_left.
  + i. apply B.join_lub.
    * eapply B.le_trans; [by apply Hx|].
      eapply B.le_trans; [by apply Hf_ext|].
      apply Hf_mono; [by apply K.eq_refl|apply B.le_refl; by apply B.eq_refl].
    * apply Hf_mono; [by apply K.eq_refl|].
      eapply B.le_trans; [by apply Hi|by apply Hx].
  + apply B.le_refl; by apply B.eq_refl.
  + apply B.le_refl; by apply B.eq_refl.
Qed.

Lemma weak_big_join_1 :
  forall f e s x (Ha : A.mem e s = true)
         (Hf_mono: Proper (K.eq ==> B.le ==> B.le) f)
         (Hf_ext: forall e x, B.le x (f e x)),
    B.le (f e x) (weak_big_join f s x).
Proof. by apply weak_big_join_1'. Qed.

End BigJoin.

Module BigJoinM (Import M : Monad) (K : KEY) (A : FOLDABLE K) (B : LAT).

(* Set comprehension style 1

big_join { f e x | e \in s }

- Type of f is (Foldable.elt -> T.t -> M.m T.t)
- T is a lattice module
*)

Definition big_join f s x :=
  let f' s acc :=
      do acc' <- acc;
      do v <- f s x;
      ret (B.join acc' v) in
  A.fold f' s (ret x).

Definition weak_big_join (f : K.t -> B.t -> m B.t) s x :=
  let f' s acc :=
      do acc' <- acc;
      f s acc' in
  A.fold f' s x.

Section Locs.

Lemma b_equiv : zb_equiv B.eq.
Proof.
constructor.
- intro. by apply B.eq_refl.
- intros x y. by apply B.eq_sym.
- intros x y z. by apply B.eq_trans.
Qed.

Definition eq_refl := zb_equiv_refl (eq_equiv b_equiv).

Definition eq_sym := zb_equiv_sym (eq_equiv b_equiv).

Definition eq_trans := zb_equiv_trans (eq_equiv b_equiv).

Lemma b_order : zb_order B.eq B.le.
Proof.
constructor.
- intro. by apply B.le_refl.
- intros x y. by apply B.le_antisym.
- intros x y z. by apply B.le_trans.
Qed.

Definition le_refl := zb_order_refl (le_order b_equiv b_order).

Definition le_antisym := zb_order_antisym (le_order b_equiv b_order).

Definition le_trans := zb_order_trans (le_order b_equiv b_order).

Lemma big_join_1' :
  forall f e s x (Ha : A.mem e s = true)
         (Hf : Proper (K.eq ==> B.le ==> le b_order) f),
    let f' s acc :=
        do acc' <- acc;
        do v <- f s x;
        ret (B.join acc' v) in
    le b_order (f e x) (A.fold f' s (ret x)).
Proof.
i. apply A.fold_1 with e.
- by apply Ha.
- unfold f'. i.
  apply le_1; i.
  apply le_2; i.
  apply ret_mono.
  apply B.join_right.
- i. eapply le_trans; [by apply Hx|].
  unfold f'.
  apply le_2; i.
  apply le_1; i.
  apply ret_mono.
  apply B.join_left.
- i. eapply le_trans; [by apply He0|].
  unfold f'.
  eapply bind_mono; [ apply le_refl; apply eq_refl |].
  intros v1 v2 Hv.
  eapply bind_mono
  ; [eapply Hf; [by apply He1|apply B.le_refl; by apply B.eq_refl]|].
  intros v1' v2' Hv'.
  apply ret_mono.
  apply B.join_lub.
  + eapply B.le_trans; [by apply Hv|by apply B.join_left].
  + eapply B.le_trans; [by apply Hv'|by apply B.join_right].
Qed.

Lemma big_join_1 :
  forall f e s x (Ha : A.mem e s = true)
         (Hf : Proper (K.eq ==> B.le ==> le b_order) f),
    le b_order (f e x) (big_join f s x).
Proof. by apply big_join_1'. Qed.

Lemma weak_big_join_1' :
  forall f e s x (Ha : A.mem e s = true)
         (Hf_mono : Proper (K.eq ==> B.le ==> le b_order) f)
         (Hf_ext : forall e x, le b_order (ret x) (f e x)),
    let f' s acc :=
        do acc' <- acc;
        f s acc' in
    le b_order (f e x) (A.fold f' s (ret x)).
Proof.
i. eapply le_trans; [apply big_join_1; [by apply Ha|by apply Hf_mono]|].
unfold big_join. eapply A.fold2_1.
- by apply le_trans.
- i. apply le_2; i.
  apply le_1; i.
  apply ret_mono.
  apply B.join_left.
- unfold f'. i. apply le_3.
  + apply le_trans with x2; [by auto|].
    apply le_2. by apply Hf_ext.
  + i. apply le_3.
    * eapply le_trans; [apply le_refl; by apply left_unit|].
      eapply bind_mono; [eapply le_trans; [by apply Hi|by apply Hx]|].
      apply Hf_mono. by apply K.eq_refl.
    * i. apply ret_join_lub; [by auto|by auto|by apply B.join_lub].
- apply le_refl; apply eq_refl.
- apply le_refl; apply eq_refl.
Qed.

Lemma weak_big_join_1 :
  forall f e s x (Ha : A.mem e s = true)
         (Hf_mono : Proper (K.eq ==> B.le ==> le b_order) f)
         (Hf_ext : forall e x, le b_order (ret x) (f e x)),
    le b_order (f e x) (weak_big_join f s (ret x)).
Proof. by apply weak_big_join_1'. Qed.

End Locs.

End BigJoinM.
