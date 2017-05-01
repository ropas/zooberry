(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
Definition leb (x y : t) := if le_dec x y then true else false.

Definition eqb (x y : t) := if eq_dec x y then true else false.

Definition zb_eq : zb_equiv eq :=
  {| zb_equiv_refl := eq_refl
   ; zb_equiv_sym := eq_sym
   ; zb_equiv_trans := eq_trans |}.

Definition zb_ord : zb_order eq le :=
  {| zb_order_refl := le_refl
   ; zb_order_antisym := le_antisym
   ; zb_order_trans := le_trans |}.

Definition join_comm_le : forall (x y : t), le (join x y) (join y x).
Proof. auto using join_lub, join_left, join_right. Qed.

Definition join_comm_eq : forall (x y : t), eq (join x y) (join y x).
Proof. auto using le_antisym, join_comm_le. Qed.

Definition join_le : forall (x y x' y': t) (Hx : le x x') (Hy : le y y'), le (join x y) (join x' y').
Proof. eauto using le_trans, join_lub, join_left, join_right. Qed.

Definition join_eq : forall (x y x' y': t) (Hx : eq x x') (Hy : eq y y'), eq (join x y) (join x' y').
Proof. auto using le_antisym, le_refl, join_le, eq_sym. Qed.

Definition join_le_idem : forall (x y : t) (Hle : le x y), eq y (join x y).
Proof.
auto using le_antisym, join_left, join_right, join_lub, le_refl, eq_refl.
Qed.

Definition join_idem : forall (x : t), eq x (join x x).
Proof.
auto using le_antisym, join_left, join_right, join_lub, le_refl, eq_refl.
Qed.

Definition join_bot : forall (x : t), eq x (join x bot).
Proof.
auto using le_antisym, join_left, join_right, join_lub, le_refl, eq_refl, bot_prop.
Qed.

Lemma join_assoc : forall x y z,
eq (join x (join y z)) (join (join x y) z).
Proof.
i. apply le_antisym.
- apply join_lub; [|apply join_lub].
  + eapply le_trans; [apply join_left|apply join_left].
  + eapply le_trans; [apply join_right|apply join_left].
  + apply join_right.
- apply join_lub; [apply join_lub|].
  + apply join_left.
  + eapply le_trans; [apply join_left|apply join_right].
  + eapply le_trans; [apply join_right|apply join_right].
Qed.

Definition meet_comm_le : forall (x y : t), le (meet x y) (meet y x).
Proof. auto using meet_glb, meet_left, meet_right. Qed.

Definition meet_comm_eq : forall (x y : t), eq (meet x y) (meet y x).
Proof. auto using le_antisym, meet_comm_le. Qed.

Definition meet_le : forall (x y x' y': t) (Hx : le x x') (Hy : le y y'), le (meet x y) (meet x' y').
Proof. eauto using le_trans, meet_glb, meet_left, meet_right. Qed.

Definition meet_eq : forall (x y x' y': t) (Hx : eq x x') (Hy : eq y y'), eq (meet x y) (meet x' y').
Proof. auto using le_antisym, le_refl, meet_le, eq_sym. Qed.

Definition meet_le_idem : forall (x y : t) (Hle : le x y), eq x (meet x y).
Proof.
auto using le_antisym, meet_left, meet_right, meet_glb, le_refl, eq_refl.
Qed.

Definition meet_idem : forall (x : t), eq x (meet x x).
Proof.
auto using le_antisym, meet_left, meet_right, meet_glb, le_refl, eq_refl.
Qed.

Definition meet_bot : forall (x : t), eq bot (meet x bot).
Proof.
auto using le_antisym, meet_left, meet_right, meet_glb, le_refl, eq_refl, bot_prop.
Qed.

Lemma meet_assoc : forall x y z,
eq (meet x (meet y z)) (meet (meet x y) z).
Proof.
i. apply le_antisym.
- apply meet_glb; [apply meet_glb|].
  + apply meet_left.
  + eapply le_trans; [apply meet_right|apply meet_left].
  + eapply le_trans; [apply meet_right|apply meet_right].
- apply meet_glb; [|apply meet_glb].
  + eapply le_trans; [apply meet_left|apply meet_left].
  + eapply le_trans; [apply meet_left|apply meet_right].
  + apply meet_right.
Qed.
