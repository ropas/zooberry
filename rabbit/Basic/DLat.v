(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** Lattice signature. *)

Set Implicit Arguments.

Require Import Relations.
Require OrderedType.
Require Import vgtac.

Record zb_equiv A (a_eq : relation A) :=
  { zb_equiv_refl : forall (x : A), a_eq x x;
    zb_equiv_sym : forall (x y : A) (Heq : a_eq x y), a_eq y x;
    zb_equiv_trans :
      forall (x y z : A) (eq1 : a_eq x y) (eq2 : a_eq y z), a_eq x z }.

Record zb_order A (a_eq : relation A) (a_le : relation A) :=
  { zb_order_refl : forall (x y : A) (Heq : a_eq x y), a_le x y;
    zb_order_antisym :
      forall (x y : A) (le1 : a_le x y) (le2 : a_le y x), a_eq x y;
    zb_order_trans :
      forall (x y z : A) (le1 : a_le x y) (le2 : a_le y z), a_le x z }.

Lemma logic_zb_eq T : @zb_equiv T Logic.eq.
Proof. constructor; i; subst; by auto. Qed.

(** KEY module type is replaced by Coq.Structures.OrderedType. *)

Module Type KEY.
  Include OrderedType.OrderedType.
  Parameter eqb : t -> t -> bool.
  Parameter zb_eq : zb_equiv eq.
End KEY.

Module Type LAT_EQUIV.
  Parameter t : Type.
  Parameter eq : t -> t -> Prop.
  Parameter eq_refl : forall (x : t), eq x x.
  Parameter eq_sym : forall (x y : t) (Heq : eq x y), eq y x.
  Parameter eq_trans :
    forall (x y z : t) (eq1 : eq x y) (eq2 : eq y z), eq x z.
End LAT_EQUIV.

Module Type LAT_ORDER (E : LAT_EQUIV).
  Parameter le : E.t -> E.t -> Prop.
  Parameter le_refl : forall (x y : E.t) (Heq : E.eq x y), le x y.
  Parameter le_antisym :
    forall (x y : E.t) (le1 : le x y) (le2 : le y x), E.eq x y.
  Parameter le_trans :
    forall (x y z : E.t) (le1 : le x y) (le2 : le y z), le x z.
End LAT_ORDER.

Module Type LAT_CORE.
  Include LAT_EQUIV.
  Include LAT_ORDER.

  Parameter le_dec : forall (x y : t), {le x y} + {~ le x y}.
  Parameter eq_dec : forall (x y : t), {eq x y} + {~ eq x y}.

  Parameter bot : t.
  Parameter bot_prop : forall (x : t), le bot x.

  Parameter join : t -> t -> t.
  Parameter join_left : forall (x y : t), le x (join x y).
  Parameter join_right : forall (x y : t), le y (join x y).
  Parameter join_lub : forall (x y u : t) (Hx : le x u) (Hy : le y u), le (join x y) u.

  Parameter meet : t -> t -> t.
  Parameter meet_left : forall (x y : t), le (meet x y) x.
  Parameter meet_right : forall (x y : t), le (meet x y) y.
  Parameter meet_glb : forall (x y l : t) (Hx : le l x) (Hy : le l y), le l (meet x y).

  Parameter widen : t -> t -> t.
  Parameter narrow : t -> t -> t.
End LAT_CORE.

Module Type LAT.
  Include LAT_CORE.

  Parameter leb : t -> t -> bool.
  Parameter eqb : t -> t -> bool.

  Parameter zb_eq : zb_equiv eq.
  Parameter zb_ord : zb_order eq le.

  Parameter join_comm_le : forall (x y : t), le (join x y) (join y x).
  Parameter join_comm_eq : forall (x y : t), eq (join x y) (join y x).
  Parameter join_le : forall (x y x' y': t) (Hx : le x x') (Hy : le y y'), le (join x y) (join x' y').
  Parameter join_eq : forall (x y x' y': t) (Hx : eq x x') (Hy : eq y y'), eq (join x y) (join x' y').
  Parameter join_le_idem : forall (x y : t) (Hle : le x y), eq y (join x y).
  Parameter join_idem : forall (x : t), eq x (join x x).
  Parameter join_bot : forall (x : t), eq x (join x bot).

  Parameter meet_comm_le : forall (x y : t), le (meet x y) (meet y x).
  Parameter meet_comm_eq : forall (x y : t), eq (meet x y) (meet y x).
  Parameter meet_le : forall (x y x' y': t) (Hx : le x x') (Hy : le y y'), le (meet x y) (meet x' y').
  Parameter meet_eq : forall (x y x' y': t) (Hx : eq x x') (Hy : eq y y'), eq (meet x y) (meet x' y').
  Parameter meet_le_idem : forall (x y : t) (Hle : le x y), eq x (meet x y).
  Parameter meet_idem : forall (x : t), eq x (meet x x).
  Parameter meet_bot : forall (x : t), eq bot (meet x bot).
End LAT.

Module JoinMeetProp (Import A : LAT_CORE).

Load JoinMeetCommon.
  
End JoinMeetProp.

Inductive pair_eq T U (t_eq : T -> T -> Prop) (u_eq : U -> U -> Prop)
  : ((T * U) -> (T * U) -> Prop)%type :=
| pair_eq_intro :
    forall (x1 x2 : T) (Hx : t_eq x1 x2)
       (y1 y2 : U) (Hy : u_eq y1 y2),
      pair_eq t_eq u_eq (x1, y1) (x2, y2).

Lemma pair_eq_refl
      T (t_eq : T -> T -> Prop) (Hteq : zb_equiv t_eq)
      U (u_eq : U -> U -> Prop) (Hueq : zb_equiv u_eq) :
  forall  x, pair_eq t_eq u_eq x x.
Proof.
destruct x. constructor.
- by apply (zb_equiv_refl Hteq).
- by apply (zb_equiv_refl Hueq).
Qed.
