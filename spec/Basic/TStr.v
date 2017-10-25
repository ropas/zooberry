(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** String Module as an Ordered Type.  *)

Set Implicit Arguments.

(** We use nat type to represent String type in Coq.  The nat type
will be extracted to string type of OCaml. *)

Require Import OrderedType OrderedTypeEx.
Require Extraction.

Axiom string_t : Type.
Extract Constant string_t => "string".

Module String_as_OT <: OrderedType.
  Definition t : Type := string_t.

  Definition eq : t -> t -> Prop := Logic.eq.

  Axiom lt : t -> t -> Prop.

  Lemma eq_refl : forall x : t, eq x x.
  Proof. intro. reflexivity. Qed.

  Lemma eq_sym : forall x y : t, eq x y -> eq y x.
  Proof. intros. symmetry. assumption. Qed.

  Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof. intros. rewrite H. assumption. Qed.

  Axiom lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.

  Axiom lt_not_eq : forall x y : t, lt x y -> ~ eq x y.

  Axiom compare : forall x y : t, OrderedType.Compare lt eq x y.

  Extract Constant compare =>
"fun x y ->
  let c = compare x y in
  if c = 0 then OrderedType.EQ else
  if c < 0 then OrderedType.LT else
  OrderedType.GT".

  Axiom eq_dec : forall x y : t, {eq x y} + {~ eq x y}.

  Extract Constant eq_dec => "(=)".
End String_as_OT.
