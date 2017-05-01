(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** Pos Module as an Ordered Type.  *)

Set Implicit Arguments.

(** We use nat type to represent Pos type in Coq.  The nat type
will be extracted to string type of OCaml. *)

Require Import OrderedType OrderedTypeEx TStr.

Axiom pos_t : Type.
Extract Constant pos_t =>
"{ pos_file : string
; pos_line : int
; pos_id : int
}".

Axiom unknown_pos : pos_t.
Extract Constant unknown_pos =>
"{ pos_file = ""__unknown_file""
 ; pos_line = -1
 ; pos_id = -1
 }".

Axiom string_of_pos : pos_t -> string_t.
Extract Constant string_of_pos =>
"fun p -> p.pos_file ^ "":"" ^ string_of_int p.pos_line".

Module Pos_as_OT <: OrderedType.
  Definition t : Type := pos_t.
  Axiom eq : t -> t -> Prop.
  Axiom lt : t -> t -> Prop.
  Axiom eq_refl : forall x : t, eq x x.
  Axiom eq_sym : forall x y : t, eq x y -> eq y x.
  Axiom eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Axiom lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Axiom lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Axiom compare : forall x y : t, OrderedType.Compare lt eq x y.
  Extract Constant compare =>
"fun x y ->
  let c = compare x.pos_id y.pos_id in
  if c = 0 then OrderedType.EQ else
  if c < 0 then OrderedType.LT else
  OrderedType.GT".
  Axiom eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Extract Constant eq_dec => 
"fun x y -> x.pos_id = y.pos_id".
End Pos_as_OT.
