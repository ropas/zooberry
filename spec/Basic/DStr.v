(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** Concrete key: string.  *)

Set Implicit Arguments.

Require Import TStr DLat.

Module DStr <: KEY.
  Include String_as_OT.
  Definition eqb x y := if eq_dec x y then true else false.
  Definition zb_eq : zb_equiv eq :=
    {| zb_equiv_refl := eq_refl
     ; zb_equiv_sym := eq_sym
     ; zb_equiv_trans := eq_trans |}.
End DStr.
