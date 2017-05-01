(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** * Abstract Array Block.  *)

Set Implicit Arguments.

Require Import ZArith Morphisms.
Require Import hpattern vgtac DBin DLat DProd DMap DPow DomBasic.
Require Import VocabA.

Module ArrInfo <: LAT.

(** Abstract type of array information is unit. *)

Include Bin.

Definition make (_ : unit) : t := top.

Definition plus_offset (x : t) : t := x.

Lemma plus_offset_mor : Proper (eq ==> eq) plus_offset.
Proof. unfold plus_offset; by intros x1 x2 Hx. Qed.

Lemma plus_offset_non_bot :
  forall (x : t) (Hx : ~ eq x bot), ~ eq (plus_offset x) bot.
Proof. i; destruct x; by ss. Qed.

Definition minus_offset (x : t) : t := x.

Lemma minus_offset_mor : Proper (eq ==> eq) minus_offset.
Proof. unfold minus_offset; by intros x1 x2 Hx. Qed.

Lemma minus_offset_non_bot :
  forall (x : t) (Hx : ~ eq x bot), ~ eq (minus_offset x) bot.
Proof. i; destruct x; by ss. Qed.

End ArrInfo.

Module ArrayBlk <: LAT.

(** ArrayBlock is a map from allocsites to array informations. *)

Include Map Allocsite ArrInfo.

Definition make (a : Allocsite.t) : t := add a (ArrInfo.make tt) bot.

Definition extern (a : Allocsite.t) : t := add a ArrInfo.top empty.

Definition plus_offset (ab : t) : t :=
  map (fun a => ArrInfo.plus_offset a) ab.

Lemma plus_offset_mor : Proper (eq ==> eq) plus_offset.
Proof.
unfold eq, plus_offset; intros ab1 ab2 Hab.
intro a. specialize Hab with a.
unfold find, map in *.
do 2 rewrite M.P.F.map_o.
remember (M.find a ab1) as opt_v1; destruct opt_v1 as [v1|]
; remember (M.find a ab2) as opt_v2; destruct opt_v2 as [v2|]; s.
- by apply ArrInfo.plus_offset_mor.
- by unfold ArrInfo.plus_offset.
- by unfold ArrInfo.plus_offset.
- by apply ArrInfo.eq_refl.
Qed.

Definition minus_offset (ab : t) : t :=
  map (fun a => ArrInfo.minus_offset a) ab.

Lemma minus_offset_mor : Proper (eq ==> eq) minus_offset.
Proof.
unfold eq, minus_offset; intros ab1 ab2 Hab.
intro a. specialize Hab with a.
unfold find, map in *.
do 2 rewrite M.P.F.map_o.
remember (M.find a ab1) as opt_v1; destruct opt_v1 as [v1|]
; remember (M.find a ab2) as opt_v2; destruct opt_v2 as [v2|]; s.
- by apply ArrInfo.minus_offset_mor.
- by unfold ArrInfo.minus_offset.
- by unfold ArrInfo.minus_offset.
- by apply ArrInfo.eq_refl.
Qed.

Definition cast_array (ab : t) : t := ab.

Lemma cast_array_mor : Proper (eq ==> eq) cast_array.
Proof. unfold cast_array, eq; by intros ab1 ab2 Hab. Qed.

Definition cast_array_int (z : Z) (ab : t) : t := cast_array ab.

Lemma cast_array_int_mor (z : Z) : Proper (eq ==> eq) (cast_array_int z).
Proof. unfold cast_array_int; by intros ab1 ab2 Hab. Qed.

Definition pow_loc_of_array (ab : t) : PowLoc.t :=
  let add_array_to_pow_loc k v acc :=
      if ArrInfo.eq_dec ArrInfo.bot v then acc else
        PowLoc.add (loc_of_allocsite k) acc in
  foldi add_array_to_pow_loc ab PowLoc.empty.

Lemma pow_loc_of_array_mor : Proper (eq ==> PowLoc.eq) pow_loc_of_array.
Proof.
unfold pow_loc_of_array; intros ab1 ab2 Hab.
apply foldi_mor; [| | |by auto|by apply PowLoc.eq_refl].
- constructor.
  + intros x; by apply PowLoc.eq_refl.
  + intros x y z; by apply PowLoc.eq_trans.
  + intros x y; by apply PowLoc.eq_sym.
- intros k1 k2 Hk v1 v2 Hv acc1 acc2 Hacc.
  destruct (ArrInfo.eq_dec ArrInfo.bot v1), (ArrInfo.eq_dec ArrInfo.bot v2)
  ; [ by auto
    | elim f; apply ArrInfo.eq_trans with v1; by auto
    | elim f; apply ArrInfo.eq_trans with v2; by auto using ArrInfo.eq_sym |].
  apply PowLoc.add_mor; [|by auto].
  by apply loc_of_allocsite_mor.
- i. destruct (ArrInfo.eq_dec ArrInfo.bot v); [by apply PowLoc.eq_refl|tauto].
Qed.

Definition pow_loc_of_struct_w_field (ab : t) (f : Field.t) : PowLoc.t :=
  let add_to_pow_loc a v acc :=
    if ArrInfo.eq_dec v ArrInfo.bot then acc else
      PowLoc.add (append_field (loc_of_allocsite a) f) acc in
  foldi add_to_pow_loc ab PowLoc.bot.

Lemma pow_loc_of_struct_w_field_mor :
  Proper (eq ==> Field.eq ==> PowLoc.eq) pow_loc_of_struct_w_field.
Proof.
intros s1 s2 Hs f1 f2 Hf. unfold pow_loc_of_struct_w_field. apply foldi2_1.
- i; dest_if_dec. elim f; by apply ArrInfo.eq_sym.
- i; dest_if_dec. elim f; by apply ArrInfo.eq_sym.
- i; dest_if_dec.
  + dest_if_dec.
    elim f; apply ArrInfo.eq_trans with v1; [by apply ArrInfo.eq_sym|by auto].
  + dest_if_dec.
    * elim f; apply ArrInfo.eq_trans with v2; by auto.
    * apply PowLoc.add_mor; [|by auto].
      apply append_field_mor; [by apply loc_of_allocsite_mor|by auto].
- by apply PowLoc.eq_refl.
- by auto.
Qed.

End ArrayBlk.
