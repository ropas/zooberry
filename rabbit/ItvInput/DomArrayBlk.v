(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** * Abstract Array Block.  *)

Set Implicit Arguments.

Require Import ZArith Morphisms.
Require Import hpattern vgtac DLat DItv DProd DMap DPow DomBasic.
Require Import VocabA.

Module ArrInfo <: LAT.

(** Abstract type of array information is [offset * size * stride]. *)

Include Prod3 Itv Itv Itv.

Definition top : t := (Itv.top, Itv.top, Itv.top).

Definition make (o sz st : Itv.t) : t := (o, sz, st).

Definition plus_offset (x : t) (i : Itv.t) : t :=
  let '(o, s, st) := x in
  if Itv.eq_dec Itv.bot o then x else
  (Itv.plus o i, s, st).

Lemma plus_offset_mor : Proper (eq ==> Itv.eq ==> eq) plus_offset.
Proof.
unfold plus_offset; intros [[o1 s1] st1] [[o2 s2] st2] Hx i1 i2 Hi.
destruct (Itv.eq_dec Itv.bot o1), (Itv.eq_dec Itv.bot o2)
; [ by auto
  | elim f; apply Itv.eq_trans with o1; [by apply e|by apply Hx]
  | elim f; apply Itv.eq_trans with o2
    ; [by apply e|apply Itv.eq_sym; by apply Hx] |].
split; [split|]; [|by apply Hx|by apply Hx].
apply Itv.plus_mor; [by apply Hx|by apply Hi].
Qed.

Lemma plus_offset_non_bot :
  forall (x : t) (i : Itv.t) (Hx : ~ eq x bot) (Hi : ~ Itv.eq i Itv.bot),
    ~ eq (plus_offset x i) bot.
Proof.
i; destruct x as [[o sz] st]; ss.
destruct (Itv.eq_dec Itv.bot o); [by elim Hx|].
inversion FH as [[Ho Hsz] Hst]; ss.
eapply Itv.plus_non_bot; [|apply Hi|apply FH].
i; apply Hx; repeat econs; by done.
Qed.

Definition minus_offset (x : t) (i : Itv.t) : t :=
  let '(o, s, st) := x in
  if Itv.eq_dec Itv.bot o then x else
  (Itv.minus o i, s, st).

Lemma minus_offset_mor : Proper (eq ==> Itv.eq ==> eq) minus_offset.
Proof.
unfold minus_offset; intros [[o1 s1] st1] [[o2 s2] st2] Hx i1 i2 Hi.
destruct (Itv.eq_dec Itv.bot o1), (Itv.eq_dec Itv.bot o2)
; [ by auto
  | elim f; apply Itv.eq_trans with o1; [by apply e|by apply Hx]
  | elim f; apply Itv.eq_trans with o2
    ; [by apply e|apply Itv.eq_sym; by apply Hx] |].
split; [split|]; [|by apply Hx|by apply Hx].
apply Itv.minus_mor; [by apply Hx|by apply Hi].
Qed.

Lemma minus_offset_non_bot :
  forall (x : t) (i : Itv.t) (Hx : ~ eq x bot) (Hi : ~ Itv.eq i Itv.bot),
    ~ eq (minus_offset x i) bot.
Proof.
i; destruct x as [[o sz] st]; ss.
destruct (Itv.eq_dec Itv.bot o); [by elim Hx|].
inversion FH as [[Ho Hsz] Hst]; ss.
eapply Itv.minus_non_bot; [|apply Hi|apply FH].
i; apply Hx; repeat econs; by done.
Qed.

End ArrInfo.

Module ArrayBlk <: LAT.

(** ArrayBlock is a map from allocsites to array informations. *)

Include Map Allocsite ArrInfo.

Definition make (a : Allocsite.t) (o sz st : Itv.t) : t :=
  add a (ArrInfo.make o sz st) bot.

Definition extern (a : Allocsite.t) : t := add a ArrInfo.top empty.

Definition plus_offset (ab : t) (i : Itv.t) : t :=
  if Itv.eq_dec i Itv.bot then bot else
    map (fun a => ArrInfo.plus_offset a i) ab.

Lemma plus_offset_mor : Proper (eq ==> Itv.eq ==> eq) plus_offset.
Proof.
unfold eq, plus_offset; intros ab1 ab2 Hab i1 i2 Hi.
destruct (Itv.eq_dec i1 Itv.bot), (Itv.eq_dec i2 Itv.bot)
; [ by apply eq_refl
  | elim f; by eauto using Itv.eq_trans, Itv.eq_sym
  | elim f; by eauto using Itv.eq_trans, Itv.eq_sym |].
intro a. specialize Hab with a.
unfold find, map in *.
do 2 rewrite M.P.F.map_o.
remember (M.find a ab1) as opt_v1; destruct opt_v1 as [v1|]
; remember (M.find a ab2) as opt_v2; destruct opt_v2 as [v2|]; s.
- by apply ArrInfo.plus_offset_mor.
- destruct v1 as [[o1 s1] st1].
  destruct Hab as [[Ho Hs] Hst]; simpl in *.
  destruct (Itv.eq_dec Itv.bot o1).
  + split; [split|]; s; by auto.
  + elim f1; apply Itv.eq_sym; by auto.
- destruct v2 as [[o2 s2] st2].
  destruct Hab as [[Ho Hs] Hst]; simpl in *.
  destruct (Itv.eq_dec Itv.bot o2).
  + split; [split|]; s; by auto.
  + elim f1; by auto.
- by apply ArrInfo.eq_refl.
Qed.

Definition minus_offset (ab : t) (i : Itv.t) : t :=
  if Itv.eq_dec i Itv.bot then bot else
    map (fun a => ArrInfo.minus_offset a i) ab.

Lemma minus_offset_mor : Proper (eq ==> Itv.eq ==> eq) minus_offset.
Proof.
unfold eq, minus_offset; intros ab1 ab2 Hab i1 i2 Hi.
destruct (Itv.eq_dec i1 Itv.bot), (Itv.eq_dec i2 Itv.bot)
; [ by apply eq_refl
  | elim f; by eauto using Itv.eq_trans, Itv.eq_sym
  | elim f; by eauto using Itv.eq_trans, Itv.eq_sym |].
intro a. specialize Hab with a.
unfold find, map in *.
do 2 rewrite M.P.F.map_o.
remember (M.find a ab1) as opt_v1; destruct opt_v1 as [v1|]
; remember (M.find a ab2) as opt_v2; destruct opt_v2 as [v2|]; s.
- by apply ArrInfo.minus_offset_mor.
- destruct v1 as [[o1 s1] st1].
  destruct Hab as [[Ho Hs] Hst]; simpl in *.
  destruct (Itv.eq_dec Itv.bot o1).
  + split; [split|]; s; by auto.
  + elim f1; apply Itv.eq_sym; by auto.
- destruct v2 as [[o2 s2] st2].
  destruct Hab as [[Ho Hs] Hst]; simpl in *.
  destruct (Itv.eq_dec Itv.bot o2).
  + split; [split|]; s; by auto.
  + elim f1; by auto.
- by apply ArrInfo.eq_refl.
Qed.

Definition cast_array (new_st : Itv.t) (ab : t) : t :=
  let resize orig_st x := Itv.divide (Itv.times x orig_st) new_st in
  let cast_offset x :=
      let '((o, s), orig_st) := x in
      let new_o := resize orig_st o in
      let new_s := resize orig_st s in
      if Itv.eq_dec Itv.bot orig_st then x else
        (new_o, new_s, new_st) in
  map cast_offset ab.

Lemma cast_array_mor : Proper (Itv.eq ==> eq ==> eq) cast_array.
Proof.
unfold cast_array, eq; intros i1 i2 Hi ab1 ab2 Hab.
intro a. specialize Hab with a.
unfold find, map in *.
do 2 rewrite M.P.F.map_o.
remember (M.find a ab1) as opt_v1; destruct opt_v1 as [v1|]
; remember (M.find a ab2) as opt_v2; destruct opt_v2 as [v2|]; s.
- destruct v1 as [[o1 s1] st1].
  destruct v2 as [[o2 s2] st2].
  destruct Hab as [[Ho Hs] Hst]; simpl in *.
  destruct (Itv.eq_dec Itv.bot st1); destruct (Itv.eq_dec Itv.bot st2).
  + split; [split|]; s; by auto.
  + elim f; apply Itv.eq_trans with st1; by auto.
  + elim f; apply Itv.eq_trans with st2; [|apply Itv.eq_sym]; by auto.
  + split; [split|]; s.
    * apply Itv.divide_mor; [|by auto].
      apply Itv.times_mor; by auto.
    * apply Itv.divide_mor; [|by auto].
      apply Itv.times_mor; by auto.
    * assumption.
- destruct v1 as [[o1 s1] st1].
  destruct Hab as [[Ho Hs] Hst]; simpl in *.
  destruct (Itv.eq_dec Itv.bot st1).
  + split; [split|]; s; by auto.
  + elim f; apply Itv.eq_sym; by auto.
- destruct v2 as [[o2 s2] st2].
  destruct Hab as [[Ho Hs] Hst]; simpl in *.
  destruct (Itv.eq_dec Itv.bot st2).
  + split; [split|]; s; by auto.
  + elim f; by auto.
- by apply ArrInfo.eq_refl.
Qed.

Definition cast_array_int (z : Z) (ab : t) : t := cast_array (Itv.of_int z) ab.

Lemma cast_array_int_mor (z : Z) : Proper (eq ==> eq) (cast_array_int z).
Proof.
unfold cast_array_int; intros ab1 ab2 Hab.
apply cast_array_mor; [by apply Itv.eq_refl|by auto].
Qed.

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
