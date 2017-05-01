(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** * Basic Abstract Domains.  *)

Set Implicit Arguments.

Require Import Morphisms.
Require Import VocabA.
Require Import hpattern vgtac Fold DFMapAVL DLat DUnit DNList DStr DProd
        DMap DSum DPow DItv InterCfg UserInputType Global.

(** ** Procedure names *)

Module Proc <: KEY := DStr.DStr.
Module PowProc <: LAT := Pow Proc.

(** ** Global/Local variables *)

Module GVar <: KEY := DStr.DStr.
Module LVar <: KEY := ProdKey2 Proc DStr.DStr.
Module Var <: KEY := SumKey2 GVar LVar.

(** ** Abstract C struct *)

Module Field <: KEY := DStr.DStr.
Module Fields <: KEY := NListKey Field.
Module ExtAllocsite <: KEY := SumKey2 Unit Proc.
Module Allocsite <: KEY := SumKey2 InterNode ExtAllocsite.

(** ** Abstract locations *)

Module VarAllocsite <: KEY := SumKey2 Var Allocsite.
Module FldLoc <: KEY := ProdKey2 VarAllocsite Fields.

(* NOTE: The last Proc location in Loc is to remember return
locations, which Dump dealt with before. *)

Module Loc <: KEY := SumKey2 FldLoc Proc.
Module PowLoc <: LAT := Pow Loc.

Definition var_of_gvar (x : GVar.t) : Var.t := Var.Inl x.
Definition var_of_lvar (x : LVar.t) : Var.t := Var.Inr x.

Definition approx_one_loc (g : G.t) (l : Loc.t) : bool :=
  match l with
    | Loc.Inl (VarAllocsite.Inl (Var.Inl _), Fields.nil) => true
    | Loc.Inl (VarAllocsite.Inl (Var.Inr (f, _)), Fields.nil) => negb (G.is_rec f g)
    | _ => false
  end.

Lemma approx_one_loc_mor : forall g, Proper (Loc.eq ==> eq) (approx_one_loc g).
Proof.
unfold approx_one_loc; inversion 1.
- destruct x', y'. destruct Heq as [Hva Hf]; simpl in *.
  destruct t, t1; [|by inversion Hva|by inversion Hva|by inversion Hva].
  destruct a, a0; [ by inversion Hf | inversion Hva; by inversion Heq
                  | inversion Hva; by inversion Heq |].
  destruct b, b0; f_equal.
  destruct t0, t2; [|by inversion Hf|by inversion Hf|by auto].
  inversion Hva; inversion Heq; subst; simpl in *.
  destruct Heq0 as [Hs _].
  rewrite G.is_rec_mor; [reflexivity|by apply Hs|reflexivity].
- reflexivity.
Qed.

Definition is_local_of f l :=
  match l with
    | Loc.Inl (VarAllocsite.Inl (Var.Inr (g, _)), _) =>
      if DStr.eq_dec f g then true else false
    | _ => false
  end.

Lemma is_local_of_mor : forall f, Proper (Loc.eq ==> eq) (is_local_of f).
Proof.
intros f l1 l2 Hl. unfold is_local_of.
inversion Hl; [|by auto].
destruct x' as [vax ?], y' as [vay ?].
simpl in Heq. destruct Heq as [Heq1 Heq2].
inversion Heq1; [|by auto].
inversion Heq; [by auto|].
destruct x'0 as [gx ?], y'0 as [gy ?].
simpl in Heq0. destruct Heq0 as [Heq3 Heq4]; subst.
reflexivity.
Qed.

Definition loc_of_var (x : Var.t) : Loc.t :=
  Loc.Inl (VarAllocsite.Inl x, Fields.nil).

Lemma loc_of_var_mor : Proper (Var.eq ==> Loc.eq) loc_of_var.
Proof.
unfold loc_of_var; intros x1 x2 Hx.
constructor; s; split; by constructor.
Qed.

Definition loc_of_allocsite (x : Allocsite.t) : Loc.t :=
  Loc.Inl (VarAllocsite.Inr x, Fields.nil).

Lemma loc_of_allocsite_mor : Proper (Allocsite.eq ==> Loc.eq) loc_of_allocsite.
Proof.
unfold loc_of_allocsite; intros a1 a2 Ha.
constructor; s; split; by constructor.
Qed.

Definition loc_of_proc (x : Proc.t) : Loc.t := Loc.Inr x.

Lemma loc_of_proc_mor : Proper (Proc.eq ==> Loc.eq) loc_of_proc.
Proof. unfold loc_of_proc; intros p1 p2 Hp. by constructor. Qed.

Definition append_field (l : Loc.t) (f : Field.t) : Loc.t :=
  match l with
    | Loc.Inl va => Loc.Inl (fst va, Fields.app (snd va) f)
    | _ => l
  end.

Lemma append_field_mor : Proper (Loc.eq ==> Field.eq ==> Loc.eq) append_field.
Proof.
unfold append_field; intros l1 l2 Hl f1 f2 Hf. inversion Hl; s.
- constructor; s; split.
  + by apply Heq.
  + apply Fields.app_mor; [by apply Heq|by apply Hf].
- by constructor.
Qed.

Module SMLocLoc := SetMap Loc PowLoc Loc PowLoc.

Definition pow_loc_append_field (ls : PowLoc.t) (f : Field.t) : PowLoc.t :=
  SMLocLoc.map (fun l => append_field l f) ls.

Lemma pow_loc_append_field_mor :
  Proper (PowLoc.eq ==> Field.eq ==> PowLoc.eq) pow_loc_append_field.
Proof.
unfold pow_loc_append_field; intros ls1 ls2 Hls f1 f2 Hf.
unfold SMLocLoc.map; apply PowLoc.fold_mor.
- constructor
  ; [ intros ?; by apply PowLoc.eq_refl
    | intros ? ?; by apply PowLoc.eq_sym
    | intros ? ? ?; by apply PowLoc.eq_trans ].
- i; apply PowLoc.add_mor; [|by auto].
  apply append_field_mor; by auto.
- by auto.
- by apply PowLoc.eq_refl.
Qed.

Definition allocsite_of_node (node : InterNode.t) : Allocsite.t :=
  Allocsite.Inl node.

Lemma allocsite_of_node_mor :
  Proper (InterNode.eq ==> Allocsite.eq) allocsite_of_node.
Proof.
unfold allocsite_of_node; intros n1 n2 Hn.
inversion Hn. by constructor.
Qed.

Definition allocsite_of_ext (fid_opt : option Proc.t) : Allocsite.t :=
  match fid_opt with
    | None => Allocsite.Inr (ExtAllocsite.Inl tt)
    | Some fid => Allocsite.Inr (ExtAllocsite.Inr fid)
  end.

Lemma allocsite_of_ext_mor :
  Proper (opt_eq Proc.eq ==> Allocsite.eq) allocsite_of_ext.
Proof.
unfold opt_eq, allocsite_of_ext; intros n1 n2 Hn.
destruct n1, n2
; [constructor; by constructor|tauto|tauto|constructor; by constructor].
Qed.
