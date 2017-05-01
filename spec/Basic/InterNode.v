(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** * Inter Node of Program.  *)

Set Implicit Arguments.

Require Import ZArith OrderedType OrderedTypeEx.
Require Import hpattern vgtac.
Require Import VocabA DLat DFSetAVL DFMapAVL TStr Syn.
Require IntraNode.

Module Pid := String_as_OT.

Include PairOrderedType Pid IntraNode.

Definition eqb x y := if eq_dec x y then true else false.

Definition zb_eq : zb_equiv eq :=
  {| zb_equiv_refl := eq_refl
   ; zb_equiv_sym := eq_sym
   ; zb_equiv_trans := eq_trans |}.

Definition get_pid (node : t) : pid_t := fst node.

Definition get_node (node : t) : IntraNode.t := snd node.

Definition is_entry_node (node : t) : bool :=
  IntraNode.is_entry_node (get_node node).

Definition is_exit_node (node : t) : bool :=
  IntraNode.is_exit_node (get_node node).

Definition entryof (f : pid_t) : t := (f, IntraNode.Entry).

Definition exitof (f : pid_t) : t := (f, IntraNode.Exit).

Lemma eq_inv : forall k k' (Hk : eq k k'), k = k'.
Proof.
i. destruct k, k'; destruct Hk as [Hk1 Hk2].
simpl in Hk1, Hk2. by inversion Hk1; inversion Hk2.
Qed.
