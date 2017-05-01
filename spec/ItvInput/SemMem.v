(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** * Memory operations.  *)

Set Implicit Arguments.

Require Import ZArith.
Require Import Monad hpattern vgtac VocabA Syn UserInputType DPow Global.
Require Import DomBasic DomAbs DomMem.

Module Make (Import M : Monad) (MB : MemBasic M).

Include MemOp M MB.

Section SemMem.

Variable mode : update_mode.

Variable g : G.t.

Fixpoint list_fold2_m {A B C : Type} (f : A -> B -> C -> m C)
         (l1 : list A) (l2 : list B) (acc : C) : m C :=
  match l1, l2 with
    | nil, nil => ret acc
    | (a :: l1')%list, (b :: l2')%list =>
      do acc' <- f a b acc ;
      list_fold2_m f l1' l2' acc'
    | _, _ => ret acc
  end.

Definition bind_arg f x v m :=
  mem_wupdate mode (PowLoc.singleton (loc_of_var (var_of_lvar (f, x)))) v m.

Definition bind_args vs f m :=
  match InterCfg.get_args (G.icfg g) f with
    | Some args => list_fold2_m (bind_arg f) args vs m
    | None => ret m
  end.

End SemMem.

End Make.
