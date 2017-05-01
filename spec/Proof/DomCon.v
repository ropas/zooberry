(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** * Concrete Domain *)

Set Implicit Arguments.

Require Import ZArith OrderedTypeEx.
Require Import Monad vgtac VocabA Syn DFSetAVL DFMapAVL InterCfg DLat
        DUnit DNat DZ DStr DList DSum DMap DProd DPow Global.
Require DMem.
Require Import SemCommon.

Local Open Scope type.

Module Step <: KEY := Nat.

(** CallId is a step number on the call node, which is used to
distinguish function calls in concrete semantics. *)

Module CallId <: KEY := Step.

Module Proc <: KEY := DStr.
Module GVar <: KEY := DStr.
Module LVar <: KEY := ProdKey3 CallId Proc DStr.
Module Var <: KEY := SumKey2 GVar LVar.

Module ExtAllocsite <: KEY := SumKey2 Unit Proc.
Module Allocsite <: KEY := SumKey2 InterNode ExtAllocsite.
Module OSS <: KEY := ProdKey3 DZ DZ DZ.
Module Region <: KEY := ProdKey3 Step Allocsite OSS.
Module VarRegion <: KEY := SumKey2 Var Region.

Module Field <: KEY := DStr.
Module Fields <: KEY := ListKey Field.

Module Loc <: KEY := ProdKey2 VarRegion Fields.

Definition val_t := Z.t + Loc.t + Proc.t.

(** Auxiliary alias functions for value *)

Definition val_of_z (z : Z) : val_t := inl (inl z).
Definition val_of_loc (l : Loc.t) : val_t := inl (inr l).
Definition val_of_proc (p : Proc.t) : val_t := inr p.

Definition loc_of_gvar (x : vid_t) (fs : Fields.t) : Loc.t :=
  (VarRegion.Inl (Var.Inl x), fs).
Definition loc_of_lvar (cid : CallId.t) (p : Proc.t) (x : vid_t) (fs : Fields.t)
: Loc.t :=
  (VarRegion.Inl (Var.Inr (cid, p, x)), fs).
Definition loc_of_alloc (step : Step.t) (alloc : Allocsite.t) (oss : OSS.t)
  (fs : Fields.t) : Loc.t :=
  (VarRegion.Inr (step, alloc, oss), fs).


Module M := FMapAVL'.Make Loc.
Definition mem_t := M.t val_t.

(** Stack is a list of call stack information, which is a product of
callee, (optional) return location, and caller's CallId for
restorations of CallId on return statements.  *)

Definition stack1 : Type := Proc.t * option Loc.t * CallId.t.

Definition stack_t : Type := list stack1.

Definition callee_t := option Proc.t.

(** intra_node_state_t represents CallId (call node's step numbers to
distinguish local variables), an optional and temporary callee name
after call statements, memory, and stack. *)

Definition intra_node_state_t := CallId.t * callee_t * mem_t * stack_t.

Definition call_nodes_t := list InterNode.t.

Definition inter_node_state_t :=
  InterNode.t * Step.t * call_nodes_t * intra_node_state_t.

Definition state_t := mem_pos * inter_node_state_t.

Inductive not_appear_stack f : stack_t -> Prop :=
| not_appear_nil : not_appear_stack f nil
| not_appear_cons :
    forall s (Hs : not_appear_stack f s) f' (Hf' : ~ Proc.eq f f') opt_loc cid,
      not_appear_stack f ((f', opt_loc, cid) :: s).

Inductive appear_once_stack f : stack_t -> Prop :=
| appear_once_nil :
    forall s (Hs : not_appear_stack f s) f' (Hf' : Proc.eq f f') opt_loc cid,
      appear_once_stack f ((f', opt_loc, cid) :: s)
| appear_once_cons :
    forall s (Hs : appear_once_stack f s) f' (Hf' : ~ Proc.eq f f') opt_loc cid,
      appear_once_stack f ((f', opt_loc, cid) :: s).

Definition wf_non_rec_stack g :=
  forall f stk (Hf : Global.G.is_rec f g = false), appear_once_stack f stk.

Local Close Scope type.
