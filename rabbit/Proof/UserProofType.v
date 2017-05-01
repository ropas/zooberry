(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** * Type of user's proof obligation *)

(** The module type defined in this file presents user's
responsibility for correctness proof of the validator.  *)

Set Implicit Arguments.

Require Import Morphisms.
Require Import UserInputType VocabA.
Require GenFunc.
Require DomCon SemCon.
Require Import vgtac.
Require Import Monad.

Module Type PINPUT.

Include INPUT.
Include GenFunc.Make.

Parameter Loc_g : DomCon.Loc.t -> Loc.t.

Parameter Val_g : DomCon.val_t -> Val.t -> Prop.

(** Abstraction of Proc.t in DomCon.stack1. *)
Parameter SProc_g : DomCon.Proc.t -> Loc.t.

Parameter val_g_monotone : monotone Val.le Val_g.

Parameter prop_approx_one_loc :
  forall g l (Hl: approx_one_loc g l = true)
     m (Hm : SemCon.wf_non_rec_mem g m)
     l1 (Hl1: Loc.eq (Loc_g l1) l) (Hml1 : DomCon.M.In l1 m)
     l2 (Hl2: Loc.eq (Loc_g l2) l) (Hml2 : DomCon.M.In l2 m),
    DomCon.Loc.eq l1 l2.

Load MemGCommon.

Parameter correct_run :
  forall g step cn cmd con_s con_s' abs_m abs_m'
    (Hmem_g : Mem_g con_s abs_m)
    (HCon : SemCon.Run g step cn cmd con_s con_s')
    (HAbs : abs_m' = run_only Strong g cn cmd abs_m),
    Mem_g con_s' abs_m'.

(* Property 1: The functions collecting access information return the
same values. *)

Load VeqCommon.

Parameter run_only_access_same :
  forall g cn cmd m,
    veq (run_only Strong g cn cmd m) (run_access Strong g cn cmd m).

Parameter run_access_sound :
  forall g cn cmd, aeqm1 (run_access Strong g cn cmd).

End PINPUT.
