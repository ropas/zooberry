(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
Set Implicit Arguments.

Require Import vgtac.
Require Import TStr.
Require Import DStr.
Require Import List.
Require Import DomAbs.
Require Import VocabA.

Inductive arg_t :=
| FixArg                      (* Fixed argument *)
| VaArg.                      (* Variable arguments *)
Inductive src_t :=
| InSrc
| ExSrc.
Inductive alloc_t :=
| NoAlloc
| DoAlloc.
Inductive argument_t :=
| Src (va_arg : arg_t)
| Dst (va_arg : arg_t) (alloc : alloc_t) (src : src_t)
| SkipArg.
Inductive ret_t :=
| CleanRet
| TaintRet
| SrcRet (alloc : alloc_t)
| DstRet.

Record t := Make
  { args : list argument_t
  ; ret : ret_t }.

(** Aliases *)
Definition src := Src FixArg.
Definition src_va := Src VaArg.
Definition src_ret := SrcRet NoAlloc.
Definition src_ret_alloc := SrcRet DoAlloc.

Definition dst := Dst FixArg NoAlloc InSrc.
Definition dst_va := Dst VaArg NoAlloc InSrc.
Definition dst_ext := Dst FixArg NoAlloc ExSrc.
Definition dst_va_ext := Dst VaArg NoAlloc ExSrc.
Definition dst_alloc := Dst FixArg DoAlloc InSrc.
Definition dst_ret := DstRet.

Definition skip := SkipArg.

Definition clean_ret := CleanRet.
Definition taint_ret := TaintRet.

Definition dst_t := (Val.t * alloc_t * src_t)%type.

Inductive dst_eq : dst_t -> dst_t -> Prop :=
| dst_eq_intro :
    forall (v1 v2 : Val.t) (Hv : Val.eq v1 v2)
       (a1 a2 : alloc_t) (Ha : Logic.eq a1 a2)
       (s1 s2 : src_t) (Hs : Logic.eq s1 s2),
      dst_eq (v1, a1, s1) (v2, a2, s2).

Definition dst_zb_eq : DLat.zb_equiv dst_eq.
Proof.
constructor; i.
- destruct x as [[v a] s]; constructor; by auto using Val.eq_refl.
- inversion Heq; subst; constructor; by auto using Val.eq_sym.
- inversion eq1; subst; inversion eq2; subst; constructor
  ; [by apply Val.eq_trans with v2|by auto|by auto].
Qed.

Fixpoint get_dstsrc_list (vs : list Val.t) (args : list argument_t)
         (dsts : list dst_t) (srcs : list Val.t) :=
  match vs, args with
  | v :: vtl, Src FixArg :: argtl =>
    get_dstsrc_list vtl argtl dsts (v :: srcs)
  | _, Src VaArg :: argtl => get_dstsrc_list nil argtl dsts (vs ++ srcs)
  | v :: vtl, Dst FixArg alloc s :: argtl =>
    get_dstsrc_list vtl argtl ((v, alloc, s) :: dsts) srcs
  | _, Dst VaArg alloc s :: argtl =>
    let dsts' := List.map (fun v => (v, alloc, s)) vs in
    get_dstsrc_list nil argtl (dsts' ++ dsts) srcs
  | v :: vtl, SkipArg :: argtl => get_dstsrc_list vtl argtl dsts srcs
  | _, _ => (dsts, srcs)
  end.

Module M := FMapAVL.Make DStr.

Definition empty := M.empty.
Definition add := M.add.
Definition find := M.find.
