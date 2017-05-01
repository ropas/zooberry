(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** * Eval semantics of expression.  *)

Set Implicit Arguments.

Require Import String ZArith Morphisms.
Require Import Monad hpattern vgtac VocabA Syn DLat DPow UserInputType.
Require Import DomBasic DomArrayBlk DomAbs DomMem SemMem.

Local Open Scope Z.
Local Open Scope sumbool.

Definition eval_const (cst : constant) : Val.t := Val.bot.

Definition eval_uop (u : unop) (v : Val.t) : Val.t := v.

Lemma eval_uop_mor (u : unop) : Proper (Val.eq ==> Val.eq) (eval_uop u).
Proof. unfold eval_uop. by intros v1 v2 Hv. Qed.

Definition is_array_loc (x : Loc.t) : bool :=
  match x with
    | Loc.Inl (VarAllocsite.Inr _, _) => true
    | _ => false
  end.

Lemma is_array_loc_mor : Proper (Loc.eq ==> eq) is_array_loc.
Proof.
unfold is_array_loc; intros x1 x2 Hx.
destruct x1, x2; [|by inversion Hx|by inversion Hx|by auto].
destruct a, a0. destruct t, t1.
- by auto.
- inversion Hx; destruct Heq as [Heq _]; by inversion Heq.
- inversion Hx; destruct Heq as [Heq _]; by inversion Heq.
- by auto.
Qed.

Definition array_loc_of_val (v : Val.t) : Val.t :=
  PowLoc.filter is_array_loc (pow_loc_of_val v).

Lemma array_loc_of_val_mor : Proper (Val.eq ==> Val.eq) array_loc_of_val.
Proof.
unfold array_loc_of_val; intros v1 v2 Hv.
apply val_of_pow_loc_mor.
apply PowLoc.SS.SF.filter_equal; [by apply is_array_loc_mor|by apply Hv].
Qed.

Definition eval_bop (b : binop) (v1 v2 : Val.t) : Val.t :=
  match b with
  | PlusPI | IndexPI =>
    Val.join (array_loc_of_val v1) (ArrayBlk.plus_offset (array_of_val v1))
  | MinusPI =>
    Val.join (array_loc_of_val v1) (ArrayBlk.minus_offset (array_of_val v1))
  | _ => Val.join v1 v2
  end.

Lemma eval_bop_mor (b : binop) :
  Proper (Val.eq ==> Val.eq ==> Val.eq) (eval_bop b).
Proof.
unfold eval_bop. intros v1 v2 Hv w1 w2 Hw; destruct b
; try by apply Val.join_eq.
- apply Val.join_eq.
  + by apply array_loc_of_val_mor.
  + by apply val_of_array_mor, ArrayBlk.plus_offset_mor, array_of_val_mor.
- apply Val.join_eq.
  + by apply array_loc_of_val_mor.
  + by apply val_of_array_mor, ArrayBlk.plus_offset_mor, array_of_val_mor.
- apply Val.join_eq.
  + by apply array_loc_of_val_mor.
  + by apply val_of_array_mor, ArrayBlk.minus_offset_mor, array_of_val_mor.
Qed.

Definition eval_string (s : string) : Val.t := Val.bot.

Definition eval_string_loc (s : string) (a : Allocsite.t) (lvs : PowLoc.t)
           : Val.t :=
  Val.join (lvs : Val.t) (ArrayBlk.make a : Val.t).

Definition deref_of_val (v : Val.t) : PowLoc.t :=
  PowLoc.join (pow_loc_of_val v) (ArrayBlk.pow_loc_of_array (array_of_val v)).

Lemma deref_of_val_mor : Proper (Val.eq ==> PowLoc.eq) deref_of_val.
Proof.
unfold deref_of_val; intros v1 v2 Hv.
apply PowLoc.join_eq.
- by apply pow_loc_of_val_mor.
- apply ArrayBlk.pow_loc_of_array_mor. by apply array_of_val_mor.
Qed.

Module Make (Import M : Monad) (MB : MemBasic M).

Module Import SemMem := SemMem.Make M MB.

Definition eval_var node x (is_global : bool) :=
  if is_global then loc_of_var (var_of_gvar x) else
    loc_of_var (var_of_lvar (InterNode.get_pid node, x)).

Fixpoint resolve_offset (mode : update_mode) (node : InterNode.t)
                    (v : Val.t) (os : offset) (m : Mem.t)
: M.m PowLoc.t :=
  match os with
  | NoOffset => ret (deref_of_val v)
  | FOffset f os' =>
    resolve_offset mode node
      (PowLoc.join
         (pow_loc_append_field (pow_loc_of_val v) f)
         (ArrayBlk.pow_loc_of_struct_w_field (array_of_val v) f))
      os' m
  | IOffset e os' =>
    do v' <- mem_lookup (deref_of_val v) m ;
    resolve_offset mode node v' os' m
  end.

Fixpoint eval (mode : update_mode) (node : InterNode.t)
         (e : exp) (m : Mem.t) : M.m Val.t :=
  match e with
  | Const c _ => ret (eval_const c)
  | Lval l _ =>
    do lv <- eval_lv mode node l m ;
    mem_lookup lv m
  | SizeOf _ _
  | SizeOfE _ _
  | SizeOfStr _ _
  | AlignOf _ _
  | AlignOfE _ _ => ret Val.bot
  | UnOp u e _ =>
    do v <- eval mode node e m ;
    ret (eval_uop u v)
  | BinOp b e1 e2 _ =>
    do v1 <- eval mode node e1 m ;
    do v2 <- eval mode node e2 m ;
    ret (eval_bop b v1 v2)
  | Question e1 e2 e3 _ =>
    do v2 <- eval mode node e2 m ;
    do v3 <- eval mode node e3 m ;
    ret (Val.join v2 v3)
  | CastE new_stride_opt e _ =>
    match new_stride_opt with
    | None => eval mode node e m
    | Some new_stride =>
      do v <- eval mode node e m ;
      let array_v := ArrayBlk.cast_array_int new_stride (array_of_val v) in
      ret (modify_array v array_v)
    end
  | AddrOf l _ =>
    do lv <- eval_lv mode node l m ;
    ret (val_of_pow_loc lv)
  | StartOf l _ =>
    do lv <- eval_lv mode node l m ;
    ret (val_of_pow_loc lv)
  end

with eval_lv (mode : update_mode) (node : InterNode.t)
             (lv : lval) (m : Mem.t) : M.m PowLoc.t :=
  match lv with
  | lval_intro lhost' ofs _ =>
    do v <-
      match lhost' with
      | VarLhost vi is_global =>
        let x := eval_var node vi is_global in
        ret ((PowLoc.singleton x) : Val.t)
      | MemLhost e => eval mode node e m
      end ;
    resolve_offset mode node v ofs m
  end.

Fixpoint eval_list (mode : update_mode) (node : InterNode.t)
         (es : list exp) (m : Mem.t) : M.m (list Val.t) :=
  match es with
    | nil => ret nil
    | e :: tl =>
      do v <- eval mode node e m;
      do tl' <- eval_list mode node tl m;
      ret (v :: tl')
  end.

Definition eval_alloc' (node : InterNode.t) : Val.t :=
  let allocsite := allocsite_of_node node in
  let pow_loc : PowLoc.t := PowLoc.singleton (loc_of_allocsite allocsite) in
  Val.join (pow_loc : Val.t) (ArrayBlk.make allocsite : Val.t).

Definition eval_alloc (mode : update_mode) (node : InterNode.t) (a : alloc)
  : Val.t :=
  match a with
    | Array e => eval_alloc' node
  end.

End Make.

Local Close Scope sumbool.
Local Close Scope Z.
