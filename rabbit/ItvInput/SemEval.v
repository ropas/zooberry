(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** * Eval semantics of expression.  *)

Set Implicit Arguments.

Require Import String ZArith Morphisms.
Require Import Monad hpattern vgtac VocabA Syn DLat DPow DItv UserInputType.
Require Import DomBasic DomArrayBlk DomAbs DomMem SemMem.

Local Open Scope Z.
Local Open Scope sumbool.

Definition eval_const (cst : constant) : Val.t :=
  match cst with
    | CInt64 (Some z) | CChr z => Itv.of_int z
    | CReal lb ub => Itv.of_ints lb ub
    | _ => Itv.top
  end.

Definition eval_uop (u : unop) (v : Val.t) : Val.t :=
  if Val.eq_dec v Val.bot then Val.bot else
    match u with
      | Neg => Itv.minus Itv.zero (itv_of_val v)
      | BNot => Itv.b_not_itv (itv_of_val v)
      | LNot => Itv.not_itv (itv_of_val v)
    end.

Lemma eval_uop_mor (u : unop) : Proper (Val.eq ==> Val.eq) (eval_uop u).
Proof.
unfold eval_uop. intros v1 v2 Hv.
destruct (Val.eq_dec v1 Val.bot), (Val.eq_dec v2 Val.bot).
- by apply Val.eq_refl.
- elim f; eapply Val.eq_trans; [|by apply e].
  apply Val.eq_sym; assumption.
- elim f; eapply Val.eq_trans; [by apply Hv|assumption].
- destruct u; apply val_of_itv_mor.
  + apply Itv.minus_mor; [by apply Itv.eq_refl|by apply Hv].
  + apply Itv.b_not_itv_mor; by apply Hv.
  + apply Itv.not_itv_mor; by apply Hv.
Qed.

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
  | PlusA => Itv.plus (itv_of_val v1) (itv_of_val v2)
  | PlusPI | IndexPI =>
    Val.join
      (array_loc_of_val v1)
      (ArrayBlk.plus_offset (array_of_val v1) (itv_of_val v2))
  | MinusA => Itv.minus (itv_of_val v1) (itv_of_val v2)
  | MinusPI =>
    Val.join
      (array_loc_of_val v1)
      (ArrayBlk.minus_offset (array_of_val v1) (itv_of_val v2))
  | MinusPP => Itv.top
  | Mult => Itv.times (itv_of_val v1) (itv_of_val v2)
  | Div => Itv.divide (itv_of_val v1) (itv_of_val v2)
  | Mod => Itv.mod_itv (itv_of_val v1) (itv_of_val v2)
  | Shiftlt => Itv.l_shift_itv (itv_of_val v1) (itv_of_val v2)
  | Shiftrt => Itv.r_shift_itv (itv_of_val v1) (itv_of_val v2)
  | Lt => Itv.lt_itv (itv_of_val v1) (itv_of_val v2)
  | Gt => Itv.gt_itv (itv_of_val v1) (itv_of_val v2)
  | Le => Itv.le_itv (itv_of_val v1) (itv_of_val v2)
  | Ge => Itv.ge_itv (itv_of_val v1) (itv_of_val v2)
  | Eq => Itv.eq_itv (itv_of_val v1) (itv_of_val v2)
  | Ne => Itv.ne_itv (itv_of_val v1) (itv_of_val v2)
  | BAnd => Itv.b_and_itv (itv_of_val v1) (itv_of_val v2)
  | BXor => Itv.b_xor_itv (itv_of_val v1) (itv_of_val v2)
  | BOr => Itv.b_or_itv (itv_of_val v1) (itv_of_val v2)
  | LAnd => Itv.and_itv (itv_of_val v1) (itv_of_val v2)
  | LOr => Itv.or_itv (itv_of_val v1) (itv_of_val v2)
  end.

Lemma eval_bop_mor (b : binop) :
  Proper (Val.eq ==> Val.eq ==> Val.eq) (eval_bop b).
Proof.
unfold eval_bop. intros v1 v2 Hv w1 w2 Hw; destruct b.
- apply val_of_itv_mor. apply Itv.plus_mor; [by apply Hv|by apply Hw].
- apply Val.join_eq.
  + by apply array_loc_of_val_mor.
  + apply val_of_array_mor.
    apply ArrayBlk.plus_offset_mor; [by apply Hv|by apply Hw].
- apply Val.join_eq.
  + by apply array_loc_of_val_mor.
  + apply val_of_array_mor.
    apply ArrayBlk.plus_offset_mor; [by apply Hv|by apply Hw].
- apply val_of_itv_mor.
  apply Itv.minus_mor; [by apply Hv|by apply Hw].
- apply Val.join_eq.
  + by apply array_loc_of_val_mor.
  + apply val_of_array_mor.
    apply ArrayBlk.minus_offset_mor; [by apply Hv|by apply Hw].
- by apply Val.eq_refl.
- split; [split; [split|] |].
  + s. apply Itv.times_mor; [by apply Hv|by apply Hw].
  + s. by apply PowLoc.eq_refl.
  + s. by apply ArrayBlk.eq_refl.
  + s. by apply PowProc.eq_refl.
- split; [split; [split|] |].
  + s. apply Itv.divide_mor; [by apply Hv|by apply Hw].
  + s. by apply PowLoc.eq_refl.
  + s. by apply ArrayBlk.eq_refl.
  + s. by apply PowProc.eq_refl.
- apply val_of_itv_mor. apply Itv.mod_itv_mor; [by apply Hv|by apply Hw].
- apply val_of_itv_mor. apply Itv.l_shift_itv_mor; [by apply Hv|by apply Hw].
- apply val_of_itv_mor. apply Itv.r_shift_itv_mor; [by apply Hv|by apply Hw].
- apply val_of_itv_mor. apply Itv.lt_itv_mor; [by apply Hv|by apply Hw].
- apply val_of_itv_mor. apply Itv.gt_itv_mor; [by apply Hv|by apply Hw].
- apply val_of_itv_mor. apply Itv.le_itv_mor; [by apply Hv|by apply Hw].
- apply val_of_itv_mor. apply Itv.ge_itv_mor; [by apply Hv|by apply Hw].
- apply val_of_itv_mor. apply Itv.eq_itv_mor; [by apply Hv|by apply Hw].
- apply val_of_itv_mor. apply Itv.ne_itv_mor; [by apply Hv|by apply Hw].
- apply val_of_itv_mor. apply Itv.b_and_itv_mor; [by apply Hv|by apply Hw].
- apply val_of_itv_mor. apply Itv.b_xor_itv_mor; [by apply Hv|by apply Hw].
- apply val_of_itv_mor. apply Itv.b_or_itv_mor; [by apply Hv|by apply Hw].
- apply val_of_itv_mor. apply Itv.and_itv_mor; [by apply Hv|by apply Hw].
- apply val_of_itv_mor. apply Itv.or_itv_mor; [by apply Hv|by apply Hw].
Qed.

Definition eval_string (s : string) : Val.t := val_of_itv Itv.zero_pos.

Definition eval_string_loc (s : string) (a : Allocsite.t) (lvs : PowLoc.t)
           : Val.t :=
  let i := Z_of_nat (S (String.length s)) in
  Val.join (lvs : Val.t)
           (ArrayBlk.make a Itv.zero (Itv.of_int i) (Itv.of_int 1) : Val.t).

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

Fixpoint eval (mode : update_mode) (node : InterNode.t)
         (e : exp) (m : Mem.t) : M.m Val.t :=
  match e with
  | Const c _ => ret (eval_const c)
  | Lval l _ =>
    do lv <- eval_lv mode node l m ;
    mem_lookup lv m
  | SizeOf t_opt _ =>
    let t_itv := match t_opt with
                   | None => Itv.top
                   | Some t => Itv.of_int t
                 end in
    ret (t_itv : Val.t)
  | SizeOfE e_opt _ =>
    let e_itv := match e_opt with
                   | None => Itv.top
                   | Some e => Itv.of_int e
                 end in
    ret (e_itv : Val.t)
  | SizeOfStr s _ =>
    let i := Z_of_nat (S (String.length s)) in
    ret (Itv.of_int i : Val.t)
  | AlignOf t _ => ret (Itv.of_int t : Val.t)
  | AlignOfE _ _ => ret (Itv.top : Val.t)
  | UnOp u e _ =>
    do v <- eval mode node e m ;
    ret (eval_uop u v)
  | BinOp b e1 e2 _ =>
    do v1 <- (eval mode node e1 m) ;
    do v2 <- (eval mode node e2 m) ;
    ret (eval_bop b v1 v2)
  | Question e1 e2 e3 _ =>
    do v1 <- (eval mode node e1 m) ;
    let i1 : Itv.t := itv_of_val v1 in
    if Itv.eq_dec i1 Itv.bot then ret Val.bot else
    if Itv.eq_dec i1 Itv.zero then eval mode node e3 m else
    if ~~ (Itv.le_dec Itv.zero i1) then eval mode node e2 m else
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
  end

with resolve_offset (mode : update_mode) (node : InterNode.t)
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
    do idx <- eval mode node e m ;
    do v' <- mem_lookup (deref_of_val v) m ;
    let v' :=
        modify_array
          v'
          (ArrayBlk.plus_offset (array_of_val v') (itv_of_val idx))
    in
    resolve_offset mode node v' os' m
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

Definition eval_alloc' (node : InterNode.t) (sz_v : Val.t) : Val.t :=
  let allocsite := allocsite_of_node node in
  let pow_loc : PowLoc.t := PowLoc.singleton (loc_of_allocsite allocsite) in
  Val.join
    (pow_loc : Val.t)
    (ArrayBlk.make allocsite Itv.zero (itv_of_val sz_v) (Itv.of_int 1) : Val.t).

Definition eval_alloc (mode : update_mode) (node : InterNode.t) (a : alloc) (mem : Mem.t)
: M.m Val.t :=
  match a with
  | Array e =>
    do sz_v <- eval mode node e mem ;
    ret (eval_alloc' node sz_v)
  end.

End Make.

Local Close Scope sumbool.
Local Close Scope Z.
