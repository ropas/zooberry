(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** Pruning. *)

Set Implicit Arguments.

Require Import ZArith.
Require Import Monad VocabA Syn DItv DLat UserInputType Global.
Require Import DomBasic DomAbs DomMem SemMem SemEval.
Require Import vgtac Morphisms.

Local Open Scope Z.

Local Open Scope sumbool.

Definition itv_prune (op : binop) (x y : Itv.t) : Itv.t :=
  match x, y with
  | Itv.Bot, _
  | _, Itv.Bot => Itv.bot
  | @Itv.V a b _ _ _ , @Itv.V c d _ _ _ =>
    match op with
    | Lt => Itv.gen_itv a (Itv.min' b (Itv.minus'_one d))
    | Gt => Itv.gen_itv (Itv.max' a (Itv.plus'_one c)) b
    | Le => Itv.gen_itv a (Itv.min' b d)
    | Ge => Itv.gen_itv (Itv.max' a c) b
    | Eq => Itv.meet x y
    | _ => x
    end
  end.

Ltac itv_prune_mor_inv Hand Hor :=
  destruct Hand as [Hand1 Hand2], Hor as [Hor1|Hor2]
  ; [ elim Hor1; eapply Itv.eq'_trans
      ; [eapply Itv.eq'_trans; [|by apply Hand1]|]; by auto
    | elim Hor2; eapply Itv.eq'_trans
      ; [eapply Itv.eq'_trans; [|by apply Hand2]|]; by auto ].

Definition itv_prune_mor :
  forall op, Proper (Itv.eq ==> Itv.eq ==> Itv.eq) (itv_prune op).
Proof.
intros op ? ? ? ? ? ?; unfold itv_prune.
inversion H; [by apply Itv.eq_refl|].
inversion H0; [by apply Itv.eq_refl|].
subst. destruct op; try assumption.
- apply Itv.gen_itv_mor; [by auto|].
  apply Itv.min'_mor; [by auto|].
  apply Itv.minus'_one_mor; by auto.
- apply Itv.gen_itv_mor; [|by auto].
  apply Itv.max'_mor; [by auto|].
  apply Itv.plus'_one_mor; by auto.
- apply Itv.gen_itv_mor; [by auto|].
  apply Itv.min'_mor; by auto.
- apply Itv.gen_itv_mor; [|by auto].
  apply Itv.max'_mor; by auto.
- apply Itv.meet_eq; by assumption.
Qed.

Local Close Scope sumbool.

Module Make (Import M : Monad) (MB : MemBasic M).

Module Import SemMem := SemMem.Make M MB.

Module Import SemEval := SemEval.Make M MB.

Definition prune (g : G.t) (mode : update_mode) (node : InterNode.t)
           (cond : exp) (m : Mem.t) : M.m Mem.t :=
  match cond with
  | BinOp op (Lval (lval_intro (VarLhost x is_global) NoOffset _) _) e _ =>
    let x_lv := eval_var node x is_global in
    do x_v <- mem_lookup (PowLoc.singleton x_lv) m ;
    do v <- eval mode node e m ;
    let x_v' := modify_itv x_v (itv_prune op (itv_of_val x_v) (itv_of_val v)) in
    mem_update mode g x_lv x_v' m
  | _ => ret m
  end.

End Make.

Local Close Scope Z.
