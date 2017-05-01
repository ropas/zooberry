(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
Module Acc := Access.Make Loc PowLoc.

Module Mem := DMem.Make Loc Val PowLoc.

Module Index <: KEY := InterNode.

Module Table := FMapAVL'.Make Index.

(** ** Type class for memory operations. *)

Module Type MemBasic (M : Monad).

Axiom mem_find :
  forall (l : Loc.t) (m : Mem.t), M.m Val.t.

Axiom mem_add :
  forall (l : Loc.t) (v : Val.t) (m : Mem.t), M.m Mem.t.

Axiom mem_weak_add :
  forall (l : Loc.t) (v : Val.t) (m : Mem.t), M.m Mem.t.

Axiom mem_pre_weak_add :
  forall (l : Loc.t) (v : Val.t) (m : Mem.t), M.m Mem.t.

End MemBasic.

(** *** Monad instances *)

Module AccMem <: MemBasic Acc.MAcc.

Definition mem_find l m := (Mem.find l m, Acc.add Acc.USE l Acc.bot).

Definition mem_add l v m := (Mem.add l v m, Acc.add Acc.DEF l Acc.bot).

Definition mem_weak_add l v m :=
  (Mem.weak_add l v m, Acc.add Acc.ALL l Acc.bot).

Definition mem_pre_weak_add l v m :=
  (Mem.fast_weak_add l v m, Acc.add Acc.ALL l Acc.bot).

End AccMem.

Module IdMem <: MemBasic MId.

Definition mem_find l m := Mem.find l m.

Definition mem_add l v m := Mem.add l v m.

Definition mem_weak_add l v m := Mem.weak_add l v m.

Definition mem_pre_weak_add l v m := Mem.fast_weak_add l v m.

End IdMem.

(** *** Memory operations *)
Module MemOp (Import M : Monad) (MB : MemBasic M).

Section MemOp.

Variable mode : update_mode.

Variable g : G.t.

Definition can_strong_update (l : Loc.t) : bool :=
  match mode with
    | Weak => false
    | Strong => approx_one_loc g l
  end.

Lemma can_strong_update_mor : Proper (Loc.eq ==> Logic.eq) can_strong_update.
Proof.
unfold can_strong_update; intros ls1 ls2 Hls.
destruct mode; [by auto|].
by apply approx_one_loc_mor.
Qed.

Lemma can_strong_update_1 :
  forall l (Heqb : can_strong_update l = true),
    approx_one_loc g l = true.
Proof.
unfold can_strong_update; i.
destruct mode; [discriminate|by auto].
Qed.

Definition mem_lookup (lvs : PowLoc.t) (m : Mem.t) : M.m Val.t :=
  let find_join loc acc_a :=
      do acc <- acc_a;
      do v <- MB.mem_find loc m;
      ret (Val.join acc v) in
  PowLoc.fold find_join lvs (ret Val.bot).

Definition add := MB.mem_add.

Definition weak_add :=
  match mode with
    | Weak => MB.mem_pre_weak_add
    | Strong => MB.mem_weak_add
  end.

Definition mem_update (l : Loc.t) (v : Val.t) (m : Mem.t) : M.m Mem.t :=
  if can_strong_update l then add l v m else weak_add l v m.

Definition mem_wupdate (lvs : PowLoc.t) (v : Val.t) (m : Mem.t)
: M.m Mem.t :=
  let weak_add_v lv m_a :=
      do m <- m_a;
      weak_add lv v m in
  PowLoc.fold weak_add_v lvs (ret m).

End MemOp.

End MemOp.
