(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
Definition Mem_g' m m' :=
  forall l v (Hcon : Some v = DomCon.M.find l m),
    Val_g v (Mem.find (Loc_g l) m').

Lemma mem_g'_monotone : monotone Mem.le Mem_g'.
Proof.
unfold monotone, Mem_g'; i.
eapply val_g_monotone; [|by apply Hle].
by apply Hx.
Qed.

Definition Stack_g stack m' :=
  forall pid l (cid : DomCon.CallId.t)
         (Hstack1 : List.In (pid, Some l, cid) stack),
    Val_g (DomCon.val_of_loc l) (Mem.find (SProc_g pid) m').

Lemma stack_g_monotone : monotone Mem.le Stack_g.
Proof.
unfold monotone, Stack_g; i.
eapply val_g_monotone; [|by apply Hle].
eapply Hx; by apply Hstack1.
Qed.

Definition Mem_g (s : DomCon.intra_node_state_t) m' :=
  let '(cid, opt_callee, m, stack) := s in
  Mem_g' m m' /\ Stack_g stack m'.

Lemma mem_g_init :
  forall s', Mem_g SemCon.init_intra_node_state s'.
Proof.
split.
- unfold Mem_g', SemCon.init_mem; i.
  by rewrite DomCon.M.P.F.empty_o in Hcon.
- unfold Stack_g, SemCon.init_stack; i.
  apply False_ind; eapply List.in_nil; by eauto.
Qed.

Lemma mem_g_monotone : monotone Mem.le Mem_g.
Proof.
unfold monotone, Mem_g; destruct c as [[[cid opt_callee] m] stk]; split.
- eapply mem_g'_monotone; [by apply Hx|by apply Hle].
- eapply stack_g_monotone; [by apply Hx|by apply Hle].
Qed.

Lemma mem_g_mor : Proper (Logic.eq ==> Mem.eq ==> iff) Mem_g.
Proof.
intros s1 s2 Hs m1 m2 Hm. split; intros Hmemg.
- eapply mem_g_monotone.
  + rewrite <- Hs. by apply Hmemg.
  + by apply Mem.le_refl.
- eapply mem_g_monotone.
  + rewrite Hs. by apply Hmemg.
  + apply Mem.le_refl. by apply Mem.eq_sym.
Qed.
