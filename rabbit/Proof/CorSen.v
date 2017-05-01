(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** * Correctness sub-proof (Con -- Sen *)

Set Implicit Arguments.

Require Import Global.
Require SemCon SemSen GamSen.
Require Import UserProofType.
Require Import vgtac.

Module Make (Import PInput : PINPUT).

Module Sen := SemSen.Make PInput.

Module GSen := GamSen.Make PInput.

Definition correctness :
  forall (g : G.t)
         s (Hpostfix : Sen.postfix g s),
  forall con_s (Hsem : SemCon.Sem g con_s), GSen.State_g con_s s.
Proof.
i; induction Hsem; simpl GSen.State_g.
{ by apply mem_g_init. }
{
edestruct (Hpostfix cn calls) as [Hpostfix_cmd _]; [by auto|].
eapply mem_g_monotone; [|apply Hpostfix_cmd; by apply Hcmd].
eapply correct_run; by eauto.
}
{
inversion Hrun; i; subst.
- edestruct (Hpostfix (p, n) rets) as [_ [Hpostfix_intra _]]; [by auto|].
  eapply mem_g_monotone; [|apply Hpostfix_intra with cfg; by auto].
  by apply IHHsem.
- edestruct (Hpostfix cn calls) as [_ [_ [Hpostfix_call _]]]; [by auto|].
  eapply mem_g_monotone; [|apply Hpostfix_call; by apply Hsucc].
  by apply IHHsem.
- edestruct (Hpostfix (p, IntraNode.Exit) calls) as [_ [_ [_ Hpostfix_ret]]]
  ; [by inversion Hreach|].
  eapply mem_g_monotone
  ; [|eapply Hpostfix_ret; [reflexivity|by apply Hsucc|by apply Hret]].
  by apply IHHsem.
}
Qed.

End Make.
