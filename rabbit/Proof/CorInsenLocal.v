(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** * Correctness sub-proof (SenLocal -- InsenLocal *)

Set Implicit Arguments.

Require Import vgtac.
Require Import Global.
Require SemSenLocal SemInsenLocal ExtInsenLocal.
Require Import UserProofType.

Module Make (Import PInput : PINPUT).

Module SenLocal := SemSenLocal.Make PInput.

Module InsenLocal := SemInsenLocal.Make PInput.

Module EInsenLocal := ExtInsenLocal.Make PInput.

Section correctness.

Variables (g : G.t) (amap : access_map)
          (s : InsenLocal.state_t)
          (Hpostfix : InsenLocal.postfix g amap s)
          (Hamap : InsenLocal.sound_amap g amap s).

Definition sen_s (sen_idx : SenLocal.index_t) :=
  let '(n, pos, _) := sen_idx in
  s (n, pos).

Lemma cor_cmd : forall cn calls, SenLocal.postfix_cmd g cn calls sen_s.
Proof. i. decompose [and] (Hpostfix cn). unfold sen_s. by auto. Qed.

Lemma cor_intra_edge :
  forall cn calls, SenLocal.postfix_intra_edge g cn calls sen_s.
Proof. i. decompose [and] (Hpostfix cn). unfold sen_s. by auto. Qed.

Lemma cor_intra_call :
  forall cn calls, SenLocal.postfix_intra_call g amap cn calls sen_s.
Proof. i. decompose [and] (Hpostfix cn). unfold sen_s. by auto. Qed.

Lemma cor_inter_call :
  forall cn calls, SenLocal.postfix_inter_call g amap cn calls sen_s.
Proof. i. decompose [and] (Hpostfix cn). unfold sen_s. by auto. Qed.

Lemma cor_inter_ret :
  forall cn calls, SenLocal.postfix_inter_ret g cn calls sen_s.
Proof. i. decompose [and] (Hpostfix cn). unfold sen_s. by auto. Qed.

Definition correctness :
  exists s',
    SenLocal.postfix g amap s'
    /\ SenLocal.sound_amap g amap s'
    /\ EInsenLocal.extends g amap s s'.
Proof.
exists sen_s. split; [|split].
{
unfold SenLocal.postfix. i. repeat split.
- by apply cor_cmd.
- by apply cor_intra_edge.
- by apply cor_intra_call.
- by apply cor_inter_call.
- by apply cor_inter_ret.
}
{
split.
- unfold SenLocal.sound_amap_run. i. by apply Hamap.
- by apply Hamap.
}
{
unfold EInsenLocal.extends, EInsenLocal.extends_mem. i.
by apply Val.eq_refl.
}
Qed.

End correctness.

End Make.
