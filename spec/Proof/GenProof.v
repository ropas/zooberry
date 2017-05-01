(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** * Proof generation *)

Set Implicit Arguments.

Require Import hpattern vgtac.
Require Import Global.
Require DomCon SemCon SemSen SemSenLocal SemInsenLocal.
Require GamSen DenSenLocal DenInsenLocal.
Require ExtSenLocal ExtInsenLocal ExtFin.
Require CorSen CorSenLocal CorInsenLocal CorFin.
Require Import UserProofType.

Module Make (Import PInput : PINPUT).

Module Sen := SemSen.Make PInput.
Module GSen := GamSen.Make PInput.
Module ESenLocal := ExtSenLocal.Make PInput.
Module EInsenLocal := ExtInsenLocal.Make PInput.
Module EFin := ExtFin.Make PInput.
Module CSen := CorSen.Make PInput.
Module CSenLocal := CorSenLocal.Make PInput.
Module CInsenLocal := CorInsenLocal.Make PInput.
Module CFin := CorFin.Make PInput.

Definition extends (g : G.t) (amap : access_map)
           (s : Table.t Mem.t) (sen_s : Sen.state_t) : Prop :=
  exists senl_s,
    exists insenl_s,
      EFin.extends g s insenl_s
      /\ EInsenLocal.extends g amap insenl_s senl_s
      /\ ESenLocal.extends g amap senl_s sen_s.

Theorem correctness :
  forall (g : G.t) (Hg : G.wf g)
         (locs : PowLoc.t) (fis_mem : Mem.t) (amap : access_map)
         (orig_inputof inputof outputof : Table.t Mem.t)
         (Hvalid :
            valid g amap orig_inputof inputof outputof = true),
  exists s', (forall s (Hsem : SemCon.Sem g s), GSen.State_g s s')
             /\ extends g amap orig_inputof s'.
Proof.
i.
exploit CFin.correctness; eauto
; destruct 1 as [insen_s [Hinsen_post [Hinsen_amap Hinsen_ext]]].
exploit CInsenLocal.correctness; eauto
; destruct 1 as [senl_s [Hsenl_post [Hsenl_amap Hsenl_ext]]].
exploit CSenLocal.correctness; eauto
; destruct 1 as [sen_s [Hsen_post Hsen_ext]].
exists sen_s; split.
- apply CSen.correctness.
  eauto.
- exists senl_s; exists insen_s; repeat split; by auto.
Qed.

End Make.
