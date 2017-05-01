(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
Set Implicit Arguments.

Require Import Morphisms.
Require Import ZArith.
Require Import DItv.
Require Import DomArrayBlk.
Require Import UserInputType.
Require Import UserProofType.
Require Import UserInput.
Require GenFunc.
Require Import VocabA.
Require Import vgtac.
Require Import Monad.
Require Import Fold.

Include Input.
Include GenFunc.Make.

Definition Var_g (x : DomCon.Var.t) : Var.t :=
  match x with
  | DomCon.Var.Inl gx => Var.Inl gx
  | DomCon.Var.Inr (_, f, lx) => Var.Inr (f, lx)
  end.

Lemma var_g_mor : Proper (DomCon.Var.eq ==> Var.eq) Var_g.
Proof.
inversion 1.
- by constructor.
- destruct x' as [[n1 f1] x'], y' as [[n2 f2] y2']. simpl in Heq.
  constructor. tauto.
Qed.

Definition Allocsite_g (a : DomCon.Allocsite.t) : Allocsite.t :=
  match a with
  | DomCon.Allocsite.Inl n => Allocsite.Inl n
  | DomCon.Allocsite.Inr (DomCon.ExtAllocsite.Inl f) =>
    Allocsite.Inr (ExtAllocsite.Inl f)
  | DomCon.Allocsite.Inr (DomCon.ExtAllocsite.Inr f) =>
    Allocsite.Inr (ExtAllocsite.Inr f)
  end.

Definition allocsite_g_mor :
  Proper (DomCon.Allocsite.eq ==> Allocsite.eq) Allocsite_g.
Proof.
inversion 1.
- constructor. tauto.
- inversion Heq.
  + constructor. constructor. by auto.
  + constructor. constructor. by auto.
Qed.

Definition VarRegion_g (vr : DomCon.VarRegion.t) : VarAllocsite.t :=
  match vr with
  | DomCon.VarRegion.Inl x => VarAllocsite.Inl (Var_g x)
  | DomCon.VarRegion.Inr (_, a, _) => VarAllocsite.Inr (Allocsite_g a)
  end.

Lemma varregion_g_mor :
  Proper (DomCon.VarRegion.eq ==> VarAllocsite.eq) VarRegion_g.
Proof.
inversion 1.
- constructor. by apply var_g_mor.
- destruct x' as [[n1 a1] [[o1 s1] st1]], y' as [[n2 a2] [[o2 s2] st2]].
  simpl in *.
  constructor. apply allocsite_g_mor. by apply Heq.
Qed.

Fixpoint Fields_g (fs : DomCon.Fields.t) : Fields.t :=
  match fs with
  | DomCon.Fields.nil => Fields.nil
  | DomCon.Fields.cons f tl => Fields.cons f (Fields_g tl)
  end.

Lemma fields_g_mor :
  Proper (DomCon.Fields.eq ==> Fields.eq) Fields_g.
Proof.
unfold Fields.eq. induction DNList.size.
- intros f1 f2 Hf. apply Fields.eq_zero.
- induction 1.
  + apply Fields.eq_nil.
  + apply Fields.eq_cons; [by auto|by apply IHn].
Qed.

Definition Loc_g (l : DomCon.Loc.t) : Loc.t :=
  let (vr, fs) := l in
  Loc.Inl (VarRegion_g vr, Fields_g fs).

Lemma loc_g_mor : Proper (DomCon.Loc.eq ==> Loc.eq) Loc_g.
Proof.
intros [vr1 f1] [vr2 f2] Hl. inversion Hl. constructor. simpl in *; split.
- by apply varregion_g_mor.
- by apply fields_g_mor.
Qed.

Definition Itv_g := Itv.gamma.

Inductive ArrayBlk_g' : DomCon.Region.t -> ArrayBlk.t -> Prop :=
| ArrayBlk_g_intro :
    forall s a o sz st o' sz' st' ab
           (Ho : Itv_g o o') (Hsz : Itv_g sz sz' ) (Hst : Itv_g st st')
           (Hab : ArrayBlk.find (Allocsite_g a) ab = (o', sz', st')),
      ArrayBlk_g' (s, a, (o, sz, st)) ab.

Definition ArrayBlk_g := ArrayBlk_g'.

Inductive Val_g' : DomCon.val_t -> Val.t -> Prop :=
| Val_g_z :
    forall z i ls ab ps (Hz : Itv_g z i), Val_g' (inl (inl z)) (i, ls, ab, ps)
| Val_g_loc :
    forall l i ls ab ps (Hl : PowLoc.mem (Loc_g l) ls = true),
      Val_g' (inl (inr l)) (i, ls, ab, ps)
| Val_g_ab :
    forall r i ls ab ps (Hl : ArrayBlk_g r ab),
      Val_g' (inl (inr (DomCon.VarRegion.Inr r, DomCon.Fields.nil)))
            (i, ls, ab, ps)
| Val_g_proc :
    forall p i ls ab ps (Hp : PowProc.mem p ps = true),
      Val_g' (inr p) (i, ls, ab, ps)
.

Definition Val_g := Val_g'.

(** Abstraction of Proc.t in DomCon.stack1. *)
Definition SProc_g (f : DomCon.Proc.t) : Loc.t := Loc.Inr f.

Lemma arrayBlk_g_monotone : monotone ArrayBlk.le ArrayBlk_g.
Proof.
intros v x y. inversion 1; i. subst.
assert (ArrInfo.le (o', sz', st') (ArrayBlk.find (Allocsite_g a) y)) as Hy
; [rewrite <- Hab; apply Hle|].
remember (ArrayBlk.find (Allocsite_g a) y) as oss'.
destruct oss' as [[o'' sz''] st''].
inversion Hy as [[Ho'' Hsz''] Hst'']; simpl in Ho'', Hsz'', Hst''.
apply ArrayBlk_g_intro with o'' sz'' st''.
- by apply Itv.gamma_monotone with o'.
- by apply Itv.gamma_monotone with sz'.
- by apply Itv.gamma_monotone with st'.
- by auto.
Qed.

Lemma val_g_monotone : monotone Val.le Val_g.
Proof.
intros v [[[i ls] ab] ps] [[[i' ls'] ab'] ps'] Hx Hle.
unfold Val.le, Val.E3.le, Val.E2.le in Hle; simpl in Hle.
destruct Hle as [[[Hi Hls] Hab] Hps].
inversion Hx; subst.
- apply Val_g_z. by apply Itv.gamma_monotone with i.
- apply Val_g_loc. by apply PowLoc.le_mem_true with ls.
- apply Val_g_ab. by apply arrayBlk_g_monotone with ab.
- apply Val_g_proc. by apply PowProc.le_mem_true with ps.
Qed.

Lemma val_g_mor : Proper (Logic.eq ==> Val.eq ==> Basics.impl) Val_g.
Proof.
intros v1 v2 Hv v1' v2' Hv'; intros Hvalg.
eapply val_g_monotone; [rewrite <- Hv; by apply Hvalg|by apply Val.le_refl].
Qed.

Lemma var_g_eq1 :
  forall x1 x2 x (Heq1 : Var.eq (Var_g x1) (Var.Inl x))
     (Heq2 : Var.eq (Var_g x2) (Var.Inl x)),
    DomCon.Var.eq x1 x2.
Proof.
i. unfold Var_g in *.
destruct x1 as [x1|[[? ?] ?]]; [|by inversion Heq1].
destruct x2 as [x2|[[? ?] ?]]; [|by inversion Heq2].
inversion_clear Heq1; inversion_clear Heq2. subst.
by apply DomCon.Var.eq_refl.
Qed.

Lemma var_g_eq2 g :
  forall m (Hm : SemCon.wf_non_rec_mem g m)
     f (Hf : Global.G.is_rec f g = false)
     x1 fs1 x2 fs2 x
     (Hml1 : DomCon.M.In (elt:=DomCon.val_t) (DomCon.VarRegion.Inl x1, fs1) m)
     (Hml2 : DomCon.M.In (elt:=DomCon.val_t) (DomCon.VarRegion.Inl x2, fs2) m)
     (Heq1 : Var.eq (Var_g x1) (Var.Inr (f, x)))
     (Heq2 : Var.eq (Var_g x2) (Var.Inr (f, x))),
    DomCon.Var.eq x1 x2.
Proof.
i. unfold Var_g in *.
destruct x1 as [x1|[[? ?] ?]]; [by inversion Heq1|].
destruct x2 as [x2|[[? ?] ?]]; [by inversion Heq2|].
inversion_clear Heq1; inversion_clear Heq2; simpl in *.
destruct Heq as [Hf1 Hx1], Heq0 as [Hf2 Hx2]. subst.
constructor; s.
split; [|by auto]. split; [|by auto].
eapply Hm; [by apply Hf|by apply Hml1|by apply Hml2].
Qed.

Lemma varregion_g_eq1 :
  forall vr1 vr2 x
     (Hveq1 : VarAllocsite.eq (VarRegion_g vr1) (VarAllocsite.Inl (Var.Inl x)))
     (Hveq2 : VarAllocsite.eq (VarRegion_g vr2) (VarAllocsite.Inl (Var.Inl x))),
    DomCon.VarRegion.eq vr1 vr2.
Proof.
i. unfold VarRegion_g in *.
destruct vr1 as [x1|[[? ?] ?]]; [|by inversion Hveq1].
destruct vr2 as [x2|[[? ?] ?]]; [|by inversion Hveq2].
inversion_clear Hveq1; inversion_clear Hveq2.
constructor. eapply var_g_eq1; [by apply Heq|by apply Heq0].
Qed.

Lemma varregion_g_eq2 g :
  forall m (Hm : SemCon.wf_non_rec_mem g m)
     f (Hf : Global.G.is_rec f g = false)
     vr1 fs1 (Hml1 : DomCon.M.In (elt:=DomCon.val_t) (vr1, fs1) m)
     vr2 fs2 (Hml2 : DomCon.M.In (elt:=DomCon.val_t) (vr2, fs2) m)
     x
     (Hveq1 :
        VarAllocsite.eq (VarRegion_g vr1) (VarAllocsite.Inl (Var.Inr (f, x))))
     (Hveq2 :
        VarAllocsite.eq (VarRegion_g vr2) (VarAllocsite.Inl (Var.Inr (f, x)))),
    DomCon.VarRegion.eq vr1 vr2.
Proof.
i. unfold VarRegion_g in *.
destruct vr1 as [x1|[[? ?] ?]]; [|by inversion Hveq1].
destruct vr2 as [x2|[[? ?] ?]]; [|by inversion Hveq2].
inversion_clear Hveq1; inversion_clear Hveq2.
constructor. eapply var_g_eq2
; [ by apply Hm | by apply Hf | by apply Hml1 | by apply Hml2
  | by apply Heq | by apply Heq0 ].
Qed.

Lemma fields_g_nil' :
  forall f n (Hn : n > 0) (Hf : Fields.eq' n (Fields_g f) Fields.nil),
    f = DomCon.Fields.nil.
Proof.
destruct n; [by inversion 1|i].
destruct f; [reflexivity|].
simpl in Hf. by inversion Hf.
Qed.

Lemma fields_g_nil :
  forall f (Hf : Fields.eq (Fields_g f) Fields.nil),
    f = DomCon.Fields.nil.
Proof.
intros. eapply fields_g_nil'; [|by apply Hf].
unfold DNList.size. omega.
Qed.

Lemma prop_approx_one_loc :
  forall g l (Hl: approx_one_loc g l = true)
     m (Hm : SemCon.wf_non_rec_mem g m)
     l1 (Hl1: Loc.eq (Loc_g l1) l) (Hml1 : DomCon.M.In l1 m)
     l2 (Hl2: Loc.eq (Loc_g l2) l) (Hml2 : DomCon.M.In l2 m),
    DomCon.Loc.eq l1 l2.
Proof.
i. unfold approx_one_loc in Hl.
destruct l as [[[[x|[f x]]|a] fs]|p]; [| |discriminate|discriminate].
- unfold Loc_g in *. destruct l1 as [vr1 fs1], l2 as [vr2 fs2].
  inversion_clear Hl1; inversion_clear Hl2. simpl in Heq, Heq0.
  destruct Heq as [Hveq1 Hfs1], Heq0 as [Hveq2 Hfs2].
  constructor; s.
  + eapply varregion_g_eq1; [by apply Hveq1|by apply Hveq2].
  + destruct fs; [|discriminate].
    rewrite (fields_g_nil _ Hfs1), (fields_g_nil _ Hfs2). constructor.
- unfold Loc_g in *. destruct l1 as [vr1 fs1], l2 as [vr2 fs2].
  inversion_clear Hl1; inversion_clear Hl2. simpl in Heq, Heq0.
  destruct Heq as [Hveq1 Hfs1], Heq0 as [Hveq2 Hfs2].
  constructor; s.
  + destruct fs; [|discriminate].
    eapply varregion_g_eq2
    ; [ by apply Hm | apply Bool.negb_true_iff; by apply Hl
      | by apply Hml1 | by apply Hml2 | by apply Hveq1 | by apply Hveq2 ].
  + destruct fs; [|discriminate].
    rewrite (fields_g_nil _ Hfs1), (fields_g_nil _ Hfs2). constructor.
Qed.

Inductive Loc_opt_g : option DomCon.Loc.t -> PowLoc.t -> Prop :=
| Loc_opt_g_none : forall l', Loc_opt_g None l'
| Loc_opt_g_some :
    forall l l' (Hv : PowLoc.mem (Loc_g l) l' = true), Loc_opt_g (Some l) l'.

Import RunOnly RunOnly.SemMem RunOnly.SemEval.

Load MemGCommon.
Load MemPfCommon.

Lemma cor_eval_const :
  forall c v (Hc : SemCon.Eval_const c v), Val_g v (SemEval.eval_const c).
Proof.
destruct 1; constructor.
- by apply Itv.cor_itv_top.
- by apply Itv.cor_of_int.
- by apply Itv.cor_of_int.
- unfold Itv.of_ints. destruct (Z_le_dec lb ub); [constructor|omega].
  + constructor; omega.
  + constructor; omega.
- by apply Itv.cor_itv_top.
Qed.

Lemma val_g_bot_false : forall x, ~ (Val_g x Val.bot).
Proof.
inversion_clear 1; subst.
- by inversion Hz.
- by inversion Hl.
- inversion_clear Hl; subst.
  inversion Hab; subst.
  by inversion Hsz.
- by inversion Hp.
Qed.

Lemma cor_eval_uop :
  forall op v v' abs_v (Hu : SemCon.Eval_uop op v v') (Habs : Val_g v abs_v),
    Val_g v' (SemEval.eval_uop op abs_v).
Proof.
i. unfold SemEval.eval_uop.
destruct (Val.eq_dec abs_v Val.bot)
; [ eapply val_g_mor in Habs
    ; [by apply val_g_bot_false in Habs|reflexivity|by apply e] |].
inversion Hu; subst.
- inversion Habs; subst. constructor.
  rewrite <- Z.sub_0_l. apply Itv.cor_minus; [by apply Itv.cor_of_int|by auto].
- inversion Habs; subst. constructor.
  unfold Itv.b_not_itv. apply Itv.unknown_unary_prop; i.
  inversion Hz; subst. by inversion FH.
- inversion Habs; subst. constructor.
  eapply Itv.not_itv_prop1; [by apply Ht|by auto].
- inversion Habs; subst. constructor.
  eapply Itv.not_itv_prop2; by auto.
Qed.

Lemma itv_non_bot :
  forall z abs_v (Habs : Val_g (DomCon.val_of_z z) abs_v),
    ~ (Itv.eq (itv_of_val abs_v) Itv.bot).
Proof.
i. destruct abs_v as [[[i ls] ab] ps].
inversion Habs; subst.
eapply Itv.non_bot; [by apply Hz|by apply FH].
Qed.

Lemma itv_non_zero :
  forall z abs_v (Ht : z <> 0%Z) (Habs : Val_g (DomCon.val_of_z z) abs_v),
    ~ (Itv.eq (itv_of_val abs_v) Itv.zero).
Proof.
inversion 2; subst. s; i.
exploit Itv.gamma_mor; [reflexivity|by apply FH|by apply Hz|].
inversion 1; subst.
elim Ht. inversion Hle1; inversion Hle2. omega.
Qed.

Local Open Scope sumbool.

Lemma cor_plus_offset :
  forall step alloc o sz st z ab i
     (Hab : ArrayBlk_g (step, alloc, (o, sz, st)) ab) (Hz : Itv_g z i),
    ArrayBlk_g (step, alloc, ((o + z)%Z, sz, st)) (ArrayBlk.plus_offset ab i).
Proof.
inversion 1; subst; i.
apply ArrayBlk_g_intro with (o':=Itv.plus o' i) (st':=st') (sz':=sz')
; [by apply Itv.cor_plus|by auto|by auto|].
unfold ArrayBlk.plus_offset.
destruct (Itv.eq_dec i Itv.bot)
; [exploit Itv.non_bot; [by apply Hz|by apply e|by auto]|].
erewrite ArrayBlk.map_1; [| |by apply Hab0].
- unfold ArrInfo.plus_offset.
  destruct (Itv.eq_dec Itv.bot o'); [|reflexivity].
  exploit Itv.non_bot; [by apply Ho|by apply Itv.eq_sym|by auto].
- unfold ArrInfo.plus_offset. simpl.
  destruct (Itv.eq_dec Itv.bot Itv.bot)
  ; [by auto|elim f0; by apply Itv.eq_refl].
Qed.

Lemma cor_minus_offset :
  forall step alloc o sz st z ab i
     (Hab : ArrayBlk_g (step, alloc, (o, sz, st)) ab) (Hz : Itv_g z i),
    ArrayBlk_g (step, alloc, ((o - z)%Z, sz, st)) (ArrayBlk.minus_offset ab i).
Proof.
inversion 1; subst; i.
apply ArrayBlk_g_intro with (o':=Itv.minus o' i) (st':=st') (sz':=sz')
; [by apply Itv.cor_minus|by auto|by auto|].
unfold ArrayBlk.minus_offset.
destruct (Itv.eq_dec i Itv.bot)
; [exploit Itv.non_bot; [by apply Hz|by apply e|by auto]|].
erewrite ArrayBlk.map_1; [| |by apply Hab0].
- unfold ArrInfo.minus_offset.
  destruct (Itv.eq_dec Itv.bot o'); [|reflexivity].
  exploit Itv.non_bot; [by apply Ho|by apply Itv.eq_sym|by auto].
- unfold ArrInfo.minus_offset. simpl.
  destruct (Itv.eq_dec Itv.bot Itv.bot)
  ; [by auto|elim f0; by apply Itv.eq_refl].
Qed.

Lemma cor_plus_pi :
  forall step alloc o sz st z v i
     (Hv : Val_g
                (DomCon.val_of_loc
                   (DomCon.loc_of_alloc
                      step alloc (o, sz, st) DomCon.Fields.nil))
                v)
     (Hz : Itv_g z i),
    Val_g
      (DomCon.val_of_loc
         (DomCon.loc_of_alloc step alloc ((o + z)%Z, sz, st) DomCon.Fields.nil))
      (Val.join
         (SemEval.array_loc_of_val v)
         (val_of_array (ArrayBlk.plus_offset (array_of_val v) i))).
Proof.
i; inversion_clear Hv; subst.
- eapply val_g_monotone; [apply Val_g_loc|by apply Val.join_left].
  unfold DomCon.loc_of_alloc, Loc_g, VarRegion_g in *.
  apply PowLoc.filter1; [by apply SemEval.is_array_loc_mor|by apply Hl|by auto].
- eapply val_g_monotone; [apply Val_g_ab|by apply Val.join_right].
  by apply cor_plus_offset.
Qed.

Lemma cor_minus_pi :
  forall step alloc o sz st z v i
     (Hv : Val_g
                (DomCon.val_of_loc
                   (DomCon.loc_of_alloc
                      step alloc (o, sz, st) DomCon.Fields.nil))
                v)
     (Hz : Itv_g z i),
    Val_g
      (DomCon.val_of_loc
         (DomCon.loc_of_alloc step alloc ((o - z)%Z, sz, st) DomCon.Fields.nil))
      (Val.join
         (SemEval.array_loc_of_val v)
         (val_of_array (ArrayBlk.minus_offset (array_of_val v) i))).
Proof.
i; inversion_clear Hv; subst.
- eapply val_g_monotone; [apply Val_g_loc|by apply Val.join_left].
  unfold DomCon.loc_of_alloc, Loc_g, VarRegion_g in *.
  apply PowLoc.filter1; [by apply SemEval.is_array_loc_mor|by apply Hl|by auto].
- eapply val_g_monotone; [apply Val_g_ab|by apply Val.join_right].
  by apply cor_minus_offset.
Qed.

Lemma cor_eval_bop :
  forall op v1 v2 v' abs_v1 abs_v2 (Hu : SemCon.Eval_bop op v1 v2 v')
     (Habs1 : Val_g v1 abs_v1) (Habs2 : Val_g v2 abs_v2),
    Val_g v' (SemEval.eval_bop op abs_v1 abs_v2).
Proof.
inversion_clear 1; subst.
{                               (* PlusA *)
i. unfold SemEval.eval_bop. constructor.
inversion_clear Habs1; inversion_clear Habs2. by apply Itv.cor_plus.
}
{                               (* PlusPI *)
i. unfold SemEval.eval_bop.
inversion_clear Habs2; subst.
by apply cor_plus_pi.
}
{                               (* IndexPI *)
i. unfold SemEval.eval_bop.
inversion_clear Habs2; subst.
by apply cor_plus_pi.
}
{                               (* MinusA *)
i. unfold SemEval.eval_bop.
inversion_clear Habs1; inversion_clear Habs2.
constructor; by apply Itv.cor_minus.
}
{                               (* MinusPI *)
i. unfold SemEval.eval_bop.
inversion_clear Habs2; subst.
by apply cor_minus_pi.
}
{                               (* Mult *)
i. unfold SemEval.eval_bop.
inversion_clear Habs1; inversion_clear Habs2. constructor.
by apply Itv.times_prop.
}
{                               (* Div *)
i. unfold SemEval.eval_bop. constructor.
inversion_clear Habs1; inversion_clear Habs2.
by apply Itv.divide_prop.
}
{                               (* Mod *)
i. unfold SemEval.eval_bop, Itv.mod_itv.
constructor. apply Itv.unknown_binary_prop; i.
- by apply itv_non_bot in Habs1.
- by apply itv_non_bot in Habs2.
}
{                               (* Shiftlt *)
i. unfold SemEval.eval_bop, Itv.l_shift_itv.
constructor. apply Itv.unknown_binary_prop; i.
- by apply itv_non_bot in Habs1.
- by apply itv_non_bot in Habs2.
}
{                               (* Shiftrt *)
i. unfold SemEval.eval_bop, Itv.r_shift_itv.
constructor. apply Itv.unknown_binary_prop; i.
- by apply itv_non_bot in Habs1.
- by apply itv_non_bot in Habs2.
}
{                               (* Lt *)
i. unfold SemEval.eval_bop. constructor.
inversion_clear Habs1; inversion_clear Habs2.
by apply Itv.cor_lt1 with (z1:=z1) (z2:=z2).
}
{                               (* Lt *)
i. unfold SemEval.eval_bop. constructor.
inversion_clear Habs1; inversion_clear Habs2.
by apply Itv.cor_lt0 with (z1:=z1) (z2:=z2).
}
{                               (* Gt *)
i. unfold SemEval.eval_bop. constructor.
inversion_clear Habs1; inversion_clear Habs2.
unfold Itv.gt_itv.
apply Itv.cor_lt1 with (z1:=z2) (z2:=z1); [omega|by auto|by auto].
}
{                               (* Gt *)
i. unfold SemEval.eval_bop. constructor.
inversion_clear Habs1; inversion_clear Habs2.
unfold Itv.gt_itv.
apply Itv.cor_lt0 with (z1:=z2) (z2:=z1); [intro; elim Hle; omega|by auto|by auto].
}
{                               (* Le *)
i. unfold SemEval.eval_bop. constructor.
inversion_clear Habs1; inversion_clear Habs2.
apply Itv.cor_le1 with (z1:=z1) (z2:=z2); by auto.
}
{
i. unfold SemEval.eval_bop. constructor.
inversion_clear Habs1; inversion_clear Habs2.
apply Itv.cor_le0 with (z1:=z1) (z2:=z2); by auto.
}
{                               (* Ge *)
i. unfold SemEval.eval_bop. constructor.
inversion_clear Habs1; inversion_clear Habs2.
unfold Itv.ge_itv.
apply Itv.cor_le1 with (z1:=z2) (z2:=z1); [omega|by auto|by auto].
}
{                               (* Ge *)
i. unfold SemEval.eval_bop. constructor.
inversion_clear Habs1; inversion_clear Habs2.
unfold Itv.ge_itv.
apply Itv.cor_le0 with (z1:=z2) (z2:=z1); [intro; elim Hlt; omega|by auto|by auto].
}
{                               (* Eq *)
i. unfold SemEval.eval_bop. constructor.
inversion_clear Habs1; inversion_clear Habs2.
apply Itv.cor_eq1 with (z:=z2); by auto.
}
{                               (* Eq *)
i. unfold SemEval.eval_bop. constructor.
inversion_clear Habs1; inversion_clear Habs2.
apply Itv.cor_eq0 with (z1:=z1) (z2:=z2); by auto.
}
{                               (* Ne *)
i. unfold SemEval.eval_bop. constructor.
inversion_clear Habs1; inversion_clear Habs2.
apply Itv.cor_ne1 with (z1:=z1) (z2:=z2); by auto.
}
{                               (* Ne *)
i. unfold SemEval.eval_bop. constructor.
inversion_clear Habs1; inversion_clear Habs2.
apply Itv.cor_ne0 with (z:=z2); by auto.
}
{                               (* BAnd *)
i. unfold SemEval.eval_bop, Itv.b_and_itv.
constructor. apply Itv.unknown_binary_prop; i.
- by apply itv_non_bot in Habs1.
- by apply itv_non_bot in Habs2.
}
{                               (* BXor *)
i. unfold SemEval.eval_bop, Itv.b_xor_itv.
constructor. apply Itv.unknown_binary_prop; i.
- by apply itv_non_bot in Habs1.
- by apply itv_non_bot in Habs2.
}
{                               (* BOr *)
i. unfold SemEval.eval_bop, Itv.b_or_itv.
constructor. apply Itv.unknown_binary_prop; i.
- by apply itv_non_bot in Habs1.
- by apply itv_non_bot in Habs2.
}
{                               (* LAnd *)
i. unfold SemEval.eval_bop, Itv.and_itv.
dest_if_dec; [|dest_if_dec; [|dest_if_dec]].
- apply False_ind. destruct o; by eauto using itv_non_bot.
- apply False_ind. destruct Hz. destruct o as [o|o].
  + by apply (itv_non_zero (z:=z1)) in o.
  + by apply (itv_non_zero (z:=z2)) in o.
- constructor. by apply Itv.true_itv_prop.
- constructor. by apply Itv.unknown_bool_prop1.
}
{                               (* LAnd *)
i. unfold SemEval.eval_bop, Itv.and_itv.
dest_if_dec; [|dest_if_dec; [|dest_if_dec]].
- apply False_ind. destruct o; by eauto using itv_non_bot.
- constructor. by apply Itv.false_itv_prop.
- destruct a1 as [a1 _]; elim a1. inversion Habs1; subst. by apply Itv.false_itv1.
- constructor. by apply Itv.unknown_bool_prop0.
}
{                               (* LAnd *)
i. unfold SemEval.eval_bop, Itv.and_itv.
dest_if_dec; [|dest_if_dec; [|dest_if_dec]].
- apply False_ind. destruct o; by eauto using itv_non_bot.
- constructor. by apply Itv.false_itv_prop.
- destruct a1 as [_ a1]; elim a1. inversion Habs2; subst. by apply Itv.false_itv1.
- constructor. by apply Itv.unknown_bool_prop0.
}
{                               (* LOr *)
i. unfold SemEval.eval_bop, Itv.or_itv.
dest_if_dec; [|dest_if_dec; [|dest_if_dec]].
- apply False_ind. destruct o; by eauto using itv_non_bot.
- destruct a0; by apply itv_non_zero in Habs1.
- constructor. by apply Itv.true_itv_prop.
- constructor. by apply Itv.unknown_bool_prop1.
}
{                               (* LOr *)
i. unfold SemEval.eval_bop, Itv.or_itv.
dest_if_dec; [|dest_if_dec; [|dest_if_dec]].
- apply False_ind. destruct o; by eauto using itv_non_bot.
- destruct a0; by apply itv_non_zero in Habs2.
- constructor. by apply Itv.true_itv_prop.
- constructor. by apply Itv.unknown_bool_prop1.
}
{                               (* LOr *)
i. unfold SemEval.eval_bop, Itv.or_itv.
dest_if_dec; [|dest_if_dec; [|dest_if_dec]].
- apply False_ind. destruct o; by eauto using itv_non_bot.
- constructor. by apply Itv.false_itv_prop.
- destruct o0 as [o0|o0]; elim o0.
  + inversion Habs1; subst; by apply Itv.false_itv1.
  + inversion Habs2; subst; by apply Itv.false_itv1.
- constructor. by apply Itv.unknown_bool_prop0.
}
Qed.

Local Close Scope sumbool.

Lemma eval_zero :
  forall abs_v (Habs : Val_g (DomCon.val_of_z 0) abs_v),
    Itv.le Itv.zero (DomAbs.itv_of_val abs_v).
Proof. inversion 1; inversion Hz; subst. by constructor. Qed.

Lemma cor_cast :
  forall step alloc o o' sz sz' st st' ab
         (Ho' : o' = (c_div (o * st) st')%Z)
         (Hsz' : sz' = (c_div (sz * st) st')%Z)
         (Hab : ArrayBlk_g (step, alloc, (o, sz, st)) ab),
    ArrayBlk_g (step, alloc, (o', sz', st')) (ArrayBlk.cast_array_int st' ab).
Proof.
inversion 3; subst. econstructor.
- apply Itv.divide_prop; [apply Itv.times_prop|].
  + by apply Ho.
  + by apply Hst.
  + by apply Itv.cor_of_int.
- apply Itv.divide_prop; [apply Itv.times_prop|].
  + by apply Hsz.
  + by apply Hst.
  + by apply Itv.cor_of_int.
- by apply Itv.cor_of_int.
- unfold ArrayBlk.cast_array_int, ArrayBlk.cast_array.
  rewrite ArrayBlk.map_1 with (v:=(o'0, sz'0, st'0)); [| |by auto].
  + destruct (Itv.eq_dec Itv.bot st'0); [|by auto].
    apply Itv.non_bot in Hst; [by elim Hst|by apply Itv.eq_sym].
  + s; destruct (Itv.eq_dec Itv.bot Itv.bot)
    ; [reflexivity|by elim f; apply Itv.eq_refl].
Qed.

Lemma cor_pow_loc_of_array :
  forall r ab (Hr : ArrayBlk_g r ab),
    PowLoc.mem (Loc_g (DomCon.VarRegion.Inr r, DomCon.Fields.nil))
               (ArrayBlk.pow_loc_of_array ab) = true.
Proof.
inversion 1; subst; s.
unfold ArrayBlk.pow_loc_of_array.
eapply ArrayBlk.foldi_1
with (teq:=PowLoc.eq) (k:=Allocsite_g a) (v:=(o', sz', st')).
- constructor
  ; [ intros ?; by apply PowLoc.eq_refl
    | intros ? ? ?; by apply PowLoc.eq_trans
    | intros ? ?; by apply PowLoc.eq_sym ].
- intros ls1 ls2 Hls; split; intro Hmem.
  + rewrite PowLoc.mem_mor
    ; [by apply Hmem|by apply Loc.eq_refl|by apply PowLoc.eq_sym].
  + rewrite PowLoc.mem_mor; [by apply Hmem|by apply Loc.eq_refl|by auto].
- rewrite Hab; by apply ArrInfo.eq_refl.
- destruct (ArrInfo.eq_dec ArrInfo.bot (o', sz', st'))
  ; [ inversion e; simpl in H0; apply Itv.non_bot in Hst
      ; [by elim Hst|by apply Itv.eq_sym] |].
  i; apply DomBasic.PowLoc.mem_add_1; by apply Loc.eq_refl.
- i; destruct (ArrInfo.eq_dec ArrInfo.bot v)
  ; [by apply PowLoc.eq_refl|by elim f].
- i; destruct (ArrInfo.eq_dec ArrInfo.bot v); [by auto|].
  by apply PowLoc.mem_add_3.
- i; destruct (ArrInfo.eq_dec ArrInfo.bot v1).
  + destruct (ArrInfo.eq_dec ArrInfo.bot v2)
    ; [|elim f; eapply ArrInfo.eq_trans; [by apply e|by auto]].
    by auto.
  + destruct (ArrInfo.eq_dec ArrInfo.bot v2)
    ; [ elim f; eapply ArrInfo.eq_trans; [by apply e|by apply ArrInfo.eq_sym]
      | rewrite <- Hf ].
    apply PowLoc.mem_mor; [by auto|].
    apply PowLoc.add_mor; [|by apply PowLoc.eq_refl].
    apply DomBasic.loc_of_allocsite_mor; by apply Allocsite.eq_sym.
Qed.

Lemma cor_deref_of_val :
  forall l v (Habs : Val_g (DomCon.val_of_loc l) v),
    PowLoc.mem (Loc_g l) (SemEval.deref_of_val v) = true.
Proof.
inversion 1; subst.
- unfold SemEval.deref_of_val.
  eapply PowLoc.le_mem_true; [by apply PowLoc.join_left|by apply Hl].
- unfold SemEval.deref_of_val.
  eapply PowLoc.le_mem_true; [by apply PowLoc.join_right|].
  apply cor_pow_loc_of_array. by apply Hl.
Qed.

Lemma cor_fields_app :
  forall fs n f,
    Fields.eq' n (Fields_g (SemCon.fields_app1 fs f))
               (Fields.app (Fields_g fs) f).
Proof.
induction fs.
- i; s; by apply Fields.eq'_refl.
- i; s. destruct n; [by constructor|].
  constructor; [by auto|by apply IHfs].
Qed.

Lemma cor_append_field :
  forall va fs f v (Hl : Val_g (DomCon.val_of_loc (va, fs)) v),
    PowLoc.mem (Loc_g (va, SemCon.fields_app1 fs f))
               (PowLoc.join
                  (DomBasic.pow_loc_append_field (DomAbs.pow_loc_of_val v) f)
                  (ArrayBlk.pow_loc_of_struct_w_field (DomAbs.array_of_val v) f)) =
    true.
Proof.
inversion 1; subst; clear Hl.
- eapply PowLoc.mem_monotone1
  ; [by apply Loc.eq_refl|by apply PowLoc.join_left|].
  unfold DomBasic.pow_loc_append_field.
  remember (fun l : Loc.t' => append_field l f) as append_f.
  assert
    (Loc.eq (Loc_g (va, SemCon.fields_app1 fs f)) (append_f (Loc_g (va, fs))))
  as Hl.
  + rewrite Heqappend_f. unfold append_field, Loc_g. constructor; s.
    split; [by apply VarAllocsite.eq_refl|by apply cor_fields_app].
  + rewrite Hl. apply SMLocLoc.map_1; [|by apply Hl0].
    intros l1 l2 Hl'. subst. by apply DomBasic.append_field_mor.
- eapply PowLoc.mem_monotone1
  ; [by apply Loc.eq_refl|by apply PowLoc.join_right|].
  unfold ArrayBlk.pow_loc_of_struct_w_field.
  inversion Hl0; subst; clear Hl0.
  apply ArrayBlk.foldi_1
  with (teq:=PowLoc.eq) (k:=Allocsite_g a) (v:=(o', sz', st')).
  + constructor
    ; [ intros ?; by apply PowLoc.eq_refl
      | intros ? ? ?; by apply PowLoc.eq_trans
      | intros ? ?; by apply PowLoc.eq_sym ].
  + intros l1 l2 Hl; split; intro Hmem.
    * rewrite DomBasic.PowLoc.mem_mor
      ; [by apply Hmem|by apply Loc.eq_refl|by apply PowLoc.eq_sym].
    * rewrite DomBasic.PowLoc.mem_mor
      ; [by apply Hmem|by apply Loc.eq_refl|by auto].
  + unfold DomAbs.array_of_val.
    rewrite <- Hab; by apply ArrInfo.eq_refl.
  + i; dest_if_dec
    ; [ inversion e; simpl in H0; apply Itv.non_bot in Hst
        ; [by elim Hst|by auto] |].
    apply PowLoc.mem_add_1.
    constructor; split; [by apply VarAllocsite.eq_refl|by apply cor_fields_app].
  + i. dest_if_dec. elim f0; by apply ArrInfo.eq_sym.
  + i; dest_if_dec. by apply PowLoc.mem_add_3.
  + i. destruct (ArrInfo.eq_dec v1 ArrInfo.bot).
    * destruct (ArrInfo.eq_dec v2 ArrInfo.bot)
      ; [| elim f0; eapply ArrInfo.eq_trans
           ; [apply ArrInfo.eq_sym; by apply Hv|by auto] ].
      by auto.
    * destruct (ArrInfo.eq_dec v2 ArrInfo.bot)
      ; [elim f0; eapply ArrInfo.eq_trans; [by apply Hv|by auto]|].
      rewrite <- Hf. apply PowLoc.mem_mor; [by apply Loc.eq_refl|].
      apply PowLoc.add_mor; [|by apply PowLoc.eq_refl].
      apply DomBasic.append_field_mor; [|by apply Field.eq_refl].
      apply DomBasic.loc_of_allocsite_mor; by apply Allocsite.eq_sym.
Qed.

Lemma cor_plus_offset_val :
  forall step alloc o idx sz st abs_idx abs_v
         (Habs : Val_g
                   (DomCon.val_of_loc
                      (DomCon.loc_of_alloc
                         step alloc (o, sz, st) DomCon.Fields.nil))
                   abs_v)
         (Hidx : Itv_g idx abs_idx),
    Val_g
      (DomCon.val_of_loc
         (DomCon.loc_of_alloc
            step alloc ((o + idx)%Z, sz, st) DomCon.Fields.nil))
      (DomAbs.modify_array
         abs_v (ArrayBlk.plus_offset (DomAbs.array_of_val abs_v) abs_idx)).
Proof.
i. unfold ArrayBlk.plus_offset.
destruct (Itv.eq_dec abs_idx Itv.bot).
- inversion Hidx; subst. inversion e.
- inversion Habs; subst.
  + apply Val_g_loc. by apply Hl.
  + apply Val_g_ab.
    inversion Hl; subst.
    eapply ArrayBlk_g_intro
    ; [ apply Itv.cor_plus; [by apply Ho|by apply Hidx]
      | by apply Hsz
      | by apply Hst |].
    rewrite ArrayBlk.map_1 with (v:=(o', sz', st')).
    * s. destruct (Itv.eq_dec Itv.bot o')
         ; [inversion Ho; subst; inversion e|reflexivity].
    * s. destruct (Itv.eq_dec Itv.bot Itv.bot); by auto.
    * by auto.
Qed.

Lemma cor_eval :
  forall step cn e cid callee m d abs_m
         (Hm : Mem_g (cid, callee, m, d) abs_m)
         v (Heval : SemCon.Eval_exp step cn cid m e v),
    Val_g v (eval Strong cn e abs_m)

with cor_eval_lv :
  forall step cn lv cid callee m d abs_m
    (Hm : Mem_g (cid, callee, m, d) abs_m)
    l (Heval : SemCon.Eval_lv step cn cid m lv l),
    PowLoc.mem (Loc_g l)
               (eval_lv Strong cn lv abs_m)
    = true

with cor_resolve_offset :
  forall cn step cid callee m d o l l' abs_m
         (Hm : Mem_g (cid, callee, m, d) abs_m)
         (Hres : SemCon.Resolve_offset step cn cid m l o l')
         v (Hl : Val_g (DomCon.val_of_loc l) v),
    PowLoc.mem (Loc_g l')
               (resolve_offset Strong cn v o abs_m)
    = true.
Proof.
induction 2.
{ s. apply cor_eval_const. by apply Hc. }
{ s. eapply cor_mem_lookup; [|by apply Hm0|by apply Hm].
eapply cor_eval_lv; [by apply Hm|by apply Hl].
}
{ s. constructor. by apply Itv.cor_of_int. }
{ s. constructor. by apply Itv.cor_of_int. }
{ s. constructor. by apply Itv.cor_of_int. }
{ s. constructor. by apply Itv.cor_of_int. }
{ s. constructor. by apply Itv.cor_itv_top. }
{ s. eapply cor_eval_uop; [by apply Hu|by apply IHHeval]. }
{ s. eapply cor_eval_bop; [by apply Hb|by apply IHHeval1|by apply IHHeval2]. }
{ s. unfold MId.bind.
match goal with [|- context[if ?c then _ else _]] => destruct c end
; [apply False_ind; eapply itv_non_bot; [by apply IHHeval1|by apply e]|].
match goal with [|- context[if ?c then _ else _]] => destruct c end
; [ apply False_ind; eapply itv_non_zero
    ; [by apply Ht|by apply IHHeval1|by apply e] |].
match goal with [|- context[if ?c then _ else _]] => destruct c end
; [ by apply IHHeval2 |].
eapply val_g_monotone; [by apply IHHeval2|by apply Val.join_left].
}
{ s. unfold MId.bind.
match goal with [|- context[if ?c then _ else _]] => destruct c end
; [apply False_ind; eapply itv_non_bot; [by apply IHHeval1|by apply e]|].
match goal with [|- context[if ?c then _ else _]] => destruct c end
; [by apply IHHeval2|].
match goal with [|- context[if ?c then _ else _]] => destruct c end
; [elim f1; apply eval_zero; by apply IHHeval1|].
eapply val_g_monotone; [by apply IHHeval2|by apply Val.join_right].
}
{ s. unfold MId.bind, MId.ret.
  rewrite Hl in IHHeval. inversion_clear IHHeval.
- apply Val_g_loc. rewrite Hl'. simpl in *. by apply Hl0.
- rewrite Hl'. apply Val_g_ab.
  eapply cor_cast; [by apply Ho'|by apply Hsz'|by apply Hl0].
}
{ s. constructor. eapply cor_eval_lv; [by apply Hm|by apply Hl]. }
{ s. constructor. eapply cor_eval_lv; [by apply Hm|by apply Hl]. }

induction 2.
{ s. eapply cor_resolve_offset; [by apply Hm|by apply Ho|].
constructor. apply PowLoc.singleton_1. by apply Loc.eq_refl. }
{ s. eapply cor_resolve_offset; [by apply Hm|by apply Ho|].
constructor. apply PowLoc.singleton_1. by apply Loc.eq_refl. }
{ s. eapply cor_resolve_offset; [by apply Hm|by apply Ho|].
eapply cor_eval; [by apply Hm|by apply Hv]. }

induction 2; i.
{ s. apply cor_deref_of_val. by apply Hl. }
{ s. eapply IHHres. constructor. eapply cor_append_field. by apply Hl. }
{ s. eapply IHHres.
rewrite Hl'. apply cor_plus_offset_val.
- eapply cor_mem_lookup.
  + apply cor_deref_of_val; by apply Hl0.
  + rewrite <- Hl; by apply Hm0.
  + by apply Hm.
- assert (Val_g (DomCon.val_of_z idx) (SemEval.eval Strong cn e abs_m)) as Hval_g
  ; [eapply cor_eval; [by apply Hm|by apply Hv]|].
  inversion Hval_g; subst. by apply Hz.
}
Qed.

Lemma cor_eval_alloc' :
  forall step cn sz
         a (Ha : a = DomCon.Allocsite.Inl cn)
         al (Hal : al = DomCon.loc_of_alloc step a (0%Z, sz, 1%Z) DomCon.Fields.nil)
         v (Hv : Val_g (DomCon.val_of_z sz) v),
    Val_g (DomCon.val_of_loc al) (eval_alloc' cn v).
Proof.
i. rewrite Hal, Ha.
eapply val_g_monotone; [|by apply Val.join_left].
unfold DomCon.val_of_loc.
apply Val_g_loc. s.
unfold loc_of_allocsite, allocsite_of_node.
apply PowLoc.singleton_1; by apply Loc.eq_refl.
Qed.

Lemma cor_eval_string :
  forall g cn s step sz cid callee d m m' abs_m
     base o (Hbase : base = DomCon.loc_of_alloc step (DomCon.Allocsite.Inl cn) (o, sz, 1%Z) DomCon.Fields.nil)
     (Hinit : SemCon.Initial_s g step (DomCon.Allocsite.Inl cn) base s m m')
     (Hmem_g : Mem_g (cid, callee, m, d) abs_m),
    Mem_g (cid, callee, m', d)
          (mem_wupdate Strong
                      (PowLoc.singleton
                         (loc_of_allocsite (allocsite_of_node cn)))
                      (SemEval.eval_string s) abs_m).
Proof.
induction s.
- i; inversion_clear Hinit; subst.
  eapply cor_wupdate; [| |by apply Hmem_g|reflexivity|reflexivity].
  + apply DomBasic.PowLoc.singleton_1; by apply Loc.eq_refl.
  + constructor; constructor; [constructor; omega|by constructor].
- i; inversion Hinit; subst. inversion Hl; subst.
  eapply mem_g_mor; [reflexivity|by apply mem_wupdate_double|].
  eapply IHs; [reflexivity|by apply Htl|].
  eapply cor_wupdate; [| |by apply Hmem_g|reflexivity|reflexivity].
  + apply DomBasic.PowLoc.singleton_1; by apply Loc.eq_refl.
  + constructor; constructor; [constructor; omega|by constructor].
Qed.

Lemma cor_eval_string_loc :
  forall step cn sz s
         a (Ha : a = DomCon.Allocsite.Inl cn)
         base (Hbase : base = DomCon.loc_of_alloc step a (0%Z, sz, 1%Z) DomCon.Fields.nil),
    Val_g (DomCon.val_of_loc base)
          (SemEval.eval_string_loc
             s (allocsite_of_node cn)
             (PowLoc.singleton (loc_of_allocsite (allocsite_of_node cn)))).
Proof.
i. unfold DomCon.val_of_loc, SemEval.eval_string_loc, DomAbs.val_of_pow_loc, DomAbs.val_of_array.
eapply val_g_monotone; [|by apply Val.join_left].
apply Val_g_loc.
rewrite Hbase, Ha. unfold allocsite_of_node, loc_of_allocsite. s.
apply PowLoc.singleton_1. by apply Loc.eq_refl.
Qed.

Lemma cor_ret_some :
  forall callee callee' cid cid' m m' retl d abs_m abs_m'
     (Hmem_g : Mem_g (cid, callee, m, (callee', Some retl, cid') :: d) abs_m)
         v v' (Hv : Val_g v v')
         (Habs_m' : abs_m' = mem_wupdate Strong
                                     (SemEval.deref_of_val
                                        (mem_lookup
                                           (PowLoc.singleton
                                              (loc_of_proc callee'))
                                           abs_m))
                                     v' abs_m)
         (Hm' : DomCon.M.add retl v m = m'),
    Mem_g (cid', callee, m', d) abs_m'.
Proof.
i. rewrite Habs_m', <- Hm'.
eapply cor_wupdate
; [|by apply Hv|eapply weaken_mem_g; by apply Hmem_g|reflexivity|reflexivity].
apply cor_deref_of_val.
destruct Hmem_g as [Hm Hs]. unfold Stack_g in Hs.
assert (Hs' : Val_g (DomCon.val_of_loc retl) (Mem.find (SProc_g callee') abs_m))
; [eapply Hs; s; left; reflexivity|].
eapply val_g_monotone; [by apply Hs'|].
apply mem_find_mem_lookup. apply PowLoc.singleton_1. by apply Loc.eq_refl.
Qed.

Lemma cor_modify_itv :
  forall v z abs_v itv_v (Hv : v = DomCon.val_of_z z) (Hz : Itv_g z itv_v),
    Val_g v (DomAbs.modify_itv abs_v itv_v).
Proof. i; unfold DomAbs.modify_itv; subst; by apply Val_g_z. Qed.

Lemma Itv_g_mor :
  forall z i1 i2 (Hz : Itv_g z i1) (Hi : Itv.eq i1 i2), Itv_g z i2.
Proof.
inversion 1; subst; inversion 1; subst; constructor.
- apply Itv.le'_trans with lb.
Abort.

Lemma cor_gen_itv :
  forall z lb ub (Hlb : Itv.le' lb (Itv.Int z)) (Hub : Itv.le' (Itv.Int z) ub)
     (lb_c : Itv.eq' lb Itv.PInf -> False) (ub_c : Itv.eq' ub Itv.MInf -> False),
    Itv_g z (Itv.gen_itv lb ub).
Proof.
i. unfold Itv.gen_itv.
destruct (Itv.le'_dec lb ub)
; [|elim f; by apply Itv.le'_trans with (Itv.Int z)].
destruct lb; [|elim lb_c; by apply Itv.eq'_refl|].
- destruct ub; [| |by inversion l]; by constructor.
- destruct ub; [| |elim ub_c; by apply Itv.eq'_refl]; by constructor.
Qed.

Lemma cor_minus'_one :
  forall z1 z2 ub (Hz : (z1 < z2)%Z) (Hub : Itv.le' (Itv.Int z2) ub),
    Itv.le' (Itv.Int z1) (Itv.minus'_one ub).
Proof.
inversion 2; subst; simpl Itv.minus'_one.
- by constructor.
- constructor; omega.
Qed.

Lemma cor_plus'_one :
  forall z1 z2 lb (Hz : (z1 < z2)%Z) (Hub : Itv.le' lb (Itv.Int z1)),
    Itv.le' (Itv.plus'_one lb) (Itv.Int z2).
Proof.
inversion 2; subst; simpl Itv.plus'_one.
- by constructor.
- constructor; omega.
Qed.

Lemma Itv_eq_min :
  forall a b c (Hle : Itv.eq' (Itv.min' a b) c), Itv.eq' a c \/ Itv.eq' b c.
Proof. i. unfold Itv.min' in Hle. destruct (Itv.le'_dec a b); by auto. Qed.

Lemma Itv_eq_max :
  forall a b c (Hle : Itv.eq' (Itv.max' a b) c), Itv.eq' a c \/ Itv.eq' b c.
Proof. i. unfold Itv.max' in Hle. destruct (Itv.le'_dec a b); by auto. Qed.

Lemma Itv_eq_min_minf :
  forall a (Ha : Itv.eq' (Itv.minus'_one a) Itv.MInf), Itv.eq' a Itv.MInf.
Proof.
destruct a; i; [by inversion Ha|by inversion Ha|by apply Itv.eq'_refl].
Qed.

Lemma Itv_eq_max_pinf :
  forall a (Ha : Itv.eq' (Itv.plus'_one a) Itv.PInf), Itv.eq' a Itv.PInf.
Proof.
destruct a; i; [by inversion Ha|by apply Itv.eq'_refl|by inversion Ha].
Qed.

Lemma Itv_g_meet :
  forall z x y (Hx : Itv_g z x) (Hy : Itv_g z y), Itv_g z (Itv.meet x y).
Proof.
inversion 1; inversion 1; subst. unfold Itv.meet.
dest_if_dec. dest_if_dec.
apply cor_gen_itv.
- by apply Itv.max'3.
- by apply Itv.min'3.
- intro Heq; apply Itv_eq_max in Heq; destruct Heq
  ; [by elim lb_c|by elim lb_c0].
- intro Heq; apply Itv_eq_min in Heq; destruct Heq
  ; [by elim ub_c|by elim ub_c0].
Qed.

Lemma cor_itv_prune :
  forall b z z0 i v2 abs_v2
    (Hprune : z <> 0%Z) (Hz : Itv_g z0 i)
    (Hb : SemCon.Eval_bop b (inl (inl z0)) v2 (DomCon.val_of_z z))
    (Habs_v2 : Val_g v2 abs_v2),
  Itv_g z0 (SemPrune.itv_prune b i (DomAbs.itv_of_val abs_v2)).
Proof.
i; inversion Hb; subst
; try (unfold SemPrune.itv_prune
     ; inversion Hz; subst; inversion Habs_v2; subst; inversion Hz0; subst
     ; s; by auto)
; try (unfold SemPrune.itv_prune
       ; inversion Hz; subst; inversion Habs_v2; subst; inversion Hz1; subst
       ; s; by auto)
; unfold SemPrune.itv_prune
; inversion Hz; subst; clear Hz
; inversion Habs_v2; subst; clear Habs_v2
; inversion Hz; subst; clear Hz; s.
- apply cor_gen_itv.
  + by auto.
  + apply Itv.min'3.
    * by auto.
    * eapply cor_minus'_one; [by apply Hlt|by auto].
  + by auto.
  + intro Hminf; apply Itv_eq_min in Hminf; elim Hminf
    ; [by auto|intro Hminf'; by apply Itv_eq_min_minf in Hminf'].
- apply cor_gen_itv.
  + apply Itv.max'3.
    * by auto.
    * eapply cor_plus'_one with z2; [omega|by auto].
  + by auto.
  + intro Hpinf; apply Itv_eq_max in Hpinf; elim Hpinf
    ; [by auto|intro Hpinf'; by apply Itv_eq_max_pinf in Hpinf'].
  + by auto.
- apply cor_gen_itv.
  + by auto.
  + apply Itv.min'3.
    * by auto.
    * apply Itv.le'_trans with (Itv.Int z2); [by constructor|by auto].
  + by auto.
  + intro Hminf; apply Itv_eq_min in Hminf; elim Hminf; by auto.
- apply cor_gen_itv.
  + apply Itv.max'3.
    * by auto.
    * apply Itv.le'_trans with (Itv.Int z2); [by auto|constructor; omega].
  + by auto.
  + intro Hpinf; apply Itv_eq_max in Hpinf; elim Hpinf; by auto.
  + by auto.
- unfold DomAbs.itv_of_val. apply Itv_g_meet.
  + by auto.
  + by constructor.
Qed.

Lemma cor_prune :
  forall g step cn abs_m abs_m' cid m d
     (Hmem_g : Mem_g (cid, None, m, d) abs_m)
     e z (Hv : SemCon.Eval_exp step cn cid m e (DomCon.val_of_z z))
     (Hprune : z <> 0%Z)
     (HAbs : abs_m' = SemPrune.prune g Strong cn e abs_m)
     (Hwf : SemCon.wf_non_rec_mem g m),
    Mem_g (cid, None, m, d) abs_m'.
Proof.
unfold SemPrune.prune; i.
destruct e; try (subst; by apply Hmem_g).
destruct e1; try (subst; by apply Hmem_g).
destruct lv; try (subst; by apply Hmem_g).
destruct lh; try (subst; by apply Hmem_g).
destruct o; try (subst; by apply Hmem_g).
subst. unfold MId.bind.
inversion_clear Hv. inversion_clear Hv1.
eapply cor_update' with (l:=l) (v:=v1); [| | |reflexivity| |]
; [ inversion Hl; subst; inversion Ho; subst; by apply Loc.eq_refl
  | | by auto
  | symmetry; by apply DomCon.M.P.F.find_mapsto_iff
  | by auto ].
remember (SemPrune.SemMem.mem_lookup
          (DomBasic.PowLoc.singleton
             (SemPrune.SemEval.eval_var cn x is_global)) abs_m) as abs_v1.
assert (Val_g v1 abs_v1) as Habs_v1.
{ rewrite Heqabs_v1; eapply cor_mem_lookup; [|by apply Hm|by apply Hmem_g]
  ; inversion Hl; subst; inversion Ho; subst; s
  ; by apply DomBasic.PowLoc.singleton_1, Loc.eq_refl. }
remember (SemPrune.SemEval.eval Strong cn e2 abs_m) as abs_v2.
assert (Val_g v2 abs_v2) as Habs_v2.
{ rewrite Heqabs_v2; eapply cor_eval; [by apply Hmem_g|by apply Hv2]. }
inversion Habs_v1; try (by constructor).
eapply cor_modify_itv; [reflexivity|].
eapply cor_itv_prune; [by apply Hprune|by apply Hz|subst; by apply Hb|by auto].
Qed.

Lemma cor_update_rets :
  forall cn cid m d step callee callees ret_opt l_opt abs_m abs_m'
         (Hcallee : PowProc.mem callee callees = true)
         (Hret : SemCon.Eval_lv_opt step cn cid m ret_opt l_opt)
         (Habs : Mem_g (step, Some callee, m, d) abs_m)
         (Hupdate :
            update_rets Strong cn callees ret_opt abs_m
            = abs_m'),
    Mem_g (step, Some callee, m, (callee, l_opt, cid) :: d) abs_m'.
Proof. {
i. subst. unfold update_rets, MId.bind, MId.ret. split.
- apply mem_wupdate_diff; [by apply Habs|].
  i. apply SMProcLoc.map_diff.
  unfold Loc_g, DomBasic.loc_of_proc; destruct l; inversion 1.
- unfold RunOnly.mem_wupdate, mem_wupdate, MId.bind, MId.ret.
  unfold weak_add, DomMem.IdMem.mem_weak_add; s.
  apply cor_update2 with
  (m := abs_m)
  (l' := match ret_opt with
         | Some ret_lv =>
           SemPrune.SemEval.eval_lv Strong cn ret_lv abs_m
         | None => DomBasic.PowLoc.bot
         end).
  + by apply Habs.
  + destruct l_opt; inversion Hret; subst; [constructor|by constructor].
    apply cor_eval_lv with
    (step:=step) (cid:=cid) (m:=m) (d:=d) (callee:=Some callee)
    ; [|by apply Hl].
    split; by apply Habs.
  + apply PowLoc.fold_3; [|by apply Mem.le_refl, Mem.eq_refl].
    i. eapply Mem.le_trans; [by apply Hx|].
    intro. destruct (Loc.eq_dec k e).
    * eapply Val.le_trans; [|by apply Val.le_refl, Mem.weak_add_prop].
      eapply Val.le_trans; [|by apply Val.join_right].
      apply Val.le_refl, Mem.find_mor; [by auto|by apply Mem.eq_refl].
    * rewrite Mem.weak_add_diff; [by apply Val.le_refl, Val.eq_refl|by auto].
  + destruct ret_opt; [|by apply Val.bot_prop].
    generalize
      (SemPrune.SemEval.eval_lv Strong cn l abs_m) as v
    ; i.
    apply PowLoc.fold_1 with (e:=loc_of_proc callee).
    * apply SMProcLoc.map_1; [by apply DomBasic.loc_of_proc_mor|by auto].
    * i.
      eapply Val.le_trans
      ; [ by apply Val.join_left
        | by apply Val.le_refl, Mem.weak_add_prop, Loc.eq_refl ].
    * i; s. destruct (Loc.eq_dec (loc_of_proc callee) e').
      { eapply Val.le_trans
        ; [by apply Val.join_left|by apply Val.le_refl, Mem.weak_add_prop]. }
      { rewrite Mem.weak_add_diff; by auto. }
    * i. eapply Val.le_trans; [by apply He0|].
      apply Mem.find_mor'; [by apply Loc.eq_refl|].
      apply Mem.weak_add_mor'
      ; [ by auto
        | by apply Val.le_refl, Val.eq_refl
        | by apply Mem.le_refl, Mem.eq_refl ].
} Qed.


Inductive Val_g_list : list DomCon.val_t -> list Val.t -> Prop :=
| Val_g_list_nil : Val_g_list nil nil
| Val_g_list_cons :
    forall v v' vs vs' (Hv : Val_g v v') (Hvs : Val_g_list vs vs'),
      Val_g_list (cons v vs) (cons v' vs').

Lemma cor_eval_list :
  forall step cn cid callee m d m'
     (Hm : Mem_g (cid, callee, m, d) m')
     es vs (Hvs : SemCon.Eval_list step cn cid m es vs)
     vs' (Hvs' : SemEval.eval_list Strong cn es m' = vs'),
    Val_g_list vs vs'.
Proof.
induction 2; i.
- simpl in Hvs'. subst. by constructor.
- simpl in Hvs'. subst. constructor.
  + eapply cor_eval; [by apply Hm|by apply Hv].
  + by apply IHHvs.
Qed.

Lemma bind_arg_monotone :
  forall f x v, Proper (Mem.le ==> Mem.le) (bind_arg Strong f x v).
Proof. unfold bind_arg. i. by apply mem_wupdate_monotone. Qed.

Lemma cor_bind_arg :
  forall step opt_callee d  callee x v v' m m' abs_m abs_m'
     (Hm_g : Mem_g (step, opt_callee, m, d) abs_m)
     (Hv_g : Val_g v v')
     (Hm :
        DomCon.M.add (DomCon.loc_of_lvar step callee x DomCon.Fields.nil) v m
        = m')
     (Habs_m : bind_arg Strong callee x v' abs_m = abs_m'),
    Mem_g (step, opt_callee, m', d) abs_m'.
Proof.
i; subst. unfold bind_arg.
eapply cor_wupdate; [|by apply Hv_g|by apply Hm_g|reflexivity|reflexivity].
by apply PowLoc.singleton_1.
Qed.

Lemma list_fold2_m_monotone A B :
  forall (f: A -> B -> Mem.t -> Mem.t) l vs
     (Hf : forall a b, Proper (Mem.le ==> Mem.le) (f a b)),
    Proper (Mem.le ==> Mem.le) (list_fold2_m f l vs).
Proof.
induction l.
- intros vs m1 m2 Hm. s. destruct vs; by auto.
- intros vs Hf m1 m2 Hm. s. destruct vs; [by auto|].
  apply IHl; [by auto|by apply Hf].
Qed.

Lemma list_fold2_m_ext A B :
  forall (f : A -> B -> Mem.t -> Mem.t) l m m' vs
     (Hm : Mem.le m m') (Hf : forall a b m, Mem.le m (f a b m)),
    Mem.le m (list_fold2_m f l vs m').
Proof.
induction l.
- i; s. destruct vs; by auto.
- i; s. destruct vs; [by auto|].
  unfold MId.bind. apply IHl; [|by auto].
  eapply Mem.le_trans; [by apply Hm|by apply Hf].
Qed.

Lemma bind_args_monotone :
  forall g vs f, Proper (Mem.le ==> Mem.le) (bind_args Strong g vs f).
Proof.
i. intros m1 m2 Hm. unfold bind_args.
destruct (InterCfg.get_args (Global.G.icfg g) f); [|by auto].
apply list_fold2_m_monotone; [by apply bind_arg_monotone|by auto].
Qed.

Lemma bind_args_ext :
  forall g vs e m, Mem.le m (bind_args Strong g vs e m).
Proof.
unfold bind_args. i. destruct (InterCfg.get_args (Global.G.icfg g) e).
- apply list_fold2_m_ext; [by apply Mem.le_refl, Mem.eq_refl|].
  unfold bind_arg. i. by apply mem_wupdate_ext.
- by apply Mem.le_refl, Mem.eq_refl.
Qed.

Lemma cor_bind_args :
  forall g step opt_callee callee callees callee_args vs vs' m m' d
     abs_m abs_m'
     (Hmem_g : Mem_g (step, opt_callee, m, d) abs_m)
     (Hargs_p : Some callee_args = InterCfg.get_args (Global.G.icfg g) callee)
     (Hbind : SemCon.Bind_list step callee callee_args vs m m')
     (Hval_g : Val_g_list vs vs')
     (Hcallee_g : PowProc.mem callee callees = true)
     (Habs_m' : abs_m' = BJProcMem.weak_big_join
                           (bind_args Strong g vs')
                           callees abs_m),
    Mem_g (step, opt_callee, m', d) abs_m'.
Proof.
i; subst.
eapply mem_g_monotone
; [|apply BJProcMem.weak_big_join_1; [by apply Hcallee_g| |]].
- unfold bind_args. rewrite <- Hargs_p.
  generalize vs m m' Hbind vs' Hval_g abs_m Hmem_g Hcallee_g.
  clear vs vs' m m' abs_m Hmem_g Hargs_p Hbind Hval_g Hcallee_g.
  induction 1; i.
  + inversion Hval_g; subst. simpl list_fold2_m. by apply Hmem_g.
  + inversion Hval_g; subst. simpl list_fold2_m. unfold MId.bind. apply IHHbind.
    * by inversion Hval_g.
    * eapply cor_bind_arg
      ; [by apply Hmem_g|by apply Hv|reflexivity|reflexivity].
    * by auto.
- intros f1 f2 Hf. subst. by apply bind_args_monotone.
- unfold MId.le, MId.ret. i. by apply bind_args_ext.
Qed.

Lemma correct_run :
  forall g step cn cmd con_s con_s' abs_m abs_m'
    (Hmem_g : Mem_g con_s abs_m)
    (HCon : SemCon.Run g step cn cmd con_s con_s')
    (HAbs : abs_m' = run_only Strong g cn cmd abs_m),
    Mem_g con_s' abs_m'.
Proof. {
destruct 2.
{ simpl run_only; i; unfold MId.bind in HAbs; subst abs_m'; destruct lv, lh, o
  ; try (eapply cor_update with (l:=l) (g:=g)
         ; [ by apply Loc.eq_refl
           | eapply cor_eval; [by apply Hmem_g|by apply Hv]
           | by apply Hmem_g
           | destruct is_global; inversion Hl; subst; inversion Ho; subst
             ; reflexivity
           | by auto
           | by auto ])
  ; try (eapply cor_wupdate with (l:=l)
         ; [ eapply cor_eval_lv; [by apply Hmem_g|by apply Hl]
           | eapply cor_eval; [by apply Hmem_g|by apply Hv]
           | by apply Hmem_g
           | try (destruct is_global; inversion Hl; subst; inversion Ho; subst)
             ; reflexivity
           | by auto ]).
}
{ simpl run_only. i.
eapply cor_wupdate; [| |by apply Hmem_g|by apply HAbs|symmetry; by apply Hm'].
- eapply cor_eval_lv; [by apply Hmem_g|by apply Hl].
- eapply cor_eval_alloc'; [by apply Ha|by apply Hal|].
  eapply cor_eval; [by apply Hmem_g|by apply Hsz].
}
{ simpl run_only. i.
eapply cor_wupdate; [| | |by apply HAbs|symmetry; by apply Hm''].
- eapply cor_eval_lv; [by apply Hmem_g|by apply Hl].
- eapply cor_eval_string_loc; [by apply Ha|by apply Hbase].
- rewrite Ha in *; eapply cor_eval_string
  ; [by apply Hbase|by apply Hinit|by apply Hmem_g].
}
{ simpl run_only. i.
eapply cor_wupdate
; [| |by apply Hmem_g|by apply HAbs|symmetry; by apply Hm'].
- eapply cor_eval_lv; [by apply Hmem_g|by apply Hl].
- unfold DomCon.val_of_proc, DomAbs.val_of_pow_proc.
  apply Val_g_proc. by apply PowProc.singleton_1.
}
{ simpl run_only. i.
  eapply cor_prune
  ; [by apply Hmem_g|by apply Hv|by apply Hprune|by apply HAbs|by apply Hwf].
}
{ unfold run_only, run, MId.bind, MId.ret. i.
remember (Global.G.is_undef_e f g) as ud; destruct ud; [discriminate|].
rewrite HAbs. clear HAbs Hf_def Hequd.
eapply cor_bind_args
with (callees := powProc_of_val (eval Strong cn f abs_m))
; [|by apply Hargs_p|by apply Hbind| | |reflexivity].
- eapply cor_update_rets;
  [|by apply Hret|by apply Hmem_g|reflexivity].
  exploit cor_eval; [by apply Hmem_g|by apply Hf|].
  i. inversion x0; subst.
  assert (RunOnly.eval = eval) as eval'; [reflexivity|by rewrite eval', <- H].
- eapply cor_eval_list; [by apply Hmem_g|by apply Hargs|reflexivity].
- exploit cor_eval; [by apply Hmem_g|by apply Hf|].
  i. inversion x0; subst. by auto.
}
{ simpl run_only. i.
eapply cor_ret_some with (cid:=cid)
; [|eapply cor_eval; [by apply Hmem_g|by apply Hv]|by apply HAbs|by apply Hm'].
eapply cor_remove_local_variables; [by apply Hmem_g|reflexivity].
}
{ simpl run_only. i. rewrite HAbs.
eapply cor_remove_local_variables; [|by apply Hm'].
eapply weaken_mem_g. by apply Hmem_g.
}
{ simpl run_only. i. by rewrite HAbs. }
{ simpl run_only. i. by rewrite HAbs. }
} Qed.
