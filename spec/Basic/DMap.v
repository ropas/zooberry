(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** Lattice constructor: map.  *)

Set Implicit Arguments.

Require Import ZArith.
Require Import Morphisms Setoid.
Require Import hpattern vgtac.
Require Import TStr VocabA DLat DFMapAVL DPow.

Axiom map_narrow_msg : string_t.

Extract Constant map_narrow_msg => """narrow small big""".

Module Map (A : KEY) (B : LAT) <: LAT.

Module M := FMapAVL'.Make A.

Definition t := M.t B.t.

(** * Lattice operations *)

Definition find (k : A.t) (m : t) : B.t :=
  match M.find k m with
    | Some v => v
    | None => B.bot
  end.

Definition le_than (y : t) (k : A.t) (v :B.t) : bool :=
  if B.le_dec v (find k y) then true else false.

Definition le (x y : t) : Prop := forall k, B.le (find k x) (find k y).

Definition eq (x y : t) : Prop := forall k, B.eq (find k x) (find k y).

Lemma le_refl : forall (x y : t) (Heq : eq x y), le x y.
Proof. unfold le, eq. by auto using B.le_refl. Qed.

Lemma le_antisym : forall (x y : t) (le1 : le x y) (le2 : le y x), eq x y.
Proof. unfold le, eq. by auto using B.le_antisym. Qed.

Lemma le_trans : forall (x y z : t) (le1 : le x y) (le2 : le y z), le x z.
Proof. unfold le. by eauto using B.le_trans. Qed.

Lemma eq_refl : forall (x : t), eq x x.
Proof. unfold eq. by auto using B.eq_refl. Qed.

Lemma eq_sym : forall (x y : t) (Heq : eq x y), eq y x.
Proof. unfold eq. by auto using B.eq_sym. Qed.

Lemma eq_trans : forall (x y z : t) (eq1 : eq x y) (eq2 : eq y z), eq x z.
Proof. unfold eq. by eauto using B.eq_trans. Qed.

Lemma find_mor' : Proper (A.eq ==> le ==> B.le) find.
Proof.
intros k1 k2 Hk m1 m2 Hm; unfold eq in Hm.
apply B.le_trans with (find k1 m2); [by apply Hm|].
apply B.le_refl.
unfold find.
rewrite (M.P.F.find_m Hk (M.P.F.Equal_refl m2)); by apply B.eq_refl.
Qed.

Lemma find_mor : Proper (A.eq ==> eq ==> B.eq) find.
Proof.
intros k1 k2 Hk m1 m2 Hm.
apply B.le_antisym.
- apply le_refl in Hm; by apply find_mor'.
- apply eq_sym in Hm; apply le_refl in Hm. apply A.eq_sym in Hk.
  by apply find_mor'.
Qed.

Lemma find_mor2 : Proper (A.eq ==> Logic.eq ==> Logic.eq) find.
Proof.
intros k1 k2 Hk m1 m2 Hm. subst.
unfold find; rewrite M.P.F.find_m_Proper
; [|by apply Hk|by apply M.P.F.Equal_refl].
reflexivity.
Qed.

Lemma le_than_mor :
  Proper (eq ==> A.eq ==> B.eq ==> Logic.eq) le_than.
Proof.
intros m1 m2 Hm k1 k2 Hk v1 v2 Hv; unfold le_than.
destruct (B.le_dec v1 (find k1 m1)); destruct (B.le_dec v2 (find k2 m2)).
- by auto.
- elim f.
  apply B.le_trans with v1; [by auto using B.le_refl, B.eq_sym|].
  eapply B.le_trans; [by apply l|].
  apply B.le_refl; by apply find_mor.
- elim f.
  apply B.le_trans with v2; [by auto using B.le_refl, B.eq_sym|].
  eapply B.le_trans; [by apply l|].
  apply B.le_refl; apply B.eq_sym; by apply find_mor.
- by auto.
Qed.

Definition for_all print cond m := M.for_all (elt := B.t) print cond m.

Lemma for_all_1 :
  forall m cond (Hcond : forall k v (Hmaps : find k m = v), cond k v = true),
    for_all print2 cond m = true.
Proof.
  unfold find, for_all; i; apply M.for_all_1; i.
  apply Hcond; apply M.P.F.find_mapsto_iff in Hmaps; by rewrite Hmaps.
Qed.

Lemma for_all_2 :
  forall m cond
         (Hmor : Proper (A.eq ==> B.eq ==> Logic.eq) cond)
         (Hbot : forall k, cond k B.bot = true)
         (Hforall : for_all print2 cond m = true),
  forall k v (Hmaps : find k m = v), cond k v.
Proof.
  unfold find, for_all; i.
  remember (M.find (elt:=B.t) k m) as o; destruct o; subst.
  + symmetry in Heqo; apply M.P.F.find_mapsto_iff in Heqo.
    eapply M.for_all_2; [|apply Hforall|apply Heqo]; i.
    apply Hmor; by auto using B.eq_refl.
  + apply Hbot.
Qed.

Lemma simple_le_dec :
  forall x y (Hdec : for_all print2 (le_than y) x = true), le x y.
Proof.
unfold le; intros x y Hb k.
apply for_all_2 with (k := k) (v := find k x) in Hb; try done.
- unfold le_than in Hb; by destruct (B.le_dec (find k x) (find k y)).
- apply le_than_mor; by apply eq_refl.
- unfold le_than; i; destruct (B.le_dec B.bot (find k0 y)); try done.
  elim f; by apply B.bot_prop.
Defined.

Lemma simple_le_dec_prop :
  forall x y (Hdec : for_all print2 (le_than y) x = false),
  exists k, M.In k x /\ ~(B.le (find k x) (find k y)).
Proof.
unfold for_all; i; eapply M.for_all_2' in Hdec
; [|i; apply le_than_mor; auto using eq_refl, B.eq_refl].
destruct Hdec as [k [v [Hmaps Hfalse]]]; exists k.
split; [eapply M.mapsto_in; by eauto|].
unfold le_than in Hfalse.
match goal with [H:(if ?c then _ else _) = _ |- _] => destruct c end
; [discriminate|].
intro; elim f.
eapply B.le_trans; [|by apply FH].
unfold find; apply M.P.F.find_mapsto_iff in Hmaps.
rewrite Hmaps; apply B.le_refl; by apply B.eq_refl.
Qed.

Definition le_dec (x y : t) : {le x y} + {~ le x y}.
refine ((if physical_eq x y as c return
           physical_eq x y = c -> {le x y} + {~ le x y}
         then fun Hc => left _ else
           fun _ =>
             match for_all print2 (le_than y) x as b return
                   for_all print2 (le_than y) x = b
                   -> {le x y} + {~ le x y} with
               | true => fun Hb => left _
               | false => fun Hb => right _
             end Logic.eq_refl) Logic.eq_refl); unfold le; i.
+ apply physical_eq_prop in Hc; subst; apply le_refl; by apply eq_refl.
+ by apply simple_le_dec.
+ by destruct (simple_le_dec_prop _ _ Hb) as [k [Hin Hle]].
Qed.

Definition eq_dec (x y : t) : {eq x y} + {~ eq x y}.
refine (match le_dec x y, le_dec y x with
          | left H1, left H2 => left _
          | _, _ => right _
        end).
- auto using le_antisym.
- intro; elim f. auto using le_refl, eq_sym.
- intro; elim f. auto using le_refl.
Qed.

Definition empty : t := M.empty B.t.

Definition bot : t := empty.

Lemma bot_prop : forall (x : t), le bot x.
Proof. destruct x; unfold le; i; by apply B.bot_prop. Qed.

Definition join' (opt_v1 opt_v2 : option B.t) : option B.t :=
  match opt_v1, opt_v2 with
    | None, None => None
    | None, Some v
    | Some v, None => if B.eq_dec v B.bot then None else Some v
    | Some v1, Some v2 =>
      let joined_v := B.join v1 v2 in
      if B.eq_dec joined_v B.bot then None else Some joined_v
  end.

Lemma join'_prop : forall x y v (Hjoin : join' x y = Some v), ~ B.eq v B.bot.
Proof.
unfold join'; i; destruct x, y; try done
; match goal with _ : context [if ?x then _ else _] |- _ => destruct x end
; try done; elim f; by inv Hjoin.
Qed.

Definition join (x y : t) : t := M.map2 join' x y.

Lemma join_left : forall (x y : t), le x (join x y).
Proof.
  unfold join, le, find; i.
  rewrite M.P.F.map2_1bis; [|eauto].
  destruct (M.find (elt:=B.t) k x); [|apply B.bot_prop].
  unfold join'.
  destruct (M.find (elt:=B.t) k y); repeat dest_if_dec
  ; by eauto using B.le_trans, B.le_refl, B.eq_refl, B.join_left.
Qed.

Lemma join_right : forall (x y : t), le y (join x y).
Proof.
  unfold join, le, find; i.
  rewrite M.P.F.map2_1bis; [|eauto].
  destruct (M.find (elt:=B.t) k y); [|apply B.bot_prop].
  unfold join'.
  destruct (M.find (elt:=B.t) k x); repeat dest_if_dec
  ; by eauto using B.le_trans, B.le_refl, B.eq_refl, B.join_right.
Qed.

Lemma map2_join' : forall k x y,
  B.eq (find k (M.map2 join' x y)) (B.join (find k x) (find k y)).
Proof.
i; unfold find.
rewrite M.P.F.map2_1bis; [|done].
destruct (M.find (elt:=B.t) k x)
; destruct (M.find (elt:=B.t) k y); s
; try dest_if_dec
; auto using B.join_lub, B.le_refl, B.eq_refl,
  B.bot_prop, B.le_antisym, B.join_left, B.join_right.
Qed.

Lemma join_lub : forall (x y u : t) (Hx : le x u) (Hy : le y u), le (join x y) u.
Proof.
unfold join, le; i.
eapply B.le_trans; [apply B.le_refl; apply map2_join'|].
by apply B.join_lub.
Qed.

Lemma join_find : forall k x y,
  B.eq (find k (join x y)) (B.join (find k x) (find k y)).
Proof.
unfold join, find; i; rewrite M.P.F.map2_1bis; [|reflexivity].
destruct (M.find (elt:=B.t) k x), (M.find (elt:=B.t) k y)
; unfold join'; try dest_if_dec
; auto using B.eq_sym, B.eq_refl, B.le_refl, B.le_antisym, B.bot_prop,
  B.le_refl, B.join_lub, B.join_left, B.join_right.
Qed.

Definition meet' (opt_v1 opt_v2 : option B.t) : option B.t :=
  match opt_v1, opt_v2 with
    | None, _
    | _, None => None
    | Some v1, Some v2 =>
      let meeted_v := B.meet v1 v2 in
      if B.eq_dec meeted_v B.bot then None else Some meeted_v
  end.

Lemma meet'_1 : forall x y v (Hmeet : meet' x y = Some v), ~ B.eq v B.bot.
Proof.
unfold meet'; i; destruct x, y; try done
; match goal with _ : context [if ?x then _ else _] |- _ => destruct x end
; try done; elim f; by inv Hmeet.
Qed.

Definition meet (x y : t) : t := M.map2 meet' x y.

Lemma meet_left : forall (x y : t), le (meet x y) x.
Proof.
  unfold meet, le, find; i.
  rewrite M.P.F.map2_1bis; [|eauto].
  destruct (M.find (elt:=B.t) k x);
  simpl; destruct (M.find (elt:=B.t) k y);
  try apply B.bot_prop.
  dest_if_dec; auto using B.bot_prop, B.meet_left.
Qed.

Lemma meet_right : forall (x y : t), le (meet x y) y.
Proof.
  unfold meet, le, find; i.
  rewrite M.P.F.map2_1bis; [|eauto].
  destruct (M.find (elt:=B.t) k x);
  simpl; destruct (M.find (elt:=B.t) k y);
  try (apply B.bot_prop).
  dest_if_dec; auto using B.bot_prop, B.meet_right.
Qed.

Lemma map2_meet' : forall k x y,
  B.eq (find k (M.map2 meet' x y)) (B.meet (find k x) (find k y)).
Proof.
i; unfold find.
rewrite M.P.F.map2_1bis; [|done].
destruct (M.find (elt:=B.t) k x)
; destruct (M.find (elt:=B.t) k y); s; try dest_if_dec
; auto using B.meet_glb, B.le_refl, B.eq_refl,
  B.bot_prop, B.le_antisym, B.meet_left, B.meet_right.
Qed.

Lemma meet_glb : forall (x y l : t) (Hx : le l x) (Hy : le l y), le l (meet x y).
Proof.
unfold meet, le; i.
eapply B.le_trans
; [|apply B.le_refl; apply B.eq_sym; apply map2_meet'].
by apply B.meet_glb.
Qed.

Lemma meet_find : forall k x y,
  B.eq (find k (meet x y)) (B.meet (find k x) (find k y)).
Proof.
unfold meet, find; i; rewrite M.P.F.map2_1bis; [|reflexivity].
destruct (M.find (elt:=B.t) k x), (M.find (elt:=B.t) k y)
; unfold meet'; try dest_if_dec
; auto using B.eq_sym, B.eq_refl, B.le_refl, B.le_antisym, B.bot_prop,
  B.le_refl, B.meet_glb, B.meet_left, B.meet_right.
Qed.

Definition widen' (opt_v1 opt_v2 : option B.t) : option B.t :=
  match opt_v1, opt_v2 with
    | None, None => None
    | None, Some v
    | Some v, None => if B.eq_dec v B.bot then None else Some v
    | Some v1, Some v2 =>
      let widened_v := B.widen v1 v2 in
      if B.eq_dec widened_v B.bot then None else Some widened_v
  end.

Definition widen (x y : t) : t := M.map2 widen' x y.

Definition narrow' (opt_v1 opt_v2 : option B.t) : option B.t :=
  match opt_v1, opt_v2 with
    | _, None => None
    | None, Some v =>
      if B.eq_dec v B.bot then None else invalid_arg map_narrow_msg
    | Some v1, Some v2 =>
      let narrowed_v := B.narrow v1 v2 in
      if B.eq_dec narrowed_v B.bot then None else Some narrowed_v
  end.

Definition narrow (x y : t) : t := M.map2 narrow' x y.

Include JoinMeetProp.

(** * Map operations *)

Definition is_empty (x : t) : bool := M.is_empty x.

Lemma find_mapsto : forall k m (Hin : M.In k m), M.MapsTo k (find k m) m.
Proof.
unfold find; i.
apply M.P.F.find_mapsto_iff.
apply M.P.F.in_find_iff in Hin.
destruct (M.find k m); by auto.
Qed.

Lemma empty_prop : forall (k : A.t), B.eq (find k empty) B.bot.
Proof. unfold find, empty; i; rewrite M.P.F.empty_o; apply B.eq_refl. Qed.

Definition add (k : A.t) (v : B.t) (m : t) : t := M.add k v m.

Lemma add_same : forall k1 k2 (Hk : A.eq k1 k2) v m, B.eq (find k1 (add k2 v m)) v.
Proof.
i. unfold find, add.
rewrite (M.P.F.find_o _ Hk).
rewrite M.P.F.add_eq_o; auto using B.eq_refl.
Qed.

Lemma add_diff : forall k1 k2 (Hk : ~ A.eq k1 k2) v m, (find k1 (add k2 v m)) = (find k1 m).
Proof. i; unfold find, add; rewrite (M.P.F.add_neq_o); auto. Qed.

Definition add_mor' : Proper (A.eq ==> B.le ==> le ==> le) add.
Proof.
intros k1 k2 Hk v1 v2 Hv m1 m2 Hm k. destruct (A.eq_dec k k1).
- eapply B.le_trans; [eapply B.le_trans; [|apply Hv]|].
  + apply B.le_refl. by apply add_same.
  + apply B.le_refl. apply B.eq_sym, add_same. by eauto using A.eq_trans.
- apply B.le_trans with (find k m1).
  + apply B.le_refl. rewrite add_diff; [by apply B.eq_refl|by auto].
  + eapply B.le_trans; [by apply Hm|].
    apply B.le_refl; apply B.eq_sym. rewrite add_diff; [by apply B.eq_refl|].
    by eauto using A.eq_trans.
Qed.

Lemma add_mor : Proper (A.eq ==> B.eq ==> eq ==> eq) add.
Proof.
intros ? ? ? ? ? ? ? ? ?. apply le_antisym.
- apply add_mor'; [by auto|by apply B.le_refl|by apply le_refl].
- apply add_mor'
  ; [by auto|by apply B.le_refl, B.eq_sym|by apply le_refl, eq_sym].
Qed.

Definition weak_add (k : A.t) (v : B.t) (m : t) : t :=
  let orig_v := find k m in
  if B.le_dec v orig_v then m else
  M.add k (B.join orig_v v) m.

Lemma weak_add_prop :
  forall k1 k2 (Hk : A.eq k1 k2) v m,
    B.eq (B.join v (find k2 m)) (find k1 (weak_add k2 v m)).
Proof.
i; unfold weak_add; dest_if_dec.
- apply B.eq_trans with (find k2 m).
  + apply B.eq_sym. by apply B.join_le_idem.
  + apply find_mor; by auto using A.eq_sym, eq_refl.
- eapply B.eq_trans; [|apply B.eq_sym; by apply add_same].
  by apply B.join_comm_eq.
Qed.

Lemma weak_add_diff : forall k1 k2 (Hk : ~ A.eq k1 k2) v m, (find k1 (weak_add k2 v m)) = (find k1 m).
Proof.
  i; unfold find, weak_add; repeat dest_if_dec
  ; rewrite M.P.F.add_neq_o; auto.
Qed.

Definition weak_add_mor' : Proper (A.eq ==> B.le ==> le ==> le) weak_add.
Proof.
intros k1 k2 Hk v1 v2 Hv m1 m2 Hm k.
destruct (A.eq_dec k k1).
- apply B.le_trans with (find k1 (weak_add k1 v1 m1))
  ; [apply find_mor'; [by auto|apply le_refl; by apply eq_refl]|].
  apply B.le_trans with (B.join v1 (find k1 m1))
  ; [ apply B.le_refl; apply B.eq_sym; apply weak_add_prop
      ; by apply A.eq_refl |].
  apply B.le_trans with (B.join v2 (find k2 m2))
  ; [apply B.join_le; [by auto|apply find_mor'; by auto]|].
  apply B.le_trans with (find k2 (weak_add k2 v2 m2))
  ; [apply B.le_refl; apply weak_add_prop; by apply A.eq_refl|].
  apply find_mor'
  ; [ apply A.eq_sym; apply A.eq_trans with k1; by auto
    | apply le_refl; by apply eq_refl ].
- apply B.le_trans with (find k m1).
  + apply B.le_refl. rewrite weak_add_diff; [by apply B.eq_refl|by auto].
  + eapply B.le_trans; [by apply Hm|].
    apply B.le_refl; apply B.eq_sym. rewrite weak_add_diff; [by apply B.eq_refl|].
    by eauto using A.eq_trans.
Qed.

Definition weak_add_mor : Proper (A.eq ==> B.eq ==> eq ==> eq) weak_add.
Proof.
intros k1 k2 Hk v1 v2 Hv m1 m2 Hm.
apply le_antisym.
- apply B.le_refl in Hv; apply le_refl in Hm. by apply weak_add_mor'.
- apply A.eq_sym in Hk; apply B.eq_sym in Hv; apply eq_sym in Hm.
  apply B.le_refl in Hv; apply le_refl in Hm.
  by apply weak_add_mor'.
Qed.

Definition fast_weak_add (k : A.t) (v : B.t) (m : t) : t :=
  let orig_v := find k m in
  M.add k (B.join orig_v v) m.

Definition remove (k : A.t) (m : t) : t := M.remove k m.

Lemma remove_same : forall k1 k2 (Hk : A.eq k1 k2) m, (find k1 (remove k2 m)) = B.bot.
Proof. i; unfold find, remove; rewrite M.P.F.remove_eq_o; auto. Qed.

Lemma remove_diff : forall k1 k2 (Hk : ~ A.eq k1 k2) m, (find k1 (remove k2 m)) = (find k1 m).
Proof. i; unfold find, remove; rewrite M.P.F.remove_neq_o; auto. Qed.

(* The input function of map ([f]) should preserve non-bottom
values. *)

Definition map (f : B.t -> B.t) (m : t) : t :=
  M.map (fun k => f k) m.

Lemma map_1 :
  forall f l v m (Hf : f B.bot = B.bot) (Hfind : find l m = v),
    find l (map f m) = f v.
Proof.
unfold find, map; i. rewrite M.P.F.map_o.
remember (M.find (elt:=B.t) l m) as v'; destruct v' as [v'|]; subst; by auto.
Qed.

Definition mapi (f : A.t -> B.t -> B.t) (m : t) : t :=
  M.mapi (fun k v => f k v) m.

Definition fold {T : Type} (f : B.t -> T -> T) (m : t) (acc : T) : T :=
  let f' (_ : A.t) (v : B.t) (acc : T) : T := f v acc in
  M.fold f' m acc.

Definition foldi {T : Type} (f : A.t -> B.t -> T -> T) (m : t) (acc : T) : T :=
  M.fold f m acc.

Lemma not_InA_findA_none :
  forall l k k' v (Hnot_InA : ~ (SetoidList.InA (M.eq_key (elt:=B.t)) (k, v) l))
     (Heq : M.E.eq k' k),
    SetoidList.findA (M.P.F.eqb k') l = None.
Proof.
induction l; [by auto|].
i; s. destruct a as [ak av].
unfold M.P.F.eqb. destruct (M.E.eq_dec k' ak).
- elim Hnot_InA. apply SetoidList.InA_cons_hd.
  unfold M.eq_key, M.Raw.Proofs.PX.eqk; s.
  eapply A.eq_trans; [apply A.eq_sym; by apply Heq|by apply e].
- eapply IHl; [|by apply Heq].
  intro. elim Hnot_InA. apply SetoidList.InA_cons_tl.
  by apply FH.
Qed.

Lemma foldi_3 :
  forall {T : Type} (teq : relation T) (teq_equiv : equivalence _ teq)
     (P : T -> Prop) (P_mor : Proper (teq ==> iff) P)
     (f : A.t -> B.t -> T -> T) (Hf : forall k v x (Hv : B.eq B.bot v), teq (f k v x) x)
     (m : t) (i : T)
     (Hinit : P i)
     (Hind : forall k v (Hkv : B.eq (find k m) v) x (Hx : P x), P (f k v x)),
    P (foldi f m i).
Proof.
unfold foldi, find; i. rewrite M.fold_1.
assert
  ( forall (k : A.t) (v : B.t),
      B.eq
        match SetoidList.findA (M.P.F.eqb k) (M.elements m) with
        | Some v0 => v0
        | None => B.bot
        end v -> forall x : T, P x -> P (f k v x)
  ) as Hind'
; [i; apply Hind; [by rewrite M.P.F.elements_o|by auto]|clear Hind].
assert (Hnodup := M.elements_3w m).
generalize dependent i; induction (M.elements m); [by auto|].
destruct a as [ak av].
s; i; eapply IHl; clear IHl.
- i. destruct (M.E.eq_dec k ak).
  + inversion Hnodup; subst.
    apply not_InA_findA_none with (k':=k) in H3; [rewrite H3 in H|by auto].
    eapply P_mor; [|by apply H0]. by apply Hf.
  + apply Hind'; [|by auto].
    s. unfold M.P.F.eqb.
    destruct (M.E.eq_dec k ak); [congruence|by auto].
- by inversion Hnodup.
- apply Hind'; [|by auto]; s.
  unfold M.P.F.eqb; destruct (M.E.eq_dec ak ak)
  ; [by apply B.eq_refl|elim n; by apply M.E.eq_refl].
Qed.

Lemma foldi_2 :
  forall {T : Type} (teq : relation T) (teq_equiv : equivalence _ teq)
     (P : T -> Prop) (P_mor : Proper (teq ==> iff) P)
     (Q : T -> Prop) (Q_mor : Proper (teq ==> iff) Q)
     (f : A.t -> B.t -> T -> T)
     k v m (Hkv : B.eq (find k m) v) (He : forall x (Hx : P x), Q (f k v x))
     (Hf : forall k v x (Hv : B.eq B.bot v), teq (f k v x) x)
     i (Hinit : P i)
     (HP : forall k v x (Hx : P x), P (f k v x))
     (HQ : forall k v x (Hx : Q x), Q (f k v x))
     (Hf_eq :
        forall k1 k2 (Hk : A.eq k1 k2) v1 v2 (Hv : B.eq v1 v2)
           x (Hf : Q (f k1 v1 x)),
          Q (f k2 v2 x)),
    Q (foldi f m i).
Proof.
unfold foldi, find; i. rewrite M.fold_1.
rewrite M.P.F.elements_o in Hkv.
assert (Hnodup := M.elements_3w m).
generalize dependent i; induction (M.elements m) as [|[ak av]]; s; i.
- erewrite <- Hf; [by apply He|by apply Hkv].
- unfold SetoidList.findA, M.P.F.eqb in Hkv; destruct (M.E.eq_dec k ak).
  + assert (Q (f ak av i)) as Hind
    ; [eapply Hf_eq; [by apply e|apply B.eq_sym; by apply Hkv|by apply He]|].
    clear IHl. generalize dependent (f ak av i); induction l.
    * by auto.
    * i; s. eapply IHl; [|by apply HQ].
      inversion Hnodup; inversion H2; subst.
      apply SetoidList.NoDupA_cons; [|by auto].
      intro. elim H1.
      by apply SetoidList.InA_cons_tl.
  + apply IHl; [by apply Hkv|by inversion Hnodup|by apply HP].
Qed.

Lemma foldi_1 :
  forall {T : Type} (teq : relation T) (teq_equiv : equivalence _ teq)
     (P : T -> Prop) (P_mor : Proper (teq ==> iff) P)
     (f : A.t -> B.t -> T -> T)
     k v m (Hkv : B.eq (find k m) v) (He : forall x, P (f k v x))
     (Hf : forall k v x (Hv : B.eq B.bot v), teq (f k v x) x)
     i (HP : forall k v x (Hx : P x), P (f k v x))
     (Hf_eq :
        forall k1 k2 (Hk : A.eq k1 k2) v1 v2 (Hv : B.eq v1 v2)
           x (Hf : P (f k1 v1 x)),
          P (f k2 v2 x)),
    P (foldi f m i).
Proof.
i. eapply foldi_2 with (P0:=fun (x:T)=>True)
; [ by apply teq_equiv | by auto | by apply P_mor | by apply Hkv
  | i; by apply He | by apply Hf | by auto | by auto | by apply HP
  | by apply Hf_eq ].
Qed.

Inductive assoc_eq : relation (list (A.t * B.t)) :=
| assoc_eq_nil : assoc_eq nil nil
| assoc_eq_bot1 :
    forall m1 m2 (Hm : assoc_eq m1 m2) k v (Hv : B.eq B.bot v),
      assoc_eq m1 (cons (k, v) m2)
| assoc_eq_bot2 :
    forall m1 m2 (Hm : assoc_eq m1 m2) k v (Hv : B.eq B.bot v),
      assoc_eq (cons (k, v) m1) m2
| assoc_eq_cons :
    forall m1 m2 (Hm : assoc_eq m1 m2) k1 k2 (Hk : A.eq k1 k2)
       v1 v2 (Hv : B.eq v1 v2)
       (Hv1 : not (B.eq B.bot v1)) (Hv2 : not (B.eq B.bot v2)),
      assoc_eq (cons (k1, v1) m1) (cons (k2, v2) m2).

Lemma assoc_eq_refl : forall x, assoc_eq x x.
Proof.
induction x; [by apply assoc_eq_nil|].
destruct a as [k v]. destruct (B.eq_dec B.bot v).
- apply assoc_eq_bot1; [|by auto].
  apply assoc_eq_bot2; by auto.
- apply assoc_eq_cons
  ; [by auto|by apply A.eq_refl|by apply B.eq_refl|by auto|by auto].
Qed.

Lemma assoc_eq_sym : forall x y (Heq : assoc_eq x y), assoc_eq y x.
Proof.
induction 1.
- by apply assoc_eq_nil.
- by apply assoc_eq_bot2.
- by apply assoc_eq_bot1.
- apply assoc_eq_cons
  ; [by auto|by apply A.eq_sym|by apply B.eq_sym|by auto|by auto].
Qed.

Lemma assoc_eq_trans :
  forall x y z (Heq1 : assoc_eq x y) (Heq2 : assoc_eq y z), assoc_eq x z.
Proof. {
intros x y z Heq1. revert z. induction Heq1.
- by auto.
- intro z. remember ((k, v) :: m2) as m2'.
  induction 1.
  + by inversion Heqm2'.
  + apply assoc_eq_bot1; [by apply IHHeq2|by auto].
  + inversion Heqm2'; subst. by apply IHHeq1.
  + inversion Heqm2'; by subst.
- i. apply assoc_eq_bot2; [by apply IHHeq1|by auto].
- induction z.
  + inversion 1; subst; tauto.
  + inversion 1; subst.
    * apply assoc_eq_bot1; [by apply IHz|by auto].
    * tauto.
    * apply assoc_eq_cons
      ; [ by apply IHHeq1
        | eapply A.eq_trans; [by apply Hk|by apply Hk0]
        | eapply B.eq_trans; [by apply Hv|by apply Hv0]
        | by auto | by auto ].
} Qed.

Lemma assoc_eq_nil_cond :
  forall l (Hl : forall k : A.t,
           B.eq B.bot
                match SetoidList.findA (M.P.F.eqb k) l with
                | Some v => v
                | None => B.bot
                end)
     (Hnodup : SetoidList.NoDupA (M.eq_key (elt:=B.t)) l),
    assoc_eq nil l.
Proof.
induction l.
- s; i. by apply assoc_eq_nil.
- s; i.
  inversion Hnodup; subst.
  destruct a as [k v]. apply assoc_eq_bot1.
  + apply IHl; [|by auto].
    intro j. specialize (Hl j). unfold M.P.F.eqb in Hl.
    destruct (M.E.eq_dec j k); [|by auto].
    erewrite not_InA_findA_none; [by apply B.eq_refl|by apply H1|by apply e].
  + specialize (Hl k). unfold M.P.F.eqb in Hl.
    destruct (M.E.eq_dec k k); [by auto|elim n; by apply A.eq_refl].
Qed.

Lemma findA_head :
  forall k k' v x (Heq : A.eq k k'),
    SetoidList.findA (B:=B.t) (M.P.F.eqb k) ((k', v) :: x) = Some v.
Proof.
i. unfold SetoidList.findA at 1, M.P.F.eqb at 1.
destruct (A.eq_dec k k'); [reflexivity|tauto].
Qed.

Lemma findA_tail :
  forall k k' v x (Heq : not (A.eq k k')),
    SetoidList.findA (B:=B.t) (M.P.F.eqb k) ((k', v) :: x)
    = SetoidList.findA (B:=B.t) (M.P.F.eqb k) x.
Proof.
i. unfold SetoidList.findA at 1, M.P.F.eqb at 1.
destruct (A.eq_dec k k'); [tauto|reflexivity].
Qed.

Lemma lt_findA_None :
  forall l k1 k2 v (Hlt : A.lt k1 k2)
     (Hsort : Sorted.Sorted (M.lt_key (elt:=B.t)) ((k2, v) :: l)),
    SetoidList.findA (M.P.F.eqb k1) ((k2, v) :: l) = None.
Proof.
induction l; i.
- s. unfold M.P.F.eqb.
  destruct (A.eq_dec k1 k2); [by apply A.lt_not_eq in Hlt|by auto].
- unfold SetoidList.findA.
  unfold M.P.F.eqb at 1.
  destruct (A.eq_dec k1 k2); [by apply A.lt_not_eq in Hlt|].
  destruct a as [ka va]; apply IHl; [|by inversion Hsort].
  inversion Hsort; inversion H2; subst.
  unfold M.lt_key, M.Raw.Proofs.PX.ltk in H4; simpl in H4.
  eapply A.lt_trans; [by apply Hlt|by apply H4].
Qed.

Lemma noDup_findA_None :
  forall k k' (Hk : M.E.eq k k')
     v x (Hnodup : SetoidList.NoDupA (M.eq_key (elt:=B.t)) ((k, v) :: x)),
    SetoidList.findA (M.P.F.eqb k') x = None.
Proof.
i. inversion Hnodup; subst.
eapply not_InA_findA_none; [by apply H1|by apply M.E.eq_sym].
Qed.

Lemma key_eqb_refl : forall k, M.P.F.eqb k k = true.
Proof.
i. unfold M.P.F.eqb.
destruct (M.P.F.eq_dec k k); [by auto|elim n; by apply M.E.eq_refl].
Qed.

Lemma key_eqb_true :
  forall k1 k2 (Heq : M.E.eq k1 k2), M.P.F.eqb k1 k2 = true.
Proof. unfold M.P.F.eqb. i. dest_if_dec. Qed.

Lemma key_eqb_false :
  forall k1 k2 (Hneq : ~ M.E.eq k1 k2), M.P.F.eqb k1 k2 = false.
Proof. unfold M.P.F.eqb. i. dest_if_dec. Qed.

Lemma key_neq_sym : forall k1 k2 (Hneq : ~ A.eq k1 k2), ~ A.eq k2 k1.
Proof. i. elim Hneq. by apply A.eq_sym. Qed.

Lemma eq_assoc_eq :
  forall x y (Heq : eq x y),
    assoc_eq (M.elements (elt:=B.t) x) (M.elements (elt:=B.t) y).
Proof. {
unfold eq, find; i.
assert
  ( forall k,
      B.eq
        match SetoidList.findA (M.P.F.eqb k) (M.elements x) with
        | Some v => v
        | None => B.bot
        end
        match SetoidList.findA (M.P.F.eqb k) (M.elements y) with
        | Some v => v
        | None => B.bot
        end ) as Heq'
; [i; by do 2 rewrite <- M.P.F.elements_o; by apply Heq|clear Heq].
assert (Hnodupx := M.elements_3w x); assert (Hnodupy := M.elements_3w y).
assert (Hsortx := M.elements_3 x); assert (Hsorty := M.elements_3 y).
Local Ltac apply_inv H :=
  apply H; [| by inversion Hnodupx | by inversion Hnodupy
            | by inversion Hsortx | by inversion Hsorty ].
revert Heq' Hnodupx Hnodupy Hsortx Hsorty
; generalize (M.elements (elt:=B.t) x) as x', (M.elements (elt:=B.t) y) as y'.
induction x'; [i; apply assoc_eq_nil_cond; by auto|].
induction y'
; [ i; apply assoc_eq_sym, assoc_eq_nil_cond
    ; [i; apply B.eq_sym; by apply Heq'|by auto] |].
i; destruct a as [k1 v1], a0 as [k2 v2].
destruct (B.eq_dec B.bot v2) as [Hv2|Hv2].
{ apply assoc_eq_bot1; [apply_inv IHy'|by auto].
  s; intros k0. specialize (Heq' k0); s in Heq'.
  destruct (A.eq_dec k0 k2); [|by rewrite (key_eqb_false n) in Heq'].
  rewrite (key_eqb_true e) in Heq'.
  rewrite noDup_findA_None with (k:=k2) (v:=v2) (x:=y')
  ; [|by apply A.eq_sym|by inversion Hnodupy].
  eapply B.eq_trans; [by apply Heq'|by apply B.eq_sym]. }
destruct (B.eq_dec B.bot v1) as [Hv1|Hv1].
{ apply assoc_eq_bot2; [apply_inv IHx'|by auto].
  s; intros k0. specialize (Heq' k0); s in Heq'.
  destruct (A.eq_dec k0 k1); [|by rewrite (key_eqb_false n) in Heq'].
  rewrite (key_eqb_true e) in Heq'.
  rewrite noDup_findA_None with (k:=k1) (v:=v1) (x:=x')
  ; [|by apply A.eq_sym|by inversion Hnodupy].
  eapply B.eq_trans; [by apply Hv1|by apply Heq']. }
{ destruct (A.compare k1 k2).
  - specialize (Heq' k1).
    rewrite findA_head in Heq'; [|by apply A.eq_refl].
    rewrite lt_findA_None in Heq'; [|by auto|by auto].
    elim Hv1; by apply B.eq_sym.
  - apply assoc_eq_cons; [|by auto| |by auto|by auto].
    + apply_inv IHx'.
      s; intros k0. specialize (Heq' k0); s in Heq'.
      destruct (A.eq_dec k0 k1).
      * rewrite noDup_findA_None with (k:=k1) (v:=v1) (x:=x')
        ; [|by apply A.eq_sym|by auto].
        rewrite noDup_findA_None with (k:=k2) (v:=v2) (x:=y')
        ; [|by apply A.eq_sym, A.eq_trans with k1|by auto].
        by apply B.eq_refl.
      * rewrite key_eqb_false in Heq'; [|by auto].
        rewrite key_eqb_false in Heq'; [by auto|].
        i; elim n. apply A.eq_trans with k2; [by auto|by apply A.eq_sym].
    + specialize (Heq' k1); s in Heq'.
      rewrite key_eqb_refl in Heq'.
      rewrite (key_eqb_true (k1:=k1) (k2:=k2)) in Heq'; [by auto|by auto].
  - specialize (Heq' k2).
    rewrite findA_head with (k':=k2) in Heq'; [|by apply A.eq_refl].
    rewrite lt_findA_None in Heq'; [|by auto|by auto].
    elim Hv2; by apply B.eq_sym. }
} Qed.

Lemma foldi2_2 :
  forall {T U : Type} (P : T -> U -> Prop)
     (f1 : A.t -> B.t -> T -> T) (f2 : A.t -> B.t -> U -> U)
     (Hf1 :
        forall k v acc1 acc2 (Hv : B.eq B.bot v) (Hacc : P acc1 acc2),
          P (f1 k v acc1) acc2)
     (Hf2 :
        forall k v acc1 acc2 (Hv : B.eq B.bot v) (Hacc : P acc1 acc2),
          P acc1 (f2 k v acc2))
     (Hf :
        forall k1 k2 v1 v2 acc1 acc2 (Hk : A.eq k1 k2) (Hv : B.eq v1 v2)
           (Hacc : P acc1 acc2),
          P (f1 k1 v1 acc1) (f2 k2 v2 acc2))
     i1 i2 (Hi : P i1 i2) m1 m2 (Heq : eq m1 m2),
    P (foldi f1 m1 i1) (foldi f2 m2 i2).
Proof.
unfold foldi; i. do 2 rewrite M.fold_1.
generalize i1, i2, Hi; clear i1 i2 Hi.
apply eq_assoc_eq in Heq. induction Heq.
- by auto.
- s; i. apply IHHeq. by apply Hf2.
- s; i. apply IHHeq. by apply Hf1.
- s; i. apply IHHeq. by apply Hf.
Qed.

Lemma foldi2_1 :
  forall {T : Type} (P : relation T) (f1 f2 : A.t -> B.t -> T -> T)
     (Hf1 :
        forall k v acc1 acc2 (Hv : B.eq B.bot v) (Hacc : P acc1 acc2),
          P (f1 k v acc1) acc2)
     (Hf2 :
        forall k v acc1 acc2 (Hv : B.eq B.bot v) (Hacc : P acc1 acc2),
          P acc1 (f2 k v acc2))
     (Hf :
        forall k1 k2 v1 v2 acc1 acc2 (Hk : A.eq k1 k2) (Hv : B.eq v1 v2)
           (Hacc : P acc1 acc2),
          P (f1 k1 v1 acc1) (f2 k2 v2 acc2))
     i1 i2 (Hi : P i1 i2) m1 m2 (Heq : eq m1 m2),
    P (foldi f1 m1 i1) (foldi f2 m2 i2).
Proof. i; by apply foldi2_2. Qed.

Lemma foldi2_3 T Q :
  forall (P : T -> Q -> Prop) f1 f2
     (Hf1 :
        forall k v acc1 acc2 (Hv : B.eq B.bot v) (Hacc : P acc1 acc2),
          P (f1 k v acc1) acc2)
     (Hf2 :
        forall k v acc1 acc2 (Hv : B.eq B.bot v) (Hacc : P acc1 acc2),
          P acc1 (f2 k v acc2))
     (Hf : forall k v acc1 acc2 (Hacc : P acc1 acc2), P (f1 k v acc1) (f2 k v acc2))
     m (i1 : T) (i2 : Q) (Hi : P i1 i2),
    P (foldi f1 m i1) (foldi f2 m i2).
Proof.
unfold foldi; i. do 2 rewrite M.fold_1.
generalize i1, i2, Hi; clear i1 i2 Hi.
induction (M.elements (elt:=B.t) m).
- by auto.
- s; i; apply IHl. by apply Hf.
Qed.

Lemma foldi_mor :
  forall {T : Type} (teq : relation T) (teq_equiv : equivalence T teq)
     (f : A.t -> B.t -> T -> T) (Hf : Proper (A.eq ==> B.eq ==> teq ==> teq) f)
     (Hf_bot : forall k v (Hv : B.eq B.bot v) acc, teq (f k v acc) acc),
    Proper (eq ==> teq ==> teq) (foldi f).
Proof.
i. intros m1 m2 Hm acc1 acc2 Hacc.
apply foldi2_1; [| | |by auto|by auto].
- i. eapply (equiv_trans _ _ teq_equiv); [by apply Hf_bot|by apply Hacc0].
- i. eapply (equiv_trans _ _ teq_equiv); [by apply Hacc0|].
  apply (equiv_sym _ _ teq_equiv). by apply Hf_bot.
- i. by apply Hf.
Qed.

Definition filter (f : A.t -> bool) (m : t) : t := M.filter f m.

Lemma filter_1 :
  forall k m cond (Hcond_mor : Proper (A.eq ==> Logic.eq) cond)
         (Hcond : cond k = true),
    B.eq (find k (filter cond m)) (find k m).
Proof.
unfold find, filter; s; i.
rewrite (M.filter_1); [by apply B.eq_refl|by auto|by auto].
Qed.

Lemma filter_2 :
  forall k m cond (Hcond_mor : Proper (A.eq ==> Logic.eq) cond)
         (Hcond : cond k = false),
    B.eq (find k (filter cond m)) B.bot.
Proof.
unfold find, filter; s; i.
rewrite (M.filter_2); [by apply B.eq_refl|by auto|by auto].
Qed.

Lemma filter_mor' :
  forall cond (Hcond_mor : Proper (A.eq ==> Logic.eq) cond),
    Proper (le ==> le) (filter cond).
Proof.
i; intros m1 m2 Hm; i; intro k.
remember (cond k) as b; destruct b.
- eapply B.le_trans; [apply B.le_refl; apply filter_1; by auto|].
  eapply B.le_trans; [by apply Hm|].
  apply B.le_refl; apply B.eq_sym; apply filter_1; by auto.
- eapply B.le_trans; [apply B.le_refl; apply filter_2; by auto|].
  apply B.le_refl; apply B.eq_sym; apply filter_2; by auto.
Qed.

Lemma filter_mor :
  forall cond (Hcond_mor : Proper (A.eq ==> Logic.eq) cond),
    Proper (eq ==> eq) (filter cond).
Proof.
i; intros m1 m2 Hm.
apply le_antisym.
- apply le_refl in Hm; by apply filter_mor'.
- apply eq_sym in Hm; apply le_refl in Hm; by apply filter_mor'.
Qed.

Lemma filter_le :
  forall cond x (Hmor : Proper (A.eq ==> Logic.eq) cond),
    le (filter cond x) x.
Proof.
i. intro k. remember (cond k) as b; destruct b.
- apply B.le_refl; by apply filter_1.
- apply B.le_trans with B.bot; [|by apply B.bot_prop].
  apply B.le_refl; by apply filter_2.
Qed.

Definition elements (m : t) : list (A.t * B.t) := M.elements m.

Definition cardinal (m : t) : Z := Zlength (M.elements m).

Fixpoint unstables (old_m new_m : t) (is_unstb : B.t -> B.t -> bool)
           (candidate : list A.t) : list (A.t * B.t * B.t) :=
  match candidate with
  | nil => nil
  | k :: tl =>
    let old_v := find k old_m in
    let new_v := find k new_m in
    if is_unstb old_v new_v then
      (k, old_v, new_v) :: unstables old_m new_m is_unstb tl
    else unstables old_m new_m is_unstb tl
  end.

Definition meet_big_small (x y : t) : t :=
  let iter1 k v := add k (B.meet (find k x) v) in
  foldi iter1 y y.

Lemma le_false :
  forall x y (Hle : ~(le x y)),
  exists k, M.In k x /\ ~(B.le (find k x) (find k y)).
Proof.
i; apply simple_le_dec_prop.
remember (for_all print2 (le_than y) x) as b; destruct b; [|by auto].
elim Hle. by auto using simple_le_dec.
Qed.

Definition strong_le (x y : t) : bool :=
  M.strong_le (fun x y => if B.le_dec x y then true else false) x y.

Lemma strong_le_1 (x y : t) (Hle : strong_le x y) : le x y.
Proof.
unfold le, strong_le in *; i; eapply M.strong_le_1 in Hle.
- elim Hle; i.
  + destruct H as [v1 [v2 [Hv1 [Hv2 He]]]].
    unfold find; rewrite Hv1; rewrite Hv2.
    destruct (B.le_dec v1 v2); [by done|discriminate].
  + unfold find; rewrite H; by apply B.bot_prop.
- i; destruct (B.le_dec v v); [done|].
  elim f; apply B.le_refl; by apply B.eq_refl.
Qed.

Definition opt_le x y :=
  if strong_le x y then true else
  if le_dec x y then true else
    false.

Lemma opt_le_prop :
  forall (x y : t) (Hstrong_le : opt_le x y = true), le x y.
Proof.
unfold opt_le; i.
remember (strong_le x y) as b; destruct b
; [by apply strong_le_1|by destruct (le_dec x y)].
Qed.

Definition strong_eq (x y : t) : bool := strong_le x y && strong_le y x.

Lemma strong_eq_1 (x y : t) (Heq : strong_eq x y) : eq x y.
Proof.
unfold strong_eq in Heq.
apply Bool.andb_true_iff in Heq. destruct Heq as [Heq1 Heq2].
apply le_antisym; by apply strong_le_1.
Qed.

End Map.
