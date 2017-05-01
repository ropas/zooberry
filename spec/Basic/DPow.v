(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** Lattice constructor: powerset.  *)

Set Implicit Arguments.

Require Import ZArith.
Require Import Morphisms SetoidList.
Require Import hpattern vgtac.
Require Import VocabA DFSetAVL DLat.

Module Type POW (A : KEY).
  Include LAT.
  Definition elt : Type := A.t.
  Parameter empty : t.
  Parameter is_empty : t -> bool.
  Parameter add : elt -> t -> t.
  Parameter add_mor : Proper (A.eq ==> eq ==> eq) add.
  Parameter mem : elt -> t -> bool.
  Parameter mem_mor : Proper (A.eq ==> eq ==> Logic.eq) mem.
  Parameter mem_join_false :
    forall l s1 s2 (Hl : mem l (join s1 s2) = false),
      mem l s1 = false /\ mem l s2 = false.
  Parameter mem_join_false_inv :
    forall l s1 s2 (H1 : mem l s1 = false) (H2 : mem l s2 = false),
      mem l (join s1 s2) = false.
  Parameter mem_add_false :
    forall l l' s (Hl : mem l (add l' s) = false), ~ (A.eq l l').
  Parameter le_mem_false :
    forall l ls ls' (Hsubset : le ls' ls) (Hmem : mem l ls = false),
      mem l ls' = false.
  Parameter le_mem_true :
    forall l ls ls' (Hsubset : le ls' ls) (Hmem : mem l ls' = true),
      mem l ls = true.
  Parameter singleton : elt -> t.
  Parameter singleton_1 :
    forall e1 e2 (Heq : A.eq e1 e2), mem e1 (singleton e2) = true.
  Parameter singleton_2 :
    forall e1 e2 (Hmem : mem e1 (singleton e2) = true), A.eq e1 e2.
  Parameter remove : elt -> t -> t.
  Parameter union : t -> t -> t.
  Parameter union_small_big : t -> t -> t.
  Parameter intersect : t -> t -> t.
  Parameter diff : t -> t -> t.
  Parameter subset : t -> t -> bool.
  Parameter filter : (elt -> bool) -> t -> t.
  Parameter fold : forall a, (elt -> a -> a) -> t -> a -> a.
  Parameter iter : (elt -> unit) -> t -> unit.
  Parameter elements : t -> list elt.
  Parameter cardinal : t -> nat.
  Parameter choose : t -> option elt.
  Parameter choose_only : t -> option elt.
  Parameter choose_only_1 :
    forall s e (Hce : choose_only s = Some e), elements s = cons e nil.
  Parameter choose_only_2 :
    forall l1 l2 l' (Hco : choose_only l' = Some l1) (Hmem : mem l2 l' = true),
      A.eq l1 l2.
  Parameter for_all : (elt -> unit) -> (elt -> bool) -> t -> bool.
  Parameter for_all_1 :
    forall k s print f (Hk: mem k s) (Hf: compat_bool A.eq f)
           (Hfor_all: for_all print f s = true),
      f k = true.
End POW.

Module Pow (A : KEY) <: LAT <: POW A.

Module SS := FSetAVL'.Make A.

Definition elt : Type := A.t.
Definition t : Type := SS.t.

(** * Lattice operations *)

Definition le (x y : t) : Prop := SS.Subset x y.

Definition eq (x y : t) : Prop := SS.eq x y.

Lemma le_refl : forall (x y : t) (Heq : eq x y), le x y.
Proof. unfold le, eq; i; intros e Hx. by apply Heq. Qed.

Lemma le_antisym : forall (x y : t) (le1 : le x y) (le2 : le y x), eq x y.
Proof. unfold le, eq; i; intro e; split; [apply le1|apply le2]. Qed.

Lemma le_trans : forall (x y z : t) (le1 : le x y) (le2 : le y z), le x z.
Proof. unfold le; i; intros e Hx; apply le2; by apply le1. Qed.

Lemma eq_refl : forall (x : t), eq x x.
Proof. by apply SS.eq_refl. Qed.

Lemma eq_sym : forall (x y : t) (Heq : eq x y), eq y x.
Proof. by apply SS.eq_sym. Qed.

Lemma eq_trans : forall (x y z : t) (eq1 : eq x y) (eq2 : eq y z), eq x z.
Proof. by apply SS.eq_trans. Qed.

Definition le_dec (x y : t) : {le x y} + {~ le x y}.
refine ((if physical_eq x y as c return
            physical_eq x y = c -> {le x y} + {~ le x y}
         then fun Hc => left _ else
           fun _ =>
             (if SS.subset x y as Bsub return
                 SS.subset x y = Bsub -> {le x y} + {~ le x y} then
                fun Hsub => left _
              else
                fun Hsub => right _) Logic.eq_refl) Logic.eq_refl); unfold le.
+ apply physical_eq_prop in Hc; subst; apply le_refl; by apply eq_refl.
+ by eauto using SS.subset_2.
+ i; apply SS.subset_1 in FH; by vauto.
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

Definition bot : t := SS.empty.

Lemma bot_prop : forall (x : t), le bot x.
Proof.
unfold le; i; destruct x.
apply SS.subset_2; unfold SS.subset, SS.MSet.subset; done.
Qed.

Definition join (x y : t) : t :=
  if le_dec x y then y else
  if le_dec y x then x else
    SS.union x y.

Lemma join_left : forall (x y : t), le x (join x y).
Proof.
  intros; unfold join.
  destruct (le_dec x y); auto.
  destruct (le_dec y x); [apply le_refl; apply eq_refl|].
  unfold le, SS.Subset. apply SS.union_2.
Qed.

Lemma join_right : forall (x y : t), le y (join x y).
Proof.
  intros; unfold join.
  destruct (le_dec x y); [apply le_refl; apply eq_refl|].
  destruct (le_dec y x); auto.
  unfold le, SS.Subset. apply SS.union_3.
Qed.

Lemma join_lub : forall (x y u : t) (Hx : le x u) (Hy : le y u), le (join x y) u.
Proof.
  i; unfold join; repeat dest_if_dec.
  unfold le, SS.Subset; intros a Hu.
  apply SS.union_1 in Hu; destruct Hu; auto using Hx, Hy.
Qed.

Definition meet (x y : t) : t :=
  if le_dec x y then x else
  if le_dec y x then y else
    SS.inter x y.

Lemma meet_left : forall (x y : t), le (meet x y) x.
Proof.
  intros; unfold meet.
  destruct (le_dec x y); [apply le_refl; apply eq_refl|].
  destruct (le_dec y x); auto.
  unfold le, SS.Subset. apply SS.inter_1.
Qed.

Lemma meet_right : forall (x y : t), le (meet x y) y.
Proof.
  intros; unfold meet.
  destruct (le_dec x y); auto.
  destruct (le_dec y x); [apply le_refl; apply eq_refl|].
  unfold le, SS.Subset. apply SS.inter_2.
Qed.

Lemma meet_glb : forall (x y l : t) (Hx : le l x) (Hy : le l y), le l (meet x y).
Proof.
  i; unfold meet; repeat dest_if_dec.
  unfold le, SS.Subset; intros a Hu.
  apply SS.inter_3; auto using Hx, Hy.
Qed.

Definition widen (x y : t) : t :=
  if structural_eq x y then x else
    SS.union x y.

Definition narrow (x y : t) : t :=
  if structural_eq x y then x else
    SS.inter x y.

Include JoinMeetProp.

(** * Functions for set *)

Definition empty : t := bot.

Definition is_empty := SS.is_empty.

Definition add (e : A.t) (x : t) : t := SS.add e x.

Lemma add_mor' : Proper (A.eq ==> le ==> le) add.
Proof. by apply SS.SF.add_s_m_Proper. Qed.

Lemma add_mor : Proper (A.eq ==> eq ==> eq) add.
Proof. by apply SS.SF.add_m. Qed.

Definition mem := SS.mem.

Definition elements := SS.elements.

Lemma mem_elements_1: forall (s : t) (x : elt) (Hin : In x (elements s)),
               mem x s = true.
Proof.
unfold mem, elements; i. rewrite SS.SF.elements_b.
induction (SS.elements s).
- inversion Hin.
- inversion Hin.
  + subst. s. apply Bool.orb_true_iff. left. unfold SS.SF.eqb.
    destruct (SS.E.eq_dec x x); [by auto|elim n; by apply SS.E.eq_refl].
  + s. apply Bool.orb_true_iff. right. by apply IHl.
Qed.

Lemma mem_elements_2: forall (s : t) (x : elt) (Hmem : mem x s = true),
                        exists x', A.eq x' x /\ In x' (elements s).
Proof.
unfold mem, elements. i. rewrite SS.SF.elements_b in Hmem.
induction (SS.elements s).
- by simpl in Hmem.
- simpl in Hmem. apply Bool.orb_true_iff in Hmem. destruct Hmem as [Hhd|Htl].
  + s. unfold SS.SF.eqb in Hhd. destruct (SS.E.eq_dec x a); [|by auto].
    exists a. split; [by apply A.eq_sym|by auto].
  + s. apply existsb_exists in Htl. destruct Htl as [x' [Hx'_in Hx'_eqb]].
    unfold SS.SF.eqb in Hx'_eqb. destruct (SS.E.eq_dec x x'); [|by auto].
    exists x'. split; [by apply A.eq_sym|by right].
Qed.

Lemma mem_monotone1 :
  forall k1 k2 (Hk : A.eq k1 k2) s1 s2 (Hs : le s1 s2) (Hmem : mem k1 s1 = true),
    mem k2 s2 = true.
Proof.
unfold le, mem; i.
apply SS.mem_1, SS.In_1 with k1; [by auto|]; apply Hs; by apply SS.mem_2.
Qed.

Lemma mem_monotone2 :
  forall k1 k2 (Hk : A.eq k1 k2) s1 s2 (Hs : le s1 s2) (Hmem : mem k2 s2 = false),
    mem k1 s1 = false.
Proof.
unfold mem; i.
apply SS.SF.not_mem_iff; apply SS.SF.not_mem_iff in Hmem.
intro Hmem'; elim Hmem.
apply SS.mem_2; apply SS.mem_1 in Hmem'.
eapply mem_monotone1; [by apply Hk|by apply Hs|by apply Hmem'].
Qed.

Lemma mem_mor : Proper (A.eq ==> eq ==> Logic.eq) mem.
Proof.
unfold Proper, respectful, eq, mem.
intros a1 a2 Ha s1 s2 Heq.
apply SS.SF.mem_m; [by auto|by apply Heq].
Qed.

Lemma mem_join_false :
  forall l s1 s2 (Hl : mem l (join s1 s2) = false),
    mem l s1 = false /\ mem l s2 = false.
Proof.
unfold mem, join; i.
destruct (le_dec s1 s2).
- split; [|by auto].
  unfold le in l0.
  apply SS.MF.not_mem_iff.
  apply SS.MF.not_mem_iff in Hl.
  intro; elim Hl.
  by apply l0.
- destruct (le_dec s2 s1).
  + split; [by auto|].
    unfold le in l0.
    apply SS.MF.not_mem_iff.
    apply SS.MF.not_mem_iff in Hl.
    intro; elim Hl.
    by apply l0.
  + rewrite SS.SF.union_b in Hl.
    by apply Bool.orb_false_iff.
Qed.

Lemma mem_join_false_inv :
  forall l s1 s2 (H1 : mem l s1 = false) (H2 : mem l s2 = false),
    mem l (join s1 s2) = false.
Proof.
i; unfold join.
destruct (le_dec s1 s2); [|destruct (le_dec s2 s1)]; unfold le in *.
- by auto.
- by auto.
- rewrite SS.SF.union_b; apply Bool.orb_false_iff; by auto.
Qed.

Lemma mem_join_left :
  forall l s1 s2 (Hs : mem l s1 = true), mem l (join s1 s2) = true.
Proof.
i. unfold join.
dest_if_dec; [eapply mem_monotone1; [by apply A.eq_refl|by apply l0|by auto]|].
dest_if_dec. eapply mem_monotone1; [by apply A.eq_refl| |by apply Hs].
intros a Ha; by apply SS.union_2.
Qed.

Lemma mem_join_right :
  forall l s1 s2 (Hs : mem l s2 = true), mem l (join s1 s2) = true.
Proof.
i. unfold join. dest_if_dec.
dest_if_dec; [eapply mem_monotone1; [by apply A.eq_refl|by apply l0|by auto]|].
 eapply mem_monotone1; [by apply A.eq_refl| |by apply Hs].
intros a Ha; by apply SS.union_3.
Qed.

Lemma mem_add_false :
  forall l l' s (Hl : mem l (add l' s) = false), ~ (A.eq l l').
Proof.
i; apply SS.MF.not_mem_iff in Hl; elim Hl.
apply SS.MF.add_iff.
left. by apply A.eq_sym.
Qed.

Lemma le_mem_false :
  forall l ls ls' (Hsubset : le ls' ls) (Hmem : mem l ls = false),
    mem l ls' = false.
Proof.
unfold le, mem; i.
apply SS.MF.not_mem_iff; intro Hmem'.
apply SS.MF.not_mem_iff in Hmem; elim Hmem.
by apply Hsubset.
Qed.

Lemma le_mem_true :
  forall l ls ls' (Hsubset : le ls' ls) (Hmem : mem l ls' = true),
    mem l ls = true.
Proof.
unfold le, mem; i.
apply SS.MF.mem_iff.
apply SS.MF.mem_iff in Hmem.
by apply Hsubset.
Qed.

Lemma mem_add_1 : forall l1 l2 s (Hl : A.eq l1 l2), mem l1 (add l2 s) = true.
Proof.
unfold mem, add; i. apply SS.MF.mem_iff.
apply SS.add_1. by apply A.eq_sym.
Qed.

Lemma mem_add_2 :
  forall l1 l2 s (Hl : not (A.eq l1 l2)), mem l1 (add l2 s) = mem l1 s.
Proof.
unfold mem, add; i. rewrite SS.SF.add_neq_b; [by auto|].
intro. elim Hl. by apply A.eq_sym.
Qed.

Lemma mem_add_3 :
  forall l1 l2 s (Hmem : mem l1 s = true), mem l1 (add l2 s) = true.
Proof.
i. destruct (A.eq_dec l1 l2); [by apply mem_add_1|by rewrite mem_add_2].
Qed.

Lemma empty_1 : forall e, mem e empty = false.
Proof. unfold mem, empty, bot. by apply SS.SF.empty_b. Qed.

Definition singleton (e : A.t) : t := SS.singleton e.

Lemma singleton_1 :
  forall e1 e2 (Heq : A.eq e1 e2), mem e1 (singleton e2) = true.
Proof.
unfold mem, singleton.
i. apply SS.OrigS.mem_1.
apply SS.OrigS.singleton_2.
by apply A.eq_sym.
Qed.

Lemma singleton_2 :
  forall e1 e2 (Hmem : mem e1 (singleton e2) = true), A.eq e1 e2.
Proof.
unfold mem, singleton. i.
by apply A.eq_sym, SS.OrigS.singleton_1, SS.OrigS.mem_2.
Qed.

Definition singleton_mor : Proper (A.eq ==> eq) singleton.
Proof.
intros a1 a2 Ha k; split; intros Hk.
- apply SS.MSF.P.Dec.F.mem_2.
  apply SS.MSF.P.Dec.F.mem_1 in Hk.
  apply singleton_2 in Hk.
  apply singleton_1.
  by apply A.eq_trans with a1.
- apply SS.MSF.P.Dec.F.mem_2.
  apply SS.MSF.P.Dec.F.mem_1 in Hk.
  apply singleton_2 in Hk.
  apply singleton_1.
  apply A.eq_trans with a2; [by auto|by apply A.eq_sym].
Qed.

Definition remove (e : A.t) (x : t) : t := SS.remove e x.
Definition union := SS.union.
Definition union_small_big small big := SS.fold SS.add small big.
Definition intersect := SS.inter.
Definition diff := SS.diff.
Definition subset := SS.subset.

Definition filter (f : A.t -> bool) (x : t) : t := SS.filter f x.

Lemma filter1 :
  forall x s f (Hf : Proper (A.eq ==> Logic.eq) f) (Hmem : mem x s = true)
     (Hx : f x = true),
    mem x (filter f s) = true.
Proof.
unfold mem, filter; i.
rewrite SS.mem_1; [by auto|].
eapply SS.filter_3; [by apply Hf|by apply SS.mem_2|by auto].
Qed.

Lemma filter2 :
  forall x s f (Hf : Proper (A.eq ==> Logic.eq) f) (Hx : f x = false),
    mem x (filter f s) = false.
Proof.
unfold mem, filter; i.
apply Bool.not_true_is_false; intro Hmem.
eapply Bool.eq_true_false_abs; [|by apply Hx].
eapply SS.filter_2; [by apply Hf|by apply SS.mem_2, Hmem].
Qed.

Definition fold := SS.fold.

Lemma fold_left_prsv (T U : Type) (P : T -> Prop) f :
  forall (Hf : forall e x (Hx : P x), P (f x e)) (l : list U) x (Hx : P x),
    P (fold_left f l x).
Proof.
induction l.
- by auto.
- s. i. apply IHl. apply Hf. by apply Hx.
Qed.

Lemma fold_left_prsv_strong (T U : Type) (P : T -> Prop) (Q : U -> Prop) f :
  forall (Hf : forall e (He : Q e) x (Hx : P x), P (f x e))
     (l : list U) (HQall : forall x : U, In x l -> Q x) x (Hx : P x),
    P (fold_left f l x).
Proof.
induction l.
- by auto.
- s. i. apply IHl.
  + i; apply HQall; by right.
  + apply Hf; [apply HQall; by left|by auto].
Qed.

Lemma fold_left_prsv2 (T1 T2 U : Type) (P : T1 -> T2 -> Prop) f1 f2:
  forall (Hf : forall v1 v2 (Hv : P v1 v2) (e : U), P (f1 v1 e) (f2 v2 e))
         l v1 v2 (Hv : P v1 v2),
    P (List.fold_left f1 l v1) (List.fold_left f2 l v2).
Proof.
induction l.
- by auto.
- s. i. apply IHl. apply Hf. by apply Hv.
Qed.

Lemma fold_2 (T : Type) (P Q: T -> Prop) f :
  forall e s (Hmem : mem e s = true)
         (He : forall (x : T) (Hx : P x), Q (f e x))
         (HP : forall e' (x : T) (Hx : P x), P (f e' x))
         (HQ : forall e' (x : T) (Hx : Q x), Q (f e' x))
         (Hf_eq : forall e1 e2 (He1 : A.eq e1 e2) (x : T) (He1 : Q (f e1 x)),
                    Q (f e2 x))
         (x : T) (Hx : P x),
    Q (fold f s x).
Proof.
unfold fold. intros. rewrite SS.fold_1.
apply mem_elements_2 in Hmem. destruct Hmem as [e' [Heq Hin]].
generalize dependent x. unfold elements in Hin. induction (SS.elements s).
- inversion Hin.
- s. inversion Hin.
  + subst. i. apply fold_left_prsv; [i; by apply HQ|].
    eapply Hf_eq; [apply A.eq_sym; by apply Heq|]; by auto.
  + i. apply IHl; [by auto|]. by apply HP.
Qed.

Lemma a_eq_equiv : Equivalence A.eq.
Proof.
constructor.
intros ?; by apply A.eq_refl.
intros ? ?; by apply A.eq_sym.
intros ? ? ?; by apply A.eq_trans.
Qed.

Lemma fold_2_strong (T : Type) (P Q: T -> Prop) f :
  forall e s (Hmem : mem e s = true)
         (He : forall (x : T) (Hx : P x), Q (f e x))
         (HP : forall e' (He' : ~ A.eq e e') (x : T) (Hx : P x), P (f e' x))
         (HQ : forall e' (He' : ~ A.eq e e') (x : T) (Hx : Q x), Q (f e' x))
         (Hf_eq : forall e1 e2 (He1 : A.eq e1 e2) (x : T) (He1 : Q (f e1 x)),
                    Q (f e2 x))
         (x : T) (Hx : P x),
    Q (fold f s x).
Proof.
unfold fold; i. rewrite SS.fold_1.
apply mem_elements_2 in Hmem. destruct Hmem as [e' [Heq Hin]].
unfold elements in Hin. assert (Hnodup := SS.elements_3w s).
generalize dependent x. induction (SS.elements s).
- inversion Hin.
- s. inversion Hin.
  + subst; i; apply fold_left_prsv_strong with (Q := fun e => ~ A.eq e' e).
    * i; apply HQ; [i; elim He0; by apply A.eq_trans with e|by auto].
    * i; inversion Hnodup; subst; elim H2.
      apply InA_eqA with x0; [by apply a_eq_equiv|by apply A.eq_sym|].
      apply In_InA; [by apply a_eq_equiv|by auto].
    * eapply Hf_eq; [apply A.eq_sym; by apply Heq|]; by auto.
  + i. apply IHl; [by auto|by inversion Hnodup|].
    apply HP; [|by auto]; i; inversion Hnodup; subst; elim H2.
    apply InA_eqA with e'; [by apply a_eq_equiv|by apply A.eq_trans with e|].
    apply In_InA; [by apply a_eq_equiv|by auto].
Qed.

Lemma fold_1 (T : Type) (P : T -> Prop) f :
  forall e s (Hmem : mem e s = true)
         (He : forall (x : T), P (f e x))
         (Hf_mono : forall e' (x : T) (Hx : P x), P (f e' x))
         (Hf_eq : forall e1 e2 (He1 : A.eq e1 e2) (x : T) (He1 : P (f e1 x)),
                    P (f e2 x))
         (x : T),
    P (fold f s x).
Proof.
i. apply fold_2 with (P:=fun _ => True) (e:=e) (s:=s); by auto.
Qed.

Lemma fold_3 (T : Type) (P : T -> Prop) f :
  forall s
         (Hf_mono : forall e x (He : mem e s = true) (Hx : P x), P (f e x))
         (x : T) (Hx : P x),
    P (fold f s x).
Proof.
unfold fold. i. rewrite SS.fold_1.
assert (forall e x (He : In e (SS.elements s)) (Hx : P x), P (f e x))
  as Hf_mono'
; [i; apply Hf_mono; [by apply mem_elements_1|by auto]|].
generalize x Hx Hf_mono'. clear x Hx Hf_mono'. induction (SS.elements s).
- by auto.
- s. i. apply IHl.
  + apply Hf_mono'; by auto.
  + i. apply Hf_mono'; by auto.
Qed.

Lemma fold2_1 :
  forall T (P : T -> T -> Prop)
         (P_trans : forall x y z, P x y -> P y z -> P x z)
         f f' i
         (Hf_ext : forall e x, P x (f e x))
         (Hff' : forall e x1 x2 (Hi : P i x1) (Hx : P x1 x2),
                   P (f e x1) (f' e x2))
         s (x1 x2 : T) (Hi : P i x1) (Hx : P x1 x2),
    P (fold f s x1) (fold f' s x2).
Proof.
unfold fold. i. do 2 rewrite SS.fold_1.
generalize x1 x2 Hi Hx; clear x1 x2 Hi Hx.
induction (SS.elements s); i; s.
- by apply Hx.
- apply IHl.
  + eapply P_trans; [by apply Hi|by apply Hf_ext].
  + by apply Hff'.
Qed.

Lemma fold2_3 :
  forall T Q (P : T -> Q -> Prop)
    f1 f2 (Hf : forall e1 e2 (He : A.eq e1 e2) t1 t2 (Ht : P t1 t2),
              P (f1 e1 t1) (f2 e2 t2))
    s1 s2 (Hs : eq s1 s2) i1 i2 (Hi : P i1 i2),
  P (fold f1 s1 i1) (fold f2 s2 i2).
Proof.
unfold fold. i. do 2 rewrite SS.fold_1. apply SS.elements_eq in Hs.
generalize i1 i2 Hi; clear i1 i2 Hi.
induction Hs.
- by auto.
- s; i; apply IHHs. by apply Hf.
Qed.

Lemma fold2_4 :
  forall T Q (P : T -> Q -> Prop)
     f1 f2 (Hf : forall e t1 t2 (Ht : P t1 t2), P (f1 e t1) (f2 e t2))
     s i1 i2 (Hi : P i1 i2),
  P (fold f1 s i1) (fold f2 s i2).
Proof.
unfold fold. i. do 2 rewrite SS.fold_1.
generalize i1 i2 Hi; clear i1 i2 Hi.
induction (SS.elements s).
- by auto.
- s; i; apply IHl; by apply Hf.
Qed.

Lemma fold2_5' :
  forall T Q (P : T -> Q -> Prop)
     (l : list elt) f1 f2
     (Hf : forall e (He : In e l) t1 t2 (Ht : P t1 t2),
         P (f1 e t1) (f2 e t2))
     i1 i2 (Hi : P i1 i2),
  P (fold_left (fun a e => f1 e a) l i1) (fold_left (fun a e => f2 e a) l i2).
Proof.
induction l.
- by auto.
- s; i; apply IHl.
  + i. apply Hf; [by right|by auto].
  + apply Hf; [by left|by auto].
Qed.

Lemma fold2_5 :
  forall T Q (P : T -> Q -> Prop)
     s f1 f2
     (Hf : forall e (He : mem e s = true) t1 t2 (Ht : P t1 t2),
         P (f1 e t1) (f2 e t2))
     i1 i2 (Hi : P i1 i2),
  P (fold f1 s i1) (fold f2 s i2).
Proof.
unfold fold. i. do 2 rewrite SS.fold_1.
apply fold2_5'; [|by auto].
i. apply Hf; [by apply mem_elements_1|by auto].
Qed.

Lemma fold2_2 :
  forall T (P : T -> T -> Prop)
    f1 f2 (Hf : forall e1 e2 (He : A.eq e1 e2) t1 t2 (Ht : P t1 t2),
              P (f1 e1 t1) (f2 e2 t2))
    s1 s2 (Hs : eq s1 s2) i1 i2 (Hi : P i1 i2),
  P (fold f1 s1 i1) (fold f2 s2 i2).
Proof. i; by apply fold2_3. Qed.

Lemma fold_mor (T : Type) :
  forall (teq : relation T) (teq_equiv : DLat.zb_equiv teq),
    let feq f1 f2 :=
      forall x1 x2 (Hx : A.eq x1 x2) acc1 acc2 (Hacc : teq acc1 acc2),
        teq (f1 x1 acc1) (f2 x2 acc2) in
    Proper (feq ==> eq ==> teq ==> teq) (@fold T).
Proof.
i; intros f1 f2 Hf s1 s2 Hs i1 i2 Hi.
apply fold2_2; [by apply Hf|by auto|by auto].
Qed.

Definition iter (f : A.t -> unit) (s : t) : unit :=
  SS.fold (fun x acc => (fun _ => acc) (f x)) s tt.

Lemma elements_eq :
  forall ls1 ls2 (Heq : eq ls1 ls2),
    eqlistA A.eq (elements ls1) (elements ls2).
Proof. by apply SS.elements_eq. Qed.

Definition cardinal := SS.cardinal.

Definition choose := SS.choose.

Lemma choose_mor : Proper (eq ==> opt_eq A.eq) choose.
Proof. by apply SS.choose_mor. Qed.

Definition choose_only := SS.choose_only.

Lemma choose_only_mor : Proper (eq ==> opt_eq A.eq) choose_only.
Proof. by apply SS.choose_only_mor. Qed.

Lemma choose_only_1 :
  forall s e (Hce : choose_only s = Some e), elements s = cons e nil.
Proof. by apply SS.choose_only_1. Qed.

Lemma choose_only_2 :
  forall l1 l2 l' (Hco : choose_only l' = Some l1) (Hmem : mem l2 l' = true),
    A.eq l1 l2.
Proof. by apply SS.choose_only_2. Qed.

Definition for_all := SS.for_all'.

Definition for_all_1 :
  forall k s print f (Hk: mem k s) (Hf: compat_bool A.eq f)
         (Hfor_all: for_all print f s = true),
    f k = true.
Proof.
i. rewrite SS.for_all'_1 in Hfor_all.
apply SS.for_all_2 in Hfor_all; [|by auto].
apply Hfor_all. by apply SS.OrigS.mem_2.
Qed.

End Pow.
