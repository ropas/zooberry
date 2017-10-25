(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
Set Implicit Arguments.

(* The next functions are added to FMapAVL.v.
- for_all: for all condition checker
- strong_le: strong less than equal checker
- filter
*)

Require Import OrderedType FMapAVL.
Require FMapFacts.
Require Import VocabA.
Require Import FunInd.

Local Open Scope bool.

Module FMapAVL'.

Module Make (X: OrderedType).

Include FMapAVL.Make X.
Include FMapFacts.OrdProperties.
  
Tactic Notation "factornode" ident(l) ident(x) ident(d) ident(r) ident(h)
 "as" ident(s) :=
 set (s:=Raw.Node l x d r h) in *; clearbody s; clear l x d r h.

(** A tactic for cleaning hypothesis after use of functional induction. *)

Ltac clearf :=
 match goal with
  | H : (@Logic.eq (Compare _ _ _ _) _ _) |- _ => clear H; clearf
  | H : (@Logic.eq (sumbool _ _) _ _) |- _ => clear H; clearf
  | _ => idtac
 end.

(** A tactic to repeat [inversion_clear] on all hyps of the
    form [(f (Node ...))] *)

Ltac inv f :=
  match goal with
     | H:f (Raw.Leaf _) |- _ => inversion_clear H; inv f
     | H:f _ (Raw.Leaf _) |- _ => inversion_clear H; inv f
     | H:f _ _ (Raw.Leaf _) |- _ => inversion_clear H; inv f
     | H:f _ _ _ (Raw.Leaf _) |- _ => inversion_clear H; inv f
     | H:f (Raw.Node _ _ _ _ _) |- _ => inversion_clear H; inv f
     | H:f _ (Raw.Node _ _ _ _ _) |- _ => inversion_clear H; inv f
     | H:f _ _ (Raw.Node _ _ _ _ _) |- _ => inversion_clear H; inv f
     | H:f _ _ _ (Raw.Node _ _ _ _ _) |- _ => inversion_clear H; inv f
     | _ => idtac
  end.

Ltac inv_all f :=
  match goal with
   | H: f _ |- _ => inversion_clear H; inv f
   | H: f _ _ |- _ => inversion_clear H; inv f
   | H: f _ _ _ |- _ => inversion_clear H; inv f
   | H: f _ _ _ _ |- _ => inversion_clear H; inv f
   | _ => idtac
  end.

(** Helper tactic concerning order of elements. *)

Ltac order := match goal with
 | U: Raw.lt_tree _ ?s, V: Raw.In _ ?s |- _ => generalize (U _ V); clear U; order
 | U: Raw.gt_tree _ ?s, V: Raw.In _ ?s |- _ => generalize (U _ V); clear U; order
 | _ => Raw.Proofs.MX.order
end.

Ltac intuition_in := repeat progress (intuition; inv Raw.In; inv Raw.MapsTo).

(* Function/Functional Scheme can't deal with internal fix.
   Let's do its job by hand: *)

Module Raw2.

Section Elt.

Variable elt : Type.

(** * For all condition check *)
Fixpoint for_all (print2 : key -> elt -> unit)
         (cond : key -> elt -> bool) (m : Raw.t elt) : bool :=
  match m with
    | Raw.Leaf _ => true
    | Raw.Node l x d r _ =>
      for_all print2 cond l
      && print_when_false (print2 x) d (cond x) d
      && for_all print2 cond r
  end.

(** * Less than equal using physical equality *)
Fixpoint strong_le (elt_le : elt -> elt -> bool) m1 m2 :=
  physical_eq m1 m2
  || match m1, m2 with
       | Raw.Leaf _, _ => true
       | Raw.Node l1 x1 d1 r1 _, Raw.Node l2 x2 d2 r2 _ =>
         strong_le elt_le l1 l2
         && match X.compare x1 x2 with
              | EQ _ => true
              | _ => false
            end
         && elt_le d1 d2
         && strong_le elt_le r1 r2
       | _, _ => false
     end.

Functional Scheme for_all_ind := Induction for for_all Sort Prop.
Functional Scheme strong_le_ind := Induction for strong_le Sort Prop.

Hint Unfold print_when_false.

Ltac destr :=
  repeat (try apply andb_true_intro; try split);
  repeat match goal with
           | [H : _ && _ = true |- _] => apply andb_prop in H; destruct H
           | [H : _ || _ = true |- _] => apply Bool.orb_prop in H; destruct H; try discriminate
           | [H : _ \/ _ |- _] => destruct H; try discriminate
         end. 

Ltac phy_eq :=
  repeat match goal with
           | [H : physical_eq (Raw.Node _ _ _ _ _) (Raw.Leaf _) = true |- _] =>
             apply physical_eq_prop in H; discriminate
           | [H : physical_eq (Raw.Leaf _) (Raw.Node _ _ _ _ _) = true |- _] =>
             apply physical_eq_prop in H; discriminate
           | [H : physical_eq (Raw.Node _ _ _ _ _) (Raw.Node _ _ _ _ _) = true |- _] =>
             apply physical_eq_prop in H; rewrite H; clear H
           | [H : physical_eq (Raw.Leaf _) (Raw.Leaf _) = true |- _] =>
             apply physical_eq_prop in H; rewrite H; clear H
         end.

Ltac find_triv := destruct (Raw.find _ _); [left|right]; eauto.

Lemma for_all_1 (print2 : key -> elt -> unit) (cond : key -> elt -> bool)
      (m : Raw.t elt) :
  (forall k v (Hmaps : Raw.MapsTo k v m), cond k v = true)
  -> for_all print2 cond m = true.
Proof.
  functional induction (for_all print2 cond m); auto; intros.
  destr; auto. autounfold; auto.
Qed.

Lemma for_all_2 (print2 : key -> elt -> unit) (cond : key -> elt -> bool)
      (Hcond : forall k k' (Hk : X.eq k k') v, cond k v = cond k' v)
      (m : Raw.t elt) :
  for_all print2 cond m = true
  -> forall k v (Hmaps : Raw.MapsTo k v m), cond k v = true.
Proof.
  functional induction (for_all print2 cond m); auto; intros; destr
  ; inv_all Raw.MapsTo; auto.
  erewrite Hcond; [apply H1|auto].
Qed.

Lemma for_all_2' (print2 : key -> elt -> unit) (cond : key -> elt -> bool)
      (Hcond : forall k k' (Hk : X.eq k k') v, cond k v = cond k' v)
      (m : Raw.t elt) :
  for_all print2 cond m = false
  -> exists k v, Raw.MapsTo k v m /\ cond k v = false.
Proof.
functional induction (for_all print2 cond m); [discriminate|].
unfold print_when_false; intros conds.
apply Bool.andb_false_iff in conds; destruct conds
; [apply Bool.andb_false_iff in H; destruct H|].
- destruct (IHb H) as [k [v [Hmaps Hfalse]]].
  exists k; exists v; auto.
- exists x; exists d; auto.
- destruct (IHb0 H) as [k [v [Hmaps Hfalse]]].
  exists k; exists v; auto.
Qed.

Lemma strong_le_1 (elt_le : elt -> elt -> bool)
      (Helt_le: forall v, elt_le v v = true) m1 m2
      (Hle: strong_le elt_le m1 m2 = true) :
  forall k,
    (exists v1, exists v2,
     Raw.find k m1 = Some v1 /\ Raw.find k m2 = Some v2 /\ elt_le v1 v2 = true)
    \/ Raw.find k m1 = None.
Proof.
functional induction (strong_le elt_le m1 m2); intros.
- right; tauto.
- destr; phy_eq.
- destr; phy_eq; [find_triv|discriminate].
- destr; phy_eq; [find_triv|].  
  simpl; destruct (X.compare k x1), (X.compare k x2); auto; try order.
  left; eauto.
- destr; phy_eq; [find_triv|discriminate].
Qed.

End Elt.

End Raw2.

Section Elt.
Variable elt : Type.

Lemma mapsto_in : forall k (v : elt) x (Hmaps : MapsTo k v x), In k x.
Proof.
intros; apply P.F.find_mapsto_iff in Hmaps.
apply P.F.in_find_iff; congruence.
Qed.

Definition for_all (print2 : key -> elt -> unit) cond m :=
  Raw2.for_all print2 cond m.(this).

Lemma for_all_1 (print2 : key -> elt -> unit)
       (cond : key -> elt -> bool) (m : t elt) :
   (forall k v (Hmaps : MapsTo k v m), cond k v = true)
   -> for_all print2 cond m = true.
Proof. eauto using Raw2.for_all_1. Qed.

Lemma for_all_2 (print2 : key -> elt -> unit)
      (cond : key -> elt -> bool)
      (Hcond : forall k k' (Hk : X.eq k k') v, cond k v = cond k' v)
      (m : t elt) :
  for_all print2 cond m = true
  -> forall k v (Hmaps : MapsTo k v m), cond k v = true.
Proof. eauto using Raw2.for_all_2. Qed.

Lemma for_all_2' (print2 : key -> elt -> unit)
      (cond : key -> elt -> bool)
      (Hcond : forall k k' (Hk : X.eq k k') v, cond k v = cond k' v)
      (m : t elt) :
  for_all print2 cond m = false
  -> exists k v, MapsTo k v m /\ cond k v = false.
Proof.
intros Hforall.
destruct (Raw2.for_all_2' print2 cond Hcond m Hforall) as [x [v [Hmaps Hfalse]]].
exists x; exists v; auto.
Qed.

Definition strong_le (elt_le : elt -> elt -> bool) m m' :=
  Raw2.strong_le elt_le m.(this) m'.(this).

Lemma strong_le_1 (elt_le : elt -> elt -> bool)
      (Helt_le: forall v, elt_le v v = true) m1 m2
      (Hle: strong_le elt_le m1 m2 = true) :
  forall k,
    (exists v1, exists v2,
                  find k m1 = Some v1 /\ find k m2 = Some v2 /\ elt_le v1 v2 = true)
    \/ find k m1 = None.
Proof. eauto using Raw2.strong_le_1. Qed.

Definition filter (f : key -> bool) (m : t elt) : t elt :=
  P.filter (fun k _ => f k) m.

Lemma filter_1 :
  forall k cond m (Hmor : Morphisms.Proper (X.eq ==> eq) cond)
         (Hcond : cond k = true),
    find k (filter cond m) = find k m.
Proof.
unfold filter; intros.
repeat match goal with
  | [|- context [find ?k ?m]] => remember (find k m) as b; destruct b
end.
- symmetry in Heqb; symmetry in Heqb0.
  apply P.F.find_mapsto_iff in Heqb.
  apply P.F.find_mapsto_iff in Heqb0.
  apply P.filter_iff in Heqb
  ; [|intros k1 k2 Hk v1 v2 Hv; apply Hmor; assumption].
  destruct Heqb as [Heqb _].
  f_equal. apply (P.F.MapsTo_fun Heqb Heqb0).
- symmetry in Heqb; symmetry in Heqb0.
  apply P.F.find_mapsto_iff in Heqb.
  apply P.filter_iff in Heqb
  ; [|intros k1 k2 Hk v1 v2 Hv; apply Hmor; assumption].
  destruct Heqb as [Heqb _].
  apply P.F.find_mapsto_iff in Heqb; congruence.
- symmetry in Heqb; symmetry in Heqb0.
  apply P.F.find_mapsto_iff in Heqb0.
  assert (MapsTo k e (P.filter (fun (k0 : key) (_ : elt) => cond k0) m))
  ; [apply P.filter_iff; [intros k1 k2 Hk v1 v2 Hv; auto|auto]|].
  apply P.F.find_mapsto_iff in H; congruence.
- auto.
Qed.

Lemma filter_2 :
  forall k cond m (Hmor : Morphisms.Proper (X.eq ==> eq) cond)
         (Hcond : cond k = false),
    find k (filter cond m) = None.
Proof.
unfold filter; intros.
apply P.F.not_find_in_iff; intro Hin.
apply P.F.in_find_iff in Hin.
remember (find k (P.filter (fun k _ => cond k) m)) as v; destruct v; [|tauto].
symmetry in Heqv; apply P.F.find_mapsto_iff in Heqv.
apply P.filter_iff in Heqv; [|intros k1 k2 Hk v1 v2 Hv; auto].
destruct Heqv as [_ Hcond']; congruence.
Qed.

Lemma filter_3 :
  forall k v cond m (Hmor : Morphisms.Proper (X.eq ==> eq) cond)
     (Hfind : find k (filter cond m) = Some v),
    find k m = Some v.
Proof.
intros. remember (cond k) as b; destruct b.
- rewrite filter_1 in Hfind; auto.
- rewrite filter_2 in Hfind; [inversion Hfind|auto|auto].
Qed.

End Elt.

End Make.

End FMapAVL'.
