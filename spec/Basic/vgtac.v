(* *********************************************************************)
(*                                                                     *)
(*                   Viktor and Gil's lemmas & tactics                         *)
(*                                                                     *)
(* *********************************************************************)

(** This file collects a number of basic lemmas and tactics for better
    proof automation, structuring large proofs, or rewriting.  Most of 
    the rewriting support is ported from ss-reflect. *)

(** Symbols starting with [vlib__] are internal. *)

Require Import Bool.
Require Import Arith.
Require Import ZArith.
Require Import String.
Require Import Program.
(*Require Export paconotation.*)

Set Implicit Arguments.

Hint Unfold not iff id.

Notation " [ x ] " := (cons x nil) : list_scope.
Notation " [ x ; .. ; y ] " := (cons x .. (cons y nil) ..) : list_scope.

Global Set Warnings "-notation-overridden".

Notation "~ x" := (forall (FH: x), False) : type_scope.

(* Function composition *)
Notation "f <*> g" := (compose f g) (at level 49, left associativity).

(* ************************************************************************** *)
(** * Coersion of [bool] into [Prop] *)
(* ************************************************************************** *)

(** Coersion of bools into Prop *)
Coercion is_true (b : bool) : Prop := b = true.

(** Hints for auto *)
Lemma vlib__true_is_true : true.
Proof. reflexivity. Qed.

Lemma vlib__not_false_is_true : ~ false.
Proof. discriminate. Qed.

Lemma vlib__negb_rewrite: forall {b}, negb b -> b = false.
Proof. intros []; (reflexivity || discriminate). Qed.

Lemma vlib__andb_split: forall {b1 b2}, b1 && b2 -> b1 /\ b2.
Proof. intros [] []; try discriminate; auto. Qed.

Hint Resolve vlib__true_is_true vlib__not_false_is_true.

(* ************************************************************************** *)
(** * Basic automation tactics *)
(* ************************************************************************** *)

(** Set up for basic simplification *)

Create HintDb vlib discriminated. 

(** Adaptation of the ss-reflect "[done]" tactic. *)

Ltac vlib__basic_done := 
  solve [trivial with vlib | apply sym_equal; trivial | discriminate | contradiction].

Ltac done := unfold not in *; trivial with vlib; hnf; intros;
  solve [try vlib__basic_done; split; 
         try vlib__basic_done; split; 
         try vlib__basic_done; split; 
         try vlib__basic_done; split; 
         try vlib__basic_done; split; vlib__basic_done
    | match goal with H : ~ _ |- _ => solve [case H; trivial] end].

(** A variant of the ssr "done" tactic that performs "eassumption". *)

Ltac edone := try eassumption; trivial; hnf; intros;
  solve [try eassumption; try vlib__basic_done; split; 
         try eassumption; try vlib__basic_done; split; 
         try eassumption; try vlib__basic_done; split; 
         try eassumption; try vlib__basic_done; split; 
         try eassumption; try vlib__basic_done; split;
         try eassumption; vlib__basic_done
    | match goal with H : ~ _ |- _ => solve [case H; trivial] end].

Tactic Notation "by"  tactic(tac) := (tac; done).
Tactic Notation "eby" tactic(tac) := (tac; edone).

Ltac vlib__complaining_inj f H :=
  let X := fresh in
  (match goal with | [|- ?P ] => set (X := P) end);
  injection H;
  (lazymatch goal with | [ |- f _ = f _ -> _] => fail | _ => idtac end);
  clear H; intros;
  subst X;
  try subst.

Ltac vlib__clarify1 :=
  try subst;
  repeat match goal with
  | [H: is_true (andb _ _) |- _] => case (vlib__andb_split H); clear H; intros ? H
  | [H: is_true (negb ?x) |- _] => rewrite (vlib__negb_rewrite H) in *
  | [H: is_true ?x        |- _] => rewrite H in *
  | [H: ?x = true         |- _] => rewrite H in *
  | [H: ?x = false        |- _] => rewrite H in *
  | [H: ?f _             = ?f _             |- _] => vlib__complaining_inj f H
  | [H: ?f _ _           = ?f _ _           |- _] => vlib__complaining_inj f H
  | [H: ?f _ _ _         = ?f _ _ _         |- _] => vlib__complaining_inj f H
  | [H: ?f _ _ _ _       = ?f _ _ _ _       |- _] => vlib__complaining_inj f H
  | [H: ?f _ _ _ _ _     = ?f _ _ _ _ _     |- _] => vlib__complaining_inj f H
  | [H: ?f _ _ _ _ _ _   = ?f _ _ _ _ _ _   |- _] => vlib__complaining_inj f H
  | [H: ?f _ _ _ _ _ _ _ = ?f _ _ _ _ _ _ _ |- _] => vlib__complaining_inj f H
  end; try done.

(** Perform injections & discriminations on all hypotheses *)

Ltac clarify :=
  vlib__clarify1;
  repeat match goal with
    | H1: ?x = Some _, H2: ?x = None   |- _ => rewrite H2 in H1; vlib__clarify1
    | H1: ?x = Some _, H2: ?x = Some _ |- _ => rewrite H2 in H1; vlib__clarify1
  end.

(** Kill simple goals that require up to two econstructor calls. *)

Ltac vauto :=
  (clarify; try edone; 
   try ([> once (econstructor; (solve [edone | [> once (econstructor; edone) ..] ])) ..])).

(** Check that the hypothesis [id] is defined. This is useful to make sure that
    an [assert] has been completely finished. *)
    
Ltac end_assert id := 
  let m := fresh in 
  pose (m := refl_equal id); clear m.

Ltac inv x := inversion x; clarify.
Ltac simpls  := simpl in *; try done.
Ltac intross := simpl in *; try done; intros.

Tactic Notation "case_eq" constr(x) := case_eq (x).

Tactic Notation "case_eq" constr(x) "as" simple_intropattern(H) :=
  destruct x as [] eqn: H; try done.


(* ************************************************************************** *)
(** * Basic simplication tactics *)
(* ************************************************************************** *)

Ltac vlib__clarsimp1 :=
  clarify; (autorewrite with vlib in * ); try done;
  match goal with
  | [H: is_true ?x |- _] => rewrite H in *; vlib__clarsimp1
  | [H: ?x = true |- _] => rewrite H in *; vlib__clarsimp1
  | [H: ?x = false |- _] => rewrite H in *; vlib__clarsimp1
  | _ => clarify; auto 1 with vlib
  end.

Ltac clarsimp := intros; simpl in *; vlib__clarsimp1.

Ltac autos   := clarsimp; auto with vlib.

(* hdesH, hdes: more general des *)

Definition  NW A (P: () -> A) : A := P ().

Notation "<< x : t >>" := (NW (fun x => t)) (at level 80, x ident, no associativity).
Notation "<< t >>" := (NW (fun _ => t)) (at level 79, no associativity).

Ltac unnw := unfold NW in *.
Ltac rednw := red; unnw.

Hint Unfold NW.

Ltac get_concl := lazymatch goal with [ |- ?G ] => G end.

Ltac des1 :=
  match goal with
    | H : NW _ |- _ => red in H
    | H : exists x, NW (fun y => _) |- _ => 
      let x' := fresh x in let y' := fresh y in destruct H as [x' y']; red in y'
    | H : exists x, ?p |- _ => 
      let x' := fresh x in destruct H as [x' H]
    | H : ?p /\ ?q |- _ => 
      let x' := match p with | NW (fun z => _) => fresh z | _ => H end in
      let y' := match q with | NW (fun z => _) => fresh z | _ => fresh H end in
      destruct H as [x' y'];
      match p with | NW _ => red in x' | _ => idtac end;
      match q with | NW _ => red in y' | _ => idtac end
    | H : ?p <-> ?q |- _ => 
      let x' := match p with | NW (fun z => _) => fresh z | _ => H end in
      let y' := match q with | NW (fun z => _) => fresh z | _ => fresh H end in
      destruct H as [x' y'];
      match p with | NW _ => unfold NW at 1 in x'; red in y' | _ => idtac end;
      match q with | NW _ => unfold NW at 1 in y'; red in x' | _ => idtac end
    | H : ?p \/ ?q |- _ =>
      let x' := match p with | NW (fun z => _) => fresh z | _ => H end in
      let y' := match q with | NW (fun z => _) => fresh z | _ => H end in
      destruct H as [x' | y'];
      [ match p with | NW _ => red in x' | _ => idtac end
      | match q with | NW _ => red in y' | _ => idtac end]
  end.

Ltac des := repeat des1.

Ltac forall_split :=
  let H := fresh "__forall_split__" in first [intro; forall_split; match goal with [H:_|-_] => revert H end | split].

Definition __HID__ (A : Type) (a : A) := a.

Ltac hdesHi H P x y :=
  let FF := fresh "__hdesfalse__" in 
  let TMP := fresh "__hdesHi__" in 
  let P1 := fresh "__hdesHi__" in 
  let P2 := fresh "__hdesHi__" in 
    evar (P1 : Prop); evar (P2 : Prop);
    assert (TMP: False -> P) by
      (intro FF; forall_split;
         [ let G := get_concl in set (TMP := G); revert P1; instantiate (1:=G)
         | let G := get_concl in set (TMP := G); revert P2; instantiate (1:=G) ];
       destruct FF);
    try clear TMP; 
    try (try (match goal with [Def := ?G : _ |- _] =>
              match Def with P1 =>
              match goal with [_ : G |- _] => fail 4 end end end);
         assert (x: P1) by (unfold P1; repeat (let x := fresh "__xhj__" in intro x; specialize (H x)); apply H));
    try unfold P1 in x; try clear P1;
    try (try (match goal with [Def := ?G : _ |- _] =>
              match Def with P2 =>
              match goal with [_ : G |- _] => fail 4 end end end);
         assert (y: P2) by (unfold P2; repeat (let x := fresh "__xhj__" in intro x; specialize (H x)); apply H)); 
    try unfold P2 in y; try clear P2;
    fold (__HID__ P) in H;
    try clear H.

Ltac hdesHP H P :=
  let H' := fresh H in let H'' := fresh H in
  match P with 
  | context[ NW (fun x => _) /\ NW (fun y => _) ] => 
    let x' := fresh x in let y' := fresh y in
    hdesHi H P x' y'; red in x'; red in y'
  | context[ NW (fun x => _) /\ _ ] => 
    let x' := fresh x in
    hdesHi H P x' H'; red in x'
  | context[ _ /\ NW (fun y => _) ] => 
    let y' := fresh y in
    hdesHi H P H' y'; red in y'
  | context[ _ /\ _ ] => 
    hdesHi H P H' H''
  | context[ NW (fun x => _) <-> NW (fun y => _) ] =>
    let x' := fresh x in let y' := fresh y in
    hdesHi H P x' y'; red in x'; red in y'
  | context[ NW (fun x => _) <-> _ ] => 
    let x' := fresh x in
    hdesHi H P x' H'; red in x'
  | context[ _ <-> NW (fun y => _) ] => 
    let y' := fresh y in
    hdesHi H P H' y'; red in y'
  | context[ _ <-> _ ] => 
    hdesHi H P H' H''
  end.

Ltac hdesH H := let P := type of H in hdesHP H P; unfold __HID__ in *.

(*
(* It works, but too slows *)
Ltac hdesF P :=
  match P with
  | fun _ => _ /\ _ => idtac
  | fun _ => _ <-> _ => idtac
  | fun x => forall y : @?ty x, @?f x y =>
    let P' := eval cbv beta in (fun p : sigT ty => f (projT1 p) (projT2 p)) in
      hdesF P'
  end.

Ltac hdes := 
  repeat match goal with | H : ?P |- _ => hdesF (fun _ : unit => P); hdesHP H P end; 
  unfold __HID__ in *.
*)

Ltac hdesF P :=
  match P with | _ /\ _ => idtac | _ <-> _ => idtac | forall _, _ => 
  match P with | forall _, _ /\ _ => idtac | forall _, _ <-> _ => idtac | forall _ _, _ => 
  match P with | forall _ _, _ /\ _ => idtac | forall _ _, _ <-> _ => idtac | forall _ _ _, _ =>
  match P with | forall _ _ _, _ /\ _ => idtac | forall _ _ _, _ <-> _ => idtac | forall _ _ _ _, _ => 
  match P with | forall _ _ _ _, _ /\ _ => idtac | forall _ _ _ _, _ <-> _ => idtac | forall _ _ _ _ _, _ =>
  match P with | forall _ _ _ _ _, _ /\ _ => idtac | forall _ _ _ _ _, _ <-> _ => idtac | forall _ _ _ _ _ _, _ => 
  match P with | forall _ _ _ _ _ _, _ /\ _ => idtac | forall _ _ _ _ _ _, _ <-> _ => idtac | forall _ _ _ _ _ _ _, _ => 
  match P with | forall _ _ _ _ _ _ _, _ /\ _ => idtac | forall _ _ _ _ _ _ _, _ <-> _ => idtac | forall _ _ _ _ _ _ _ _, _ => 
  match P with | forall _ _ _ _ _ _ _ _, _ /\ _ => idtac | forall _ _ _ _ _ _ _ _, _ <-> _ => idtac | forall _ _ _ _ _ _ _ _ _, _ =>
  match P with | forall _ _ _ _ _ _ _ _ _, _ /\ _ => idtac | forall _ _ _ _ _ _ _ _ _, _ <-> _ => idtac | forall _ _ _ _ _ _ _ _ _ _, _ => 
  match P with | forall _ _ _ _ _ _ _ _ _ _, _ /\ _ => idtac | forall _ _ _ _ _ _ _ _ _ _, _ <-> _ => idtac | forall _ _ _ _ _ _ _ _ _ _ _, _ => 
  match P with | forall _ _ _ _ _ _ _ _ _ _ _, _ /\ _ => idtac | forall _ _ _ _ _ _ _ _ _ _ _, _ <-> _ => idtac | forall _ _ _ _ _ _ _ _ _ _ _ _, _ => 
  match P with | forall _ _ _ _ _ _ _ _ _ _ _ _, _ /\ _ => idtac | forall _ _ _ _ _ _ _ _ _ _ _ _, _ <-> _ => idtac | forall _ _ _ _ _ _ _ _ _ _ _ _ _, _ => 
  match P with | forall _ _ _ _ _ _ _ _ _ _ _ _ _, _ /\ _ => idtac | forall _ _ _ _ _ _ _ _ _ _ _ _ _, _ <-> _ => idtac | forall _ _ _ _ _ _ _ _ _ _ _ _ _ _, _ => 
  match P with | forall _ _ _ _ _ _ _ _ _ _ _ _ _ _, _ /\ _ => idtac | forall _ _ _ _ _ _ _ _ _ _ _ _ _ _, _ <-> _ => idtac | forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, _ => 
  match P with | forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, _ /\ _ => idtac | forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, _ <-> _ => idtac | forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, _ => 
  match P with | forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, _ /\ _ => idtac | forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, _ <-> _ => idtac | forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, _ => 
  match P with | forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, _ /\ _ => idtac | forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, _ <-> _ => idtac | forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, _ => 
  match P with | forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, _ /\ _ => idtac | forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, _ <-> _ => idtac | forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, _ => 
  match P with | forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, _ /\ _ => idtac | forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, _ <-> _ => idtac | forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, _ => 
  match P with | forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, _ /\ _ => idtac | forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, _ <-> _ => idtac
  end end end end end end end end end end end end end end end end end end end end end.

Ltac hdes := 
  repeat match goal with | H : ?P |- _ => hdesF P; hdesHP H P end; 
  unfold __HID__ in *.

Ltac rdes H := red in H; des.
Ltac rrdes H := repeat red in H; des.
Ltac rhdes H := red in H; hdes.
Ltac rrhdes H := repeat red in H; hdes.

Ltac dup tac H := let X := fresh "_X_" in assert (X := H); tac X.

Ltac clarassoc := clarsimp; autorewrite with vlib vlibA in *; try done. 

Ltac vlib__hacksimp1 :=
   clarsimp;
   match goal with
     | H: _ |- _ => solve [rewrite H; clear H; clarsimp
                         |rewrite <- H; clear H; clarsimp]
     | _ => solve [f_equal; clarsimp]
   end.

Ltac hacksimp :=
   clarsimp;
   try match goal with
   | H: _ |- _ => solve [rewrite H; clear H; clarsimp
                              |rewrite <- H; clear H; clarsimp]
   | |- context[if ?p then _ else _] => solve [destruct p; vlib__hacksimp1]
   | _ => solve [f_equal; clarsimp]
   end.

(* ************************************************************************** *)
(** * Delineating cases in proofs *)
(* ************************************************************************** *)

(** Named case tactics (taken from Libtactics) *)

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move x at top
  | assert_eq x name
  | fail 1 "because we are working on a different case." ].

Ltac Case name := Case_aux case name.
Ltac SCase name := Case_aux subcase name.
Ltac SSCase name := Case_aux subsubcase name.
Ltac SSSCase name := Case_aux subsubsubcase name.
Ltac SSSSCase name := Case_aux subsubsubsubcase name.

(** Lightweight case tactics (without names) *)

Tactic Notation "-" tactic(c) :=
  first [
    assert (WithinCaseM := True); move WithinCaseM at top
  | fail 1 "because we are working on a different case." ]; c.

Tactic Notation "+" tactic(c) :=
  first [
    assert (WithinCaseP := True); move WithinCaseP at top
  | fail 1 "because we are working on a different case." ]; c.

Tactic Notation "*" tactic(c) :=
  first [
    assert (WithinCaseS := True); move WithinCaseS at top
  | fail 1 "because we are working on a different case." ]; c.

Tactic Notation ":" tactic(c) :=
  first [
    assert (WithinCaseC := True); move WithinCaseC at top
  | fail 1 "because we are working on a different case." ]; c.

(* ************************************************************************** *)
(** * Exploiting a hypothesis *)
(* ************************************************************************** *)

(** Exploit an assumption (adapted from CompCert). *)

Ltac exploit x :=
    refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _) _)
 || refine ((fun x y => y x) (x _ _) _)
 || refine ((fun x y => y x) (x _) _).

(* When 'exploit x' generates too many sub goals, try 'hexploit x' *)

Lemma mp: forall P Q: Type, P -> (P -> Q) -> Q.
Proof. intuition. Defined.

Lemma mp': forall P Q : Type, (P -> Q) -> P -> Q.
Proof. intuition. Qed.

Ltac hexploit x := eapply mp; [eapply x|].

(* set_prop N T A performs 'assert (A : P); [|set (N := T A)]' when T is a term of type (P -> _) *)

Ltac set_prop N T A := 
  let b := fresh in let ty := type of T in
  match ty with (forall (_:?P), _) => assert (A: P); [|set (N := T A)] end.

(* ************************************************************************** *)
(** * Induction tactics *)
(* ************************************************************************** *)

Tactic Notation "induction" "[" ident_list(y) "]" ident(x)  :=
  first [ try (intros until x); revert y; induction x
        | red; try (intros until x); revert y; induction x ].

Tactic Notation "induction" "[" ident_list(y) "]" ident(x) "[" ident(z) "]"  :=
  first [ try (intros until x); revert y; induction x; destruct z
        | red; try (intros until x); revert y; induction x; destruct z ].

(** Versions with hacksimp *)

Tactic Notation "induct" ident(x) := induction x; hacksimp.

Tactic Notation "induct" ident(x) "[" ident(z) "]" := 
  induction x; destruct z; hacksimp.

Tactic Notation "induct" "[" ident_list(y) "]" ident(x)  :=
  first [ try (intros until x); revert y; induction x; hacksimp
        | red; try (intros until x); revert y; induction x; hacksimp ].

Tactic Notation "induct" "[" ident_list(y) "]" ident(x) "[" ident(z) "]"  :=
  first [ try (intros until x); revert y; induction x; destruct z; hacksimp
        | red; try (intros until x); revert y; induction x; destruct z; hacksimp ].

Tactic Notation "edestructs" ident(a) := 
  (edestruct a).
Tactic Notation "edestructs" ident(a) ident(b) := 
  (edestruct a; edestruct b).
Tactic Notation "edestructs" ident(a) ident(b) ident(c) := 
  (edestruct a; edestructs b c).
Tactic Notation "edestructs" ident(a) ident(b) ident(c) ident(d) := 
  (edestruct a; edestructs b c d).
Tactic Notation "edestructs" ident(a) ident(b) ident(c) ident(d) ident(e) := 
  (edestruct a; edestructs b c d e).
Tactic Notation "edestructs" ident(a) ident(b) ident(c) ident(d) ident(e) ident(f) :=
  (edestruct a; edestructs b c d e f).
Tactic Notation "edestructs" ident(a) ident(b) ident(c) ident(d) ident(e) ident(f) ident(g) := 
  (edestruct a; edestructs b c d e f g).
Tactic Notation "edestructs" ident(a) ident(b) ident(c) ident(d) ident(e) ident(f) ident(g) ident(h) :=
  (edestruct a; edestructs b c d e f g h).
Tactic Notation "edestructs" ident(a) ident(b) ident(c) ident(d) ident(e) ident(f) ident(g) ident(h) ident(i) := 
  (edestruct a; edestructs b c d e f g h i).
Tactic Notation "edestructs" ident(a) ident(b) ident(c) ident(d) ident(e) ident(f) ident(g) ident(h) ident(i) ident(j) := 
  (edestruct a; edestructs b c d e f g h i j).

Tactic Notation "destructs" ident(a) :=
  (destruct a).
Tactic Notation "destructs" ident(a) ident(b) := 
  (destruct a; destruct b).
Tactic Notation "destructs" ident(a) ident(b) ident(c) := 
  (destruct a; destructs b c).
Tactic Notation "destructs" ident(a) ident(b) ident(c) ident(d) :=
  (destruct a; destructs b c d).
Tactic Notation "destructs" ident(a) ident(b) ident(c) ident(d) ident(e) :=
  (destruct a; destructs b c d e).
Tactic Notation "destructs" ident(a) ident(b) ident(c) ident(d) ident(e) ident(f) :=
  (destruct a; destructs b c d e f).
Tactic Notation "destructs" ident(a) ident(b) ident(c) ident(d) ident(e) ident(f) ident(g) :=
  (destruct a; destructs b c d e f g).
Tactic Notation "destructs" ident(a) ident(b) ident(c) ident(d) ident(e) ident(f) ident(g) ident(h) := 
  (destruct a; destructs b c d e f g h).
Tactic Notation "destructs" ident(a) ident(b) ident(c) ident(d) ident(e) ident(f) ident(g) ident(h) ident(i) := 
  (destruct a; destructs b c d e f g h i).
Tactic Notation "destructs" ident(a) ident(b) ident(c) ident(d) ident(e) ident(f) ident(g) ident(h) ident(i) ident(j) := 
  (destruct a; destructs b c d e f g h i j).

Tactic Notation "depdes" ident(_something_which_shold_not_occur_in_the_goal_) :=
  (let _x_ := type of _something_which_shold_not_occur_in_the_goal_ 
   in dependent destruction _something_which_shold_not_occur_in_the_goal_).
Tactic Notation "depdes" ident(a) ident(b) := 
  (depdes a; depdes b).
Tactic Notation "depdes" ident(a) ident(b) ident(c) := 
  (depdes a; depdes b c).
Tactic Notation "depdes" ident(a) ident(b) ident(c) ident(d) :=
  (depdes a; depdes b c d).
Tactic Notation "depdes" ident(a) ident(b) ident(c) ident(d) ident(e) :=
  (depdes a; depdes b c d e).
Tactic Notation "depdes" ident(a) ident(b) ident(c) ident(d) ident(e) ident(f) :=
  (depdes a; depdes b c d e f).
Tactic Notation "depdes" ident(a) ident(b) ident(c) ident(d) ident(e) ident(f) ident(g) :=
  (depdes a; depdes b c d e f g).
Tactic Notation "depdes" ident(a) ident(b) ident(c) ident(d) ident(e) ident(f) ident(g) ident(h) := 
  (depdes a; depdes b c d e f g h).
Tactic Notation "depdes" ident(a) ident(b) ident(c) ident(d) ident(e) ident(f) ident(g) ident(h) ident(i) := 
  (depdes a; depdes b c d e f g h i).
Tactic Notation "depdes" ident(a) ident(b) ident(c) ident(d) ident(e) ident(f) ident(g) ident(h) ident(i) ident(j) := 
  (depdes a; depdes b c d e f g h i j).

Tactic Notation "depgen" ident(x) := generalize dependent x.

(* eappleft, eappright *)

Ltac eappleft H :=
  let X := fresh "__lem__" in let X1 := fresh "__lem__" in let X2 := fresh "__lem__" in
  assert (X:= H); let P := type of X in hdesHi X P X1 X2;
  eapply X1; clear X1 X2.

Ltac eappright H :=
  let X := fresh "__lem__" in let X1 := fresh "__lem__" in let X2 := fresh "__lem__" in
  assert (X:= H); let P := type of X in hdesHi X P X1 X2;
  eapply X2; clear X1 X2.

(* guard for simpl *)

(* for Coq8.4 *)

Definition __guard__ A (a : A) : A := a.
Definition __GUARD__ A (a : A) : A := a.
(* Arguments __guard__ A a : simpl never. *)
(* Arguments __GUARD__ A a : simpl never. *)

Tactic Notation "guard" constr(t) "in" hyp(H) := fold (__guard__ t) in H.
Tactic Notation "guard" "in" hyp(H) := let t := type of H in guard t in H.
Tactic Notation "sguard" constr(t) "in" hyp(H) := fold (__GUARD__ t) in H.
Tactic Notation "sguard" "in" hyp(H) := let t := type of H in sguard t in H.

Ltac unguard := unfold __guard__ in *.
Ltac unsguard H := unfold __GUARD__ in H.

Ltac splits :=
  unnw; intros;
  repeat match goal with 
  | [ |- _ /\ _ ] => split
  end.
Ltac esplits :=
  unnw; intros;
  repeat match goal with 
  | [ |- @ex _ _ ] => eexists
  | [ |- _ /\ _ ] => split
  | [ |- @sig _ _ ] => eexists
  | [ |- @sigT _ _ ] => eexists
  | [ |- @prod _  _ ] => split

  end.

Tactic Notation "replace_all" constr(e) := repeat (
  let X := fresh in assert (X: e) by (clarify; eauto; done); 
  first [rewrite !X | setoid_rewrite X]; clear X).

Lemma all_conj_dist: forall A (P Q: A -> Prop), 
  (forall a, P a /\ Q a) -> (forall a, P a) /\ (forall a, Q a).
Proof. intros; hdes; eauto. Qed.

(* extensionalities *)

Tactic Notation "extensionalities" :=
  repeat let x := fresh in extensionality x.
Tactic Notation "extensionalities" ident(a) :=
  (extensionality a).
Tactic Notation "extensionalities" ident(a) ident(b) :=
  (extensionality a; extensionality b).
Tactic Notation "extensionalities" ident(a) ident(b) ident(c) :=
  (extensionality a; extensionalities b c).
Tactic Notation "extensionalities" ident(a) ident(b) ident(c) ident(d) :=
  (extensionality a; extensionalities b c d).
Tactic Notation "extensionalities" ident(a) ident(b) ident(c) ident(d) ident(e) :=
  (extensionality a; extensionalities b c d e).
Tactic Notation "extensionalities" ident(a) ident(b) ident(c) ident(d) ident(e) ident(f) :=
  (extensionality a; extensionalities b c d e f).

(* short for common tactics *)

Tactic Notation "inst" := instantiate.
Tactic Notation "econs" := econstructor.
Tactic Notation "econs" int_or_var(x) := econstructor x.
Tactic Notation "i" := intros.
Tactic Notation "ii" := repeat intro.
Tactic Notation "s" := simpl.
Tactic Notation "s" ident(a) := simpl a.
Tactic Notation "s" constr(t) := simpl t.
Tactic Notation "s" "in" hyp(H) := simpl in H.
Tactic Notation "ss" := simpls.
Tactic Notation "r" := red.
Tactic Notation "r" "in" hyp(H) := red in H.
Tactic Notation "rr" := repeat red.
Tactic Notation "rr" "in" hyp(H) := repeat red in H.

(* running a tactic selectively on subgoals *)

Definition __mark__ A (a : A) : A := a.

Tactic Notation "M" := 
  match goal with [|-?G] => fold (__mark__ G) end.

Tactic Notation "Mdo" tactic(tac) :=
  first [ try match goal with [|- __mark__ _ ] => fail 2 end | unfold __mark__; tac ].

Tactic Notation "Mskip" tactic(tac) :=
  first [ match goal with [|- __mark__ _ ] => unfold __mark__ end | tac ].

Tactic Notation "Mfirst" tactic(main) ";;" tactic(post) := 
   main; (Mdo (post; M)); (Mskip post).

(* revert until *)

Ltac on_last_hyp tac :=
  match goal with [ H : _ |- _ ] => first [ tac H | fail 1 ] end.

Ltac revert_until id :=
  on_last_hyp ltac:(fun id' =>
    match id' with
      | id => idtac
      | _ => revert id' ; revert_until id
    end).

Ltac eautoi := eauto; instantiate; eauto.

Open Scope string_scope.
Open Scope list_scope.

Fixpoint beq_str (s1 s2: string) : bool := 
  match s1, s2 with
  | "", "" => true
  | String a s1', String b s2' => if Ascii.ascii_dec a b then beq_str s1' s2' else false
  | _, _ => false
  end.

Ltac uf := (autounfold with * in *).

Tactic Notation "patout" constr(z) "in" hyp(a) :=
  pattern z in a; match goal with [a:=?f z|-_] => unfold a; clear a; set (a:=f) end.

Ltac check_equal H1 H2 := match H1 with | H2 => idtac end.

Ltac clear_upto H :=
  repeat (match goal with [Hcrr : _ |- _ ] => first [ check_equal Hcrr H; fail 2
 | clear Hcrr ] end).

Definition _Evar_Gil_ (A:Type) (x:A) := x.

Tactic Notation "hide_evar" int_or_var(n) := let QQ := fresh "QQ" in
  hget_evar n; intro;
  lazymatch goal with [ H := ?X |- _] => 
    set (QQ := X) in *; fold (_Evar_Gil_ X) in QQ; clear H 
  end.

Ltac hide_evars := repeat (hide_evar 1).

Ltac show_evars := repeat (match goal with [ H := @_Evar_Gil_ _ _ |- _ ] => unfold
 _Evar_Gil_ in H; unfold H in *; clear H end).

Ltac revert1 := match goal with [H: _|-_] => revert H end.

Lemma eqimpl: forall P Q : Prop, P = Q -> P -> Q. 
Proof. by i; subst; auto. Qed.
