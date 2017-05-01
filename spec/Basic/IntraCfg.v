(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** * Syntax of Program.  *)

Set Implicit Arguments.

Require Import ZArith OrderedType OrderedTypeEx.
Require Import hpattern vgtac.
Require Import VocabA DFSetAVL DFMapAVL TStr Syn.
Require IntraNode.

Module NodeMap := FMapAVL'.Make IntraNode.

Module NodeSet := FSetAVL'.Make IntraNode.

Record t :=
  { args : list vid_t
  ; cmds : NodeMap.t cmd
  ; succ : NodeMap.t NodeSet.t
  ; pred : NodeMap.t NodeSet.t
  ; nodes : NodeSet.t
  }.

Definition get_cmd (cfg : t) (node : IntraNode.t) : option cmd :=
  NodeMap.find node (cmds cfg).

Lemma get_cmd_mor (cfg : t) :
  Proper (IntraNode.eq ==> Logic.eq) (get_cmd cfg).
Proof.
unfold get_cmd, Proper, respectful; i.
by apply NodeMap.P.F.find_m_Proper.
Qed.

Definition is_call_node (cfg : t) (node : IntraNode.t) : bool :=
  match get_cmd cfg node with
    | Some (Ccall _ _ _ _) => true
    | _ => false
  end.

Lemma is_call_node_mor (cfg : t) :
  Proper (IntraNode.eq ==> Logic.eq) (is_call_node cfg).
Proof.
unfold is_call_node, Proper, respectful; intros n n' Hn.
by rewrite (get_cmd_mor cfg Hn).
Qed.

Definition returnof (cfg : t) (call_node : IntraNode.t) : option IntraNode.t :=
  match NodeMap.find call_node (succ cfg) with
    | Some succs => NodeSet.choose succs
    | None => None
  end.

Definition callof (cfg : t) (ret_node : IntraNode.t) : option IntraNode.t :=
  match NodeMap.find ret_node (pred cfg) with
    | Some preds =>
      match NodeSet.elements preds with
        | cons pred_node nil =>
          if is_call_node cfg pred_node then Some pred_node else None
        | _ => None
      end
    | None => None
  end.

Definition is_return_node (cfg : t) (node : IntraNode.t) : bool :=
  match callof cfg node with
    | Some _ => true
    | None => false
  end.

Definition remove_node_pred node m :=
  let m := NodeMap.remove node m in
  NodeMap.map (NodeSet.remove node) m.

Definition remove_node (node : IntraNode.t) (g : t) : t :=
  {| args := args g
   ; cmds := NodeMap.remove node (cmds g)
   ; succ := NodeMap.remove node (succ g)
   ; pred := remove_node_pred node (pred g)
   ; nodes := NodeSet.remove node (nodes g)
  |}.

Inductive is_succ (cfg : t) : IntraNode.t -> IntraNode.t -> Prop :=
| is_succ_intro :
    forall n n' succs
           (Hsuccs : NodeMap.MapsTo n succs (succ cfg))
           (Hn' : NodeSet.In n' succs),
      is_succ cfg n n'.

Definition wf_pred_succ (cfg : t) :=
  forall from to succs preds
         (Hsuccs: NodeMap.MapsTo from succs (succ cfg))
         (Hto: NodeSet.In to succs)
         (Hpred: NodeMap.MapsTo to preds (pred cfg)),
    NodeSet.In from preds.

Lemma returnof_1 :
  forall g cn cn' retn (Hwf_g : wf_pred_succ g)
         (Hretn : Some retn = returnof g cn) (Hcall : Some cn' = callof g retn),
    IntraNode.eq cn cn'.
Proof.
unfold returnof, callof. i. repeat dest_trivial_match.
remember (NodeSet.elements t0) as elts_t.
destruct elts_t; [discriminate|destruct elts_t; [|discriminate]].
dest_if. inversion Hcall; subst. clear Hcall.
symmetry in Heqcond0. apply NodeMap.P.F.find_mapsto_iff in Heqcond0.
symmetry in Heqcond. apply NodeMap.P.F.find_mapsto_iff in Heqcond.
symmetry in Hretn. apply NodeSet.choose_1 in Hretn.
assert (Hin := Hwf_g _ _ _ _ Heqcond0 Hretn Heqcond).
assert (HinA := NodeSet.elements_1 Hin).
rewrite <- Heqelts_t in HinA.
inversion HinA; [|by inversion H0].
by subst.
Qed.
