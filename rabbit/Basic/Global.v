(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** * Syntax of Program.  *)

Set Implicit Arguments.

Require Import ZArith OrderedType OrderedTypeEx.
Require Import hpattern vgtac.
Require Import VocabA DFSetAVL DFMapAVL TStr.
Require Import Syn IntraCfg InterCfg.
Require Import DLat.

Module Callgraph.

Record t : Type :=
  { node_calls : NodeMap.t PidSet.t
  ; calls : PidMap.t PidSet.t
  ; trans_calls : PidMap.t PidSet.t
  }.

Definition empty :t :=
  {| node_calls := NodeMap.empty PidSet.t
   ; calls := PidMap.empty PidSet.t
   ; trans_calls := PidMap.empty PidSet.t |}.

Definition is_rec (p : pid_t) (cg : t) : bool :=
  match PidMap.find p (trans_calls cg) with
    | None => false
    | Some fs => PidSet.mem p fs
  end.

Lemma is_rec_mor : Proper (Pid.eq ==> eq ==> eq) is_rec.
Proof.
unfold is_rec; intros f1 f2 Hf g1 g2 Hg; subst.
rewrite PidMap.P.F.find_o with (y:=f2); [|by auto].
destruct (PidMap.find (elt:=PidSet.t) f2 (trans_calls g2)); [|by auto].
by apply PidSet.SF.mem_b.
Qed.

Definition node_calls_remove_function (f : pid_t)
  (node_calls : NodeMap.t PidSet.t) : NodeMap.t PidSet.t :=
  let is_not_f node :=
    if Pid.eq_dec f (InterNode.get_pid node) then false else true in
  NodeMap.filter is_not_f node_calls.

Definition calls_remove_function (f : pid_t) (calls : PidMap.t PidSet.t)
  : PidMap.t PidSet.t :=
  let is_not_f g := if Pid.eq_dec f g then false else true in
  PidMap.filter is_not_f calls.

Definition remove_function (f : pid_t) (cg : t) : t :=
  {| node_calls := node_calls_remove_function f (node_calls cg)
   ; calls := calls_remove_function f (calls cg)
   ; trans_calls := calls_remove_function f (trans_calls cg)
  |}.

Definition remove_node (node : InterNode.t) (cg : t) : t :=
  {| node_calls := NodeMap.remove node (node_calls cg)
   ; calls := calls cg
   ; trans_calls := trans_calls cg
  |}.

End Callgraph.

Module G.

Record t : Type :=
  { icfg : InterCfg.t
  ; callgraph : Callgraph.t
  }.

Definition is_undef (f : pid_t) (g : t) : bool := InterCfg.is_undef f (icfg g).

Definition is_undef_e (e : exp) (g : t) : option pid_t :=
  match e with
  | Lval (lval_intro (VarLhost f _) NoOffset _) _ =>
    if is_undef f g then Some f else None
  | _ => None
  end.

Definition is_call_node (p : t) (node : InterNode.t) : bool :=
  InterCfg.is_call_node (icfg p) node.

Definition is_exit_node (node : InterNode.t) : bool :=
  InterNode.is_exit_node node.

Definition is_rec (f : pid_t) (g : t) : bool :=
  Callgraph.is_rec f (callgraph g).

Lemma is_rec_mor : Proper (Pid.eq ==> eq ==> eq) is_rec.
Proof.
intros f1 f2 Hf g1 g2 Hg; subst.
by apply Callgraph.is_rec_mor.
Qed.

Definition get_callees (g : t) (node : InterNode.t) : PidSet.t :=
  let opt_callees := NodeMap.find node (Callgraph.node_calls (callgraph g)) in
  default PidSet.empty opt_callees.

Definition remove_function (f : pid_t) (g : t) : t :=
  {| icfg := InterCfg.remove_function f (icfg g)
   ; callgraph := Callgraph.remove_function f (callgraph g)
  |}.

Definition remove_node (node : InterNode.t) (g : t) : t :=
  {| icfg := InterCfg.remove_node node (icfg g)
   ; callgraph := Callgraph.remove_node node (callgraph g)
  |}.

Definition get_args (f : pid_t) (g : t) : option (list vid_t) :=
  InterCfg.get_args (icfg g) f.

(*
Well-formedness of the input graph

1. callof/returnof are consistent
2-3. call edge/return edge are consistent
4. impossible: call node -> exit node
5. impossible: exit node -> entry node
6. IntraCfg's preds/succs are consistent
*)

Definition wf_callof_returnof (g : t) := InterCfg.wf_callof_returnof (icfg g).

Definition wf_call_ret_edge_1 (g : t) := InterCfg.wf_call_ret_edge_1 (icfg g).

Definition wf_call_ret_edge_2 (g : t) := InterCfg.wf_call_ret_edge_2 (icfg g).

Definition wf_call_node_1 (g : t) := InterCfg.wf_call_node_1 (icfg g).

Definition wf_call_node_2 (g : t) := InterCfg.wf_call_node_2 (icfg g).

Definition wf_intra_pred_succ g := InterCfg.wf_intra_pred_succ (icfg g).

Definition wf (g : t) :=
  wf_callof_returnof g
  /\ wf_call_ret_edge_1 g
  /\ wf_call_ret_edge_2 g
  /\ wf_call_node_1 g
  /\ wf_call_node_2 g
  /\ wf_intra_pred_succ g.

Definition node_in_g (g : t) (n : InterNode.t) :=
  InterCfg.node_in_icfg (G.icfg g) n.

Inductive nodes_in_g (g : t) : list InterNode.t -> Prop :=
| nodes_in_g_nil : nodes_in_g g nil
| nodes_in_g_cons :
    forall n ns' (Hn: node_in_g g n) (Hns': nodes_in_g g ns'),
      nodes_in_g g (n :: ns').

End G.
