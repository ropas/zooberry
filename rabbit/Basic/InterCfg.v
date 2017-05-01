(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** * Syntax of Program.  *)

Set Implicit Arguments.

Require Import ZArith OrderedType OrderedTypeEx.
Require Import hpattern vgtac VocabA DFSetAVL DFMapAVL TStr Syn
        DNat.
Require IntraCfg InterNode.

Module Pid := String_as_OT.

Module PidMap := FMapAVL'.Make Pid.
Module PidSet := FSetAVL'.Make Pid.
Module NodeMap := FMapAVL'.Make InterNode.
Module NodeSet := FSetAVL'.Make InterNode.

Record t :=
  { cfgs : PidMap.t IntraCfg.t
  ; succ : NodeMap.t NodeSet.t
  ; pred : NodeMap.t NodeSet.t
  ; nodes : NodeSet.t
  }.

Definition get_cmd (g : t) (node : InterNode.t) : option cmd :=
  let pid := InterNode.get_pid node in
  let cfg_node := InterNode.get_node node in
  match PidMap.find pid (cfgs g) with
    | None => None
    | Some cfg => IntraCfg.get_cmd cfg cfg_node
  end.

Definition has_cmd (g : t) (n : InterNode.t) : bool :=
match get_cmd g n with
  | None => false
  | Some _ => true
end.

Definition get_args (g : t) (pid : pid_t) : option (list vid_t) :=
  match PidMap.find pid (cfgs g) with
    | None => None
    | Some cfg => Some (IntraCfg.args cfg)
  end.

Definition is_undef (pid : pid_t) (g : t) : bool :=
  negb (PidMap.mem pid (cfgs g)).

Definition is_call_node (g : t) (node : InterNode.t) : bool :=
  let pid := InterNode.get_pid node in
  match PidMap.find pid (cfgs g) with
    | Some cfg => IntraCfg.is_call_node cfg (InterNode.get_node node)
    | None => false
  end.

Definition is_return_node (g : t) (node : InterNode.t) : bool :=
  let pid := InterNode.get_pid node in
  match PidMap.find pid (cfgs g) with
    | Some cfg => IntraCfg.is_return_node cfg (InterNode.get_node node)
    | None => false
  end.

Definition is_unreachable_return (g : t) (n : InterNode.t) :=
  (is_return_node g n
   && match NodeMap.find n (pred g) with
        | None => true
        | Some preds =>
          if Nat.eqb (NodeSet.cardinal preds) 0 then true else false
      end) %bool.

Definition pidsof (g : t) : list pid_t :=
  PidMap.fold (fun pid _ => cons pid) (cfgs g) nil.

Definition returnof (g : t) (node : InterNode.t) : option InterNode.t :=
  let f := InterNode.get_pid node in
  match PidMap.find f (cfgs g) with
  | Some cfg =>
    match IntraCfg.returnof cfg (InterNode.get_node node) with
    | Some return_node => Some (f, return_node)
    | None => None
    end
  | None => None
  end.

Lemma returnof_same_pid :
  forall icfg n n' (Hreturnof : Some n' = returnof icfg n),
    InterNode.get_pid n = InterNode.get_pid n'.
Proof.
unfold returnof; i.
repeat match goal with
  | [H : Some _ = match ?cond with Some _ => _ | None => _ end |- _ ] =>
    destruct cond; [|congruence]
end.
destruct n, n'; s; by inversion Hreturnof.
Qed.

Definition callof (g : t) (node : InterNode.t) : option InterNode.t :=
  let f := InterNode.get_pid node in
  match PidMap.find f (cfgs g) with
  | Some cfg =>
    match IntraCfg.callof cfg (InterNode.get_node node) with
    | Some call_node => Some (f, call_node)
    | None => None
    end
  | None => None
  end.

Definition callnodesof (g : t) : NodeSet.t :=
  NodeSet.filter (is_call_node g) (nodes g).

Definition is_f (f : pid_t) (g : pid_t) : bool :=
  if Pid.eq_dec f g then true else false.

Definition is_node_of_f (f : pid_t) (n : InterNode.t) : bool :=
  is_f f (InterNode.get_pid n).

Definition is_same_node (n1 : InterNode.t) (n2 : InterNode.t) : bool :=
  if InterNode.eq_dec n1 n2 then true else false.

Definition nodeset_remove (cond : InterNode.t -> bool) (s : NodeSet.t)
: NodeSet.t :=
  NodeSet.filter (fun n => negb (cond n)) s.

Definition nodemap_remove (cond : InterNode.t -> bool)
           (s : NodeMap.t NodeSet.t) : NodeMap.t NodeSet.t:=
  let remove1 k v acc :=
    if cond k then acc else NodeMap.add k (nodeset_remove cond v) acc in
  NodeMap.fold remove1 s (NodeMap.empty _).

Definition remove_function (f : pid_t) (g : t) : t :=
  {| cfgs := PidMap.remove f (cfgs g)
   ; succ := nodemap_remove (is_node_of_f f) (succ g)
   ; pred := nodemap_remove (is_node_of_f f) (pred g)
   ; nodes := nodeset_remove (is_node_of_f f) (nodes g)
  |}.

Definition cfgs_remove_node (node : InterNode.t) (cfgs : PidMap.t IntraCfg.t)
  : PidMap.t IntraCfg.t :=
  let pid := InterNode.get_pid node in
  match PidMap.find pid cfgs with
    | Some cfg =>
      PidMap.add pid (IntraCfg.remove_node (InterNode.get_node node) cfg) cfgs
    | None => cfgs
  end.

Definition remove_node (node : InterNode.t) (g : t) : t :=
  {| cfgs := cfgs_remove_node node (cfgs g)
   ; succ := nodemap_remove (is_same_node node) (succ g)
   ; pred := nodemap_remove (is_same_node node) (pred g)
   ; nodes := NodeSet.remove node (nodes g)
  |}.

Inductive is_succ (g : t) : InterNode.t -> InterNode.t -> Prop :=
| is_succ_intro :
    forall n n' succs
           (Hsuccs : NodeMap.MapsTo n succs (succ g))
           (Hn' : NodeSet.In n' succs),
      is_succ g n n'.

Inductive reachable (g : t) : pid_t -> pid_t -> Prop :=
| reachable_self : forall p, reachable g p p
| reachable_other :
    forall p n q r
           (Hinter: is_succ g (p, n) (q, IntraNode.Entry))
           (Hr: reachable g q r),
      reachable g p r.

Inductive reachables (g : t) : list InterNode.t -> pid_t -> Prop :=
| reachables_nil : forall pid, reachables g nil pid
| reachables_cons :
    forall n ns pid
           (Hn: reachable g (InterNode.get_pid n) pid)
           (Hns: reachables g ns pid),
      reachables g (n :: ns) pid.

Definition wf_callof_returnof (g : t) :=
  forall calln retn,
    Some retn = returnof g calln <-> Some calln = callof g retn.

Definition wf_call_ret_edge_1 (g : t) :=
  forall cn retn callee
         (Hcall: is_succ g cn (callee, IntraNode.Entry))
         (Hret: Some retn = returnof g cn),
    is_succ g (callee, IntraNode.Exit) retn.

Definition wf_call_ret_edge_2 (g : t) :=
  forall cn retn callee
         (Hexit : is_succ g (callee, IntraNode.Exit) retn)
         (Hret : Some cn = callof g retn),
    is_succ g cn (callee, IntraNode.Entry).

Definition wf_call_node_1 (g : t) :=
  forall callee, is_call_node g (callee, IntraNode.Exit) = false.

Definition wf_call_node_2 (g : t) :=
  forall cn callee (Hcall: is_succ g cn (callee, IntraNode.Entry)),
    InterNode.is_exit_node cn = false.

Definition wf_intra_pred_succ (g : t) :=
  forall f cfg (Hcfg: PidMap.MapsTo f cfg (cfgs g)),
    IntraCfg.wf_pred_succ cfg.

Lemma returnof_1 :
  forall g cn cn' retn
         (Hwf_g : wf_intra_pred_succ g)
         (Hretn : Some retn = returnof g cn)
         (Hcall : Some cn' = callof g retn),
    InterNode.eq cn cn'.
Proof.
unfold returnof, callof. i. repeat dest_trivial_match.
destruct cn as [f n], retn as [retf' retn']. simpl in *.
inversion Hretn; subst; clear Hretn.
inversion Hcall; subst; clear Hcall.
rewrite <- Heqcond1 in Heqcond. inversion Heqcond; subst; clear Heqcond.
split; [by auto|s].
unfold wf_intra_pred_succ in Hwf_g.
symmetry in Heqcond1. apply PidMap.P.F.find_mapsto_iff in Heqcond1.
by apply (IntraCfg.returnof_1 _ (Hwf_g _ _ Heqcond1) Heqcond2 Heqcond0).
Qed.

Definition node_in_icfg (g : t) (n : InterNode.t) := NodeSet.In n (nodes g).
