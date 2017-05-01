(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
Set Implicit Arguments.

Require Import Setoid.
Require Import Morphisms.
Require Import Monad hpattern vgtac VocabA Syn Global DLat
        DPow DMap DPos UserInputType.
Require DMem Access.

Definition fail_cmd_mem (f : pid_t) (node : IntraNode.t) := false.
Extract Constant fail_cmd_mem =>
"fun f node ->
prerr_string ""fail on "";
PPVocab.pp_string PPIL.print_inter_node (f, node);
prerr_endline "" by unsound abstract memory"";
false".

Definition fail_access (f : pid_t) (node : IntraNode.t) := false.
Extract Constant fail_access =>
"fun f node ->
prerr_string ""fail on "";
PPVocab.pp_string PPIL.print_inter_node (f, node);
prerr_endline "" by unsound accessibility"";
false".

Definition fail_intra_edge (f : pid_t) (from_node to_node : IntraNode.t) :=
  false.
Extract Constant fail_intra_edge =>
"fun f from_node to_node ->
prerr_string ""fail on edge "";
PPVocab.pp_string PPIL.print_inter_node (f, from_node);
prerr_string ""->"";
PPVocab.pp_endline PPIL.print_inter_node (f, to_node);
false".

Definition fail_inter_edge (from_node to_node : InterNode.t) := false.
Extract Constant fail_inter_edge =>
"fun from_node to_node ->
prerr_string ""fail on edge "";
PPVocab.pp_string PPIL.print_inter_node from_node;
prerr_string ""->"";
PPVocab.pp_endline PPIL.print_inter_node to_node;
false".

Definition fail_inter_acc (from_node to_node : InterNode.t) := false.
Extract Constant fail_inter_acc =>
"fun from_node to_node ->
prerr_string ""fail on inter acc "";
PPVocab.pp_string PPIL.print_inter_node from_node;
prerr_string ""->"";
PPVocab.pp_endline PPIL.print_inter_node to_node;
false".

Definition fail_inter_edge_invalid (from_node to_node : InterNode.t) := false.
Extract Constant fail_inter_edge_invalid =>
"fun from_node to_node ->
prerr_string ""fail on edge "";
PPVocab.pp_string PPIL.print_inter_node from_node;
prerr_string ""->"";
PPVocab.pp_string PPIL.print_inter_node to_node;
prerr_endline "" by cmd invalidity"";
false".

Definition fail_inter_edge_no_callof (from_node to_node : InterNode.t) := false.
Extract Constant fail_inter_edge_no_callof =>
"fun from_node to_node ->
prerr_string ""fail on edge "";
PPVocab.pp_string PPIL.print_inter_node from_node;
prerr_string ""->"";
PPVocab.pp_string PPIL.print_inter_node to_node;
prerr_endline "" by call node not found"";
false".

Definition fail_dens_inputof (node : InterNode.t) := false.
Extract Constant fail_dens_inputof =>
"fun node ->
prerr_string ""fail on node "";
PPVocab.pp_string PPIL.print_inter_node node;
prerr_endline "" by invalid densification of inputof."";
false".


Module Make (Import I : INPUT).

(* Disjoin relation between memories and accessibilities. *)

Definition disjoint (m : Mem.t) (acc : Acc.t) : Prop :=
  forall l (Hl : PowLoc.mem l (Acc.accessof acc) = true),
    Val.eq (Mem.find l m) Val.bot.

Lemma disjoint_bot : forall acc, disjoint Mem.bot acc.
Proof. unfold disjoint; i. by apply Mem.empty_prop with (k:=l). Qed.

Lemma disjoint_join :
  forall m1 m2 acc (Hdis1: disjoint m1 acc) (Hdis2: disjoint m2 acc),
    disjoint (Mem.join m1 m2) acc.
Proof.
unfold disjoint; i. eapply Val.eq_trans; [by apply Mem.join_find|].
apply Val.le_antisym.
- apply Val.join_lub; apply Val.le_refl; [by apply Hdis1|by apply Hdis2].
- by apply Val.bot_prop.
Qed.

Lemma disjoint_le :
  forall m acc1 acc2 (Hle: Acc.le acc2 acc1) (Hdis: disjoint m acc1),
    disjoint m acc2.
Proof.
unfold disjoint. i.
apply Hdis.
eapply PowLoc.le_mem_true; [|by apply Hl].
by apply Acc.accessof_mor'.
Qed.

Lemma disjoint_mor :
  Proper (Mem.eq ==> Acc.eq ==> Basics.impl) disjoint.
Proof.
unfold disjoint. intros m1 m2 Hm a1 a2 Ha Hdis1. i.
eapply Val.eq_trans; [|apply Hdis1].
- apply Val.eq_sym, Mem.find_mor; [by apply Loc.eq_refl|by auto].
- rewrite <- Hl. apply PowLoc.mem_mor; [by apply Loc.eq_refl|].
  by apply Acc.accessof_mor.
Qed.

Lemma disjoint_left :
  forall m a1 a2 (Hdis : disjoint m (Acc.join a1 a2)), disjoint m a1.
Proof.
unfold disjoint; i.
apply Hdis. eapply Acc.le_mem_true; [|by apply Hl].
by apply Acc.join_left.
Qed.

Lemma disjoint_right :
  forall m a1 a2 (Hdis : disjoint m (Acc.join a1 a2)), disjoint m a2.
Proof.
unfold disjoint; i.
apply Hdis. eapply Acc.le_mem_true; [|by apply Hl].
by apply Acc.join_right.
Qed.

Lemma disjoint_mono :
  forall a1 a2 (Hle : Acc.le a1 a2) m (Hdis : disjoint m a2), disjoint m a1.
Proof.
i. intros l Hl1.
apply Hdis. eapply Acc.le_mem_true; [by apply Hle|]. by auto.
Qed.

(* Access map *)

Definition access_map := InterCfg.PidMap.t Acc.t.

Definition get_access (pid : pid_t) (m : access_map) : Acc.t :=
  default Acc.empty (InterCfg.PidMap.find pid m).

Definition get_def_access (pid : pid_t) (m : access_map) : PowLoc.t :=
  Acc.defof (get_access pid m).

Definition get_use_access (pid : pid_t) (m : access_map) : PowLoc.t :=
  Acc.useof (get_access pid m).

Definition get_all_access (pid : pid_t) (m : access_map) : PowLoc.t :=
  Acc.accessof (get_access pid m).

(* Validator *)

Section Validate.

Local Open Scope bool.

Variable g : G.t.

Variable access_map : access_map.

Variables orig_inputof orig_outputof : Table.t Mem.t.

Variables inputof outputof : Table.t Mem.t.

Definition icfg := G.icfg g.

(* [valid_cmd] validates the three conditions at the same time,
  because their processes are similar with regard to abstract memory
  calculation.

  - validity of output memories dangling on nodes
  - validity of access *)

Section IntraCfg.

Variable f : pid_t.

Variable cfg : IntraCfg.t.

Definition table_find n s := default Mem.bot (Table.find n s).

Definition valid_cmd (node : IntraNode.t) (cmd : cmd) : bool :=
  let i_m := table_find (f, node) inputof in
  let o_m := table_find (f, node) outputof in
  let access_f := get_access f access_map in
  let '(o_m', access_f') := run_access Strong g (f, node) cmd i_m in
  if Acc.le_dec access_f' access_f then
    if Mem.opt_le o_m' o_m then true else fail_cmd_mem f node
  else fail_access f node.

Definition valid_cmds :=
  IntraCfg.NodeMap.for_all print2 valid_cmd (IntraCfg.cmds cfg).

Definition valid_intra_edge (from_node to_node : IntraNode.t) : bool :=
  let from_m := table_find (f, from_node) outputof in
  let to_m := table_find (f, to_node) inputof in
  (* Edges from call nodes to return nodes are validated in
  valid_inter_edge. *)
  if IntraCfg.is_call_node cfg from_node then true else
  if Mem.opt_le from_m to_m then true else
    fail_intra_edge f from_node to_node.

Definition valid_intra_edges : bool :=
  let valid_intra_edges' from_node to_nodes :=
    IntraCfg.NodeSet.for_all (valid_intra_edge from_node) to_nodes in
  IntraCfg.NodeMap.for_all print2 valid_intra_edges' (IntraCfg.succ cfg).

Definition valid_cfg := valid_cmds && valid_intra_edges.

End IntraCfg.

Definition valid_cfgs :=
  InterCfg.PidMap.for_all print2 valid_cfg (InterCfg.cfgs icfg).

Definition valid_inter_edge (from_node to_node : InterNode.t) : bool :=
  let from_m := table_find from_node outputof in
  let to_m := table_find to_node inputof in

  if InterCfg.is_call_node icfg from_node then
    let callee := InterNode.get_pid to_node in
    let access := get_all_access callee access_map in
    let from_m := Mem.restrict access from_m in
    if Mem.opt_le from_m to_m then true else
      fail_inter_edge from_node to_node

  else if G.is_exit_node from_node then
    let callee := InterNode.get_pid from_node in
    let access := get_all_access callee access_map in
    match InterCfg.callof icfg to_node with
    | None => fail_inter_edge_no_callof from_node to_node
    | Some call_node =>
      let caller_m := table_find call_node outputof in
      let caller_m := Mem.subtract access caller_m in
      if Mem.opt_le from_m to_m then
        if Mem.opt_le caller_m to_m then true else
          fail_inter_edge call_node to_node
      else fail_inter_edge from_node to_node
    end

  else fail_inter_edge_invalid from_node to_node.

Definition valid_inter_edges :=
  let valid_inter_edges' from_node to_nodes :=
    InterCfg.NodeSet.for_all (valid_inter_edge from_node) to_nodes in
  InterCfg.NodeMap.for_all print2 valid_inter_edges' (InterCfg.succ icfg).

(* Access info validation: if there is a call from f to g, acc(g) <= acc(f). *)

Definition valid_inter_acc (from_node to_node : InterNode.t) : bool :=
  if InterNode.is_entry_node to_node then
    let caller := InterNode.get_pid from_node in
    let callee := InterNode.get_pid to_node in
    let caller_access := get_access caller access_map in
    let callee_access := get_access callee access_map in
    if Acc.le_dec callee_access caller_access then true else
      fail_inter_acc from_node to_node
  else true.

Definition valid_inter_accs :=
  let valid_inter_accs' from_node to_nodes :=
    InterCfg.NodeSet.for_all (valid_inter_acc from_node) to_nodes in
  InterCfg.NodeMap.for_all print2 valid_inter_accs' (InterCfg.succ icfg).

(* Correct densification validation:
all values of accessed locations should be the same. *)

Definition valid_dens_node f (intra_n : IntraNode.t) (cmd : cmd) : bool :=
  let n := (f, intra_n) in
  let orig_m := table_find n orig_inputof in
  let m := table_find n inputof in
  let '(m', acc_n) := run_access Strong g n cmd orig_m in
  let uses_n := Acc.useof acc_n in
  if Mem.eq_wrt uses_n orig_m m then true else fail_dens_inputof n.

Definition valid_dens_cfg f cfg :=
  IntraCfg.NodeMap.for_all print2 (valid_dens_node f) (IntraCfg.cmds cfg).

Definition valid_dens :=
  InterCfg.PidMap.for_all print2 valid_dens_cfg (InterCfg.cfgs icfg).

Definition valid : bool :=
  valid_cfgs && valid_inter_edges && valid_inter_accs && valid_dens.

Local Close Scope bool.

End Validate.

(* Alarm report *)

Module AlarmAccess := Alarm Acc.MAcc AccMem.

Definition check_query_access := AlarmAccess.check_query.

Module AlarmOnly := Alarm MId IdMem.

Definition check_query_only := AlarmOnly.check_query.

Section AlarmReport.

Variable (mode : update_mode) (g : G.t) (inputof : Table.t Mem.t).

Definition check_queries node m (q_pos : query * DPos.t)
: query * DPos.t * list status :=
  let '(q, pos) := q_pos in
  let statuses := check_query_only mode node m q in
  (q, pos, statuses).

Fixpoint query_flatten' (q : query) (pos : DPos.t)
         (statuses : list status)
: list (query * DPos.t * status) :=
  match statuses with
    | nil => nil
    | s :: tl => (q, pos, s) :: query_flatten' q pos tl
  end.

Fixpoint query_flatten (l : list (query * DPos.t * list status))
: list (query * DPos.t * status) :=
  match l with
    | nil => nil
    | (q, pos, statuses) :: tl =>
      query_flatten' q pos statuses ++ query_flatten tl
  end.

Definition collect_alarm_result_node pid node cmd acc
: list (query * DPos.t * status) :=
  let query_list := collect_query cmd in
  let m := table_find (pid, node) inputof in
  let query_status_list := List.map (check_queries (pid, node) m) query_list in
  query_flatten query_status_list ++ acc.

Definition collect_alarm_result_intra pid cfg acc
: list (query * DPos.t * status) :=
  let cmds := IntraCfg.cmds cfg in
  IntraCfg.NodeMap.fold (collect_alarm_result_node pid) cmds acc.

Definition collect_alarm_result : list (query * DPos.t * status) :=
  let icfg := G.icfg g in
  let cfgs := InterCfg.cfgs icfg in
  InterCfg.PidMap.fold collect_alarm_result_intra cfgs nil.

End AlarmReport.

End Make.
