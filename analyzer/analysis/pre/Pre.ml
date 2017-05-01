(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(* Access Pre-Analysis Framework *)

open Monad
open VocabA
open VocabB
open Syn
open UserInputType
open UserInput.Input
open RunWrapper
open Global

module ProcG = Graph.Persistent.Digraph.Concrete (Key2Ordered (Proc))

let calls2procG calls =
  let add_callee caller callee acc = ProcG.add_edge acc caller callee in
  let add_callees caller callees =
    InterCfg.PidSet.fold (add_callee caller) callees in
  InterCfg.PidMap.fold add_callees calls ProcG.empty

let procG2calls ocaml_cg =
  let add_vertex v g = InterCfg.PidMap.add v InterCfg.PidSet.empty g in
  let add_edge caller callee g =
    let callees = get_some (InterCfg.PidMap.find caller g) in
    let callees = InterCfg.PidSet.add callee callees in
    InterCfg.PidMap.add caller callees g in
  InterCfg.PidMap.empty
  |> ProcG.fold_vertex add_vertex ocaml_cg
  |> ProcG.fold_edges add_edge ocaml_cg

type t =
  { mem : Mem.t
  ; total_abslocs : PowLoc.t
  ; access : Acc.t InterCfg.NodeMap.t
  ; access_proc : Acc.t InterCfg.PidMap.t
  ; access_reach : Acc.t InterCfg.PidMap.t
  ; defs_of : InterCfg.NodeSet.t LocMap.t
  ; uses_of : InterCfg.NodeSet.t LocMap.t
  }

let empty =
  { mem = Mem.bot
  ; total_abslocs = PowLoc.empty
  ; access = InterCfg.NodeMap.empty
  ; access_proc = InterCfg.PidMap.empty
  ; access_reach = InterCfg.PidMap.empty
  ; defs_of = LocMap.empty
  ; uses_of = LocMap.empty
  }

let get_mem i = i.mem
let get_total_abslocs i = i.total_abslocs
let get_access i n =
  default Acc.empty (InterCfg.NodeMap.find n i.access)
let get_access_proc i pid =
  default Acc.empty (InterCfg.PidMap.find pid i.access_proc)
let get_access_reach i pid =
  default Acc.empty (InterCfg.PidMap.find pid i.access_reach)
let get_defs_of t = t.defs_of
let get_uses_of t = t.uses_of

let restrict_access t locs =
  let add_access node access =
    InterCfg.NodeMap.add node (Acc.restrict locs access) in
  { t with
    access = InterCfg.NodeMap.fold add_access t.access InterCfg.NodeMap.empty }

let restrict abslocs m = InterCfg.NodeMap.map (Acc.restrict abslocs) m
let init_access g m =
  let nodes = InterCfg.nodes (G.icfg g) in
  let add_access node =
    let access = accessof Strong g node m in
    let qaccess = qaccessof Strong g node m in
    InterCfg.NodeMap.add node (Acc.join access qaccess) in
  let node2access =
    InterCfg.NodeSet.fold add_access nodes InterCfg.NodeMap.empty in
  let union_access _ access acc =
    let acc = PowLoc.union_small_big (Acc.useof access) acc in
    PowLoc.union_small_big (Acc.defof access) acc in
  let abslocs = InterCfg.NodeMap.fold union_access node2access PowLoc.empty in
  (abslocs, restrict abslocs node2access)

let init_access_proc access : Acc.t InterCfg.PidMap.t =
  let add_access node new_access proc2access =
    let pid = InterNode.get_pid node in
    let access =
      default Acc.empty (InterCfg.PidMap.find pid proc2access) in
    let access = Acc.union access new_access in
    InterCfg.PidMap.add pid access proc2access in
  InterCfg.NodeMap.fold add_access access InterCfg.PidMap.empty

let make_pid2n pids pid2n_func scc_num =
  let add_pid2n pid (m, n) =
    let (k, n) = try (pid2n_func pid, n) with Not_found -> (n, n + 1) in
    (InterCfg.PidMap.add pid k m, n) in
  list_fold add_pid2n pids (InterCfg.PidMap.empty, scc_num)

let make_n2pids pids group_num pid2n =
  let n2pids_empty =
    let rec n2pids_empty_rec n m =
      if n <= 0 then m else
        let n' = n - 1 in
        n2pids_empty_rec n' (IntMap.add n' InterCfg.PidSet.empty m) in
    n2pids_empty_rec group_num IntMap.empty in
  let add_n2pid pid m =
    let n = get_some (InterCfg.PidMap.find pid pid2n) in
    let pids = InterCfg.PidSet.add pid (IntMap.find n m) in
    IntMap.add n pids m in
  list_fold add_n2pid pids n2pids_empty

let make_n2access n2pids access_proc =
  let add_access pid =
    Acc.union (default Acc.empty (InterCfg.PidMap.find pid access_proc)) in
  let access_procs pids = InterCfg.PidSet.fold add_access pids Acc.empty in
  IntMap.map access_procs n2pids

let make_n2trans_ns pid2n trans_calls =
  let add f acc = IntSet.add (get_some (InterCfg.PidMap.find f pid2n)) acc in
  let trans_callees2trans_ns trans_callees =
    InterCfg.PidSet.fold add trans_callees IntSet.empty in
  let adds f trans_callees acc =
    let f_n = get_some (InterCfg.PidMap.find f pid2n) in
    let trans_ns = trans_callees2trans_ns trans_callees in
    let orig_trans_ns = try IntMap.find f_n acc with _ -> IntSet.empty in
    IntMap.add f_n (IntSet.union orig_trans_ns trans_ns) acc in
  InterCfg.PidMap.fold adds trans_calls IntMap.empty

let make_n2reach_access n2pids n2trans_ns n2access =
  let n2reach_access = ref IntMap.empty in
  let join_n_access n acc = Acc.join (IntMap.find n !n2reach_access) acc in
  let rec iter n : unit =
    if not (IntMap.mem n !n2reach_access) then
      let other_ns = IntSet.remove n (IntMap.find n n2trans_ns) in
      IntSet.iter iter other_ns;
      let f_access = IntMap.find n n2access in
      let other_access = IntSet.fold join_n_access other_ns Acc.empty in
      let reach_access = Acc.join f_access other_access in
      n2reach_access := IntMap.add n reach_access !n2reach_access in
  let iter' n _ = iter n in
  IntMap.iter iter' n2trans_ns;
  !n2reach_access

(* NOTE: Not_found cases are unreachable functions from _G_.  They
   will be removed later. *)
let make_pid2reach_access n2reach_access pid2n =
  let get_reach_access n =
    try IntMap.find n n2reach_access with Not_found -> Acc.empty in
  InterCfg.PidMap.map get_reach_access pid2n

let init_access_reach pids cg access_proc trans_calls =
  let module SCC = Graph.Components.Make (ProcG) in
  let (scc_num, pid2n_func) = SCC.scc (calls2procG (Callgraph.calls cg)) in
  let (pid2n, group_num) = make_pid2n pids pid2n_func scc_num in
  let n2pids = make_n2pids pids group_num pid2n in
  let n2access = make_n2access n2pids access_proc in
  let n2trans_ns = make_n2trans_ns pid2n trans_calls in
  let n2reach_access = make_n2reach_access n2pids n2trans_ns n2access in
  let pid2reach_access = make_pid2reach_access n2reach_access pid2n in
  pid2reach_access

let init_defs_of access_map =
  let add_node node loc defs_of =
    let nodes = default InterCfg.NodeSet.empty (LocMap.find loc defs_of) in
    LocMap.add loc (InterCfg.NodeSet.add node nodes) defs_of in
  let init_defs_of1 node access defs_of =
    PowLoc.fold (add_node node) (Acc.defof access) defs_of in
  InterCfg.NodeMap.fold init_defs_of1 access_map LocMap.empty

let init_uses_of access_map =
  let add_node node loc uses_of =
    let nodes = default InterCfg.NodeSet.empty (LocMap.find loc uses_of) in
    LocMap.add loc (InterCfg.NodeSet.add node nodes) uses_of in
  let init_uses_of1 node access uses_of =
    PowLoc.fold (add_node node) (Acc.useof access) uses_of in
  InterCfg.NodeMap.fold init_uses_of1 access_map LocMap.empty

let fixpt g nodes m =
  let rec fixpt' k m =
    if not !Options.opt_nobar then
      (prerr_string ("\r#iters: " ^ string_of_int k);
       flush stderr);
    let m' = InterCfg.NodeSet.fold (run Weak g) nodes m in
    let m' = Mem.widen m m' in
    if Mem.le_dec m' m then
      (prerr_newline ();
       prerr_endline ("#mem entries: " ^ string_of_int (Mem.cardinal m'));
       m')
    else fixpt' (k + 1) m' in
  fixpt' 1 m

let callees_of icfg node mem =
  match InterCfg.get_cmd icfg node with
  | Some c ->
    (match c with
     | Ccall (_, Lval (Coq_lval_intro (VarLhost (vi, _), NoOffset, _), _), _, _)
       when vi = "zoo_print" -> InterCfg.PidSet.empty
     | Ccall (_, Lval (Coq_lval_intro (VarLhost (vi, _), NoOffset, _), _), _, _)
       when vi = "zoo_stack" -> InterCfg.PidSet.empty
     | Ccall (_, e, _, _) ->
       let v = eval Strong node e mem in
       PowProc.fold InterCfg.PidSet.add (powProc_of_val v)
         InterCfg.PidSet.empty
     | _ -> InterCfg.PidSet.empty )
  | None -> InterCfg.PidSet.empty

let init_node_calls icfg nodes m cg =
  let add_node_calls icfg m node =
    if InterCfg.is_call_node icfg node then
      InterCfg.NodeMap.add node (callees_of icfg node m)
    else id in
  let node_calls =
    InterCfg.NodeSet.fold (add_node_calls icfg m) nodes
      InterCfg.NodeMap.empty in
  { cg with Callgraph.node_calls = node_calls }

let init_calls pids cg =
  let init_map =
    let add_empty_set pid m =
      InterCfg.PidMap.add pid InterCfg.PidSet.empty m in
    list_fold add_empty_set pids InterCfg.PidMap.empty in
  let calls_add node new_callees calls =
    let caller = InterNode.get_pid node in
    let callees =
      default InterCfg.PidSet.empty (InterCfg.PidMap.find caller calls) in
    let callees = InterCfg.PidSet.union callees new_callees in
    InterCfg.PidMap.add caller callees calls in
  let calls =
    InterCfg.NodeMap.fold calls_add (Callgraph.node_calls cg) init_map in
  { cg with Callgraph.calls = calls }

let init_trans_calls pids cg =
  let module T = Graph.Oper.P (ProcG) in
  let calls = Callgraph.calls cg in
  let ocaml_cg = calls2procG calls in
  let ocaml_tran_cg = T.transitive_closure ocaml_cg in
  let trans_calls = procG2calls ocaml_tran_cg in
  { cg with Callgraph.trans_calls = trans_calls }

let init_callgraph nodes g m =
  let icfg = G.icfg g in
  let pids = InterCfg.pidsof icfg in
  let cg =
    G.callgraph g
    |> init_node_calls icfg nodes m
    |> init_calls pids
    |> init_trans_calls pids in
  { g with G.callgraph = cg }

let get_reachable pid cg =
  let trans_calls = Callgraph.trans_calls cg in
  let trans_callees = get_some (InterCfg.PidMap.find pid trans_calls) in
  InterCfg.PidSet.add pid trans_callees

let remove_unreachable_functions (info, g) =
  let pids_all =
    list_fold InterCfg.PidSet.add (InterCfg.pidsof (G.icfg g))
      InterCfg.PidSet.empty in
  let reachable = get_reachable "_G_" (G.callgraph g) in
  let unreachable = InterCfg.PidSet.diff pids_all reachable in
  let g = InterCfg.PidSet.fold G.remove_function unreachable g in
  prerr_string "#functions: ";
  prerr_endline (string_of_int (InterCfg.PidSet.cardinal pids_all));
  prerr_string "#unreachable functions: ";
  prerr_endline (string_of_int (InterCfg.PidSet.cardinal unreachable));
  g

let unreachable_node_intra (cfg : IntraCfg.t) : IntraCfg.NodeSet.t =
  let nodes = IntraCfg.nodes cfg in
  let rec remove_reachable_node work acc =
    match IntraCfg.NodeSet.choose work with
    | Some node ->
      let work = IntraCfg.NodeSet.remove node work in
      if IntraCfg.NodeSet.mem node acc then
        let acc = IntraCfg.NodeSet.remove node acc in
        let succ_map = IntraCfg.succ cfg in
        let succs_opt = IntraCfg.NodeMap.find node succ_map in
        let succs = default IntraCfg.NodeSet.empty succs_opt in
        let succs = IntraCfg.NodeSet.remove node succs in
        let work = IntraCfg.NodeSet.union work succs in
        remove_reachable_node work acc
      else remove_reachable_node work acc
    | None -> acc in
  remove_reachable_node (IntraCfg.NodeSet.singleton IntraNode.Entry)
    nodes

let unreachable_node_inter icfg =
  let add_pid_nodes pid nodes =
    let add_pid_node node = InterCfg.NodeSet.add (pid, node) in
    IntraCfg.NodeSet.fold add_pid_node nodes InterCfg.NodeSet.empty in
  let add_unreachable_node pid cfg =
    let intra_nodes = unreachable_node_intra cfg in
    let inter_nodes = add_pid_nodes pid intra_nodes in
    InterCfg.NodeSet.union inter_nodes in
  InterCfg.PidMap.fold add_unreachable_node (InterCfg.cfgs icfg)
    InterCfg.NodeSet.empty

let remove_unreachable_nodes g =
  let icfg = G.icfg g in
  let unreachable = unreachable_node_inter icfg in
  let g = InterCfg.NodeSet.fold G.remove_node unreachable g in
  prerr_string "#nodes: ";
  prerr_endline
    (string_of_int (InterCfg.NodeSet.cardinal (InterCfg.nodes icfg)));
  prerr_string "#unreachable nodes: ";
  prerr_endline (string_of_int (InterCfg.NodeSet.cardinal unreachable));
  g

let init_access_info g m =
  let pids = InterCfg.pidsof (G.icfg g) in
  let trans_calls = Callgraph.trans_calls (G.callgraph g) in
  let (total_abslocs, access) = init_access g m in
  prerr_string "#abstract locations: ";
  prerr_endline (string_of_int (PowLoc.cardinal total_abslocs));
  let defs_of = init_defs_of access in
  let uses_of = init_uses_of access in
  let access_proc = init_access_proc access in
  let access_reach =
    init_access_reach pids (G.callgraph g) access_proc trans_calls in
  { mem = m
  ; total_abslocs = total_abslocs
  ; access = access
  ; access_proc = access_proc
  ; access_reach = access_reach
  ; defs_of = defs_of
  ; uses_of = uses_of }

let analyze g =
  let g = Step.small "Remove unreachable nodes" remove_unreachable_nodes g in
  let nodes = InterCfg.nodes (G.icfg g) in
  let m = Step.small "Fixpoint iteration" (fixpt g nodes) Mem.bot in
  let g = Step.small "Initialize callgraph" (init_callgraph nodes g) m in
  let info = Step.small "Initialize access info" (init_access_info g) m in
  let g = Step.small "Remove unreachable functions"
      remove_unreachable_functions (info, g) in
  let g = Step.small "Draw inter edges" Trans.t_inter_edges g in
  (info, g)
