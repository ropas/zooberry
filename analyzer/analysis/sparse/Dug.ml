(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
open VocabA
open VocabB
open UserInputType
open UserInput.Input
open RunWrapper
open Global

module InterNodeG = Key2Ordered (InterNode)

module Label = struct
  type t = PowLoc.t
  let compare : t -> t -> int = compare
  let default = PowLoc.empty
end
module DFG =
  Graph.Persistent.Digraph.ConcreteBidirectionalLabeled (InterNodeG) (Label)
module Check = Graph.Path.Check (DFG)

type t = DFG.t * ((InterNodeG.t * InterNodeG.t), PowLoc.t) Hashtbl.t
let empty : t = (DFG.empty, Hashtbl.create 251)
let nodesof (g, _) = DFG.fold_vertex (fun node acc -> node :: acc) g []
let reachable_nodesof from (g, _) =
  let checker = Check.create g in
  let iter_vertex v acc =
    if Check.check_path checker from v then v :: acc else acc in
  DFG.fold_vertex iter_vertex g []
let succ n (g, _) = try DFG.succ g n with _ -> []
let pred n (g, _) = try DFG.pred g n with _ -> []
let add_edge src dst (g, cache) = (DFG.add_edge g src dst, cache)
let remove_node n (g, cache) = (DFG.remove_vertex g n, cache)
let remove_edge src dst (g, cache) =
  let g = try DFG.remove_edge g src dst with _ -> g in
  (g, cache)
let get_abslocs src dst (g, cache) =
  try Hashtbl.find cache (src, dst) with Not_found ->
    let r = try DFG.E.label (DFG.find_edge g src dst) with _ -> PowLoc.empty in
    (Hashtbl.add cache (src, dst) r; r)

let mem_abslocs x ls = PowLoc.mem x ls
let add_absloc icfg src x dst (dfg, cache) =
  if InterCfg.has_cmd icfg src && InterCfg.has_cmd icfg dst then
    let old_locs = get_abslocs src dst (dfg, cache) in
    let new_locs = PowLoc.add x old_locs in
    let edge = DFG.E.create src new_locs dst in
    let (dfg, _) = remove_edge src dst (dfg, cache) in
    Hashtbl.replace cache (src, dst) new_locs;
    (DFG.add_edge_e dfg edge, cache)
  else (dfg, cache)
let add_abslocs icfg src xs dst (dfg, cache) =
  if InterCfg.has_cmd icfg src && InterCfg.has_cmd icfg dst then
    if PowLoc.is_empty xs then (dfg, cache) else
      let old_locs = get_abslocs src dst (dfg, cache) in
      let new_locs = PowLoc.union xs old_locs in
      let edge = DFG.E.create src new_locs dst in
      let (dfg, _) = remove_edge src dst (dfg, cache) in
      Hashtbl.replace cache (src, dst) new_locs;
      (DFG.add_edge_e dfg edge, cache)
  else (dfg, cache)
let remove_absloc src x dst (g, cache) =
  let old_locs = get_abslocs src dst (g, cache) in
  let new_locs = PowLoc.remove x old_locs in
  let edge = DFG.E.create src new_locs dst in
  let (g, _) = remove_edge src dst (g, cache) in
  Hashtbl.replace cache (src, dst) new_locs;
  (DFG.add_edge_e g edge, cache)
let remove_abslocs src xs dst g =
  PowLoc.fold (fun x -> remove_absloc src x dst) xs g
let in_degree ((g, _) : t) = DFG.in_degree g
let fold_node f ((g, _) : t) = DFG.fold_vertex f g
let fold_edges f ((g, _) : t) = DFG.fold_edges f g
let iter_edges f ((g, _) : t) = DFG.iter_edges f g
let sizeof g =
  let add_cardinal src dst size =
    PowLoc.cardinal (get_abslocs src dst g) + size in
  fold_edges add_cardinal g 0

(* initialize DUG *)

module IntraNodeG = Key2Ordered (IntraNode)
module IntraG = Graph.Persistent.Digraph.ConcreteBidirectional (IntraNodeG)

let parent_of_dom_tree node dom_tree =
  match IntraG.pred dom_tree node with
  | [] -> None
  | [p] -> Some p
  | _ -> invalid_arg "not one parent"

let children_of_dom_tree node f_dom_tree =
  let children = IntraG.succ f_dom_tree node in
  let children =
    list_fold IntraCfg.NodeSet.add children IntraCfg.NodeSet.empty in
  IntraCfg.NodeSet.remove node children

module Dom = Graph.Dominator.Make (IntraG)

type loc = Loc.t

type dom_fronts = IntraCfg.NodeSet.t IntraCfg.NodeMap.t
type phi_points = PowLoc.t InterCfg.NodeMap.t

type access_map = PowLoc.t IntraCfg.NodeMap.t
type access_map_inv = IntraCfg.NodeSet.t LocMap.t

let init_g_cfg cfg =
  let add_edge node succ g_cfg = IntraG.add_edge g_cfg node succ in
  let add_edges node succs = IntraCfg.NodeSet.fold (add_edge node) succs in
  IntraCfg.NodeMap.fold add_edges (IntraCfg.succ cfg) IntraG.empty

let get_dom_fronts_tree cfg =
  let g_graph = init_g_cfg cfg in
  let idom = Dom.compute_idom g_graph IntraNode.Entry in
  let dom_tree_f = Dom.idom_to_dom_tree g_graph idom in
  let dom_fronts_f = Dom.compute_dom_frontier g_graph dom_tree_f idom in
  let nodes = IntraCfg.nodes cfg in
  let dom_tree =
    let add_edge x y graph = IntraG.add_edge graph x y in
    let add_idoms x graph = list_fold (add_edge x) (dom_tree_f x) graph in
    IntraCfg.NodeSet.fold add_idoms nodes IntraG.empty in
  let of_list l = list_fold IntraCfg.NodeSet.add l IntraCfg.NodeSet.empty in
  let dom_fronts =
    let add_fronts x graph =
      IntraCfg.NodeMap.add x (of_list (dom_fronts_f x)) graph in
    IntraCfg.NodeSet.fold add_fronts nodes IntraCfg.NodeMap.empty in
  (dom_fronts, dom_tree)

let get_ordinary_defs pre node = Acc.defof (Pre.get_access pre node)
let get_ordinary_uses pre node = Acc.useof (Pre.get_access pre node)

let get_def_points_of pre l =
  default InterCfg.NodeSet.empty (LocMap.find l (Pre.get_defs_of pre))
let get_use_points_of pre l =
  default InterCfg.NodeSet.empty (LocMap.find l (Pre.get_uses_of pre))

let uses_of_function pre f = Acc.useof (Pre.get_access_reach pre f)
let defs_of_function pre f = Acc.defof (Pre.get_access_reach pre f)
let access_of_function pre f =
  let defs = Acc.defof (Pre.get_access_reach pre f) in
  let uses = Acc.useof (Pre.get_access_reach pre f) in
  PowLoc.union defs uses

let find_callees node g =
  let cg = G.callgraph g in
  let node_calls = Callgraph.node_calls cg in
  match InterCfg.NodeMap.find node node_calls with
  | Some v -> v
  | None -> InterCfg.PidSet.empty

(** locations considered as being used in the given node *)
let lhsof (g, pre) node =
  let icfg = G.icfg g in
  let ordinary_defs = get_ordinary_defs pre node in
  (* entry defines access(f) *)
  let defs_at_entry =
    if InterNode.is_entry_node node then
      access_of_function pre (InterNode.get_pid node)
    else PowLoc.empty in
  (* return nodes define access(callees) *)
  let union_defs_f f = PowLoc.union (access_of_function pre f) in
  let defs_at_return =
    if not (InterCfg.is_return_node icfg node)
    || InterCfg.is_unreachable_return icfg node then PowLoc.empty else
      match InterCfg.callof icfg node with
      | Some call_node ->
        let callees = find_callees call_node g in
        InterCfg.PidSet.fold union_defs_f callees PowLoc.empty
      | None -> failwith "call node is not found" in
  PowLoc.union ordinary_defs (PowLoc.union defs_at_entry defs_at_return)

(** locations considered as being defined in the given node *)
let rec rhsof (g, pre) node =
  let f = InterNode.get_pid node in
  let icfg = G.icfg g in
  let ordinary_uses = get_ordinary_uses pre node in
  (* exit uses access(f) *)
  let uses_at_exit =
    if InterNode.is_exit_node node then access_of_function pre f else
      PowLoc.empty in
  (* return node *)
  let uses_at_return =
    if InterCfg.is_return_node icfg node then
      match InterCfg.callof icfg node with
      | Some call_node ->
        (* return node uses defined variables(e.g. arguments) of call node *)
        let defs_callee = lhsof (g, pre) call_node in
        (* return node uses not-localized variables of call node *)
        let callees = find_callees call_node g in
        let access_of_callees =
          let add_access callee =
            PowLoc.union (access_of_function pre callee) in
          InterCfg.PidSet.fold add_access callees PowLoc.empty in
        let add_not_accessed callee =
          let accs = access_of_function pre callee in
          PowLoc.union (PowLoc.diff access_of_callees accs) in
        let non_localized =
          InterCfg.PidSet.fold add_not_accessed callees PowLoc.empty in
        PowLoc.union defs_callee non_localized
      | None -> PowLoc.empty
    else PowLoc.empty in
  (* call nodes uses access(callees) *)
  let union_access_f f = PowLoc.union (access_of_function pre f) in
  let uses_at_call =
    if InterCfg.is_call_node icfg node then
      InterCfg.PidSet.fold union_access_f (find_callees node g)
        PowLoc.empty
    else PowLoc.empty in
  list_fold PowLoc.union
    [ ordinary_uses; uses_at_exit; uses_at_call; uses_at_return ]
    PowLoc.empty

let prepare_defs_uses (g, pre) (f, cfg) =
  let collect func =
    let add_func_result node =
      let inter_node = (f, node) in
      IntraCfg.NodeMap.add node (func (g, pre) inter_node) in
    IntraCfg.NodeSet.fold add_func_result (IntraCfg.nodes cfg)
      IntraCfg.NodeMap.empty in
  (collect lhsof, collect rhsof)

let prepare_defnodes (g, pre) cfg defs_of =
  let add_def_of_node node l loc2nodes =
    let nodes =
      default IntraCfg.NodeSet.empty (LocMap.find l loc2nodes) in
    LocMap.add l (IntraCfg.NodeSet.add node nodes) loc2nodes in
  let add_defs_of_node node =
    match IntraCfg.NodeMap.find node defs_of with
    | Some defs_of_node ->
      PowLoc.fold (add_def_of_node node) defs_of_node
    | None -> id in
  IntraCfg.NodeSet.fold add_defs_of_node (IntraCfg.nodes cfg)
    LocMap.empty

let add_joinpoint node x joinpoints =
  let vars = default PowLoc.empty (InterCfg.NodeMap.find node joinpoints) in
  InterCfg.NodeMap.add node (PowLoc.add x vars) joinpoints

(** Implements an algorithm computing phi-points in the paper,
    "Efficiently Computing Static Single Assignment Form and the
    Control Dependence Graph.  Ron Cytron et al."  See Fig. 11 of the
    paper for more details.

    About arguments:
    - [w] is the worklist of CFG nodes being processed.
    - [work] is a map of nodes to flags, which indicates whether a
    node has ever been added to [w] during the current iteration.
    - [has_already] is a map of nodes to flags, which indicates
    whether a phi-function for a variable already been inserted at the
    node.
*)
let get_phi_points (f, cfg) pre dom_fronts (defs_of, uses_of, defnodes_of) =
  let iter_dom_fronts (var, cnt) node (rest, has_already, work, joinpoints) =
    if get_some (IntraCfg.NodeMap.find node has_already) < cnt then
      let joinpoints = add_joinpoint (f, node) var joinpoints in
      let has_already = IntraCfg.NodeMap.add node cnt has_already in
      let (work, rest) =
        if get_some (IntraCfg.NodeMap.find node work) < cnt then
          (IntraCfg.NodeMap.add node cnt work, node :: rest)
        else (work, rest) in
      (rest, has_already, work, joinpoints)
    else (rest, has_already, work, joinpoints) in
  let rec iter_w (var, cnt) (w, has_already, work, joinpoints) =
    match w with
    | node :: rest ->
      let dom_fronts = get_some (IntraCfg.NodeMap.find node dom_fronts) in
      (rest, has_already, work, joinpoints)
      |> IntraCfg.NodeSet.fold (iter_dom_fronts (var, cnt)) dom_fronts
      |> iter_w (var, cnt)
    | [] -> (cnt, has_already, work, joinpoints) in
  let rec iter_var vars (cnt, has_already, work, joinpoints) =
    match vars with
    | var :: rest ->
      let cnt = cnt + 1 in
      let update_work node (w, work) =
        (node :: w, IntraCfg.NodeMap.add node cnt work) in
      let defnodes = get_some (LocMap.find var defnodes_of) in
      let (w, work) = IntraCfg.NodeSet.fold update_work defnodes ([], work) in
      (w, has_already, work, joinpoints)
      |> iter_w (var, cnt)
      |> iter_var rest
    | [] -> joinpoints in
  let vars =
    let cons_x x _ acc = x :: acc in
    LocMap.fold cons_x defnodes_of [] in
  let cnt = 0 in
  let (hasalready, work) =
    let add_zero x = IntraCfg.NodeMap.add x 0 in
    let nodes = IntraCfg.nodes cfg in
    let init_v =
      IntraCfg.NodeSet.fold add_zero nodes IntraCfg.NodeMap.empty in
    (init_v, init_v) in
  (cnt, hasalready, work, InterCfg.NodeMap.empty) |> iter_var vars

let cfg2dug (g, pre) (f, cfg) (dug, dom_tree) =
  let (dom_fronts, f_dom_tree) = get_dom_fronts_tree cfg in
  let dom_tree = InterCfg.PidMap.add f f_dom_tree dom_tree in
  let (node2defs, node2uses) = prepare_defs_uses (g, pre) (f, cfg) in
  let loc2defnodes = prepare_defnodes (g, pre) cfg node2defs in
  let phi_points =
    get_phi_points (f, cfg) pre dom_fronts (node2defs, node2uses, loc2defnodes)
  in
  let defs_of node = get_some (IntraCfg.NodeMap.find node node2defs) in
  let uses_of node = get_some (IntraCfg.NodeMap.find node node2uses) in
  let phi_vars_of node =
    default PowLoc.empty (InterCfg.NodeMap.find (f, node) phi_points) in
  let draw_from_lastdef loc2lastdef here loc dug =
    try
      let src = (f, get_some (LocMap.find loc loc2lastdef)) in
      let dst = (f, here) in
      add_absloc (G.icfg g) src loc dst dug
    with _ -> dug in
  let rec search loc2lastdef node dug =
    (* 1: draw non-phi uses from their last definition points do not
          draw for phi-vars since their the last defpoints are the
          current node *)
    let non_phi_uses = PowLoc.diff (uses_of node) (phi_vars_of node) in
    let dug =
      PowLoc.fold (draw_from_lastdef loc2lastdef node) non_phi_uses dug in
    (* 2: update the last definitions:
          (1) phi-variables are defined here
          (2) lhs are defined here *)
    let add_lastdef loc = LocMap.add loc node in
    let update_locs = PowLoc.union (defs_of node) (phi_vars_of node) in
    let loc2lastdef = PowLoc.fold add_lastdef update_locs loc2lastdef in

    (* 3: draw phi-vars of successors from their last definitions *)
    let add_phi_vars succ =
      PowLoc.fold (draw_from_lastdef loc2lastdef succ) (phi_vars_of succ) in
    let dug =
      match IntraCfg.NodeMap.find node (IntraCfg.succ cfg) with
      | Some succs -> IntraCfg.NodeSet.fold add_phi_vars succs dug
      | None -> dug in

    (* 4: process children of dominator trees *)
    let children = children_of_dom_tree node f_dom_tree in

    IntraCfg.NodeSet.fold (search loc2lastdef) children dug in
  (search LocMap.empty IntraNode.Entry dug, dom_tree)

let draw_intraedges (g, pre) (dug, dom_tree) =
  let cfgs = InterCfg.cfgs (G.icfg g) in
  let n = InterCfg.PidMap.cardinal cfgs in
  prerr_endline "- drawing intra-procedural edges";
  let draw_intraedge f cfg (k, (dug, dom_tree)) =
    prerr_progressbar k n;
    (k + 1, cfg2dug (g, pre) (f, cfg) (dug, dom_tree)) in
  let (_, (dug, dom_tree)) =
    InterCfg.PidMap.fold draw_intraedge cfgs (1, (dug, dom_tree)) in
  (dug, dom_tree)

let draw_interedges (g, pre) dug =
  let icfg = G.icfg g in
  let calls = InterCfg.callnodesof icfg in
  let n = InterCfg.NodeSet.cardinal calls in
  prerr_endline "- drawing inter-procedural edges";
  let iter_call call (k, dug) =
    prerr_progressbar ~itv:100 k n;
    let return = get_some (InterCfg.returnof icfg call) in
    let callees = G.get_callees g call in
    let iter_callee callee dug =
      let entry = InterNode.entryof callee in
      let exit  = InterNode.exitof callee in
      let locs_on_call = access_of_function pre callee in
      let locs_on_return = access_of_function pre callee in
      dug
      |> add_abslocs icfg call locs_on_call entry
      |> add_abslocs icfg exit locs_on_return return in
    (k + 1, InterCfg.PidSet.fold iter_callee callees dug) in
  (1, dug) |> InterCfg.NodeSet.fold iter_call calls |> snd

let icfg2dug (g, pre) =
  let (dug, dom_tree) =
    draw_intraedges (g, pre) (empty, InterCfg.PidMap.empty) in
  let dug = draw_interedges (g, pre) dug in
  prerr_endline ("#nodes in def-use graph: "
                 ^ string_of_int (List.length (nodesof dug)));
  prerr_endline ("#locations on def-use graph: " ^ string_of_int (sizeof dug));
  (dug, dom_tree)
