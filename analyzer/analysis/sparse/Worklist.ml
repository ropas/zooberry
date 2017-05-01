(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
open VocabB
open Dug
open UserInputType
open UserInput.Input
open Global

module NGraph = struct
  module NOrder = struct
    type t = int
    let compare = compare
    let hash = Hashtbl.hash
    let equal = ( = )
  end

  module G = Graph.Persistent.Digraph.Concrete (NOrder)
  include G
  include Graph.Components.Make (G)
end

module NodeSet = Set.Make (InterNodeG)

module NodeMap = Map.Make (InterNodeG)

module Workorder = struct

type t = {
  order : (int * bool) NodeMap.t;
  headorder: int NodeMap.t;
  loopheads : NodeSet.t
}

let empty = {
  order = NodeMap.empty;
  headorder = NodeMap.empty;
  loopheads = NodeSet.empty
}

let make dug : NGraph.t * InterNodeG.t IntMap.t =
  let i = ref 0 in
  let new_i () = let v = !i in i := !i + 1; v in
  let create n i2n n2i =
    try (NodeMap.find n n2i, i2n, n2i) with Not_found ->
      let i = new_i () in
      (i, IntMap.add i n i2n, NodeMap.add n i n2i) in
  let add_edge src dst (ng, i2n, n2i) =
    let (i_src, i2n, n2i) = create src i2n n2i in
    let (i_dst, i2n, n2i) = create dst i2n n2i in
    (NGraph.add_edge ng i_src i_dst, i2n, n2i) in
  fold_edges add_edge dug (NGraph.empty, IntMap.empty, NodeMap.empty)
  |> fun (ng, i2n, _) -> (ng, i2n)

let projection scc ng =
  let add_back_edge e newg =
    let succ = NGraph.succ ng e in
    let succ = List.filter (fun x -> IntSet.mem x scc) succ in
    list_fold (fun s newg -> NGraph.add_edge newg e s) succ newg in
  IntSet.fold add_back_edge scc NGraph.empty

let loophead_of scc ng =
  let add_entry src dst acc =
    if not (IntSet.mem src scc) && IntSet.mem dst scc then IntSet.add dst acc
    else acc in
  let entries = NGraph.fold_edges add_entry ng IntSet.empty in
  let get_score n =
    let preds = NGraph.pred ng n in
    let preds = List.filter (fun n -> IntSet.mem n scc) preds in
    List.length preds in
  let compare_score n (candidate, score) =
    let score_n = get_score n in
    if score_n > score then (n, score_n) else (candidate, score) in
  fst (IntSet.fold compare_score entries (IntSet.choose scc, 0))

let cut_backedges ng entry =
  let preds = NGraph.pred ng entry in
  let cut_edge pred ng = NGraph.remove_edge ng pred entry in
  list_fold cut_edge preds ng

let rec get_order sccs ng (wo, lhs, ho) order =
  match sccs with
  | scc :: t ->
    if List.length scc > 1 then
      let headorder = order + 3 * (List.length scc) in
      let scc = IntSet.of_list scc in
      let ng' = projection scc ng in
      let lh = loophead_of scc ng in
      let (lhs, ho) = (IntSet.add lh lhs, IntMap.add lh headorder ho) in
      let (wo, lhs, ho, _) = get_order t ng (wo, lhs, ho) (headorder + 1) in
      let ng' = cut_backedges ng' lh in
      let sccs' = List.rev (Array.to_list (NGraph.scc_array ng')) in
      get_order sccs' ng' (wo, lhs, ho) order
    else
      let n = List.hd scc in
      get_order t ng (IntMap.add n order wo, lhs, ho) (order + 1)
  | [] -> (wo, lhs, ho, order)

let is_loopheader here info = NodeSet.mem here info.loopheads

let rec perform (g, dug) =
  let (ng, i2n) = make dug in
  let sccs = List.rev (Array.to_list (NGraph.scc_array ng)) in
  let (wo, lhs, ho, _) =
    get_order sccs ng (IntMap.empty, IntSet.empty, IntMap.empty) 0 in

  let add_rec_node src dst nodes =
    if src = dst then IntSet.add src nodes else nodes in
  let lhs = NGraph.fold_edges add_rec_node ng lhs in

  let trans_map trans_k trans_v m =
    let add_1 k v = NodeMap.add (trans_k k) (trans_v k v) in
    IntMap.fold add_1 m NodeMap.empty in
  let trans_set trans_v s =
    let add_1 v = NodeSet.add (trans_v v) in
    IntSet.fold add_1 s NodeSet.empty in
  let trans_k k = IntMap.find k i2n in

  let wo = trans_map trans_k (fun k v -> (v, IntSet.mem k lhs)) wo in
  let lhs = trans_set (fun v -> IntMap.find v i2n) lhs in
  let ho = trans_map trans_k (fun _ v -> v) ho in

  (* If call is loophead, adjust loopheads. *)
  let lhs =
    let sccs = List.map (List.map trans_k) sccs in
    let find_scc n sccs =
      try Some (List.find (List.mem n) sccs) with _ -> None in
    let adjust_lhs call lhs =
      if not (NodeSet.mem call lhs) then lhs else
        match find_scc call sccs with
        | None -> NodeSet.remove call lhs
        | Some scc ->
          if List.length scc < 2 then NodeSet.remove call lhs else
            (* Assumption: Every call nodes' successors cannot be call
               nodes. *)
            let alternatives = Dug.succ call dug in
            list_fold NodeSet.add alternatives (NodeSet.remove call lhs) in
    let callnodes = InterCfg.callnodesof (G.icfg g) in
    InterCfg.NodeSet.fold adjust_lhs callnodes lhs in

  { order = wo; headorder = ho; loopheads = lhs }
end

module WorkSet = struct
  type workorder = int * bool

  let no_order = (0, false)

  module Ord = struct
    type t = workorder * InterNodeG.t

    let compare ((o1, _), v1) ((o2, _), v2) =
      let cmp_o = o1 - o2 in
      let cmp_v = Pervasives.compare v1 v2 in
      if cmp_o = 0 then cmp_v else cmp_o
  end

  include Set.Make (Ord)
end

type t = WorkSet.t
let empty = WorkSet.empty
let cardinal = WorkSet.cardinal
let mem = WorkSet.mem
let compare_order x y = WorkSet.Ord.compare x y <= 0

let queue is_inneredge ho n o ws =
  (* change order if,
     - the n node has a loophead order, and
     - an inneredge to the n node is updated
  *)
  let rec change_order n o is_inneredge =
    let is_loophead = snd o in
    if is_inneredge && is_loophead then
      try (NodeMap.find n ho, is_loophead) with Not_found -> o
    else o in
  let new_o = change_order n o is_inneredge in
  WorkSet.add (new_o, n) ws

let init wo nodes =
  let init_v v =
    let wo_of_v = try NodeMap.find v wo with _ -> WorkSet.no_order in
    queue false NodeMap.empty v wo_of_v in
  InterCfg.NodeSet.fold init_v nodes WorkSet.empty

let pick ws =
  try
    let (o, n) = WorkSet.min_elt ws in
    let ws = WorkSet.remove (o, n) ws in
    Some (n, ws)
  with Not_found -> None
