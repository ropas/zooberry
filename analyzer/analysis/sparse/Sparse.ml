(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
open VocabB
open UserInputType
open UserInput.Input
open Vali.Vali
open RunWrapper
open Pre
open Dug
open Global

let total_iters = ref 0
let g_clock = ref 0.0

module Workorder = Worklist.Workorder
let needwidening idx order = Workorder.is_loopheader idx order

let def_locs_cache = Hashtbl.create 251
let get_def_locs idx dug =
  try Hashtbl.find def_locs_cache idx with Not_found ->
  let def_locs =
    let union_locs succ = PowLoc.union (get_abslocs idx succ dug) in
    let def_locs = list_fold union_locs (succ idx dug) PowLoc.empty in
    PowLoc.fold (fun x acc -> x :: acc) def_locs [] in
  Hashtbl.add def_locs_cache idx def_locs; def_locs

(* fixpoint iterator specialized to the widening phase *)
let analyze_node idx (works, g, dug, pre, inputof, outputof, order) =
  total_iters := !total_iters + 1 ;
  if !total_iters = 1 then g_clock := Sys.time() else
  if !total_iters mod 10000 = 0 then
    (Printf.eprintf "#iters: %d took %.1f sec\n" !total_iters
       (Sys.time () -. !g_clock);
     flush stderr;
     g_clock := Sys.time ())
  else ();
  let input = table_find idx inputof in
  let old_output = table_find idx outputof in
  let new_output = run Strong g idx input in

  let (new_output, b_stable, unstables) =
    let def_locs = get_def_locs idx dug in
    let is_unstb v1 v2 = not (Val.le_dec v2 v1) in
    let u = Mem.unstables old_output new_output is_unstb def_locs in
    let op = if needwidening idx order then Val.widen else Val.join in
    let u = List.map (fun ((k, v1), v2) -> (k, op v1 v2)) u in
    let new_output =
      list_fold (fun (k, v) -> Mem.add k v) u old_output in
    let u = List.map (fun (k, _) -> (k, Mem.find k new_output)) u in
    (new_output, u = [], u) in

  if b_stable then (works, g, dug, pre, inputof, outputof, order) else
    let id1 = Worklist.NodeMap.find idx order.Workorder.order in
    let (works, inputof) =
      let update_succ succ (works, inputof) =
        let old_input = table_find succ inputof in
        let locs_on_edge = get_abslocs idx succ dug in
        let is_on_edge (x, _) = mem_abslocs x locs_on_edge in
        let to_join = List.filter is_on_edge unstables in
        if to_join = [] then (works, inputof) else
          let weak_add (k, v) = Mem.weak_add k v in
          let new_input = list_fold weak_add to_join old_input in
          let id2 = Worklist.NodeMap.find succ order.Workorder.order in
          let bInnerLoop = Worklist.compare_order (id2, succ) (id1, idx) in
          (Worklist.queue bInnerLoop order.Workorder.headorder succ id2 works,
           Table.add succ new_input inputof) in
      let succs = succ idx dug in
      list_fold update_succ succs (works, inputof) in
    (works, g, dug, pre, inputof, Table.add idx new_output outputof, order)

let rec iterate (widen, join, le)
    (works, g, dug, pre, inputof, outputof, order) =
  match Worklist.pick works with
  | None -> (works, g, dug, pre, inputof, outputof, order)
  | Some (idx, rest) ->
    (rest, g, dug, pre, inputof, outputof, order)
    |> analyze_node idx
    |> iterate (widen, join, le)

let widening (g, dug, pre, inputof, outputof, order) =
  total_iters := 0;
  let nodes = InterCfg.nodes (G.icfg g) in
  let init_worklist = Worklist.init order.Workorder.order nodes in
  let (_, g, dug, pre, inputof, outputof, order) =
    iterate (Val.widen, Val.join, Val.le_dec)
      (init_worklist, g, dug, pre, inputof, outputof, order) in
  prerr_endline ("#iters: " ^ string_of_int !total_iters);
  (g, dug, pre, inputof, outputof, order)

let narrowing (g, dug, pre, inputof, outputof, order) =
  total_iters := 0;
  let nodes = InterCfg.nodes (G.icfg g) in
  let init_worklist = Worklist.init order.Workorder.order nodes in
  let (_, g, dug, pre, inputof, outputof, order) =
    iterate
      (Val.narrow, Val.join, fun x y -> Val.le_dec y x)
      (init_worklist, g, dug, pre, inputof, outputof, order) in
  prerr_endline ("#iters: " ^ string_of_int !total_iters);
  (g, dug, pre, inputof, outputof, order)

let perform (g, dug, pre, order) =
  (* flow-insensitive analysis *)
  let nodes = InterCfg.nodes (G.icfg g) in
  let memFI =
    Step.small "Flow-insensitive analysis" (Pre.fixpt g nodes) Mem.bot in

  (* main analysis *)
  let (inputof, outputof) = (Table.empty, Table.empty) in
  let (g, dug, pre, inputof, outputof, order) =
    Step.small "Fixpoint iteration"
      widening (g, dug, pre, inputof, outputof, order) in

  (* meet with memFI *)
  let meet_memFI (inputof, outputof) =
    (Table.map (Mem.meet_big_small memFI) inputof,
     Table.map (Mem.meet_big_small memFI) outputof) in
  let (inputof, outputof) =
    Step.small "Meet with flow-insensitive memory"
      meet_memFI (inputof, outputof) in

  (* narrowing *)
  let (g, dug, pre, inputof, outputof, order) =
    Step.small_opt !Options.opt_narrow "Narrowing"
      narrowing (g, dug, pre, inputof, outputof, order) in

  (inputof, outputof, memFI)

(* Merge m1 and m2 while taking m2(x) if x is in locs *)
let merge_over locs m1 m2 =
  let add_when_in k m1 = Mem.add k (Mem.find k m2) m1 in
  PowLoc.fold add_when_in locs m1

let filter_locs locs m =
  Mem.filter (fun l -> PowLoc.mem l locs) m

let get_use_locs_by_du idx_here dug =
  let add_locs pred = PowLoc.union (get_abslocs pred idx_here dug) in
  list_fold add_locs (pred idx_here dug) PowLoc.empty

let get_def_locs_by_du idx_here dug =
  let add_locs succ = PowLoc.union (get_abslocs idx_here succ dug) in
  list_fold add_locs (succ idx_here dug) PowLoc.empty

(* Generate the full input table for a given procedure : exploits the
   SSA property that the value of a location not used at a node is
   identical to the value at the immediate dominator of the node *)
let densify_cfg (g, dug, pre) inputof outputof (f, cfg) f_dom_tree =
  let rec propagate here (inputof, outputof) =
    let idx_here = (f, here) in
    let use_locs = get_use_locs_by_du idx_here dug in
    let def_locs = get_def_locs_by_du idx_here dug in
    let input_here = table_find idx_here inputof in
    let output_here = table_find idx_here outputof in
    let d_input_here =
      let basic_mem_spec =
        match Dug.parent_of_dom_tree here f_dom_tree with
        | None -> Mem.bot
        | Some idom -> table_find (f, idom) outputof in
      merge_over use_locs basic_mem_spec input_here in
    let d_output_here =
      let output_here' =
        run Strong g idx_here d_input_here in
      merge_over def_locs output_here' output_here in
    let d_inputof = Table.add idx_here d_input_here inputof in
    let d_outputof = Table.add idx_here d_output_here outputof in
    let nodes_dom_ordered = Dug.children_of_dom_tree here f_dom_tree in
    IntraCfg.NodeSet.fold propagate nodes_dom_ordered (d_inputof, d_outputof)
  in
  propagate IntraNode.Entry (inputof, outputof)

let densify (g, dug, pre, inputof, outputof, dom_tree) =
  let icfg = G.icfg g in
  let pids = InterCfg.pidsof icfg in
  let cfgs = InterCfg.cfgs icfg in
  let todo = List.length pids in
  let iter_func f (k, (inputof, outputof)) =
    let f_dom_tree = get_some (InterCfg.PidMap.find f dom_tree) in
    prerr_progressbar k todo;
    match InterCfg.PidMap.find f cfgs with
    | Some cfg ->
      (k + 1,
       densify_cfg (g, dug, pre) inputof outputof (f, cfg) f_dom_tree)
    | None -> (k + 1, (inputof, outputof)) in
  (1, (inputof, outputof))
  |> list_fold iter_func pids
  |> snd

let analyze (pre, g) =
  let (dug, dom_tree) =
    Step.small "Def-use graph construction" Dug.icfg2dug (g, pre) in
  let order = Step.small "Compute workorder"
      Worklist.Workorder.perform (g, dug) in
  let (inputof, outputof, memFI) =
    perform (g, dug, pre, order) in
  let (d_inputof, d_outputof) =
    if !Options.opt_densify then
      Step.small "Densify"
        densify (g, dug, pre, inputof, outputof, dom_tree)
    else (inputof, outputof) in
  ( dug, memFI, order, inputof, outputof, d_inputof, d_outputof )
