(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** Initialize function in frontend *)

open VocabA
open VocabB
open Cil
open FSyn
open InterCfg
open FIntraCfg

let insert_return_node n g =
  if is_call_node n g then
    let succs = succs_of n g in
    let g = remove_edges_from n g in
    let (g, retn) = push_cmd_node Cmd.Cskip (g, n) in
    list_fold (fun s -> add_edge retn s) succs g
  else g

let insert_return_nodes g = modify_on_nodes insert_return_node g

let insert_return_cmds g =
  let add_return pred acc =
    match find_cmd pred g with
    | Cmd.Creturn _ -> acc
    | _ ->
      let ret_cmd = Cmd.Creturn (None, locUnknown) in
      insert_cmd_node pred FIntraNode.Exit ret_cmd acc in
  list_fold add_return (preds_of FIntraNode.Exit g) g

let add_exit_edges g =
  let lasts = NodeSet.filter (fun n -> succs_of n g = []) (nodes_of g) in
  NodeSet.fold (fun last -> add_edge last FIntraNode.Exit) lasts g

(* NOTE: Order of translations

   1. Desugar.run should follow right after initial node copy, because
   it uses FIntraNode.node_map to distinguish true/false edges, but
   other translations, which run after Desugar.run, may make the
   FIntraNode.node_map invalid.

   2. remove_empty_nodes should run before insert_return_nodes, unless
   it will remove inserted return nodes.
*)

let run_intra fd =
  FIntraNode.init_node_env ();
  let (g, tail) = InitDecl.run false (empty fd, FIntraNode.Entry) in
  g
  |> add_edge tail (FIntraNode.node_of_stmt (List.hd fd.sallstmts))
  |> list_fold set_stmt fd.sallstmts
  |> add_exit_edges
  |> Desugar.run
  |> InitMalloc.run
  |> InitSalloc.run
  |> remove_empty_nodes
  |> insert_return_nodes
  |> insert_return_cmds

let run file =
  let add_init global m =
    match global with
    | GFun (fd, _) -> PidMap.add fd.svar.vname (run_intra fd) m
    | _ -> m in
  list_fold add_init file.globals PidMap.empty
