(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** Intra CFG in frontend *)

open VocabA
open Cil
open FSyn

exception Not_found_cmd

module NodeSet = Set.Make (FIntraNode)

module NodeMap = Map.Make (FIntraNode)

module G = Graph.Persistent.Digraph.Concrete (FIntraNode)

type t =
  { fun_dec : Cil.fundec
  ; graph : G.t
  ; cmds : Cmd.t NodeMap.t }

let empty fd =
  { fun_dec = fd
  ; graph = G.empty
  ; cmds = NodeMap.empty }

let get_formals g = List.map (fun svar -> svar.vname) g.fun_dec.sformals

let nodes_of g = G.fold_vertex NodeSet.add g.graph NodeSet.empty

let preds_of n g = G.pred g.graph n

let succs_of n g = G.succ g.graph n

let find_cmd n g =
  if n = FIntraNode.Entry || n = FIntraNode.Exit then Cmd.Cskip else
    try NodeMap.find n g.cmds with Not_found -> raise Not_found_cmd

let is_call_node n g =
  match find_cmd n g with
  | Cmd.Ccall _ -> true
  | _ -> false

let modify_on_nodes f g = G.fold_vertex f g.graph g

let add_edge n1 n2 g = { g with graph = G.add_edge g.graph n1 n2 }

let remove_node n g =
  { g with
    graph = G.remove_vertex g.graph n
  ; cmds = NodeMap.remove n g.cmds }

let remove_nodes ns g = list_fold remove_node ns g

let remove_edge n1 n2 g = { g with graph = G.remove_edge g.graph n1 n2 }

let remove_edges_from n g =
  list_fold (fun s -> remove_edge n s) (succs_of n g) g

let set_cmd n c g =
  { g with
    graph = G.add_vertex g.graph n
  ; cmds = NodeMap.add n c g.cmds }

let push_cmd_node cmd (g, tail) =
  let node = FIntraNode.make () in
  g |> set_cmd node cmd |> add_edge tail node, node

let push_cmd_nodes cmds (g, tail) = list_fold push_cmd_node cmds (g, tail)

let insert_cmd_node pred succ c g =
  let (g, cmd_node) = push_cmd_node c (g, pred) in
  g
  |> remove_edge pred succ
  |> add_edge cmd_node succ

let remove_empty_node n g =
  let succs = succs_of n g in
  let preds = preds_of n g in
  if find_cmd n g = Cmd.Cskip && List.length succs = 1 && List.length preds = 1
  then
    let pred, succ = List.hd preds, List.hd succs in
    g |> remove_node n |> add_edge pred succ
  else g

let remove_empty_nodes g = modify_on_nodes remove_empty_node g

(** Add allocation/cast commands for

    lv = (typ* )alloc(sizeof(typ) * size); *)
let push_alloc_cmd_node lv typ size loc (g, tail) =
  let loc_var = var (makeTempVar g.fun_dec voidPtrType) in
  let arg = BinOp (Mult, sizeOf typ, size, intType) in
  let casted_var = mkCast (Lval loc_var) (TPtr (typ, [])) in
  let alloc_cmd = Cmd.Calloc (loc_var, Cmd.Array arg, loc) in
  let cast_cmd = Cmd.Cset (lv, casted_var, loc) in
  push_cmd_nodes [alloc_cmd; cast_cmd] (g, tail)

let set_stmt s g =
  let pred = FIntraNode.node_of_stmt s in
  let succs = List.map FIntraNode.node_of_stmt s.succs in
  g
  |> set_cmd pred (Cmd.of_stmt s.skind)
  |> list_fold (add_edge pred) succs
