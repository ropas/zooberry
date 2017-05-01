(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** Interprocedural CFG. *)

open VocabB
open Cil

type pid = string

module FInterNode = struct

  type t = pid * FIntraNode.t

  let compare = compare

end

module NodeSet = Set.Make (FInterNode)

module NodeMap = Map.Make (FInterNode)

type t =
  { cfgs : FIntraCfg.t InterCfg.PidMap.t
  ; globals : Cil.global list }

let init file =
  { cfgs = InitFun.run file |> InitG.run file
  ; globals = file.Cil.globals }

let nodes_of g =
  let add_node pid n acc = NodeSet.add (pid, n) acc in
  let add_nodes pid cfg acc =
    FIntraCfg.NodeSet.fold (add_node pid) (FIntraCfg.nodes_of cfg) acc in
  InterCfg.PidMap.fold add_nodes g.cfgs NodeSet.empty
