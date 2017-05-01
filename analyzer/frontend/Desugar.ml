(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** Desugar stmts *)

open VocabA
open Cil
open FSyn
open FIntraCfg

let if_stmt n g =
  match find_cmd n g with
  | Cmd.Cif (e, tb, fb, loc) ->
    let succs = succs_of n g in
    let tbn, fbn =
      if List.length succs = 2 then
        let succ1, succ2 = List.nth succs 0, List.nth succs 1 in
        match tb.bstmts, fb.bstmts with
        | tstmt :: _, fstmt :: _ ->
          let succ1' = FIntraNode.node_of_stmt tstmt in
          let succ2' = FIntraNode.node_of_stmt fstmt in
          assert ( (succ1, succ2) = (succ1', succ2')
                   || (succ1, succ2) = (succ2', succ1') );
          succ1', succ2'
        | tstmt :: _, [] ->
          let succ' = FIntraNode.node_of_stmt tstmt in
          if succ1 = succ' then succ', succ2 else
          if succ2 = succ' then succ', succ1 else
            assert false
        | [], fstmt :: _ ->
          let succ' = FIntraNode.node_of_stmt fstmt in
          if succ1 = succ' then succ2, succ' else
          if succ2 = succ' then succ1, succ' else
            assert false
        | [], [] -> assert false
      else if List.length succs = 1 then
        let succ = List.nth succs 0 in
        match tb.bstmts, fb.bstmts with
        | [], [] -> succ, succ
        | _, _ -> assert false
      else assert false
    in
    g
    |> insert_cmd_node n tbn (Cmd.Cassume (e, loc))
    |> insert_cmd_node n fbn (Cmd.Cassume (UnOp (LNot, e, typeOf e), loc))
    |> set_cmd n Cmd.Cskip
  | _ -> g

let if_stmts g = modify_on_nodes if_stmt g

let loop_stmt n g =
  match find_cmd n g with
  | Cmd.CLoop _ -> set_cmd n Cmd.Cskip g
  | _ -> g

let loop_stmts g = modify_on_nodes loop_stmt g

let instr_stmt n g =
  match find_cmd n g with
  | Cmd.Cinstr instrs when instrs <> [] ->
    let preds, succs = preds_of n g, succs_of n g in
    let cmds = List.map Cmd.of_instr instrs in
    let g = remove_edges_from n g in
    let (g, tail) = push_cmd_nodes cmds (g, n) in
    let head = List.hd (succs_of n g) in
    g
    |> list_fold (fun p -> add_edge p head) preds
    |> list_fold (fun s -> add_edge tail s) succs
    |> remove_node n
  | Cmd.Cinstr [] -> set_cmd n Cmd.Cskip g
  | _ -> g

let instr_stmts g = modify_on_nodes instr_stmt g

let run g = g |> if_stmts |> loop_stmts |> instr_stmts
