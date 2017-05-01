(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
open VocabA
open VocabB
open Monad
open UserInputType
open UserInput.Input
open Vali.Vali
open Global

module LocMap = DFMapAVL.FMapAVL'.Make(Loc)

let get_cmd node g = get_some (InterCfg.get_cmd (G.icfg g) node)

let run mode g node m =
  let cmd = get_cmd node g in
  run_only mode g node cmd m

let accessof mode g node m =
  let cmd = get_cmd node g in
  let (_, access) = run_access mode g node cmd m in
  access

let qaccessof mode g node m =
  let cmd = get_cmd node g in
  let add_access (aexp, _) acc =
    let (_, access) = check_query_access mode node m aexp in
    Acc.join acc access in
  list_fold add_access (collect_query cmd) Acc.bot

let eval = RunOnly.SemEval.eval
