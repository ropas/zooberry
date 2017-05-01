(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** Main. *)

open Graph
open Cmdline
open Cil
open VocabA
open VocabB
open PPVocab
open UserInputType
open UserInput.Input
open Vali.Vali
open Global

let parse () =
  Cil.initCIL ();
  let one = frontend () in
  makeCFGinfo one;
  if !E.hadErrors then E.s (E.error "Parsing to Cil failed.");
  { G.icfg = one |> FInterCfg.init |> Trans.t_inter_cfg
  ; G.callgraph = Callgraph.empty }

let validate (g, access_map, io, oo, d_io, d_oo) =
  if valid g access_map io d_io d_oo then
    prerr_endline "Validation succeeded."
  else prerr_endline "Validation failed."

let main () =

let t0 = Sys.time () in
Printexc.record_backtrace true;
try

Format.set_formatter_out_channel stderr;

let usageMsg = "Usage: Main.native [options] source-files" in
Arg.parse Options.opts args usageMsg;
files := List.rev !files;

let g = Step.big "Reading source program" parse () in
let (pre, g) = Step.big "Pre analysis" Pre.analyze g in
let (dug, memFI, order, io, oo, d_io, d_oo) =
  Step.big "Main analysis" Sparse.analyze (pre, g) in
let access_map = pre.Pre.access_reach in
Step.big_side !Options.opt_validate_bool "Validation"
  validate (g, access_map, io, oo, d_io, d_oo);
Step.big_side true "Alarm report" Report.run (g, d_io);
Step.big_side !Options.opt_debug "Debug mode"
  Debug.debug (g, memFI, access_map, dug, io, oo, d_io, d_oo);

prerr_endline hr;
Printf.eprintf "Finished: %.1f sec\n" (Sys.time() -. t0)

with exc ->
  prerr_endline (Printexc.to_string exc);
  prerr_endline (Printexc.get_backtrace())

let _ = main ()
