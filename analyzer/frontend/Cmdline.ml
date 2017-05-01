(*
 *
 * Copyright (c) 2001-2002,
 *  George C. Necula    <necula@cs.berkeley.edu>
 *  Scott McPeak        <smcpeak@cs.berkeley.edu>
 *  Wes Weimer          <weimer@cs.berkeley.edu>
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 * 1. Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *
 * 3. The names of the contributors may not be used to endorse or promote
 * products derived from this software without specific prior written
 * permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
 * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER
 * OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 *)
(* excerpt from http://fossies.org/linux/cil/src/main.ml *)

open Cil

module C = Cil
module F = Frontc
module E = Errormsg

let files = ref []

let args f =
  if Sys.file_exists f then
    if Filename.check_suffix f ".i" || Filename.check_suffix f ".c" then
      files := f :: !files
    else raise (Arg.Bad (f ^ " is not a pre-processed file."))
  else raise (Arg.Bad (f ^ " is not found."))

let parseOneFile fname =
  if !Cilutil.printStages then E.log "Parsing %s\n" fname;
  let cil = F.parse fname () in
  if not !Epicenter.doEpicenter then Rmtmps.removeUnusedTemps cil;
  cil

let frontend () =
  Mergecil.ignore_merge_conflicts := true;
  match List.map parseOneFile !files with
  | [one] -> one
  | [] -> E.s (E.error "No arguments are given")
  | files ->
    let merged = Stats.time "merge" (Mergecil.merge files) "merged" in
    if !E.hadErrors then E.s (E.error "There were errors during merging");
    merged

let parseGlobal = function
  | Cil.GFun (fd, _) ->
    Cil.prepareCFG fd;
    Cil.computeCFGInfo fd true
  | _ -> ()

let makeCFGinfo f =
  Partial.calls_end_basic_blocks f;
  Partial.globally_unique_vids f;
  Cil.iterGlobals f parseGlobal
