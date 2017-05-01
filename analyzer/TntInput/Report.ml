(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
open Format
open VocabB
open PPVocab
open UserInput.Input
open Vali.Vali
open Pos
open DPos
open Global

module PosMod = struct
  type t = pos_t
  let compare = of_coq_compare Pos_as_OT.compare
end

module PosMap = Map.Make (PosMod)

let query_find pos m = try PosMap.find pos m with Not_found -> []
let query_add pos (q, status) m =
  PosMap.add pos ((q, status) :: query_find pos m) m

let rec partition_rec acc queries =
  match queries with
  | [] -> acc
  | ((q, pos), status) :: tl ->
    partition_rec (query_add pos (q, status) acc) tl
let partition queries = partition_rec PosMap.empty queries

let is_clean _ v = List.for_all (fun (_, status) -> status = Clean) v
let print_stats m =
  let all_n = PosMap.cardinal m in
  let clean_n = PosMap.cardinal (PosMap.filter is_clean m) in
  prerr_endline ("#all: " ^ string_of_int all_n);
  prerr_endline ("#clean: " ^ string_of_int clean_n);
  prerr_endline ("#tainted: " ^ string_of_int (all_n - clean_n))

let string_of_query e = PPIL.string_of_exp false e

let print_status = function
  | Tainted exts ->
    (open_box 0;
     print_string "tainted: ";
     PPMem.print_pow_proc_pos exts;
     close_box ())
  | Clean ->
    (open_box 0;
     print_string "clean";
     close_box ())

let rec print_detail_1 pos v =
  match v with
  | [] -> ()
  | (q, status) :: tl ->
    (open_box 0;
     print_string (string_of_pos pos ^ ":" ^ string_of_query q ^ ":");
     print_status status;
     close_box ());
    print_cut ();
    print_detail_1 pos tl

let print_detail m =
  open_vbox 0;
  PosMap.iter print_detail_1 m;
  close_box ();
  print_flush ()

let run (g, inputof) =
  let res = collect_alarm_result UserInputType.Strong g inputof |> partition in
  Step.small "Query status" print_stats res;
  Step.small_side !Options.opt_query "All queries" print_detail res
