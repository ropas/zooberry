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
open DItv
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

let is_proven _ v = List.for_all (fun (_, status) -> status = Proven) v

let print_stats m =
  let all_n = PosMap.cardinal m in
  let proven_n = PosMap.cardinal (PosMap.filter is_proven m) in
  prerr_endline ("#all: " ^ string_of_int all_n);
  prerr_endline ("#proven: " ^ string_of_int proven_n);
  prerr_endline ("#unproven: " ^ string_of_int (all_n - proven_n))

let string_of_query = function
  | ArrayExp (lv, e) ->
    PPIL.string_of_lval true lv ^ "[" ^ PPIL.string_of_exp false e ^ "]"
  | DerefExp e -> "*" ^ PPIL.string_of_exp true e

let string_of_status = function
  | Proven -> "proven"
  | UnProven -> "unproven"
  | BotAlarm -> "bottom alarm"

let rec print_detail_1 pos v =
  match v with
  | [] -> ()
  | (q, status) :: tl ->
    let spos = string_of_pos pos in
    let squery = string_of_query q in
    let sstatus = string_of_status status in
    let str = Printf.sprintf "%s:%s:%s" spos squery sstatus in
    prerr_endline str;
    print_detail_1 pos tl
    
let print_detail m = PosMap.iter print_detail_1 m

let run (g, inputof) =
  let res = collect_alarm_result UserInputType.Strong g inputof |> partition in
  Step.small "Query status" print_stats res;
  Step.small_side !Options.opt_query "All queries" print_detail res
