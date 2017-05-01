(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** Intra node in frontend *)

open VocabB
open Cil

type t = Entry | Node of int | Exit

let compare = compare

let equal n1 n2 =
  match n1, n2 with
  | Entry, Entry -> true
  | Exit, Exit -> true
  | Node i1, Node i2 -> i1 = i2
  | _, _ -> false

let hash = Hashtbl.hash

let nid = ref 0

(* NOTE: The note_map argument is a map from cil node to FIntraNode.t.
   It will be used when desugaring if statements. *)
let node_map = ref IntMap.empty

let make () = nid := !nid + 1; Node !nid

let init_node_env () = nid := 0; node_map := IntMap.empty

let node_of_stmt s =
  try IntMap.find s.sid !node_map with Not_found ->
    let new_node = make () in
    node_map := IntMap.add s.sid new_node !node_map;
    new_node

let string_of = function
  | Entry -> "Entry"
  | Exit -> "Exit"
  | Node i -> string_of_int i
