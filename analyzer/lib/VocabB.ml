(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** Vocabularies *)

let id x = x

(* This applies [List.fold_left], but the argument type is the same
   with [PSet.fold]. *)
let list_fold f list init = List.fold_left (fun acc x -> f x acc) init list

let list_rev l =
  let rec list_rev_rec l1 l2 =
    match l1 with
    | [] -> l2
    | a :: b -> list_rev_rec b (a :: l2) in
  list_rev_rec l []

let get_some = function
  | Some v -> v
  | None -> invalid_arg "None value"

let apply_opt f = function
  | Some x -> Some (f x)
  | None -> None

let prerr_progressbar ?(itv = 1) n total =
  let width = 40 in
  if !Options.opt_nobar then () else
  if n mod itv = 0 || n = total then
    let v = n * width / total in
    let u = width - v in
    let rec ps f s n = if n = 0 then () else (f s; ps f s (n - 1)) in
    prerr_string("\r  [");
    ps prerr_string "=" v;
    ps prerr_string "." u;
    prerr_string("] (" ^ string_of_int n ^ "/" ^ string_of_int total ^ ")");
    if n = total then prerr_newline ();
    flush stderr
  else ()

let prerr_memory_usage () =
  let stat = Gc.stat () in
  let kB_of_word w = w * Sys.word_size / 1000 / 8 in
  let live_kB = kB_of_word stat.Gc.live_words in
  prerr_endline ("live memory : " ^ string_of_int live_kB ^ " kB")

let hr =
  "----------------------------------------------------------------------"

let of_coq_compare coq_compare =
  fun x y ->
    match coq_compare x y with
    | OrderedType.LT -> -1
    | OrderedType.EQ -> 0
    | OrderedType.GT -> 1

(* CAUTION: The Key.t type should be hashable by the default hash
   function, Hashtbl.hash. *)
module Key2Ordered (Key : DLat.KEY) = struct
  type t = Key.t
  let compare = of_coq_compare Key.compare
  let equal = Key.eq_dec
  let hash = Hashtbl.hash
end

(* The Int module is already defined in Coq. *)
module IntB = struct type t = int let compare = compare end

module IntSet = Set.Make (IntB)

module IntMap = Map.Make (IntB)
