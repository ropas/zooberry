(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** Step print manager *)

open VocabB

let make_istr x = hr ^ "\n" ^ x ^ "\n" ^ hr ^ "\n"

let step size title fn i =
  let t0 = Sys.time() in
  if size then prerr_endline (make_istr (title ^ " begins...")) else
    prerr_endline (title ^ " begins...");
  let v = fn i in
  Printf.eprintf "%s completes: %.1f sec\n" title (Sys.time() -. t0);
  prerr_newline ();
  v
(** big step of process *)
let big title fn i = step true title fn i
(** small step of process *)
let small title fn i = step false title fn i

let step_opt b size title fn i = if b then step size title fn i else i
(** optional big step of process *)
let big_opt b title fn i = step_opt b true title fn i
(** optional small step of process *)
let small_opt b title fn i = step_opt b false title fn i

let step_side b size title fn i = if b then step size title fn i
(** big step of process with only side effect *)
let big_side b title fn i = step_side b true title fn i
(** small step of process with only side effect *)
let small_side b title fn i = step_side b false title fn i
