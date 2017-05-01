(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
let max_sections = 30

let check_point = ref (Sys.time ())
let sections = ref (Array.make max_sections 0.0)
let cur_section = ref 0

let add_time_diff i time =
  let acc = Array.get !sections i +. time in
  Array.set !sections i acc

let start () =
  cur_section := 0;
  check_point := Sys.time ()

let next () =
  let cur_time = Sys.time () in
  let time_diff = cur_time -. !check_point in
  add_time_diff !cur_section time_diff;
  cur_section := !cur_section + 1;
  check_point := cur_time

let finish () = next ()

let flush () =
  let rec print_profile_result_rec i n =
    if i >= n then () else
      (Printf.eprintf "section %d : %.1f sec\n" i (Array.get !sections i);
       print_profile_result_rec (i + 1) n) in
  prerr_endline "Profile results";
  print_profile_result_rec 0 !cur_section;
  sections := Array.make max_sections 0.0

let reset () = sections := Array.make max_sections 0.0

let check_point () =
  let cur_time = Sys.time () in
  let time_diff = cur_time -. !check_point in
  prerr_endline ("check point : " ^ string_of_float time_diff);
  check_point := cur_time
