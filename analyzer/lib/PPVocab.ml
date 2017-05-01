(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** Pretty print vocabulary *)

open Format

let print_opt print_x x_opt =
  open_box 0;
  (match x_opt with
   | None -> print_string "None"
   | Some x ->
     print_string "Some";
     print_space ();
     print_x x
  );
  close_box ()

let string_of_opt string_of_x x_opt =
  match x_opt with
  | None -> "None"
  | Some x -> "Some " ^ string_of_x x

let print_list first last sep print_x x_list =
  let rec print_list' x_list =
    match x_list with
    | [] -> invalid_arg "list should not be empty"
    | [x] -> print_x x
    | x :: tl ->
      print_x x;
      print_string sep;
      print_space ();
      print_list' tl in
  open_box (String.length first);
  print_string first;
  (match x_list with
   | [] -> ()
   | _ -> print_list' x_list;
  );
  print_string last;
  close_box ()

let string_of_list first last sep string_of_x x_list =
  let rec string_of_list' x_list =
    match x_list with
    | [] -> invalid_arg "list should not be empty"
    | [x] -> string_of_x x
    | x :: tl -> string_of_x x ^ sep ^ " " ^ string_of_list' tl
  in
  first
  ^ (match x_list with
      | [] -> ""
      | _ -> string_of_list' x_list
    )
  ^ last

let print_int_opt i_opt = print_opt print_int i_opt

let string_of_int_opt i_opt = string_of_opt string_of_int i_opt

let pp_string print x = print x; print_flush ()
let pp_endline print x = pp_string print x; Pervasives.prerr_newline ()
