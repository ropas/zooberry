(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** Debugging tool *)

open VocabA
open VocabB
open UserInputType
open UserInput.Input
open Vali.Vali
open Syn
open Pos
open Global

type table = Input | Output | DInput | DOutput

type dbg_cmd =
  | Mem of table * InterNode.t
  | MemFI
  | Cmd of InterNode.t
  | CF of InterNode.t
  | DU_from of InterNode.t
  | DU_to of InterNode.t
  | Access of Syn.pid_t
  | Help
  | Exit
  | Skip
  | VisAll
  | Vis of Syn.pid_t

exception Invalid_dbg
exception Invalid_loc

let prerr_error_msg () = prerr_endline
    "ERROR: Debug command is invalid.  Type \"help\" to see valid commands."

let prerr_loc_error_msg () = prerr_endline
    "ERROR: Location number is invalid."

let print_help () = print_endline "\
help                   Print help documents.
exit                   Exit debugging mode.
[TABLE] [FID] [NODE]   Print a memory.
memFI                  Print the flow insensitive analysis result.
cmd [FID] [NODE]       Print command of a node.
cf [FID] [NODE]        Print control flow edges of the node.
du_from [FID] [NODE]   Print def/use edges from the node.
du_to [FID] [NODE]     Print def/use edges to the node.
access [FID]           Print accessibility.
visall                 Visulaize all functions
vis [FID]              Visualize a function

TABLE
    oi                 Original input
    oo                 Original output
    di                 Densified input
    do                 Densified output

FID
    [string]           Function name

NODE
    entry              Entry node
    exit               Exit node
    [number]           Node number"

(** Parsing debug command *)

let read_table t =
  if t = "oi" then Input else
  if t = "oo" then Output else
  if t = "di" then DInput else
  if t = "do" then DOutput else
    raise Invalid_dbg

let read_node fname node =
  if node = "entry" then (fname, IntraNode.Entry) else
  if node = "exit" then (fname, IntraNode.Exit) else
    let i =
      try int_of_string node with
      | Failure _ -> raise Invalid_dbg in
    (fname, IntraNode.Node i)

let read_dbg_cmd () =
  print_string "Input debug command (\"help\" for commands): ";
  flush_all ();
  let str = read_line () in
  match Str.split (Str.regexp " ") str with
  | t :: [] when t = "help" -> Help
  | t :: [] when t = "exit" -> Exit
  | t :: [] when t = "memFI" -> MemFI
  | t :: [] when t = "visall" -> VisAll
  | t :: fname :: [] when t = "vis" -> Vis fname
  | t :: fname :: node :: []
    when t = "oi" || t = "oo" || t = "di" || t = "do" ->
    Mem (read_table t, read_node fname node)
  | t :: fname :: node :: [] when t = "cmd" ->
    Cmd (read_node fname node)
  | t :: fname :: node :: [] when t = "du_from" ->
    DU_from (read_node fname node)
  | t :: fname :: node :: [] when t = "du_to" ->
    DU_to (read_node fname node)
  | t :: fname :: node :: [] when t = "cf" ->
    CF (read_node fname node)
  | t :: fname :: [] when t = "access" -> Access fname
  | _ -> raise Invalid_dbg

(** Pretty print functions *)

let print_keys s elems n =
  let rec print_keys' elems n =
    match elems with
    | [] -> ()
    | (l, _) :: tl ->
      Format.print_int n;
      Format.print_string ":";
      PPMem.print_loc l;
      Format.print_space ();
      print_keys' tl (n + 1) in
  Format.open_box 0;
  Format.print_string ("Location entries (" ^ s ^ "): ");
  Format.print_space ();
  print_keys' elems n;
  Format.close_box ()

let query_loc m =
  let elems = Mem.elements m in
  let size = List.length elems in
  PPVocab.pp_endline (print_keys "keys" elems) 0;
  print_string "Input location number, or empty for all locations: ";
  flush_all ();
  let str = read_line () in
  if str = "" then None else
    match int_of_string str with
    | i ->
      if 0 <= i && i < size then Some (snd (List.nth elems i)) else
        raise Invalid_loc
    | exception (Failure _) -> raise Invalid_loc

let query_mem m =
  try
    let val_opt = query_loc m in
    (match val_opt with
     | None -> PPVocab.pp_endline PPMem.print_mem m
     | Some v -> PPVocab.pp_endline PPMem.print_val v)
  with Invalid_loc -> prerr_loc_error_msg ()

let print_du (node1, node2, abslocs) =
  Format.open_box 0;
  PPIL.print_inter_node node1;
  Format.print_string "->";
  PPIL.print_inter_node node2;
  Format.print_string ":";
  PPMem.print_pow_loc abslocs

let print_dus dus =
  let rec print_dus' dus =
    match dus with
    | [] -> ()
    | du :: tl -> PPVocab.pp_endline print_du du; print_dus' tl in
  Format.open_vbox 0;
  print_dus' dus;
  Format.close_box ()

let get_preds node inter_succ intra_succ =
  let f = InterNode.get_pid node in
  let intra_node = InterNode.get_node node in
  let filter_inter k v acc =
    if InterCfg.NodeSet.mem node v then k :: acc else acc in
  let filter_intra k v acc =
    if IntraCfg.NodeSet.mem intra_node v then (f, k) :: acc else acc in
  []
  |> InterCfg.NodeMap.fold filter_inter inter_succ
  |> IntraCfg.NodeMap.fold filter_intra intra_succ
  |> List.rev  

let get_succs node inter_succ intra_succ =
  let f = InterNode.get_pid node in
  let node' = InterNode.get_node node in
  let inter_succs =
    default InterCfg.NodeSet.empty (InterCfg.NodeMap.find node inter_succ) in
  let intra_succs =
    default IntraCfg.NodeSet.empty (IntraCfg.NodeMap.find node' intra_succ) in
  InterCfg.NodeSet.elements inter_succs @
  List.map (fun n -> (f, n)) (IntraCfg.NodeSet.elements intra_succs)

let print_inter_nodes nodes =
  PPVocab.print_list "{" "}" "," PPIL.print_inter_node nodes

(** Main debug query processor *)

let rec debug (g, memFI, access_map, dug, io, oo, d_io, d_oo) =
  let dbg_cmd =
    try read_dbg_cmd () with Invalid_dbg ->
      prerr_error_msg ();
      Skip in
  let continue =
    match dbg_cmd with
    | Mem (t, node) ->
      let tbl =
        match t with
        | Input -> io
        | Output -> oo
        | DInput -> d_io
        | DOutput -> d_oo in
      let m = default Mem.bot (Table.find node tbl) in
      query_mem m; true
    | MemFI -> query_mem memFI; true
    | Cmd node ->
      (try
         let icfg = G.icfg g in
         let cmd = default (Syn.Cskip unknown_pos) (InterCfg.get_cmd icfg node) in
         PPVocab.pp_endline PPIL.print_cmd cmd
       with _ -> prerr_endline "No command."); true
    | CF node ->
      (try
         let icfg = G.icfg g in
         let cfgs = InterCfg.cfgs icfg in
         let inter_succ = InterCfg.succ icfg in
         let f = InterNode.get_pid node in
         let cfg = get_some (InterCfg.PidMap.find f cfgs) in
         let intra_succ = IntraCfg.succ cfg in
         let preds = get_preds node inter_succ intra_succ in
         let succs = get_succs node inter_succ intra_succ in
         let print_title_nodes title nodes =
           Format.open_box 2;
           Format.print_string (title ^ ": ");
           print_inter_nodes nodes;
           Format.close_box () in
         PPVocab.pp_endline (print_title_nodes "Preds") preds;
         PPVocab.pp_endline (print_title_nodes "Succs") succs;
         Format.print_flush ()
       with _ -> prerr_endline "No control flows."); true
    | DU_from node ->
      let succs = Dug.succ node dug in
      let make_dus_succ succ =
        let abslocs = Dug.get_abslocs node succ dug in
        (node, succ, abslocs) in
      let dus = List.map make_dus_succ succs in
      PPVocab.pp_endline print_dus dus; true
    | DU_to node ->
      let preds = Dug.pred node dug in
      let make_dus_pred pred =
        let abslocs = Dug.get_abslocs pred node dug in
        (pred, node, abslocs) in
      let dus = List.map make_dus_pred preds in
      PPVocab.pp_endline print_dus dus; true
    | Access f ->
      let def = get_def_access f access_map in
      let use = get_use_access f access_map in
      let print_access s a =
        Format.open_box 0;
        Format.print_string (s ^ ": ");
        PPMem.print_pow_loc a;
        Format.close_box () in
      PPVocab.pp_endline (print_access "Def") def;
      PPVocab.pp_endline (print_access "Use") use; true
    | Help -> print_help (); true
    | Exit -> false
    | Skip -> true
    | VisAll -> Vis.run_all g; true
    | Vis f -> Vis.run g f; true in
  if continue then
    debug (g, memFI, access_map, dug, io, oo, d_io, d_oo)
  else ()
