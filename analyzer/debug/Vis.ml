(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
open VocabA
open VocabB
open PPVocab
open UserInput.Input
open PPIL
open Syn
open Pos
open Global

let dir = "vis_result"
let callgraph_file = "__callgraph"
let dot_path s = dir ^ "/" ^ s ^ ".dot"
let svg_path_file s = s ^ ".svg"
let svg_path s = dir ^ "/" ^ s ^ ".svg"

let make_dir () =
  try Unix.mkdir dir 0o755 with
  | Unix.Unix_error (Unix.EEXIST, _, _) -> ()
  | e -> raise e

let make_dot_file file contents =
  let dot_intro graph_name =
    Format.print_string ("digraph " ^ graph_name ^ " {");
    Format.print_cut ();
    Format.print_string "node [shape=box];";
    Format.print_cut () in
  let dot_ending () = Format.print_string "}" in
  let chan = open_out (dot_path file) in
  Format.set_formatter_out_channel chan;
  Format.open_vbox 0;
  dot_intro file;
  contents ();
  dot_ending ();
  Format.close_box ();
  Format.print_newline ();
  close_out chan;
  Format.set_formatter_out_channel stderr

let make_svg src tgt =
  Unix.create_process "dot" [|"dot"; "-Tsvg"; "-o" ^ tgt; src|]
    Unix.stdin Unix.stdout Unix.stderr
  |> ignore;
  Unix.wait () |> ignore

let dump_nodes f cfg =
  let print_node node _ =
    let cmd = default (Syn.Cskip unknown_pos) (IntraCfg.get_cmd cfg node) in
    let callnode = IntraCfg.is_call_node cfg node in
    let node_string = string_of_intra_node node in
    let s = node_string ^ " [label=\"" ^ node_string ^ ": "
            ^ (if IntraNode.is_entry_node node then
                 f ^ string_of_list "(" ")" "," id (IntraCfg.args cfg)
               else String.escaped (string_of_cmd cmd))
            ^ "\""
            ^ (if callnode then " style=filled color=grey" else "")
            ^ "];" in
    Format.print_string s;
    Format.print_cut () in
  IntraCfg.NodeSet.fold print_node (IntraCfg.nodes cfg) ()

let dump_edges f cfg =
  let print_edge node succ _ =
    let s = string_of_intra_node node ^ " -> " ^ string_of_intra_node succ
            ^ ";" in
    Format.print_string s;
    Format.print_cut () in
  let print_succs node succs _ =
    IntraCfg.NodeSet.fold (print_edge node) succs () in
  IntraCfg.NodeMap.fold print_succs (IntraCfg.succ cfg) ()

let make_f_dot f cfg =
  let contents () =
    dump_nodes f cfg;
    Format.print_cut ();
    dump_edges f cfg in
  make_dot_file f contents

let dump_cg_nodes cfgs =
  let print_f_node f _ _ =
    let s = f ^ " [URL=\"" ^ svg_path_file f ^ "\"];" in
    Format.print_string s;
    Format.print_cut () in
  InterCfg.PidMap.fold print_f_node cfgs ()

let dump_cg_edges cg =
  let print_call caller callee _ =
    let s = caller ^ " -> " ^ callee ^ ";" in
    Format.print_string s;
    Format.print_cut () in
  let print_callees caller callees _ =
    InterCfg.PidSet.fold (print_call caller) callees () in
  InterCfg.PidMap.fold print_callees (Callgraph.calls cg) ()

let make_cg_dot cfgs cg =
  let contents () = dump_cg_nodes cfgs; dump_cg_edges cg in
  make_dot_file callgraph_file contents

let vis_f f cfg _ =
  prerr_endline ("Visualize: " ^ f);
  make_f_dot f cfg;
  make_svg (dot_path f) (svg_path f)

let vis_callgraph cfgs cg =
  make_cg_dot cfgs cg;
  make_svg (dot_path callgraph_file) (svg_path callgraph_file)

let run g f =
  make_dir ();
  match InterCfg.PidMap.find f (InterCfg.cfgs (G.icfg g)) with
  | None -> prerr_endline ("No function:" ^ f)
  | Some cfg -> vis_f f cfg ()

let run_all g =
  let cfgs = InterCfg.cfgs (G.icfg g) in
  make_dir ();
  InterCfg.PidMap.fold vis_f cfgs ();
  vis_callgraph cfgs (G.callgraph g);
  ()
