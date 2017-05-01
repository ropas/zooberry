(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** Pretty print of IL *)

open VocabA
open PPVocab
open Format

let string_of_intra_node node =
  match node with
  | IntraNode.Entry -> "entry"
  | IntraNode.Exit -> "exit"
  | IntraNode.Node i -> "node" ^ string_of_int i

let print_intra_node node = print_string (string_of_intra_node node)

let string_of_inter_node (f, node) =
  "(" ^ f ^ ", " ^ string_of_intra_node node ^ ")"

let print_inter_node (f, node) = print_string (string_of_inter_node (f, node))

let string_of_const c =
  match c with
  | Syn.CInt64 None -> "[-oo,+oo]"
  | Syn.CInt64 (Some i) -> string_of_int i
  | Syn.CChr c -> "CChr(" ^ string_of_int c ^ ")"
  | Syn.CReal (lb, ub) ->
    "CReal[" ^ string_of_int lb ^ "," ^ string_of_int ub ^ "]"
  | Syn.CEnum -> "CEnum"

let string_of_unop u =
  match u with
  | Syn.Neg -> "-"
  | Syn.BNot -> "~"
  | Syn.LNot -> "!"

let string_of_binop b =
  match b with
  | Syn.PlusA -> "+"
  | Syn.PlusPI -> "+PI"
  | Syn.IndexPI -> "+IdxPI"
  | Syn.MinusA -> "-"
  | Syn.MinusPI -> "-PI"
  | Syn.MinusPP -> "-PP"
  | Syn.Mult -> "*"
  | Syn.Div -> "/"
  | Syn.Mod -> "%"
  | Syn.Shiftlt -> "<<"
  | Syn.Shiftrt -> ">>"
  | Syn.Lt -> "<"
  | Syn.Gt -> ">"
  | Syn.Le -> "<="
  | Syn.Ge -> ">="
  | Syn.Eq -> "=="
  | Syn.Ne -> "!="
  | Syn.BAnd -> "&"
  | Syn.BXor -> "^"
  | Syn.BOr -> "|"
  | Syn.LAnd -> "&&"
  | Syn.LOr -> "||"

let rec string_of_char_list s =
  match s with
  | [] -> ""
  | c :: tl -> Char.escaped c ^ string_of_char_list tl

(** If need_paren is true and the e expression is complicated, the
    returned expression should be parenthesized. *)
let rec string_of_exp need_paren e =
  match e with
  | Syn.Const (c, _) -> string_of_const c
  | Syn.Lval (lv, _) -> string_of_lval need_paren lv
  | Syn.SizeOf (i_opt, _) -> "SizeOf(" ^ string_of_int_opt i_opt ^ ")"
  | Syn.SizeOfE (i_opt, _) -> "SizeOfE(" ^ string_of_int_opt i_opt ^ ")"
  | Syn.SizeOfStr (s, _) -> "SizeOfStr(\"" ^ string_of_char_list s ^ "\")"
  | Syn.AlignOf (i, _) -> "AlignOf(" ^ string_of_int i ^ ")"
  | Syn.AlignOfE (e, _) -> "AlignOfE(" ^ string_of_exp false e ^ ")"
  | Syn.UnOp (u, e, _) ->
    let s = string_of_unop u ^ string_of_exp true e in
    if need_paren then "(" ^ s ^ ")" else s
  | Syn.BinOp (b, e1, e2, _) ->
    let s = string_of_exp true e1 ^ " " ^ string_of_binop b ^ " "
            ^ string_of_exp true e2 in
    if need_paren then "(" ^ s ^ ")" else s
  | Syn.Question (c, e_true, e_false, _) ->
    let s = string_of_exp true c ^ " ? " ^ string_of_exp true e_true ^ " : "
            ^ string_of_exp true e_false in
    if need_paren then "(" ^ s ^ ")" else s
  | Syn.CastE (i_opt, e, _) ->
    "CastE(" ^ string_of_int_opt i_opt ^ ", " ^ string_of_exp false e ^ ")"
  | Syn.AddrOf (lv, _) -> "&" ^ string_of_lval true lv
  | Syn.StartOf (lv, _) -> "StartOf(" ^ string_of_lval false lv ^ ")"

and string_of_lval need_paren lv =
  match lv with Syn.Coq_lval_intro (lh, o, _) ->
    let s = string_of_lhost lh ^ string_of_offset o in
    if need_paren && o <> Syn.NoOffset then "(" ^ s ^ ")" else s

and string_of_lhost lh =
  match lh with
  | Syn.VarLhost (x, is_global) -> (if is_global then "@" else "") ^ x
  | Syn.MemLhost e -> "*" ^ string_of_exp true e

and string_of_offset o =
  match o with
  | Syn.NoOffset -> ""
  | Syn.FOffset (f, o) -> "." ^ f ^ string_of_offset o
  | Syn.IOffset (i, o) -> "[" ^ string_of_exp false i ^ "]" ^ string_of_offset o

let string_of_alloc a = string_of_exp false a
let string_of_args args = string_of_list "(" ")" "," (string_of_exp false) args

let string_of_cmd c =
  match c with
  | Syn.Cset (lv, e, _) -> string_of_lval false lv ^ " := " ^ string_of_exp false e
  | Syn.Cexternal (lv, _) -> "extern " ^ string_of_lval false lv
  | Syn.Calloc (lv, a, _) ->
    string_of_lval false lv ^ " := alloc(" ^ string_of_alloc a ^ ")"
  | Syn.Csalloc (lv, s, _) ->
    string_of_lval false lv ^ " := \"" ^ string_of_char_list s ^ "\""
  | Syn.Cfalloc (lv, name, _) -> string_of_lval false lv ^ " := function " ^ name
  | Syn.Cassume (e, _) -> "assume(" ^ string_of_exp false e ^ ")"
  | Syn.Ccall (None, f, args, _) -> string_of_exp true f ^ string_of_args args
  | Syn.Ccall (Some lv, f, args, _) ->
    string_of_lval false lv ^ " := " ^ string_of_exp true f
    ^ string_of_args args
  | Syn.Creturn (None, _) -> "return";
  | Syn.Creturn (Some e, _) -> "return " ^ string_of_exp false e
  | Syn.Casm _ -> "asm"
  | Syn.Cskip _ -> "skip"

let print_cmd c = print_string (string_of_cmd c)

let print_cmds cmds =
  let print_node_cmd node cmd n =
    print_intra_node node;
    print_string " ";
    print_cmd cmd;
    if n > 1 then print_cut ();
    n - 1 in
  open_vbox 0;
  let n = IntraCfg.NodeMap.cardinal cmds in
  ignore (IntraCfg.NodeMap.fold print_node_cmd cmds n);
  close_box ()

let print_cmds_from_cfg cfg = print_cmds (IntraCfg.cmds cfg)

let print_cmds_from_cfgs cfgs =
  let print_pid_cfg pid cfg n =
    print_string "Function ";
    print_string pid;
    print_break 1 2;
    print_cmds_from_cfg cfg;
    if n > 1 then print_cut ();
    n - 1 in
  open_vbox 0;
  let n = InterCfg.PidMap.cardinal cfgs in
  ignore (InterCfg.PidMap.fold print_pid_cfg cfgs n);
  close_box ()

let print_cmds_from_icfg icfg = print_cmds_from_cfgs (InterCfg.cfgs icfg)
