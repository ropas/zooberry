(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** Initialize _G_ *)

open VocabA
open VocabB
open Cil
open FSyn
open FIntraCfg

let global_fname = "_G_"

let global_fd = emptyFunction global_fname

let init_fun_decl fd loc (g, tail) =
  push_cmd_node (Cmd.Cfalloc (var fd.svar, fd, loc)) (g, tail)

let is_main = function
  | GFun (fd, _) -> fd.svar.vname = "main"
  | _ -> false

let get_main_dec globals =
  match List.find is_main globals with
  | GFun (fd, loc) -> (fd, loc)
  | exception Not_found -> failwith "Main function is not found"
  | _ -> assert false

let add_main_call (main_dec, main_loc) (g, tail) =
  let argc = var (makeTempVar g.fun_dec intType) in
  let argc_cmd = Cmd.Cexternal (argc, main_loc) in
  let assume_argc_cmd =
    Cmd.Cassume (BinOp (Ge, Lval argc, one, intType), main_loc) in
  let argv = var (makeTempVar g.fun_dec (TPtr (intPtrType, []))) in
  let argv_cmd = Cmd.Calloc (argv, Cmd.Array (Lval argc), main_loc) in
  let alloc_argv_cmd = Cmd.Cexternal (mkMem (Lval argv) NoOffset, main_loc) in
  let main, arguments = Lval (var main_dec.svar), [Lval argc; Lval argv] in
  let call_cmd = Cmd.Ccall (None, main, arguments, main_loc) in
  let cmds = [argc_cmd; assume_argc_cmd; argv_cmd; alloc_argv_cmd; call_cmd] in
  push_cmd_nodes cmds (g, tail)

let init_global_lib main_loc (g, tail) =
  let optind = (Var (makeGlobalVar "optind" intType), NoOffset) in
  let optarg = (Var (makeGlobalVar "optarg" charPtrType), NoOffset) in
  let optind_cmd = Cmd.Cexternal (optind, main_loc) in
  let optarg_cmd = Cmd.Cexternal (optarg, main_loc) in
  let progname = (Var (makeGlobalVar "__progname" charPtrType), NoOffset) in
  let progname_cmd = Cmd.Cexternal (progname, main_loc) in
  push_cmd_nodes [optind_cmd; optarg_cmd; progname_cmd] (g, tail)

let init_global_decl global (g, tail) =
  match global with
  | GVar (x, init, loc) -> InitDecl.init_var true (var x) init loc (g, tail)
  | GVarDecl (x, loc) -> InitDecl.init_var_decl true (var x) loc (g, tail)
  | GFun (fd, loc) -> init_fun_decl fd loc (g, tail)
  | _ -> (g, tail)

let init_global_decls globals (g, tail) =
  list_fold init_global_decl globals (g, tail)

let run_intra globals =
  let (main_dec, main_loc) = get_main_dec globals in
  let (g, tail) =
    (empty global_fd, FIntraNode.Entry)
    |> init_global_decls globals
    |> init_global_lib main_loc
    |> add_main_call (main_dec, main_loc) in
  let g = add_edge tail FIntraNode.Exit g in
  g
  |> InitSalloc.run
  |> remove_empty_nodes
  |> InitFun.insert_return_nodes

let run file cfgs =
  let cfg = run_intra file.globals in
  InterCfg.PidMap.add global_fname cfg cfgs
