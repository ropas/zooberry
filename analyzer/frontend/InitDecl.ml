(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** Initialize declaration *)

open VocabA
open Cil
open FSyn
open FIntraCfg

let rec add_explicit_init lv i loc (g, tail) =
  let add_explicit_init' (offset, init) (g, tail) =
    let lv = addOffsetLval offset lv in
    add_explicit_init lv init loc (g, tail) in
  match i with
  | SingleInit exp -> push_cmd_node (Cmd.Cset (lv, exp, loc)) (g, tail)
  | CompoundInit (typ, ilist) -> list_fold add_explicit_init' ilist (g, tail)

(* Add simple for loop of

   for(idx = 0; idx < iter; i++){
     lv[idx] = work;
   }
 *)
let add_simple_for_loop iter lv work loc (g, tail) =
  let idx = var (makeTempVar g.fun_dec intType) in
  let init_cmd = Cmd.Cset (idx, zero, loc) in
  let incr_cmd = Cmd.Cset (idx, BinOp (PlusA, Lval idx, one, intType), loc) in
  let cond = BinOp (Lt, Lval idx, iter, intType) in
  let assume_cmd = Cmd.Cassume (cond, loc) in
  let nassume_cmd = Cmd.Cassume (UnOp (LNot, cond, intType), loc) in
  let lv' = addOffsetLval (Index (Lval idx, NoOffset)) lv in
  let (g, skip_node) =
    (g, tail)
    |> push_cmd_node init_cmd   (* idx = 0 *)
    |> push_cmd_node Cmd.Cskip in
  let (g, incr_node) =
    (g, skip_node)
    |> push_cmd_node assume_cmd  (* assume (idx < size) *)
    |> work lv'                  (* do something *)
    |> push_cmd_node incr_cmd in (* idx++ *)
  let g = add_edge incr_node skip_node g in
  push_cmd_node nassume_cmd (g, skip_node) (* assume (!(idx < size)) *)

let rec need_decl is_G = function
  | TInt _
  | TFloat _ -> is_G
  | TArray (_, Some _, _) -> true
  | TComp (ci, _) -> need_decl_fields is_G ci.cfields
  | TNamed (typeinfo, _) -> need_decl is_G typeinfo.ttype
  | _ -> false

and need_decl_fields is_G fieldinfos =
  List.exists (need_decl_field is_G) fieldinfos

and need_decl_field is_G fieldinfo = need_decl is_G fieldinfo.ftype

let rec init_var_decl is_G lv loc (g, tail) =
  init_var_decl_typed is_G (typeOfLval lv) lv loc (g, tail)

and init_var_decl_typed is_G typ lv loc (g, tail) =
  match typ with
  | TInt _
  | TFloat _ ->
    if is_G then push_cmd_node (Cmd.Cset (lv, zero, loc)) (g, tail) else
      (g, tail)
  | TArray (inner_typ, Some size, _) ->
    let (g, tail) = push_alloc_cmd_node lv inner_typ size loc (g, tail) in
    if need_decl is_G inner_typ then
      let work lv' = init_var_decl_typed is_G inner_typ lv' loc in
      add_simple_for_loop size lv work loc (g, tail)
    else (g, tail)
  | TComp (ci, _) -> init_fields is_G lv ci.cfields (g, tail)
  | TNamed (typeinfo, _) ->
    init_var_decl_typed is_G typeinfo.ttype lv loc (g, tail)
  | _ -> (g, tail)

and init_fields is_G lv fieldinfos (g, tail) =
  list_fold (init_field is_G lv) fieldinfos (g, tail)

and init_field is_G lv fieldinfo (g, tail) =
  if need_decl is_G fieldinfo.ftype then
    let lv' = addOffsetLval (Field (fieldinfo, NoOffset)) lv in
    init_var_decl_typed is_G fieldinfo.ftype lv' fieldinfo.floc (g, tail)
  else (g, tail)

let rec init_var is_G lv i loc (g, tail) =
  match i.init with
  | None -> init_var_decl is_G lv loc (g, tail)
  | Some (SingleInit _ as init) ->
    add_explicit_init lv init loc (g, tail) (* TODO: no init_gvar_decl here? *)
  | Some (CompoundInit _ as init) ->
    (g, tail)
    |> init_var_decl is_G lv loc
    |> add_explicit_init lv init loc

let run' is_G varinfo (g, tail) =
  init_var is_G (var varinfo) varinfo.vinit varinfo.vdecl (g, tail)

let run is_G (g, tail) =
  list_fold (run' is_G) g.fun_dec.slocals (g, tail)
  
