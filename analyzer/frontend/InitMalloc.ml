(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** Transform malloc to Calloc *)

open VocabA
open Cil
open FSyn
open FIntraCfg

let is_malloc name = name = "malloc" || name = "__builtin_alloca"

(* Returns lv when it is casted from src. *)
let cast_follow n src g =
  match succs_of n g with
  | [succ] ->
    ( match find_cmd succ g with
      | Cmd.Cset (lv, CastE (_, Lval src'), _) when src = src' -> Some lv
      | _ -> None )
  | _ -> None

let simple_trans lv e loc n g = set_cmd n (Cmd.Cset (lv, e, loc)) g

let is_typical_form = function
  | BinOp (Mult, SizeOf _, _, _)
  | BinOp (Mult, _, SizeOf _, _)
  | SizeOf _
  | CastE (_, SizeOf _)
  | SizeOfE _ -> true
  | _ -> false

let trans_malloc lv e loc (g, tail) =
  match e with
  | BinOp (Mult, SizeOf typ, size, _)
  | BinOp (Mult, size, SizeOf typ, _) ->
    let array_typ = TArray (typ, Some size, []) in
    InitDecl.init_var_decl_typed false array_typ lv loc (g, tail)
  | SizeOf typ
  | CastE (_, SizeOf typ) ->
    InitDecl.init_var_decl_typed false typ lv loc (g, tail)
  | SizeOfE e' ->
    InitDecl.init_var_decl_typed false (typeOf e') lv loc (g, tail)
  | _ -> invalid_arg "malloc is added only when typical form"

let run' n g =
  match find_cmd n g with
  | Cmd.Ccall (Some lv, Lval (Var varinfo, _), args, loc) ->
    if is_malloc varinfo.vname then
      let e = List.hd args in
      if is_typical_form e then
        match cast_follow n lv g with
        | Some lv' ->
          let preds = preds_of n g in
          let cast_of_n = List.hd (succs_of n g) in
          let succs = succs_of (List.hd (succs_of n g)) g in
          let g = remove_edges_from n g in
          let (g, tail) = trans_malloc lv' e loc (g, n) in
          ( match List.hd (succs_of n g) with
            | head ->
              g
              |> list_fold (fun p -> add_edge p head) preds
              |> list_fold (fun s -> add_edge tail s) succs
              |> remove_nodes [n; cast_of_n]
            | exception Failure _ -> (* Type is complicated *)
              g
              |> list_fold (fun s -> add_edge n s) succs
              |> simple_trans lv e loc n
          )
        | None -> simple_trans lv e loc n g
      else simple_trans lv e loc n g
    else g
  | _ -> g
  | exception Not_found_cmd -> g (* Removed cast node may not be found. *)

(** It initializes allocations by the malloc/__builtin_alloca
    functions when,

    1. The argument of malloc has a typical form we know.
    2. A cast node follows the malloc node.
*)
let run g = modify_on_nodes run' g
