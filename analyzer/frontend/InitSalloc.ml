(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** Translate string use to Salloc *)

open VocabA
open VocabB
open Cil
open FSyn
open FIntraCfg

module CilStr = struct
  type t =
    | Normal of string
    | Wide of int64 list
  let compare = compare
end

module CilStrSet = Set.Make (CilStr)

module CilStrMap = Map.Make (CilStr)

(* NOTE: CWStr is not supported. *)
let rec strings_in_exp = function
  | Const c -> strings_in_constant c
  | AddrOf l
  | StartOf l
  | Lval l -> strings_in_lval l
  | SizeOfE e
  | AlignOfE e
  | UnOp (_, e, _)
  | CastE (_, e) -> strings_in_exp e
  | BinOp (_, e1, e2, _) ->
    CilStrSet.union (strings_in_exp e1) (strings_in_exp e2)
  | Question (e1, e2, e3, _) ->
    CilStrSet.union
      (CilStrSet.union (strings_in_exp e1) (strings_in_exp e2))
      (strings_in_exp e3)
  | _ -> CilStrSet.empty

and strings_in_lval = function
  | (Mem e, _) -> strings_in_exp e
  | _ -> CilStrSet.empty

and strings_in_constant = function
  | CStr s -> CilStrSet.singleton (CilStr.Normal s)
  | CWStr ws -> CilStrSet.singleton (CilStr.Wide ws)
  | CEnum (e, _, _) -> strings_in_exp e
  | _ -> CilStrSet.empty

let strings_in_alloc = function
  | Cmd.Array e -> strings_in_exp e

let strings_in_opt_exp opte =
  default CilStrSet.empty (apply_opt strings_in_exp opte)

let strings_in_opt_lval optl =
  default CilStrSet.empty (apply_opt strings_in_lval optl)

let strings_in_exps es =
  list_fold (fun e -> CilStrSet.union (strings_in_exp e)) es CilStrSet.empty

let strings_in_cmd = function
  | Cmd.Cinstr _
  | Cmd.Cif _
  | Cmd.CLoop _ -> assert false
  | Cmd.Cset (l, e, _) ->
    CilStrSet.union (strings_in_lval l) (strings_in_exp e)
  | Cmd.Cexternal (l, _) -> strings_in_lval l
  | Cmd.Calloc (l, a, _) ->
    CilStrSet.union (strings_in_lval l) (strings_in_alloc a)
  | Cmd.Csalloc (l, _, _) -> strings_in_lval l
  | Cmd.Cfalloc (l, _, _) -> strings_in_lval l
  | Cmd.Cassume (e, _) -> strings_in_exp e
  | Cmd.Ccall (optl, e, es, loc) ->
    CilStrSet.union
      (CilStrSet.union (strings_in_opt_lval optl) (strings_in_exp e))
      (strings_in_exps es)
  | Cmd.Creturn (opte, _) -> strings_in_opt_exp opte
  | _ -> CilStrSet.empty

let rec replace_string_in_exp m = function
  | Const (CStr s) -> Lval (CilStrMap.find (CilStr.Normal s) m)
  | Const (CWStr ws) -> Lval (CilStrMap.find (CilStr.Wide ws) m)
  | Const (CEnum (e', s, i)) -> Const (CEnum (replace_string_in_exp m e', s, i))
  | AddrOf l -> AddrOf (replace_string_in_lval m l)
  | StartOf l -> StartOf (replace_string_in_lval m l)
  | Lval l -> Lval (replace_string_in_lval m l)
  | SizeOfE e' -> SizeOfE (replace_string_in_exp m e')
  | AlignOfE e' -> AlignOfE (replace_string_in_exp m e')
  | UnOp (u, e', l) -> UnOp (u, replace_string_in_exp m e', l)
  | CastE (t, e') -> CastE (t, replace_string_in_exp m e')
  | BinOp (b, e1, e2, l) ->
    BinOp (b, replace_string_in_exp m e1, replace_string_in_exp m e2, l)
  | Question (e1, e2, e3, l) ->
    let e1' = replace_string_in_exp m e1 in
    let e2' = replace_string_in_exp m e2 in
    let e3' = replace_string_in_exp m e3 in
    Question (e1', e2', e3', l)
  | _ as e -> e

and replace_string_in_lval m = function
  | (Mem e, fs) -> (Mem (replace_string_in_exp m e), fs)
  | _ as l -> l

let replace_string_in_alloc m = function
  | Cmd.Array e -> Cmd.Array (replace_string_in_exp m e)

let replace_string_in_opt_exp m = apply_opt (replace_string_in_exp m)

let replace_string_in_opt_lval m = apply_opt (replace_string_in_lval m)

let replace_string_in_exps m = List.map (replace_string_in_exp m)

let replace_string_in_cmd m = function
  | Cmd.Cinstr _
  | Cmd.Cif _
  | Cmd.CLoop _ -> assert false
  | Cmd.Cset (l, e, loc) ->
    Cmd.Cset (replace_string_in_lval m l, replace_string_in_exp m e, loc)
  | Cmd.Cexternal (l, loc) ->
    Cmd.Cexternal (replace_string_in_lval m l, loc)
  | Cmd.Calloc (l, a, loc) ->
    Cmd.Calloc (replace_string_in_lval m l, replace_string_in_alloc m a, loc)
  | Cmd.Csalloc (l, s, loc) -> Cmd.Csalloc (replace_string_in_lval m l, s, loc)
  | Cmd.Cfalloc (l, fd, loc) ->
    Cmd.Cfalloc (replace_string_in_lval m l, fd, loc)
  | Cmd.Cassume (e, loc) -> Cmd.Cassume (replace_string_in_exp m e, loc)
  | Cmd.Ccall (optl, e, es, loc) ->
    let optl' = replace_string_in_opt_lval m optl in
    let e' = replace_string_in_exp m e in
    let es' = replace_string_in_exps m es in
    Cmd.Ccall (optl', e', es', loc)
  | Cmd.Creturn (opte, loc) ->
    Cmd.Creturn (replace_string_in_opt_exp m opte, loc)
  | _ as s -> s

let trans_string_alloc n g =
  let add_bind_to_var s acc =
    let lv = var (makeTempVar g.fun_dec intPtrType) in
    CilStrMap.add s lv acc in
  let bind_to_vars s = CilStrSet.fold add_bind_to_var s CilStrMap.empty in
  let binding_cmd_of loc (c, e) =
    match c, e with
    | CilStr.Normal s, lv -> Cmd.Csalloc (lv, s, loc)
    | CilStr.Wide ws, lv ->
      let s = list_fold (fun _ acc -> "a" ^ acc) ws "" in
      Cmd.Csalloc (lv, s, loc) in
  let cmd = find_cmd n g in
  let str_map = bind_to_vars (strings_in_cmd cmd) in
  if CilStrMap.cardinal str_map > 0 then
    let loc = Cmd.loc_of cmd in
    let binding_cmds =
      List.map (binding_cmd_of loc) (CilStrMap.bindings str_map) in
    let cmd = replace_string_in_cmd str_map cmd in
    let preds, succs = preds_of n g, succs_of n g in
    let g = remove_edges_from n g in
    let (g, tail) =
      (g, n)
      |> push_cmd_nodes binding_cmds
      |> push_cmd_node cmd in
    let head = List.hd (succs_of n g) in
    g
    |> list_fold (fun p -> add_edge p head) preds
    |> list_fold (fun s -> add_edge tail s) succs
    |> remove_node n
  else g

let run g = modify_on_nodes trans_string_alloc g
