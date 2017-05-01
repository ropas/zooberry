(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** * Translation *)

open VocabA
open VocabB
open Pos
open Global

module Cmd = FSyn.Cmd

module PidMap = InterCfg.PidMap

module PidSet = InterCfg.PidSet

module Callgraph = Global.Callgraph

let t_pid_map t_k t_v add init m =
  let add_k_v k v = add (t_k k) (t_v v) in
  InterCfg.PidMap.fold add_k_v m init

let t_intra_node_map t_k t_v add init m =
  let add_k_v k v = add (t_k k) (t_v v) in
  FIntraCfg.NodeMap.fold add_k_v m init

let t_opt t_elt = function
  | Some v -> Some (t_elt v)
  | None -> None

let rec t_list t_elt = function
  | [] -> []
  | hd :: tl -> t_elt hd :: t_list t_elt tl

let t_vid (vi : Cil.varinfo) : Syn.vid_t = vi.Cil.vname

let byteSizeOf (t : Cil.typ) : int option =
  try Some (Cil.bitsSizeOf t / 8) with _ -> None

let rec t_string (s : string) : char list =
  let length = String.length s in
  if length = 0 then [] else
    let first_char = s.[0] in
    let left_s = String.sub s 1 (length - 1) in
    first_char :: t_string left_s

let pos_id_ref = ref 0
let new_pos file line =
  let pos_id = !pos_id_ref in
  pos_id_ref := !pos_id_ref + 1;
  { pos_file = Filename.basename file
  ; pos_line = line
  ; pos_id = pos_id }
let t_pos (l : Cil.location) : pos_t  = new_pos l.Cil.file l.Cil.line

let t_const = function
  | Cil.CInt64 (i64, _, _) ->
    let opt_i = try Some (Cil.i64_to_int i64) with _ -> None in
    Syn.CInt64 opt_i
  | Cil.CStr _ -> invalid_arg "CStr"
  | Cil.CWStr _ -> invalid_arg "CWStr"
  | Cil.CChr c -> Syn.CChr (int_of_char c)
  | Cil.CReal (f, _, _) ->
    Syn.CReal (int_of_float (floor f), int_of_float (ceil f))
  | Cil.CEnum _ -> Syn.CEnum

let t_unop : Cil.unop -> Syn.unop = function
  | Cil.Neg -> Syn.Neg
  | Cil.BNot -> Syn.BNot
  | Cil.LNot -> Syn.LNot

let t_binop : Cil.binop -> Syn.binop = function
  | Cil.PlusA -> Syn.PlusA
  | Cil.PlusPI -> Syn.PlusPI
  | Cil.IndexPI -> Syn.IndexPI
  | Cil.MinusA -> Syn.MinusA
  | Cil.MinusPI -> Syn.MinusPI
  | Cil.MinusPP -> Syn.MinusPP
  | Cil.Mult -> Syn.Mult
  | Cil.Div -> Syn.Div
  | Cil.Mod -> Syn.Mod
  | Cil.Shiftlt -> Syn.Shiftlt
  | Cil.Shiftrt -> Syn.Shiftrt
  | Cil.Lt -> Syn.Lt
  | Cil.Gt -> Syn.Gt
  | Cil.Le -> Syn.Le
  | Cil.Ge -> Syn.Ge
  | Cil.Eq -> Syn.Eq
  | Cil.Ne -> Syn.Ne
  | Cil.BAnd -> Syn.BAnd
  | Cil.BXor -> Syn.BXor
  | Cil.BOr -> Syn.BOr
  | Cil.LAnd -> Syn.LAnd
  | Cil.LOr -> Syn.LOr

let elem_typ_of = function
  | Cil.TPtr (t, _)
  | Cil.TArray (t, _, _) -> Some t
  | _ -> None

let rec t_lhost file line = function
  | Cil.Var vi -> Syn.VarLhost (vi.Cil.vname, vi.Cil.vglob)
  | Cil.Mem e -> Syn.MemLhost (t_exp file line e)

and t_exp file line = function
  | Cil.Const c -> Syn.Const (t_const c, new_pos file line)
  | Cil.Lval l -> Syn.Lval (t_lval file line l, new_pos file line)
  | Cil.SizeOf t -> Syn.SizeOf (byteSizeOf t, new_pos file line)
  | Cil.SizeOfE e -> Syn.SizeOfE (byteSizeOf (Cil.typeOf e), new_pos file line)
  | Cil.SizeOfStr s -> Syn.SizeOfStr (t_string s, new_pos file line)
  | Cil.AlignOf t -> Syn.AlignOf (Cil.alignOf_int t, new_pos file line)
  | Cil.AlignOfE e -> Syn.AlignOfE (t_exp file line e, new_pos file line)
  | Cil.UnOp (unop, e, _) ->
    Syn.UnOp (t_unop unop, t_exp file line e, new_pos file line)
  | Cil.BinOp (binop, e1, e2, _) ->
    Syn.BinOp (t_binop binop,
               t_exp file line e1,
               t_exp file line e2,
               new_pos file line)
  | Cil.Question (e1, e2, e3, _) ->
    Syn.Question (t_exp file line e1,
                  t_exp file line e2,
                  t_exp file line e3,
                  new_pos file line)
  | Cil.CastE (t, e) ->
    let np = new_pos file line in
    (match elem_typ_of t with
     | Some t' -> Syn.CastE (byteSizeOf t', t_exp file line e, np)
     | None -> Syn.CastE (None, t_exp file line e, np))
  | Cil.AddrOf l -> Syn.AddrOf (t_lval file line l, new_pos file line)
  | Cil.AddrOfLabel _ -> invalid_arg "AddrOfLabel"
  | Cil.StartOf l -> Syn.StartOf (t_lval file line l, new_pos file line)

and t_lval file line (lh, o) =
  Syn.Coq_lval_intro (t_lhost file line lh, t_offset file line o, new_pos file line)

and t_offset file line = function
  | Cil.NoOffset -> Syn.NoOffset
  | Cil.Field (fi, o) -> Syn.FOffset (fi.Cil.fname, t_offset file line o)
  | Cil.Index (e, o) -> Syn.IOffset (t_exp file line e, t_offset file line o)

let t_lval_opt file line (l_opt : Cil.lval option) : Syn.lval option =
  t_opt (t_lval file line) l_opt

let t_exp_opt file line (e_opt : Cil.exp option) : Syn.exp option =
  t_opt (t_exp file line) e_opt

let t_exps file line (es : Cil.exp list) : Syn.exp list =
  t_list (t_exp file line) es

let t_alloc file line = function
  | Cmd.Array e -> t_exp file line e

let t_cmd = function
  | Cmd.Cinstr _ -> invalid_arg "Cinstr"
  | Cmd.Cif _ -> invalid_arg "Cif"
  | Cmd.CLoop _ -> invalid_arg "CLoop"
  | Cmd.Cset (l, e, pos) -> 
    Syn.Cset (t_lval pos.Cil.file pos.Cil.line l,
              t_exp pos.Cil.file pos.Cil.line e,
              t_pos pos)
  | Cmd.Cexternal (l, pos) -> 
    Syn.Cexternal (t_lval pos.Cil.file pos.Cil.line l, t_pos pos)
  | Cmd.Calloc (l, a, pos) -> 
    Syn.Calloc (t_lval pos.Cil.file pos.Cil.line l,
                t_alloc pos.Cil.file pos.Cil.line a,
                t_pos pos)
  | Cmd.Csalloc (l, s, pos) -> 
    Syn.Csalloc (t_lval pos.Cil.file pos.Cil.line l, t_string s, t_pos pos)
  | Cmd.Cfalloc (l, fd, pos) ->
    let func_name = fd.Cil.svar.Cil.vname in
    Syn.Cfalloc (t_lval pos.Cil.file pos.Cil.line l, func_name, t_pos pos)
  | Cmd.Cassume (e, pos) ->
    Syn.Cassume (t_exp pos.Cil.file pos.Cil.line e, t_pos pos)
  | Cmd.Ccall (_, Cil.Lval (Cil.Var f, Cil.NoOffset), _, pos)
    when f.Cil.vname = "zoo_print"
      || f.Cil.vname = "airac_print"
      || f.Cil.vname = "zoo_dump" -> Syn.Cskip (t_pos pos)
  | Cmd.Ccall (l_opt, e, es, pos) ->
    Syn.Ccall (t_lval_opt pos.Cil.file pos.Cil.line l_opt,
               t_exp pos.Cil.file pos.Cil.line e,
               t_exps pos.Cil.file pos.Cil.line es,
               t_pos pos)
  | Cmd.Creturn (e_opt, pos) -> 
    Syn.Creturn (t_exp_opt pos.Cil.file pos.Cil.line e_opt,
                 t_pos pos)
  | Cmd.Casm (_, _, _, _, _, pos) -> Syn.Casm (t_pos pos)
  | Cmd.Cskip -> Syn.Cskip unknown_pos
  | Cmd.Crefute _ -> invalid_arg "Crefute"

let t_intra_node = function
  | FIntraNode.Entry -> IntraNode.Entry
  | FIntraNode.Exit -> IntraNode.Exit
  | FIntraNode.Node i -> IntraNode.Node i

let t_intra_edges g =
  let add_edge' k v m =
    let vs = default IntraCfg.NodeSet.empty (IntraCfg.NodeMap.find k m) in
    let vs = IntraCfg.NodeSet.add v vs in
    IntraCfg.NodeMap.add k vs m in
  let add_edge n1 n2 (m_succs, m_preds) =
    let t1 = t_intra_node n1 in
    let t2 = t_intra_node n2 in
    (add_edge' t1 t2 m_succs, add_edge' t2 t1 m_preds) in
  let m_empty = IntraCfg.NodeMap.empty in
  FIntraCfg.G.fold_edges add_edge g (m_empty, m_empty)

let t_intra_cfg cfg =
  let (succ, pred) = t_intra_edges (cfg.FIntraCfg.graph) in
  let cmds =
    let add = IntraCfg.NodeMap.add in
    let init = IntraCfg.NodeMap.empty in
    t_intra_node_map t_intra_node t_cmd add init cfg.FIntraCfg.cmds in
  let add_skip node cmds =
    IntraCfg.NodeMap.add node (Syn.Cskip unknown_pos) cmds in
  let cmds = cmds |> add_skip IntraNode.Entry |> add_skip IntraNode.Exit in

  { IntraCfg.args = FIntraCfg.get_formals cfg
  ; IntraCfg.cmds = cmds
  ; IntraCfg.succ = succ
  ; IntraCfg.pred = pred
  ; IntraCfg.nodes =
      (let add node = IntraCfg.NodeSet.add (t_intra_node node) in
       let init = IntraCfg.NodeSet.empty in
       FIntraCfg.G.fold_vertex add cfg.FIntraCfg.graph init)
  }

let t_cfgs cfgs =
  t_pid_map id t_intra_cfg PidMap.add PidMap.empty cfgs

let t_inter_node node = (fst node, t_intra_node (snd node))

let add_inter_edge n1 n2 (m_succs, m_preds) =
  let add_edge' k v m =
    let vs = default InterCfg.NodeSet.empty (InterCfg.NodeMap.find k m) in
    let vs = InterCfg.NodeSet.add v vs in
    InterCfg.NodeMap.add k vs m in
  (add_edge' n1 n2 m_succs, add_edge' n2 n1 m_preds)

let t_inter_cfg icfg =
  { InterCfg.cfgs = t_cfgs icfg.FInterCfg.cfgs
  ; InterCfg.succ = InterCfg.NodeMap.empty
  ; InterCfg.pred = InterCfg.NodeMap.empty
  ; InterCfg.nodes =
      (let add node = InterCfg.NodeSet.add (t_inter_node node) in
       let init = InterCfg.NodeSet.empty in
       FInterCfg.NodeSet.fold add (FInterCfg.nodes_of icfg) init)
  }

(** updates the successor map in inter cfg *)
let t_inter_edges' icfg cg =
  let call_ret node = (node, get_some (InterCfg.returnof icfg node)) in
  let entry_exit f acc = ((f, IntraNode.Entry), (f, IntraNode.Exit)) :: acc in
  let entries_exits fs = PidSet.fold entry_exit fs [] in
  let add1 (call, ret) (entry', exit') acc =
    acc
    |> add_inter_edge call entry'
    |> if not (InterCfg.has_cmd icfg exit') then id else
         add_inter_edge exit' ret in
  let add call_node callees =
    list_fold (add1 (call_ret call_node)) (entries_exits callees) in
  let init = InterCfg.NodeMap.empty in
  InterCfg.NodeMap.fold add (Callgraph.node_calls cg) (init, init)

let t_inter_edges g =
  let icfg = G.icfg g in
  let cg = G.callgraph g in
  let (succ, pred) = t_inter_edges' icfg cg in
  let icfg = { icfg with InterCfg.succ = succ ; InterCfg.pred = pred } in
  { g with G.icfg = icfg }
