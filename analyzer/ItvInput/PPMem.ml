(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** Pretty print of memory *)

open VocabA
open PPVocab
open Format
open UserInput.Input

let print_var v =
  open_box 0;
  (match v with
   | Var.Inl x ->
     print_string "@";
     print_string x
   | Var.Inr (f, x) ->
     print_string x;
     print_string "@";
     print_string f
  );
  close_box ()

let print_alloc a =
  open_box 0;
  print_string "alloc@";
  (match a with
   | Allocsite.Inl node -> PPIL.print_inter_node node
   | Allocsite.Inr (ExtAllocsite.Inl _) -> print_string "extern"
   | Allocsite.Inr (ExtAllocsite.Inr f) -> print_string f
  );
  close_box ()

let print_var_alloc va =
  open_box 0;
  (match va with
   | VarAllocsite.Inl v -> print_var v
   | VarAllocsite.Inr a -> print_alloc a
  );
  close_box ()

let print_fields fs =
  open_box 0;
  let rec print_fields' fs =
    match fs with
    | Fields.Coq_nil -> ()
    | Fields.Coq_cons (f, tl) ->
      print_string ".";
      print_string f;
      print_fields' tl in
  print_fields' fs;
  close_box ()

let print_loc l =
  open_box 0;
  (match l with
   | Loc.Inl (va, fs) ->
     print_var_alloc va;
     print_fields fs
   | Loc.Inr f -> print_string ("rets_of " ^ f)
  );
  close_box ()

let print_itv itv =
  let print_itv' = function
    | DItv.Itv.Int i -> print_int i
    | DItv.Itv.PInf -> print_string "+oo"
    | DItv.Itv.MInf -> print_string "-oo" in
  open_box 0;
  (match itv with
   | DItv.Itv.V (lb, ub) ->
     print_string "[";
     print_itv' lb;
     print_string ",";
     print_itv' ub;
     print_string "]"
   | DItv.Itv.Bot -> print_string "bot"
  );
  close_box ()

let print_pow_loc pow_loc =
  print_list "{" "}" "," print_loc (DomBasic.PowLoc.elements pow_loc)

let print_array_blk array_blk =
  let array_blk = DomArrayBlk.ArrayBlk.elements array_blk in
  let print_array_blk_1 (alloc, ((o, st), sz)) =
    open_box 1;
    print_string "(";
    print_alloc alloc;
    print_string ",";
    print_space ();
    print_itv o;
    print_string ",";
    print_space ();
    print_itv st;
    print_string ",";
    print_space ();
    print_itv sz;
    print_string ")";
    close_box () in
  print_list "{" "}" "," print_array_blk_1 array_blk

let print_pow_proc pow_proc =
  print_list "{" "}" "," print_string (PowProc.elements pow_proc)

let print_val (((itv, pow_loc), array_blk), pow_proc) =
  open_box 1;
  print_string "(";
  print_itv itv;
  print_string ",";
  print_space ();
  print_pow_loc pow_loc;
  print_string ",";
  print_space ();
  print_array_blk array_blk;
  print_string ",";
  print_space ();
  print_pow_proc pow_proc;
  print_string ")";
  close_box ()

let print_mem m =
  let print_loc_val l v n =
    print_loc l;
    print_string " ";
    print_val v;
    if n > 1 then print_cut ();
    n - 1 in
  open_vbox 0;
  ignore (Mem.foldi print_loc_val m (Mem.cardinal m));
  close_box ()
