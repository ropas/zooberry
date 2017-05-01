(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** Abstract Semantics. *)

Set Implicit Arguments.

Require Import Morphisms.
Require Import List ZArith.
Require Import Monad VocabA Syn TStr DLat DPow DMap DStr Pos DPos
        UserInputType Global Fold.
Require Import DomArrayBlk DomBasic DomAbs DomMem SemMem SemEval.
Require StringFun.

Local Open Scope Z.
Local Open Scope sumbool.

Axiom str_realloc : string_t.
Axiom str_strlen : string_t.
Axiom str_scanf : string_t.
Extract Constant str_realloc => """realloc""".
Extract Constant str_strlen => """strlen""".
Extract Constant str_scanf => """scanf""".

(* printfs the format arguments is the first. *)
Axiom str_printf : string_t.
Axiom str_vprintf : string_t.
Extract Constant str_printf => """printf""".
Extract Constant str_vprintf => """vprintf""".

(* printfs the format arguments is the second. *)
Axiom str_fprintf : string_t.
Axiom str_sprintf : string_t.
Axiom str_vfprintf : string_t.
Axiom str_vsprintf : string_t.
Axiom str_vasprintf : string_t.
Axiom str___asprintf : string_t.
Axiom str_asprintf : string_t.
Axiom str_vdprintf : string_t.
Axiom str_dprintf : string_t.
Axiom str_obstack_printf : string_t.
Axiom str_obstack_vprintf : string_t.
Axiom str_easprintf : string_t.
Axiom str_evasprintf : string_t.
Extract Constant str_fprintf => """fprintf""".
Extract Constant str_sprintf => """sprintf""".
Extract Constant str_vfprintf => """vfprintf""".
Extract Constant str_vsprintf => """vsprintf""".
Extract Constant str_obstack_printf => """obstack""".
Extract Constant str_obstack_vprintf => """obstack""".
(* the type of assign target is pointer of pointer *)
Extract Constant str_vasprintf => """vasprintf""".
Extract Constant str___asprintf => """__asprintf""".
Extract Constant str_asprintf => """asprintf""".
Extract Constant str_easprintf => """easprintf""".
Extract Constant str_evasprintf => """evasprintf""".
(* no assignment *)
Extract Constant str_vdprintf => """vdprintf""".
Extract Constant str_dprintf => """dprintf""".

(* printfs the format arguments is the third. *)
Axiom str_snprintf : string_t.
Axiom str_vsnprintf : string_t.
Extract Constant str_snprintf => """snprintf""".
Extract Constant str_vsnprintf => """vsnprintf""".

Axiom str_argv : string_t.
Extract Constant str_argv => """argv""".
(* Encoding API *)

Axiom ext_api : StringFun.M.t StringFun.t.
Extract Constant ext_api => "APIMap.read".

Definition is_printf1 s : bool :=
  if DStr.eq_dec s str_printf ||| DStr.eq_dec s str_vprintf then true else false.
Definition is_printf2 s : bool :=
  if DStr.eq_dec s str_fprintf ||| DStr.eq_dec s str_sprintf
     ||| DStr.eq_dec s str_vfprintf ||| DStr.eq_dec s str_vsprintf
     ||| DStr.eq_dec s str_vasprintf ||| DStr.eq_dec s str___asprintf
     ||| DStr.eq_dec s str_asprintf ||| DStr.eq_dec s str_vdprintf
     ||| DStr.eq_dec s str_dprintf ||| DStr.eq_dec s str_obstack_printf
     ||| DStr.eq_dec s str_obstack_vprintf ||| DStr.eq_dec s str_easprintf
     ||| DStr.eq_dec s str_evasprintf
  then true else false.
Definition is_printf3 s : bool :=
  if DStr.eq_dec s str_snprintf ||| DStr.eq_dec s str_vsnprintf then true else false.
Definition is_ppointer_printf s : bool :=
  if DStr.eq_dec s str_vasprintf ||| DStr.eq_dec s str___asprintf
     ||| DStr.eq_dec s str_asprintf ||| DStr.eq_dec s str_easprintf
     ||| DStr.eq_dec s str_evasprintf
  then true else false.
Definition is_no_assign_printf s : bool :=
  if DStr.eq_dec s str_vdprintf ||| DStr.eq_dec s str_dprintf then true else false.

Definition is_printf (e : exp) : option pid_t :=
  match e with
  | Lval (lval_intro (VarLhost f _) NoOffset _) _ =>
    if (is_printf1 f || is_printf2 f || is_printf3 f)%bool then Some f else None
  | _ => None
  end.

Module SMProcLoc := SetMap Proc PowProc Loc PowLoc.

Load RunType.

Module Run (Import M : Monad) (MB : MemBasic M) <: RUN M MB.

Module Import SemMem := SemMem.Make M MB.

Module Import SemEval := SemEval.Make M MB.

Module BJProcMem := BigJoinM M Proc PowProc Mem.

Section Run.

Variable mode : update_mode.

Variable (g : G.t).

Variable (node : InterNode.t).

Let pid : pid_t := InterNode.get_pid node.

Definition eval := SemEval.eval mode.

Definition mem_lookup k m := mem_lookup k m.

Definition mem_update k v m := mem_update mode g k v m.

Definition mem_wupdate k v m := mem_wupdate mode k v m.

Definition update_rets (callees : PowProc.t) (ret_opt : option lval)
           (m : Mem.t) : M.m Mem.t :=
  do ret_locs <- match ret_opt with
               | None => ret PowLoc.bot
               | Some ret_lv => eval_lv mode node ret_lv m
             end ;
  let callees_locs := SMProcLoc.map loc_of_proc callees in
  mem_wupdate callees_locs ret_locs m.

Definition external_value (a : Allocsite.t) (pos : DPos.t)  : Val.t :=
  match proc_of_allocsite a with
    | Some f =>
      ( PowExtProcPos.singleton (f, pos)
      , PowLoc.singleton (loc_of_allocsite a)
      , ArrayBlk.extern a
      , PowProc.bot)
    | None =>
      ( PowExtProcPos.singleton (str_argv, pos)
      , PowLoc.singleton (loc_of_allocsite a)
      , ArrayBlk.extern a
      , PowProc.bot)
  end.

Definition is_undef (e : exp) : option pid_t :=
  match e with
  | Lval (lval_intro (VarLhost f _) NoOffset _) _ =>
    if InterCfg.is_undef f (G.icfg g) then Some f else None
  | _ => None
  end.

Definition run_realloc (ret_lv : lval) (vs : list Val.t) (m : Mem.t)
: M.m Mem.t :=
  match vs with
    | ptr_v :: size_v :: _ =>
      let allocsite := eval_alloc' node in
      do lv <- eval_lv mode node ret_lv m ;
      do m <- mem_wupdate lv allocsite m ;
      do orig_v <- mem_lookup (deref_of_val ptr_v) m ;
      mem_wupdate (deref_of_val allocsite) orig_v m
    | _ => ret m
  end.

Definition run_strlen (ret_lv : lval) (m : Mem.t) : M.m Mem.t :=
  do lv <- SemEval.eval_lv mode node ret_lv m ;
  mem_wupdate lv Val.bot m.

Definition run_scanf (vs : list Val.t) (fname : pid_t) (pos : DPos.t) (m : Mem.t)
  : M.m Mem.t :=
  match vs with
    | _ :: vs' =>
      let v := PowExtProcPos.singleton (str_scanf, pos) in
      list_fold (fun k m_acc => do acc <- m_acc; mem_wupdate k v acc)
                (List.map pow_loc_of_val vs') (ret m)
    | _ => ret m
  end.

Definition run_printf1 (m : Mem.t) : M.m Mem.t := ret m.

Definition val_joins (vals : list Val.t) :=
  list_fold (fun e acc => Val.join acc e) vals Val.bot.

Definition va_src_val_joins (srcs : list Val.t) (m : Mem.t) :=
  let va_src_val_join (m : Mem.t) (v : Val.t) (m_acc : M.m Val.t) :=
    do str_v <- mem_lookup (deref_of_val v) m ;
    do acc <- m_acc ;
    ret (Val.join (Val.join acc v) str_v) in
  list_fold (va_src_val_join m) srcs (ret Val.bot).

Definition va_arg_joins (args : list exp) (m : Mem.t) : M.m Val.t :=
  let va_arg_join (m : Mem.t) (e : exp) (m_acc : M.m Val.t) : M.m Val.t :=
    do acc <- m_acc ;
    let deref_e :=
        Lval (lval_intro (MemLhost e) NoOffset unknown_pos) unknown_pos in
    do v1 <- eval node deref_e m ;
    do v2 <- eval node e m ;
    ret (Val.join (Val.join acc v1) v2) in
  list_fold (va_arg_join m) args (ret Val.bot).

(* when target is a pointer *)
Definition run_printf_pointer (e : exp) (args : list exp)
           (m : Mem.t) : M.m Mem.t :=
  do lv <- eval node e m ;
  do v <- va_arg_joins args m ;
  mem_wupdate (deref_of_val lv) (pow_proc_pos_of_val v) m.

(* when target is a pointer of a pointer *)
Definition run_printf_ppointer (e : exp) (args : list exp)
           (m : Mem.t) : M.m Mem.t :=
  do lv <- eval node e m ;
  do v <- va_arg_joins args m ;
  let alloc_v := eval_alloc' node in
  do m <- mem_wupdate (deref_of_val lv) alloc_v m ;
  mem_wupdate (deref_of_val alloc_v) (pow_proc_pos_of_val v) m.

Definition run_printf2 (f : pid_t) (args : list exp) (m : Mem.t)
: M.m Mem.t :=
  match args with
    | hd_x :: _ :: tl_x =>
      if is_ppointer_printf f then run_printf_ppointer hd_x tl_x m else
        if is_no_assign_printf f then ret m else
          run_printf_pointer hd_x tl_x m
    | _ => ret m
  end.

Definition run_printf3 (args : list exp) (m : Mem.t)
: M.m Mem.t :=
  match args with
    | hd_x :: _ :: _ :: tl_x => run_printf_pointer hd_x tl_x m
    | _ => ret m
  end.

Definition run_printf (f : pid_t) (args : list exp) (m : Mem.t)
: M.m Mem.t :=
  if is_printf1 f then run_printf1 m else
    if is_printf2 f then run_printf2 f args m else
      if is_printf3 f then run_printf3 args m else
        ret m.

Definition set_ext_allocsite (ret_lv : lval) (allocsite : Allocsite.t)
           (pos : DPos.t) (m : Mem.t) : M.m Mem.t :=
  let ext_v := external_value allocsite pos in
  do lv <- SemEval.eval_lv mode node ret_lv m ;
  do m <- mem_wupdate lv ext_v m ;
  mem_wupdate (PowLoc.singleton (loc_of_allocsite allocsite)) ext_v m.

Definition find_string_api_name (f : string_t) := StringFun.find f ext_api.

Definition process_dsts (pos : DPos.t) (fname : string_t)
           dsts (src_val : Val.t) (m : Mem.t) :=
  let taint_val := external_value (allocsite_of_ext (Some fname)) pos in
  let process_dst dst (m_m : M.m Mem.t) :=
    do m <- m_m ;
    match dst with
      | (val, StringFun.NoAlloc, StringFun.InSrc) =>
        mem_wupdate (deref_of_val val) src_val m
      | (val, StringFun.NoAlloc, StringFun.ExSrc) =>
        mem_wupdate (deref_of_val val) taint_val m
      | (val, StringFun.DoAlloc, StringFun.InSrc) =>
        let alloc_v := eval_alloc' node in
        do m <- mem_wupdate (deref_of_val val) alloc_v m ;
          mem_wupdate (deref_of_val alloc_v) (pow_proc_pos_of_val src_val) m
      | (val, StringFun.DoAlloc, StringFun.ExSrc) =>
        let alloc_v := eval_alloc' node in
        do m <- mem_wupdate (deref_of_val val) alloc_v m ;
          mem_wupdate (pow_loc_of_val alloc_v) (pow_proc_pos_of_val taint_val) m
    end in
  list_fold process_dst dsts (ret m).

Definition process_ret (pos : DPos.t)
           (fname : string_t) (sfun : StringFun.t)
           (ret_opt : option lval)
           (dsts : list (Val.t * StringFun.alloc_t * StringFun.src_t))
           (src_val : Val.t) (m : Mem.t) :=
  match ret_opt with
    | Some ret_l =>
      do lv <- eval_lv mode node ret_l m ;
      match StringFun.ret sfun with
        | StringFun.CleanRet => mem_wupdate lv Val.bot m
        | StringFun.TaintRet =>
          let taint_val := external_value (allocsite_of_ext (Some fname)) pos in
          mem_wupdate lv taint_val m
        | StringFun.SrcRet StringFun.NoAlloc =>
          mem_wupdate lv src_val m
        | StringFun.SrcRet StringFun.DoAlloc =>
          let alloc_v := eval_alloc' node in
          do m <- mem_wupdate lv alloc_v m ;
          mem_wupdate (pow_loc_of_val alloc_v) (pow_proc_pos_of_val src_val) m
        | StringFun.DstRet =>
          let get_dst_val dst := match dst with (val, _, _) => val end in
          let dst_val := val_joins (List.map get_dst_val dsts) in
          mem_wupdate lv dst_val m
      end
    | None => ret m
  end.

Definition run_api (ret_opt : option lval)
           (vs : list Val.t) (pos : DPos.t)
           (fname : string_t) (sfun : StringFun.t) (m : Mem.t) : M.m Mem.t :=
  let args := StringFun.args sfun in
  let (dsts, srcs) := StringFun.get_dstsrc_list vs args nil nil in
  do src_val <- va_src_val_joins srcs m ;
  do m <- process_dsts pos fname dsts src_val m ;
  do m <- process_ret pos fname sfun ret_opt dsts src_val m ;
  ret m.

Definition run_api_with_name
           (ret_opt : option lval) (vs : list Val.t) (pos : DPos.t)
           (fname : string_t) (m : Mem.t) :=
  match find_string_api_name fname with
  | Some sfun =>
    run_api ret_opt vs pos fname sfun m
  | None =>
    match ret_opt with
    | Some ret_lv =>
      set_ext_allocsite ret_lv (allocsite_of_ext (Some fname)) pos m
    | None =>
      ret m
    end
  end.

Definition run_undef_funcs (ret_opt : option lval) (ext : pid_t)
           (vs : list Val.t) (pos : DPos.t) (m : Mem.t) : M.m Mem.t :=
  run_api_with_name ret_opt vs pos ext m.

Definition run (cmd : cmd) (m : Mem.t) : M.m Mem.t :=
  match cmd with
  | Cset l e _ =>
    do lv <- eval_lv mode node l m ;
    do v <- eval node e m ;
    mem_wupdate lv v m
  | Cexternal l pos =>
    set_ext_allocsite l (allocsite_of_ext None) pos m
  | Calloc l a _ =>
    do lv <- eval_lv mode node l m ;
    let v := eval_alloc mode node a in
    mem_wupdate lv v m
  | Csalloc l s _ =>
    let allocsite := allocsite_of_node node in
    let pow_loc := PowLoc.singleton (loc_of_allocsite allocsite) in
    do lv <- eval_lv mode node l m ;
    do m <- mem_wupdate pow_loc (eval_string s) m ;
    mem_wupdate lv (eval_string_loc s allocsite pow_loc) m
  | Cfalloc l name _ =>
    do lv <- eval_lv mode node l m ;
    mem_wupdate lv (PowProc.singleton name) m
  | Cassume e _ => ret m
  | Ccall ret_opt f args pos =>
    do vs <- eval_list mode node args m ;
    match G.is_undef_e f g with
    | Some fname =>
      match is_printf f with
      | Some fname => run_printf fname args m
      | None => run_undef_funcs ret_opt fname vs pos m
      end
    | None =>
      do f_v <- eval node f m ;
      let fs := powProc_of_val f_v in
      do m <- update_rets fs ret_opt m ;
      BJProcMem.weak_big_join (bind_args mode g vs) fs (ret m)
    end
  | Creturn ret_opt _ =>
    match ret_opt with
    | None => ret m
    | Some e =>
      do v <- eval node e m ;
      do ret_loc <- mem_lookup (PowLoc.singleton (loc_of_proc pid)) m ;
      mem_wupdate (deref_of_val ret_loc) v m
    end
  | Casm _
  | Cskip _ => ret m
  end.

End Run.

End Run.

Local Close Scope sumbool.
Local Close Scope Z.

Load RunInst.
