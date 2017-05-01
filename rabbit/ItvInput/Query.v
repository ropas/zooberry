(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
Set Implicit Arguments.

Require Import ZArith List.
Require Import Monad vgtac VocabA Syn InterCfg DStr DLat DItv DPos
        UserInputType.
Require Import DomBasic DomArrayBlk DomAbs DomMem SemEval SemAbs.

Local Open Scope sumbool.

Inductive query' : Type :=
| ArrayExp (lv : lval) (e : exp)
| DerefExp (e : exp).
Definition query : Type := query'.

Inductive status' := Proven | UnProven | BotAlarm.

Definition status : Type := status'.

(** ** Collect alarm expressions *)

Fixpoint add_offset (o : offset) (orig_offset : offset) : offset :=
  match orig_offset with
  | NoOffset => o
  | FOffset f o1 => FOffset f (add_offset o o1)
  | IOffset e o1 => IOffset e (add_offset o o1)
  end.

Definition lval_append_field (lv : lval) (f : vid_t) : lval :=
  match lv with
  | lval_intro lh o pos =>
    lval_intro lh (add_offset (FOffset f NoOffset) o) pos
  end.

Definition lval_append_index (lv : lval) (e : exp) : lval :=
  match lv with
  | lval_intro lh o pos =>
    lval_intro lh (add_offset (IOffset e NoOffset) o) pos
  end.

Fixpoint c_offset (lv : lval) (ofs : offset) (pos : DPos.t)
: list (query * DPos.t) :=
  match ofs with
  | NoOffset => nil
  | FOffset f o => c_offset (lval_append_field lv f) o pos
  | IOffset e o =>
    (ArrayExp lv e, pos)
      :: c_exp e ++ c_offset (lval_append_index lv e) o pos
  end

with c_lv (lv : lval) : list (query * DPos.t) :=
  match lv with
  | lval_intro (VarLhost v is_g) ofs pos =>
    c_offset (lval_intro (VarLhost v is_g) NoOffset pos) ofs pos
  | lval_intro (MemLhost e) ofs pos =>
    (DerefExp e, pos)
      :: c_exp e
      ++ c_offset (lval_intro (MemLhost e) NoOffset pos) ofs pos
  end

with c_exp (e : exp) : list (query * DPos.t) :=
  match e with
  | Lval lv _ => c_lv lv
  | AlignOfE e _ => c_exp e
  | UnOp _ e _ => c_exp e
  | BinOp _ e1 e2 _ => c_exp e1 ++ c_exp e2
  | CastE _ e _ => c_exp e
  | AddrOf lv _ => c_lv lv
  | StartOf lv _ => c_lv lv
  | _ => nil
  end.

Definition c_alloc (alloc : alloc) : list (query * DPos.t) :=
  match alloc with
  | Array e => c_exp e
  end.

Definition c_exps (exps : list exp) : list (query * DPos.t) :=
  list_fold (fun e q => c_exp e ++ q) exps nil.

Definition collect_query (cmd : cmd) : list (query * DPos.t) :=
  match cmd with
  | Cset lv e _ => c_lv lv ++ c_exp e
  | Cexternal lv _ => c_lv lv
  | Calloc lv a _ => c_lv lv ++ c_alloc a
  | Csalloc lv _ _ => c_lv lv
  | Cassume e _ => c_exp e
  | Ccall None e es _ => c_exp e ++ c_exps es
  | Ccall (Some lv) e es _ => c_lv lv ++ c_exp e ++ c_exps es
  | Creturn (Some e) _ => c_exp e
  | _ => nil
  end.

Load AlarmType.

Module Alarm (Import M : Monad) (MB : MemBasic M) <: ALARM M MB.

Module Import SemMem := SemMem.Make M MB.

Module Import SemEval := SemEval.Make M MB.

Module Import Run := SemAbs.Run M MB.

Section Alarm.

Variable mode : update_mode.

Definition check_bo arr i : list status :=
  if ArrayBlk.eq_dec arr ArrayBlk.bot then BotAlarm :: nil else
    let check_bo' a ofs_size lst :=
      let '(ofs, size, _) := ofs_size in
      let ofs := Itv.plus ofs i in
      let status :=
        match ofs, size with
        | Itv.Bot, _
        | _, Itv.Bot => BotAlarm
        | @Itv.V (Itv.Int ol) (Itv.Int oh) _ _ _, @Itv.V (Itv.Int sl) _ _ _ _ =>
          if Z_ge_dec ol 0%Z &&& Z_lt_dec oh sl then Proven else UnProven
        | _, _ => UnProven
        end in
      status :: lst in
    ArrayBlk.foldi check_bo' arr nil.

Definition make_bot_proven status :=
  match status with
    | BotAlarm => Proven
    | _ => status
  end.

Definition check_query (node : InterNode.t) (mem : Mem.t) (q : query)
: m (list status) :=
  match q with
  | ArrayExp lv e =>
    do lvs <- SemEval .eval_lv mode node lv mem ;
    do v1 <- mem_lookup lvs mem ;
    do v2 <- eval mode node e mem ;
    ret (check_bo (array_of_val v1) (itv_of_val v2))
  | DerefExp e =>
    do v <- eval mode node e mem ;
    let statuses := check_bo (array_of_val v) Itv.zero in
    let r :=
        if Val.eq_dec v Val.bot then statuses else
          List.map make_bot_proven statuses
    in
    ret r
  end.

End Alarm.

End Alarm.

Local Close Scope sumbool.
