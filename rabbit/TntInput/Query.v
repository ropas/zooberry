(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** * Query generation *)
Set Implicit Arguments.

Require Import ZArith List.
Require Import Monad vgtac VocabA Syn InterCfg DStr DLat DPos Pos
        UserInputType.
Require Import DomBasic DomAbs DomMem SemEval SemAbs.

Local Open Scope sumbool.

Definition query : Type := exp.

Inductive status' :=
| Tainted (exts: PowExtProcPos.t)
| Clean.
Definition status : Type := status'.

(** ** Collect alarm expressions *)

Definition fmt_query (fmt : exp) : list (query * DPos.t) :=
  [(fmt, pos_of_exp fmt)].
Definition collect_query (cmd : cmd) : list (query * DPos.t) :=
  match cmd with
  | Ccall _ (Lval (lval_intro (VarLhost f _) NoOffset pos) _) arg _ =>
    if is_printf1 f then
      match arg with fmt :: _ => fmt_query fmt | _ => nil end
    else if is_printf2 f then
      match arg with _ :: fmt :: _ => fmt_query fmt | _ => nil end
    else if is_printf3 f then
      match arg with _ :: _ :: fmt :: _ => fmt_query fmt | _ => nil end
    else nil
  | _ => nil
  end.

(** ** Get queries and check proven *)

Load AlarmType.

Module Alarm (Import M : Monad) (MB : MemBasic M) <: ALARM M MB.

Module Import SemMem := SemMem.Make M MB.

Module Import SemEval := SemEval.Make M MB.

Module Import Run := SemAbs.Run M MB.

Section Alarm.

Variable mode : update_mode.

Definition check_query (node : InterNode.t) (mem : Mem.t) (q : query)
: m (list status) :=
  let deref_e :=
      Lval (lval_intro (MemLhost q) NoOffset unknown_pos) unknown_pos in
  do v <- eval mode node deref_e mem ;
  ret [if PowExtProcPos.eq_dec (pow_proc_pos_of_val v) PowExtProcPos.bot then Clean else Tainted (pow_proc_pos_of_val v)].

End Alarm.

End Alarm.

Local Close Scope sumbool.
