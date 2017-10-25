(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** * Syntax of Program.  *)

Set Implicit Arguments.

Require Import ZArith OrderedType OrderedTypeEx.
Require Import hpattern vgtac.
Require Import VocabA DFSetAVL DFMapAVL TStr Pos.

(* NOTE: pid and vid should have a string type in OCaml when the
validator is extracted. *)

Definition pid_t : Type := string_t.
Definition vid_t : Type := string_t.

(** The syntax is based on that of cil.  See [cil.mli] for more
information. *)

(** Float values ([CReal]) and Enumerated types ([CEnum]) is not
supported well by the analyzer. *)

Inductive constant : Type :=
| CInt64 (v : option Z)
(* "CInt64 None" represents an unkonwn int64 constant. *)
| CChr (c : Z)
| CReal (lb ub : Z)
| CEnum.

Inductive unop : Type :=
| Neg
| BNot
| LNot.

Inductive binop : Type :=
| PlusA
| PlusPI
| IndexPI
| MinusA
| MinusPI
| MinusPP
| Mult
| Div
| Mod
| Shiftlt
| Shiftrt
| Lt
| Gt
| Le
| Ge
| Eq
| Ne
| BAnd
| BXor
| BOr
| LAnd
| LOr.

Definition binop_dec : forall (x y : binop), {x = y} + {~ x = y}.
Proof. destruct x, y; try (left; reflexivity); right; inversion 1. Defined.

Inductive exp : Type :=
| Const (c : constant) (pos : pos_t)
| Lval (lv : lval) (pos : pos_t)
| SizeOf (i : option Z) (pos : pos_t) (* i is a byte size of type t *)
| SizeOfE (i : option Z) (pos : pos_t) (* i is a byte size of type t *)
| SizeOfStr (i : String.string) (pos : pos_t)
| AlignOf (i : Z) (pos : pos_t) (* i is a byte size of type t *)
| AlignOfE (e : exp) (pos : pos_t)
| UnOp (u : unop) (e : exp) (pos : pos_t)
| BinOp (b : binop) (e1 : exp) (e2 : exp) (pos : pos_t)
| Question (c : exp) (c_true : exp) (c_false : exp) (pos : pos_t)
| CastE (i : option Z) (e : exp) (pos : pos_t) (* i is a byte size of type t *)
| AddrOf (lv : lval) (pos : pos_t)
| StartOf (lv : lval) (pos : pos_t)

with lval : Type :=
| lval_intro (lh : lhost) (o : offset) (pos : pos_t)

with lhost : Type :=
| VarLhost (x : vid_t) (is_global: bool)
| MemLhost (e : exp)

with offset : Type :=
| NoOffset
| FOffset (f : vid_t) (o : offset)
| IOffset (i : exp) (o : offset).

Inductive alloc : Type :=
| Array (e : exp).

(** ** Command statements *)

(**
- [Cexternal] : initializes exteranl arguments such as argc and argv.
- [Cfalloc] (function allocation) : makes closures from function declarations.
- [Casm] : inline assembly is not supported.
*)

Inductive cmd :=
| Cset (lv : lval) (e : exp) (pos : pos_t)
| Cexternal (lv : lval) (pos : pos_t)
| Calloc (lv : lval) (a : alloc) (pos : pos_t)
| Csalloc (lv : lval) (s : String.string) (pos : pos_t)
| Cfalloc (lv : lval) (name : pid_t) (pos : pos_t)
| Cassume (e : exp) (pos : pos_t)
| Ccall (ret_opt : option lval) (f : exp) (args : list exp) (pos : pos_t)
| Creturn (ret_opt : option exp) (pos : pos_t)
| Casm (pos : pos_t)
| Cskip (pos : pos_t).

Definition pos_of_exp (e : exp) : pos_t :=
  match e with
    | Const _ pos
    | Lval _ pos
    | SizeOf _ pos
    | SizeOfE _ pos
    | SizeOfStr _ pos
    | AlignOf _ pos
    | AlignOfE _ pos
    | UnOp _ _ pos
    | BinOp _ _ _ pos
    | Question _ _ _ pos
    | CastE _ _ pos
    | AddrOf _ pos
    | StartOf _ pos => pos
  end.

Definition pos_of_lv (lv : lval) : pos_t :=
  match lv with lval_intro _ _ pos => pos end.
