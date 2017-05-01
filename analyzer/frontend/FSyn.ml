(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** Temporary syntax in frontend  *)

open Cil

module Cmd = struct
  (* Final graph should not have Cinstr, Cif, and CLoop. *)
  type t =
    | Cinstr of instr list
    | Cif of exp * block * block * location
    | CLoop of location
    | Cset of lval * exp * location
    | Cexternal of lval * location
    | Calloc of lval * alloc * location
    | Csalloc of lval * string * location
    | Cfalloc of lval * fundec * location
    | Cassume of exp * location
    | Ccall of lval option * exp * exp list * location
    | Creturn of exp option * location
    | Casm of attributes * string list *
              (string option * string * lval) list *
              (string option * string * exp) list *
              string list * location
    | Crefute of alarm_exp * location
    | Cskip

  and alloc =
    | Array of exp

  and alarm_exp =
    | ArrayExp of lval * exp * location
    | DerefExp of exp * location

  let of_stmt = function
    | Instr instrs -> Cinstr instrs
    | If (exp, b1, b2, loc) -> Cif (exp, b1, b2, loc)
    | Loop (_, loc, _, _) -> CLoop loc
    | Return (expo, loc) -> Creturn (expo, loc)
    | _ -> Cskip

  let of_instr = function
    | Set (lv, e, loc) -> Cset (lv, e, loc)
    | Call (lvo, f, args, loc) -> Ccall (lvo, f, args, loc)
    | Asm (attr, temps, ci, dj, rk, loc) -> Casm (attr, temps, ci, dj, rk, loc)

  let loc_of = function
    | Cskip
    | Cinstr _ -> assert false
    | Cif (_, _, _, loc)
    | CLoop loc
    | Cset (_, _, loc)
    | Cexternal (_, loc)
    | Calloc (_, _, loc)
    | Csalloc (_, _, loc)
    | Cfalloc (_, _, loc)
    | Cassume (_, loc)
    | Ccall (_, _, _, loc)
    | Creturn (_, loc)
    | Casm (_, _, _, _, _, loc)
    | Crefute (_, loc) -> loc
end
