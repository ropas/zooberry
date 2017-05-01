(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** * User input type *)
Set Implicit Arguments.

Require Import Morphisms.
Require Import Monad hpattern vgtac VocabA Syn Global DLat DPow
        DMap DPos DStr DFMapAVL.
Require DMem Access.

Inductive update_mode := Weak | Strong.

Inductive loc_type := GVarLoc | LVarLoc (f : pid_t) | OtherLoc.

Module Type INPUT.

(** ** 1. Basic domains: user's obligation *)

Declare Module Loc : KEY.

Declare Module Val : LAT.

Module PowLoc := Pow Loc.

(** Returns true if an abstract location approximates *only one*
concrete location.  The call graph given as the second input is used
to check how many times concrete local variables can be piled up in
the stack, e.g., a local variable of a recursive function should not
be a target of strong update. *)

Parameter approx_one_loc : G.t -> Loc.t -> bool.

Parameter approx_one_loc_mor :
  forall g, Proper (Loc.eq ==> eq) (approx_one_loc g).

(** ** 2. Memory domain *)

Load DomMemCommon.

(** ** 3. Abstract semantic function: user's obligation *)

Load RunType.

Declare Module Run : RUN.

Load RunInst.

(** ** 4. Alarm report *)

Parameter query : Type.

Parameter status : Type.

Parameter collect_query : cmd -> list (query * DPos.t).

Load AlarmType.

Declare Module Alarm : ALARM.

End INPUT.
