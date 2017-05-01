(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
Set Implicit Arguments.

Require DomBasic DomAbs SemAbs Query.
Require Import UserInputType.

Module Input <: INPUT.
  Include DomBasic.
  Include DomAbs.
  Include DomMem.
  Include SemAbs.
  Include Query.
End Input.
