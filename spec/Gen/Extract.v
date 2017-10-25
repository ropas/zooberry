(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
Set Implicit Arguments.

Require Vali.

Extract Inductive unit => "unit" [ "()" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive nat => int [ "0" "Pervasives.succ" ]
  "(fun fO fS n -> if n=0 then fO () else fS (n-1))".
Extraction Blacklist String List Nat.
Require Import ExtrOcamlZInt.
Require Import ExtrOcamlString.

Global Set Warnings "-extraction-opaque-accessed".
Global Set Warnings "-extraction-reserved-identifier".
Global Set Warnings "-extraction-logical-axiom".

Recursive Extraction Library Vali.
