(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
open Arg

let opt_debug = ref false
let opt_narrow = ref false
let opt_nobar = ref false

let opt_densify = ref false
let opt_validate_bool = ref false
let opt_validate () = opt_densify := true
                    ; opt_validate_bool := true

let opt_query = ref false

let opts =
  [ ("-debug", (Arg.Set opt_debug), "Turn debug mode on")
  ; ("-narrow", (Arg.Set opt_narrow), "Revise analysis results by narrowing")
  ; ("-nobar", (Arg.Set opt_nobar), "Turn verbose progress bars off")
  ; ("-validate", (Arg.Unit opt_validate), "Validate analysis results")
  ; ("-query", (Arg.Set opt_query), "Print all queries")
  ]
