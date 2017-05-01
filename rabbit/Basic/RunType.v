(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
Module Type RUN (M : Monad) (MB : MemBasic M).

Parameter run : update_mode -> G.t -> InterNode.t -> cmd -> Mem.t -> M.m Mem.t.

End RUN.
