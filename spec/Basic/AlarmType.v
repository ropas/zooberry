(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
Module Type ALARM (M : Monad) (MB : MemBasic M).

Parameter check_query :
  update_mode -> InterNode.t -> Mem.t -> query -> M.m (list status).

End ALARM.
