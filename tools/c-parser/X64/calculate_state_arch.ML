(*
 * Copyright 2017, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

signature CALCULATE_STATE_ARCH = sig
  val mk_array_size_type : int -> typ
end;

structure CalculateStateArch : CALCULATE_STATE_ARCH = struct
  open TermsTypes
  fun mk_array_size_type sz =
    if sz = 1048576
      then @{typ "ty1048576"}
      else mk_numeral_type sz
end
