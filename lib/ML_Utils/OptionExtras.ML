(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

signature OPTION_EXTRAS =
sig
  (*
    `get_or_else f opt` unwraps `opt` if it is `SOME x`. Otherwise,
    it uses `f` to construct a value.

    This is useful when `f` has side effects, such as throwing an
    exception or printing a warning.
  *)
  val get_or_else: (unit -> 'a) -> 'a option -> 'a
end

structure OptionExtras: OPTION_EXTRAS =
struct

fun get_or_else _ (SOME x) = x
  | get_or_else f NONE = f ()

end