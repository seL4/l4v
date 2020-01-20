(*
 * Copyright 2019, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.

 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.

 * @TAG(DATA61_BSD)
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