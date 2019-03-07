(*
 * Copyright 2019, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.

 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.

 * @TAG(DATA61_BSD)
 *)

signature LIST_EXTRAS =
sig
  (*
    `map_find_first f xs` applies `f` to each element of `xs`, returning
    the first result that is `SOME _`, or `NONE` otherwise. For example:

    `map_find_first (try hd) [[], [1], [2]] = SOME 1`

    `map_find_first (try hd) [[], [], []] = NONE`
  *)
  val map_find_first: ('a -> 'b option) -> 'a list -> 'b option;
end

structure ListExtras: LIST_EXTRAS =
struct

fun map_find_first (f: 'a -> 'b option) (xs: 'a list): 'b option =
    case xs of
      [] => NONE
    | x :: xs' =>
          (case f x of
            SOME x' => SOME x'
          | NONE => map_find_first f xs')
end
