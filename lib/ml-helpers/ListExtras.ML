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
    `map_find_first f xs` applies `f` to each element of `xs`, returning the
    first result that is `SOME _`, or `NONE` otherwise. For example:

    `map_find_first (try hd) [[], [1], [2]] = SOME 1`

    `map_find_first (try hd) [[], [], []] = NONE`
  *)
  val map_find_first: ('a -> 'b option) -> 'a list -> 'b option;

  (*
    `find_index test xs` returns the index of the first element of `xs` that
    passes `test`, or `NONE` if no such element exists. For example:

    `find_index (curry op = "c") ["a", "b", "c"] = SOME 2`

    `find_index (curry op = "d") ["a", "b", "c"] = NONE`

    This is similar to `Library.get_index`, except we don't try and return the
    found element.
  *)
  val find_index: ('a -> bool) -> 'a list -> int option;
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

fun find_index test =
  Library.get_index (fn x => if test x then SOME () else NONE) #> Option.map fst

end
