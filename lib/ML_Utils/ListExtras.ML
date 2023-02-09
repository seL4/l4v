(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
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

  (*
    `unfold f init` repeatedly calls `f` to construct elements
    of a list, until it returns NONE. For example:

    `unfold
      (fn idx => if idx < 10 then SOME ("hello", idx + 1) else NONE)
      7
      = ["hello", "hello", "hello"]`

    `unfold (fn x => SOME (1, x)) anything` never returns.

    `unfold (K NONE) anything = []`
  *)
  val unfold: ('acc -> ('item * 'acc) option) -> 'acc -> 'item list;

  (* `range from to` produces the list of integers between
     `from` (inclusive) and `to` (exclusive). For example:

     `range 3 5 = [3, 4]`
     `range ~1 2 = [~1, 0, 1]`
  *)
  val range: int -> int -> int list;
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

fun unfold (f: 'acc -> ('item * 'acc) option) (acc: 'acc) =
    case f acc of
      NONE => []
    | SOME (item, new_acc) => item :: unfold f new_acc;

fun range from to =
    unfold (fn i => if i < to then SOME (i, i + 1) else NONE) from;

end
