(* SPDX-License-Identifier: BSD-3-Clause *)
(* SPDX-FileCopyrightText: Lawrence C Paulson, Cambridge University Computer Laboratory *)
(* SPDX-FileCopyrightText: Markus Wenzel, TU Muenchen *)

(*  Extracted from Isabelle sources (src/Pure/library.ML) *)

signature LIBRARY =
sig

  val is_equal: order -> bool

  val build: ('a list -> 'a list) -> 'a list
  val sort : ('a * 'a -> order) -> 'a list -> 'a list

  val foldl: ('a * 'b -> 'a) -> 'a * 'b list -> 'a

  val insert: ('a * 'a -> bool) -> 'a -> 'a list -> 'a list
  val remove: ('b * 'a -> bool) -> 'b -> 'a list -> 'a list
  val update: ('a * 'a -> bool) -> 'a -> 'a list -> 'a list
  val union: ('a * 'a -> bool) -> 'a list -> 'a list -> 'a list
  val merge: ('a * 'a -> bool) -> 'a list * 'a list -> 'a list

end

structure Library : LIBRARY =
struct

fun is_equal ord = ord = EQUAL;

fun build (f: 'a list -> 'a list) = f [];

(*stable mergesort -- preserves order of equal elements*)
fun mergesort unique ord =
  let
    fun merge (xs as x :: xs') (ys as y :: ys') =
          (case ord (x, y) of
            LESS => x :: merge xs' ys
          | EQUAL =>
              if unique then merge xs ys'
              else x :: merge xs' ys
          | GREATER => y :: merge xs ys')
      | merge [] ys = ys
      | merge xs [] = xs;

    fun merge_all [xs] = xs
      | merge_all xss = merge_all (merge_pairs xss)
    and merge_pairs (xs :: ys :: xss) = merge xs ys :: merge_pairs xss
      | merge_pairs xss = xss;

    fun runs (x :: y :: xs) =
          (case ord (x, y) of
             LESS => ascending y [x] xs
           | EQUAL =>
               if unique then runs (x :: xs)
               else ascending y [x] xs
           | GREATER => descending y [x] xs)
      | runs xs = [xs]

    and ascending x xs (zs as y :: ys) =
          (case ord (x, y) of
             LESS => ascending y (x :: xs) ys
           | EQUAL =>
               if unique then ascending x xs ys
               else ascending y (x :: xs) ys
           | GREATER => rev (x :: xs) :: runs zs)
      | ascending x xs [] = [rev (x :: xs)]

    and descending x xs (zs as y :: ys) =
          (case ord (x, y) of
             GREATER => descending y (x :: xs) ys
           | EQUAL =>
               if unique then descending x xs ys
               else (x :: xs) :: runs zs
           | LESS => (x :: xs) :: runs zs)
      | descending x xs [] = [x :: xs];

  in merge_all o runs end;

fun sort ord = mergesort false ord;

(*  (op @) (e, [x1, ..., xn])  ===>  ((e @ x1) @ x2) ... @ xn
    for operators that associate to the left (TAIL RECURSIVE)*)
fun foldl (f: 'a * 'b -> 'a) : 'a * 'b list -> 'a =
  let fun itl (e, [])  = e
        | itl (e, a::l) = itl (f(e, a), l)
  in  itl end;

fun insert eq x xs = if member eq xs x then xs else x :: xs;

fun remove eq x xs = if member eq xs x then filter_out (fn y => eq (x, y)) xs else xs;

fun update eq x list =
  (case list of
    [] => [x]
  | y :: rest =>
      if member eq rest x then x :: remove eq x list
      else if eq (x, y) then list else x :: list);

fun union eq = fold (insert eq);

fun merge eq (xs, ys) =
  if pointer_eq (xs, ys) then xs
  else if null xs then ys
  else fold_rev (insert eq) ys xs;

end

val is_equal = Library.is_equal
