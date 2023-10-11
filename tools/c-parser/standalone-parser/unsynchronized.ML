(* SPDX-License-Identifier: BSD-3-Clause *)
(* SPDX-FileCopyrightText: Markus Wenzel, TU Muenchen *)

(*  Extracted from Isabelle sources (src/Pure/Concurrent/unsynchronized.ML),
    reduced to work for mlton *)

signature UNSYNCHRONIZED =
sig
  datatype ref = datatype ref
  val := : 'a ref * 'a -> unit
  val ! : 'a ref -> 'a
  val change: 'a ref -> ('a -> 'a) -> unit
  val change_result: 'a ref -> ('a -> 'b * 'a) -> 'b
  val inc: int ref -> int
  val dec: int ref -> int
  val add: int ref -> int -> int
end;

structure Unsynchronized: UNSYNCHRONIZED =
struct

(* regular references *)

datatype ref = datatype ref;

val op := = op :=;
val ! = !;

fun change r f = r := f (! r);
fun change_result r f = let val (x, y) = f (! r) in r := y; x end;

fun inc i = (i := ! i + (1: int); ! i);
fun dec i = (i := ! i - (1: int); ! i);
fun add i n = (i := ! i + (n: int); ! i);

end;
