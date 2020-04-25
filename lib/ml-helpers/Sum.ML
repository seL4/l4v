(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

signature SUM =
sig
  datatype ('a, 'b) sum = Inl of 'a | Inr of 'b
  val case_sum : ('a -> 'c) -> ('b -> 'c) -> ('a, 'b) sum -> 'c
  val map_sum : ('a -> 'c) -> ('b -> 'd) -> ('a, 'b) sum -> ('c, 'd) sum
  val isl : ('a, 'b) sum -> bool
  val isr : ('a, 'b) sum -> bool
  val froml : 'a -> ('a, 'b) sum -> 'a
  val fromr : 'b -> ('a, 'b) sum -> 'b
  val lefts : ('a, 'b) sum list -> 'a list
  val rights : ('a, 'b) sum list -> 'b list
end


structure Sum: SUM =
struct

datatype ('a, 'b) sum = Inl of 'a | Inr of 'b

fun case_sum f _ (Inl x) = f x
  | case_sum _ g (Inr y) = g y;

fun map_sum f _ (Inl x) = Inl (f x)
  | map_sum _ g (Inr y) = Inr (g y);

fun isl (Inl _) = true
  | isl (Inr _) = false;

fun isr (Inl _) = false
  | isr (Inr _) = true;

fun froml _ (Inl x) = x
  | froml x _ = x;

fun fromr _ (Inr y) = y
  | fromr y _ = y;

fun lefts [] = []
  | lefts (Inl x :: xs) = x :: lefts xs
  | lefts (_ :: xs) = lefts xs;

fun rights [] = []
  | rights (Inr y :: ys) = y :: rights ys
  | rights (_ :: ys) = rights ys;

end

open Sum;
