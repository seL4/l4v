(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * Title:      Pure/Concurrent/lazy_sequential.ML
 * Author:     Florian Haftmann and Makarius, TU Muenchen
 *             David Greenaway, NICTA
 *
 * Thread-safe lazy evaluation with memoing, without using futures.
 *)

structure SimpleLazy: LAZY =
struct

(* datatype *)

datatype 'a expr =
  Expr of unit -> 'a |
  Result of 'a Exn.result;

abstype 'a lazy = Lazy of 'a expr Synchronized.var
with

fun peek (Lazy r) =
  (case (Synchronized.value r) of
    Expr _ => NONE
  | Result res => SOME res);

fun lazy e = Lazy (Synchronized.var "simple_lazy" (Expr e));
fun value a = Lazy (Synchronized.var "simple_lazy" (Result (Exn.Res a)));

(* force result *)

fun force_result (Lazy r) =
  Synchronized.change_result r (fn x =>
    (case x of
      Expr e =>
      let
        val x = Exn.capture e ()
      in
        (x, Result x)
      end
    | Result res => (res, Result res)))

fun force r = Exn.release (force_result r);

fun is_finished x = is_some (peek x)

fun map f x = lazy (fn () => f (force x));

fun future params x =
  if is_finished x then Future.value_result (force_result x)
  else (singleton o Future.forks) params (fn () => force x);

end;
end;

type 'a simple_lazy = 'a SimpleLazy.lazy;

