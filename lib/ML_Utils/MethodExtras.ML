(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

signature METHOD_EXTRAS =
sig
  (* `then_all_new m1 m2` is equivalent to `(m1; m2)`. *)
  val then_all_new:
      (Proof.context -> Method.method) * (Proof.context -> Method.method)
      -> Proof.context -> Method.method;
end

structure MethodExtras: METHOD_EXTRAS =
struct
open Method

fun then_all_new (m1, m2) =
    Combinator (no_combinator_info, Then_All_New, [Basic m1, Basic m2]) |> evaluate

end
