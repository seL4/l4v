(*
 * Copyright 2019, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.

 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.

 * @TAG(DATA61_BSD)
 *)

signature METHOD_UTILS =
sig
  include METHOD

  (* `then_all_new m1 m2` is equivalent to `(m1; m2)`. *)
  val then_all_new:
      (Proof.context -> method) * (Proof.context -> method) -> Proof.context -> method;
end

structure MethodUtils: METHOD_UTILS =
struct
open Method

fun then_all_new (m1, m2) =
    Combinator (no_combinator_info, Then_All_New, [Basic m1, Basic m2]) |> evaluate
end
