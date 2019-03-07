(*
 * Copyright 2019, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.

 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.

 * @TAG(DATA61_BSD)
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
