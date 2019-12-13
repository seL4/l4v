(*
 * Copyright 2019, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.

 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.

 * @TAG(DATA61_BSD)
 *)

signature TERM_EXTRAS =
sig
  val drop_binders: int -> typ -> typ
end

structure TermExtras: TERM_EXTRAS =
struct

\<comment> \<open>
  Drops the first n binders of a type.
\<close>
fun drop_binders 0 T = T
| drop_binders n (Type ("fun", [_, T])) = drop_binders (n-1) T
| drop_binders _ T = T;

end