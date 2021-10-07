(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory AutoCorresSimpset
imports SimplBucket
begin

lemma globals_surj: "surj globals"
  apply (rule surjI [where f="\<lambda>x. undefined\<lparr> globals := x\<rparr>"])
  apply simp
  done

(*
 * The "full" simpset used internally within AutoCorres during
 * processing.
 *)
ML \<open>

val AUTOCORRES_SIMPSET =
  @{context} delsimps (
    (* interferes with heap_lift *)
    @{thms fun_upd_apply}
    (* affects boolean expressions *)
    @ @{thms word_neq_0_conv neq0_conv}
    (* interferes with struct_rewrite *)
    @ @{thms ptr_coerce.simps ptr_add_0_id}
    (* oversimplifies Spec sets prior to L2 stage
       (we will control this explicitly in L2Peephole) *)
    @ @{thms CollectPairFalse})
    (* avoid take_bit terms in word abstraction and user simps *)
    @ @{thms of_int_and_nat}
  addsimps (
    (* Needed for L2corres_spec *)
    @{thms globals_surj}
    )
  |> simpset_of

\<close>

end
