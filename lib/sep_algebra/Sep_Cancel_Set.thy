(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory Sep_Cancel_Set
imports Separation_Algebra Sep_Tactic_Helpers
begin

ML \<open>
  structure SepCancel_Rules = Named_Thms (
    val name = @{binding "sep_cancel"}
    val description = "sep_cancel rules"
  )
\<close>

setup SepCancel_Rules.setup

lemma refl_imp: "P \<Longrightarrow> P" by assumption

declare refl_imp[sep_cancel]

declare sep_conj_empty[sep_cancel]
lemmas sep_conj_empty' = sep_conj_empty[simplified sep_conj_commute[symmetric]]
declare sep_conj_empty'[sep_cancel]


end
