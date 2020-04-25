(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
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
