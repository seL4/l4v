(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory many_local_vars
imports
  "CParser.CTranslation"
begin

(* Avoid memory explosion caused by the C parser generating a huge record
 * containing local variables. *)
declare [[record_codegen = false]]

external_file "many_local_vars.c"
install_C_file "many_local_vars.c"

context "many_local_vars_global_addresses" begin
lemma "\<forall>\<sigma>. \<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> {\<sigma>} Call test_'proc
              {t. t may_not_modify_globals \<sigma>}"
  apply (tactic \<open>HoarePackage.vcg_tac "_modifies" "false" [] @{context} 1\<close>)
done
end

end
