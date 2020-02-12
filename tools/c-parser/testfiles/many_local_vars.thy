(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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
