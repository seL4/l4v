(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory fnptr
imports "CParser.CTranslation"
begin

external_file "fnptr.c"
install_C_file "fnptr.c"

context fnptr_global_addresses
begin
  thm f_body_def
  thm callthem_body_def
  thm callable1_body_def
  thm voidcaller_body_def
  thm callvoidcaller_body_def

  thm callintcaller_body_def
  thm intcaller_body_def
  thm intcallable1_body_def

declare [[hoare_use_call_tr'=false]]

definition
  "symbols_ok == procs_consistent symbol_table \<Gamma>_naming
        \<and> c_fnptr_guard (Ptr (symbol_table ''callable1''))
        \<and> c_fnptr_guard (Ptr (symbol_table ''intcallable2''))"

lemma cvc_updates_global1: "!!x. \<Gamma> \<turnstile> \<lbrace> \<acute>global1 = x \<and> symbols_ok \<rbrace>
    \<acute>ret__int :== PROC callvoidcaller() \<lbrace> \<acute>global1 = x + 1 \<rbrace>"
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply vcg_step
   apply vcg_step
  apply vcg_step
    apply vcg_step
   apply vcg_step
  apply vcg_step
   apply vcg_step
  apply vcg_step
   defer
   apply vcg_step
    apply vcg_step
   apply vcg_step
     apply vcg_step
    apply vcg_step
   apply vcg_step
    apply vcg_step
   apply vcg_step
    apply (rule order_refl)
   apply (rule hoare_indirect_call_procs_consistent, rule callable1_name)
   apply vcg
  using callable1_name
  apply (clarsimp simp: symbols_ok_def procs_consistent_safe)
  done

lemma cic_returns_4:
  "\<Gamma>\<turnstile> {| symbols_ok |} \<acute>ret__int :== PROC callintcaller()
                        {| \<acute>ret__int = 4 |}"
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply vcg_step
   apply vcg_step
  apply vcg_step
    apply vcg_step
   apply vcg_step
  apply vcg_step
   apply vcg_step

  apply (rule HoarePartial.CallBody
             [where R = "%s t. { u. ret__int_' t = 4 }"
                 and \<Gamma>=\<Gamma>, OF _ _ _ intcaller_impl])
    defer
    apply (simp only: intcaller_body_def)
    apply (rule allI)
    apply vcg_step
     apply vcg_step
    apply vcg_step
      apply vcg_step
     apply vcg_step
    apply vcg_step
     apply vcg_step
    apply vcg_step
     apply (rule order_refl)
    apply (rule hoare_indirect_call_procs_consistent)
     apply (rule intcallable2_name)
    apply simp
    apply vcg
   apply vcg
  using intcallable2_name
  apply (auto simp: symbols_ok_def procs_consistent_safe)[1]
  done

end

end

