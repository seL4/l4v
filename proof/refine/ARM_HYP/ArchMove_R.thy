(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Arch specific lemmas that should be moved into theory files before Refine *)

theory ArchMove_R
imports
  Move_R
begin

(* Use one of these forms everywhere, rather than choosing at random. *)
lemmas cte_index_repair = mult.commute[where a="(2::'a::len word) ^ cte_level_bits"]
lemmas cte_index_repair_sym = cte_index_repair[symmetric]

lemmas of_nat_inj32 = of_nat_inj[where 'a=32, folded word_bits_def]

(* prefer 2 as a tactic *)
method prefer_next = tactic \<open>SUBGOAL (K (prefer_tac 2)) 1\<close>

context begin interpretation Arch .

(* Move to Deterministic_AI*)
crunches copy_global_mappings
  for valid_etcbs[wp]: valid_etcbs (wp: mapM_x_wp')

(* Move to Machine_AI *)
lemma no_fail_writeContextIDAndPD[wp]: "no_fail \<top> (writeContextIDAndPD a w)"
  by (simp add: writeContextIDAndPD_def)

(* Move to Machine_AI *)
crunches
  get_gic_vcpu_ctrl_apr, get_gic_vcpu_ctrl_lr, addressTranslateS1, getHDFAR, getHSR,
  writeVCPUHardwareReg, readVCPUHardwareReg, get_gic_vcpu_ctrl_vmcr, get_gic_vcpu_ctrl_hcr,
  set_gic_vcpu_ctrl_hcr, set_gic_vcpu_ctrl_vmcr, setHCR, setSCTLR,
  set_gic_vcpu_ctrl_lr, set_gic_vcpu_ctrl_apr
  for (no_fail) no_fail[wp, intro!, simp]
  (wp: no_fail_machine_op_lift crunch_wps
   ignore: get_gic_vcpu_ctrl_lr_impl bind addressTranslateS1_impl writeVCPUHardwareReg_impl
           set_gic_vcpu_ctrl_hcr_impl set_gic_vcpu_ctrl_vmcr_impl setHCR_impl setSCTLR_impl
           set_gic_vcpu_ctrl_lr_impl set_gic_vcpu_ctrl_apr_impl)

(* Move to ArchVSpace_AI *)
lemma flush_space_vspace_objs[wp]:
  "\<lbrace>valid_vspace_objs\<rbrace> flush_space space \<lbrace>\<lambda>rv. valid_vspace_objs\<rbrace>"
  by (wpsimp simp: flush_space_def)

end

end
