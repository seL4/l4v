(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ProofHelpers_DP
imports
  Kernel_DP
  "SepDSpec.Frame_SD"
begin

crunch_ignore (add:
  Nondet_Monad.bind return "when" get gets fail
  assert put modify unless select
  alternative assert_opt gets_the
  returnOk throwError lift bindE
  liftE whenE unlessE throw_opt
  assertE liftM liftME sequence_x
  zipWithM_x mapM_x sequence mapM sequenceE_x
  mapME_x catch select_f
  handleE' handleE handle_elseE forM forM_x
  zipWithM throw chaos)

lemmas crunch_wps =
  hoare_drop_imps mapM_wp' mapM_x_wp'

lemmas crunch_simps = split_def whenE_def unlessE_def Let_def if_fun_split
                      assertE_def zipWithM_mapM zipWithM_x_mapM

lemma do_kernel_op_wp:
  assumes "\<lbrace> P \<rbrace> f \<lbrace> \<lambda>_ s. Q s \<rbrace>"
  shows "\<lbrace> P \<circ> kernel_state \<rbrace> do_kernel_op f \<lbrace> \<lambda>_ s. Q (kernel_state s) \<rbrace>"
  using assms
  apply (simp only: do_kernel_op_def split_def)
  apply wp
  apply (simp add: valid_def split_def)
  done

end
