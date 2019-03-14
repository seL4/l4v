(*
 * Copyright 2019, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

theory ArchKernelInit_AI
imports
  "../ADT_AI"
  "../Tcb_AI"
  "../Arch_AI"
begin

context Arch begin global_naming RISCV64

text {*
  Showing that there is a state that satisfies the abstract invariants.
*}

definition
  "init_vspace_uses p \<equiv>
     if p \<in> {pptr_base ..< kernel_base} then RISCVVSpaceKernelWindow
     else if kernel_base \<le> p then RISCVVSpaceKernelELFWindow
     else if p \<le> user_vtop then RISCVVSpaceUserRegion
     else RISCVVSpaceInvalidRegion"

lemma "valid_uses_2 init_vspace_uses"
  using user_vtop_pptr_base pptr_base_kernel_base user_vtop_pptr_base[simp del]
  unfolding valid_uses_2_def init_vspace_uses_def
  by (auto intro: below_user_vtop_canonical above_pptr_base_canonical)

(* FIXME RISCV: TODO *)

end

end
