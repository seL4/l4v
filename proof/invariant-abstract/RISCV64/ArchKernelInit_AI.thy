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

lemma "valid_uses_2 init_vspace_uses"
  using canonical_user_pptr_base pptr_base_kernel_base
  unfolding valid_uses_2_def init_vspace_uses_def window_defs
  by (auto intro: canonical_user_canonical above_pptr_base_canonical)

(* FIXME RISCV: TODO *)

end

end
