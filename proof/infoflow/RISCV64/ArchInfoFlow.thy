(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchInfoFlow
imports
  "Access.ArchSyscall_AC"
  "Lib.EquivValid"
begin

context Arch begin global_naming RISCV64

section \<open>Arch-specific equivalence properties\<close>

subsection \<open>ASID equivalence\<close>

definition equiv_asid :: "asid \<Rightarrow> det_ext state \<Rightarrow> det_ext state \<Rightarrow> bool" where
  "equiv_asid asid s s' \<equiv>
    ((riscv_asid_table (arch_state s) (asid_high_bits_of asid)) =
     (riscv_asid_table (arch_state s') (asid_high_bits_of asid))) \<and>
    (\<forall>pool_ptr. riscv_asid_table (arch_state s) (asid_high_bits_of asid) = Some pool_ptr
                \<longrightarrow> asid_pool_at pool_ptr s = asid_pool_at pool_ptr s' \<and>
                    (\<forall>asid_pool asid_pool'. asid_pools_of False s pool_ptr = Some asid_pool \<and>
                                            asid_pools_of False s' pool_ptr = Some asid_pool'
                                            \<longrightarrow> asid_pool (asid_low_bits_of asid) =
                                                asid_pool' (asid_low_bits_of asid)))"

definition equiv_asid' where
  "equiv_asid' asid pool_ptr_opt pool_ptr_opt' kh kh' \<equiv>
    (case pool_ptr_opt of None \<Rightarrow> pool_ptr_opt' = None
                        | Some pool_ptr \<Rightarrow>
       (case pool_ptr_opt' of None \<Rightarrow> False
                            | Some pool_ptr' \<Rightarrow>
          (pool_ptr' = pool_ptr \<and>
           ((\<exists>asid_pool. kh pool_ptr = Some (ArchObj (ASIDPool asid_pool))) =
            (\<exists>asid_pool'. kh' pool_ptr' = Some (ArchObj (ASIDPool asid_pool')))) \<and>
           (\<forall>asid_pool asid_pool'. kh pool_ptr = Some (ArchObj (ASIDPool asid_pool)) \<and>
                                   kh' pool_ptr' = Some (ArchObj (ASIDPool asid_pool'))
                                   \<longrightarrow> asid_pool (asid_low_bits_of asid) =
                                       asid_pool' (asid_low_bits_of asid)))))"

definition non_asid_pool_kheap_update where
  "non_asid_pool_kheap_update s kh \<equiv>
     \<forall>x. (\<exists>asid_pool. kheap s x = Some (ArchObj (ASIDPool asid_pool)) \<or>
                      kh x = Some (ArchObj (ASIDPool asid_pool)))
         \<longrightarrow> kheap s x = kh x"


subsection \<open>Exclusive machine state equivalence\<close>

subsection \<open>Global (Kernel) VSpace equivalence\<close>
(* globals_equiv should be maintained by everything except the scheduler, since
   nothing else touches the globals frame *)

definition arch_globals_equiv :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> kheap \<Rightarrow> kheap \<Rightarrow> arch_state \<Rightarrow>
                                  arch_state \<Rightarrow> machine_state \<Rightarrow> machine_state \<Rightarrow> bool" where
  "arch_globals_equiv ct it kh kh' as as' ms ms' \<equiv>
     riscv_global_pt as = riscv_global_pt as' \<and>
     kh (riscv_global_pt as) = kh' (riscv_global_pt as)"

declare arch_globals_equiv_def[simp]

end

requalify_consts
  RISCV64.equiv_asid
  RISCV64.equiv_asid'
  RISCV64.arch_globals_equiv
  RISCV64.non_asid_pool_kheap_update

end
