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

(* Declare here and define in InfoFlow_IF *)
consts equiv_for :: "('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'c) \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool"

context Arch begin global_naming AARCH64

section \<open>Arch-specific equivalence properties\<close>

subsection \<open>ASID equivalence\<close>

definition equiv_asid :: "asid \<Rightarrow> det_ext state \<Rightarrow> det_ext state \<Rightarrow> bool" where
  "equiv_asid asid s s' \<equiv>
    ((arm_asid_table (arch_state s) (asid_high_bits_of asid)) =
     (arm_asid_table (arch_state s') (asid_high_bits_of asid))) \<and>
    (\<forall>pool_ptr. arm_asid_table (arch_state s) (asid_high_bits_of asid) = Some pool_ptr
                \<longrightarrow> asid_pool_at pool_ptr s = asid_pool_at pool_ptr s' \<and>
                    (\<forall>asid_pool asid_pool'. asid_pools_of s pool_ptr = Some asid_pool \<and>
                                            asid_pools_of s' pool_ptr = Some asid_pool'
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


subsection \<open>VCPU equivalence\<close>

(* FIXME AARCH64 IF: move *)
locale_abbrev numlistregs :: "'s state \<Rightarrow> nat" where
  "numlistregs s \<equiv> arm_gicvcpu_numlistregs (arch_state s)"

(* FIXME AARCH64 IF: move *)
locale_abbrev current_vcpu :: "'s state \<rightharpoonup> obj_ref \<times> bool" where
  "current_vcpu s \<equiv> arm_current_vcpu (arch_state s)"

definition hw_vcpu ::
  "nat \<Rightarrow> bool option \<Rightarrow> vcpu_state \<rightharpoonup> vcpu_state"
where
  "hw_vcpu n cv vcpu \<equiv> case cv of
     None \<Rightarrow> None
   | Some enabled \<Rightarrow> Some
       \<lparr>vcpu_vgic = \<lparr>vgic_hcr = if \<not>enabled then undefined else vgic_hcr (vcpu_vgic vcpu),
                     vgic_vmcr = vgic_vmcr (vcpu_vgic vcpu),
                     vgic_apr = vgic_apr (vcpu_vgic vcpu),
                     vgic_lr = \<lambda>r. if r < n then vgic_lr (vcpu_vgic vcpu) r else undefined\<rparr>,
        vcpu_regs = \<lambda>r. if \<not>enabled \<and> vcpuRegSavedWhenDisabled r
                        then undefined
                        else vcpu_regs vcpu r\<rparr>"

locale_abbrev hw_vcpu_of where
  "hw_vcpu_of s p \<equiv> hw_vcpu (numlistregs s) (cur_vcpu_of s p) (vcpu_state (machine_state s))"

lemmas hw_vcpu_of_def = hw_vcpu_def

definition equiv_hyp :: "(obj_ref \<Rightarrow> bool) \<Rightarrow> det_state \<Rightarrow> det_state \<Rightarrow> bool" where
  "equiv_hyp P s s' \<equiv> equiv_for P (K \<circ> numlistregs) s s' \<and>
                       equiv_for P cur_vcpu_of s s' \<and>
                       equiv_for P hw_vcpu_of s s'"


subsection \<open>FPU equivalence\<close>

(* FIXME AARCH64 IF: move *)
locale_abbrev current_fpu :: "'s state \<rightharpoonup> obj_ref" where
  "current_fpu s \<equiv> arm_current_fpu_owner (arch_state s)"

definition is_arch_cur_fpu_2 :: "obj_ref \<Rightarrow> obj_ref option \<Rightarrow> bool" where
  "is_arch_cur_fpu_2 ptr fopt \<equiv> fopt = Some ptr"

locale_abbrev is_arch_cur_fpu :: "obj_ref \<Rightarrow> 's state \<Rightarrow> bool" where
  "is_arch_cur_fpu ptr s \<equiv> is_arch_cur_fpu_2 ptr (arm_current_fpu_owner (arch_state s))"

lemmas is_arch_cur_fpu_def = is_arch_cur_fpu_2_def

definition hw_fpu :: "bool \<Rightarrow> fpu_state \<Rightarrow> fpu_state option"
where
  "hw_fpu cf fpu \<equiv> if cf then Some fpu else None"

locale_abbrev hw_fpu_of where
  "hw_fpu_of s t \<equiv> hw_fpu (is_arch_cur_fpu t s) (fpu_state (machine_state s))"

definition equiv_fpu :: "(obj_ref \<Rightarrow> bool) \<Rightarrow> det_state \<Rightarrow> det_state \<Rightarrow> bool" where
  "equiv_fpu P s s' \<equiv> equiv_for P hw_fpu_of s s'"


subsection \<open>Global (Kernel) VSpace equivalence\<close>
(* globals_equiv should be maintained by everything except the scheduler, since
   nothing else touches the globals frame *)

definition arch_globals_equiv :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> kheap \<Rightarrow> kheap \<Rightarrow> arch_state \<Rightarrow>
                                  arch_state \<Rightarrow> machine_state \<Rightarrow> machine_state \<Rightarrow> bool" where
  "arch_globals_equiv ct it kh kh' as as' ms ms' \<equiv>
     arm_us_global_vspace as = arm_us_global_vspace as' \<and>
     kh (arm_us_global_vspace as) = kh' (arm_us_global_vspace as)"

declare arch_globals_equiv_def[simp]

end

(* FIXME AARCH64 IF: requalify elsewhere *)
arch_requalify_consts
  equiv_asid
  equiv_asid'
  arch_globals_equiv
  non_asid_pool_kheap_update

end
