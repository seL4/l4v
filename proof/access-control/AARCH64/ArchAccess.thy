(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchAccess
imports Types
begin

context Arch begin arch_global_naming

subsection \<open>Arch-specific transformation of caps into authorities\<close>

definition vspace_cap_rights_to_auth :: "cap_rights \<Rightarrow> auth set" where
  "vspace_cap_rights_to_auth r \<equiv>
     (if AllowWrite \<in> r then {Write} else {})
   \<union> (if AllowRead \<in> r then {Read} else {})"

definition arch_cap_auth_conferred where
  "arch_cap_auth_conferred arch_cap \<equiv>
     (if is_FrameCap arch_cap then vspace_cap_rights_to_auth (acap_rights arch_cap) else {Control})"

subsection \<open>Generating a policy from the current ASID distribution\<close>

definition pte_ref2 where
  "pte_ref2 level pte \<equiv> case pte of
     PagePTE paddr _ _ rights
       \<Rightarrow> Some (ptrFromPAddr paddr,
                pt_bits_left level,
                vspace_cap_rights_to_auth rights)
   | PageTablePTE ppn
       \<Rightarrow> Some (ptrFromPAddr (paddr_from_ppn ppn), 0, {Control})
   | _ \<Rightarrow> None"

definition vs_refs_aux :: "vm_level \<Rightarrow> arch_kernel_obj \<Rightarrow> (obj_ref \<times> obj_ref \<times> aa_type \<times> auth) set"
  where
  "vs_refs_aux level \<equiv> \<lambda>ko. case ko of
     ASIDPool pool \<Rightarrow> (\<lambda>(r,p). (p, ucast r, AASIDPool, Control)) ` graph_of (option_map ap_vspace o pool)
   | PageTable pt \<Rightarrow> (case pt of
       VSRootPT pt \<Rightarrow> \<Union>(r,(p, sz, auth)) \<in> graph_of (pte_ref2 level o pt).
                      (\<lambda>(p, a). (p, ucast r, APageTable VSRootPT_T, a)) ` (ptr_range p sz \<times> auth)
     | NormalPT pt \<Rightarrow> \<Union>(r,(p, sz, auth)) \<in> graph_of (pte_ref2 level o pt).
                      (\<lambda>(p, a). (p, ucast r, APageTable NormalPT_T, a)) ` (ptr_range p sz \<times> auth))
   | _ \<Rightarrow> {}"

definition state_vrefs where
  "state_vrefs s \<equiv> \<lambda>p.
     \<Union>{vs_refs_aux lvl ao | lvl ao bot asid vref. vs_lookup_table bot asid vref s = Some (lvl, p)
                                                 \<and> vspace_objs_of s p = Some ao \<and> vref \<in> user_region}"

primrec aobj_ref' where
  "aobj_ref' (ASIDPoolCap ref _) = {ref}"
| "aobj_ref' ASIDControlCap = {}"
| "aobj_ref' (FrameCap ref _ sz _ _) = ptr_range ref (pageBitsForSize sz)"
| "aobj_ref' (PageTableCap ref _ _) = {ref}"
| "aobj_ref' (VCPUCap ref) = {ref}"
| "aobj_ref' (SGISignalCap _ _) = {}"

fun acap_asid' :: "arch_cap \<Rightarrow> asid set" where
  "acap_asid' (FrameCap _ _ _ _ mapping) = fst ` set_option mapping"
| "acap_asid' (PageTableCap _ _ mapping) = fst ` set_option mapping"
| "acap_asid' (ASIDPoolCap _ asid) = {x. asid_high_bits_of x = asid_high_bits_of asid \<and> x \<noteq> 0}"
| "acap_asid' ASIDControlCap = UNIV"
| "acap_asid' (VCPUCap _) = {}"
| "acap_asid' (SGISignalCap _ _) = {}"

inductive_set state_asids_to_policy_aux for aag caps asid_tab vrefs where
  sata_asid:
    "\<lbrakk> caps ptr = Some (ArchObjectCap acap); asid \<in> acap_asid' acap \<rbrakk>
       \<Longrightarrow> (pasObjectAbs aag (fst ptr), Control, pasASIDAbs aag asid)
             \<in> state_asids_to_policy_aux aag caps asid_tab vrefs"
| sata_asid_lookup:
    "\<lbrakk> asid_tab (asid_high_bits_of asid) = Some poolptr;
       (pdptr, ucast (asid && mask asid_low_bits), AASIDPool, a) \<in> vrefs poolptr \<rbrakk>
       \<Longrightarrow> (pasASIDAbs aag asid, a, pasObjectAbs aag pdptr)
             \<in> state_asids_to_policy_aux aag caps asid_tab vrefs"
| sata_asidpool:
    "\<lbrakk> asid_tab (asid_high_bits_of asid) = Some poolptr; asid \<noteq> 0 \<rbrakk>
       \<Longrightarrow> (pasObjectAbs aag poolptr, AAuth ASIDPoolMapsASID, pasASIDAbs aag asid)
             \<in> state_asids_to_policy_aux aag caps asid_tab vrefs"

definition
  "state_asids_to_policy_arch aag caps astate vrefs \<equiv>
     state_asids_to_policy_aux aag caps (arm_asid_table astate)
                               (vrefs :: 64 word \<Rightarrow> (64 word \<times> 64 word \<times> aa_type \<times> auth) set)"
declare state_asids_to_policy_arch_def[simp]

section \<open>Arch-specific integrity definition\<close>

subsection \<open>How ASIDs can change\<close>

definition integrity_asids_2 ::
  "'a PAS \<Rightarrow> 'a set \<Rightarrow> obj_ref \<Rightarrow> asid \<Rightarrow> arch_state \<Rightarrow> arch_state \<Rightarrow>
   (obj_ref \<rightharpoonup> arch_kernel_obj) \<Rightarrow> (obj_ref \<rightharpoonup> arch_kernel_obj) \<Rightarrow> bool"
where
  "integrity_asids_2 aag subjects x asid as as' ao ao'  \<equiv>
     (arm_asid_table as (asid_high_bits_of asid) \<noteq> arm_asid_table as' (asid_high_bits_of asid)
      \<longrightarrow> (\<forall>x. arm_asid_table as' (asid_high_bits_of asid) = Some x \<longrightarrow> pasObjectAbs aag x \<in> subjects) \<and>
          (\<forall>asid'. asid' \<noteq> 0 \<and> asid_high_bits_of asid' = asid_high_bits_of asid
                   \<longrightarrow> pasASIDAbs aag asid' \<in> subjects)) \<and>
     (pasObjectAbs aag x \<notin> subjects
      \<longrightarrow> (\<forall>pool. (ao |> asid_pool_of) x = Some pool
                  \<longrightarrow> (ao' |> asid_pool_of) x \<noteq> None \<and>
                      (\<forall>pool'. (ao' |> asid_pool_of) x = Some pool' \<longrightarrow>
                               (pool \<noteq> pool' \<longrightarrow> (\<exists>asid. arm_asid_table as (asid_high_bits_of asid) = Some x)))))"

lemmas integrity_asids_def = integrity_asids_2_def

subsection \<open>How VCPUs can change\<close>

definition vcpu_of_state ::
  "vcpu_state \<Rightarrow> (obj_ref \<times> bool) option \<Rightarrow> nat \<Rightarrow> (obj_ref \<Rightarrow> vcpu option) \<Rightarrow> obj_ref \<Rightarrow> vcpu option"
where
  "vcpu_of_state vst cv n vcpus vcpu_ptr \<equiv>
     \<comment> \<open>Ignore some values\<close>
     let vmask = vcpu_vtimer_update (\<lambda>_. undefined)
               \<circ> vcpu_regs_update (\<lambda>f r. if r = VCPURegCNTVOFF then undefined else f r)
               \<circ> vcpu_vgic_update (vgic_lr_update (\<lambda>f r. if r \<ge> n then undefined else f r))
     in case (vcpus vcpu_ptr, cv) of
       (None,_) \<Rightarrow> None \<comment> \<open>No VCPU\<close>
     | (Some vcpu,None) \<Rightarrow> Some (vmask vcpu) \<comment> \<open>No current VCPU\<close>
     | (Some vcpu, Some (vcpu_ptr',enabled)) \<Rightarrow> Some (vmask
         (if vcpu_ptr' = vcpu_ptr \<comment> \<open>Current VCPU = VCPU\<close>
          then vcpu\<lparr>vcpu_regs := \<lambda>reg. if vcpuRegSavedWhenDisabled reg \<and> \<not>enabled
                                       then vcpu_regs vcpu reg \<comment> \<open>Register saved when VCPU disabled\<close>
                                       else vcpu_regs vst reg,
                    vcpu_vgic := (vcpu_vgic vcpu)
                      \<lparr>vgic_hcr := if \<not>enabled
                                   then vgic_hcr (vcpu_vgic vcpu) \<comment> \<open>Saved when VCPU disabled\<close>
                                   else vgic_hcr (vcpu_vgic vst),
                       vgic_vmcr := vgic_vmcr (vcpu_vgic vst),
                       vgic_apr := vgic_apr (vcpu_vgic vst),
                       vgic_lr := vgic_lr (vcpu_vgic vst)\<rparr>\<rparr>
          else vcpu))" \<comment> \<open>Not current VCPU\<close>

definition vcpu_integrity where
   "vcpu_integrity aag subjects x hv hv' cv cv' n n' vcpus vcpus' \<equiv>
    (pasObjectAbs aag x \<notin> subjects \<longrightarrow> vcpu_of_state hv cv n vcpus x = vcpu_of_state hv' cv' n' vcpus' x)"

definition integrity_hyp_2 ::
  "'a PAS \<Rightarrow> 'a set \<Rightarrow> obj_ref \<Rightarrow> machine_state \<Rightarrow> machine_state \<Rightarrow> arch_state \<Rightarrow> arch_state
          \<Rightarrow> (obj_ref \<Rightarrow> arch_kernel_obj option) \<Rightarrow> (obj_ref \<Rightarrow> arch_kernel_obj option) \<Rightarrow> bool"
where
  "integrity_hyp_2 aag subjects x ms ms' as as' aobjs aobjs' \<equiv>
     arm_gicvcpu_numlistregs as = arm_gicvcpu_numlistregs as' \<and>
     vcpu_integrity aag subjects x (vcpu_state ms) (vcpu_state ms')
                                        (arm_current_vcpu as) (arm_current_vcpu as')
                                        (arm_gicvcpu_numlistregs as) (arm_gicvcpu_numlistregs as')
                                        (aobjs |> vcpu_of) (aobjs' |> vcpu_of)"

lemmas integrity_hyp_def = integrity_hyp_2_def

definition "valid_cur_hyp \<equiv> valid_cur_vcpu"

subsection \<open>How FPUs can change\<close>

definition fpu_of_state :: "fpu_state \<Rightarrow> (obj_ref \<Rightarrow> kernel_object option) \<Rightarrow> obj_ref \<Rightarrow> fpu_state option"
where
  "fpu_of_state hw_fpu kh t \<equiv>
     case kh t of
       Some (TCB tcb) \<Rightarrow> Some (if tcb_cur_fpu (tcb_arch tcb) then hw_fpu
                               else user_fpu_state (tcb_context (tcb_arch tcb)))
     | _ \<Rightarrow> None"

definition integrity_fpu_2 ::
  "'a PAS \<Rightarrow> 'a set \<Rightarrow> obj_ref \<Rightarrow> machine_state \<Rightarrow> machine_state
          \<Rightarrow> (obj_ref \<Rightarrow> kernel_object option) \<Rightarrow> (obj_ref \<Rightarrow> kernel_object option) \<Rightarrow> bool"
where
  "integrity_fpu_2 aag subjects x ms ms' kh kh' \<equiv>
     (pasObjectAbs aag x \<notin> subjects
      \<longrightarrow> fpu_of_state (fpu_state ms) kh x = fpu_of_state (fpu_state ms') kh' x)"

lemmas integrity_fpu_def = integrity_fpu_2_def

subsection \<open>How arch objects can change\<close>

definition asid_pool_integrity ::
  "'a set \<Rightarrow> 'a PAS \<Rightarrow> (asid_low_index \<rightharpoonup> asid_pool_entry) \<Rightarrow> (asid_low_index \<rightharpoonup> asid_pool_entry) \<Rightarrow> bool" where
  "asid_pool_integrity subjects aag pool pool' \<equiv>
     \<forall>x. pool' x \<noteq> pool x
         \<longrightarrow> pool' x = None \<and> aag_subjects_have_auth_to subjects aag Control (ap_vspace (the (pool x)))"

inductive arch_integrity_obj_atomic ::
   "'a PAS \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> arch_kernel_obj \<Rightarrow> arch_kernel_obj \<Rightarrow> bool"
  for aag subjects l ao ao' where
  arch_troa_asidpool_clear:
    "\<lbrakk> ao = ASIDPool pool; ao' = ASIDPool pool';
       asid_pool_integrity subjects aag pool pool' \<rbrakk>
       \<Longrightarrow> arch_integrity_obj_atomic aag subjects l ao ao'"
  (* Allow any VCPU changes; constraints are imposed by integrity_hyp instead *)
| arch_troa_vcpu:
    "\<lbrakk> ao = VCPU vcpu; ao' = VCPU vcpu' \<rbrakk>
       \<Longrightarrow> arch_integrity_obj_atomic aag subjects l ao ao'"

inductive arch_integrity_obj_alt ::
   "'a PAS \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> arch_kernel_obj \<Rightarrow> arch_kernel_obj \<Rightarrow> bool"
  for aag subjects l' ao ao' where
  arch_tro_alt_asidpool_clear:
    "\<lbrakk> ao = ASIDPool pool; ao' = ASIDPool pool';
       asid_pool_integrity subjects aag pool pool'\<rbrakk>
       \<Longrightarrow> arch_integrity_obj_alt aag subjects l' ao ao'"
| arch_tro_alt_vcpu:
    "\<lbrakk> ao = VCPU vcpu; ao' = VCPU vcpu' \<rbrakk>
       \<Longrightarrow> arch_integrity_obj_alt aag subjects l' ao ao'"

subsection \<open>Misc definitions\<close>

abbreviation arch_IP_update where
  "arch_IP_update a \<equiv>
   arch_tcb_set_registers ((arch_tcb_get_registers a)(NextIP := arch_tcb_get_registers a FaultIP)) a"

definition auth_ipc_buffers :: "'z::state_ext state \<Rightarrow> obj_ref \<Rightarrow> obj_ref set" where
  "auth_ipc_buffers s \<equiv> \<lambda>p. case (get_tcb p s) of
     None \<Rightarrow> {}
   | Some tcb \<Rightarrow>
     (case tcb_ipcframe tcb of
        ArchObjectCap (FrameCap p' R vms False _) \<Rightarrow>
          if AllowWrite \<in> R
          then (ptr_range (p' + (tcb_ipc_buffer tcb && mask (pageBitsForSize vms))) msg_align_bits)
          else {}
      | _ \<Rightarrow> {})"

end

end
