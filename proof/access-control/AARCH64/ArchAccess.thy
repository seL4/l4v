(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchAccess
imports Types
begin

context Arch begin global_naming AARCH64

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

lemma state_vrefsD:
  "\<lbrakk> vs_lookup_table level asid vref s = Some (lvl, p);
     vspace_objs_of s p = Some ao; vref \<in> user_region; x \<in> vs_refs_aux lvl ao \<rbrakk>
     \<Longrightarrow> x \<in> state_vrefs s p"
  unfolding state_vrefs_def by fastforce

end

context Arch_p_arch_update_eq begin global_naming AARCH64

interpretation Arch .

lemma state_vrefs[iff]: "state_vrefs (f s) = state_vrefs s"
  by (simp add: state_vrefs_def pspace)

end

context Arch begin global_naming AARCH64

lemmas state_vrefs_upd =
  cur_thread_update.state_vrefs
  cdt_update.state_vrefs
  irq_node_update_arch.state_vrefs
  interrupt_update.state_vrefs
  revokable_update.state_vrefs
  machine_state_update.state_vrefs
  more_update.state_vrefs

end

context Arch begin

primrec aobj_ref' where
  "aobj_ref' (ASIDPoolCap ref _) = {ref}"
| "aobj_ref' ASIDControlCap = {}"
| "aobj_ref' (FrameCap ref _ sz _ _) = ptr_range ref (pageBitsForSize sz)"
| "aobj_ref' (PageTableCap ref _ _) = {ref}"
| "aobj_ref' (VCPUCap ref) = {ref}"

fun acap_asid' :: "arch_cap \<Rightarrow> asid set" where
  "acap_asid' (FrameCap _ _ _ _ mapping) = fst ` set_option mapping"
| "acap_asid' (PageTableCap _ _ mapping) = fst ` set_option mapping"
| "acap_asid' (ASIDPoolCap _ asid) = {x. asid_high_bits_of x = asid_high_bits_of asid \<and> x \<noteq> 0}"
| "acap_asid' ASIDControlCap = UNIV"
| "acap_asid' (VCPUCap _) = {}"

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

abbreviation integrity_asids_aux :: "'a PAS \<Rightarrow> 'a set \<Rightarrow> obj_ref \<Rightarrow> asid \<Rightarrow>
                                     (asid_high_index \<rightharpoonup> obj_ref) \<Rightarrow> (asid_high_index \<rightharpoonup> obj_ref) \<Rightarrow>
                                     (obj_ref \<rightharpoonup> asid_pool) \<Rightarrow> (obj_ref \<rightharpoonup> asid_pool) \<Rightarrow> bool" where
  "integrity_asids_aux aag subjects x asid atab atab' pools pools'  \<equiv>
     (atab (asid_high_bits_of asid) \<noteq> atab' (asid_high_bits_of asid)
      \<longrightarrow> (\<forall>x. atab' (asid_high_bits_of asid) = Some x \<longrightarrow> pasObjectAbs aag x \<in> subjects) \<and>
          (\<forall>asid'. asid' \<noteq> 0 \<and> asid_high_bits_of asid' = asid_high_bits_of asid
                   \<longrightarrow> pasASIDAbs aag asid' \<in> subjects)) \<and>
     (pasObjectAbs aag x \<notin> subjects
      \<longrightarrow> (\<forall>pool. pools x = Some pool
                  \<longrightarrow> pools' x \<noteq> None \<and>
                      (\<forall>pool'. pools' x = Some pool' \<longrightarrow>
                               (pool \<noteq> pool' \<longrightarrow> (\<exists>asid. atab (asid_high_bits_of asid) = Some x)))))"

definition integrity_asids ::
  "'a PAS \<Rightarrow> 'a set \<Rightarrow> obj_ref \<Rightarrow> asid \<Rightarrow> 'y::state_ext state \<Rightarrow> 'z::state_ext state  \<Rightarrow> bool" where
  "integrity_asids aag subjects x asid s s' \<equiv>
   integrity_asids_aux aag subjects x asid (asid_table s) (asid_table s')
                                           (asid_pools_of s) (asid_pools_of s')"

sublocale kheap_update: Arch_arch_update_eq "kheap_update f"
  by unfold_locales simp

lemma (in Arch_p_arch_update_eq) integrity_asids_update[simp]:
  "integrity_asids aag subjects x a (f st) s = integrity_asids aag subjects x a st s"
  "integrity_asids aag subjects x a st (f s) = integrity_asids aag subjects x a st s"
  by (auto simp: integrity_asids_def arch pspace)

lemmas integrity_asids_updates =
  cdt_update.integrity_asids_update
  more_update.integrity_asids_update
  revokable_update.integrity_asids_update
  interrupt_update.integrity_asids_update
  cur_thread_update.integrity_asids_update
  machine_state_update.integrity_asids_update

lemma integrity_asids_cnode_update':
  "\<lbrakk> kheap st p = Some (CNode sz cs); integrity_asids aag subjects x a st (s\<lparr>kheap := rest\<rparr>) \<rbrakk>
     \<Longrightarrow> integrity_asids aag subjects x a st (s\<lparr>kheap := \<lambda>x. if x = p then v else rest x\<rparr>)"
  by (auto simp: integrity_asids_def opt_map_def split: option.splits)

lemma integrity_asids_tcb_update':
  "\<lbrakk> kheap st p = Some (TCB tcb); integrity_asids aag subjects x a st (s\<lparr>kheap := rest\<rparr>) \<rbrakk>
     \<Longrightarrow> integrity_asids aag subjects x a st (s\<lparr>kheap := \<lambda>x. if x = p then v else rest x\<rparr>)"
  by (auto simp: integrity_asids_def opt_map_def split: option.splits)

lemma integrity_asids_ep_update':
  "\<lbrakk> kheap st p = Some (Endpoint ep); integrity_asids aag subjects x a st (s\<lparr>kheap := rest\<rparr>) \<rbrakk>
     \<Longrightarrow> integrity_asids aag subjects x a st (s\<lparr>kheap := \<lambda>x. if x = p then v else rest x\<rparr>)"
  by (auto simp: integrity_asids_def opt_map_def split: option.splits)

lemma integrity_asids_ntfn_update':
  "\<lbrakk> kheap st p = Some (Notification ntfn); integrity_asids aag subjects x a st (s\<lparr>kheap := rest\<rparr>) \<rbrakk>
     \<Longrightarrow> integrity_asids aag subjects x a st (s\<lparr>kheap := \<lambda>x. if x = p then v else rest x\<rparr>)"
  by (auto simp: integrity_asids_def opt_map_def split: option.splits)

lemmas integrity_asids_kh_upds'' =
  integrity_asids_cnode_update'
  integrity_asids_tcb_update'
  integrity_asids_ep_update'
  integrity_asids_ntfn_update'

lemmas integrity_asids_kh_upds =
  integrity_asids_kh_upds''
  integrity_asids_kh_upds''[where rest="kheap s" and s=s for s, folded fun_upd_def, simplified]

declare integrity_asids_def[simp]

lemma integrity_asids_kh_upds':
  "integrity_asids aag subjects x a (s\<lparr>kheap := (kheap s)(p \<mapsto> CNode sz cs)\<rparr>) s"
  "integrity_asids aag subjects x a (s\<lparr>kheap := (kheap s)(p \<mapsto> TCB tcb)\<rparr>) s"
  "integrity_asids aag subjects x a (s\<lparr>kheap := (kheap s)(p \<mapsto> Endpoint ep)\<rparr>) s"
  "integrity_asids aag subjects x a (s\<lparr>kheap := (kheap s)(p \<mapsto> Notification ntfn)\<rparr>) s"
  by (auto simp: opt_map_def split: option.splits)

lemma integrity_asids_kh_update:
  "integrity_asids aag subject x a (s\<lparr>kheap := kh\<rparr>) (s\<lparr>kheap := kh'\<rparr>)
   \<Longrightarrow> integrity_asids aag subject x a (s\<lparr>kheap := kh(p := v)\<rparr>) (s\<lparr>kheap := kh'(p := v)\<rparr>)"
  by (clarsimp simp: opt_map_def)


subsection \<open>Misc definitions\<close>

fun ctxt_IP_update where
  "ctxt_IP_update (UserContext fpu ctxt) = UserContext fpu (ctxt(NextIP := ctxt FaultIP))"

lemma ctxt_IP_update_def:
  "ctxt_IP_update ctxt =
   (case ctxt of (UserContext fpu ctxt') \<Rightarrow> UserContext fpu (ctxt'(NextIP := ctxt' FaultIP)))"
  by (cases ctxt; clarsimp)

abbreviation arch_IP_update where
  "arch_IP_update arch \<equiv> arch_tcb_context_set (ctxt_IP_update (arch_tcb_context_get arch)) arch"

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

inductive arch_integrity_obj_alt ::
   "'a PAS \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> arch_kernel_obj \<Rightarrow> arch_kernel_obj \<Rightarrow> bool"
  for aag subjects l' ao ao' where
  arch_tro_alt_asidpool_clear:
    "\<lbrakk> ao = ASIDPool pool; ao' = ASIDPool pool';
       asid_pool_integrity subjects aag pool pool'\<rbrakk>
       \<Longrightarrow> arch_integrity_obj_alt aag subjects l' ao ao'"

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


context begin interpretation Arch .

requalify_consts
  vspace_cap_rights_to_auth
  aobj_ref'
  acap_asid'
  state_vrefs
  state_asids_to_policy_arch
  integrity_asids
  ctxt_IP_update
  arch_IP_update
  arch_cap_auth_conferred
  arch_integrity_obj_atomic
  arch_integrity_obj_alt
  auth_ipc_buffers

requalify_facts
  integrity_asids_updates
  state_vrefs_upd
  integrity_asids_kh_upds
  integrity_asids_kh_upds'
  integrity_asids_kh_update

end

declare state_vrefs_upd[simp]
declare integrity_asids_updates[simp]


context Arch begin global_naming AARCH64

(* FIXME AARCH64: update the access control spec
   -Parameterise arch object updates with machine state and arch state
   -Model virtualised machine state more explicitly
   -Specify when virtualised machine state can change (i.e. restoring from current VCPU)
   -Specify when arm_current_vcpu can change (i.e. once current VCPU has been saved)
   -Specify integrity constraints for FPUs
*)

\<comment> \<open>Anyone can save virtualised registers to the current VCPU\<close>
lemma arch_troa_vcpu_save_reg:
    "\<lbrakk> aobjs_of s vptr = Some (VCPU vcpu); ao' = VCPU vcpu';
       option_map fst (arm_current_vcpu (arch_state s)) = Some vptr;
       vcpu' = vcpu\<lparr>vcpu_regs := (vcpu_regs vcpu)(reg := vcpuHardwareReg_val reg (machine_state s))\<rparr> \<rbrakk>
       \<Longrightarrow> arch_integrity_obj_atomic aag subjects l ao ao'"
  sorry

(* FIXME AARCH64: assert a connection to the current (or soon-to-be-switched-to) thread? *)
\<comment> \<open>Anyone can update the virtual count offset in the current VCPU\<close>
lemma arch_troa_vcpu_restore_vtimer:
  "\<lbrakk> aobjs_of s vptr = Some (VCPU vcpu); ao' = VCPU vcpu';
     option_map fst (arm_current_vcpu (arch_state s)) = Some vptr;
     vcpu' = vcpu\<lparr>vcpu_regs := (vcpu_regs vcpu)
                    (VCPURegCNTVOFF := vcpu_regs vcpu VCPURegCNTVOFF
                                       + (read_cntpct_val (machine_state s)
                                          - vtimerLastPCount (vcpu_vtimer vcpu)))\<rparr> \<rbrakk>
     \<Longrightarrow> arch_integrity_obj_atomic aag subjects l ao ao'"
  sorry

\<comment> \<open>Anyone can save the physical count register to the current VCPU\<close>
lemma arch_troa_vcpu_save_virt_timer:
    "\<lbrakk> aobjs_of s vptr = Some (VCPU vcpu); ao' = VCPU vcpu';
       option_map fst (arm_current_vcpu (arch_state s)) = Some vptr;
       vcpu' = vcpu\<lparr>vcpu_vtimer := VirtTimer (read_cntpct_val (machine_state s))\<rparr> \<rbrakk>
       \<Longrightarrow> arch_integrity_obj_atomic aag subjects l ao ao'"
  sorry

\<comment> \<open>Anyone can save virtualised GIC registers to the current VCPU\<close>
lemma arch_troa_vcpu_save_vgic:
    "\<lbrakk> aobjs_of s vptr = Some (VCPU vcpu); ao' = VCPU vcpu';
       option_map fst (arm_current_vcpu (arch_state s)) = Some vptr;
       vcpu' = vcpu \<lparr>vcpu_vgic := vgic\<rparr>;
       vgic = vcpu_vgic vcpu\<lparr>vgic_hcr := gic_vcpu_ctrl_hcr_val (machine_state s)\<rparr> \<or>
       vgic = vcpu_vgic vcpu\<lparr>vgic_vmcr := gic_vcpu_ctrl_vmcr_val (machine_state s)\<rparr> \<or>
       vgic = vcpu_vgic vcpu\<lparr>vgic_apr := gic_vcpu_ctrl_apr_val (machine_state s)\<rparr> \<or>
       vgic = vcpu_vgic vcpu\<lparr>vgic_lr := (vgic_lr (vcpu_vgic vcpu))
                                        (vreg := gic_vcpu_ctrl_lr_val (of_nat vreg) (machine_state s))\<rparr> \<rbrakk>
       \<Longrightarrow> arch_integrity_obj_atomic aag subjects l ao ao'"
  sorry

\<comment> \<open>Update the vmid of a pool\<close>
lemma
  arch_troa_asidpool_vmid:
    "\<lbrakk> ao = ASIDPool pool; ao' = ASIDPool pool';
       \<forall>x. (pool x = None) = (pool' x = None);
       \<forall>x e e'. pool x = Some e \<and> pool' x = Some e'
           \<longrightarrow> (ap_vspace e = ap_vspace e' \<and>
               (ap_vmid e = ap_vmid e' \<or> ap_vmid e = None \<or> ap_vmid e' = None)) \<rbrakk>
       \<Longrightarrow> arch_integrity_obj_atomic aag subjects l ao ao'"
  sorry

\<comment> \<open>If a VCPU belongs to the current agent, then so does its associated TCB\<close>
lemma associated_tcb_is_subject:
  "\<lbrakk> vcpus_of s v = Some vcpu; vcpu_tcb vcpu = Some t; is_subject aag v \<rbrakk>
     \<Longrightarrow> is_subject aag t"
  sorry

\<comment> \<open>If a TCB belongs to the current agent, then so does its associated VCPU\<close>
lemma associated_vcpu_is_subject:
  "\<lbrakk> get_tcb t s = Some tcb; tcb_vcpu (tcb_arch tcb) = Some v; is_subject aag t \<rbrakk>
     \<Longrightarrow> is_subject aag v"
  sorry

(* FIXME AARCH64: clarify when we can assume this *)
lemma invs_valid_cur_vcpu:
  "invs s \<Longrightarrow> valid_cur_vcpu s"
  sorry

end

end
