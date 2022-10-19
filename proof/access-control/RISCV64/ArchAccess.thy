(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchAccess
imports Types
begin

context Arch begin global_naming RISCV64

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
     PagePTE ppn atts rights
       \<Rightarrow> Some (ptrFromPAddr (addr_from_ppn ppn),
                pageBitsForSize (vmpage_size_of_level level),
                vspace_cap_rights_to_auth rights)
   | PageTablePTE ppn atts
       \<Rightarrow> Some (ptrFromPAddr (addr_from_ppn ppn), 0, {Control})
   | _ \<Rightarrow> None"

definition vs_refs_aux :: "vm_level \<Rightarrow> arch_kernel_obj \<Rightarrow> (obj_ref \<times> obj_ref \<times> aa_type \<times> auth) set"
  where
  "vs_refs_aux level \<equiv> \<lambda>ko. case ko of
     ASIDPool pool \<Rightarrow> (\<lambda>(r,p). (p, ucast r, AASIDPool, Control)) ` graph_of pool
   | PageTable pt \<Rightarrow>
       \<Union>(r,(p, sz, auth)) \<in> graph_of (pte_ref2 level o pt) - {(x,y). x \<in> kernel_mapping_slots \<and> level = max_pt_level}.
         (\<lambda>(p, a). (p, ucast r, APageTable, a)) ` (ptr_range p sz \<times> auth)
   | _ \<Rightarrow> {}"

definition state_vrefs where
  "state_vrefs s \<equiv> \<lambda>p.
     \<Union>{vs_refs_aux lvl ao | lvl ao bot asid vref. vs_lookup_table bot asid vref s = Some (lvl, p)
                                                   \<and> aobjs_of False s p = Some ao \<and> vref \<in> user_region}"

lemma state_vrefsD[simplified f_kheap_to_kheap]:
  "\<lbrakk> vs_lookup_table level asid vref s = Some (lvl, p);
     aobjs_of False s p = Some ao; vref \<in> user_region; x \<in> vs_refs_aux lvl ao \<rbrakk>
     \<Longrightarrow> x \<in> state_vrefs s p"
  unfolding state_vrefs_def by fastforce

end

context Arch_p_arch_update_eq begin global_naming RISCV64

interpretation Arch .

lemma state_vrefs[iff]: "state_vrefs (f s) = state_vrefs s"
  by (simp add: state_vrefs_def pspace ta_filter_def obind_def)

end

context Arch begin global_naming RISCV64

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
  "aobj_ref' (ASIDPoolCap p as) = {p}"
| "aobj_ref' ASIDControlCap = {}"
| "aobj_ref' (FrameCap ref cR sz dev as) = ptr_range ref (pageBitsForSize sz)"
| "aobj_ref' (PageTableCap x as3) = {x}"

fun acap_asid' :: "arch_cap \<Rightarrow> asid set" where
  "acap_asid' (FrameCap _ _ _ _ mapping) = fst ` set_option mapping"
| "acap_asid' (PageTableCap _ mapping) = fst ` set_option mapping"
| "acap_asid' (ASIDPoolCap _ asid)
     = {x. asid_high_bits_of x = asid_high_bits_of asid \<and> x \<noteq> 0}"
| "acap_asid' ASIDControlCap = UNIV"

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
     state_asids_to_policy_aux aag caps (riscv_asid_table astate)
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
                                           (asid_pools_of False s) (asid_pools_of False s')"

sublocale kheap_update: Arch_arch_update_eq "kheap_update f"
  by unfold_locales simp

lemma (in Arch_p_arch_update_eq) integrity_asids_update[simp]:
  "integrity_asids aag subjects x a (f st) s = integrity_asids aag subjects x a st s"
  "integrity_asids aag subjects x a st (f s) = integrity_asids aag subjects x a st s"
  by (auto simp: integrity_asids_def arch pspace ta_filter_def obind_def)

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
  by (auto simp: integrity_asids_def opt_map_def obind_def split: option.splits)

lemma integrity_asids_tcb_update':
  "\<lbrakk> kheap st p = Some (TCB tcb); integrity_asids aag subjects x a st (s\<lparr>kheap := rest\<rparr>) \<rbrakk>
     \<Longrightarrow> integrity_asids aag subjects x a st (s\<lparr>kheap := \<lambda>x. if x = p then v else rest x\<rparr>)"
  by (auto simp: integrity_asids_def opt_map_def obind_def split: option.splits)

lemma integrity_asids_ep_update':
  "\<lbrakk> kheap st p = Some (Endpoint ep); integrity_asids aag subjects x a st (s\<lparr>kheap := rest\<rparr>) \<rbrakk>
     \<Longrightarrow> integrity_asids aag subjects x a st (s\<lparr>kheap := \<lambda>x. if x = p then v else rest x\<rparr>)"
  by (auto simp: integrity_asids_def opt_map_def obind_def split: option.splits)

lemma integrity_asids_ntfn_update':
  "\<lbrakk> kheap st p = Some (Notification ntfn); integrity_asids aag subjects x a st (s\<lparr>kheap := rest\<rparr>) \<rbrakk>
     \<Longrightarrow> integrity_asids aag subjects x a st (s\<lparr>kheap := \<lambda>x. if x = p then v else rest x\<rparr>)"
  by (auto simp: integrity_asids_def opt_map_def obind_def split: option.splits)

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
  "integrity_asids aag subjects x a (s\<lparr>kheap := kheap s(p \<mapsto> CNode sz cs)\<rparr>) s"
  "integrity_asids aag subjects x a (s\<lparr>kheap := kheap s(p \<mapsto> TCB tcb)\<rparr>) s"
  "integrity_asids aag subjects x a (s\<lparr>kheap := kheap s(p \<mapsto> Endpoint ep)\<rparr>) s"
  "integrity_asids aag subjects x a (s\<lparr>kheap := kheap s(p \<mapsto> Notification ntfn)\<rparr>) s"
  by (auto simp: opt_map_def ta_filter_def split: option.splits if_splits)

lemma integrity_asids_kh_update:
  "integrity_asids aag subject x a (s\<lparr>kheap := kh\<rparr>) (s\<lparr>kheap := kh'\<rparr>)
   \<Longrightarrow> integrity_asids aag subject x a (s\<lparr>kheap := kh(p := v)\<rparr>) (s\<lparr>kheap := kh'(p := v)\<rparr>)"
  by (clarsimp simp: opt_map_def obind_def)


subsection \<open>Misc definitions\<close>

fun ctxt_IP_update where
  "ctxt_IP_update (UserContext ctxt) = UserContext (ctxt(NextIP := ctxt FaultIP))"

lemma ctxt_IP_update_def:
  "ctxt_IP_update ctxt =
   (case ctxt of (UserContext ctxt') \<Rightarrow> UserContext (ctxt'(NextIP := ctxt' FaultIP)))"
  by (cases ctxt; clarsimp)

abbreviation arch_IP_update where
  "arch_IP_update arch \<equiv> arch_tcb_context_set (ctxt_IP_update (arch_tcb_context_get arch)) arch"

definition asid_pool_integrity ::
  "'a set \<Rightarrow> 'a PAS \<Rightarrow> (asid_low_index \<rightharpoonup> obj_ref) \<Rightarrow> (asid_low_index \<rightharpoonup> obj_ref) \<Rightarrow> bool" where
  "asid_pool_integrity subjects aag pool pool' \<equiv>
     \<forall>x. pool' x \<noteq> pool x
         \<longrightarrow> pool' x = None \<and> aag_subjects_have_auth_to subjects aag Control (the (pool x))"

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
  "auth_ipc_buffers s \<equiv> \<lambda>p. case (get_tcb False p s) of
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

end
