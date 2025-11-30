(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchFinalise_AC
imports Finalise_AC
begin

context Arch begin arch_global_naming

named_theorems Finalise_AC_assms

lemma state_vrefs_clear_asid_table:
  "state_vrefs (s\<lparr>arch_state := arch_state s\<lparr>arm_asid_table := \<lambda>a. if a = asid_high_bits_of base
                                                                     then None
                                                                     else asid_table s a\<rparr>\<rparr>) x
   \<subseteq> state_vrefs s x"
  by (fastforce simp: state_vrefs_def dest: vs_lookup_clear_asid_table[simplified fun_upd_def])

lemma state_vrefs_clear_asid_pool:
  assumes "asid_table s (asid_high_bits_of asid) = Some pool_ptr"
  and "ako_at (ASIDPool pool) pool_ptr s"
  shows "state_vrefs (s\<lparr>kheap := (kheap s)(pool_ptr \<mapsto> ArchObj
           (ASIDPool (\<lambda>a. if a = asid_low_bits_of asid then None else pool a)))\<rparr>) x
           \<subseteq> state_vrefs s x"
  apply (rule state_vrefs_subseteq)
  using assms
  by (auto simp: vspace_for_pool_def entry_for_pool_def opt_map_def obind_def obj_at_def)

lemma pas_refined_arm_next_vmid[simp]:
  "pas_refined aag (s\<lparr>arch_state := arch_state s\<lparr>arm_next_vmid := v\<rparr>\<rparr>) = pas_refined aag s"
  by (auto simp: pas_refined_def state_objs_to_policy_def state_vrefs_def)

lemma pas_refined_arm_vmid_table[simp]:
  "pas_refined aag (s\<lparr>arch_state := arch_state s\<lparr>arm_vmid_table := v\<rparr>\<rparr>) = pas_refined aag s"
  by (auto simp: pas_refined_def state_objs_to_policy_def state_vrefs_def)

crunch invalidate_vmid_entry
  for pas_refined[wp]: "pas_refined aag"

lemma set_vcpu_state_vrefs[wp]:
  "set_vcpu ptr vcpu \<lbrace>\<lambda>s. P (state_vrefs s)\<rbrace>"
  apply (wpsimp wp: set_vcpu_wp)
  apply (erule_tac P=P in rsubst)
  apply (fastforce intro: state_vrefs_eqI simp: opt_map_def typ_at_eq_kheap_obj)
  done

lemma state_vrefs_set_asid_pool_vmid:
  assumes "pool_for_asid asid s = Some pool_ptr"
      and "asid_pools_of s pool_ptr = Some pool"
      and "pool (asid_low_bits_of asid) = Some entry"
    shows "state_vrefs
            (s\<lparr>kheap := (kheap s)
                 (pool_ptr \<mapsto>
                  ArchObj
                   (ASIDPool
                     (\<lambda>a. if a = asid_low_bits_of asid
                           then Some (ASIDPoolVSpace vmid (ap_vspace entry)) else pool a)))\<rparr>)
            x
           \<subseteq> state_vrefs s x"
  (is "state_vrefs ?s' _ \<subseteq> state_vrefs _ _")
  apply (rule state_vrefs_subseteq)
  using assms
  by (auto simp: vspace_for_pool_def entry_for_pool_def opt_map_def obind_def obj_at_def
          split: option.splits)

lemma update_asid_pool_entry_vmid_pas_refined[wp]:
  "update_asid_pool_entry (\<lambda>entry. Some (ASIDPoolVSpace vmid (ap_vspace entry))) asid \<lbrace>pas_refined aag\<rbrace>"
  unfolding update_asid_pool_entry_def set_asid_pool_def
  apply (wpsimp wp: set_object_wp)+
  apply (erule pas_refined_subseteq; clarsimp?)
       apply (rule caps_of_state_fun_upd)
       apply (clarsimp simp: obj_at_def opt_map_def split: option.splits)
      apply (erule rev_subsetD, rule state_vrefs_subseteq)
         apply (auto simp: vspace_for_pool_def entry_for_pool_def opt_map_def obind_def
                    split: option.splits kernel_object.splits)[4]
     apply (clarsimp simp: state_hyp_refs_of_def split: option.splits if_splits)
    apply (auto simp: domains_of_state_aux.simps etcbs_of'_def opt_map_def
               split: if_splits option.splits)[1]
   apply (rule thread_st_auth_fun_upd)
   apply (clarsimp simp: obj_at_def asid_pools_of_ko_at get_tcb_def)
  apply (rule thread_bound_ntfns_fun_upd)
  apply (clarsimp simp: asid_pools_of_ko_at get_tcb_def obj_at_def)
  done

crunch set_vm_root, invalidate_asid_entry
  for pas_refined[wp]: "pas_refined aag"
  (wp: crunch_wps ignore: update_asid_pool_entry)

lemma delete_asid_pool_pas_refined[wp]:
  "delete_asid_pool base ptr \<lbrace>pas_refined aag\<rbrace>"
  apply (wpsimp simp: delete_asid_pool_def)
      apply (rule_tac Q'="\<lambda>_ s. pas_refined aag s \<and> asid_low_bits_of base = 0 \<and>
                                arm_asid_table (arch_state s) = asid_table \<and> asid_pool_at ptr s"
                   in hoare_strengthen_post[rotated], clarsimp)
       apply (erule pas_refined_subseteq; clarsimp?)
       apply (erule rev_subsetD, rule state_vrefs_subseteq)
          apply (auto simp: pool_for_asid_def)[4]
      apply (wpsimp wp: mapM_wp')+
  apply (clarsimp simp: asid_pools_at_eq)
  done

lemma delete_asid_pas_refined[wp]:
  "delete_asid asid pt \<lbrace>pas_refined aag\<rbrace>"
  apply (wpsimp wp: set_object_wp simp: delete_asid_def set_asid_pool_def simp_del: fun_upd_apply)
      apply (rule_tac Q'="\<lambda>_ s. pas_refined aag s \<and> pool_for_asid asid s = Some x2 \<and> asid_pool_at x2 s"
                   in hoare_strengthen_post[rotated])
       apply (clarsimp simp: asid_pools_at_eq)
       apply (erule pas_refined_subseteq; clarsimp?)
           apply (rule caps_of_state_fun_upd)
           apply (clarsimp simp: obj_at_def opt_map_def split: option.splits)
          apply (erule rev_subsetD, rule state_vrefs_subseteq)
             apply (auto simp: vspace_for_pool_def entry_for_pool_def opt_map_def obind_def
                        split: option.splits)[4]
         apply (clarsimp simp: state_hyp_refs_of_def split: if_splits)
    apply (auto simp: domains_of_state_aux.simps etcbs_of'_def opt_map_def split: if_splits option.splits)[1]

        apply (rule thread_st_auth_fun_upd)
        apply (clarsimp simp: obj_at_def get_tcb_def opt_map_def split: option.splits)
       apply (rule thread_bound_ntfns_fun_upd)
       apply (clarsimp simp: obj_at_def get_tcb_def opt_map_def split: option.splits)
      apply wpsimp+
  apply (clarsimp simp: asid_pools_at_eq)
  done

lemma vcpu_finalise_cap_pas_refined[wp]:
  "vcpu_finalise vr \<lbrace>pas_refined aag\<rbrace>"
  unfolding vcpu_finalise_def
  by (wpsimp wp: get_vcpu_wp)

lemma arch_finalise_cap_pas_refined[Finalise_AC_assms, wp]:
  "\<lbrace>pas_refined aag and invs and valid_arch_cap c\<rbrace> arch_finalise_cap c x \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  unfolding arch_finalise_cap_def
  apply (wpsimp wp: unmap_page_pas_refined unmap_page_table_pas_refined)
  apply (auto simp: valid_arch_cap_def wellformed_mapdata_def)
  done

lemma arch_thread_set_cur_fpu_pas_refined[wp]:
  "arch_thread_set (tcb_cur_fpu_update v) tptr \<lbrace>pas_refined aag\<rbrace>"
  unfolding pas_refined_def state_objs_to_policy_def by (wp | wps)+

lemma set_arm_current_fpu_owner_pas_refined[wp]:
  "set_arm_current_fpu_owner new_owner \<lbrace>pas_refined aag\<rbrace>"
  by (wpsimp wp: hoare_drop_imps simp: set_arm_current_fpu_owner_def)

crunch prepare_thread_delete
  for pas_refined[Finalise_AC_assms, wp]: "pas_refined aag"
  (wp: crunch_wps)


locale_abbrev machine_fpu :: "'a :: state_ext state \<Rightarrow> fpu_state" where
  "machine_fpu \<equiv> \<lambda>s. fpu_state (machine_state s)"

locale_abbrev tcb_cur_fpu_of :: "'a :: state_ext state \<Rightarrow> obj_ref \<rightharpoonup> bool" where
  "tcb_cur_fpu_of \<equiv> \<lambda>s t. option_map (tcb_cur_fpu o tcb_arch) (get_tcb t s)"

locale_abbrev tcb_fpu_of :: "'a :: state_ext state \<Rightarrow> obj_ref \<rightharpoonup> fpu_state" where
  "tcb_fpu_of \<equiv> \<lambda>s t. option_map (user_fpu_state o tcb_context o tcb_arch) (get_tcb t s)"

locale_abbrev tcb_vcpu_of :: "'a :: state_ext state \<Rightarrow> obj_ref \<rightharpoonup> obj_ref" where
  "tcb_vcpu_of \<equiv> \<lambda>s. (\<lambda>t. get_tcb t s) |> tcb_vcpu o tcb_arch"

lemma get_tcb_machine_state_update[simp]:
  "get_tcb t (machine_state_update f s) = get_tcb t s"
  by (simp add: get_tcb_def)

crunch load_fpu_state
  for get_tcb[wp]: "\<lambda>s. P (get_tcb t s)"
  and arch_state[wp]: "\<lambda>s. P (arch_state s)"
  (wp: as_user_inv simp: getFPUState_def crunch_simps)

crunch save_fpu_state
  for machine_state[wp]: "\<lambda>s. P (machine_state s)"
  (wp: dmo_wp simp: readFpuState_def)

crunch enableFpu, disableFpu
  for fpu_state[wp]: "\<lambda>ms. P (fpu_state ms)"

definition fpu_of :: "bool option \<Rightarrow> fpu_state option \<Rightarrow> fpu_state \<rightharpoonup> fpu_state" where
  "fpu_of bopt fpu hw_fpu \<equiv> case bopt of
     None \<Rightarrow> None
   | Some True \<Rightarrow> Some hw_fpu
   | Some False \<Rightarrow> fpu"

lemma save_fpu_state_machine_fpu[wp]:
  "\<lbrace>\<lambda>s. P (if tptr = t then Some (machine_fpu s) else tcb_fpu_of s t)\<rbrace>
   save_fpu_state tptr
   \<lbrace>\<lambda>_ s. P (tcb_fpu_of s t)\<rbrace>"
  unfolding save_fpu_state_def as_user_def readFpuState_def setFPUState_def
  apply (wpsimp wp: set_object_wp dmo_wp)
  apply (auto simp: option_map_def arch_tcb_context_set_def
                    get_tcb_def modify_def put_def bind_def)
  done

lemma save_fpu_state_cur_fpu_of[wp]:
  "save_fpu_state tptr \<lbrace>\<lambda>s. P (tcb_cur_fpu_of s t)\<rbrace>"
  unfolding save_fpu_state_def readFpuState_def setFPUState_def
  apply (wpsimp wp: dmo_wp as_user_wp_thread_set_helper thread_set_wp)
  apply (clarsimp simp: get_tcb_def arch_tcb_context_set_def)
  done

lemma load_fpu_state_machine_fpu[wp]:
 " \<lbrace>\<lambda>s. tcb_at t s \<longrightarrow> P (the (tcb_fpu_of s t))\<rbrace>
   load_fpu_state t
   \<lbrace>\<lambda>_ s. P (machine_fpu s)\<rbrace>"
  unfolding load_fpu_state_def as_user_def writeFpuState_def getFPUState_def
  apply (wpsimp wp: dmo_wp)
  apply (clarsimp simp: gets_def get_def return_def bind_def
                        tcb_at_def arch_tcb_context_get_def)
  done

lemma set_arm_current_fpu_owner_fpu_of[wp]:
  "\<lbrace>\<lambda>s. fopt = fpu_of (if tptr = Some t then Some True
                       else if arm_current_fpu_owner (arch_state s) = Some t then Some False
                       else tcb_cur_fpu_of s t) (tcb_fpu_of s t) (machine_fpu s)\<rbrace>
   set_arm_current_fpu_owner tptr
   \<lbrace>\<lambda>_ s. fopt = fpu_of (tcb_cur_fpu_of s t) (tcb_fpu_of s t) (machine_fpu s)\<rbrace>"
  unfolding set_arm_current_fpu_owner_def
  by (wpsimp wp: arch_thread_set_wp simp: fpu_of_def get_tcb_def)

lemma switch_local_fpu_owner_fpu_of[wp]:
  "\<lbrace>\<lambda>s. fopt = fpu_of (tcb_cur_fpu_of s t) (tcb_fpu_of s t) (machine_fpu s) \<and> valid_cur_fpu s\<rbrace>
   switch_local_fpu_owner tptr
   \<lbrace>\<lambda>_ s. fopt = fpu_of (tcb_cur_fpu_of s t) (tcb_fpu_of s t) (machine_fpu s)\<rbrace>"
  apply (simp add: switch_local_fpu_owner_def)
  apply (wps | wpc | wp dmo_wp | simp add: tcb_at_typ split del: if_split)+
  apply (auto simp: fpu_of_def get_tcb_def valid_cur_fpu_def obj_at_def
                    valid_cur_fpu_is_tcb_cur_fpu_unique is_tcb_cur_fpu_def
             split: option.split_asm kernel_object.splits bool.splits)
  done

lemma fpu_of_state_fpu_of:
  "fpu_of_state (machine_fpu s) (kheap s) t =
   fpu_of (tcb_cur_fpu_of s t) (tcb_fpu_of s t) (machine_fpu s)"
  by (auto simp: fpu_of_state_def fpu_of_def opt_map_def get_tcb_def
          split: option.splits kernel_object.splits)

lemma switch_local_fpu_owner_integrity_fpu[wp]:
  "\<lbrace>integrity_fpu aag subjects x st and valid_cur_fpu\<rbrace>
   switch_local_fpu_owner t
   \<lbrace>\<lambda>_. integrity_fpu aag subjects x st\<rbrace>"
  unfolding integrity_fpu_def integrity_fpu_def fpu_of_state_fpu_of
  by (wpsimp wp: hoare_weak_lift_imp)

lemma arch_thread_set_arch_tcb_states_of_state[wp]:
  "arch_thread_set f t \<lbrace>\<lambda>s. P (tcb_states_of_state s)\<rbrace>"
  apply (wpsimp wp: arch_thread_set_wp)
  apply (auto elim!: rsubst[where P=P] simp: tcb_states_of_state_def get_tcb_def)
  done

lemma arch_thread_set_asid_pools_of[wp]:
  "arch_thread_set t f \<lbrace>\<lambda>s. P (asid_pools_of s)\<rbrace>"
  apply (wpsimp wp: arch_thread_set_wp)
  apply (fastforce elim!: rsubst[where P=P] simp: get_tcb_def opt_map_def split: option.splits)
  done

lemma as_user_vcpus_of[wp]:
  "as_user t f \<lbrace>\<lambda>s. P (vcpus_of s)\<rbrace>"
  by (wpsimp wp: as_user_wp_thread_set_helper)

crunch readFpuState, writeFpuState, disableFpu, enableFpu
  for vcpu_state[wp]: "\<lambda>ms. P (vcpu_state ms)"

crunch switch_local_fpu_owner
  for cdt[wp]: "\<lambda>s. P (cdt s)"
  and no_revokable[wp]: "\<lambda>s. P (is_original_cap s)"
  and interrupt_states[wp]: "\<lambda>s. P (interrupt_states s)"
  and underlying_memory[wp]: "\<lambda>s. P (underlying_memory (machine_state s))"
  and vcpus_of[wp]: "\<lambda>s. P (vcpus_of s)"
  and asid_pools_of[wp]: "\<lambda>s. P (asid_pools_of s)"
  and tcb_states_of_state[wp]: "\<lambda>s. P (tcb_states_of_state s)"
  and numlistregs[wp]: "\<lambda>s. P (arm_gicvcpu_numlistregs (arch_state s))"
  and arm_current_vcpu[wp]: "\<lambda>s. P (arm_current_vcpu (arch_state s))"
  and asid_table[wp]: "\<lambda>s. P (asid_table s)"
  and device_state[wp]: "\<lambda>s. P (device_state (machine_state s))"
  and vcpu_state[wp]: "\<lambda>s. P (vcpu_state (machine_state s))"
  (wp: dmo_machine_state_lift)

lemma set_arm_current_fpu_owner_integrity_obj:
  "set_arm_current_fpu_owner new
   \<lbrace>\<lambda>s. integrity_obj aag activate subjects (pasObjectAbs aag x) (kheap st x) (kheap s x)\<rbrace>"
  unfolding set_arm_current_fpu_owner_def
  apply (wpsimp wp: arch_thread_set_wp)
  apply (auto elim!: tro_trans_spec intro!: tro_tcb_fpu
               simp: get_tcb_def arch_tcb_get_registers_def
              split: option.splits kernel_object.splits)
  done

lemma switch_local_fpu_owner_integrity_obj[wp]:
  "switch_local_fpu_owner new
   \<lbrace>\<lambda>s. integrity_obj aag activate subjects (pasObjectAbs aag x) (kheap st x) (kheap s x)\<rbrace>"
  unfolding switch_local_fpu_owner_def load_fpu_state_def save_fpu_state_def
            getFPUState_def setFPUState_def readFpuState_def enableFpu_def
  apply (wpsimp wp: set_arm_current_fpu_owner_integrity_obj dmo_wp thread_set_wp
                    as_user_inv[OF gets_inv] as_user_wp_thread_set_helper hoare_vcg_all_lift)
  apply (auto elim!: tro_trans_spec intro!: tro_tcb_fpu
               simp: arch_tcb_get_registers_def arch_tcb_context_set_def arch_tcb_context_get_def
                     get_tcb_def modify_def get_def put_def bind_def
              split: option.splits kernel_object.splits)
  done

lemma switch_local_fpu_owner_integrity[wp]:
  "\<lbrace>integrity aag X st and valid_cur_fpu\<rbrace>
   switch_local_fpu_owner new
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  unfolding integrity_def integrity_hyp_def integrity_asids_def
  by (wpsimp wp: hoare_vcg_all_lift | wps)+


crunch load_fpu_state
  for tcb_vcpus_of[wp]: "\<lambda>s. P (tcb_vcpu_of s)"
  (wp: as_user_inv simp: getFPUState_def crunch_simps)

lemma as_user_setFPUState_tcb_vcpu_of[wp]:
  "save_fpu_state t \<lbrace>\<lambda>s. P (tcb_vcpu_of s)\<rbrace>"
  unfolding save_fpu_state_def readFpuState_def
  apply (wpsimp wp: as_user_wp_thread_set_helper thread_set_wp dmo_wp)
  apply (auto elim!: back_subst[where P=P] simp: get_tcb_def opt_map_def arch_tcb_context_set_def)
  done

lemma set_arm_current_fpu_owner_tcb_vcpu_of[wp]:
  "set_arm_current_fpu_owner t \<lbrace>\<lambda>s. P (tcb_vcpu_of s)\<rbrace>"
  unfolding set_arm_current_fpu_owner_def
  apply (wpsimp wp: arch_thread_set_wp)
  apply (auto elim!: back_subst[where P=P] simp: get_tcb_def opt_map_def)
  done

lemma switch_local_fpu_owner_tcb_vcpu_of[wp]:
  "switch_local_fpu_owner t \<lbrace>\<lambda>s. P (tcb_vcpu_of s)\<rbrace>"
  unfolding switch_local_fpu_owner_def
  apply (wpsimp wp: dmo_wp)
  apply (auto elim!: back_subst[where P=P] simp: opt_map_def)
  done

crunch fpu_release, lazy_fpu_restore
  for respects[wp]: "integrity aag X st"
  and tcb_vcpus_of[wp]: "\<lambda>s. P (tcb_vcpu_of s)"
  (simp: crunch_simps wp: dmo_no_mem_respects wp: hoare_drop_imps)

lemma prepare_thread_delete_integrity[Finalise_AC_assms, wp]:
  "\<lbrace>integrity aag X st and pas_refined aag and valid_cur_fpu and K (is_subject aag t)\<rbrace>
   prepare_thread_delete t
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  unfolding prepare_thread_delete_def
  by (wpsimp wp: dissociate_vcpu_tcb_respects arch_thread_get_wp
           simp: associated_vcpu_is_subject get_tcb_ko_at)

lemma sbn_st_vrefs[Finalise_AC_assms]:
  "set_bound_notification t st \<lbrace>\<lambda>s. P (state_vrefs s)\<rbrace>"
  apply (simp add: set_bound_notification_def)
  apply (wpsimp wp: set_object_wp dxo_wp_weak)
  apply (subst state_vrefs_tcb_upd)
   apply (auto simp: tcb_at_def valid_arch_state_def)
  done

lemma arch_finalise_cap_auth'[Finalise_AC_assms]:
  "\<lbrace>pas_refined aag\<rbrace> arch_finalise_cap x12 final \<lbrace>\<lambda>rv s. pas_cap_cur_auth aag (fst rv)\<rbrace>"
  unfolding arch_finalise_cap_def
  by (wp | wpc | simp add: comp_def hoare_TrueI[where P = \<top>] split del: if_split)+

lemma arch_finalise_cap_obj_refs[Finalise_AC_assms]:
  "\<lbrace>\<lambda>s. \<forall>x \<in> aobj_ref' acap. P x\<rbrace>
   arch_finalise_cap acap slot
   \<lbrace>\<lambda>rv s. \<forall>x \<in> obj_refs_ac (fst rv). P x\<rbrace>"
  by (wpsimp simp: arch_finalise_cap_def)

lemma arch_finalise_cap_makes_halted[Finalise_AC_assms]:
  "\<lbrace>\<top>\<rbrace> arch_finalise_cap arch_cap ex \<lbrace>\<lambda>rv s. \<forall>t\<in>obj_refs_ac (fst rv). halted_if_tcb t s\<rbrace>"
  apply (case_tac arch_cap, simp_all add: arch_finalise_cap_def)
  by (wpsimp simp: valid_cap_def split: option.split bool.split)+

lemma arch_cap_cleanup_wf[Finalise_AC_assms]:
  "\<lbrakk> arch_cap_cleanup_opt acap \<noteq> NullCap; \<not> is_arch_cap (arch_cap_cleanup_opt acap) \<rbrakk>
     \<Longrightarrow> (\<exists>irq. arch_cap_cleanup_opt acap = IRQHandlerCap irq \<and> is_subject_irq aag irq)"
  by simp

lemma update_asid_pool_entry_vmid_integrity:
  "\<lbrace>\<lambda>s. integrity aag X st s \<and> (vmid = None \<or> vmid_for_asid s asid = None)\<rbrace>
   update_asid_pool_entry (\<lambda>entry. Some (ASIDPoolVSpace vmid (ap_vspace entry))) asid
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  unfolding update_asid_pool_entry_def set_asid_pool_def
  apply (wpsimp wp: set_object_wp simp_del: fun_upd_apply)
  apply (clarsimp simp: integrity_def integrity_asids_def)
  apply (subst tcb_states_of_state_fun_upd, fastforce simp: get_tcb_def asid_pools_of_ko_at obj_at_def)+
  apply (intro conjI; simp?)
     apply (fastforce elim: tro_trans_spec
                     intro: tro_arch[OF refl refl] arch_integrity_obj_atomic.intros[OF refl refl]
                      simp: asid_pool_integrity_def entry_for_pool_def pool_for_asid_def opt_map_def
                     split: option.splits)
    apply (erule_tac x=asid in allE, fastforce simp: pool_for_asid_def)
   apply (erule allEI, erule trhyp_trans)
   apply (clarsimp simp: integrity_hyp_ao_upd in_opt_map_eq)
  apply (erule allEI, erule trfpu_trans)
  apply (clarsimp simp: integrity_arch_kh_upds in_opt_map_eq)
  done

lemma store_vmid_Some_integrity:
  "\<lbrace>\<lambda>s. integrity aag X st s \<and> vmid_for_asid s asid = None\<rbrace>
   store_vmid asid vmid
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  unfolding store_vmid_def
  by (wpsimp wp: update_asid_pool_entry_vmid_integrity)

crunch find_free_vmid
  for respects[wp]: "integrity aag X st"
  (wp: update_asid_pool_entry_vmid_integrity dmo_no_mem_respects ignore: update_asid_pool_entry)

lemma get_vmid_respects[wp]:
  "get_vmid asid \<lbrace>integrity aag X st\<rbrace>"
  unfolding get_vmid_def
  by (wpsimp wp: store_vmid_Some_integrity)

crunch arm_context_switch, set_global_user_vspace, set_vm_root,
       invalidate_vmid_entry, invalidate_asid_entry, invalidate_tlb_by_asid
  for respects[wp]: "integrity aag X st"
  (wp: dmo_no_mem_respects simp: setVSpaceRoot_def ignore: update_asid_pool_entry)

lemma delete_asid_pool_respects[wp]:
  "\<lbrace>integrity aag X st and
    K (\<forall>asid'. asid' \<noteq> 0 \<and> asid_high_bits_of asid' = asid_high_bits_of x
               \<longrightarrow> is_subject_asid aag asid')\<rbrace>
   delete_asid_pool x y
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  by (wpsimp simp: delete_asid_pool_def wp: asid_table_entry_update_integrity mapM_wp')

crunch set_asid_pool
  for is_original_cap[wp]: "\<lambda>s. P (is_original_cap s x)"

lemma set_asid_pool_tcb_states_of_state[wp]:
  "set_asid_pool p pool \<lbrace>\<lambda>s. P (tcb_states_of_state s)\<rbrace>"
  apply (wpsimp wp: set_object_wp_strong simp: obj_at_def set_asid_pool_def)
  apply (erule_tac P=P in rsubst)
  apply (fastforce simp: tcb_states_of_state_def get_tcb_def split: kernel_object.splits)
  done

lemma set_asid_pool_integrity_objs:
  "\<lbrace>integrity_obj_state aag activate subjects st and
    (\<lambda>s. \<forall>pool'. ako_at (ASIDPool pool') ptr s \<longrightarrow> asid_pool_integrity subjects aag pool' pool)\<rbrace>
   set_asid_pool ptr pool
   \<lbrace>\<lambda>_. integrity_obj_state aag activate subjects st\<rbrace>"
  apply (wpsimp wp: set_object_wp_strong simp: obj_at_def set_asid_pool_def)
  by (fastforce elim: tro_trans_spec
               intro: tro_arch arch_troa_asidpool_clear
                simp: a_type_def aa_type_def
               split: if_splits kernel_object.splits arch_kernel_obj.splits)

lemma set_asid_pool_integrity_autarch:
  "\<lbrace>\<lambda>s. integrity aag X st s \<and> pas_refined aag s \<and> invs s \<and>
        (\<exists>asid pool. pool_for_asid asid s = Some pool_ptr \<and> asid_pools_of s pool_ptr = Some pool \<and>
                     pool' = pool (asid_low_bits_of asid := None) \<and>
                     (\<forall>entry. pool (asid_low_bits_of asid) = Some entry
                              \<longrightarrow> is_subject aag (ap_vspace entry)))\<rbrace>
   set_asid_pool pool_ptr pool'
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  unfolding integrity_def integrity_asids_def conj_assoc[symmetric]
  apply (wp set_object_wp_strong set_asid_pool_integrity_objs dmo_wp hoare_vcg_all_lift
         | wps | simp add: obj_at_def set_asid_pool_def)+
  apply (intro conjI impI; clarsimp)
     apply (fastforce simp: opt_map_def asid_pool_integrity_def aag_has_Control_iff_owns)
    apply (erule_tac x=asid in allE)
    apply (fastforce simp: pool_for_asid_def)
   apply (erule allE, erule trhyp_trans)
   apply (clarsimp simp: integrity_hyp_ao_upd in_opt_map_eq)
  apply (erule allE, erule trfpu_trans)
  apply (clarsimp simp: integrity_arch_kh_upds in_opt_map_eq)
  done

lemma delete_asid_respects:
  "\<lbrace>integrity aag X st and pas_refined aag and invs and K (0 < asid \<and> is_subject aag pd)\<rbrace>
   delete_asid asid pd
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: delete_asid_def)
  apply (wpsimp wp: set_asid_pool_integrity_autarch)
      apply (rule_tac Q'="\<lambda>_ s. integrity aag X st s \<and> pas_refined aag s \<and> invs s \<and>
                                is_subject aag pd \<and> pool_for_asid asid s = Some x2 \<and>
                                vspace_for_asid asid s = Some pd" in hoare_strengthen_post[rotated])
       apply (fastforce simp: vspace_for_asid_def obind_def entry_for_asid_def entry_for_pool_def
                       split: if_splits)
      apply (wpsimp wp: set_asid_pool_integrity_autarch invalidate_tlb_by_asid_invs)+
  apply (clarsimp simp: vspace_for_asid_def entry_for_asid_def entry_for_pool_def in_obind_eq)
  done

lemma vcpu_finalise_integrity_autarch:
  "\<lbrace>integrity aag X st and pas_refined aag and K (is_subject aag vr)\<rbrace>
   vcpu_finalise vr
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  unfolding vcpu_finalise_def
  apply (wpsimp wp: dissociate_vcpu_tcb_respects get_vcpu_wp)
  apply (erule (3) associated_tcb_is_subject)
  done

lemma arch_finalise_cap_respects[Finalise_AC_assms, wp]:
  "\<lbrace>integrity aag X st and invs and pas_refined aag and valid_cap (ArchObjectCap cap)
                       and K (pas_cap_cur_auth aag (ArchObjectCap cap))\<rbrace>
   arch_finalise_cap cap final
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: arch_finalise_cap_def)
  apply (wpsimp wp: unmap_page_respects unmap_page_table_respects
                    delete_asid_respects delete_asid_pool_respects vcpu_finalise_integrity_autarch)
  apply (auto simp: cap_auth_conferred_def arch_cap_auth_conferred_def wellformed_mapdata_def
                    aag_cap_auth_def pas_refined_all_auth_is_owns valid_cap_simps
                    cap_links_asid_slot_def label_owns_asid_slot_def
             intro: pas_refined_Control_into_is_subject_asid)
  done

declare prepare_thread_delete_st_tcb_at_halted[Finalise_AC_assms]
declare suspend_valid_cur_fpu[Finalise_AC_assms]
declare unbind_notification_valid_cur_fpu[Finalise_AC_assms]
declare finalise_cap_valid_list[Finalise_AC_assms]
declare finalise_cap_replaceable[Finalise_AC_assms]

end


global_interpretation Finalise_AC_1?: Finalise_AC_1
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact Finalise_AC_assms)?)
qed


context Arch begin arch_global_naming

lemma cap_revoke_respects'[Finalise_AC_assms]:
  "s \<turnstile> \<lbrace>(\<lambda>s. trp \<longrightarrow> integrity aag X st s) and K (is_subject aag (fst slot))
                                           and pas_refined aag and einvs and simple_sched_action\<rbrace>
       cap_revoke slot
       \<lbrace>\<lambda>_. (\<lambda>s. trp \<longrightarrow> integrity aag X st s) and pas_refined aag\<rbrace>,
       \<lbrace>\<lambda>_. (\<lambda>s. trp \<longrightarrow> integrity aag X st s) and pas_refined aag\<rbrace>"
proof (induct rule: cap_revoke.induct[where ?a1.0=s])
  case (1 slot s)
  show ?case
    apply (subst cap_revoke.simps)
    apply (rule hoare_pre_spec_validE)
     apply (wp "1.hyps")
            apply ((wp preemption_point_inv' | simp add: integrity_subjects_def pas_refined_def)+)[1]
           apply (wp select_ext_weak_wp cap_delete_respects cap_delete_pas_refined
                  | simp split del: if_split | wp (once) hoare_vcg_const_imp_lift hoare_drop_imps)+
    by (auto simp: emptyable_def descendants_of_def
             dest: reply_slot_not_descendant
            intro: cca_owned)
qed

lemma finalise_cap_caps_of_state_nullinv[Finalise_AC_assms]:
  "\<lbrace>\<lambda>s. P (caps_of_state s) \<and> (\<forall>p. P ((caps_of_state s)(p \<mapsto> NullCap)))\<rbrace>
   finalise_cap cap final
   \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  by (cases cap;
      wpsimp wp: suspend_caps_of_state unbind_notification_caps_of_state
                 unbind_notification_cte_wp_at
                 hoare_vcg_all_lift hoare_drop_imps
                 deleting_irq_handler_caps_of_state_nullinv
           simp: fun_upd_def[symmetric] if_apply_def2 split_del: if_split)

lemma finalise_cap_fst_ret[Finalise_AC_assms]:
  "\<lbrace>\<lambda>_. P NullCap \<and> (\<forall>a b c. P (Zombie a b c))\<rbrace>
   finalise_cap cap is_final
   \<lbrace>\<lambda>rv _. P (fst rv)\<rbrace>"
  including classic_wp_pre
  apply (cases cap, simp_all add: arch_finalise_cap_def split del: if_split)
  apply (wp | simp add: comp_def split del: if_split | fastforce)+
  apply (rule hoare_pre)
  apply (wp | simp | (rule hoare_pre, wpc))+
  done

end


global_interpretation Finalise_AC_2?: Finalise_AC_2
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact Finalise_AC_assms)?)
qed

end