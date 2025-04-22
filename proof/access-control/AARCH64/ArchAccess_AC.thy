(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchAccess_AC
imports Access_AC
begin

section\<open>Arch-specific AC proofs\<close>

context Arch begin arch_global_naming

named_theorems Access_AC_assms

lemma acap_class_reply[Access_AC_assms]:
  "acap_class acap \<noteq> ReplyClass t"
  by (cases acap; simp)

lemma arch_troa_tro_alt[Access_AC_assms, elim!]:
  "arch_integrity_obj_atomic aag subjects l ko ko'
   \<Longrightarrow> arch_integrity_obj_alt aag subjects l ko ko'"
  by (fastforce elim: arch_integrity_obj_atomic.cases intro: arch_integrity_obj_alt.intros)

lemma clear_asidpool_trans[elim]:
  "\<lbrakk> asid_pool_integrity subjects aag pool pool';
     asid_pool_integrity subjects aag pool' pool'' \<rbrakk>
     \<Longrightarrow> asid_pool_integrity subjects aag pool pool''"
  apply (clarsimp simp: asid_pool_integrity_def)
  apply (erule_tac x=x in allE)+
  apply (fastforce split: option.split_asm)
  done

lemma cap_asid'_member[simp]:
  "asid \<in> cap_asid' cap = (\<exists>acap. cap = ArchObjectCap acap \<and> asid \<in> acap_asid' acap)"
  by (cases cap; clarsimp)

lemma clas_caps_of_state[Access_AC_assms]:
  "\<lbrakk> caps_of_state s slot = Some cap; pas_refined aag s \<rbrakk>
     \<Longrightarrow> cap_links_asid_slot aag (pasObjectAbs aag (fst slot)) cap"
  apply (clarsimp simp: cap_links_asid_slot_def label_owns_asid_slot_def pas_refined_def)
  apply (drule state_asids_to_policy_aux.intros)
   apply assumption
  apply (blast dest: state_asids_to_policy_aux.intros)
  done

lemma arch_tro_alt_trans_spec[Access_AC_assms]:
  "\<lbrakk> arch_integrity_obj_alt aag subjects l ko ko';
     arch_integrity_obj_alt aag subjects l ko' ko'' \<rbrakk>
     \<Longrightarrow> arch_integrity_obj_alt aag subjects l ko ko''"
  by (fastforce simp: arch_integrity_obj_alt.simps)

lemma tcb_hyp_refs_arch_tcb_set_registers[Access_AC_assms]:
  "tcb_hyp_refs (arch_tcb_set_registers regs atcb) = tcb_hyp_refs atcb"
  by (simp add: arch_tcb_set_registers_def)

end


global_interpretation Access_AC_1?: Access_AC_1
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact Access_AC_assms)?)
qed


context Arch begin arch_global_naming

lemma auth_ipc_buffers_tro[Access_AC_assms]:
  "\<lbrakk> integrity_obj_state aag activate subjects s s';
     x \<in> auth_ipc_buffers s' p; pasObjectAbs aag p \<notin> subjects \<rbrakk>
     \<Longrightarrow> x \<in> auth_ipc_buffers s p "
  by (drule_tac x = p in spec)
     (erule integrity_objE;
      fastforce simp: tcb_states_of_state_def get_tcb_def auth_ipc_buffers_def
               split: cap.split_asm arch_cap.split_asm if_split_asm bool.splits)

lemma trasids_trans[Access_AC_assms]:
  "\<lbrakk> \<forall>x a. integrity_asids_2 aag subjects x a as as' ao ao';
     \<forall>x a. integrity_asids_2 aag subjects x a as' as'' ao' ao'' \<rbrakk>
     \<Longrightarrow> \<forall>x a. integrity_asids_2 aag subjects x a as as'' ao ao''"
  by (clarsimp simp: integrity_asids_def) metis

lemma integrity_asids_refl[Access_AC_assms, simp]:
  "integrity_asids aag subjects x a s s"
  by (simp add: integrity_asids_def)

lemma integrity_asids_update_autarch[Access_AC_assms]:
  "\<lbrakk> integrity_asids_2 aag subjects x a as as' ao ao'; pasObjectAbs aag ptr \<in> subjects \<rbrakk>
     \<Longrightarrow> integrity_asids_2 aag subjects x a as as' ao (ao'(ptr := ako))"
  by (auto simp: integrity_asids_def opt_map_def)

lemma integrity_hyp_refl[Access_AC_assms,simp]:
  "integrity_hyp_2 aag subjects x ms ms as as ao ao"
  by (simp add: integrity_hyp_def vcpu_integrity_def)

lemma trhyp_trans[Access_AC_assms]:
  "\<lbrakk> integrity_hyp_2 aag subjects x ms ms' as as' ao ao';
     integrity_hyp_2 aag subjects x ms' ms'' as' as'' ao' ao'' \<rbrakk>
     \<Longrightarrow> integrity_hyp_2 aag subjects x ms ms'' as as'' ao ao'' "
  by (auto simp: integrity_hyp_def vcpu_integrity_def)

lemma integrity_hyp_update_autarch[Access_AC_assms]:
  "\<lbrakk> integrity_hyp_2 aag subjects x ms ms' as as' ao ao'; pasObjectAbs aag ptr \<in> subjects \<rbrakk>
     \<Longrightarrow> integrity_hyp_2 aag subjects x  ms ms' as as' ao (ao'(ptr := ako))"
  by (fastforce simp: integrity_hyp_def vcpu_integrity_def vcpu_of_state_def opt_map_def
               split: option.splits elim!: trhyp_trans)

lemma integrity_fpu_refl[Access_AC_assms,simp]:
  "integrity_fpu_2 aag subjects x ms ms kh kh"
  by (simp add: integrity_fpu_def)

lemma trfpu_trans[Access_AC_assms]:
  "\<lbrakk> integrity_fpu_2 aag subjects x ms ms' kh kh';
     integrity_fpu_2 aag subjects x ms' ms'' kh' kh'' \<rbrakk>
     \<Longrightarrow> integrity_fpu_2 aag subjects x ms ms'' kh kh''"
  by (simp add: integrity_fpu_def)

lemma integrity_fpu_update_autarch[Access_AC_assms]:
  "\<lbrakk> integrity_fpu_2 aag subjects x ms ms' kh kh'; pasObjectAbs aag ptr \<in> subjects \<rbrakk>
     \<Longrightarrow> integrity_fpu_2 aag subjects x ms ms' kh (kh'(ptr \<mapsto> obj))"
  unfolding integrity_fpu_def integrity_fpu_def fpu_of_state_def
  by (auto split: option.splits kernel_object.splits)

end


global_interpretation Access_AC_2?: Access_AC_2
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact Access_AC_assms)?)
qed


context Arch begin arch_global_naming

lemma ipcframe_subset_page:
  "\<lbrakk> valid_objs s; get_tcb p s = Some tcb;
     tcb_ipcframe tcb = ArchObjectCap (FrameCap p' R vms d xx);
     x \<in> ptr_range (p' + (tcb_ipc_buffer tcb && mask (pageBitsForSize vms))) msg_align_bits \<rbrakk>
     \<Longrightarrow> x \<in> ptr_range p' (pageBitsForSize vms)"
   apply (frule (1) valid_tcb_objs)
   apply (clarsimp simp add: valid_tcb_def ran_tcb_cap_cases)
   apply (erule set_mp[rotated])
   apply (rule ptr_range_subset)
     apply (simp add: valid_cap_def cap_aligned_def)
    apply (simp add: valid_tcb_def valid_ipc_buffer_cap_def is_aligned_andI1 split:bool.splits)
   apply (rule order_trans [OF _ pbfs_atleast_pageBits])
   apply (simp add: msg_align_bits pageBits_def)
  apply (rule and_mask_less')
  apply (simp add: pbfs_less_wb' [unfolded word_bits_conv])
  done

lemma auth_ipc_buffers_member_def:
  "x \<in> auth_ipc_buffers s p =
   (\<exists>tcb p' R vms xx. get_tcb p s = Some tcb
                   \<and> tcb_ipcframe tcb = (ArchObjectCap (FrameCap p' R vms False xx))
                   \<and> caps_of_state s (p, tcb_cnode_index 4) =
                      Some (ArchObjectCap (FrameCap p' R vms False xx))
                   \<and> AllowWrite \<in> R
                   \<and> x \<in> ptr_range (p' + (tcb_ipc_buffer tcb && mask (pageBitsForSize vms)))
                                    msg_align_bits)"
  unfolding auth_ipc_buffers_def
  by (clarsimp simp: caps_of_state_tcb' split: option.splits cap.splits arch_cap.splits bool.splits)

lemma auth_ipc_buffers_member[Access_AC_assms]:
  "\<lbrakk> x \<in> auth_ipc_buffers s p; valid_objs s \<rbrakk>
     \<Longrightarrow> \<exists>tcb acap. get_tcb p s = Some tcb
                  \<and> tcb_ipcframe tcb = (ArchObjectCap acap)
                  \<and> caps_of_state s (p, tcb_cnode_index 4) = Some (ArchObjectCap acap)
                  \<and> Write \<in> arch_cap_auth_conferred acap
                  \<and> x \<in> aobj_ref' acap"
  by (fastforce simp: auth_ipc_buffers_def caps_of_state_tcb' arch_cap_auth_conferred_def
                      vspace_cap_rights_to_auth_def ipcframe_subset_page
               split: option.splits cap.splits arch_cap.splits bool.splits if_splits)

lemma asid_pool_integrity_mono[Access_AC_assms]:
  "\<lbrakk> asid_pool_integrity S aag cont cont'; S \<subseteq> T \<rbrakk> \<Longrightarrow> asid_pool_integrity T aag cont cont'"
  unfolding asid_pool_integrity_def by fastforce

lemma integrity_asids_mono[Access_AC_assms]:
    "\<lbrakk> integrity_asids aag S x a s s'; S \<subseteq> T; pas_refined aag s; valid_objs s \<rbrakk>
       \<Longrightarrow> integrity_asids aag T x a s s'"
  by (fastforce simp: integrity_asids_def)

lemma integrity_hyp_mono[Access_AC_assms]:
    "\<lbrakk> integrity_hyp aag S x s s'; S \<subseteq> T \<rbrakk>
       \<Longrightarrow> integrity_hyp aag T x s s'"
  by (fastforce simp: integrity_hyp_def vcpu_integrity_def)

lemma integrity_fpu_mono[Access_AC_assms]:
    "\<lbrakk> integrity_fpu aag S x s s'; S \<subseteq> T \<rbrakk>
       \<Longrightarrow> integrity_fpu aag T x s s'"
  by (fastforce simp: integrity_fpu_def)

lemma arch_integrity_obj_atomic_mono[Access_AC_assms]:
  "\<lbrakk> arch_integrity_obj_atomic aag S l ao ao'; S \<subseteq> T; pas_refined aag s; valid_objs s \<rbrakk>
     \<Longrightarrow> arch_integrity_obj_atomic aag T l ao ao'"
  by (clarsimp simp: arch_integrity_obj_atomic.simps asid_pool_integrity_mono)

end


global_interpretation Access_AC_3?: Access_AC_3
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact Access_AC_assms)?)
qed


locale Arch_hyp_machine_update_eq = Arch +
  fixes f :: "('a \<Rightarrow> 'a) \<Rightarrow> machine_state \<Rightarrow> machine_state"
  assumes vcpu: "vcpu_state (f g ms) = vcpu_state ms"
begin arch_global_naming

lemma integrity_hyp_machine_upd:
  "integrity_hyp_2 aag subjects x (f (g ms) (h ms)) ms' as as' ao ao' =
   integrity_hyp_2 aag subjects x (h ms) ms' as as' ao ao'"
  "integrity_hyp_2 aag subjects x ms (f (g ms') (h ms')) as as' ao ao' =
   integrity_hyp_2 aag subjects x ms (h ms') as as' ao ao'"
  by (auto simp: integrity_hyp_def vcpu)

lemmas [Access_AC_assms, simp] =
  integrity_hyp_machine_upd[where h="\<lambda>_. _"]
  integrity_hyp_machine_upd[where h="\<lambda>_. _" and g="\<lambda>_. _"]
  integrity_hyp_machine_upd[where h=id, simplified machine_state_update_id id_apply]
  integrity_hyp_machine_upd[where h=id and g="\<lambda>_. _", simplified machine_state_update_id id_apply]

end

locale Arch_fpu_machine_update_eq = Arch +
  fixes f :: "('a \<Rightarrow> 'a) \<Rightarrow> machine_state \<Rightarrow> machine_state"
  assumes fpu: "fpu_state (f g ms) = fpu_state ms"
begin arch_global_naming

lemma integrity_fpu_machine_upd:
  "integrity_fpu_2 aag subjects x (f (g ms) (h ms)) ms' kh kh' =
   integrity_fpu_2 aag subjects x (h ms) ms' kh kh'"
  "integrity_fpu_2 aag subjects x ms (f (g ms') (h ms')) kh kh' =
   integrity_fpu_2 aag subjects x ms (h ms') kh kh'"
  by (auto simp: integrity_fpu_def fpu)

lemmas [Access_AC_assms, simp] =
  integrity_fpu_machine_upd[where h="\<lambda>_. _"]
  integrity_fpu_machine_upd[where h="\<lambda>_. _" and g="\<lambda>_. _"]
  integrity_fpu_machine_upd[where h=id, simplified machine_state_update_id id_apply]
  integrity_fpu_machine_upd[where h=id and g="\<lambda>_. _", simplified machine_state_update_id id_apply]

end

locale Arch_integrity_machine_update_eq = Arch_fpu_machine_update_eq + Arch_hyp_machine_update_eq

sublocale Arch \<subseteq> irq_state_update: Arch_integrity_machine_update_eq irq_state_update by unfold_locales auto
sublocale Arch \<subseteq> underlying_memory_update: Arch_integrity_machine_update_eq underlying_memory_update by unfold_locales auto
sublocale Arch \<subseteq> device_state_update: Arch_integrity_machine_update_eq device_state_update by unfold_locales auto
sublocale Arch \<subseteq> rest_update: Arch_integrity_machine_update_eq machine_state_rest_update by unfold_locales auto
sublocale Arch \<subseteq> irq_masks_update: Arch_integrity_machine_update_eq irq_masks_update by unfold_locales auto
sublocale Arch \<subseteq> vcpu_state_update: Arch_fpu_machine_update_eq vcpu_state_update by unfold_locales auto
sublocale Arch \<subseteq> fpu_state_update: Arch_hyp_machine_update_eq fpu_state_update by unfold_locales auto
sublocale Arch \<subseteq> fpu_enabled_update: Arch_integrity_machine_update_eq fpu_enabled_update by unfold_locales auto


context Arch_p_arch_update_eq begin arch_global_naming

lemma state_vrefs[Access_AC_assms, iff]:
  "state_vrefs (f s) = state_vrefs s"
  by (simp add: state_vrefs_def pspace)

end


context Arch begin arch_global_naming

lemma integrity_asids_kh_upd_None[Access_AC_assms]:
  "\<lbrakk> ao' p = None; integrity_asids_2 aag subjects x a as as' ao ao'\<rbrakk>
     \<Longrightarrow> integrity_asids_2 aag subjects x a as as' (ao(p := None)) ao'"
  "\<lbrakk> ao p = None; integrity_asids_2 aag subjects x a as as' ao ao'\<rbrakk>
     \<Longrightarrow> integrity_asids_2 aag subjects x a as as' ao (ao'(p := None)) "
  unfolding integrity_asids_def opt_map_def
  by (auto split: option.split_asm)

lemma integrity_hyp_kh_upd_None[Access_AC_assms]:
  "\<lbrakk> ao' p = None; integrity_hyp_2 aag subjects x ms ms' as as' ao ao'\<rbrakk>
     \<Longrightarrow> integrity_hyp_2 aag subjects x ms ms' as as' (ao(p := None)) ao'"
  "\<lbrakk> ao p = None; integrity_hyp_2 aag subjects x ms ms' as as' ao ao'\<rbrakk>
     \<Longrightarrow> integrity_hyp_2 aag subjects x ms ms' as as' ao (ao'(p := None)) "
  unfolding integrity_hyp_def vcpu_integrity_def vcpu_of_state_def opt_map_def
  by (auto split: option.split_asm)

lemma integrity_fpu_kh_upd[Access_AC_assms]:
  "\<lbrakk> \<forall>tcb. kh p \<noteq> Some (TCB tcb); \<forall>tcb. v \<noteq> Some (TCB tcb);
     integrity_fpu_2 aag subjects x ms ms' kh kh' \<rbrakk>
    \<Longrightarrow> integrity_fpu_2 aag subjects x ms ms' (kh(p := v)) kh'"
  "\<lbrakk> \<forall>tcb. kh' p \<noteq> Some (TCB tcb); \<forall>tcb. v \<noteq> Some (TCB tcb);
     integrity_fpu_2 aag subjects x ms ms' kh kh' \<rbrakk>
    \<Longrightarrow> integrity_fpu_2 aag subjects x ms ms' kh (kh'(p := v))"
  by (auto simp: integrity_fpu_def fpu_of_state_def
          split: option.splits kernel_object.splits)

lemma integrity_fpu_kh_upd_neq[Access_AC_assms]:
  assumes "x \<noteq> p"
  shows "integrity_fpu_2 aag subjects x ms ms' (kh(p := v)) kh' =
         integrity_fpu_2 aag subjects x ms ms' kh kh'"
        "integrity_fpu_2 aag subjects x ms ms' kh (kh'(p := v)) =
         integrity_fpu_2 aag subjects x ms ms' kh kh'"
  by (auto simp: assms integrity_fpu_def fpu_of_state_def)

lemma integrity_fpu_tcb_upd[Access_AC_assms]:
  "\<lbrakk> kh p = Some (TCB tcb); v = Some (TCB tcb'); tcb_arch tcb = tcb_arch tcb'\<rbrakk>
     \<Longrightarrow> integrity_fpu_2 aag subjects x ms ms' (kh(p \<mapsto> TCB tcb')) kh' =
         integrity_fpu_2 aag subjects x ms ms' kh kh'"
  "\<lbrakk> kh' p = Some (TCB tcb); v = Some (TCB tcb'); tcb_arch tcb = tcb_arch tcb'\<rbrakk>
     \<Longrightarrow> integrity_fpu_2 aag subjects x ms ms' kh (kh'(p \<mapsto> TCB tcb')) =
         integrity_fpu_2 aag subjects x ms ms' kh kh'"
  unfolding integrity_fpu_def opt_map_def
  by (auto simp: fpu_of_state_def split: option.splits if_splits kernel_object.splits)

lemma integrity_fpu_set_registers[Access_AC_assms]:
  "\<lbrakk> kh x = Some (TCB tcb); kh' x = Some (TCB tcb');
     tcb_arch tcb' = arch_tcb_set_registers regs (tcb_arch tcb) \<rbrakk>
     \<Longrightarrow> integrity_fpu_2 aag subjects x ms ms kh kh'"
  by (auto simp: integrity_fpu_def fpu_of_state_def arch_tcb_set_registers_def opt_map_def
          split: option.splits kernel_object.splits)

lemma integrity_hyp_ao_upd:
  "\<lbrakk> ao' p = Some ako'; vcpu_of ako = None; vcpu_of ako' = None;
     integrity_hyp_2 aag subjects x ms ms' as as' ao ao' \<rbrakk>
     \<Longrightarrow> integrity_hyp_2 aag subjects x ms ms' as as' (ao(p \<mapsto> ako)) ao'"
  "\<lbrakk> ao p = Some ako; vcpu_of ako = None; vcpu_of ako' = None;
     integrity_hyp_2 aag subjects x ms ms' as as' ao ao' \<rbrakk>
     \<Longrightarrow> integrity_hyp_2 aag subjects x ms ms' as as' ao (ao'(p \<mapsto> ako')) "
  unfolding integrity_hyp_def vcpu_integrity_def vcpu_of_state_def opt_map_def
  by (case_tac "x = p"; clarsimp; auto split: option.splits)+

end


global_interpretation Access_AC_4?: Access_AC_4
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact Access_AC_assms)?)
qed


locale Arch_pas_refined_arch_update_eq = Arch +
  fixes f :: "('a \<Rightarrow> 'a) \<Rightarrow> arch_state \<Rightarrow> arch_state"
  assumes atable: "arm_asid_table (f g ms) = arm_asid_table ms"
begin

lemma vs_lookup_table_arch_upd:
  "vs_lookup_table lvl asid vref (arch_state_update (\<lambda>ms. f (g ms) (h ms)) s) =
   vs_lookup_table lvl asid vref (arch_state_update h s)"
  by (auto simp: vs_lookup_table_eq_lift pool_for_asid_def atable)

lemma pas_refined_arch_upd:
  "pas_refined aag (arch_state_update (\<lambda>ms. f (g ms) (h ms)) s) =
   pas_refined aag (arch_state_update h s)"
  unfolding pas_refined_def state_objs_to_policy_def state_vrefs_def
  by (auto simp: vs_lookup_table_arch_upd atable)

lemma arch_state_update_id:
  "arch_state_update id s = s"
  by simp

lemmas [simp] =
  pas_refined_arch_upd[where h="\<lambda>_. _"]
  pas_refined_arch_upd[where h="\<lambda>_. _" and g="\<lambda>_. _"]
  pas_refined_arch_upd[where h=id, simplified arch_state_update_id id_apply]
  pas_refined_arch_upd[where h=id and g="\<lambda>_. _", simplified arch_state_update_id id_apply]

end

sublocale Arch \<subseteq> kernel_vspace_update: Arch_pas_refined_arch_update_eq arm_kernel_vspace_update by unfold_locales auto
sublocale Arch \<subseteq> vmid_table_update: Arch_pas_refined_arch_update_eq arm_vmid_table_update by unfold_locales auto
sublocale Arch \<subseteq> next_vmid_update: Arch_pas_refined_arch_update_eq arm_next_vmid_update by unfold_locales auto
sublocale Arch \<subseteq> global_vspace_update: Arch_pas_refined_arch_update_eq arm_us_global_vspace_update by unfold_locales auto
sublocale Arch \<subseteq> current_vcpu_update: Arch_pas_refined_arch_update_eq arm_current_vcpu_update by unfold_locales auto
sublocale Arch \<subseteq> numlistregs_update: Arch_pas_refined_arch_update_eq arm_gicvcpu_numlistregs_update by unfold_locales auto
sublocale Arch \<subseteq> current_fpu_update: Arch_pas_refined_arch_update_eq arm_current_fpu_owner_update by unfold_locales auto


context Arch begin arch_global_naming

lemma pas_refined_irq_state_independent[intro!, simp]:
  "pas_refined x (s\<lparr>machine_state := machine_state s\<lparr>irq_state := f (irq_state (machine_state s))\<rparr>\<rparr>) =
   pas_refined x s"
  by (simp add: pas_refined_def)

lemma vspace_objs_of_Some:
  "(vspace_objs_of s p = Some ao) = (aobjs_of s p = Some ao \<and> \<not>is_VCPU ao)"
  by (clarsimp simp: in_opt_map_eq vspace_obj_of_Some)

lemma state_irqs_to_policy_eq_caps:
  "\<lbrakk> x \<in> state_irqs_to_policy_aux aag caps; caps = caps' \<rbrakk>
     \<Longrightarrow> x \<in> state_irqs_to_policy_aux aag caps'"
  by (erule subst)

lemma vs_lookup_table_eqI':
    "\<lbrakk> asid_table s' (asid_high_bits_of asid) = asid_table s (asid_high_bits_of asid);
       \<forall>pool_ptr. asid_table s' (asid_high_bits_of asid) = Some pool_ptr
                  \<longrightarrow> bot_level \<le> max_pt_level
                  \<longrightarrow> vspace_for_pool pool_ptr asid (asid_pools_of s') =
                      vspace_for_pool pool_ptr asid (asid_pools_of s);
       bot_level < max_pt_level \<longrightarrow> pts_of s' = pts_of s \<rbrakk>
   \<Longrightarrow> vs_lookup_table bot_level asid vref s' = vs_lookup_table bot_level asid vref s"
  by (auto simp: obind_def vs_lookup_table_def asid_pool_level_eq[symmetric]
                 pool_for_asid_def entry_for_pool_def vspace_for_pool_def
          split: option.splits)

lemma vs_refs_aux_eqI:
  assumes "pts_of s' = pts_of s"
  and "\<forall>p sz. data_at sz p s' = data_at sz p s"
  and "\<forall>pool_ptr asid. (asid_pools_of s' |> oapply asid |> ogets ap_vspace) pool_ptr
                     = (asid_pools_of s |> oapply asid |> ogets ap_vspace) pool_ptr"
  and "aobjs_of s p = Some ao"
  and "aobjs_of s' p = Some ao'"
  shows "vs_refs_aux level ao = vs_refs_aux level ao'"
  apply (insert assms)
  apply (clarsimp simp: fun_eq_iff)
  apply (erule_tac x=p in allE)+
  apply (fastforce simp: vs_refs_aux_def graph_of_def image_iff opt_map_def ogets_def
                  split: option.splits arch_kernel_obj.splits)
  done

lemma state_vrefsD:
  "\<lbrakk> vs_lookup_table level asid vref s = Some (lvl, p);
     vspace_objs_of s p = Some ao; vref \<in> user_region; x \<in> vs_refs_aux lvl ao \<rbrakk>
     \<Longrightarrow> x \<in> state_vrefs s p"
  unfolding state_vrefs_def by fastforce

lemma state_vrefs_eqI':
  assumes "asid_table s' = asid_table s"
    and "pts_of s' = pts_of s"
    and "\<forall>p sz. data_at sz p s' = data_at sz p s"
    and "\<forall>pool_ptr asid. (asid_pools_of s' |> oapply asid |> ogets ap_vspace) pool_ptr
                       = (asid_pools_of s |> oapply asid |> ogets ap_vspace) pool_ptr"
  shows "state_vrefs s' = state_vrefs s"
  apply (insert assms)
  apply (prop_tac "\<And>level asid vref. vs_lookup_table level asid vref s' = vs_lookup_table level asid vref s")
   apply (rule vs_lookup_table_eqI')
     apply (auto simp: fun_eq_iff vspace_for_pool_def entry_for_pool_def obind_def ogets_def opt_map_def)[3]
  apply (rule ext)+
  apply (intro equalityI subsetI; subst (asm) state_vrefs_def; clarsimp)

   apply (clarsimp simp: vspace_objs_of_Some)
   apply (case_tac "vspace_objs_of s x"; clarsimp?)
    apply (clarsimp simp: fun_eq_iff)
    apply (erule_tac x=x in allE)+
    apply (fastforce simp: vspace_obj_of_def vs_refs_aux_def graph_of_def
                           image_iff opt_map_def ogets_def is_VCPU_def
                    split: option.splits arch_kernel_obj.splits if_splits )[1]
   apply (prop_tac "\<forall>level. vs_refs_aux level ao = vs_refs_aux level ac")
    apply (intro allI vs_refs_aux_eqI; fastforce simp: vspace_objs_of_Some)
   apply (fastforce intro: state_vrefsD)

  apply (clarsimp simp: vspace_objs_of_Some)
  apply (case_tac "vspace_objs_of s' x"; clarsimp?)
   apply (clarsimp simp: fun_eq_iff)
   apply (erule_tac x=x in allE)+
   apply (fastforce simp: vspace_obj_of_def vs_refs_aux_def graph_of_def
                          image_iff opt_map_def ogets_def is_VCPU_def
                   split: option.splits arch_kernel_obj.splits if_splits )[1]
  apply (prop_tac "\<forall>level. vs_refs_aux level ac = vs_refs_aux level ao")
   apply (intro allI vs_refs_aux_eqI; fastforce simp: vspace_objs_of_Some)
  apply (fastforce intro!: state_vrefsD)
  done

lemma state_vrefs_eqI:
  assumes "asid_table s' = asid_table s"
    and "vspace_objs_of s' = vspace_objs_of s"
  shows "state_vrefs s' = state_vrefs s"
  apply (prop_tac "\<forall>level asid vref. vs_lookup_table level asid vref s = vs_lookup_table level asid vref s'")
   apply (intro allI vs_lookup_table_eqI')
  using assms apply (fastforce simp: obj_at_def)
  using vspace_objs_of_aps_eq assms apply fastforce
  using vspace_objs_of_pts_eq assms apply fastforce
  using assms apply (fastforce simp: state_vrefs_def)
  done

lemma dmo_no_mem_respects:
  assumes p: "\<And>P. mop \<lbrace>\<lambda>ms. P (underlying_memory ms)\<rbrace>"
  assumes q: "\<And>P. mop \<lbrace>\<lambda>ms. P (device_state ms)\<rbrace>"
  assumes r: "\<And>P. mop \<lbrace>\<lambda>ms. P (vcpu_state ms)\<rbrace>"
  assumes s: "\<And>P. mop \<lbrace>\<lambda>ms. P (fpu_state ms)\<rbrace>"
  shows "do_machine_op mop \<lbrace>integrity aag X st\<rbrace>"
  unfolding integrity_def integrity_asids_def integrity_hyp_def integrity_fpu_def
            integrity_fpu_def tcb_states_of_state_def get_tcb_def
  by (wpsimp wp: dmo_machine_state_lift | wps assms)+

end

end
