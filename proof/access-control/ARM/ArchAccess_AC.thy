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

lemma as_user_state_vrefs[Access_AC_assms, wp]:
  "as_user t f \<lbrace>\<lambda>s. P (state_vrefs s)\<rbrace>"
  apply (simp add: as_user_def)
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: state_vrefs_def vs_refs_no_global_pts_def get_tcb_def
                 elim!: rsubst[where P=P, OF _ ext]
                 split: option.split_asm Structures_A.kernel_object.split)
  done

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

lemma integrity_hyp_triv[intro!,simp]:
  "integrity_hyp_2 aag subjects x ms ms' as as' ao ao'"
  by (simp add: integrity_hyp_def)

lemma integrity_fpu_triv[intro!,simp]:
  "integrity_fpu_2 aag subjects x as as' kh kh'"
  by (simp add: integrity_fpu_def)

lemma integrity_hyp_wp_triv:
  "\<lbrace>P\<rbrace> c \<lbrace>\<lambda>_ s. integrity_hyp aag subjects x st (f s)\<rbrace>"
  by wpsimp

lemma integrity_fpu_wp_triv:
  "\<lbrace>P\<rbrace> c \<lbrace>\<lambda>_ s. integrity_fpu aag subjects x st (f s)\<rbrace>"
  by wpsimp

lemma integrity_hyp_eq_triv:
  "integrity_hyp_2 a b c d e f g h i = integrity_hyp_2 r s t u v w x y z"
  by simp

lemma integrity_fpu_eq_triv:
  "integrity_fpu_2 a b c d e f g = integrity_fpu_2 t u v w x y z"
  by simp

lemmas integrity_arch_triv =
  integrity_hyp_wp_triv
  integrity_fpu_wp_triv
  integrity_hyp_triv
  integrity_fpu_triv
  integrity_hyp_eq_triv
  integrity_fpu_eq_triv

end


global_interpretation Access_AC_2?: Access_AC_2
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact Access_AC_assms | solves \<open>rule integrity_arch_triv\<close>)?)
qed


context Arch begin arch_global_naming

lemma ipcframe_subset_page:
  "\<lbrakk> valid_objs s; get_tcb p s = Some tcb;
     tcb_ipcframe tcb = ArchObjectCap (PageCap d p' R vms xx);
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
                   \<and> tcb_ipcframe tcb = (ArchObjectCap (PageCap False p' R vms xx))
                   \<and> caps_of_state s (p, tcb_cnode_index 4) =
                      Some (ArchObjectCap (PageCap False p' R vms xx))
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

lemma arch_integrity_obj_atomic_mono[Access_AC_assms]:
  "\<lbrakk> arch_integrity_obj_atomic aag S l ao ao'; S \<subseteq> T; pas_refined aag s; valid_objs s \<rbrakk>
     \<Longrightarrow> arch_integrity_obj_atomic aag T l ao ao'"
  by (clarsimp simp: arch_integrity_obj_atomic.simps asid_pool_integrity_mono)

end


global_interpretation Access_AC_3?: Access_AC_3
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact Access_AC_assms | solves \<open>rule integrity_arch_triv\<close>)?)
qed


context Arch_pspace_update_eq begin arch_global_naming

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

end


global_interpretation Access_AC_4?: Access_AC_4
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact Access_AC_assms | solves \<open>rule integrity_arch_triv\<close>)?)
qed


locale Arch_pas_refined_arch_update_eq = Arch +
  fixes f :: "('a \<Rightarrow> 'a) \<Rightarrow> arch_state \<Rightarrow> arch_state"
  assumes atable: "arm_asid_table (f g ms) = arm_asid_table ms"
begin

lemma pas_refined_arch_upd:
  "pas_refined aag (arch_state_update (\<lambda>ms. f (g ms) (h ms)) s) =
   pas_refined aag (arch_state_update h s)"
  unfolding pas_refined_def state_objs_to_policy_def state_vrefs_def
  by (auto simp: atable)

lemma arch_state_update_id:
  "arch_state_update id s = s"
  by simp

lemmas [simp] =
  pas_refined_arch_upd[where h="\<lambda>_. _"]
  pas_refined_arch_upd[where h="\<lambda>_. _" and g="\<lambda>_. _"]
  pas_refined_arch_upd[where h=id, simplified arch_state_update_id id_apply]
  pas_refined_arch_upd[where h=id and g="\<lambda>_. _", simplified arch_state_update_id id_apply]

end

sublocale Arch \<subseteq> hwasid_table_update: Arch_pas_refined_arch_update_eq arm_hwasid_table_update by unfold_locales auto
sublocale Arch \<subseteq> next_asid_update: Arch_pas_refined_arch_update_eq arm_next_asid_update by unfold_locales auto
sublocale Arch \<subseteq> asid_map_update: Arch_pas_refined_arch_update_eq arm_asid_map_update by unfold_locales auto
sublocale Arch \<subseteq> global_pd_update: Arch_pas_refined_arch_update_eq arm_global_pd_update by unfold_locales auto
sublocale Arch \<subseteq> global_pts_update: Arch_pas_refined_arch_update_eq arm_global_pts_update by unfold_locales auto
sublocale Arch \<subseteq> kernel_vspace_update: Arch_pas_refined_arch_update_eq arm_kernel_vspace_update by unfold_locales auto


context Arch begin arch_global_naming

(* FIXME: move *)
lemma dmo_machine_state_lift:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>\<lambda>s. P (machine_state s)\<rbrace> do_machine_op f \<lbrace>\<lambda>rv s. Q rv (machine_state s)\<rbrace>"
  unfolding do_machine_op_def by wpsimp (erule use_valid; assumption)

lemma dmo_no_mem_respects:
  assumes p: "\<And>P. mop \<lbrace>\<lambda>ms. P (underlying_memory ms)\<rbrace>"
  assumes q: "\<And>P. mop \<lbrace>\<lambda>ms. P (device_state ms)\<rbrace>"
  shows "do_machine_op mop \<lbrace>integrity aag X st\<rbrace>"
  unfolding integrity_def tcb_states_of_state_def get_tcb_def
  by (wpsimp wp: dmo_machine_state_lift | wps assms)+

end

end
