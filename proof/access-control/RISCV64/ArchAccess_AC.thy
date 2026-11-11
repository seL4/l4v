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

clear_named_theorems Arch_assms (* accumulate assumptions for Access_AC locale *)

lemma acap_class_reply[Arch_assms]:
  "acap_class acap \<noteq> ReplyClass t"
  by (cases acap; simp)

lemma arch_troa_tro_alt[Arch_assms, elim!]:
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

lemma clas_caps_of_state[Arch_assms]:
  "\<lbrakk> caps_of_state s slot = Some cap; pas_refined aag s \<rbrakk>
   \<Longrightarrow> cap_links_asid_slot aag (pasObjectAbs aag (fst slot)) cap"
  apply (clarsimp simp: cap_links_asid_slot_def label_owns_asid_slot_def pas_refined_def)
  apply (drule state_asids_to_policy_aux.intros)
   apply assumption
  apply (blast dest: state_asids_to_policy_aux.intros)
  done

lemma arch_tro_alt_trans_spec[Arch_assms]:
  "\<lbrakk> arch_integrity_obj_alt aag subjects l ko ko';
     arch_integrity_obj_alt aag subjects l ko' ko'' \<rbrakk>
   \<Longrightarrow> arch_integrity_obj_alt aag subjects l ko ko''"
  by (fastforce simp: arch_integrity_obj_alt.simps)

lemma tcb_hyp_refs_arch_tcb_set_registers[Arch_assms]:
  "tcb_hyp_refs (arch_tcb_set_registers regs atcb) = tcb_hyp_refs atcb"
  by (simp add: arch_tcb_set_registers_def)

lemmas Access_AC_assms = Arch_assms (* extract accumulated assumptions *)

end (* Arch *)

global_interpretation Access_AC?: Access_AC
proof goal_cases
  case 1 show ?case
    by (unfold_locales; (fact RISCV64.Access_AC_assms)?)
qed

context Arch begin arch_global_naming

clear_named_theorems Arch_assms (* accumulate assumptions for Access_AC_2 locale *)

lemma auth_ipc_buffers_tro[Arch_assms]:
  "\<lbrakk> integrity_obj_state aag activate subjects s s';
     x \<in> auth_ipc_buffers s' p; pasObjectAbs aag p \<notin> subjects \<rbrakk>
   \<Longrightarrow> x \<in> auth_ipc_buffers s p"
  by (drule_tac x = p in spec)
     (erule integrity_objE;
      fastforce simp: tcb_states_of_state_def get_tcb_def auth_ipc_buffers_def
               split: cap.split_asm arch_cap.split_asm if_split_asm bool.splits)

lemma trasids_trans[Arch_assms]:
  "\<lbrakk> \<forall>x a. integrity_asids_2 aag subjects x a as as' ao ao';
     \<forall>x a. integrity_asids_2 aag subjects x a as' as'' ao' ao'' \<rbrakk>
   \<Longrightarrow> \<forall>x a. integrity_asids_2 aag subjects x a as as'' ao ao''"
  by (clarsimp simp: integrity_asids_def) metis

lemma integrity_asids_refl[Arch_assms, simp]:
  "integrity_asids aag subjects x a s s"
  by (simp add: integrity_asids_def)

lemma integrity_asids_update_autarch[Arch_assms]:
  "\<lbrakk> integrity_asids_2 aag subjects x a as as' ao ao'; pasObjectAbs aag ptr \<in> subjects \<rbrakk>
   \<Longrightarrow> integrity_asids_2 aag subjects x a as as' ao (ao'(ptr := ako))"
  by (auto simp: integrity_asids_def opt_map_def)

lemma integrity_hyp_triv[intro!,simp]:
  "integrity_hyp_2 aag subjects x ms ms' as as' ao ao'"
  by (simp add: integrity_hyp_def)

lemma integrity_fpu_triv[intro!,simp]:
  "integrity_fpu_2 aag subjects x as as' kh kh'"
  by (simp add: integrity_fpu_def)

lemma integrity_hyp_post_taut:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>_ s. integrity_hyp_2 aag subjects x (ms s) (ms' s) (as s) (as' s) (ao s) (ao' s)\<rbrace>"
  by (wpsimp simp: integrity_hyp_def)

lemma integrity_fpu_post_taut:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>_ s. integrity_fpu_2 aag subjects x (as s) (as' s) (kh s) (kh' s)\<rbrace>"
  by (wpsimp simp: integrity_hyp_def)

lemmas [wp] =
  integrity_hyp_post_taut[where P=\<top>]
  integrity_fpu_post_taut[where P=\<top>]

(* trivial assumptions *)
lemma [Arch_assms]:
  shows integrity_hyp_refl:
    "integrity_hyp_2 aag subjects x ms ms as as ao ao"
  and integrity_fpu_refl:
    "integrity_fpu_2 aag subjects x ms ms kh kh"
  and trhyp_trans:
    "\<lbrakk> integrity_hyp_2 aag subjects x ms ms' as as' ao ao';
       integrity_hyp_2 aag subjects x ms' ms'' as' as'' ao' ao'' \<rbrakk>
     \<Longrightarrow> integrity_hyp_2 aag subjects x ms ms'' as as'' ao ao''"
  and trfpu_trans:
    "\<lbrakk> integrity_fpu_2 aag subjects x ms ms' kh kh';
       integrity_fpu_2 aag subjects x ms' ms'' kh' kh'' \<rbrakk>
     \<Longrightarrow> integrity_fpu_2 aag subjects x ms ms'' kh kh''"
  and integrity_hyp_update_autarch:
    "\<lbrakk> integrity_hyp_2 aag subjects x ms ms' as as' ao ao'; pasObjectAbs aag ptr \<in> subjects \<rbrakk>
     \<Longrightarrow> integrity_hyp_2 aag subjects x ms ms' as as' ao (ao'(ptr := ako))"
  and integrity_fpu_update_autarch:
    "\<lbrakk> integrity_fpu_2 aag subjects x ms ms' kh kh'; pasObjectAbs aag ptr \<in> subjects \<rbrakk>
     \<Longrightarrow> integrity_fpu_2 aag subjects x ms ms' kh (kh'(ptr \<mapsto> obj))"
  by auto

lemmas Access_AC_2_assms = Arch_assms (* extract accumulated assumptions *)

end (* Arch *)

global_interpretation Access_AC_2?: Access_AC_2
proof goal_cases
  case 1 show ?case
    by (unfold_locales; (fact RISCV64.Access_AC_2_assms)?)
qed

context Arch begin arch_global_naming

clear_named_theorems Arch_assms (* accumulate assumptions for Access_AC_3 locale *)

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
    apply (simp add: valid_tcb_def valid_ipc_buffer_cap_def is_aligned_andI1 split: bool.splits)
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

lemma auth_ipc_buffers_member[Arch_assms]:
  "\<lbrakk> x \<in> auth_ipc_buffers s p; valid_objs s \<rbrakk>
   \<Longrightarrow> \<exists>tcb acap. get_tcb p s = Some tcb
                \<and> tcb_ipcframe tcb = (ArchObjectCap acap)
                \<and> caps_of_state s (p, tcb_cnode_index 4) = Some (ArchObjectCap acap)
                \<and> Write \<in> arch_cap_auth_conferred acap
                \<and> x \<in> aobj_ref' acap"
  by (fastforce simp: auth_ipc_buffers_def caps_of_state_tcb' arch_cap_auth_conferred_def
                      vspace_cap_rights_to_auth_def ipcframe_subset_page
               split: option.splits cap.splits arch_cap.splits bool.splits if_splits)

lemma asid_pool_integrity_mono[Arch_assms]:
  "\<lbrakk> asid_pool_integrity S aag cont cont'; S \<subseteq> T \<rbrakk> \<Longrightarrow> asid_pool_integrity T aag cont cont'"
  unfolding asid_pool_integrity_def by fastforce

lemma integrity_asids_mono[Arch_assms]:
  "\<lbrakk> integrity_asids aag S x a s s'; S \<subseteq> T; pas_refined aag s; valid_objs s \<rbrakk>
   \<Longrightarrow> integrity_asids aag T x a s s'"
  by (fastforce simp: integrity_asids_def)

lemma arch_integrity_obj_atomic_mono[Arch_assms]:
  "\<lbrakk> arch_integrity_obj_atomic aag S l ao ao'; S \<subseteq> T; pas_refined aag s; valid_objs s \<rbrakk>
   \<Longrightarrow> arch_integrity_obj_atomic aag T l ao ao'"
  by (clarsimp simp: arch_integrity_obj_atomic.simps asid_pool_integrity_mono)

(* trivial assumptions *)
lemma [Arch_assms]:
  shows integrity_hyp_mono:
    "\<lbrakk> integrity_hyp aag S x s s'; S \<subseteq> T \<rbrakk>
     \<Longrightarrow> integrity_hyp aag T x s s'"
  and integrity_fpu_mono:
    "\<lbrakk> integrity_fpu aag S x s s'; S \<subseteq> T \<rbrakk>
     \<Longrightarrow> integrity_fpu aag T x s s'"
  by auto

lemmas Access_AC_3_assms = Arch_assms (* extract accumulated assumptions *)

end (* Arch *)

global_interpretation Access_AC_3?: Access_AC_3
proof goal_cases
  case 1 show ?case
    by (unfold_locales; (fact RISCV64.Access_AC_3_assms)?)
qed

context Arch_p_arch_update_eq begin arch_global_naming

lemma state_vrefs[iff]:
  "state_vrefs (f s) = state_vrefs s"
  by (simp add: state_vrefs_def pspace)

end (* Arch_p_arch_update_eq *)

context Arch begin arch_global_naming

clear_named_theorems Arch_assms (* accumulate assumptions for Access_AC_4 locale *)

lemmas [Arch_assms] =
  cdt_update.state_vrefs
  cur_domain_update.state_vrefs
  cur_thread_update.state_vrefs
  domain_index_update.state_vrefs
  domain_list_update.state_vrefs
  domain_start_index_update.state_vrefs
  domain_time_update.state_vrefs
  irq_node_update_arch.state_vrefs
  interrupt_update.state_vrefs
  revokable_update.state_vrefs
  machine_state_update.state_vrefs
  ready_queues_update.state_vrefs
  scheduler_action_update.state_vrefs
  more_update.state_vrefs

lemma integrity_hyp_machine_upd:
  "integrity_hyp_2 aag subjects x (f (g ms) (h ms)) ms' as as' ao ao' =
   integrity_hyp_2 aag subjects x (h ms) ms' as as' ao ao'"
  "integrity_hyp_2 aag subjects x ms (f (g ms') (h ms')) as as' ao ao' =
   integrity_hyp_2 aag subjects x ms (h ms') as as' ao ao'"
  by auto

lemmas integrity_hyp_machine_upds[Arch_assms] =
  integrity_hyp_machine_upd[where h="\<lambda>_. _"]
  integrity_hyp_machine_upd[where h="\<lambda>_. _" and g="\<lambda>_. _"]
  integrity_hyp_machine_upd[where h=id, simplified machine_state_update_id id_apply]
  integrity_hyp_machine_upd[where h=id and g="\<lambda>_. _", simplified machine_state_update_id id_apply]

lemma integrity_fpu_machine_upd:
  "integrity_fpu_2 aag subjects x (f (g ms) (h ms)) ms' kh kh' =
   integrity_fpu_2 aag subjects x (h ms) ms' kh kh'"
  "integrity_fpu_2 aag subjects x ms (f (g ms') (h ms')) kh kh' =
   integrity_fpu_2 aag subjects x ms (h ms') kh kh'"
  by auto

lemmas integrity_fpu_machine_upds[Arch_assms] =
  integrity_fpu_machine_upd[where h="\<lambda>_. _"]
  integrity_fpu_machine_upd[where h="\<lambda>_. _" and g="\<lambda>_. _"]
  integrity_fpu_machine_upd[where h=id, simplified machine_state_update_id id_apply]
  integrity_fpu_machine_upd[where h=id and g="\<lambda>_. _", simplified machine_state_update_id id_apply]

lemma integrity_asids_kh_upd_None[Arch_assms]:
  "\<lbrakk> ao' p = None; integrity_asids_2 aag subjects x a as as' ao ao'\<rbrakk>
   \<Longrightarrow> integrity_asids_2 aag subjects x a as as' (ao(p := None)) ao'"
  "\<lbrakk> ao p = None; integrity_asids_2 aag subjects x a as as' ao ao'\<rbrakk>
   \<Longrightarrow> integrity_asids_2 aag subjects x a as as' ao (ao'(p := None))"
  unfolding integrity_asids_def opt_map_def
  by (auto split: option.split_asm)

(* trivial assumptions *)
lemma [Arch_assms]:
  shows integrity_hyp_kh_upd_None:
    "\<lbrakk> ao' p = None; integrity_hyp_2 aag subjects x ms ms' as as' ao ao'\<rbrakk>
     \<Longrightarrow> integrity_hyp_2 aag subjects x ms ms' as as' (ao(p := None)) ao'"
    "\<lbrakk> ao p = None; integrity_hyp_2 aag subjects x ms ms' as as' ao ao'\<rbrakk>
     \<Longrightarrow> integrity_hyp_2 aag subjects x ms ms' as as' ao (ao'(p := None))"
  and integrity_fpu_kh_upd:
    "\<lbrakk> \<forall>tcb. kh p \<noteq> Some (TCB tcb); \<forall>tcb. v \<noteq> Some (TCB tcb);
       integrity_fpu_2 aag subjects x ms ms' kh kh' \<rbrakk>
     \<Longrightarrow> integrity_fpu_2 aag subjects x ms ms' (kh(p := v)) kh'"
    "\<lbrakk> \<forall>tcb. kh' p \<noteq> Some (TCB tcb); \<forall>tcb. v \<noteq> Some (TCB tcb);
       integrity_fpu_2 aag subjects x ms ms' kh kh' \<rbrakk>
     \<Longrightarrow> integrity_fpu_2 aag subjects x ms ms' kh (kh'(p := v))"
  and integrity_fpu_kh_upd_neq:
    "x \<noteq> p
     \<Longrightarrow> integrity_fpu_2 aag subjects x ms ms' (kh(p := v)) kh' =
         integrity_fpu_2 aag subjects x ms ms' kh kh'"
    "x \<noteq> p
     \<Longrightarrow> integrity_fpu_2 aag subjects x ms ms' kh (kh'(p := v)) =
         integrity_fpu_2 aag subjects x ms ms' kh kh'"
  and integrity_fpu_tcb_upd:
    "\<lbrakk> kh p = Some (TCB tcb); v = Some (TCB tcb'); tcb_arch tcb = tcb_arch tcb'\<rbrakk>
     \<Longrightarrow> integrity_fpu_2 aag subjects x ms ms' (kh(p \<mapsto> TCB tcb')) kh' =
         integrity_fpu_2 aag subjects x ms ms' kh kh'"
    "\<lbrakk> kh' p = Some (TCB tcb); v = Some (TCB tcb'); tcb_arch tcb = tcb_arch tcb'\<rbrakk>
     \<Longrightarrow> integrity_fpu_2 aag subjects x ms ms' kh (kh'(p \<mapsto> TCB tcb')) =
         integrity_fpu_2 aag subjects x ms ms' kh kh'"
  and integrity_fpu_set_registers:
    "\<lbrakk> kh x = Some (TCB tcb); kh' x = Some (TCB tcb');
       tcb_arch tcb' = arch_tcb_set_registers regs (tcb_arch tcb) \<rbrakk>
     \<Longrightarrow> integrity_fpu_2 aag subjects x ms ms kh kh'"
  by auto

lemmas Access_AC_4_assms = Arch_assms (* extract accumulated assumptions *)

end (* Arch *)

global_interpretation Access_AC_4?: Access_AC_4
proof goal_cases
  case 1 show ?case
    by (unfold_locales; (fact RISCV64.Access_AC_4_assms)?)
qed

locale Arch_pas_refined_arch_update_eq = Arch +
  fixes f :: "('a \<Rightarrow> 'a) \<Rightarrow> arch_state \<Rightarrow> arch_state"
  assumes atable: "riscv_asid_table (f g ms) = riscv_asid_table ms"
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

end (* Arch_pas_refined_arch_update_eq *)

sublocale Arch \<subseteq> global_pts_update: Arch_pas_refined_arch_update_eq riscv_global_pts_update by unfold_locales auto
sublocale Arch \<subseteq> kernel_vspace_update: Arch_pas_refined_arch_update_eq riscv_kernel_vspace_update by unfold_locales auto

context Arch begin arch_global_naming

lemma dmo_no_mem_respects:
  assumes p: "\<And>P. mop \<lbrace>\<lambda>ms. P (underlying_memory ms)\<rbrace>"
  assumes q: "\<And>P. mop \<lbrace>\<lambda>ms. P (device_state ms)\<rbrace>"
  shows "do_machine_op mop \<lbrace>integrity aag X st\<rbrace>"
  unfolding integrity_def tcb_states_of_state_def get_tcb_def
  by (wpsimp wp: dmo_machine_state_lift | wps assms)+

lemma state_vrefsD:
  "\<lbrakk> vs_lookup_table level asid vref s = Some (lvl, p);
     aobjs_of s p = Some ao; vref \<in> user_region; x \<in> vs_refs_aux lvl ao \<rbrakk>
   \<Longrightarrow> x \<in> state_vrefs s p"
  unfolding state_vrefs_def by fastforce

end (* Arch *)

end
