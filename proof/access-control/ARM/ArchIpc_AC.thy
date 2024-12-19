(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchIpc_AC
imports Ipc_AC
begin

context Arch begin global_naming ARM_A

named_theorems Ipc_AC_assms

declare make_fault_message_inv[Ipc_AC_assms]
declare handle_arch_fault_reply_typ_at[Ipc_AC_assms]

crunch cap_insert_ext
  for integrity_asids[Ipc_AC_assms, wp]: "integrity_asids aag subjects x a st"

lemma arch_derive_cap_auth_derived[Ipc_AC_assms]:
  "\<lbrace>\<top>\<rbrace> arch_derive_cap acap \<lbrace>\<lambda>rv _. rv \<noteq> NullCap \<longrightarrow> auth_derived rv (ArchObjectCap acap)\<rbrace>, -"
  by (case_tac acap;
      simp add: derive_cap_def arch_derive_cap_def;
      wpc?;
      wp?;
      simp add: auth_derived_def cap_auth_conferred_def arch_cap_auth_conferred_def)

lemma lookup_ipc_buffer_has_auth[Ipc_AC_assms, wp]:
  "\<lbrace>pas_refined aag and valid_objs\<rbrace>
   lookup_ipc_buffer True receiver
   \<lbrace>\<lambda>rv _. ipc_buffer_has_auth aag receiver rv\<rbrace>"
  apply (rule hoare_pre)
   apply (simp add: lookup_ipc_buffer_def)
   apply (wp get_cap_wp thread_get_wp'
        | wpc)+
  apply (clarsimp simp: cte_wp_at_caps_of_state ipc_buffer_has_auth_def get_tcb_ko_at[symmetric])
  apply (frule caps_of_state_tcb_cap_cases [where idx="tcb_cnode_index 4"])
   apply (simp add: dom_tcb_cap_cases)
  apply (frule (1) caps_of_state_valid_cap)
  apply (rule conjI)
   apply (clarsimp simp: valid_cap_simps cap_aligned_def)
   apply (erule aligned_add_aligned)
    apply (rule is_aligned_andI1)
    apply (drule (1) valid_tcb_objs)
    apply (clarsimp simp: valid_obj_def valid_tcb_def valid_ipc_buffer_cap_def
                   split: if_splits)
   apply (rule order_trans [OF _ pbfs_atleast_pageBits])
   apply (simp add: msg_align_bits pageBits_def)
  apply simp
  apply (drule (1) cap_auth_caps_of_state)
  apply (clarsimp simp: aag_cap_auth_def cap_auth_conferred_def arch_cap_auth_conferred_def
                        vspace_cap_rights_to_auth_def vm_read_write_def is_page_cap_def)
  apply (drule bspec)
   apply (erule (3) ipcframe_subset_page)
  apply simp
  done

lemma tcb_context_no_change[Ipc_AC_assms]:
  "\<exists>ctxt. tcb = tcb\<lparr>tcb_arch := arch_tcb_context_set ctxt (tcb_arch tcb)\<rparr>"
  apply (cases tcb, clarsimp)
  apply (case_tac tcb_arch)
  apply (auto simp: arch_tcb_context_set_def)
  done

lemma transfer_caps_loop_valid_arch[Ipc_AC_assms]:
  "transfer_caps_loop ep buffer n caps slots mi \<lbrace>valid_arch_state :: det_ext state \<Rightarrow> _\<rbrace>"
  by (wp valid_arch_state_lift_aobj_at_no_caps transfer_caps_loop_aobj_at)

end


global_interpretation Ipc_AC_1?: Ipc_AC_1
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; fact Ipc_AC_assms)
qed


context Arch begin global_naming ARM_A

lemma store_word_offs_respects_in_ipc[Ipc_AC_assms]:
  "\<lbrace>integrity_tcb_in_ipc aag X receiver epptr TRContext st and
    K ((\<not> is_subject aag receiver \<longrightarrow> auth_ipc_buffers st receiver = ptr_range buf msg_align_bits)
        \<and> is_aligned buf msg_align_bits \<and> r < 2 ^ (msg_align_bits - word_size_bits))\<rbrace>
   store_word_offs buf r v
   \<lbrace>\<lambda>_. integrity_tcb_in_ipc aag X receiver epptr TRContext st\<rbrace>"
  apply (simp add: store_word_offs_def storeWord_def pred_conj_def)
  apply (rule hoare_pre)
   apply (wp dmo_wp)
  apply (unfold integrity_tcb_in_ipc_def)
  apply (elim conjE)
  apply (intro impI conjI)
     apply assumption+
   apply clarsimp
   apply (erule integrity_trans)
   apply (clarsimp simp: ptr_range_off_off_mems integrity_def is_aligned_mask[symmetric])
   apply (intro conjI impI)
     apply (subst (asm) ptr_range_off_off_mems; clarsimp simp: word_size_def)+
  apply simp
  done

crunch set_extra_badge
  for respects_in_ipc[Ipc_AC_assms, wp]: "integrity_tcb_in_ipc aag X receiver epptr TRContext st"
  (wp: store_word_offs_respects_in_ipc)

crunch arch_get_sanitise_register_info
  for inv[Ipc_AC_assms, wp]: P
crunch handle_arch_fault_reply
  for pas_refined[Ipc_AC_assms, wp]: "pas_refined aag"

lemma set_mrs_respects_in_ipc[Ipc_AC_assms]:
  "\<lbrace>integrity_tcb_in_ipc aag X receiver epptr TRContext st and
    K ((\<not> is_subject aag receiver \<longrightarrow>
        (case recv_buf of None \<Rightarrow> True | Some buf' \<Rightarrow> auth_ipc_buffers st receiver =
                                                     ptr_range buf' msg_align_bits)) \<and>
       (case recv_buf of None \<Rightarrow> True | Some buf' \<Rightarrow> is_aligned buf' msg_align_bits))\<rbrace>
     set_mrs receiver recv_buf msgs
   \<lbrace>\<lambda>rv. integrity_tcb_in_ipc aag X receiver epptr TRContext st\<rbrace>"
  unfolding set_mrs_def set_object_def get_object_def
  apply (rule hoare_gen_asm)
  apply (wp mapM_x_wp' store_word_offs_respects_in_ipc
         | wpc
         | simp split del: if_split add: zipWithM_x_mapM_x split_def)+
   apply (clarsimp simp add: set_zip nth_append simp: msg_align_bits' msg_max_length_def
                   split: if_split_asm)
   apply (simp add: msg_registers_def msgRegisters_def upto_enum_def fromEnum_def enum_register)
   apply arith
   apply simp
   apply wp+
  apply (clarsimp simp: arch_tcb_set_registers_def)
  by (rule update_tcb_context_in_ipc [unfolded fun_upd_def]
      ; fastforce simp: arch_tcb_context_set_def)

lemma lookup_ipc_buffer_ptr_range_in_ipc[Ipc_AC_assms]:
  "\<lbrace>valid_objs and integrity_tcb_in_ipc aag X thread epptr tst st\<rbrace>
   lookup_ipc_buffer True thread
   \<lbrace>\<lambda>rv _. \<not> is_subject aag thread \<longrightarrow>
           (case rv of None \<Rightarrow> True | Some buf' \<Rightarrow> auth_ipc_buffers st thread =
                                                   ptr_range buf' msg_align_bits)\<rbrace>"
  unfolding lookup_ipc_buffer_def
  apply (rule hoare_pre)
  apply (wp get_cap_wp thread_get_wp' | wpc)+
  apply (clarsimp simp: cte_wp_at_caps_of_state ipc_buffer_has_auth_def get_tcb_ko_at [symmetric])
  apply (frule caps_of_state_tcb_cap_cases [where idx = "tcb_cnode_index 4"])
   apply (simp add: dom_tcb_cap_cases)
  apply (clarsimp simp: auth_ipc_buffers_def get_tcb_ko_at [symmetric] integrity_tcb_in_ipc_def)
  apply (drule get_tcb_SomeD)
  apply (erule(1) valid_objsE)
  apply (clarsimp simp: valid_obj_def valid_tcb_def valid_ipc_buffer_cap_def case_bool_if
                 split: if_split_asm)
  apply (erule tcb_in_ipc.cases; clarsimp simp: get_tcb_def vm_read_write_def)
  done

lemma lookup_ipc_buffer_aligned[Ipc_AC_assms]:
  "\<lbrace>valid_objs\<rbrace>
   lookup_ipc_buffer True thread
   \<lbrace>\<lambda>rv _. (case rv of None \<Rightarrow> True | Some buf' \<Rightarrow> is_aligned buf' msg_align_bits)\<rbrace>"
  unfolding lookup_ipc_buffer_def
  apply (rule hoare_pre)
   apply (wp get_cap_wp thread_get_wp' | wpc)+
  apply (clarsimp simp: cte_wp_at_caps_of_state get_tcb_ko_at [symmetric])
  apply (frule caps_of_state_tcb_cap_cases [where idx = "tcb_cnode_index 4"])
   apply (simp add: dom_tcb_cap_cases)
  apply (frule (1) caps_of_state_valid_cap)
  apply (clarsimp simp: valid_cap_simps cap_aligned_def)
  apply (erule aligned_add_aligned)
    apply (rule is_aligned_andI1)
    apply (drule (1) valid_tcb_objs)
    apply (clarsimp simp: valid_obj_def valid_tcb_def valid_ipc_buffer_cap_def
                   split: if_splits)
  apply (rule order_trans [OF _ pbfs_atleast_pageBits])
  apply (simp add: msg_align_bits pageBits_def)
  done

lemma handle_arch_fault_reply_respects[Ipc_AC_assms]:
  "\<lbrace>integrity aag X st and K (is_subject aag thread)\<rbrace>
   handle_arch_fault_reply fault thread x y
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  by (wpsimp simp: handle_arch_fault_reply_def)

lemma auth_ipc_buffers_kheap_update[Ipc_AC_assms]:
  "\<lbrakk> x \<in> auth_ipc_buffers st thread; kheap st thread = Some (TCB tcb);
     kheap s thread = Some (TCB tcb'); tcb_ipcframe tcb = tcb_ipcframe tcb' \<rbrakk>
     \<Longrightarrow> x \<in> auth_ipc_buffers (s\<lparr>kheap := (kheap s)(thread \<mapsto> TCB tcb)\<rparr>) thread"
  by (clarsimp simp: auth_ipc_buffers_member_def get_tcb_def caps_of_state_tcb)

lemma auth_ipc_buffers_machine_state_update[Ipc_AC_assms, simp]:
  "auth_ipc_buffers (machine_state_update f s) = auth_ipc_buffers s"
  by (clarsimp simp: auth_ipc_buffers_def get_tcb_def)

declare handle_arch_fault_reply_inv[Ipc_AC_assms]
declare arch_get_sanitise_register_info_inv[Ipc_AC_assms]

end


context is_extended begin interpretation Arch . (*FIXME: arch-split*)

lemma list_integ_lift_in_ipc[Ipc_AC_assms]:
  assumes li:
   "\<lbrace>list_integ (cdt_change_allowed aag {pasSubject aag} (cdt st) (tcb_states_of_state st)) st and Q\<rbrace>
    f
    \<lbrace>\<lambda>_. list_integ (cdt_change_allowed aag {pasSubject aag} (cdt st) (tcb_states_of_state st)) st\<rbrace>"
  assumes ekh: "\<And>P. \<lbrace>\<lambda>s. P (ekheap s)\<rbrace> f \<lbrace>\<lambda>rv s. P (ekheap s)\<rbrace>"
  assumes rq: "\<And>P. \<lbrace> \<lambda>s. P (ready_queues s) \<rbrace> f \<lbrace> \<lambda>rv s. P (ready_queues s) \<rbrace>"
  shows "\<lbrace>integrity_tcb_in_ipc aag X receiver epptr ctxt st and Q\<rbrace>
         f
         \<lbrace>\<lambda>_. integrity_tcb_in_ipc aag X receiver epptr ctxt st\<rbrace>"
  apply (unfold integrity_tcb_in_ipc_def integrity_def[abs_def])
  apply (simp del:split_paired_All)
  apply (rule hoare_pre)
   apply (simp only: integrity_cdt_list_as_list_integ)
   apply (rule hoare_lift_Pf2[where f="ekheap"])
    apply (simp add: tcb_states_of_state_def get_tcb_def)
    apply (wp li[simplified tcb_states_of_state_def get_tcb_def] ekh rq)+
  apply (simp only: integrity_cdt_list_as_list_integ)
  apply (simp add: tcb_states_of_state_def get_tcb_def)
  done

lemma cap_insert_ext_integrity_asids_in_ipc[Ipc_AC_assms, wp]:
  "cap_insert_ext src_parent src_slot dest_slot src_p dest_p
   \<lbrace>\<lambda>s. integrity_asids aag subjects x asid st
          (s\<lparr>kheap := \<lambda>a. if a = receiver then kheap st receiver else kheap s a\<rparr>)\<rbrace>"
  by wpsimp

end


global_interpretation Ipc_AC_2?: Ipc_AC_2
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact Ipc_AC_assms)?)
qed

end
