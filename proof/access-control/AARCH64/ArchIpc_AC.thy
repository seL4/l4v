(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchIpc_AC
imports Ipc_AC
begin

context Arch begin arch_global_naming

named_theorems Ipc_AC_assms

lemma make_fault_message_inv[Ipc_AC_assms, wp]:
  "make_fault_msg ft t \<lbrace>P\<rbrace>"
  apply (cases ft, simp_all split del: if_split)
  by (wp as_user_inv getRestartPC_inv mapM_wp' make_arch_fault_msg_inv | simp add: getRegister_def)+

declare handle_arch_fault_reply_typ_at[Ipc_AC_assms]

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
   apply (wp get_cap_wp thread_get_wp' | wpc)+
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
                        vspace_cap_rights_to_auth_def vm_read_write_def)
  apply (drule bspec)
   apply (erule (3) ipcframe_subset_page)
  apply simp
  done

lemma arch_tcb_get_set_registers[Ipc_AC_assms,simp]:
  "arch_tcb_get_registers (arch_tcb_set_registers regs atcb) = regs"
  by (clarsimp simp: arch_tcb_get_registers_def arch_tcb_set_registers_def)

lemma arch_tcb_set_get_registers[Ipc_AC_assms,simp]:
  "arch_tcb_set_registers (arch_tcb_get_registers atcb) atcb = atcb"
  by (simp add: arch_tcb_set_registers_def arch_tcb_get_registers_def)

lemma arch_tcb_set_set_registers[Ipc_AC_assms,simp]:
  "arch_tcb_set_registers regs (arch_tcb_set_registers regs' atcb) =
   arch_tcb_set_registers regs atcb"
  by (auto simp: arch_tcb_set_registers_def)

lemma arch_tcb_context_set_set_registers[Ipc_AC_assms,simp]:
  "arch_tcb_context_set (arch_tcb_context_get (arch_tcb_set_registers regs atcb)) atcb =
   arch_tcb_set_registers regs atcb"
  by (auto simp: arch_tcb_context_set_def arch_tcb_context_get_def arch_tcb_set_registers_def)

lemma arch_tcb_setRegister[Ipc_AC_assms]:
  "((), uc) \<in> fst (setRegister r v (arch_tcb_context_get atcb))
   \<Longrightarrow> uc = arch_tcb_context_get (arch_tcb_set_registers ((arch_tcb_get_registers atcb)(r := v)) atcb)"
  by (simp add: arch_tcb_context_get_def arch_tcb_context_set_def
                arch_tcb_get_registers_def arch_tcb_set_registers_def
                setRegister_def modify_def get_def put_def bind_def)

end


global_interpretation Ipc_AC_1?: Ipc_AC_1
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact Ipc_AC_assms)?)
qed


context Arch begin arch_global_naming

lemma store_word_offs_respects_in_ipc[Ipc_AC_assms]:
  "\<lbrace>integrity_tcb_in_ipc aag X receiver epptr TRContext st and
    K ((\<not> is_subject aag receiver \<longrightarrow> auth_ipc_buffers st receiver = ptr_range buf msg_align_bits)
        \<and> is_aligned buf msg_align_bits \<and> r < 2 ^ (msg_align_bits - word_size_bits))\<rbrace>
   store_word_offs buf r v
   \<lbrace>\<lambda>_. integrity_tcb_in_ipc aag X receiver epptr TRContext st\<rbrace>"
  apply (simp add: store_word_offs_def storeWord_def pred_conj_def)
  apply (wp dmo_wp)
  apply (clarsimp simp: integrity_tcb_in_ipc_def)
  apply (erule integrity_trans)
  apply (clarsimp simp: integrity_def integrity_asids_def)
  apply (subgoal_tac "\<forall>i \<in> set [0..7].
                      buf + of_nat r * of_nat word_size + of_int i \<in> ptr_range buf msg_align_bits")
   apply (fastforce simp: word_rsplit_0 upto.simps atLeastAtMost_upto)
  apply (fastforce simp add: unat_def word_size_def of_nat_nat[symmetric] word_of_nat_less
                   simp del: of_nat_nat intro: ptr_range_off_off_mems)
  done

crunch set_extra_badge
  for respects_in_ipc[Ipc_AC_assms, wp]: "integrity_tcb_in_ipc aag X receiver epptr TRContext st"
  (wp: store_word_offs_respects_in_ipc)

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
  apply (rule update_tcb_context_in_ipc [unfolded fun_upd_def]; fastforce simp: arch_tcb_set_registers_def)
  done

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

lemma cap_insert_ext_integrity_asids_in_ipc[Ipc_AC_assms, wp]:
  "cap_insert_ext src_parent src_slot dest_slot src_p dest_p
   \<lbrace>\<lambda>s. integrity_asids aag subjects x asid st
          (s\<lparr>kheap := \<lambda>a. if a = receiver then kheap st receiver else kheap s a\<rparr>)\<rbrace>"
  by (wpsimp simp: integrity_asids_def)

lemma cap_insert_ext_integrity_hyp_in_ipc[Ipc_AC_assms, wp]:
  "cap_insert_ext src_parent src_slot dest_slot src_p dest_p
   \<lbrace>\<lambda>s. integrity_hyp aag subjects x st
          (s\<lparr>kheap := \<lambda>a. if a = receiver then kheap st receiver else kheap s a\<rparr>)\<rbrace>"
  by (wpsimp simp: integrity_hyp_def)

lemma cap_insert_ext_integrity_fpu_in_ipc[Ipc_AC_assms, wp]:
  "cap_insert_ext src_parent src_slot dest_slot src_p dest_p
   \<lbrace>\<lambda>s. integrity_fpu aag subjects x st
          (s\<lparr>kheap := \<lambda>a. if a = receiver then kheap st receiver else kheap s a\<rparr>)\<rbrace>"
  by (wpsimp simp: integrity_fpu_def)

lemma integrity_asids_kh_updI[Ipc_AC_assms]:
  "integrity_asids_2 aag subjects x asid as as ao ao'
   \<Longrightarrow> integrity_asids_2 aag subjects x asid as as (ao(p := ako)) (ao'(p := ako))"
  by (clarsimp simp: integrity_asids_def opt_map_def)

lemma integrity_hyp_kh_updI[Ipc_AC_assms]:
  "integrity_hyp_2 aag subjects x ms ms as as ao ao'
   \<Longrightarrow> integrity_hyp_2 aag subjects x ms ms as as (ao(p := ako)) (ao'(p := ako))"
  by (simp add: integrity_hyp_def vcpu_integrity_def vcpu_of_state_def opt_map_def)

lemma integrity_fpu_kh_updI[Ipc_AC_assms]:
  "integrity_fpu_2 aag subjects x ms ms kh kh'
   \<Longrightarrow> integrity_fpu_2 aag subjects x ms ms (kh(p := ko)) (kh'(p := ko))"
  by (clarsimp simp: integrity_fpu_def fpu_of_state_def opt_map_def)

declare handle_arch_fault_reply_inv[Ipc_AC_assms]
declare arch_get_sanitise_register_info_inv[Ipc_AC_assms]

end


context is_extended begin interpretation Arch .

lemma list_integ_lift_in_ipc[Ipc_AC_assms]:
  assumes li:
    "\<lbrace>list_integ (cdt_change_allowed aag {pasSubject aag} (cdt st) (tcb_states_of_state st)) st and Q\<rbrace>
     f
     \<lbrace>\<lambda>_. list_integ (cdt_change_allowed aag {pasSubject aag} (cdt st) (tcb_states_of_state st)) st\<rbrace>"
  shows
    "\<lbrace>integrity_tcb_in_ipc aag X receiver epptr ctxt st and Q\<rbrace>
     f
     \<lbrace>\<lambda>_. integrity_tcb_in_ipc aag X receiver epptr ctxt st\<rbrace>"
  apply (unfold integrity_tcb_in_ipc_def integrity_def[abs_def] pool_for_asid_def
                integrity_asids_def integrity_hyp_def integrity_fpu_def)
  apply (simp del: split_paired_All)
  apply (rule hoare_pre)
   apply (simp only: integrity_cdt_list_as_list_integ)
   apply (simp add: tcb_states_of_state_def get_tcb_def)
   apply (wp li[simplified tcb_states_of_state_def get_tcb_def])
  apply (simp only: integrity_cdt_list_as_list_integ)
  apply (clarsimp simp: tcb_states_of_state_def get_tcb_def fun_upd_def)
  done

end


global_interpretation Ipc_AC_2?: Ipc_AC_2
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact Ipc_AC_assms)?)
qed

end
