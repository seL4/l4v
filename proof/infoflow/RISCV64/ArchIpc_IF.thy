(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchIpc_IF
imports Ipc_IF
begin

context Arch begin global_naming RISCV64

named_theorems Ipc_IF_assms

lemma lookup_ipc_buffer_reads_respects[Ipc_IF_assms]:
  "reads_respects aag l (K (aag_can_read aag thread \<or> aag_can_affect aag l thread))
                  (lookup_ipc_buffer is_receiver thread)"
  unfolding lookup_ipc_buffer_def
  by (wp thread_get_reads_respects get_cap_reads_respects | wpc | simp)+

lemma as_user_equiv_but_for_labels[Ipc_IF_assms]:
  "\<lbrace>equiv_but_for_labels aag L st and K (pasObjectAbs aag thread \<in> L)\<rbrace>
   as_user thread f
   \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  unfolding as_user_def
  apply (wp set_object_equiv_but_for_labels | simp add: split_def)+
  apply (blast dest: get_tcb_not_asid_pool_at)
  done

lemma storeWord_equiv_but_for_labels[Ipc_IF_assms]:
  "\<lbrace>\<lambda>ms. equiv_but_for_labels aag L st (s\<lparr>machine_state := ms\<rparr>) \<and>
         for_each_byte_of_word (\<lambda>x. pasObjectAbs aag x \<in> L) p\<rbrace>
   storeWord p v
   \<lbrace>\<lambda>_ ms. equiv_but_for_labels aag L st (s\<lparr>machine_state := ms\<rparr>)\<rbrace>"
  unfolding storeWord_def
  apply (wp modify_wp)
  apply (clarsimp simp: equiv_but_for_labels_def)
  apply (rule states_equiv_forI)
          apply (fastforce intro!: equiv_forI elim!: states_equiv_forE dest: equiv_forD)
         apply (simp add: states_equiv_for_def)
         apply (rule conjI)
          apply (rule equiv_forI)
          apply clarsimp
          apply (drule_tac f=underlying_memory in equiv_forD,fastforce)
          apply (fastforce intro: is_aligned_no_wrap' word_plus_mono_right
                            simp: is_aligned_mask for_each_byte_of_word_def word_size_def upto.simps)
         apply (rule equiv_forI)
         apply clarsimp
         apply (drule_tac f=device_state in equiv_forD,fastforce)
         apply clarsimp
        apply (fastforce elim: states_equiv_forE intro: equiv_forI dest: equiv_forD[where f=cdt])
       apply (fastforce elim: states_equiv_forE intro: equiv_forI dest: equiv_forD[where f=cdt_list])
      apply (fastforce elim: states_equiv_forE intro: equiv_forI dest: equiv_forD[where f=is_original_cap])
     apply (fastforce elim: states_equiv_forE intro: equiv_forI dest: equiv_forD[where f=interrupt_states])
    apply (fastforce elim: states_equiv_forE intro: equiv_forI dest: equiv_forD[where f=interrupt_irq_node])
   apply (fastforce simp: equiv_asids_def equiv_asid_def elim: states_equiv_forE)
  apply (fastforce elim: states_equiv_forE intro: equiv_forI dest: equiv_forD[where f=ready_queues])
  done

lemma set_thread_state_runnable_equiv_but_for_labels[Ipc_IF_assms]:
  "runnable tst
   \<Longrightarrow> \<lbrace>equiv_but_for_labels aag L st and K (pasObjectAbs aag thread \<in> L)\<rbrace>
       set_thread_state thread tst
       \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  unfolding set_thread_state_def
  apply (wpsimp wp: set_object_equiv_but_for_labels[THEN hoare_set_object_weaken_pre]
                    set_thread_state_act_runnable_equiv_but_for_labels)
    apply (wpsimp wp: set_object_wp)+
  apply (fastforce dest: get_tcb_not_asid_pool_at simp: st_tcb_at_def obj_at_def)
  done

lemma set_endpoint_equiv_but_for_labels[Ipc_IF_assms]:
  "\<lbrace>equiv_but_for_labels aag L st and K (pasObjectAbs aag epptr \<in> L)\<rbrace>
   set_endpoint epptr ep
   \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  unfolding set_simple_ko_def
  apply (wp set_object_equiv_but_for_labels get_object_wp)
  apply (clarsimp simp: asid_pool_at_kheap partial_inv_def obj_at_def split: kernel_object.splits)
  done

(* FIXME move *)
lemma conj_imp:
  "\<lbrakk> Q \<longrightarrow> R; P \<longrightarrow> Q; P' \<longrightarrow> Q \<rbrakk> \<Longrightarrow> (P \<longrightarrow> R) \<and> (P' \<longrightarrow> R)"
  by fastforce

(* basically clagged directly from lookup_ipc_buffer_has_auth *)
lemma lookup_ipc_buffer_has_read_auth[Ipc_IF_assms]:
  "\<lbrace>pas_refined aag and valid_objs\<rbrace>
   lookup_ipc_buffer is_receiver thread
   \<lbrace>\<lambda>rv s. ipc_buffer_has_read_auth aag (pasObjectAbs aag thread) rv\<rbrace>"
  apply (rule hoare_pre)
   apply (simp add: lookup_ipc_buffer_def)
   apply (wp get_cap_wp thread_get_wp' | wpc)+
  apply (clarsimp simp: cte_wp_at_caps_of_state ipc_buffer_has_read_auth_def get_tcb_ko_at[symmetric])
  apply (frule caps_of_state_tcb_cap_cases [where idx = "tcb_cnode_index 4"])
   apply (simp add: dom_tcb_cap_cases)
  apply (frule (1) caps_of_state_valid_cap)
  apply (clarsimp simp: vm_read_only_def vm_read_write_def)
  apply (rule_tac Q="AllowRead \<in> xb" in conj_imp)
    apply (clarsimp simp: valid_cap_simps cap_aligned_def)
    apply (rule conjI)
     apply (erule aligned_add_aligned)
      apply (rule is_aligned_andI1)
      apply (drule (1) valid_tcb_objs)
      apply (clarsimp simp: valid_obj_def valid_tcb_def valid_ipc_buffer_cap_def
                     split: if_splits)
     apply (rule order_trans [OF _ pbfs_atleast_pageBits])
     apply (simp add: msg_align_bits pageBits_def)
    apply (drule (1) cap_auth_caps_of_state)
    apply (clarsimp simp: aag_cap_auth_def cap_auth_conferred_def arch_cap_auth_conferred_def
                          vspace_cap_rights_to_auth_def vm_read_only_def)
    apply (drule bspec)
     apply (erule (3) ipcframe_subset_page)
   apply (simp_all)
  done

lemma cptrs_in_ipc_buffer[Ipc_IF_assms]:
  "\<lbrakk> n \<in> set [buffer_cptr_index ..< buffer_cptr_index + unat (mi_extra_caps mi)];
     is_aligned (p :: obj_ref) msg_align_bits;
     buffer_cptr_index + unat (mi_extra_caps mi) < 2 ^ (msg_align_bits - word_size_bits) \<rbrakk>
     \<Longrightarrow> ptr_range (p + of_nat n * of_nat word_size) word_size_bits \<subseteq> ptr_range p msg_align_bits"
  apply (rule ptr_range_subset)
     apply assumption
    apply (simp add: msg_align_bits')
   apply (simp add: msg_align_bits' word_size_bits_def word_bits_def)
  apply (simp add: word_size_def)
  apply (subst upto_enum_step_shift_red[where us=3, simplified])
     apply (simp add: msg_align_bits' word_bits_def word_size_bits_def)+
  done

lemma msg_in_ipc_buffer[Ipc_IF_assms]:
  "\<lbrakk> n = msg_max_length \<or> n < msg_max_length;  is_aligned p msg_align_bits;
     unat (mi_length mi) < 2 ^ (msg_align_bits - word_size_bits) \<rbrakk>
     \<Longrightarrow> ptr_range (p + of_nat n * of_nat word_size) word_size_bits
         \<subseteq> ptr_range (p :: obj_ref) msg_align_bits"
  apply (rule ptr_range_subset)
     apply assumption
    apply (simp add: msg_align_bits')
   apply (simp add: msg_align_bits word_bits_def)
  apply (simp add: word_size_def)
  apply (subst upto_enum_step_shift_red[where us=3, simplified])
     apply (simp add: msg_align_bits word_bits_def)+
  apply (simp add: image_def)
  apply (rule_tac x=n in bexI)
   apply (rule refl)
  apply (auto simp: msg_max_length_def)
  done

lemma arch_derive_cap_reads_respects[Ipc_IF_assms]:
  "reads_respects aag l \<top> (arch_derive_cap cap)"
  unfolding arch_derive_cap_def fun_app_def
  apply (rule equiv_valid_guard_imp)
   apply (wp | wpc)+
  apply (simp)
  done

lemma arch_derive_cap_rev[Ipc_IF_assms]:
  "reads_equiv_valid_inv aag l \<top> (arch_derive_cap cap)"
  unfolding arch_derive_cap_def fun_app_def
  apply (rule equiv_valid_guard_imp)
   apply (wp | wpc)+
  apply (simp)
  done

lemma captransfer_in_ipc_buffer[Ipc_IF_assms]:
  "\<lbrakk> is_aligned (buf :: obj_ref) msg_align_bits; n \<in> {0..2} \<rbrakk>
     \<Longrightarrow> ptr_range (buf + (2 + (of_nat msg_max_length + of_nat msg_max_extra_caps)) * word_size
                                                                                    + n * word_size)
                   word_size_bits
         \<subseteq> ptr_range buf msg_align_bits"
  apply (rule ptr_range_subset)
     apply assumption
    apply (simp add: msg_align_bits')
   apply (simp add: msg_align_bits word_bits_def)
  apply (simp add: word_size_def)
  apply (subst upto_enum_step_shift_red[where us=3, simplified])
     apply (simp add: msg_align_bits word_bits_def)+
  apply (simp add: image_def msg_max_length_def msg_max_extra_caps_def)
  apply (rule_tac x="(125::nat) + unat n"  in bexI)
   apply simp+
  apply (fastforce intro: unat_less_helper word_leq_minus_one_le)
  done

lemma mrs_in_ipc_buffer[Ipc_IF_assms]:
  "\<lbrakk> n \<in> set [length msg_registers + 1 ..< Suc n'];
     is_aligned (buf :: obj_ref) msg_align_bits; n' < 2 ^ (msg_align_bits - word_size_bits) \<rbrakk>
     \<Longrightarrow> ptr_range (buf + of_nat n * of_nat word_size) word_size_bits \<subseteq> ptr_range buf msg_align_bits"
  apply (rule ptr_range_subset)
     apply assumption
    apply (simp add: msg_align_bits')
   apply (simp add: msg_align_bits word_bits_def)
  apply (simp add: word_size_def)
  apply (subst upto_enum_step_shift_red[where us=3, simplified])
     apply (simp add: msg_align_bits word_bits_def word_size_bits_def)+
  apply (simp add: image_def)
  apply (rule_tac x=n in bexI)
   apply (rule refl)
  apply (fastforce split: if_split_asm)
  done

lemma dmo_loadWord_reads_respects[Ipc_IF_assms]:
  "reads_respects aag l (K (for_each_byte_of_word (\<lambda> x. aag_can_read_or_affect aag l x) p))
                  (do_machine_op (loadWord p))"
  apply (rule gen_asm_ev)
  apply (rule use_spec_ev)
  apply (rule spec_equiv_valid_hoist_guard)
  apply (rule do_machine_op_spec_reads_respects)
   apply (simp add: loadWord_def equiv_valid_def2 spec_equiv_valid_def)
   apply (rule_tac R'="\<lambda>rv rv'. for_each_byte_of_word (\<lambda>y. rv y = rv' y) p"
               and Q="\<top>\<top>" and Q'="\<top>\<top>" and P="\<top>" and P'="\<top>" in equiv_valid_2_bind_pre)
        apply (rule_tac R'="(=)" and Q="\<lambda> r s. p && mask 3 = 0" and Q'="\<lambda> r s. p && mask 3 = 0"
                    and P="\<top>" and P'="\<top>" in equiv_valid_2_bind_pre)
             apply (rule return_ev2)
             apply (rule_tac f="word_rcat" in arg_cong)
             apply (fastforce simp: upto.simps is_aligned_mask for_each_byte_of_word_def word_size_def
                             intro: is_aligned_no_wrap' word_plus_mono_right)
            apply (rule assert_ev2[OF refl])
           apply (rule assert_wp)+
         apply simp+
       apply (clarsimp simp: equiv_valid_2_def in_monad for_each_byte_of_word_def)
       apply (fastforce elim: equiv_forD orthD1 simp: ptr_range_def add.commute)
      apply (wp wp_post_taut loadWord_inv | simp)+
  done

lemma complete_signal_reads_respects[Ipc_IF_assms]:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows "reads_respects aag l (K (aag_can_read aag ntfnptr \<or> aag_can_affect aag l ntfnptr))
                        (complete_signal ntfnptr receiver)"
  unfolding complete_signal_def
  by (wp set_simple_ko_reads_respects get_simple_ko_reads_respects as_user_set_register_reads_respects'
      | wpc | simp)+

lemma handle_arch_fault_reply_reads_respects[Ipc_IF_assms, wp]:
  "reads_respects aag l (K (aag_can_read aag thread)) (handle_arch_fault_reply afault thread x y)"
  by (simp add: handle_arch_fault_reply_def, wp)

lemma arch_get_sanitise_register_info_reads_respects[Ipc_IF_assms, wp]:
  "reads_respects aag l \<top> (arch_get_sanitise_register_info t)"
  by wpsimp

declare arch_get_sanitise_register_info_inv[Ipc_IF_assms]

lemma lookup_ipc_buffer_ptr_range'[Ipc_IF_assms]:
  "\<lbrace>valid_objs\<rbrace>
   lookup_ipc_buffer True thread
   \<lbrace>\<lambda>rv s. rv = Some buf' \<longrightarrow> auth_ipc_buffers s thread = ptr_range buf' msg_align_bits\<rbrace>"
  unfolding lookup_ipc_buffer_def
  apply (rule hoare_pre)
   apply (wp get_cap_wp thread_get_wp' | wpc)+
  apply (clarsimp simp: cte_wp_at_caps_of_state ipc_buffer_has_auth_def get_tcb_ko_at [symmetric])
  apply (frule caps_of_state_tcb_cap_cases [where idx = "tcb_cnode_index 4"])
   apply (simp add: dom_tcb_cap_cases)
  apply (clarsimp simp: auth_ipc_buffers_def get_tcb_ko_at [symmetric])
  apply (drule(1) valid_tcb_objs)
  apply (drule get_tcb_SomeD)+
  apply (simp add: vm_read_write_def valid_tcb_def valid_ipc_buffer_cap_def split: bool.splits)
  done

lemma lookup_ipc_buffer_aligned'[Ipc_IF_assms]:
  "\<lbrace>valid_objs\<rbrace>
   lookup_ipc_buffer True thread
   \<lbrace>\<lambda>rv s. rv = Some buf' \<longrightarrow> is_aligned buf' msg_align_bits\<rbrace>"
  apply (insert lookup_ipc_buffer_aligned)
  apply (fastforce simp: valid_def)
  done

lemma handle_arch_fault_reply_globals_equiv[Ipc_IF_assms]:
  "\<lbrace>globals_equiv st and valid_arch_state and (\<lambda>s. thread \<noteq> idle_thread s)\<rbrace>
   handle_arch_fault_reply vmf thread x y
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  by (wpsimp simp: handle_arch_fault_reply_def)+

crunch arch_get_sanitise_register_info, handle_arch_fault_reply
  for valid_global_objs[Ipc_IF_assms, wp]: "valid_global_objs"

crunch handle_arch_fault_reply
  for valid_arch_state[Ipc_IF_assms,wp]: "\<lambda>s :: det_state. valid_arch_state s"

lemma transfer_caps_loop_valid_arch[Ipc_IF_assms]:
  "transfer_caps_loop ep buffer n caps slots mi \<lbrace>valid_arch_state :: det_ext state \<Rightarrow> _\<rbrace>"
  by (wp valid_arch_state_lift_aobj_at_no_caps transfer_caps_loop_aobj_at)

end


global_interpretation Ipc_IF_1?: Ipc_IF_1
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact Ipc_IF_assms)?)
qed


context Arch begin global_naming RISCV64

lemma copy_mrs_reads_respects[Ipc_IF_assms]:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "reads_respects aag (l :: 'a subject_label)
     (K (aag_can_read_or_affect aag l sender \<and> aag_can_read_or_affect_ipc_buffer aag l sbuf
                                             \<and> unat n < 2 ^ (msg_align_bits - word_size_bits)))
     (copy_mrs sender sbuf receiver rbuf n)"
  unfolding copy_mrs_def fun_app_def
  apply (rule gen_asm_ev)
  apply (wp mapM_ev'' store_word_offs_reads_respects load_word_offs_reads_respects
            as_user_set_register_reads_respects' as_user_reads_respects
         | wpc
         | simp add: det_setRegister det_getRegister split del: if_split)+
  apply clarsimp
  apply (rename_tac n')
  apply (subgoal_tac "ptr_range (x + of_nat n' * of_nat word_size) word_size_bits
                      \<subseteq> ptr_range x msg_align_bits")
   apply (simp add: for_each_byte_of_word_def2)
   apply (simp add: aag_can_read_or_affect_ipc_buffer_def)
   apply (erule conjE)
   apply (rule ballI)
   apply (erule bspec)
   apply (erule (1) subsetD[rotated])
  apply (rule ptr_range_subset)
     apply (simp add: aag_can_read_or_affect_ipc_buffer_def)
    apply (simp add: msg_align_bits')
   apply (simp add: msg_align_bits word_bits_def)
  apply (simp add: word_size_def word_size_bits_def)
  apply (subst upto_enum_step_shift_red[where us=3, simplified])
     apply (simp add: msg_align_bits word_bits_def aag_can_read_or_affect_ipc_buffer_def )+
  apply (fastforce simp: image_def)
  done

lemma get_message_info_reads_respects[Ipc_IF_assms]:
  "reads_respects aag (l :: 'a subject_label) (K (aag_can_read_or_affect aag l ptr)) (get_message_info ptr)"
  apply (simp add: get_message_info_def)
  apply (wp as_user_reads_respects | clarsimp simp: getRegister_def)+
  done

lemma do_normal_transfer_reads_respects[Ipc_IF_assms]:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "reads_respects aag (l :: 'a subject_label)
     (pas_refined aag and valid_mdb and valid_objs
                      and K (aag_can_read_or_affect aag l sender \<and>
                             ipc_buffer_has_read_auth aag (pasObjectAbs aag sender) sbuf \<and>
                             ipc_buffer_has_read_auth aag (pasObjectAbs aag receiver) rbuf \<and>
                             (grant \<longrightarrow> (is_subject aag sender \<and> is_subject aag receiver))))
     (do_normal_transfer sender sbuf endpoint badge grant receiver rbuf)"
  apply (cases grant)
   apply (rule gen_asm_ev)
   apply (simp add: do_normal_transfer_def)
   apply (wp copy_mrs_pas_refined get_message_info_rev lookup_extra_caps_rev
             as_user_set_register_reads_respects' set_message_info_reads_respects
             transfer_caps_reads_respects copy_mrs_reads_respects lookup_extra_caps_rev
             lookup_extra_caps_authorised lookup_extra_caps_auth get_message_info_rev
             get_mi_length' get_mi_length validE_E_wp_post_taut
             copy_mrs_cte_wp_at hoare_vcg_ball_lift lec_valid_cap'
             lookup_extra_caps_srcs[simplified ball_conj_distrib,THEN hoare_conjDR1]
             lookup_extra_caps_srcs[simplified ball_conj_distrib,THEN hoare_conjDR2]
          | wpc
          | simp add: det_setRegister ball_conj_distrib)+
   apply (fastforce intro: aag_has_read_auth_can_read_or_affect_ipc_buffer)
  apply (rule gen_asm_ev)
  apply (simp add: do_normal_transfer_def transfer_caps_def)
  apply (wp ev_irrelevant_bind[where f="get_receive_slots receiver rbuf"]
            as_user_set_register_reads_respects'
            set_message_info_reads_respects copy_mrs_reads_respects
            get_message_info_reads_respects get_mi_length
         | wpc
         | simp)+
  apply (auto simp: ipc_buffer_has_read_auth_def aag_can_read_or_affect_ipc_buffer_def
              dest: reads_read_thread_read_pages split: option.splits)
  done

lemma make_arch_fault_msg_reads_respects[Ipc_IF_assms]:
  "reads_respects aag (l :: 'a subject_label) (\<lambda>y. aag_can_read_or_affect aag l sender)
                  (make_arch_fault_msg x4 sender)"
  apply (case_tac x4)
  apply (wp as_user_reads_respects | simp add: det_getRegister det_getRestartPC)+
  done

lemma set_mrs_equiv_but_for_labels[Ipc_IF_assms]:
  "\<lbrace>equiv_but_for_labels (aag :: 'a subject_label PAS) L st and
    K (pasObjectAbs aag thread \<in> L \<and>
       (case buf of (Some buf') \<Rightarrow> is_aligned buf' msg_align_bits \<and>
                                   (\<forall>x \<in> ptr_range buf' msg_align_bits. pasObjectAbs aag x \<in> L)
                            | _ \<Rightarrow> True))\<rbrace>
   set_mrs thread buf msgs
   \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  unfolding set_mrs_def
  apply (wp | wpc)+
        apply (subst zipWithM_x_mapM_x)
        apply (rule_tac Q'="\<lambda>_. equiv_but_for_labels aag L st and K (pasObjectAbs aag thread \<in> L  \<and>
                               (case buf of (Some buf') \<Rightarrow> is_aligned buf' msg_align_bits \<and>
                                                           (\<forall>x \<in> ptr_range buf' msg_align_bits.
                                                              pasObjectAbs aag x \<in> L)
                                                    | _ \<Rightarrow> True))" in hoare_strengthen_post)
         apply (wp mapM_x_wp' store_word_offs_equiv_but_for_labels | simp add: split_def)+
         apply (case_tac x, clarsimp split: if_split_asm elim!: in_set_zipE)
         apply (clarsimp simp: for_each_byte_of_word_def)
         apply (erule bspec)
         apply (clarsimp simp: ptr_range_def)
         apply (rule conjI)
          apply (erule order_trans[rotated])
          apply (erule is_aligned_no_wrap')
          apply (rule mul_word_size_lt_msg_align_bits_ofnat)
          apply (fastforce simp: msg_max_length_def msg_align_bits')
         apply (erule order_trans)
         apply (subst p_assoc_help)
         apply (simp add: add.assoc)
         apply (rule word_plus_mono_right)
          apply (rule word_less_sub_1)
          apply (rule_tac y="of_nat msg_max_length * of_nat word_size + (word_size - 1)"
                       in le_less_trans)
           apply (rule word_plus_mono_left)
            apply (rule word_mult_le_mono1)
              apply (erule disjE)
               apply (rule word_of_nat_le)
               apply (simp add: msg_max_length_def)
              apply clarsimp
              apply (rule word_of_nat_le)
              apply (simp add: msg_max_length_def)
             apply (simp add: word_size_def)
            apply (simp add: msg_max_length_def word_size_def)
           apply (simp add: msg_max_length_def word_size_def)
          apply (rule mul_add_word_size_lt_msg_align_bits_ofnat)
           apply (simp add: msg_max_length_def msg_align_bits')
          apply (simp add: word_size_def)
         apply (erule is_aligned_no_overflow')
        apply simp
       apply (wp set_object_equiv_but_for_labels hoare_vcg_all_lift hoare_weak_lift_imp | simp)+
  apply (fastforce dest: get_tcb_not_asid_pool_at)+
  done

lemma set_mrs_reads_respects'[Ipc_IF_assms]:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
    "reads_respects aag (l :: 'a subject_label)
       (K (ipc_buffer_has_auth aag thread buf \<and>
           (case buf of (Some buf') \<Rightarrow> is_aligned buf' msg_align_bits | _ \<Rightarrow> True)))
       (set_mrs thread buf msgs)"
  apply (case_tac "aag_can_read_or_affect aag l thread")
   apply ((wp equiv_valid_guard_imp[OF set_mrs_reads_respects] | simp)+)[1]
  apply (rule gen_asm_ev)
  apply (simp add: equiv_valid_def2)
  apply (rule equiv_valid_rv_guard_imp)
   apply (case_tac buf)
    apply (rule_tac Q="\<top>" and P="\<top>" and L="{pasObjectAbs aag thread}" in ev_invisible[OF domains_distinct])
      apply (clarsimp simp: labels_are_invisible_def)
     apply (rule modifies_at_mostI)
     apply (simp add: set_mrs_def)
     apply ((wp set_object_equiv_but_for_labels | simp | auto dest: get_tcb_not_asid_pool_at)+)[1]
    apply (simp)
    apply (rule set_mrs_ret_eq)
   apply (rename_tac buf')
   apply (rule_tac Q="\<top>" and L="{pasObjectAbs aag thread} \<union> (pasObjectAbs aag)
                                 ` (ptr_range buf' msg_align_bits)"
                in ev_invisible[OF domains_distinct])
     apply (auto simp: labels_are_invisible_def ipc_buffer_has_auth_def
                 dest: reads_read_page_read_thread simp: aag_can_affect_label_def)[1]
    apply (rule modifies_at_mostI)
    apply (wp set_mrs_equiv_but_for_labels | simp)+
   apply (rule set_mrs_ret_eq)
  by simp

end


global_interpretation Ipc_IF_2?: Ipc_IF_2
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact Ipc_IF_assms)?)
qed

end
