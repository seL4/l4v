(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchIpc_AI
imports Ipc_AI
begin

context Arch begin arch_global_naming

named_theorems Ipc_AI_1_assms

lemma cap_asid_PageCap_None[simp]:
  "cap_asid (ArchObjectCap (FrameCap r R pgsz dev None)) = None"
  by (simp add: cap_asid_def)

lemma arch_derive_cap_is_derived:
  "\<lbrace>\<lambda>s. cte_wp_at (\<lambda>cap . cap_master_cap cap =
                          cap_master_cap (ArchObjectCap c') \<and>
                          cap_aligned cap \<and>
                          cap_asid cap = cap_asid (ArchObjectCap c') \<and>
                          vs_cap_ref cap = vs_cap_ref (ArchObjectCap c')) p s\<rbrace>
     arch_derive_cap c'
   \<lbrace>\<lambda>rv s. cte_wp_at (is_derived (cdt s) p rv) p s\<rbrace>, -"
  unfolding arch_derive_cap_def
  apply(cases c', simp_all add: is_cap_simps cap_master_cap_def)
      apply((wp throwError_validE_R
             | clarsimp simp: is_derived_def
                              is_cap_simps cap_master_cap_def
                              cap_aligned_def is_aligned_no_overflow is_pt_cap_def
                              cap_asid_def vs_cap_ref_def vs_cap_ref_arch_def
             | erule cte_wp_at_weakenE
             | simp split: arch_cap.split_asm cap.split_asm option.splits
             | rule conjI)+)
  done

lemma derive_cap_is_derived [Ipc_AI_1_assms]:
  "\<lbrace>\<lambda>s. c'\<noteq> cap.NullCap \<longrightarrow> cte_wp_at (\<lambda>cap. cap_master_cap cap = cap_master_cap c'
                     \<and> (cap_badge cap, cap_badge c') \<in> capBadge_ordering False
                     \<and> cap_asid cap = cap_asid c'
                     \<and> vs_cap_ref cap = vs_cap_ref c') slot s
       \<and> valid_objs s\<rbrace>
  derive_cap slot c'
  \<lbrace>\<lambda>rv s. rv \<noteq> cap.NullCap \<longrightarrow>
          cte_wp_at (is_derived (cdt s) slot rv) slot s\<rbrace>, -"
  unfolding derive_cap_def
  apply (cases c', simp_all add: is_cap_simps)
          apply ((wp ensure_no_children_wp
                    | clarsimp simp: is_derived_def is_cap_simps
                                     cap_master_cap_def bits_of_def
                                     same_object_as_def is_pt_cap_def
                                     cap_asid_def
                    | fold validE_R_def
                    | erule cte_wp_at_weakenE
                    | simp split: cap.split_asm)+)[11]
  apply(wp hoare_drop_imps arch_derive_cap_is_derived)
  apply(clarify, drule cte_wp_at_norm, clarify)
  apply(frule(1) cte_wp_at_valid_objs_valid_cap)
  apply(erule cte_wp_at_weakenE)
  apply(clarsimp simp: valid_cap_def)
  done

end

interpretation Ipc_AI?: Ipc_AI
proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact Ipc_AI_1_assms)?)
qed

context Arch begin arch_global_naming

named_theorems Ipc_AI_2_assms

lemma is_derived_cap_rights [simp, Ipc_AI_2_assms]:
  "is_derived m p (cap_rights_update R c) = is_derived m p c"
  apply (rule ext)
  apply (simp add: cap_rights_update_def is_derived_def is_cap_simps)
  apply (case_tac x, simp_all)
  by (auto simp: cap_master_cap_def bits_of_def is_cap_simps
                     vs_cap_ref_def is_frame_cap_def
                     acap_rights_update_def is_pt_cap_def
           cong: arch_cap.case_cong
           split: arch_cap.split cap.split bool.splits)


lemma data_to_message_info_valid [Ipc_AI_2_assms]:
  "valid_message_info (data_to_message_info w)"
  by (simp add: valid_message_info_def data_to_message_info_def  word_and_le1 msg_max_length_def
                msg_max_extra_caps_def Let_def not_less mask_def)

lemma get_extra_cptrs_length[wp, Ipc_AI_2_assms]:
  "\<lbrace>\<lambda>s . valid_message_info mi\<rbrace>
   get_extra_cptrs buf mi
   \<lbrace>\<lambda>rv s. length rv \<le> msg_max_extra_caps\<rbrace>"
  apply (cases buf)
   apply (simp, wp, simp)
  apply (simp add: msg_max_length_def)
  apply (subst hoare_liftM_subst, simp add: o_def)
  apply (rule hoare_pre)
   apply (rule mapM_length, simp)
  apply (clarsimp simp: valid_message_info_def msg_max_extra_caps_def
                        word_le_nat_alt
                 intro: length_upt)
  done

lemma cap_asid_rights_update [simp, Ipc_AI_2_assms]:
  "cap_asid (cap_rights_update R c) = cap_asid c"
  by (simp add: cap_rights_update_def acap_rights_update_def cap_asid_def
         split: cap.splits arch_cap.splits)

lemma cap_rights_update_vs_cap_ref[simp, Ipc_AI_2_assms]:
  "vs_cap_ref (cap_rights_update rs cap) = vs_cap_ref cap"
  by (simp add: vs_cap_ref_def vs_cap_ref_arch_def cap_rights_update_def acap_rights_update_def
         split: cap.split arch_cap.split)

lemma is_derived_cap_rights2[simp, Ipc_AI_2_assms]:
  "is_derived m p c (cap_rights_update R c') = is_derived m p c c'"
  apply (case_tac c'; simp add: cap_rights_update_def)
     apply (clarsimp simp: is_derived_def is_cap_simps cap_master_cap_def vs_cap_ref_def
                    split: cap.splits)+
  apply (rename_tac acap1 acap2)
  apply (case_tac acap1)
  by (auto simp: acap_rights_update_def)

lemma cap_range_update [simp, Ipc_AI_2_assms]:
  "cap_range (cap_rights_update R cap) = cap_range cap"
  by (simp add: cap_range_def cap_rights_update_def acap_rights_update_def
         split: cap.splits arch_cap.splits)

lemma derive_cap_idle[wp, Ipc_AI_2_assms]:
  "\<lbrace>\<lambda>s. global_refs s \<inter> cap_range cap = {}\<rbrace>
   derive_cap slot cap
  \<lbrace>\<lambda>c s. global_refs s \<inter> cap_range c = {}\<rbrace>, -"
  apply (simp add: derive_cap_def)
  apply (rule hoare_pre)
   apply (wpc| wp | simp add: arch_derive_cap_def)+
  apply (case_tac cap, simp_all add: cap_range_def)
  apply (rename_tac arch_cap)
  apply (case_tac arch_cap, simp_all)
  done

lemma arch_derive_cap_objrefs_iszombie [Ipc_AI_2_assms]:
  "\<lbrace>\<lambda>s . P (set_option (aobj_ref cap)) False s\<rbrace>
     arch_derive_cap cap
   \<lbrace>\<lambda>rv s. rv \<noteq> NullCap \<longrightarrow> P (obj_refs rv) (is_zombie rv) s\<rbrace>,-"
  apply(cases cap, simp_all add: is_zombie_def arch_derive_cap_def)
      apply(rule hoare_pre, wpsimp+)+
  done

lemma obj_refs_remove_rights[simp, Ipc_AI_2_assms]:
  "obj_refs (remove_rights rs cap) = obj_refs cap"
  by (auto simp add: remove_rights_def cap_rights_update_def
                acap_rights_update_def
         split: cap.splits arch_cap.splits bool.splits)

lemma storeWord_um_inv:
  "\<lbrace>\<lambda>s. underlying_memory s = um\<rbrace>
   storeWord a v
   \<lbrace>\<lambda>_ s. is_aligned a 3 \<and> x \<in> {a,a+1,a+2,a+3,a+4,a+5,a+6,a+7} \<or> underlying_memory s x = um x\<rbrace>"
  by (wpsimp simp: upto.simps storeWord_def is_aligned_mask)

lemma store_word_offs_vms[wp, Ipc_AI_2_assms]:
  "\<lbrace>valid_machine_state\<rbrace> store_word_offs ptr offs v \<lbrace>\<lambda>_. valid_machine_state\<rbrace>"
proof -
  have aligned_offset_ignore:
    "\<And>(l::machine_word) (p::machine_word) sz. l<8 \<Longrightarrow> p && mask 3 = 0 \<Longrightarrow>
       p+l && ~~ mask (pageBitsForSize sz) = p && ~~ mask (pageBitsForSize sz)"
  proof -
    fix l::machine_word and p::machine_word and sz
    assume al: "p && mask 3 = 0"
    assume "l < 8" hence less: "l<2^3" by simp
    have le: "3 \<le> pageBitsForSize sz" by (case_tac sz; simp add: bit_simps)
    show "?thesis l p sz"
      by (rule is_aligned_add_helper[simplified is_aligned_mask,
          THEN conjunct2, THEN mask_out_first_mask_some,
          where n=3, OF al less le])
  qed

  show ?thesis
    apply (simp add: valid_machine_state_def store_word_offs_def
                     do_machine_op_def split_def)
    apply wp
    apply clarsimp
    apply (drule_tac use_valid)
    apply (rule_tac x=p in storeWord_um_inv, simp+)
    apply (drule_tac x=p in spec)
    apply (erule disjE, simp)
    apply (erule disjE, simp_all)
    apply (erule conjE)
    apply (erule disjE, simp)
    apply (simp add: in_user_frame_def word_size_def)
    apply (erule exEI)
    apply (subgoal_tac "(ptr + of_nat offs * 8) && ~~ mask (pageBitsForSize x) =
                        p && ~~ mask (pageBitsForSize x)", simp)
    apply (simp only: is_aligned_mask[of _ 3])
    apply (elim disjE, simp_all)
    apply (rule aligned_offset_ignore[symmetric], simp+)+
    done
qed

lemma is_zombie_update_cap_data[simp, Ipc_AI_2_assms]:
  "is_zombie (update_cap_data P data cap) = is_zombie cap"
  by (simp add: update_cap_data_closedform arch_update_cap_data_def is_zombie_def
         split: cap.splits)

lemma valid_msg_length_strengthen [Ipc_AI_2_assms]:
  "valid_message_info mi \<longrightarrow> unat (mi_length mi) \<le> msg_max_length"
  apply (clarsimp simp: valid_message_info_def)
  apply (subgoal_tac "unat (mi_length mi) \<le> unat (of_nat msg_max_length :: machine_word)")
   apply (clarsimp simp: unat_of_nat msg_max_length_def)
  apply (clarsimp simp: un_ui_le word_le_def)
  done

lemma copy_mrs_in_user_frame[wp, Ipc_AI_2_assms]:
  "\<lbrace>in_user_frame p\<rbrace> copy_mrs t buf t' buf' n \<lbrace>\<lambda>rv. in_user_frame p\<rbrace>"
  by (simp add: in_user_frame_def) (wp hoare_vcg_ex_lift)

lemma as_user_getRestart_inv[wp]:
  "as_user t getRestartPC \<lbrace>P\<rbrace>"
  by (simp add: getRestartPC_def, rule user_getreg_inv)

lemma make_arch_fault_msg_inv[wp, Ipc_AI_2_assms]:
  "make_arch_fault_msg ft t \<lbrace>P\<rbrace>"
  by (cases ft; wpsimp)

lemma make_fault_msg_inv[wp, Ipc_AI_2_assms]:
  "make_fault_msg ft t \<lbrace>P\<rbrace>"
  by (cases ft; wpsimp wp: as_user_inv getRestartPC_inv mapM_wp' split_del: if_split)

lemma do_fault_transfer_invs[wp, Ipc_AI_2_assms]:
  "\<lbrace>invs and tcb_at receiver\<rbrace>
      do_fault_transfer badge sender receiver recv_buf
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (simp add: do_fault_transfer_def split_def | wp
    | clarsimp split: option.split)+

lemma lookup_ipc_buffer_in_user_frame[wp, Ipc_AI_2_assms]:
  "\<lbrace>valid_objs and tcb_at t\<rbrace> lookup_ipc_buffer b t
   \<lbrace>case_option (\<lambda>_. True) in_user_frame\<rbrace>"
  apply (simp add: lookup_ipc_buffer_def)
  apply (wp get_cap_wp thread_get_wp | wpc | simp)+
  apply (clarsimp simp add: obj_at_def is_tcb)
  apply (rename_tac p R sz dev m)
  apply (subgoal_tac "in_user_frame (p + (tcb_ipc_buffer tcb && mask (pageBitsForSize sz))) s",
         simp)
  apply (frule (1) cte_wp_valid_cap)
  apply (clarsimp simp: valid_cap_def cap_aligned_def in_user_frame_def)
  apply (thin_tac "case_option a b c" for a b c)
  apply (rule_tac x=sz in exI)
  apply (subst is_aligned_add_helper[THEN conjunct2])
    apply simp
   apply (rule and_mask_less')
   apply (rule pageBitsForSize_bounded[unfolded word_bits_def])
  apply simp
  done

lemma transfer_caps_loop_cte_wp_at:
  assumes imp: "\<And>cap. P cap \<Longrightarrow> \<not> is_untyped_cap cap"
  shows "\<lbrace>cte_wp_at P sl and K (sl \<notin> set slots) and (\<lambda>s. \<forall>x \<in> set slots. cte_at x s)\<rbrace>
   transfer_caps_loop ep buffer n caps slots mi
   \<lbrace>\<lambda>rv. cte_wp_at P sl\<rbrace>"
  apply (induct caps arbitrary: slots n mi)
   apply (simp, wp, simp)
  apply (clarsimp simp: Let_def split_def whenE_def
                  cong: if_cong list.case_cong
             split del: if_split)
  apply (rule hoare_pre)
   apply (wp hoare_vcg_const_imp_lift hoare_vcg_const_Ball_lift
              derive_cap_is_derived_foo
             hoare_drop_imps
        | assumption | simp split del: if_split)+
      apply (wp hoare_vcg_conj_lift cap_insert_weak_cte_wp_at2)
       apply (erule imp)
      by (wp hoare_vcg_ball_lift
             | clarsimp simp: is_cap_simps split del:if_split
             | unfold derive_cap_def arch_derive_cap_def
             | wpc
             | rule conjI
             | case_tac slots)+

lemma transfer_caps_tcb_caps:
  fixes P t ref mi caps ep receiver recv_buf
  assumes imp: "\<And>c. P c \<Longrightarrow> \<not> is_untyped_cap c"
  shows
  "\<lbrace>valid_objs and cte_wp_at P (t, ref) and tcb_at t\<rbrace>
     transfer_caps mi caps ep receiver recv_buf
   \<lbrace>\<lambda>rv. cte_wp_at P (t, ref)\<rbrace>"
  apply (simp add: transfer_caps_def)
  apply (wp hoare_vcg_const_Ball_lift hoare_vcg_const_imp_lift
            transfer_caps_loop_cte_wp_at
         | wpc | simp)+
    apply (erule imp)
   apply (wp hoare_vcg_conj_lift hoare_vcg_const_imp_lift hoare_vcg_all_lift)
    apply (rule_tac Q'="\<lambda>rv s. (\<forall>x\<in>set rv. real_cte_at x s) \<and> cte_wp_at P (t, ref) s \<and> tcb_at t s"
                    in hoare_strengthen_post)
     apply (wp get_rs_real_cte_at)
    apply clarsimp
    apply (drule(1) bspec)
    apply (clarsimp simp:obj_at_def is_tcb is_cap_table)
   apply (rule hoare_post_imp)
    apply (rule_tac Q="\<lambda>x. real_cte_at x s" in ballEI, assumption)
    apply (erule real_cte_at_cte)
   apply (rule get_rs_real_cte_at)
  apply clarsimp
 done

lemma transfer_caps_non_null_cte_wp_at:
  assumes imp: "\<And>c. P c \<Longrightarrow> \<not> is_untyped_cap c"
  shows  "\<lbrace>valid_objs and cte_wp_at (P and ((\<noteq>) cap.NullCap)) ptr\<rbrace>
     transfer_caps mi caps ep receiver recv_buf
   \<lbrace>\<lambda>_. cte_wp_at (P and ((\<noteq>) cap.NullCap)) ptr\<rbrace>"
  unfolding transfer_caps_def
  apply simp
  apply (rule hoare_pre)
   apply (wp hoare_vcg_ball_lift transfer_caps_loop_cte_wp_at hoare_weak_lift_imp
     | wpc | clarsimp simp:imp)+
   apply (rule hoare_strengthen_post
            [where Q'="\<lambda>rv s'. (cte_wp_at ((\<noteq>) cap.NullCap) ptr) s'
                      \<and> (\<forall>x\<in>set rv. cte_wp_at ((=) cap.NullCap) x s')",
             rotated])
    apply (clarsimp)
    apply  (rule conjI)
     apply (erule contrapos_pn)
     apply (drule_tac x=ptr in bspec, assumption)
     apply (clarsimp elim!: cte_wp_at_orth)
    apply (rule ballI)
    apply (drule(1) bspec)
    apply (erule cte_wp_cte_at)
   apply (wp)
  apply (auto simp: cte_wp_at_caps_of_state)
  done

crunch do_fault_transfer
  for cte_wp_at[wp,Ipc_AI_2_assms]: "cte_wp_at P p"

lemma do_normal_transfer_non_null_cte_wp_at [Ipc_AI_2_assms]:
  assumes imp: "\<And>c. P c \<Longrightarrow> \<not> is_untyped_cap c"
  shows  "\<lbrace>valid_objs and cte_wp_at (P and ((\<noteq>) cap.NullCap)) ptr\<rbrace>
   do_normal_transfer st send_buffer ep b gr rt recv_buffer
   \<lbrace>\<lambda>_. cte_wp_at (P and ((\<noteq>) cap.NullCap)) ptr\<rbrace>"
  unfolding do_normal_transfer_def
  apply simp
  apply (wp transfer_caps_non_null_cte_wp_at
    | clarsimp simp:imp)+
  done

lemma is_derived_ReplyCap [simp, Ipc_AI_2_assms]:
  "\<And>m p R. is_derived m p (cap.ReplyCap t False R) = (\<lambda>c. is_master_reply_cap c \<and> obj_ref_of c = t)"
  apply (subst fun_eq_iff)
  apply clarsimp
  apply (case_tac x, simp_all add: is_derived_def is_cap_simps
                                   cap_master_cap_def conj_comms is_pt_cap_def
                                   vs_cap_ref_def)
  done

lemma do_normal_transfer_tcb_caps:
  assumes imp: "\<And>c. P c \<Longrightarrow> \<not> is_untyped_cap c"
  shows
  "\<lbrace>valid_objs and cte_wp_at P (t, ref) and tcb_at t\<rbrace>
   do_normal_transfer st sb ep badge grant rt rb
   \<lbrace>\<lambda>rv. cte_wp_at P (t, ref)\<rbrace>"
  apply (simp add: do_normal_transfer_def)
  apply (rule hoare_pre)
   apply (wp hoare_drop_imps transfer_caps_tcb_caps
     | simp add:imp)+
  done

lemma do_ipc_transfer_tcb_caps [Ipc_AI_2_assms]:
  assumes imp: "\<And>c. P c \<Longrightarrow> \<not> is_untyped_cap c"
  shows
  "\<lbrace>valid_objs and cte_wp_at P (t, ref) and tcb_at t\<rbrace>
   do_ipc_transfer st ep b gr rt
   \<lbrace>\<lambda>rv. cte_wp_at P (t, ref)\<rbrace>"
  apply (simp add: do_ipc_transfer_def)
  apply (rule hoare_pre)
  apply (wp do_normal_transfer_tcb_caps hoare_drop_imps
       | wpc | simp add:imp)+
  done

lemma setup_caller_cap_valid_global_objs[wp, Ipc_AI_2_assms]:
  "\<lbrace>valid_global_objs\<rbrace> setup_caller_cap send recv grant \<lbrace>\<lambda>rv. valid_global_objs\<rbrace>"
  apply (simp add: valid_global_objs_def)
  unfolding setup_caller_cap_def
   apply (wp sts_obj_at_impossible | simp add: tcb_not_empty_table)+
  done

crunch handle_arch_fault_reply, arch_get_sanitise_register_info
  for inv[Ipc_AI_2_assms]: P

lemma transfer_caps_loop_valid_vspace_objs[wp, Ipc_AI_2_assms]:
  "\<lbrace>valid_vspace_objs\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. valid_vspace_objs\<rbrace>"
  apply (induct caps arbitrary: slots n mi, simp)
  apply (clarsimp simp: Let_def split_def whenE_def
                  cong: if_cong list.case_cong
             split del: if_split)
  apply (rule hoare_pre)
   apply (wp hoare_vcg_const_imp_lift hoare_vcg_const_Ball_lift
              derive_cap_is_derived_foo
             hoare_drop_imps
        | assumption | simp split del: if_split)+
  done

crunch  make_arch_fault_msg
  for aligned[wp, Ipc_AI_2_assms]: "pspace_aligned"
crunch  make_arch_fault_msg
  for distinct[wp, Ipc_AI_2_assms]: "pspace_distinct"
crunch  make_arch_fault_msg
  for vmdb[wp, Ipc_AI_2_assms]: "valid_mdb"
crunch  make_arch_fault_msg
  for ifunsafe[wp, Ipc_AI_2_assms]: "if_unsafe_then_cap"
crunch  make_arch_fault_msg
  for iflive[wp, Ipc_AI_2_assms]: "if_live_then_nonz_cap"
crunch  make_arch_fault_msg
  for state_refs_of[wp, Ipc_AI_2_assms]: "\<lambda>s. P (state_refs_of s)"
crunch  make_arch_fault_msg
  for ct[wp, Ipc_AI_2_assms]: "cur_tcb"
crunch  make_arch_fault_msg
  for zombies[wp, Ipc_AI_2_assms]: "zombies_final"
crunch  make_arch_fault_msg
  for it[wp, Ipc_AI_2_assms]: "\<lambda>s. P (idle_thread s)"
crunch  make_arch_fault_msg
  for valid_globals[wp, Ipc_AI_2_assms]: "valid_global_refs"
crunch  make_arch_fault_msg
  for reply_masters[wp, Ipc_AI_2_assms]: "valid_reply_masters"
crunch  make_arch_fault_msg
  for valid_idle[wp, Ipc_AI_2_assms]: "valid_idle"
crunch  make_arch_fault_msg
  for arch[wp, Ipc_AI_2_assms]: "\<lambda>s. P (arch_state s)"
crunch  make_arch_fault_msg
  for typ_at[wp, Ipc_AI_2_assms]: "\<lambda>s. P (typ_at T p s)"
crunch  make_arch_fault_msg
  for irq_node[wp, Ipc_AI_2_assms]: "\<lambda>s. P (interrupt_irq_node s)"
crunch  make_arch_fault_msg
  for valid_reply[wp, Ipc_AI_2_assms]: "valid_reply_caps"
crunch  make_arch_fault_msg
  for irq_handlers[wp, Ipc_AI_2_assms]: "valid_irq_handlers"
crunch  make_arch_fault_msg
  for vspace_objs[wp, Ipc_AI_2_assms]: "valid_vspace_objs"
crunch  make_arch_fault_msg
  for global_objs[wp, Ipc_AI_2_assms]: "valid_global_objs"
crunch  make_arch_fault_msg
  for global_vspace_mapping[wp, Ipc_AI_2_assms]: "valid_global_vspace_mappings"
crunch  make_arch_fault_msg
  for arch_caps[wp, Ipc_AI_2_assms]: "valid_arch_caps"
crunch  make_arch_fault_msg
  for v_ker_map[wp, Ipc_AI_2_assms]: "valid_kernel_mappings"
crunch  make_arch_fault_msg
  for eq_ker_map[wp, Ipc_AI_2_assms]: "equal_kernel_mappings"
crunch  make_arch_fault_msg
  for asid_map[wp, Ipc_AI_2_assms]: "valid_asid_map"
crunch  make_arch_fault_msg
  for only_idle[wp, Ipc_AI_2_assms]: "only_idle"
crunch  make_arch_fault_msg
  for pspace_in_kernel_window[wp, Ipc_AI_2_assms]: "pspace_in_kernel_window"
crunch  make_arch_fault_msg
  for cap_refs_in_kernel_window[wp, Ipc_AI_2_assms]: "cap_refs_in_kernel_window"
crunch  make_arch_fault_msg
  for valid_objs[wp, Ipc_AI_2_assms]: "valid_objs"
crunch  make_arch_fault_msg
  for valid_ioc[wp, Ipc_AI_2_assms]: "valid_ioc"
crunch  make_arch_fault_msg
  for pred_tcb[wp, Ipc_AI_2_assms]: "pred_tcb_at proj P t"
crunch  make_arch_fault_msg
  for cap_to[wp, Ipc_AI_2_assms]: "ex_nonz_cap_to p"

crunch  make_arch_fault_msg
  for obj_at[wp, Ipc_AI_2_assms]: "\<lambda>s. P (obj_at P' pd s)"
  (wp: as_user_inv getRestartPC_inv mapM_wp'  simp: getRegister_def)

crunch make_arch_fault_msg
  for vms[wp, Ipc_AI_2_assms]: valid_machine_state
  (wp: as_user_inv getRestartPC_inv mapM_wp'  simp: getRegister_def ignore: do_machine_op)

crunch make_arch_fault_msg
  for valid_irq_states[wp, Ipc_AI_2_assms]: "valid_irq_states"
  (wp: as_user_inv getRestartPC_inv mapM_wp'  simp: getRegister_def ignore: do_machine_op)

crunch make_arch_fault_msg
  for cap_refs_respects_device_region[wp, Ipc_AI_2_assms]: "cap_refs_respects_device_region"
  (wp: as_user_inv getRestartPC_inv mapM_wp'  simp: getRegister_def ignore: do_machine_op)

lemma setup_caller_cap_aobj_at:
  "arch_obj_pred P' \<Longrightarrow>
  \<lbrace>\<lambda>s. P (obj_at P' pd s)\<rbrace> setup_caller_cap st rt grant \<lbrace>\<lambda>r s. P (obj_at P' pd s)\<rbrace>"
  unfolding setup_caller_cap_def
  by (wpsimp wp: cap_insert_aobj_at sts.aobj_at)

lemma setup_caller_cap_valid_arch[Ipc_AI_2_assms, wp]:
  "setup_caller_cap st rt grant \<lbrace>valid_arch_state\<rbrace>"
  by (wpsimp wp: valid_arch_state_lift_aobj_at_no_caps[rotated -1] setup_caller_cap_tcb_at setup_caller_cap_aobj_at)

lemma transfer_caps_loop_valid_arch[Ipc_AI_2_assms]:
  "\<And>slots caps ep buffer n mi.
    \<lbrace>valid_arch_state and valid_objs and valid_mdb and K (distinct slots)
         and (\<lambda>s. \<forall>x \<in> set slots. real_cte_at x s \<and> cte_wp_at (\<lambda>cap. cap = cap.NullCap) x s)
         and transfer_caps_srcs caps\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  by (wpsimp wp: valid_arch_state_lift_aobj_at_no_caps transfer_caps_loop_typ_ats transfer_caps_loop_aobj_at)

end

interpretation Ipc_AI?: Ipc_AI_2
proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact Ipc_AI_2_assms)?)
qed

context Arch begin arch_global_naming

named_theorems Ipc_AI_3_assms

crunch make_fault_msg
  for pspace_respects_device_region[wp]: "pspace_respects_device_region"
  (wp: as_user_inv getRestartPC_inv mapM_wp'  simp: getRegister_def ignore: do_machine_op)

crunch do_ipc_transfer
  for pspace_respects_device_region[wp, Ipc_AI_3_assms]: "pspace_respects_device_region"
  (wp: crunch_wps ignore: const_on_failure simp: crunch_simps)

lemma do_ipc_transfer_respects_device_region[Ipc_AI_3_assms]:
  "\<lbrace>cap_refs_respects_device_region and tcb_at t and  valid_objs and valid_mdb\<rbrace>
   do_ipc_transfer t ep bg grt r
   \<lbrace>\<lambda>rv. cap_refs_respects_device_region\<rbrace>"
  apply (wpsimp simp: do_ipc_transfer_def do_normal_transfer_def transfer_caps_def bind_assoc
                wp: hoare_vcg_all_lift hoare_drop_imps)+
         apply (simp only: ball_conj_distrib[where P="\<lambda>x. real_cte_at x s" for s])
         apply (wpsimp wp: get_rs_cte_at2 thread_get_wp hoare_weak_lift_imp grs_distinct
                           hoare_vcg_ball_lift hoare_vcg_all_lift hoare_vcg_conj_lift
                       simp: obj_at_def is_tcb_def)+
   apply (simp split: kernel_object.split_asm)
   done

lemma set_mrs_state_hyp_refs_of[wp]:
  "\<lbrace>\<lambda> s. P (state_hyp_refs_of s)\<rbrace> set_mrs thread buf msgs \<lbrace>\<lambda>_ s. P (state_hyp_refs_of s)\<rbrace>"
  by (wp set_mrs_thread_set_dmo thread_set_hyp_refs_trivial | simp)+

crunch do_ipc_transfer
  for state_hyp_refs_of[wp, Ipc_AI_3_assms]: "\<lambda> s. P (state_hyp_refs_of s)"
  (wp: crunch_wps simp: zipWithM_x_mapM)

lemma arch_derive_cap_untyped:
  "\<lbrace>\<lambda>s. P (untyped_range (ArchObjectCap cap))\<rbrace>
   arch_derive_cap cap
   \<lbrace>\<lambda>rv s. rv \<noteq> cap.NullCap \<longrightarrow> P (untyped_range rv)\<rbrace>,-"
  by (wpsimp simp: arch_derive_cap_def)

lemma valid_arch_mdb_cap_swap:
  "\<And>s cap capb.
       \<lbrakk>valid_arch_mdb (is_original_cap s) (caps_of_state s);
        weak_derived c cap; caps_of_state s a = Some cap;
        is_untyped_cap cap \<longrightarrow> cap = c; a \<noteq> b;
        weak_derived c' capb; caps_of_state s b = Some capb\<rbrakk>
       \<Longrightarrow> valid_arch_mdb
            ((is_original_cap s)
             (a := is_original_cap s b, b := is_original_cap s a))
            ((caps_of_state s)(a \<mapsto> c', b \<mapsto> c))"
  by (auto simp: valid_arch_mdb_def)

lemma do_ipc_transfer_valid_arch[Ipc_AI_3_assms]:
  "\<lbrace>valid_arch_state and valid_objs and valid_mdb \<rbrace>
   do_ipc_transfer s ep bg grt r
   \<lbrace>\<lambda>rv. valid_arch_state\<rbrace>"
  by (wpsimp wp: valid_arch_state_lift_aobj_at_no_caps dit_tcb_at do_ipc_transfer_aobj_at)

end

interpretation Ipc_AI?: Ipc_AI_3
proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales;(fact Ipc_AI_3_assms)?)
qed

end
