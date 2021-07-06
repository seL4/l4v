(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Ipc_AI
imports "./$L4V_ARCH/ArchFinalise_AI"
  "Lib.WPBang"
begin

context begin interpretation Arch .
requalify_consts
  in_device_frame
requalify_facts
  set_mi_invs
  set_mrs_ioports
  as_user_ioports
  set_message_info_ioports
  copy_mrs_ioports
  store_word_offs_ioports
  make_arch_fault_msg_ioports
  arch_derive_cap_notzombie
  arch_derive_cap_notIRQ

end

declare set_mi_invs[wp]

lemmas lookup_slot_wrapper_defs[simp] =
   lookup_source_slot_def lookup_target_slot_def lookup_pivot_slot_def

lemma get_mi_inv[wp]: "\<lbrace>I\<rbrace> get_message_info a \<lbrace>\<lambda>x. I\<rbrace>"
  by (simp add: get_message_info_def user_getreg_inv | wp)+

lemma set_mi_tcb [wp]:
  "\<lbrace> tcb_at t \<rbrace> set_message_info receiver msg \<lbrace>\<lambda>rv. tcb_at t\<rbrace>"
  by (simp add: set_message_info_def) wp

lemma lsfco_cte_at:
  "\<lbrace>valid_objs and valid_cap cn\<rbrace>
  lookup_slot_for_cnode_op f cn idx depth
  \<lbrace>\<lambda>rv. cte_at rv\<rbrace>,-"
  by (rule hoare_post_imp_R, rule lookup_cnode_slot_real_cte, simp add: real_cte_at_cte)

declare do_machine_op_tcb[wp]

lemma load_ct_inv[wp]:
  "\<lbrace>P\<rbrace> load_cap_transfer buf \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp add: load_cap_transfer_def)
  apply (wp dmo_inv mapM_wp' loadWord_inv)
  done

lemma get_recv_slot_inv[wp]:
  "\<lbrace> P \<rbrace> get_receive_slots receiver buf \<lbrace>\<lambda>rv. P \<rbrace>"
  apply (case_tac buf)
   apply simp
  apply (simp add: split_def whenE_def)
  apply (wp | simp)+
  done

lemma cte_wp_at_eq_simp:
  "cte_wp_at ((=) cap) = cte_wp_at (\<lambda>c. c = cap)"
  apply (rule arg_cong [where f=cte_wp_at])
  apply (safe intro!: ext)
  done

lemma get_rs_cte_at[wp]:
  "\<lbrace>\<top>\<rbrace>
  get_receive_slots receiver recv_buf
  \<lbrace>\<lambda>rv s. \<forall>x \<in> set rv. cte_wp_at (\<lambda>c. c = cap.NullCap) x s\<rbrace>"
  apply (cases recv_buf)
   apply (simp,wp,simp)
  apply (clarsimp simp add: split_def whenE_def)
  apply (wp | simp add: cte_wp_at_eq_simp | rule get_cap_wp)+
  done

lemma get_rs_cte_at2[wp]:
  "\<lbrace>\<top>\<rbrace>
  get_receive_slots receiver recv_buf
  \<lbrace>\<lambda>rv s. \<forall>x \<in> set rv. cte_wp_at ((=) cap.NullCap) x s\<rbrace>"
  apply (rule hoare_strengthen_post, rule get_rs_cte_at)
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  done

lemma get_rs_real_cte_at[wp]:
  "\<lbrace>valid_objs\<rbrace>
   get_receive_slots receiver recv_buf
   \<lbrace>\<lambda>rv s. \<forall>x \<in> set rv. real_cte_at x s\<rbrace>"
  apply (cases recv_buf)
   apply (simp,wp,simp)
  apply (clarsimp simp add: split_def whenE_def)
  apply (wp hoare_drop_imps lookup_cnode_slot_real_cte lookup_cap_valid | simp | rule get_cap_wp)+
  done

declare returnOKE_R_wp [wp]

lemma cap_derive_not_null_helper:
  "\<lbrace>P\<rbrace> derive_cap slot cap \<lbrace>Q\<rbrace>,- \<Longrightarrow>
   \<lbrace>\<lambda>s. cap \<noteq> cap.NullCap \<and> \<not> is_zombie cap \<and> cap \<noteq> cap.IRQControlCap \<longrightarrow> P s\<rbrace>
     derive_cap slot
       cap
   \<lbrace>\<lambda>rv s. rv \<noteq> cap.NullCap \<longrightarrow> Q rv s\<rbrace>,-"
  apply (case_tac cap,
         simp_all add: is_zombie_def,
         safe elim!: hoare_post_imp_R)
   apply (wp | simp add: derive_cap_def is_zombie_def)+
  done

lemma mask_cap_Null [simp]:
  "(mask_cap R c = cap.NullCap) = (c = cap.NullCap)"
  by (cases c) (auto simp: mask_cap_def cap_rights_update_def split: bool.split)

lemma ensure_no_children_wp:
  "\<lbrace>\<lambda>s. descendants_of p (cdt s) = {} \<longrightarrow> P s\<rbrace> ensure_no_children p \<lbrace>\<lambda>_. P\<rbrace>, -"
  apply (simp add: ensure_no_children_descendants valid_def validE_R_def validE_def)
  apply (auto simp: in_monad)
  done

definition
  "valid_message_info mi \<equiv>
     mi_length mi \<le> of_nat msg_max_length \<and>
     mi_extra_caps mi \<le> of_nat msg_max_extra_caps"

(* FIXME: can some of these assumptions be proved with lifting lemmas? *)
locale Ipc_AI =
  fixes state_ext_t :: "'state_ext::state_ext itself"
  assumes derive_cap_is_derived:
    "\<And>c' slot.
      \<lbrace>\<lambda>s::'state_ext state. c'\<noteq> cap.NullCap \<longrightarrow>
            cte_wp_at (\<lambda>cap. cap_master_cap cap = cap_master_cap c'
                           \<and> (cap_badge cap, cap_badge c') \<in> capBadge_ordering False
                           \<and> cap_asid cap = cap_asid c'
                           \<and> vs_cap_ref cap = vs_cap_ref c') slot s
                           \<and> valid_objs s\<rbrace>
        derive_cap slot c'
      \<lbrace>\<lambda>rv s. rv \<noteq> cap.NullCap \<longrightarrow> cte_wp_at (is_derived (cdt s) slot rv) slot s\<rbrace>, -"
  assumes is_derived_cap_rights [simp]:
    "\<And>m p R c. is_derived m p (cap_rights_update R c) = is_derived m p c"
  assumes data_to_message_info_valid:
    "\<And>w. valid_message_info (data_to_message_info w)"
  assumes get_extra_cptrs_length[wp]:
    "\<And>mi buf.
      \<lbrace>\<lambda>s::'state_ext state. valid_message_info mi\<rbrace>
         get_extra_cptrs buf mi
      \<lbrace>\<lambda>rv s. length rv \<le> msg_max_extra_caps\<rbrace>"
  assumes cap_asid_rights_update [simp]:
    "\<And>R c. cap_asid (cap_rights_update R c) = cap_asid c"
  assumes cap_rights_update_vs_cap_ref[simp]:
    "\<And>rs cap. vs_cap_ref (cap_rights_update rs cap) = vs_cap_ref cap"
  assumes is_derived_cap_rights2[simp]:
    "\<And>m p c R c'. is_derived m p c (cap_rights_update R c') = is_derived m p c c'"
  assumes cap_range_update [simp]:
    "\<And>R cap. cap_range (cap_rights_update R cap) = cap_range cap"
  assumes derive_cap_idle[wp]:
    "\<And>cap slot.
      \<lbrace>\<lambda>s::'state_ext state. global_refs s \<inter> cap_range cap = {}\<rbrace>
        derive_cap slot cap
      \<lbrace>\<lambda>c s. global_refs s \<inter> cap_range c = {}\<rbrace>, -"
  assumes arch_derive_cap_objrefs_iszombie:
    "\<And>P cap.
      \<lbrace>\<lambda>s::'state_ext state. P (set_option (aobj_ref cap)) False s\<rbrace>
        arch_derive_cap cap
      \<lbrace>\<lambda>rv s. rv \<noteq> NullCap \<longrightarrow> P (obj_refs rv) (is_zombie rv) s\<rbrace>,-"
  assumes obj_refs_remove_rights[simp]:
    "\<And>rs cap. obj_refs (remove_rights rs cap) = obj_refs cap"
  assumes store_word_offs_vms[wp]:
    "\<And>ptr offs v.
      \<lbrace>valid_machine_state :: 'state_ext state \<Rightarrow> bool\<rbrace>
        store_word_offs ptr offs v
      \<lbrace>\<lambda>_. valid_machine_state\<rbrace>"
  assumes is_zombie_update_cap_data[simp]:
    "\<And>P data cap. is_zombie (update_cap_data P data cap) = is_zombie cap"
  assumes valid_msg_length_strengthen:
    "\<And>mi. valid_message_info mi \<longrightarrow> unat (mi_length mi) \<le> msg_max_length"
  assumes copy_mrs_in_user_frame[wp]:
    "\<And>p t buf t' buf' n.
      \<lbrace>in_user_frame p :: 'state_ext state \<Rightarrow> bool\<rbrace>
        copy_mrs t buf t' buf' n
      \<lbrace>\<lambda>rv. in_user_frame p\<rbrace>"
  assumes make_arch_fault_msg_invs[wp]:
    "\<And>ft t. make_arch_fault_msg ft t \<lbrace>invs :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_aligned[wp]:
    "\<And>ft t. make_arch_fault_msg  ft t \<lbrace>pspace_aligned :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_distinct[wp]:
    "\<And>ft t. make_arch_fault_msg  ft t \<lbrace>pspace_distinct :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_vmdb[wp]:
    "\<And>ft t. make_arch_fault_msg  ft t \<lbrace>valid_mdb :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_ifunsafe[wp]:
    "\<And>ft t. make_arch_fault_msg  ft t \<lbrace>if_unsafe_then_cap :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_iflive[wp]:
    "\<And>ft t. make_arch_fault_msg  ft t \<lbrace>if_live_then_nonz_cap :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_state_refs_of[wp]:
    "\<And>P ft t. make_arch_fault_msg ft t \<lbrace>\<lambda>s:: 'state_ext state. P (state_refs_of s)\<rbrace>"
  assumes make_arch_fault_msg_ct[wp]:
    "\<And>ft t.   make_arch_fault_msg ft t \<lbrace>cur_tcb :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_cst[wp]:
    "\<And>ft t.   make_arch_fault_msg ft t \<lbrace>cur_sc_tcb :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_zombies[wp]:
    "\<And>ft t.   make_arch_fault_msg ft t \<lbrace>zombies_final :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_it[wp]:
    "\<And>P ft t. make_arch_fault_msg ft t \<lbrace>\<lambda>s :: 'state_ext state. P (idle_thread s)\<rbrace>"
  assumes make_arch_fault_msg_valid_globals[wp]:
    "\<And>ft t.   make_arch_fault_msg ft t \<lbrace>valid_global_refs :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_valid_idle[wp]:
    "\<And>ft t. make_arch_fault_msg ft t \<lbrace>valid_idle :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_arch[wp]:
    "\<And>P ft t. make_arch_fault_msg ft t \<lbrace>\<lambda>s::'state_ext state. P (arch_state s)\<rbrace>"
  assumes make_arch_fault_msg_typ_at[wp]:
    "\<And>P ft t T p. make_arch_fault_msg ft t \<lbrace>\<lambda>s::'state_ext state. P (typ_at T p s)\<rbrace>"
  assumes make_arch_fault_msg_irq_node[wp]:
    "\<And>P ft t. make_arch_fault_msg ft t \<lbrace>\<lambda>s::'state_ext state. P (interrupt_irq_node s)\<rbrace>"
  assumes make_arch_fault_msg_obj_at[wp]:
    "\<And> P P' pd ft t. make_arch_fault_msg ft t \<lbrace>\<lambda>s::'state_ext state. P (obj_at P' pd s)\<rbrace>"
  assumes make_arch_fault_msg_irq_handlers[wp]:
    "\<And>ft t. make_arch_fault_msg ft t \<lbrace>valid_irq_handlers :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_vspace_objs[wp]:
    "\<And>ft t. make_arch_fault_msg ft t \<lbrace>valid_vspace_objs :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_arch_caps[wp]:
    "\<And>ft t. make_arch_fault_msg ft t \<lbrace>valid_arch_caps :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_v_ker_map[wp]:
    "\<And>ft t. make_arch_fault_msg ft t \<lbrace>valid_kernel_mappings :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_eq_ker_map[wp]:
    "\<And>ft t. make_arch_fault_msg ft t \<lbrace>equal_kernel_mappings :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_asid_map [wp]:
    "\<And>ft t. make_arch_fault_msg ft t \<lbrace>valid_asid_map :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_only_idle [wp]:
    "\<And> ft t. make_arch_fault_msg ft t \<lbrace>only_idle :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_pspace_in_kernel_window[wp]:
    "\<And> ft t. make_arch_fault_msg ft t \<lbrace>pspace_in_kernel_window :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_cap_refs_in_kernel_window[wp]:
    "\<And> ft t. make_arch_fault_msg ft t \<lbrace>cap_refs_in_kernel_window :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_valid_objs[wp]:
    "\<And> ft t. make_arch_fault_msg ft t \<lbrace>valid_objs :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_valid_global_objs[wp]:
    "\<And> ft t. make_arch_fault_msg ft t \<lbrace>valid_global_objs :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_valid_global_vspace_mappings[wp]:
    "\<And> ft t. make_arch_fault_msg ft t \<lbrace>valid_global_vspace_mappings :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_valid_ioc[wp]:
    "\<And> ft t. make_arch_fault_msg ft t \<lbrace>valid_ioc :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_vms[wp]:
    "\<And> ft t. make_arch_fault_msg ft t \<lbrace>valid_machine_state :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_st_tcb_at'[wp]:
    "\<And> Q P p ft t. make_arch_fault_msg ft t \<lbrace>\<lambda>s :: 'state_ext state. Q (st_tcb_at P p s)\<rbrace>"
  assumes make_arch_fault_msg_fault_tcb_at[wp]:
    "\<And> Q P p ft t. make_arch_fault_msg ft t \<lbrace>\<lambda>s :: 'state_ext state. Q (fault_tcb_at P p s)\<rbrace>"
  assumes make_arch_fault_msg_bound_sc[wp]:
    "\<And> Q P p ft t. make_arch_fault_msg ft t \<lbrace>\<lambda>s :: 'state_ext state. Q (bound_sc_tcb_at P p s)\<rbrace>"
  assumes make_arch_fault_msg_cap_to[wp]:
    "\<And> ft t p. make_arch_fault_msg ft t \<lbrace>ex_nonz_cap_to p :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_valid_irq_states[wp]:
    "\<And> ft t. make_arch_fault_msg ft t \<lbrace>valid_irq_states :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_cap_refs_respects_device_region[wp]:
    "\<And> ft t. make_arch_fault_msg ft t \<lbrace>cap_refs_respects_device_region :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_reply_sc[wp]:
    "\<And> P p ft t. make_arch_fault_msg ft t \<lbrace>reply_sc_reply_at P p :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_reply_tcb[wp]:
    "\<And> P p ft t. make_arch_fault_msg ft t \<lbrace>reply_tcb_reply_at P p :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes do_fault_transfer_invs[wp]:
    "\<And>receiver badge sender recv_buf.
      \<lbrace>invs and tcb_at receiver :: 'state_ext state \<Rightarrow> bool\<rbrace>
        do_fault_transfer badge sender receiver recv_buf
      \<lbrace>\<lambda>rv. invs\<rbrace>"
  assumes lookup_ipc_buffer_in_user_frame[wp]:
    "\<And>t b.
      \<lbrace>valid_objs and tcb_at t :: 'state_ext state \<Rightarrow> bool\<rbrace>
        lookup_ipc_buffer b t
      \<lbrace>case_option (\<lambda>_. True) in_user_frame\<rbrace>"
  assumes do_normal_transfer_non_null_cte_wp_at:
    "\<And>P ptr st send_buffer ep b gr rt recv_buffer.
      (\<And>c. P c \<Longrightarrow> \<not> is_untyped_cap c) \<Longrightarrow>
        \<lbrace>valid_objs and cte_wp_at (P and ((\<noteq>) cap.NullCap)) ptr :: 'state_ext state \<Rightarrow> bool\<rbrace>
          do_normal_transfer st send_buffer ep b gr rt recv_buffer
        \<lbrace>\<lambda>_. cte_wp_at (P and ((\<noteq>) cap.NullCap)) ptr\<rbrace>"
  assumes do_ipc_transfer_tcb_caps:
    "\<And>P t ref st ep b gr rt.
      (\<And>c. P c \<Longrightarrow> \<not> is_untyped_cap c) \<Longrightarrow>
        \<lbrace>valid_objs and cte_wp_at P (t, ref) and tcb_at t :: 'state_ext state \<Rightarrow> bool\<rbrace>
          do_ipc_transfer st ep b gr rt
        \<lbrace>\<lambda>rv. cte_wp_at P (t, ref)\<rbrace>"
  assumes handle_arch_fault_reply_typ_at[wp]:
    "\<And> P T p x4 t label msg.
      \<lbrace>\<lambda>s::'state_ext state. P (typ_at T p s)\<rbrace>
        handle_arch_fault_reply x4 t label msg
      \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
 assumes do_fault_transfer_cte_wp_at[wp]:
  "\<And> P p x t label msg.
      \<lbrace>cte_wp_at P p :: 'state_ext state \<Rightarrow> bool\<rbrace>
        do_fault_transfer x t label msg
      \<lbrace> \<lambda>rv. cte_wp_at P p \<rbrace>"
  assumes transfer_caps_loop_valid_vspace_objs:
  "\<And>ep buffer n caps slots mi.
    \<lbrace>valid_vspace_objs::'state_ext state \<Rightarrow> bool\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. valid_vspace_objs\<rbrace>"
  assumes arch_get_sanitise_register_info_typ_at[wp]:
  "\<And> P T p t.
      \<lbrace>\<lambda>s::'state_ext state. P (typ_at T p s)\<rbrace>
        arch_get_sanitise_register_info t
      \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"


context Ipc_AI begin

lemma is_derived_mask [simp]:
  "is_derived m p (mask_cap R c) = is_derived m p c"
  by (simp add: mask_cap_def)

lemma is_derived_remove_rights [simp]:
  "is_derived m p (remove_rights R c) = is_derived m p c"
  by (simp add: remove_rights_def)

lemma get_mi_valid[wp]:
  "\<lbrace>valid_mdb\<rbrace> get_message_info a \<lbrace>\<lambda>rv s. valid_message_info rv\<rbrace>"
  apply (simp add: get_message_info_def)
  apply (wp | simp add: data_to_message_info_valid)+
  done

end

crunch inv[wp]: get_extra_cptr P (wp: dmo_inv loadWord_inv)
crunches set_extra_badge
  for pspace_respects_device_region[wp]: "pspace_respects_device_region"
  and cap_refs_respects_device_region[wp]: "cap_refs_respects_device_region"
  (wp: crunch_wps pspace_respects_device_region_dmo cap_refs_respects_device_region_dmo)

lemma get_extra_cptrs_inv[wp]:
  "\<lbrace>P\<rbrace> get_extra_cptrs buf mi \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (cases buf, simp_all del: upt.simps)
  apply (wp mapM_wp' dmo_inv loadWord_inv
             | simp add: load_word_offs_def del: upt.simps)+
  done

lemma mapM_length[wp]:
  "\<lbrace>\<lambda>s. P (length xs)\<rbrace> mapM f xs \<lbrace>\<lambda>rv s. P (length rv)\<rbrace>"
  by (induct xs arbitrary: P) (wpsimp simp: mapM_Cons mapM_def sequence_def|assumption)+

lemma cap_badge_rights_update[simp]:
  "cap_badge (cap_rights_update rights cap) = cap_badge cap"
  by (auto simp: cap_rights_update_def split: cap.split bool.splits)

lemma get_cap_cte_wp_at_rv:
  "\<lbrace>cte_wp_at (\<lambda>cap. P cap cap) p\<rbrace> get_cap p \<lbrace>\<lambda>rv. cte_wp_at (P rv) p\<rbrace>"
  apply (wp get_cap_wp)
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  done


lemma lsfco_cte_wp_at_univ:
  "\<lbrace>valid_objs and valid_cap croot and K (\<forall>cap rv. P cap rv)\<rbrace>
      lookup_slot_for_cnode_op f croot idx depth
   \<lbrace>\<lambda>rv. cte_wp_at (P rv) rv\<rbrace>, -"
  apply (rule hoare_gen_asmE)
  apply (rule hoare_post_imp_R)
   apply (rule lsfco_cte_at)
  apply (clarsimp simp: cte_wp_at_def)
  done


lemma bits_low_high_eq:
  assumes low: "x && mask bits = y && mask bits"
  and    high: "x >> bits = y >> bits"
  shows        "x = y"
  apply (rule word_eqI[rule_format])
  apply (case_tac "n < bits")
   apply (cut_tac x=n in word_eqD[OF low])
   apply (simp add: word_size)
  apply (cut_tac x="n - bits" in word_eqD[OF high])
  apply (simp add: nth_shiftr)
  done

context Ipc_AI begin
lemma mask_cap_vs_cap_ref[simp]:
  "vs_cap_ref (mask_cap msk cap) = vs_cap_ref cap"
  by (simp add: mask_cap_def)
end

lemma set_extra_badge_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> set_extra_badge buffer b n \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  by (simp add: set_extra_badge_def store_word_offs_def | wp)+

lemmas set_extra_badge_typ_ats[wp] = abs_typ_at_lifts[OF set_extra_badge_typ_at]

crunch valid_objs [wp]: set_extra_badge valid_objs

crunch aligned [wp]: set_extra_badge pspace_aligned

crunch dist [wp]: set_extra_badge pspace_distinct

crunch valid_mdb [wp]: set_extra_badge valid_mdb

crunch cte_wp_at [wp]: set_extra_badge "cte_wp_at P p"

lemma impEM:
  "\<lbrakk>P \<longrightarrow> Q; P; \<lbrakk>P; Q\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  by auto

lemma derive_cap_is_derived_foo:
  "\<lbrace>\<lambda>s. \<forall>cap'. (cte_wp_at (\<lambda>capa.
                 cap_master_cap capa = cap_master_cap cap \<and>
                 (cap_badge capa, cap_badge cap) \<in> capBadge_ordering False \<and>
                 cap_asid capa = cap_asid cap \<and> vs_cap_ref capa = vs_cap_ref cap)
      slot s \<and> valid_objs s \<and> cap' \<noteq> NullCap
          \<longrightarrow> cte_at slot s )
            \<and> (s \<turnstile> cap \<longrightarrow> s \<turnstile> cap')
            \<and> (cap' \<noteq> NullCap \<longrightarrow> cap \<noteq> NullCap \<and> \<not> is_zombie cap \<and> cap \<noteq> IRQControlCap)
          \<longrightarrow> Q cap' s \<rbrace>
      derive_cap slot cap \<lbrace>Q\<rbrace>,-"
  apply (clarsimp simp add: validE_R_def validE_def valid_def
                     split: sum.splits)
  apply (frule in_inv_by_hoareD[OF derive_cap_inv], clarsimp)
  apply (erule allE)
  apply (erule impEM)
   apply (frule use_validE_R[OF _ cap_derive_not_null_helper, OF _ _ imp_refl])
    apply (rule derive_cap_inv[THEN valid_validE_R])
    apply (intro conjI)
     apply (clarsimp simp:cte_wp_at_caps_of_state)+
     apply (erule(1) use_validE_R[OF _ derive_cap_valid_cap])
    apply simp
  apply simp
  done

lemma cap_rights_update_NullCap[simp]:
  "(cap_rights_update rs cap = cap.NullCap) = (cap = cap.NullCap)"
  by (auto simp: cap_rights_update_def split: cap.split bool.splits)

crunch in_user_frame[wp]: set_extra_badge "in_user_frame buffer"
crunch in_device_frame[wp]: set_extra_badge "in_device_frame buffer"

lemma cap_insert_cte_wp_at:
  "\<lbrace>\<lambda>s. cte_wp_at (is_derived (cdt s) src cap) src s \<and> valid_mdb s \<and> valid_objs s
    \<and> (if p = dest then P cap else cte_wp_at (\<lambda>c. P (masked_as_full c cap)) p s)\<rbrace> cap_insert cap src dest \<lbrace>\<lambda>uu. cte_wp_at P p\<rbrace>"
  supply if_cong[cong]
  apply (rule hoare_name_pre_state)
  apply (clarsimp split:if_split_asm)
  apply (clarsimp simp:cap_insert_def)
  apply (wp set_cap_cte_wp_at | simp split del: if_split)+
     apply (clarsimp simp:set_untyped_cap_as_full_def split del:if_splits)
    apply (wp get_cap_wp)+
   apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (clarsimp simp:cap_insert_def)
  apply (wp set_cap_cte_wp_at | simp split del: if_split)+
    apply (clarsimp simp:set_untyped_cap_as_full_def split del:if_splits)
   apply (wp set_cap_cte_wp_at get_cap_wp)+
  apply (clarsimp simp:cte_wp_at_caps_of_state)
  apply (frule(1) caps_of_state_valid)
  apply (intro conjI impI)
    apply (clarsimp simp:masked_as_full_def split:if_splits)+
   apply (clarsimp simp:valid_mdb_def is_derived_def)
   apply (drule(4) untyped_incD)
   apply (clarsimp simp:is_cap_simps cap_aligned_def
      dest!:valid_cap_aligned split:if_split_asm)
    apply (drule_tac y = "of_nat fa" in word_plus_mono_right[OF _ is_aligned_no_overflow',rotated])
     apply (simp add:word_of_nat_less)
    apply (clarsimp simp:p_assoc_help)
   apply (drule(1) caps_of_state_valid)+
   apply (clarsimp simp:valid_cap_def valid_untyped_def max_free_index_def)
  apply (clarsimp simp:masked_as_full_def split:if_splits)
  apply (erule impEM)
    apply (clarsimp simp: is_derived_def split:if_splits)
     apply (clarsimp simp:is_cap_simps cap_master_cap_simps)
   apply (clarsimp simp:is_cap_simps cap_master_cap_simps dest!:cap_master_cap_eqDs)
  apply (erule impEM)
    apply (clarsimp simp: is_derived_def split:if_splits)
     apply (clarsimp simp:is_cap_simps cap_master_cap_simps)
   apply (clarsimp simp:is_cap_simps cap_master_cap_simps dest!:cap_master_cap_eqDs)
   apply (clarsimp simp:is_derived_def is_cap_simps cap_master_cap_simps)
  done

lemma cap_insert_weak_cte_wp_at2:
  assumes imp: "\<And>c. P c \<Longrightarrow> \<not>is_untyped_cap c"
  shows
  "\<lbrace>\<lambda>s. if p = dest then P cap else cte_wp_at P p s\<rbrace>
   cap_insert cap src dest
   \<lbrace>\<lambda>uu. cte_wp_at P p\<rbrace>"
  unfolding cap_insert_def
  by (wp set_cap_cte_wp_at get_cap_wp static_imp_wp
      | simp add: cap_insert_def
      | unfold set_untyped_cap_as_full_def
      | auto simp: cte_wp_at_def dest!:imp)+

crunch in_user_frame[wp]: cap_insert "in_user_frame buffer"
  (wp: crunch_wps ignore: get_cap)

crunch cdt [wp]: set_extra_badge "\<lambda>s. P (cdt s)"

lemma descendants_insert_update:
  "\<lbrakk>m dest = None; p \<in> descendants_of a m\<rbrakk>
   \<Longrightarrow> p \<in> descendants_of a (\<lambda>x. if x = dest then y else m x)"
  apply (clarsimp simp:descendants_of_empty descendants_of_def)
  apply (simp add:cdt_parent_rel_def)
  apply (erule trancl_mono)
  apply (clarsimp simp:is_cdt_parent_def)
  done

lemma masked_as_full_null_cap[simp]:
  "(masked_as_full x x = cap.NullCap) = (x = cap.NullCap)"
  "(cap.NullCap  = masked_as_full x x) = (x = cap.NullCap)"
  by (case_tac x,simp_all add:masked_as_full_def)+

lemma transfer_caps_loop_mi_label[wp]:
  "\<lbrace>\<lambda>s. P (mi_label mi)\<rbrace>
     transfer_caps_loop ep buffer n caps slots mi
   \<lbrace>\<lambda>mi' s. P (mi_label mi')\<rbrace>"
  supply if_weak_cong[cong del]
  apply (induct caps arbitrary: n slots mi)
   apply simp
   apply wp
   apply simp
  apply (clarsimp split del: if_split)
  apply (rule hoare_pre)
   apply (wp const_on_failure_wp hoare_drop_imps | assumption)+
  apply simp
  done

lemma valid_remove_rights_If[simp]:
  "valid_cap cap s \<Longrightarrow> valid_cap (if P then remove_rights rs cap else cap) s"
  by simp

declare const_on_failure_wp [wp]

crunch ex_cte_cap_wp_to [wp]: set_extra_badge, do_machine_op "ex_cte_cap_wp_to P p"
  (rule: ex_cte_cap_to_pres)

lemma cap_insert_assume_null:
  "\<lbrace>P\<rbrace> cap_insert cap src dest \<lbrace>Q\<rbrace> \<Longrightarrow>
   \<lbrace>\<lambda>s. cte_wp_at ((=) cap.NullCap) dest s \<longrightarrow> P s\<rbrace> cap_insert cap src dest \<lbrace>Q\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (erule impCE)
   apply (simp add: cap_insert_def)
   apply (rule hoare_seq_ext[OF _ get_cap_sp])+
   apply (clarsimp simp: valid_def cte_wp_at_caps_of_state in_monad
              split del: if_split)
  apply (erule hoare_pre(1))
  apply simp
  done

context Ipc_AI begin

lemma transfer_caps_loop_presM:
  fixes P vo em ex buffer slots caps n mi
  assumes x: "\<And>cap src dest.
              \<lbrace>\<lambda>s::'state_ext state.
                               P s \<and> (vo \<longrightarrow> valid_objs s \<and> valid_mdb s \<and> real_cte_at dest s \<and> s \<turnstile> cap \<and> tcb_cap_valid cap dest s
                                   \<and> real_cte_at src s
                                   \<and> cte_wp_at (is_derived (cdt s) src cap) src s \<and> cap \<noteq> cap.NullCap)
                       \<and> (em \<longrightarrow> cte_wp_at ((=) cap.NullCap) dest s)
                       \<and> (ex \<longrightarrow> ex_cte_cap_wp_to (appropriate_cte_cap cap) dest s)\<rbrace>
                 cap_insert cap src dest \<lbrace>\<lambda>rv. P\<rbrace>"
  assumes eb: "\<And>b n. \<lbrace>P\<rbrace> set_extra_badge buffer b n \<lbrace>\<lambda>_. P\<rbrace>"
  shows      "\<lbrace>\<lambda>s. P s \<and> (vo \<longrightarrow> valid_objs s \<and> valid_mdb s \<and> distinct slots \<and>
                                 (\<forall>x \<in> set slots.  cte_wp_at (\<lambda>cap. cap = cap.NullCap) x s \<and> real_cte_at x s) \<and>
                                 (\<forall>x \<in> set caps. valid_cap (fst x) s \<and>
                                  cte_wp_at (\<lambda>cp. fst x \<noteq> cap.NullCap \<longrightarrow> cp \<noteq> fst x \<longrightarrow> cp = masked_as_full (fst x) (fst x)) (snd x) s
                                           \<and> real_cte_at (snd x) s))
                       \<and> (ex \<longrightarrow> (\<forall>x \<in> set slots. ex_cte_cap_wp_to is_cnode_cap x s))\<rbrace>
                  transfer_caps_loop ep buffer n caps slots mi
              \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (induct caps arbitrary: slots n mi)
   apply (simp, wp, simp)
  apply (clarsimp simp add: Let_def split_def whenE_def
                      cong: if_cong list.case_cong split del: if_split)
  apply (rule hoare_pre)
   apply (wp eb hoare_vcg_const_imp_lift hoare_vcg_const_Ball_lift static_imp_wp
           | assumption | simp split del: if_split)+
      apply (rule cap_insert_assume_null)
      apply (wp x hoare_vcg_const_Ball_lift cap_insert_cte_wp_at static_imp_wp)+
      apply (rule hoare_vcg_conj_liftE_R)
       apply (rule derive_cap_is_derived_foo)
      apply (rule_tac Q' ="\<lambda>cap' s. (vo \<longrightarrow> cap'\<noteq> cap.NullCap \<longrightarrow>
          cte_wp_at (is_derived (cdt s) (aa, b) cap') (aa, b) s)
          \<and> (cap'\<noteq> cap.NullCap \<longrightarrow> QM s cap')" for QM
          in hoare_post_imp_R)
        prefer 2
        apply clarsimp
        apply assumption
       apply (rule hoare_vcg_conj_liftE_R)
         apply (rule hoare_vcg_const_imp_lift_R)
        apply (rule derive_cap_is_derived)
      apply (wp derive_cap_is_derived_foo)+
  apply (clarsimp simp: cte_wp_at_caps_of_state
                        ex_cte_cap_to_cnode_always_appropriate_strg
                        real_cte_tcb_valid caps_of_state_valid
             split del: if_split)
  apply (clarsimp simp: remove_rights_def caps_of_state_valid
                        neq_Nil_conv cte_wp_at_caps_of_state
                        imp_conjR[symmetric] conj_comms
                 split del: if_split)
  apply (intro conjI)
   apply clarsimp
   apply (case_tac "cap = a",clarsimp)
   apply (clarsimp simp:masked_as_full_def is_cap_simps)
   apply (clarsimp simp: cap_master_cap_simps split:if_splits)
  apply (clarsimp split del: if_split)
  apply (intro conjI)
    apply (clarsimp split: if_split)
   apply (clarsimp)
  apply (rule ballI)
  apply (drule(1) bspec)
  apply clarsimp
  apply (intro conjI)
   apply (case_tac "capa = ac",clarsimp+)
  apply (case_tac "capa = ac")
   apply (clarsimp simp:masked_as_full_def is_cap_simps split:if_splits)+
  done

end

abbreviation (input)
  "transfer_caps_srcs caps s \<equiv>
    (\<forall>x \<in> set caps. cte_wp_at (\<lambda>cp. fst x \<noteq> cap.NullCap \<longrightarrow> cp = fst x) (snd x) s
                                           \<and> real_cte_at (snd x) s)"

context Ipc_AI begin

lemmas transfer_caps_loop_pres =
    transfer_caps_loop_presM[where vo=False and ex=False and em=False, simplified]

lemma transfer_caps_loop_typ_at[wp]:
   "\<And>P T p ep buffer n caps slots mi.
      \<lbrace>\<lambda>s::'state_ext state. P (typ_at T p s)\<rbrace>
        transfer_caps_loop ep buffer n caps slots mi
      \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by (wp transfer_caps_loop_pres)

lemma transfer_loop_aligned[wp]:
  "\<And>ep buffer n caps slots mi.
    \<lbrace>pspace_aligned :: 'state_ext state \<Rightarrow> bool\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
     \<lbrace>\<lambda>rv. pspace_aligned\<rbrace>"
  by (wp transfer_caps_loop_pres)

lemma transfer_loop_distinct[wp]:
  "\<And>ep buffer n caps slots mi.
    \<lbrace>pspace_distinct :: 'state_ext state \<Rightarrow> bool\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. pspace_distinct\<rbrace>"
  by (wp transfer_caps_loop_pres)

lemma invs_valid_objs2:
  "\<And>s. invs s \<longrightarrow> valid_objs s"
  by clarsimp

lemma transfer_caps_loop_valid_objs[wp]:
  "\<And>slots caps ep buffer n mi.
    \<lbrace>valid_objs and valid_mdb and (\<lambda>s. \<forall>slot \<in> set slots. real_cte_at slot s \<and> cte_wp_at (\<lambda>cap. cap = cap.NullCap) slot s)
            and transfer_caps_srcs caps and K (distinct slots) :: 'state_ext state \<Rightarrow> bool\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  apply (rule hoare_pre)
   apply (rule transfer_caps_loop_presM[where vo=True and em=False and ex=False])
    apply (wp|clarsimp)+
  apply (drule(1) bspec)
  apply (clarsimp simp:cte_wp_at_caps_of_state)
  apply (drule(1) caps_of_state_valid)
  apply (case_tac "a = cap.NullCap")
   apply clarsimp+
  done

lemma transfer_caps_loop_valid_mdb[wp]:
  "\<And>slots caps ep buffer n mi.
    \<lbrace>\<lambda>s. valid_mdb s \<and> valid_objs s \<and> pspace_aligned s \<and> pspace_distinct s
         \<and> (\<forall>slot \<in> set slots. real_cte_at slot s \<and> cte_wp_at (\<lambda>cap. cap = cap.NullCap) slot s)
         \<and> transfer_caps_srcs caps s \<and> distinct slots\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. valid_mdb :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  apply (rule hoare_pre)
   apply (rule transfer_caps_loop_presM[where vo=True and em=True and ex=False])
    apply wp
    apply (clarsimp simp: cte_wp_at_caps_of_state)
   apply (wp set_extra_badge_valid_mdb)
  apply (clarsimp simp:cte_wp_at_caps_of_state)
  apply (drule(1) bspec)+
  apply clarsimp
  apply (drule(1) caps_of_state_valid)
  apply (case_tac "a = cap.NullCap")
   apply clarsimp+
  done

crunch state_refs_of [wp]: set_extra_badge "\<lambda>s. P (state_refs_of s)"
crunch state_hyp_refs_of [wp]: set_extra_badge "\<lambda>s. P (state_hyp_refs_of s)"

lemma tcl_state_refs_of[wp]:
  "\<And>P ep buffer n caps slots mi.
    \<lbrace>\<lambda>s::'state_ext state. P (state_refs_of s)\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  by (wp transfer_caps_loop_pres)

lemma tcl_state_hyp_refs_of[wp]:
  "\<And>P ep buffer n caps slots mi.
    \<lbrace>\<lambda>s::'state_ext state. P (state_hyp_refs_of s)\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv s. P (state_hyp_refs_of s)\<rbrace>"
  by (wp transfer_caps_loop_pres)

crunch if_live [wp]: set_extra_badge if_live_then_nonz_cap

lemma tcl_iflive[wp]:
  "\<And>ep buffer n caps slots mi.
    \<lbrace>if_live_then_nonz_cap :: 'state_ext state \<Rightarrow> bool\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  by (wp transfer_caps_loop_pres cap_insert_iflive)

crunch if_unsafe [wp]: set_extra_badge if_unsafe_then_cap

lemma tcl_ifunsafe[wp]:
  "\<And>slots ep buffer n caps mi.
    \<lbrace>\<lambda>s::'state_ext state. if_unsafe_then_cap s
                             \<and> (\<forall>x\<in>set slots. ex_cte_cap_wp_to is_cnode_cap x s)\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. if_unsafe_then_cap\<rbrace>"
  by (wp transfer_caps_loop_presM[where vo=False and em=False and ex=True, simplified]
            cap_insert_ifunsafe | simp)+

end

lemma get_cap_global_refs[wp]:
  "\<lbrace>valid_global_refs\<rbrace> get_cap p \<lbrace>\<lambda>c s. global_refs s \<inter> cap_range c = {}\<rbrace>"
  apply (rule hoare_pre)
   apply (rule get_cap_wp)
  apply (clarsimp simp: valid_refs_def2 valid_global_refs_def cte_wp_at_caps_of_state)
  by blast

crunch pred_tcb_at [wp]: set_extra_badge "\<lambda>s. Q (pred_tcb_at proj P p s)"
crunch idle [wp]: set_extra_badge "\<lambda>s. P (idle_thread s)"

lemma (in Ipc_AI) tcl_idle[wp]:
  "\<And>ep buffer n caps slots mi.
    \<lbrace>valid_idle::'state_ext state \<Rightarrow> bool\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  by (wpsimp simp: set_extra_badge_def wp: transfer_caps_loop_pres valid_idle_lift)

crunch cur_tcb [wp]: set_extra_badge cur_tcb

lemma dmo_storeWord_cur_sc_tcb [wp]:
  "\<lbrace>cur_sc_tcb\<rbrace> do_machine_op (storeWord x y) \<lbrace>\<lambda>_. cur_sc_tcb\<rbrace>"
  by (wpsimp simp: do_machine_op_def cur_sc_tcb_def)

lemma set_extra_badge_cur_sc_tcb [wp]:
  "\<lbrace>cur_sc_tcb\<rbrace> set_extra_badge buffer badge n \<lbrace>\<lambda>_. cur_sc_tcb\<rbrace>"
  by (wpsimp simp: set_extra_badge_def store_word_offs_def)

lemma (in Ipc_AI) tcl_ct[wp]:
  "\<And>ep buffer n caps slots mi.
    \<lbrace>cur_tcb::'state_ext state \<Rightarrow> bool\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. cur_tcb\<rbrace>"
  by (wp transfer_caps_loop_pres)

lemma (in Ipc_AI) tcl_cst[wp]:
  "\<And>ep buffer n caps slots mi.
    \<lbrace>cur_sc_tcb::'state_ext state \<Rightarrow> bool\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. cur_sc_tcb\<rbrace>"
  by (wp transfer_caps_loop_pres)

crunch it[wp]: cap_insert "\<lambda>s. P (idle_thread s)"
  (wp: crunch_wps simp: crunch_simps)

lemma (in Ipc_AI) tcl_it[wp]:
  "\<And>P ep buffer n caps slots mi.
    \<lbrace>\<lambda>s::'state_ext state. P (idle_thread s)\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv s. P (idle_thread s)\<rbrace>"
  by (wp transfer_caps_loop_pres)

lemma (in Ipc_AI) derive_cap_objrefs_iszombie:
  "\<And>cap P slot.
    \<lbrace>\<lambda>s::'state_ext state. \<not> is_zombie cap \<longrightarrow> P (obj_refs cap) False s\<rbrace>
      derive_cap slot cap
    \<lbrace>\<lambda>rv s. rv \<noteq> cap.NullCap \<longrightarrow> P (obj_refs rv) (is_zombie rv) s\<rbrace>,-"
  apply (case_tac cap, simp_all add: derive_cap_def is_zombie_def)
   apply ((wpsimp wp: arch_derive_cap_objrefs_iszombie[simplified is_zombie_def] | rule validE_R_validE)+)
  done

lemma is_zombie_rights[simp]:
  "is_zombie (remove_rights rs cap) = is_zombie cap"
  by (auto simp: is_zombie_def remove_rights_def cap_rights_update_def
          split: cap.splits bool.splits)

crunch caps_of_state [wp]: set_extra_badge "\<lambda>s. P (caps_of_state s)"

lemma set_extra_badge_zombies_final[wp]:
  "\<lbrace>zombies_final\<rbrace> set_extra_badge buffer b n \<lbrace>\<lambda>_. zombies_final\<rbrace>"
  apply (simp add: zombies_final_def cte_wp_at_caps_of_state is_final_cap'_def2)
  apply (wp hoare_vcg_all_lift final_cap_lift)
  done

lemma (in Ipc_AI) tcl_zombies[wp]:
  "\<And>slots caps ep buffer n mi.
    \<lbrace>zombies_final and valid_objs and valid_mdb and K (distinct slots)
          and (\<lambda>s::'state_ext state. \<forall>slot \<in> set slots. real_cte_at slot s
                                     \<and> cte_wp_at (\<lambda>cap. cap = NullCap) slot s )
          and transfer_caps_srcs caps\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. zombies_final\<rbrace>"
  apply (rule hoare_pre)
   apply (rule transfer_caps_loop_presM[where vo=True and em=False and ex=False])
    apply (wp cap_insert_zombies)
    apply clarsimp
    apply (case_tac "(a, b) = (ab, bb)")
     apply (clarsimp simp: cte_wp_at_caps_of_state is_derived_def)
     apply (simp split: if_split_asm)
      apply ((clarsimp simp: is_cap_simps cap_master_cap_def
                     split: cap.split_asm)+)[2]
    apply (frule (3) zombies_finalD3)
     apply (clarsimp simp: is_derived_def is_cap_simps cap_master_cap_simps
                     split: if_split_asm dest!:cap_master_cap_eqDs)
     apply (drule_tac a=r in equals0D)
     apply (drule master_cap_obj_refs, simp)
    apply (fastforce simp: cte_wp_at_caps_of_state is_derived_def
                           is_cap_simps cap_master_cap_def
                    split: if_split_asm cap.split_asm)
   apply wp
  apply (clarsimp simp:cte_wp_at_caps_of_state)
  apply (drule(1) bspec,clarsimp)
  apply (fastforce dest!:caps_of_state_valid)
  done

lemmas derive_cap_valid_globals [wp]
  = derive_cap_inv[where P=valid_global_refs and slot = r and c = cap for r cap]

crunch arch [wp]: set_extra_badge "\<lambda>s. P (arch_state s)"

crunch irq [wp]: set_extra_badge "\<lambda>s. P (interrupt_irq_node s)"

context Ipc_AI begin

lemma transfer_caps_loop_valid_globals [wp]:
  "\<And>slots caps ep buffer n mi.
    \<lbrace>valid_global_refs and valid_objs and valid_mdb and K (distinct slots)
       and (\<lambda>s::'state_ext state. \<forall>slot \<in> set slots. real_cte_at slot s
                                  \<and> cte_wp_at (\<lambda>cap. cap = cap.NullCap) slot s)
       and transfer_caps_srcs caps\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. valid_global_refs\<rbrace>"
  apply (rule hoare_pre)
  apply (rule transfer_caps_loop_presM[where em=False and ex=False and vo=True])
     apply (wp | simp)+
     apply (clarsimp simp: cte_wp_at_caps_of_state is_derived_cap_range)
    apply (wp valid_global_refs_cte_lift|simp|intro conjI ballI)+
   apply (clarsimp simp:cte_wp_at_caps_of_state)
   apply (drule(1) bspec,clarsimp)
   apply (frule(1) caps_of_state_valid)
   apply (fastforce simp:valid_cap_def)
  apply clarsimp
  apply (drule(1) bspec)
  apply (clarsimp simp:cte_wp_at_caps_of_state)
  done

lemma transfer_caps_loop_arch[wp]:
  "\<And>P ep buffer n caps slots mi.
    \<lbrace>\<lambda>s::'state_ext state. P (arch_state s)\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv s. P (arch_state s)\<rbrace>"
  by (rule transfer_caps_loop_pres) wp+


lemma transfer_caps_loop_cspace_agnostic_obj_at:
  "cspace_agnostic_pred P' \<Longrightarrow>
  \<lbrace>\<lambda>s. P (obj_at P' pd s)\<rbrace> transfer_caps_loop ep buffer n caps slots mi \<lbrace>\<lambda>r s::'state_ext state. P (obj_at P' pd s)\<rbrace>"
  apply (rule hoare_pre)
   apply (rule transfer_caps_loop_presM[where em=False and ex=False and vo=False, simplified, where P="\<lambda>s. P (obj_at P' pd s)"])
    apply (wp cap_insert_cspace_agnostic_obj_at)
   apply (wpsimp simp: set_extra_badge_def)
  apply assumption
  done

lemmas transfer_caps_loop_aobj_at =
  transfer_caps_loop_cspace_agnostic_obj_at[OF cspace_arch_obj_pred_imp]

lemma transfer_caps_loop_valid_arch[wp]:
  "\<And>ep buffer n caps slots mi.
    \<lbrace>valid_arch_state::'state_ext state \<Rightarrow> bool\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. valid_arch_state\<rbrace>"
  by (rule valid_arch_state_lift_aobj_at; wp transfer_caps_loop_aobj_at)
(*
lemma tcl_reply':
  "\<And>slots caps ep buffer n mi.
    \<lbrace>valid_reply_caps and valid_reply_masters and valid_objs and valid_mdb and K(distinct slots)
          and (\<lambda>s. \<forall>x \<in> set slots. real_cte_at x s \<and> cte_wp_at (\<lambda>cap. cap = cap.NullCap) x s)
          and transfer_caps_srcs caps\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. valid_reply_caps and valid_reply_masters :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  apply (rule hoare_pre)
   apply (rule transfer_caps_loop_presM[where vo=True and em=False and ex=False])
     apply wp
     apply (clarsimp simp: real_cte_at_cte)
     apply (clarsimp simp: cte_wp_at_caps_of_state is_derived_def is_cap_simps)
     apply (frule(1) valid_reply_mastersD'[OF caps_of_state_cteD])
     apply (frule(1) tcb_cap_valid_caps_of_stateD)
     apply (frule(1) caps_of_state_valid)
     apply (clarsimp simp: tcb_cap_valid_def valid_cap_def is_cap_simps)
     apply (clarsimp simp: obj_at_def is_tcb is_cap_table cap_master_cap_def)
    apply (wpsimp wp: valid_reply_caps_st_cte_lift valid_reply_masters_cte_lift)
    apply (clarsimp simp:cte_wp_at_caps_of_state | intro conjI)+
   apply (drule(1) bspec,clarsimp)
   apply (frule(1) caps_of_state_valid)
   apply (fastforce simp:valid_cap_def)
  apply (drule(1) bspec)
  apply clarsimp
  done

lemmas tcl_reply[wp] = tcl_reply' [THEN hoare_strengthen_post
                                        [where R="\<lambda>_. valid_reply_caps"],
                                   simplified]

lemmas tcl_reply_masters[wp] = tcl_reply' [THEN hoare_strengthen_post
                                        [where R="\<lambda>_. valid_reply_masters"],
                                   simplified]
*)
lemma transfer_caps_loop_irq_node[wp]:
  "\<And>P ep buffer n caps slots mi.
    \<lbrace>\<lambda>s::'state_ext state. P (interrupt_irq_node s)\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv s. P (interrupt_irq_node s)\<rbrace>"
  by (rule transfer_caps_loop_pres; wp)

lemma cap_master_cap_irqs:
  "\<And>cap. cap_irqs cap = (case cap_master_cap cap
           of cap.IRQHandlerCap irq \<Rightarrow> {irq}
              | _ \<Rightarrow> {})"
  by (simp add: cap_master_cap_def split: cap.split)


crunch irq_state [wp]: set_extra_badge "\<lambda>s. P (interrupt_states s)"

lemma transfer_caps_loop_irq_handlers[wp]:
  "\<And>slots caps ep buffer n mi.
    \<lbrace>valid_irq_handlers and valid_objs and valid_mdb and K (distinct slots)
         and (\<lambda>s. \<forall>x \<in> set slots. real_cte_at x s \<and> cte_wp_at (\<lambda>cap. cap = cap.NullCap) x s)
         and transfer_caps_srcs caps\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. valid_irq_handlers :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  apply (rule hoare_pre)
   apply (rule transfer_caps_loop_presM[where vo=True and em=False and ex=False])
     apply wp
     apply (clarsimp simp: cte_wp_at_caps_of_state)
     apply (clarsimp simp: is_derived_def split: if_split_asm)
     apply (simp add: cap_master_cap_irqs)+
    apply (wp valid_irq_handlers_lift)
   apply (clarsimp simp:cte_wp_at_caps_of_state|intro conjI ballI)+
   apply (drule(1) bspec,clarsimp)
   apply (frule(1) caps_of_state_valid)
   apply (fastforce simp:valid_cap_def)
  apply (drule(1) bspec)
  apply clarsimp
  done

crunch valid_arch_caps [wp]: set_extra_badge valid_arch_caps

lemma transfer_caps_loop_ioports[wp]:
  "\<And>slots caps ep buffer n mi.
    \<lbrace>valid_ioports and valid_objs and valid_mdb and K (distinct slots)
         and (\<lambda>s. \<forall>x \<in> set slots. real_cte_at x s \<and> cte_wp_at (\<lambda>cap. cap = cap.NullCap) x s)
         and transfer_caps_srcs caps\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. valid_ioports :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  apply (rule hoare_pre)
   apply (rule transfer_caps_loop_presM[where vo=True and em=False and ex=False])
     apply (wp cap_insert_derived_ioports)
     apply (clarsimp simp: cte_wp_at_caps_of_state)
    apply (wp valid_ioports_lift)
   apply (clarsimp simp:cte_wp_at_caps_of_state|intro conjI ballI)+
   apply (drule(1) bspec,clarsimp)
   apply (frule(1) caps_of_state_valid)
   apply (fastforce simp:valid_cap_def)
  apply (drule(1) bspec)
  apply clarsimp
  done

lemma transfer_caps_loop_valid_arch_caps[wp]:
  "\<And>slots caps ep buffer n mi.
    \<lbrace>valid_arch_caps and valid_objs and valid_mdb and K(distinct slots)
           and (\<lambda>s. \<forall>x \<in> set slots. real_cte_at x s \<and> cte_wp_at (\<lambda>cap. cap = cap.NullCap) x s)
           and transfer_caps_srcs caps\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. valid_arch_caps :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  apply (wp transfer_caps_loop_presM[where vo=True and em=False and ex=False]
            cap_insert_valid_arch_caps)+
     apply simp
    apply wp
   apply (clarsimp simp:cte_wp_at_caps_of_state|intro conjI)+
   apply (drule(1) bspec,clarsimp)
   apply (frule(1) caps_of_state_valid)
   apply (fastforce simp:valid_cap_def)
  apply (drule(1) bspec)
  apply clarsimp
  done

crunch valid_global_objs [wp]: set_extra_badge valid_global_objs


lemma transfer_caps_loop_valid_global_objs[wp]:
  "\<And>ep buffer n caps slots mi.
    \<lbrace>valid_global_objs :: 'state_ext state \<Rightarrow> bool\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. valid_global_objs\<rbrace>"
  by (wp transfer_caps_loop_pres cap_insert_valid_global_objs)

crunch valid_kernel_mappings [wp]: set_extra_badge valid_kernel_mappings


lemma transfer_caps_loop_v_ker_map[wp]:
  "\<And>ep buffer n caps slots mi.
    \<lbrace>valid_kernel_mappings :: 'state_ext state \<Rightarrow> bool\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. valid_kernel_mappings\<rbrace>"
  by (wp transfer_caps_loop_pres)


crunch equal_kernel_mappings [wp]: set_extra_badge equal_kernel_mappings


lemma transfer_caps_loop_eq_ker_map[wp]:
  "\<And>ep buffer n caps slots mi.
    \<lbrace>equal_kernel_mappings :: 'state_ext state \<Rightarrow> bool\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. equal_kernel_mappings\<rbrace>"
  by (wp transfer_caps_loop_pres)


crunch valid_asid_map [wp]: set_extra_badge valid_asid_map


lemma transfer_caps_loop_asid_map[wp]:
  "\<And>ep buffer n caps slots mi.
    \<lbrace>valid_asid_map :: 'state_ext state \<Rightarrow> bool\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. valid_asid_map\<rbrace>"
  by (wp transfer_caps_loop_pres | simp)+


crunch only_idle [wp]: set_extra_badge only_idle


lemma transfer_caps_loop_only_idle[wp]:
  "\<And>ep buffer n caps slots mi.
    \<lbrace>only_idle :: 'state_ext state \<Rightarrow> bool\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. only_idle\<rbrace>"
  by (wp transfer_caps_loop_pres | simp)+

crunch valid_global_vspace_mappings [wp]: set_extra_badge valid_global_vspace_mappings


lemma transfer_caps_loop_valid_global_pd_mappings[wp]:
  "\<And>ep buffer n caps slots mi.
    \<lbrace>valid_global_vspace_mappings :: 'state_ext state \<Rightarrow> bool\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. valid_global_vspace_mappings\<rbrace>"
  by (wp transfer_caps_loop_pres)


crunch pspace_in_kernel_window [wp]: set_extra_badge pspace_in_kernel_window


lemma transfer_caps_loop_pspace_in_kernel_window[wp]:
  "\<And>ep buffer n caps slots mi.
    \<lbrace>pspace_in_kernel_window :: 'state_ext state \<Rightarrow> bool\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. pspace_in_kernel_window\<rbrace>"
  by (wp transfer_caps_loop_pres)


crunch cap_refs_in_kernel_window[wp]: set_extra_badge cap_refs_in_kernel_window

lemma transfer_caps_loop_cap_refs_in_kernel_window [wp]:
  "\<And>slots caps ep buffer n mi.
    \<lbrace>cap_refs_in_kernel_window and valid_objs and valid_mdb and K (distinct slots)
          and (\<lambda>s. \<forall>slot \<in> set slots. real_cte_at slot s \<and> cte_wp_at (\<lambda>cap. cap = cap.NullCap) slot s )
          and transfer_caps_srcs caps\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. cap_refs_in_kernel_window :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  apply (rule hoare_pre)
  apply (rule transfer_caps_loop_presM[where em=False and ex=False and vo=True])
     apply (wp | simp)+
     apply (clarsimp simp: cte_wp_at_caps_of_state is_derived_cap_range)
    apply (wp | simp)+
  apply (clarsimp simp:cte_wp_at_caps_of_state | intro conjI)+
   apply (drule(1) bspec,clarsimp)
   apply (frule(1) caps_of_state_valid)
   apply (fastforce simp:valid_cap_def)
  apply (drule(1) bspec)
  apply clarsimp
  done


crunch valid_ioc[wp]: store_word_offs valid_ioc


lemma transfer_caps_loop_valid_ioc[wp]:
  "\<And>ep buffer n caps slots mi.
    \<lbrace>\<lambda>s::'state_ext state. valid_ioc s\<rbrace>
     transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>_. valid_ioc\<rbrace>"
  by (wp transfer_caps_loop_pres | simp add: set_extra_badge_def)+


lemma set_extra_badge_vms[wp]:
  "\<And>buffer b n.
    \<lbrace>valid_machine_state::'state_ext state \<Rightarrow> bool\<rbrace>
      set_extra_badge buffer b n
    \<lbrace>\<lambda>_. valid_machine_state\<rbrace>"
  by (simp add: set_extra_badge_def) wp


lemma transfer_caps_loop_vms[wp]:
  "\<And>ep buffer n caps slots mi.
    \<lbrace>\<lambda>s::'state_ext state. valid_machine_state s\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>_. valid_machine_state\<rbrace>"
  by (wp transfer_caps_loop_pres)

crunches set_extra_badge
for valid_irq_states[wp]: "valid_irq_states"
  (ignore: do_machine_op)

lemma transfer_caps_loop_valid_irq_states[wp]:
  "\<And>ep buffer n caps slots mi.
    \<lbrace>\<lambda>s::'state_ext state. valid_irq_states s\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>_. valid_irq_states\<rbrace>"
  by (wp transfer_caps_loop_pres)

lemma transfer_caps_respects_device_region[wp]:
  "\<lbrace>\<lambda>s::'state_ext state. pspace_respects_device_region s\<rbrace>
    transfer_caps_loop ep buffer n caps slots mi
   \<lbrace>\<lambda>_. pspace_respects_device_region\<rbrace>"
  apply (wp transfer_caps_loop_pres)
  done

crunches do_machine_op, set_extra_badge
  for valid_replies[wp]: valid_replies

lemma transfer_caps_respects_valid_replies[wp]:
  "\<lbrace>\<lambda>s::'state_ext state. valid_replies s\<rbrace>
    transfer_caps_loop ep buffer n caps slots mi
   \<lbrace>\<lambda>_. valid_replies\<rbrace>"
  apply (wp transfer_caps_loop_pres)
  done

lemma transfer_caps_refs_respects_device_region[wp]:
  "\<lbrace>cap_refs_respects_device_region and valid_objs and valid_mdb and (\<lambda>s. \<forall>slot \<in> set slots. real_cte_at slot s \<and> cte_wp_at (\<lambda>cap. cap = cap.NullCap) slot s)
            and transfer_caps_srcs caps and K (distinct slots)\<rbrace>
    transfer_caps_loop ep buffer n caps slots mi
   \<lbrace>\<lambda>_ s::'state_ext state. cap_refs_respects_device_region s\<rbrace>"
  apply (rule hoare_pre)
   apply (rule transfer_caps_loop_presM[where vo=True and em=True and ex=False])
    apply wp
    apply (clarsimp simp: cte_wp_at_caps_of_state is_derived_cap_range is_derived_cap_is_device)
   apply (wp set_extra_badge_valid_mdb)
  apply (clarsimp simp:cte_wp_at_caps_of_state)
  apply (drule(1) bspec)+
  apply clarsimp
  apply (drule(1) caps_of_state_valid)
  apply (case_tac "a = cap.NullCap")
  apply clarsimp+
  done

crunches transfer_caps_loop
  for fault_tcbs_valid_states_except_set[wp]: "fault_tcbs_valid_states_except_set TS :: 'state_ext state \<Rightarrow> _"
  (rule: transfer_caps_loop_pres wp: crunch_wps)

lemma transfer_caps_loop_invs[wp]:
  "\<And>slots.
    \<lbrace>\<lambda>s::'state_ext state. invs s
          \<and> (\<forall>x \<in> set slots. ex_cte_cap_wp_to is_cnode_cap x s) \<and> distinct slots
          \<and> (\<forall>x \<in> set slots. real_cte_at x s \<and> cte_wp_at (\<lambda>cap. cap = cap.NullCap) x s)
          \<and> transfer_caps_srcs caps s\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. invs\<rbrace>"
  unfolding invs_def valid_state_def valid_pspace_def
  by (wpsimp wp: valid_irq_node_typ transfer_caps_loop_valid_vspace_objs)

end

(* FIXME: move *)
crunch valid_vspace_objs [wp]: set_extra_badge valid_vspace_objs

crunch vspace_objs [wp]: set_untyped_cap_as_full "valid_vspace_objs"
  (wp: crunch_wps simp: crunch_simps ignore: set_object set_cap)

crunch vspace_objs [wp]: cap_insert "valid_vspace_objs"
  (wp: crunch_wps simp: crunch_simps ignore: set_object set_cap)

lemma zipWith_append2:
  "length ys + 1 < n \<Longrightarrow>
   zipWith f [0 ..< n] (ys @ [y]) = zipWith f [0 ..< n] ys @ [f (length ys) y]"
  apply (simp add: zipWith_def zip_append2)
  apply (subst upt_conv_Cons, erule Suc_lessD)
  apply simp
  apply (subst zip_take_triv[OF order_refl, symmetric], fastforce)
  done

(* FIXME: move *)
lemma list_all2_zip_same:
  assumes rl: "\<And>a a' x y. P (x, a) (y, a) \<Longrightarrow> P (x, a') (y, a')"
  shows "list_all2 (\<lambda>x y. P (x, a) (y, a)) xs ys \<Longrightarrow> list_all2 P (zip xs as) (zip ys as)"
  apply (induct xs arbitrary: as ys a)
   apply simp
  apply (case_tac as)
   apply simp
  apply simp
  apply (case_tac ys)
   apply simp
  apply clarsimp
  apply (erule rl)
  done


lemma grs_distinct[wp]:
  "\<lbrace>\<top>\<rbrace> get_receive_slots t buf \<lbrace>\<lambda>rv s. distinct rv\<rbrace>"
  by (cases buf; wpsimp)


lemma transfer_caps_mi_label[wp]:
  "\<lbrace>\<lambda>s. P (mi_label mi)\<rbrace>
     transfer_caps mi caps ep receiver recv_buf
   \<lbrace>\<lambda>mi' s. P (mi_label mi')\<rbrace>"
  by (wpsimp simp: transfer_caps_def)


context Ipc_AI begin

lemma transfer_cap_typ_at[wp]:
  "\<And>P T p mi caps ep receiver recv_buf.
    \<lbrace>\<lambda>s::'state_ext state. P (typ_at T p s)\<rbrace>
      transfer_caps mi caps ep receiver recv_buf
    \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by (wpsimp wp: cap_insert_typ_at hoare_drop_imps simp: transfer_caps_def)

lemma transfer_cap_tcb[wp]:
  "\<And>mi caps ep receiver recv_buf.
    \<lbrace>\<lambda>s::'state_ext state. tcb_at t s\<rbrace>
      transfer_caps mi caps ep receiver recv_buf
    \<lbrace>\<lambda>rv. tcb_at t\<rbrace>"
  by (simp add: tcb_at_typ, wp)

end

lemma cte_refs_mask[simp]:
  "cte_refs (mask_cap rs cap) = cte_refs cap"
  by (rule ext, cases cap, simp_all add: mask_cap_def cap_rights_update_def split:bool.splits)


lemma get_cap_cte_caps_to[wp]:
  "\<lbrace>\<lambda>s. \<forall>cp. P cp = P cp\<rbrace>
     get_cap sl
   \<lbrace>\<lambda>rv s. P rv \<longrightarrow> (\<forall>p\<in>cte_refs rv (interrupt_irq_node s). ex_cte_cap_wp_to P p s)\<rbrace>"
  apply (wp get_cap_wp)
  apply (clarsimp simp: ex_cte_cap_wp_to_def)
  apply (cases sl, fastforce elim!: cte_wp_at_weakenE)
  done


lemma lookup_cap_cte_caps_to[wp]:
  "\<lbrace>\<lambda>s. \<forall>rs cp. P (mask_cap rs cp) = P cp\<rbrace>
     lookup_cap t cref
   \<lbrace>\<lambda>rv s. P rv \<longrightarrow> (\<forall>p\<in>cte_refs rv (interrupt_irq_node s). ex_cte_cap_wp_to P p s)\<rbrace>,-"
  by (simp add: lookup_cap_def split_def) wpsimp


lemma is_cnode_cap_mask[simp]:
  "is_cnode_cap (mask_cap rs cap) = is_cnode_cap cap"
  by (auto simp: mask_cap_def cap_rights_update_def
          split: cap.split bool.splits)


lemma get_rs_cap_to[wp]:
  "\<lbrace>\<top>\<rbrace> get_receive_slots rcvr buf
   \<lbrace>\<lambda>rv s. \<forall>x \<in> set rv. ex_cte_cap_wp_to is_cnode_cap x s\<rbrace> "
  apply (cases buf, simp_all add: split_def whenE_def split del: if_split)
   apply (wp | simp | rule hoare_drop_imps)+
  done

lemma derive_cap_notzombie[wp]:
  "\<lbrace>\<top>\<rbrace> derive_cap slot cap \<lbrace>\<lambda>rv s. \<not> is_zombie rv\<rbrace>,-"
  apply (cases cap; clarsimp simp: derive_cap_def)
             by (wpsimp wp: arch_derive_cap_notzombie simp: is_zombie_def)+


lemma derive_cap_notIRQ[wp]:
  "\<lbrace>\<top>\<rbrace> derive_cap slot cap \<lbrace>\<lambda>rv s. rv \<noteq> cap.IRQControlCap\<rbrace>,-"
  by (cases cap; wpsimp wp: arch_derive_cap_notIRQ simp: derive_cap_def o_def)


lemma get_cap_zombies_helper:
  "\<lbrace>zombies_final\<rbrace>
     get_cap p
   \<lbrace>\<lambda>rv s. \<not> is_zombie rv
     \<longrightarrow> (\<forall>r\<in>obj_refs rv. \<forall>p'.
           cte_wp_at (\<lambda>c. r \<in> obj_refs c) p' s
             \<longrightarrow> cte_wp_at (Not \<circ> is_zombie) p' s)\<rbrace>"
  apply (wp get_cap_wp)
  apply (clarsimp simp: cte_wp_at_def)
  apply (subgoal_tac "p \<noteq> (a, b)")
   apply (drule(3) zombies_finalD2)
    apply blast
   apply simp
  apply clarsimp
  done

context Ipc_AI begin

lemma random_helper[simp]:
  "\<And>ct_send_data ct ms cap.
    is_zombie (case ct_send_data ct of None \<Rightarrow> mask_cap ms cap
                 | Some w \<Rightarrow> update_cap_data P w (mask_cap ms cap))
      = is_zombie cap"
  by (simp split: option.splits)

end

lemma zombies_final_pres:
  assumes x: "\<And>P T p. \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
      and y: "\<And>P p. \<lbrace>cte_wp_at P p\<rbrace> f \<lbrace>\<lambda>rv. cte_wp_at P p\<rbrace>"
  shows      "\<lbrace>zombies_final\<rbrace> f \<lbrace>\<lambda>rv. zombies_final\<rbrace>"
  apply (simp only: zombies_final_def final_cap_at_eq
                    imp_conv_disj cte_wp_at_neg2[where P=is_zombie]
                    de_Morgan_conj)
  apply (intro hoare_vcg_disj_lift hoare_vcg_ex_lift hoare_vcg_conj_lift
               y hoare_vcg_all_lift valid_cte_at_neg_typ x)
  done


lemma cte_wp_at_orth:
  "\<lbrakk> cte_wp_at (\<lambda>c. P c) p s; cte_wp_at (\<lambda>c. \<not> P c) p s \<rbrakk> \<Longrightarrow> False"
  unfolding cte_wp_at_def
  by clarsimp


declare sym_ex_elim[elim!]


lemma no_irq_case_option:
  "\<lbrakk> no_irq f; \<And>x. no_irq (g x) \<rbrakk> \<Longrightarrow> no_irq (case_option f g x)"
  apply (subst no_irq_def)
  apply clarsimp
  apply (rule hoare_pre, wpsimp wp: no_irq)
  apply assumption
  done


lemma get_mrs_inv[wp]:
  "\<lbrace>P\<rbrace> get_mrs t buf info \<lbrace>\<lambda>rv. P\<rbrace>"
  by (wpsimp simp: get_mrs_def load_word_offs_def wp: dmo_inv loadWord_inv mapM_wp')


lemma copy_mrs_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> copy_mrs s sb r rb n \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  apply (simp add: copy_mrs_def load_word_offs_def
                   store_word_offs_def set_object_def
              cong: option.case_cong
              split del: if_split)
  apply (wp hoare_vcg_split_case_option mapM_wp')
   apply (wp hoare_drop_imps mapM_wp')+
   apply simp_all
  done


lemmas copy_mrs_typ_ats[wp] = abs_typ_at_lifts[OF copy_mrs_typ_at]


lemma copy_mrs_tcb[wp]:
  "\<lbrace> tcb_at t \<rbrace> copy_mrs s sb r rb n \<lbrace>\<lambda>rv. tcb_at t \<rbrace>"
  by (simp add: tcb_at_typ, wp)

lemma copy_mrs_ntfn_at[wp]:
  "\<lbrace> ntfn_at p \<rbrace> copy_mrs s sb r rb n \<lbrace>\<lambda>rv. ntfn_at p \<rbrace>"
  by (simp add: ntfn_at_typ, wp)


lemmas copy_mrs_redux =
   copy_mrs_def bind_assoc[symmetric]
   thread_set_def[simplified, symmetric]

lemma store_word_offs_invs[wp]:
  "\<lbrace>invs\<rbrace> store_word_offs p x w \<lbrace>\<lambda>_. invs\<rbrace>"
  by (wp | simp add: store_word_offs_def)+

lemma copy_mrs_invs[wp]:
  "\<lbrace> invs and tcb_at r and tcb_at s \<rbrace> copy_mrs s sb r rb n \<lbrace>\<lambda>rv. invs \<rbrace>"
  unfolding copy_mrs_redux by (wpsimp wp: mapM_wp')

lemma set_mrs_aligned [wp]:
  "\<lbrace>pspace_aligned\<rbrace>  set_mrs t a msgs \<lbrace>\<lambda>rv. pspace_aligned\<rbrace>"
  apply (simp add: set_mrs_redux zipWithM_x_mapM split_def
                   store_word_offs_def
             cong: option.case_cong
              del: upt.simps)
  apply (wp mapM_wp' | wpcw | simp)+
  done


lemma copy_mrs_valid_objs [wp]:
  "\<lbrace>valid_objs\<rbrace> copy_mrs s sb r rb n \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  apply (simp add: copy_mrs_redux)
  apply (wp mapM_wp' | wpc
       | simp add: store_word_offs_def load_word_offs_def)+
  done


lemma copy_mrs_aligned [wp]:
  "\<lbrace>pspace_aligned\<rbrace> copy_mrs s sb r rb n \<lbrace>\<lambda>rv. pspace_aligned\<rbrace>"
  apply (simp add: copy_mrs_redux)
  apply (wp mapM_wp' | wpc
       | simp add: store_word_offs_def load_word_offs_def)+
  done



lemmas get_tcb_ko_atI = get_tcb_ko_at [THEN iffD1]


crunch "distinct" [wp]: set_mrs pspace_distinct
  (wp: select_wp hoare_vcg_split_case_option mapM_wp
       hoare_drop_imps  refl
   simp: zipWithM_x_mapM)


crunch "distinct" [wp]: copy_mrs pspace_distinct
  (wp: mapM_wp' simp: copy_mrs_redux)


crunch mdb [wp]: store_word_offs valid_mdb (wp: crunch_wps simp: crunch_simps)


crunch caps_of_state [wp]: store_word_offs "\<lambda>s. P (caps_of_state s)"
  (wp: crunch_wps simp: crunch_simps)


crunch mdb_P [wp]: set_mrs "\<lambda>s. P (cdt s)"
  (wp: crunch_wps simp: crunch_simps zipWithM_x_mapM)


crunch mdb_R [wp]: set_mrs "\<lambda>s. P (is_original_cap s)"
  (wp: crunch_wps simp: crunch_simps zipWithM_x_mapM)


lemma set_mrs_caps_of_state[wp]:
  "\<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> set_mrs t b m \<lbrace>\<lambda>rv s. P (caps_of_state s)\<rbrace>"
  apply (simp add: set_mrs_redux zipWithM_x_mapM split_def
             cong: option.case_cong
                split del: if_split)
  apply (wp mapM_wp' | wpc)+
  apply (wp thread_set_caps_of_state_trivial2 | simp)+
  done


lemma set_mrs_mdb [wp]:
  "\<lbrace>valid_mdb\<rbrace> set_mrs t b m \<lbrace>\<lambda>_. valid_mdb\<rbrace>"
  by (rule valid_mdb_lift; wp)


crunch mdb_P [wp]: copy_mrs "\<lambda>s. P (cdt s)"
  (wp: crunch_wps simp: crunch_simps)


crunch mdb_R [wp]: copy_mrs "\<lambda>s. P (is_original_cap s)"
  (wp: crunch_wps simp: crunch_simps)


crunch mdb [wp]: copy_mrs valid_mdb
  (wp: crunch_wps simp: crunch_simps)


lemma set_mrs_ep_at[wp]:
  "\<lbrace>ep_at x\<rbrace> set_mrs tcb buf msg \<lbrace>\<lambda>rv. ep_at x\<rbrace>"
  by (simp add: ep_at_typ, wp)


lemma copy_mrs_ep_at[wp]:
  "\<lbrace>ep_at x\<rbrace> copy_mrs s sb r rb n \<lbrace>\<lambda>rv. ep_at x\<rbrace>"
  by (simp add: ep_at_typ, wp)

crunch cte_wp_at[wp]: copy_mrs "cte_wp_at P p"
  (wp: crunch_wps)


crunch inv[wp]: lookup_extra_caps "P"
  (wp: crunch_wps mapME_wp' simp: crunch_simps ignore: mapME)

lemma lookup_extra_caps_srcs[wp]:
  "\<lbrace>valid_objs\<rbrace> lookup_extra_caps thread buf info \<lbrace>transfer_caps_srcs\<rbrace>,-"
  apply (simp add: lookup_extra_caps_def lookup_cap_and_slot_def
                   split_def lookup_slot_for_thread_def)
  apply (wp mapME_set[where R=valid_objs] get_cap_wp resolve_address_bits_real_cte_at
             | simp add: cte_wp_at_caps_of_state
             | wp (once) hoare_drop_imps
             | clarsimp simp: objs_valid_tcb_ctable)+
  done


lemma mapME_length:
  "\<lbrace>\<lambda>s. P (length xs)\<rbrace> mapME m xs \<lbrace>\<lambda>ys s. P (length ys)\<rbrace>, -"
  apply (induct xs arbitrary: P)
   apply (simp add: mapME_Nil | wp)+
  apply (simp add: mapME_def sequenceE_def)
  apply (rule hoare_pre)
   apply (wp | simp | assumption)+
  done

context Ipc_AI begin

crunch typ_at[wp]: do_normal_transfer "\<lambda>s::'state_ext state. P (typ_at T p s)"

lemma do_normal_tcb[wp]:
  "\<And>t sender send_buf ep badge can_grant receiver recv_buf.
    \<lbrace>tcb_at t :: 'state_ext state \<Rightarrow> bool\<rbrace>
      do_normal_transfer sender send_buf ep badge
                         can_grant receiver recv_buf
    \<lbrace>\<lambda>rv. tcb_at t\<rbrace>"
  by (simp add: tcb_at_typ, wp)

end

lemma valid_recv_ep_tcb:
  "\<lbrakk> valid_ep (RecvEP (a # lista)) s \<rbrakk> \<Longrightarrow> tcb_at a s"
  by (simp add: valid_ep_def tcb_at_def)


lemma copy_mrs_thread_set_dmo:
  assumes ts: "\<And>c. \<lbrace>Q\<rbrace> thread_set (\<lambda>tcb. tcb\<lparr>tcb_arch := arch_tcb_context_set (c tcb) (tcb_arch tcb)\<rparr>) r \<lbrace>\<lambda>rv. Q\<rbrace>"
  assumes dmo: "\<And>x y. \<lbrace>Q\<rbrace> do_machine_op (storeWord x y) \<lbrace>\<lambda>rv. Q\<rbrace>"
               "\<And>x. \<lbrace>Q\<rbrace> do_machine_op (loadWord x) \<lbrace>\<lambda>rv. Q\<rbrace>"
  shows "\<lbrace>Q\<rbrace> copy_mrs s sb r rb n \<lbrace>\<lambda>rv. Q\<rbrace>"
  apply (simp add: copy_mrs_redux)
  apply (wp mapM_wp [where S=UNIV, simplified] dmo ts | wpc
       | simp add: store_word_offs_def load_word_offs_def
       | rule as_user_wp_thread_set_helper hoare_drop_imps)+
  done


lemma set_mrs_refs_of[wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace>
     set_mrs a b c
   \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  by (wp set_mrs_thread_set_dmo thread_set_refs_trivial | simp)+


lemma set_mrs_cur [wp]:
  "\<lbrace>cur_tcb\<rbrace> set_mrs r t mrs \<lbrace>\<lambda>rv. cur_tcb\<rbrace>"
  by (wp set_mrs_thread_set_dmo)

lemma set_mrs_state_hyp_refs_of[wp]:
  "\<lbrace>\<lambda> s. P (state_hyp_refs_of s)\<rbrace> set_mrs thread buf msgs \<lbrace>\<lambda>_ s. P (state_hyp_refs_of s)\<rbrace>"
  by (wp set_mrs_thread_set_dmo thread_set_hyp_refs_trivial | simp)+

lemma set_mrs_iflive[wp]:
  "\<lbrace>if_live_then_nonz_cap\<rbrace> set_mrs a b c \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  by (wp set_mrs_thread_set_dmo thread_set_iflive_trivial
         ball_tcb_cap_casesI | simp)+


lemma set_mrs_ifunsafe[wp]:
  "\<lbrace>if_unsafe_then_cap\<rbrace> set_mrs a b c \<lbrace>\<lambda>rv. if_unsafe_then_cap\<rbrace>"
  by (wp set_mrs_thread_set_dmo thread_set_ifunsafe_trivial
         ball_tcb_cap_casesI | simp)+


lemma set_mrs_zombies[wp]:
  "\<lbrace>zombies_final\<rbrace> set_mrs a b c \<lbrace>\<lambda>rv. zombies_final\<rbrace>"
  by (wp set_mrs_thread_set_dmo thread_set_zombies_trivial
         ball_tcb_cap_casesI | simp)+


lemma set_mrs_valid_globals[wp]:
  "\<lbrace>valid_global_refs\<rbrace> set_mrs a b c \<lbrace>\<lambda>rv. valid_global_refs\<rbrace>"
  by (wp set_mrs_thread_set_dmo thread_set_global_refs_triv
         ball_tcb_cap_casesI valid_global_refs_cte_lift | simp)+


context Ipc_AI begin

crunch aligned[wp]: do_ipc_transfer "pspace_aligned :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps simp: crunch_simps zipWithM_x_mapM)

crunch "distinct"[wp]: do_ipc_transfer "pspace_distinct :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps simp: crunch_simps zipWithM_x_mapM)

crunch vmdb[wp]: set_message_info "valid_mdb :: 'state_ext state \<Rightarrow> bool"

crunch vmdb[wp]: do_ipc_transfer "valid_mdb :: 'state_ext state \<Rightarrow> bool"
  (ignore: as_user set_object simp: crunch_simps ball_conj_distrib
       wp: crunch_wps hoare_vcg_const_Ball_lift transfer_caps_loop_valid_mdb)

crunch ifunsafe[wp]: do_ipc_transfer "if_unsafe_then_cap :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps hoare_vcg_const_Ball_lift simp: zipWithM_x_mapM ignore: transfer_caps_loop)

crunch iflive[wp]: do_ipc_transfer "if_live_then_nonz_cap :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps sched_context_update_consumed_if_live simp: zipWithM_x_mapM gets_the_wp
   ignore: transfer_caps_loop set_object sched_context_update_consumed)

(* Move to Realtime_AI *)
lemma sched_context_update_consumed_if_live[wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace>
   sched_context_update_consumed param_a
   \<lbrace>\<lambda>_ s. P (state_refs_of s)\<rbrace>"
  by (wpsimp simp: sched_context_update_consumed_def)

crunch state_refs_of[wp]: do_ipc_transfer "\<lambda>s::'state_ext state. P (state_refs_of s)"
  (wp: crunch_wps simp: zipWithM_x_mapM ignore: transfer_caps_loop set_object)

crunch ct[wp]: do_ipc_transfer "cur_tcb :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps simp: zipWithM_x_mapM ignore: transfer_caps_loop set_object)

crunch zombies[wp]: do_ipc_transfer "zombies_final :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps hoare_vcg_const_Ball_lift tcl_zombies simp: crunch_simps ball_conj_distrib )

crunch it[wp]: do_ipc_transfer "\<lambda>s::'state_ext state. P (idle_thread s)"
  (wp: sched_context_update_consumed_it crunch_wps
    simp: crunch_simps zipWithM_x_mapM ignore: set_object)

crunch valid_globals[wp]: do_ipc_transfer "valid_global_refs :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps hoare_vcg_const_Ball_lift simp: crunch_simps zipWithM_x_mapM ball_conj_distrib
   ignore: set_object)

end

lemma set_mrs_idle[wp]:
  "\<lbrace>valid_idle\<rbrace> set_mrs param_a param_b param_c \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  by (wp set_mrs_thread_set_dmo thread_set_valid_idle_trivial
         ball_tcb_cap_casesI | simp)+

context Ipc_AI begin

crunch arch[wp]: do_ipc_transfer "\<lambda>s::'state_ext state. P (arch_state s)"
  (wp: crunch_wps simp: zipWithM_x_mapM ignore: transfer_caps_loop)

crunch typ_at[wp]: do_ipc_transfer "\<lambda>s::'state_ext state. P (typ_at T p s)"
  (wp: crunch_wps simp: zipWithM_x_mapM ignore: transfer_caps_loop)

crunch irq_node[wp]: do_ipc_transfer "\<lambda>s::'state_ext state. P (interrupt_irq_node s)"
  (wp: crunch_wps simp: zipWithM_x_mapM crunch_simps)

lemma do_ipc_transfer_aobj_at:
  "arch_obj_pred P' \<Longrightarrow>
  \<lbrace>\<lambda>s. P (obj_at P' pd s)\<rbrace> do_ipc_transfer s ep bg grt r \<lbrace>\<lambda>r s :: 'state_ext state. P (obj_at P' pd s)\<rbrace>"
  unfolding
    do_ipc_transfer_def do_normal_transfer_def set_message_info_def transfer_caps_def
    copy_mrs_def do_fault_transfer_def sched_context_update_consumed_def
  apply (wpsimp wp: as_user.aobj_at set_mrs.aobj_at hoare_drop_imps mapM_wp' transfer_caps_loop_aobj_at)
       apply (case_tac f, simp split del: if_split)
          by (wpsimp simp: sched_context_update_consumed_def
                 wp: as_user.aobj_at hoare_drop_imps update_sched_context.aobj_at)+

lemma do_ipc_transfer_valid_arch[wp]:
  "\<lbrace>valid_arch_state\<rbrace>
    do_ipc_transfer s ep bg grt r \<lbrace>\<lambda>rv. valid_arch_state :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  by (rule valid_arch_state_lift_aobj_at; wp do_ipc_transfer_aobj_at)

end

lemma set_mrs_irq_handlers[wp]:
  "\<lbrace>valid_irq_handlers\<rbrace> set_mrs r t mrs \<lbrace>\<lambda>rv. valid_irq_handlers\<rbrace>"
  apply (rule set_mrs_thread_set_dmo)
   apply ((wp valid_irq_handlers_lift thread_set_caps_of_state_trivial
              ball_tcb_cap_casesI | simp)+)[1]
  apply wp
  done

lemma copy_mrs_irq_handlers[wp]:
  "\<lbrace>valid_irq_handlers\<rbrace> copy_mrs s sb r rb n \<lbrace>\<lambda>rv. valid_irq_handlers\<rbrace>"
  apply (rule copy_mrs_thread_set_dmo)
   apply ((wp valid_irq_handlers_lift thread_set_caps_of_state_trivial
              ball_tcb_cap_casesI | simp)+)[1]
  apply wp+
  done


context Ipc_AI begin

crunch irq_handlers[wp]: do_ipc_transfer "valid_irq_handlers :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps hoare_vcg_const_Ball_lift simp: zipWithM_x_mapM crunch_simps ball_conj_distrib)

crunch valid_global_objs[wp]: do_ipc_transfer "valid_global_objs :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps simp: zipWithM_x_mapM ignore: make_arch_fault_msg)

crunch vspace_objs[wp]: do_ipc_transfer "valid_vspace_objs :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps transfer_caps_loop_valid_vspace_objs simp: zipWithM_x_mapM crunch_simps)

crunch valid_global_vspace_mappings[wp]: do_ipc_transfer "valid_global_vspace_mappings :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps transfer_caps_loop_valid_vspace_objs simp: zipWithM_x_mapM crunch_simps)

crunch arch_caps[wp]: do_ipc_transfer "valid_arch_caps :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps hoare_vcg_const_Ball_lift transfer_caps_loop_valid_arch_caps
   simp: zipWithM_x_mapM crunch_simps ball_conj_distrib )

crunch ioports[wp]: do_ipc_transfer "valid_ioports :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps hoare_vcg_const_Ball_lift transfer_caps_loop_ioports
   simp: zipWithM_x_mapM crunch_simps ball_conj_distrib )

crunch v_ker_map[wp]: do_ipc_transfer "valid_kernel_mappings :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps simp: zipWithM_x_mapM crunch_simps)

crunch eq_ker_map[wp]: do_ipc_transfer "equal_kernel_mappings :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps simp: zipWithM_x_mapM crunch_simps ignore: set_object)

crunch asid_map [wp]: do_ipc_transfer "valid_asid_map :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps simp: crunch_simps)

end

declare as_user_only_idle [wp]

crunch only_idle [wp]: store_word_offs only_idle

lemma set_mrs_only_idle [wp]:
  "\<lbrace>only_idle\<rbrace> set_mrs t b m \<lbrace>\<lambda>_. only_idle\<rbrace>"
  apply (simp add: set_mrs_def split_def zipWithM_x_mapM
                   set_object_def get_object_def
              cong: option.case_cong
               del: upt.simps)
  apply (wp mapM_wp'|wpc)+
  apply (clarsimp simp del: fun_upd_apply)
  apply (erule only_idle_tcb_update)
   apply (drule get_tcb_SomeD)
   apply (fastforce simp: obj_at_def)
  by (simp add: get_tcb_rev)

context Ipc_AI begin

crunch only_idle [wp]: do_ipc_transfer "only_idle :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps simp: crunch_simps)

crunch valid_global_vspace_mappings [wp]: set_extra_badge valid_global_vspace_mappings

crunch pspace_in_kernel_window[wp]: do_ipc_transfer "pspace_in_kernel_window :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps simp: crunch_simps)

end

lemma as_user_cap_refs_in_kernel_window[wp]:
  "\<lbrace>cap_refs_in_kernel_window\<rbrace> as_user t m \<lbrace>\<lambda>rv. cap_refs_in_kernel_window\<rbrace>"
  by (wp as_user_wp_thread_set_helper ball_tcb_cap_casesI
            thread_set_cap_refs_in_kernel_window
            | simp)+

lemma as_user_cap_refs_respects_device_region[wp]:
  "\<lbrace>cap_refs_respects_device_region\<rbrace> as_user t m \<lbrace>\<lambda>rv. cap_refs_respects_device_region\<rbrace>"
  by (wp as_user_wp_thread_set_helper ball_tcb_cap_casesI
            thread_set_cap_refs_respects_device_region
            | simp)+

lemmas set_mrs_cap_refs_in_kernel_window[wp]
    = set_mrs_thread_set_dmo[OF thread_set_cap_refs_in_kernel_window
                                do_machine_op_cap_refs_in_kernel_window,
                                simplified tcb_cap_cases_def, simplified]

lemmas set_mrs_cap_refs_respects_device_region[wp]
    = set_mrs_thread_set_dmo[OF thread_set_cap_refs_respects_device_region
                                VSpace_AI.cap_refs_respects_device_region_dmo[OF storeWord_device_state_inv],
                                simplified tcb_cap_cases_def, simplified]

context Ipc_AI begin

crunch cap_refs_in_kernel_window[wp]: do_ipc_transfer "cap_refs_in_kernel_window :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps hoare_vcg_const_Ball_lift ball_tcb_cap_casesI
     simp: zipWithM_x_mapM crunch_simps ball_conj_distrib)

lemma sched_context_update_consumed_valid_objs[wp]:
 "\<lbrace>valid_objs\<rbrace> sched_context_update_consumed scp \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  by (wpsimp simp: sched_context_update_consumed_def)

crunch valid_objs[wp]: do_ipc_transfer "valid_objs :: 'state_ext state \<Rightarrow> bool"
  (wp: hoare_vcg_const_Ball_lift simp:ball_conj_distrib )

end

context Ipc_AI begin

lemma set_mrs_valid_ioc[wp]:
  "\<And>thread buf msgs.
    \<lbrace>valid_ioc :: 'state_ext state \<Rightarrow> bool\<rbrace>
      set_mrs thread buf msgs
    \<lbrace>\<lambda>_. valid_ioc\<rbrace>"
  apply (simp add: set_mrs_def)
  apply (wp | wpc)+
     apply (simp only: zipWithM_x_mapM_x split_def)
     apply (wp mapM_x_wp' set_object_valid_ioc_caps static_imp_wp
        | simp)+
  apply (clarsimp simp: obj_at_def get_tcb_def valid_ioc_def
                  split: option.splits Structures_A.kernel_object.splits)
  apply (drule spec, drule spec, erule impE, assumption)
  apply (clarsimp simp: cap_of_def tcb_cnode_map_tcb_cap_cases
                        cte_wp_at_cases null_filter_def)
  apply (simp add: tcb_cap_cases_def split: if_split_asm)
  done

crunch valid_ioc[wp]: do_ipc_transfer "valid_ioc :: 'state_ext state \<Rightarrow> bool"
  (wp: mapM_UNIV_wp)

end

lemma as_user_machine_state[wp]:
  "\<lbrace>\<lambda>s. P(machine_state s)\<rbrace> as_user r f \<lbrace>\<lambda>_. \<lambda>s. P(machine_state s)\<rbrace>"
  by (wp | simp add: as_user_def split_def)+

lemma set_mrs_def2:
  "set_mrs thread buf msgs \<equiv>
   do thread_set
        (\<lambda>tcb. tcb\<lparr>tcb_arch := arch_tcb_set_registers
                     (\<lambda>reg. if reg \<in> set (take (length msgs) msg_registers)
                           then msgs ! the_index msg_registers reg
                           else (arch_tcb_get_registers o tcb_arch) tcb reg) (tcb_arch tcb)\<rparr>)
        thread;
      remaining_msgs \<leftarrow> return (drop (length msg_registers) msgs);
      case buf of
      None \<Rightarrow> return $ nat_to_len (min (length msg_registers) (length msgs))
      | Some pptr \<Rightarrow>
          do zipWithM_x (store_word_offs pptr)
              [length msg_registers + 1..<Suc msg_max_length] remaining_msgs;
             return $ nat_to_len $ min (length msgs) msg_max_length
          od
   od"
  by (rule eq_reflection) (simp add: set_mrs_def thread_set_def bind_assoc cong: if_cong)

context Ipc_AI begin

lemma set_mrs_vms[wp]:
  notes if_split [split del]
  shows "\<And>thread buf msgs.
    \<lbrace>valid_machine_state::'state_ext state \<Rightarrow> bool\<rbrace>
      set_mrs thread buf msgs
    \<lbrace>\<lambda>_. valid_machine_state\<rbrace>"
  unfolding set_mrs_def2
  by (wpsimp simp: zipWithM_x_mapM_x split_def
               wp: mapM_x_wp_inv hoare_vcg_all_lift hoare_drop_imps)

crunch vms[wp]: do_ipc_transfer "valid_machine_state :: 'state_ext state \<Rightarrow> bool"
  (wp: mapM_UNIV_wp)

crunch valid_idle[wp]: set_message_info valid_idle

lemma copy_mrs_valid_idle [wp]:
  "\<lbrace>valid_idle :: 'state_ext state \<Rightarrow> bool\<rbrace>
   copy_mrs sender sbuf receiver rbuf n
   \<lbrace>\<lambda>rv. valid_idle\<rbrace>"
  apply (simp add: copy_mrs_redux)
  apply (wp mapM_wp' | wpc | simp add: store_word_offs_def load_word_offs_def)+
  done

lemma sched_context_update_consumed_valid_idle [wp]:
  "\<lbrace>valid_idle\<rbrace> sched_context_update_consumed scp \<lbrace>\<lambda>rv. valid_idle\<rbrace>"
  apply (simp add: sched_context_update_consumed_def)
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (wpsimp simp: sched_context_update_consumed_def update_sched_context_def set_object_def
                      get_object_def valid_idle_def obj_at_def pred_tcb_at_def)
  done

lemma make_fault_msg_valid_idle [wp]:
  "\<lbrace>valid_idle :: 'state_ext state \<Rightarrow> bool\<rbrace>
   make_fault_msg f sender
   \<lbrace>\<lambda>rv. valid_idle\<rbrace>"
  apply (case_tac f)
      apply (intro conjI | wpsimp)+
  done

lemma do_fault_transfer_valid_idle [wp]:
  "\<lbrace>valid_idle :: 'state_ext state \<Rightarrow> bool\<rbrace>
   do_fault_transfer badge sender receiver buf
   \<lbrace>\<lambda>rv. valid_idle\<rbrace>"
  by (wpsimp simp: do_fault_transfer_def set_message_info_def thread_get_def)

lemma do_ipc_transfer_valid_idle [wp]:
  "\<lbrace>valid_idle :: 'state_ext state \<Rightarrow> bool\<rbrace> do_ipc_transfer s ep bg grt r \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  unfolding do_ipc_transfer_def
  by (wpsimp simp: do_normal_transfer_def transfer_caps_def)

lemma as_user_cur_sc_tcb[wp]:
  "\<lbrace>cur_sc_tcb:: 'state_ext state \<Rightarrow> bool\<rbrace> as_user t m \<lbrace>\<lambda>rv. cur_sc_tcb\<rbrace>"
  by (wpsimp wp: as_user_wp_thread_set_helper thread_set_cur_sc_tcb)

lemma set_message_info_cur_sc_tcb [wp]:
  "\<lbrace>cur_sc_tcb :: 'state_ext state \<Rightarrow> bool\<rbrace> set_message_info thread info \<lbrace>\<lambda>rv. cur_sc_tcb\<rbrace>"
  by (wpsimp simp: set_message_info_def)

lemma copy_mrs_cur_sc_tcb [wp]:
  "\<lbrace>cur_sc_tcb :: 'state_ext state \<Rightarrow> bool\<rbrace>
   copy_mrs sender sbuf receiver rbuf n
   \<lbrace>\<lambda>rv. cur_sc_tcb\<rbrace>"
  apply (simp add: copy_mrs_redux)
  apply (wp mapM_wp' | wpc
       | simp add: store_word_offs_def load_word_offs_def)+
  done

lemma set_mrs_cur_sc_tcb[wp]:
  "\<lbrace>cur_sc_tcb\<rbrace> set_mrs param_a param_b param_c \<lbrace>\<lambda>_. cur_sc_tcb\<rbrace>"
  by (wpsimp wp: set_mrs_thread_set_dmo thread_set_cur_sc_tcb)

lemma sched_context_update_consumed_cur_sc_tcb [wp]:
  "\<lbrace>cur_sc_tcb\<rbrace> sched_context_update_consumed scp \<lbrace>\<lambda>rv. cur_sc_tcb\<rbrace>"
  apply (simp add: sched_context_update_consumed_def)
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (wpsimp simp: sched_context_update_consumed_def update_sched_context_def set_object_def
                      get_object_def cur_sc_tcb_def sc_tcb_sc_at_def obj_at_def)
  done

lemma make_fault_msg_cur_sc_tcb [wp]:
  "\<lbrace>cur_sc_tcb :: 'state_ext state \<Rightarrow> bool\<rbrace>
   make_fault_msg f sender
   \<lbrace>\<lambda>rv. cur_sc_tcb\<rbrace>"
  apply (case_tac f)
      apply (intro conjI | wpsimp)+
  done

lemma do_fault_transfer_cur_sc_tcb [wp]:
  "\<lbrace>cur_sc_tcb :: 'state_ext state \<Rightarrow> bool\<rbrace>
   do_fault_transfer badge sender receiver buf
   \<lbrace>\<lambda>rv. cur_sc_tcb\<rbrace>"
  by (wpsimp simp: do_fault_transfer_def thread_get_def)

lemma do_ipc_transfer_cur_sc_tcb[wp]:
  "\<lbrace>cur_sc_tcb and tcb_at r and tcb_at s :: 'state_ext state \<Rightarrow> bool\<rbrace>
   do_ipc_transfer s ep bg grt r
   \<lbrace>\<lambda>rv. cur_sc_tcb\<rbrace>"
  unfolding do_ipc_transfer_def
  by (wpsimp simp: do_normal_transfer_def transfer_caps_def)

lemma do_ipc_transfer_invs[wp]:
  "\<lbrace>invs and tcb_at r and tcb_at s :: 'state_ext state \<Rightarrow> bool\<rbrace>
   do_ipc_transfer s ep bg grt r
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  unfolding do_ipc_transfer_def
  apply (wpsimp simp: do_normal_transfer_def transfer_caps_def bind_assoc ball_conj_distrib
                  wp:  hoare_drop_imps get_rs_cte_at2 thread_get_wp
                       hoare_vcg_ball_lift hoare_vcg_all_lift hoare_vcg_conj_lift)
  apply (clarsimp simp: obj_at_def is_tcb invs_valid_objs)
  done

lemma dit_tcb_at [wp]:
  "\<And>t s ep bg grt r.
    \<lbrace>tcb_at t :: 'state_ext state \<Rightarrow> bool\<rbrace>
      do_ipc_transfer s ep bg grt r
    \<lbrace>\<lambda>rv. tcb_at t\<rbrace>"
  by (simp add: tcb_at_typ) wp

lemma dit_cte_at [wp]:
  "\<And>t s ep bg grt r.
    \<lbrace>cte_at t :: 'state_ext state \<Rightarrow> bool\<rbrace>
      do_ipc_transfer s ep bg grt r
    \<lbrace>\<lambda>rv. cte_at t\<rbrace>"
  by (wp valid_cte_at_typ)

end

lemma (in Ipc_AI) handle_fault_reply_typ_at[wp]:
  "\<lbrace>\<lambda>s :: 'state_ext state. P (typ_at T p s)\<rbrace> handle_fault_reply ft t label msg \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by(cases ft, simp_all, wp+)

lemma (in Ipc_AI) handle_fault_reply_tcb[wp]:
  "\<lbrace>tcb_at t' :: 'state_ext state \<Rightarrow> bool\<rbrace>
     handle_fault_reply ft t label msg
   \<lbrace>\<lambda>rv. tcb_at t'\<rbrace>"
  by (simp add: tcb_at_typ, wp)

lemma (in Ipc_AI) handle_fault_reply_cte[wp]:
  "\<lbrace>cte_at t' :: 'state_ext state \<Rightarrow> bool\<rbrace> handle_fault_reply ft t label msg \<lbrace>\<lambda>rv. cte_at t'\<rbrace>"
  by (wp valid_cte_at_typ)
(*
lemma valid_reply_caps_awaiting_reply:
  "\<lbrakk>valid_reply_caps s; kheap s t = Some (TCB tcb);
    has_reply_cap t s; tcb_state tcb = st\<rbrakk> \<Longrightarrow>
   awaiting_reply st"
  apply (simp add: valid_reply_caps_def pred_tcb_at_def)
  apply (fastforce simp: obj_at_def)
  done*)

lemmas cap_insert_typ_ats [wp] = abs_typ_at_lifts [OF cap_insert_typ_at]

context Ipc_AI begin

lemma do_ipc_transfer_non_null_cte_wp_at:
  fixes P ptr st ep b gr rt
  assumes imp: "\<And>c. P c \<Longrightarrow> \<not> is_untyped_cap c"
  shows
  "\<lbrace>valid_objs and cte_wp_at (P and ((\<noteq>) cap.NullCap)) ptr :: 'state_ext state \<Rightarrow> bool\<rbrace>
   do_ipc_transfer st ep b gr rt
   \<lbrace>\<lambda>_. cte_wp_at (P and ((\<noteq>) cap.NullCap)) ptr\<rbrace>"
  unfolding do_ipc_transfer_def
  apply (wp do_normal_transfer_non_null_cte_wp_at hoare_drop_imp hoare_allI
    | wpc | simp add:imp)+
  done

end

lemma thread_get_tcb_at:
  "\<lbrace>\<top>\<rbrace> thread_get f tptr \<lbrace>\<lambda>rv. tcb_at tptr\<rbrace>"
  unfolding thread_get_def
  by (wp, clarsimp simp add: get_tcb_ko_at tcb_at_def)

lemmas st_tcb_ex_cap' = st_tcb_ex_cap [OF _ invs_iflive]

lemma cap_delete_one_tcb_at [wp]:
  "\<lbrace>\<lambda>s. P (tcb_at p s)\<rbrace> cap_delete_one slot \<lbrace>\<lambda>_ s'. P (tcb_at p s')\<rbrace>"
  by (clarsimp simp add: tcb_at_typ, rule cap_delete_one_typ_at)

lemma cap_delete_one_ep_at [wp]:
  "\<lbrace>\<lambda>s. P (ep_at word s)\<rbrace> cap_delete_one slot \<lbrace>\<lambda>_ s'. P (ep_at word s')\<rbrace>"
  by (simp add: ep_at_typ, wp)

lemma cap_delete_one_reply_at [wp]:
  "\<lbrace>\<lambda>s. P (reply_at word s)\<rbrace> cap_delete_one slot \<lbrace>\<lambda>_ s'. P (reply_at word s')\<rbrace>"
  by (simp add: reply_at_typ, wp)

lemma cap_delete_one_ntfn_at [wp]:
  "\<lbrace>\<lambda>s. P (ntfn_at word s)\<rbrace> cap_delete_one slot \<lbrace>\<lambda>_ s'. P (ntfn_at word s')\<rbrace>"
  by (simp add: ntfn_at_typ, wp)

lemma cap_delete_one_valid_tcb_state:
  "\<lbrace>\<lambda>s. P (valid_tcb_state st s)\<rbrace> cap_delete_one slot \<lbrace>\<lambda>_ s'. P (valid_tcb_state st s')\<rbrace>"
  apply (simp add: valid_tcb_state_def)
  apply (case_tac st; simp)
         defer 4
         defer 5
         apply wpsimp+
   apply (rename_tac rp_op pl)
   apply (case_tac rp_op, wpsimp)
   apply (rule P_bool_lift[where P = P], wpsimp)
   apply (subst de_Morgan_conj)+
   apply (wpsimp wp: hoare_vcg_disj_lift)
  apply (rename_tac rp_op)
  apply (case_tac rp_op; wpsimp)
  done

lemma cte_wp_at_reply_cap_can_fast_finalise:
  "cte_wp_at ((=) (cap.ReplyCap tcb R)) slot s \<longrightarrow> cte_wp_at can_fast_finalise slot s"
  by (clarsimp simp: cte_wp_at_caps_of_state can_fast_finalise_def)

context Ipc_AI begin

crunches do_ipc_transfer
  for st_tcb_at[wp]: "\<lambda>s :: 'state_ext state. Q (st_tcb_at P t s)"
  and fault_tcb_at[wp]: "\<lambda>s :: 'state_ext state. Q (fault_tcb_at P t s)"
  and fault_tcbs_valid_states_except_set[wp]: "fault_tcbs_valid_states_except_set TS :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps transfer_caps_loop_pres rule: fault_tcbs_valid_states_lift)

end

definition
  "queue_of ep \<equiv> case ep of
     Structures_A.IdleEP \<Rightarrow> []
   | Structures_A.SendEP q \<Rightarrow> q
   | Structures_A.RecvEP q \<Rightarrow> q"


primrec
  threads_of_ntfn :: "ntfn \<Rightarrow> obj_ref list"
where
  "threads_of_ntfn (ntfn.WaitingNtfn ts) = ts"
| "threads_of_ntfn (ntfn.IdleNtfn)       = []"
| "threads_of_ntfn (ntfn.ActiveNtfn x) = []"


primrec (nonexhaustive)
  threads_of :: "Structures_A.kernel_object \<Rightarrow> obj_ref list"
where
  "threads_of (Notification x) = threads_of_ntfn (ntfn_obj x)"
| "threads_of (TCB x)           = []"
| "threads_of (Endpoint x)      = queue_of x"


(*
lemma tcb_bound_refs_eq_restr:
  "get_refs TCBBound mptr = {x. x \<in> id tcb_bound_refs mptr \<and> snd x = TCBBound}"
  by (auto dest: refs_in_tcb_bound_refs)
*)

crunches sched_context_resume
  for valid_irq_node[wp]: valid_irq_node
  (wp: crunch_wps)

crunches maybe_donate_sc
  for equal_kernel_mappings[wp]: equal_kernel_mappings
  and pspace_in_kernel_window[wp]: pspace_in_kernel_window
  and valid_arch_caps[wp]: valid_arch_caps
  and valid_arch_state[wp]: valid_arch_state
  and valid_asid_map[wp]: valid_asid_map
  and valid_global_objs[wp]: valid_global_objs
  and valid_global_vspace_mappings[wp]: valid_global_vspace_mappings
  and valid_kernel_mappings[wp]: valid_kernel_mappings
  and valid_vspace_objs[wp]: valid_vspace_objs
  and pspace_aligned[wp]: pspace_aligned
  and pspace_distinct[wp]: pspace_distinct
  and cap_refs_in_kernel_window[wp]: cap_refs_in_kernel_window
  and cap_refs_respects_device_region[wp]: cap_refs_respects_device_region
  and cur_tcb[wp]: cur_tcb
  and if_unsafe_then_cap[wp]: if_unsafe_then_cap
  and only_idle[wp]: only_idle
  and pspace_respects_device_region[wp]: pspace_respects_device_region
  and valid_global_refs[wp]: valid_global_refs
  and valid_ioc[wp]: valid_ioc
  and valid_irq_node[wp]: valid_irq_node
  and valid_irq_handlers[wp]: valid_irq_handlers
  and valid_irq_states[wp]: valid_irq_states
  and valid_machine_state[wp]: valid_machine_state
  and valid_mdb[wp]: valid_mdb
  and cte_wp_at[wp]: "cte_wp_at P c"
  and zombies_final[wp]: zombies_final
  and arch_state[wp]: "\<lambda>s. P (arch_state s)"
  and idle_thread[wp]: "\<lambda>s. P (idle_thread s)"
  and caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"
  and interrupt_irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"
  and typ_at[wp]: "\<lambda>s. P (typ_at T t s)"
  (wp: maybeM_inv crunch_wps simp: crunch_simps is_round_robin_def)

crunch typ_at[wp]: send_signal "\<lambda>s. P (typ_at T t s)"
  (wp: hoare_drop_imps maybeM_inv)

lemma gsc_ntfn_sp:
  "\<lbrace>P\<rbrace> get_ntfn_obj_ref ntfn_sc ntfnptr
   \<lbrace>\<lambda>sc s. (\<exists>ntfn. kheap s ntfnptr = Some (Notification ntfn) \<and> ntfn_sc ntfn = sc) \<and> P s\<rbrace>"
  apply (wpsimp simp: get_sk_obj_ref_def get_simple_ko_def get_object_def)
  apply auto
  done

lemma maybe_donate_sc_if_live_then_nonz_cap[wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap s \<and> ex_nonz_cap_to tptr s \<and> valid_objs s
        \<and> (\<forall>scptr ntfn. kheap s ntfnptr = Some (Notification ntfn) \<and> ntfn_sc ntfn = Some scptr
                        \<longrightarrow> ex_nonz_cap_to scptr s)\<rbrace>
   maybe_donate_sc tptr ntfnptr
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  apply (simp add: maybe_donate_sc_def)
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (case_tac sc_opt)
   apply clarsimp
   apply (rule hoare_seq_ext[OF _ gsc_ntfn_sp])
   apply (wpsimp simp: get_sc_obj_ref_def wp: maybeM_wp weak_if_wp)
  apply wpsimp
  done

lemma maybe_donate_sc_valid_idle[wp]:
  "\<lbrace>\<lambda>s. valid_idle s \<and> tptr \<noteq> idle_thread s\<rbrace> maybe_donate_sc tptr ntfnptr \<lbrace>\<lambda>rv. valid_idle\<rbrace>"
  apply (simp add: maybe_donate_sc_def)
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (case_tac sc_opt)
   apply clarsimp
   apply (rule hoare_seq_ext[OF _ gsc_ntfn_sp])
   apply (wpsimp simp: get_sc_obj_ref_def get_sched_context_def get_object_def sc_tcb_sc_at_def
                       obj_at_def
                   wp: maybeM_wp)
  apply wpsimp
  done

lemma maybe_donate_sc_valid_objs[wp]:
  "\<lbrace>valid_objs\<rbrace> maybe_donate_sc tptr ntfnptr \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  apply (simp add: maybe_donate_sc_def)
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (case_tac sc_opt)
   apply clarsimp
   apply (rule hoare_seq_ext[OF _ gsc_ntfn_sp])
   apply (wpsimp simp: get_sc_obj_ref_def pred_tcb_at_def obj_at_def is_tcb
                   wp: maybeM_wp weak_if_wp)
  apply wpsimp
  done

lemma maybe_donate_sc_ex_nonz_cap_to[wp]:
  "\<lbrace>ex_nonz_cap_to p\<rbrace> maybe_donate_sc r n \<lbrace>\<lambda>rv. ex_nonz_cap_to p\<rbrace>"
  by (wp ex_nonz_cap_to_pres)

lemma maybe_donate_sc_state_hyp_refs_of[wp]:
  "\<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace> maybe_donate_sc tcb_ptr ntfn_ptr
   \<lbrace>\<lambda>r s. P (state_hyp_refs_of s)\<rbrace>"
  by (wpsimp simp: maybe_donate_sc_def sched_context_donate_def
               wp: hoare_vcg_if_lift2 hoare_drop_imp)

lemma not_idle_tcb_in_waitingntfn:
  "kheap s ntfnptr = Some (Notification ntfn) \<Longrightarrow> ntfn_obj ntfn = WaitingNtfn q \<Longrightarrow> valid_idle s
   \<Longrightarrow> sym_refs (state_refs_of s) \<Longrightarrow> \<forall>t\<in>set q. t \<noteq> idle_thread s"
  apply (clarsimp simp: sym_refs_def)
  apply (erule_tac x = ntfnptr in allE)
  apply (erule_tac x = "(idle_thread s, NTFNSignal)" in ballE)
   apply (auto simp: state_refs_of_def valid_idle_def obj_at_def pred_tcb_at_def)
  done

lemma ex_nonz_cap_to_tcb_in_waitingntfn:
  "kheap s ntfnptr = Some (Notification ntfn) \<Longrightarrow> ntfn_obj ntfn = WaitingNtfn q \<Longrightarrow> valid_objs s
   \<Longrightarrow> sym_refs (state_refs_of s) \<Longrightarrow> if_live_then_nonz_cap s \<Longrightarrow> \<forall>t\<in>set q. ex_nonz_cap_to t s"
  apply (erule (1) valid_objsE)
  apply (clarsimp simp: valid_obj_def valid_ntfn_def)
  apply (erule_tac x = t in ballE)
   apply (clarsimp simp: sym_refs_def)
   apply (erule_tac x = ntfnptr in allE)
   apply (erule_tac x = "(t, NTFNSignal)" in ballE)
    apply (auto simp: state_refs_of_def is_tcb get_refs_def2 live_def dest!: if_live_then_nonz_capD)
  done

lemma st_in_waitingntfn:
  "kheap s ntfnptr = Some (Notification ntfn) \<Longrightarrow> ntfn_obj ntfn = WaitingNtfn q \<Longrightarrow> valid_objs s
   \<Longrightarrow> sym_refs (state_refs_of s)
   \<Longrightarrow> \<forall>t\<in>set q. st_tcb_at (\<lambda>x. x = BlockedOnNotification ntfnptr) t s"
  apply (erule (1) valid_objsE)
  apply (clarsimp simp: valid_obj_def valid_ntfn_def)
  apply (erule_tac x = t in ballE)
   apply (clarsimp simp: sym_refs_def)
   apply (erule_tac x = ntfnptr in allE)
   apply (erule_tac x = "(t, NTFNSignal)" in ballE)
    apply (auto simp: state_refs_of_def is_tcb obj_at_def pred_tcb_at_def tcb_st_refs_of_def
                      get_refs_def2
               split: thread_state.splits if_splits)
  done

crunch st_tcb_at[wp]: sched_context_resume "\<lambda>s. P (st_tcb_at P' t s)"
  (wp: crunch_wps)

crunch valid_replies_pred[wp]: refill_unblock_check "\<lambda>s.  valid_replies_pred P s"
  (wp: crunch_wps simp: crunch_simps is_round_robin_def)

lemma maybe_donate_sc_st_tcb_at[wp]:
  "maybe_donate_sc tcb_ptr ntfn_ptr \<lbrace> \<lambda>s. P (st_tcb_at P' t s) \<rbrace>"
  by (wpsimp wp: hoare_drop_imps get_sk_obj_ref_inv gbn_inv
           simp: maybe_donate_sc_def
           cong: if_cong)

lemma maybe_donate_sc_valid_replies[wp]:
  "maybe_donate_sc tcb_ptr ntfn_ptr \<lbrace> valid_replies_pred P \<rbrace>"
  by (wpsimp wp: hoare_drop_imps get_sk_obj_ref_inv gbn_inv
           simp: maybe_donate_sc_def
           cong: if_cong)

abbreviation (input) mk_ntfn_q
  where
  "mk_ntfn_q q \<equiv> case q of [] \<Rightarrow> IdleNtfn | t # q' \<Rightarrow> WaitingNtfn q"

abbreviation (input) mk_ntfn
  where
  "mk_ntfn q tcb sc \<equiv> Notification \<lparr>ntfn_obj = q, ntfn_bound_tcb = tcb, ntfn_sc = sc\<rparr>"

(* FIXME: replace the original with this stronger lemma *)
lemma tcb_at_no_sc_tcb2:
  "\<lbrakk> tcb_at x s \<rbrakk> \<Longrightarrow> (t, SCTcb) \<notin> state_refs_of s x"
  by (auto simp: state_refs_of_def obj_at_def is_tcb get_refs_def tcb_st_refs_of_def
          split: thread_state.splits option.splits if_splits)

(* FIXME: move *)
lemma sc_at_no_tcb_sc:
  "\<lbrakk> sc_at_pred_n N proj P x s \<rbrakk> \<Longrightarrow> (t, TCBSchedContext) \<notin> state_refs_of s x"
  by (auto simp: state_refs_of_def obj_at_def  get_refs_def sc_at_pred_n_def
          split: thread_state.splits option.splits if_splits)

lemma maybe_donate_sc_sym_refs:
  "\<lbrace>\<lambda>s. sym_refs (state_refs_of s)\<rbrace>
     maybe_donate_sc tcb_ptr ntfn_ptr
   \<lbrace>\<lambda>rv s. sym_refs (state_refs_of s)\<rbrace>"
  apply (simp add: maybe_donate_sc_def)
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (case_tac sc_opt; simp)
   apply (rule hoare_seq_ext[OF _ gsc_ntfn_sp])
   apply (rename_tac ntfn_sc')
   apply (case_tac ntfn_sc')
    apply (clarsimp simp: maybeM_def)
    apply wpsimp
   apply (clarsimp simp: maybeM_def)
   apply (rule hoare_seq_ext[OF _ gsct_sp])
   apply (rename_tac sc_tcb_opt)
   apply (case_tac sc_tcb_opt)
    apply (clarsimp simp: sched_context_donate_def bind_assoc)
    apply (rule hoare_seq_ext[OF _ gsct_sp])
    apply (case_tac x)
     apply wpsimp
     apply (fastforce simp: state_refs_of_def obj_at_def get_refs_def2 pred_tcb_at_def
                            sc_tcb_sc_at_def
                     elim!: delta_sym_refs
                     split: if_splits)
    apply (wpsimp simp: sc_tcb_sc_at_def obj_at_def)
   apply wpsimp
  apply wpsimp
  done

crunches maybe_donate_sc
  for cur_sc_tcb[wp]: cur_sc_tcb
  and fault_tcbs_valid_states[wp]: fault_tcbs_valid_states
  (wp: crunch_wps simp: crunch_simps is_round_robin_def)

lemma maybe_donate_sc_invs[wp]:
  "\<lbrace>\<lambda>s. invs s \<and> ex_nonz_cap_to tcb_ptr s\<rbrace> maybe_donate_sc tcb_ptr ntfn_ptr \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                  wp: maybe_donate_sc_sym_refs valid_ioports_lift)
  apply safe
   apply (clarsimp simp: sym_refs_def)
   apply (erule_tac x = ntfn_ptr in allE)
   apply (erule (1) valid_objsE)
   apply (clarsimp simp: valid_obj_def valid_ntfn_def is_sc_obj_def obj_at_def)
   apply (erule (1) if_live_then_nonz_capD2)
   apply (case_tac ko; simp)
   apply (clarsimp simp: state_refs_of_def get_refs_def2 live_def live_sc_def)
  apply (clarsimp simp: idle_no_ex_cap)
  done

lemma set_thread_state_not_BOReply_valid_replies:
  "\<lbrace>valid_replies and st_tcb_at (\<lambda>st. \<not> is_blocked_on_reply st) t\<rbrace>
   set_thread_state t st
   \<lbrace>\<lambda>r. valid_replies\<rbrace>"
  apply (wpsimp wp: sts_valid_replies)
  apply (clarsimp simp: valid_replies_2_def replies_blocked_upd_tcb_st_def image_def)
  apply (subgoal_tac "a \<in> {y. \<exists>x\<in>replies_blocked s. y = fst x}"; clarsimp)
   apply (subgoal_tac "ba \<noteq> t";
          fastforce simp: replies_blocked_def pred_tcb_at_def obj_at_def)
  apply fastforce
  done

lemma update_waiting_invs:
  "\<lbrace>\<lambda>s. invs s \<and> (\<exists>ntfn. ko_at (Notification ntfn) ntfnptr s
        \<and> ntfn_obj ntfn = WaitingNtfn q \<and> ntfn_bound_tcb ntfn = bound_tcb \<and> ntfn_sc ntfn = sc)
        \<and> (bound sc \<longrightarrow> ex_nonz_cap_to (the sc) s)\<rbrace>
   update_waiting_ntfn ntfnptr q bound_tcb sc bdg
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  supply if_split[split del] if_cong[cong]
  apply (simp add: update_waiting_ntfn_def)
  apply (rule hoare_seq_ext[OF _ assert_sp])
  apply wpsimp
    apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                    wp: sts_valid_replies sts_only_idle sts_fault_tcbs_valid_states)
   apply (wpsimp wp: valid_ioports_lift)
  apply (simp add: invs_def valid_state_def valid_pspace_def obj_at_def)
  apply (clarsimp simp: not_idle_tcb_in_waitingntfn ex_nonz_cap_to_tcb_in_waitingntfn cong: conj_cong)
  apply (cases q; simp)
  apply (erule (1) pspace_valid_objsE; clarsimp simp: valid_obj_def valid_ntfn_def)
  apply (rule conjI, fastforce simp: valid_ntfn_def split: option.splits list.splits)
  apply (rule conjI, fastforce simp: live_def live_ntfn_def elim!: if_live_then_nonz_capD2)
  apply (rule conjI)
   apply (rename_tac t q')
   apply (frule_tac x=t in bspec[OF st_in_waitingntfn], assumption+, simp)
   apply (clarsimp simp: obj_at_def is_tcb pred_tcb_at_def)
   apply (subst replies_blocked_upd_tcb_st_not_BlockedonReply, simp+)
  apply (rule conjI)
   apply (frule (3) st_in_waitingntfn)
   apply (clarsimp elim!: fault_tcbs_valid_states_not_fault_tcb_states
                          pred_tcb_weakenE
                    simp: pred_neg_def)
  apply (rule delta_sym_refs, assumption)
   apply (fastforce simp: state_refs_of_def get_refs_def2 st_tcb_at_def obj_at_def
                   split: if_splits list.splits)
  apply (frule_tac x=a in bspec[OF st_in_waitingntfn], assumption+, simp)
  apply (clarsimp simp: get_refs_def2 state_refs_of_def
                  split: if_splits list.splits option.splits)
         apply ((clarsimp simp: is_tcb obj_at_def)+)[3]
      apply (clarsimp simp: is_tcb obj_at_def)
      apply (subgoal_tac "tp = TCBSignal \<and> y = ntfnptr", clarsimp)
      apply (elim disjE;
             clarsimp simp: tcb_st_refs_of_def st_tcb_at_def obj_at_def
                     dest!: refs_in_get_refs)
     apply (clarsimp simp: is_tcb obj_at_def)
     apply (subgoal_tac "tp = TCBSignal \<and> y = ntfnptr", clarsimp)
     apply (elim disjE;
            clarsimp simp: tcb_st_refs_of_def st_tcb_at_def obj_at_def
                    dest!: refs_in_get_refs)
    apply (elim disjE; clarsimp simp: is_tcb obj_at_def)+
  done

lemma not_idle_tcb_in_SendEp:
  "\<lbrakk> kheap s ptr = Some (Endpoint (SendEP q)); valid_idle s; sym_refs (state_refs_of s); t\<in>set q \<rbrakk>
  \<Longrightarrow> t \<noteq> idle_thread s"
  apply (clarsimp simp: sym_refs_def)
  apply (erule_tac x = ptr in allE)
  apply (drule_tac x = "(idle_thread s, EPSend)" in bspec)
   apply (auto simp: state_refs_of_def valid_idle_def obj_at_def pred_tcb_at_def)
  done

lemma not_idle_tcb_in_RecvEp:
  "\<lbrakk> kheap s ptr = Some (Endpoint (RecvEP q)); valid_idle s; sym_refs (state_refs_of s); t\<in>set q \<rbrakk>
  \<Longrightarrow> t \<noteq> idle_thread s"
  apply (clarsimp simp: sym_refs_def)
  apply (erule_tac x = ptr in allE)
  apply (drule_tac x = "(idle_thread s, EPRecv)" in bspec)
   apply (auto simp: state_refs_of_def valid_idle_def obj_at_def pred_tcb_at_def)
  done

(* FIXME: remove from all arches. *)
lemma cancel_ipc_ex_nonz_tcb_cap:
  "\<lbrace>\<lambda>s. \<exists>ptr. cte_wp_at ((=) (cap.ThreadCap p)) ptr s\<rbrace>
     cancel_ipc t
   \<lbrace>\<lambda>rv. ex_nonz_cap_to p\<rbrace>"
  apply (simp add: ex_nonz_cap_to_def cte_wp_at_caps_of_state
              del: split_paired_Ex)
  apply (wp cancel_ipc_caps_of_state)
  apply (clarsimp simp del: split_paired_Ex split_paired_All)
   apply (rule_tac x="(a, b)" in exI)
   apply (clarsimp simp: cte_wp_at_caps_of_state can_fast_finalise_def)
  done


lemma valid_cap_tcb_at_tcb_or_zomb:
  "\<lbrakk> s \<turnstile> cap; t \<in> obj_refs cap; tcb_at t s \<rbrakk>
       \<Longrightarrow> is_thread_cap cap \<or> is_zombie cap"
  by (rule obj_ref_is_tcb)

lemma cancel_ipc_cap_to:
  "\<lbrace>ex_nonz_cap_to p\<rbrace> cancel_ipc t \<lbrace>\<lambda>rv. ex_nonz_cap_to p\<rbrace>"
  by (wpsimp wp: cancel_ipc_caps_of_state
           simp: ex_nonz_cap_to_def cte_wp_at_caps_of_state
       simp_del: split_paired_Ex)

(* FIXME: remove from all arches. *)
lemma cancel_ipc_ex_nonz_cap_to_tcb:
  "\<lbrace>\<lambda>s. ex_nonz_cap_to p s \<and> valid_objs s \<and> tcb_at p s\<rbrace>
     cancel_ipc t
   \<lbrace>\<lambda>rv. ex_nonz_cap_to p\<rbrace>"
  by (wpsimp wp: cancel_ipc_cap_to)


lemma cancel_ipc_simple2:
  "\<lbrace>K (\<forall>st. simple st \<longrightarrow> P st)\<rbrace>
     cancel_ipc t
   \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  apply (rule hoare_assume_pre)
  apply (rule hoare_chain, rule cancel_ipc_simple, simp_all)
  apply (clarsimp simp: st_tcb_def2)
  apply fastforce
  done

lemma cancel_ipc_cte_wp_at_not_reply_state:
  "\<lbrace>\<lambda>s. st_tcb_at (Not \<circ> is_blocked_on_reply) t s \<and> cte_wp_at P p s\<rbrace>
    cancel_ipc t
   \<lbrace>\<lambda>r. cte_wp_at P p\<rbrace>"
  apply (simp add: cancel_ipc_def)
  apply (wpsimp wp: thread_set_cte_wp_at_trivial ball_tcb_cap_casesI gts_wp)
  done

lemma cancel_ipc_simpler:
  "\<lbrace>\<lambda>s. sym_refs (state_refs_of s) \<and> valid_objs s \<and> t \<noteq> idle_thread s \<and>
        only_idle s\<rbrace>
   cancel_ipc t
   \<lbrace>\<lambda>_. st_tcb_at (\<lambda>st. st \<in> {Running, Inactive, Restart}) t\<rbrace>"
  apply (clarsimp simp: cancel_ipc_def)
  apply (rule hoare_seq_ext [OF _ gts_sp])
  apply (wpsimp wp: hoare_strengthen_post [OF blocked_cancel_ipc_inactive]
                    hoare_strengthen_post [OF reply_remove_tcb_inactive]
                    hoare_strengthen_post [OF cancel_signal_inactive]
                    thread_set_no_change_tcb_pred hoare_vcg_imp_lift |
         clarsimp simp: only_idle_def st_tcb_at_def obj_at_def)+
  done

crunches blocked_cancel_ipc, reply_remove_tcb, cancel_signal
  for fault_tcb_at[wp]: "fault_tcb_at P t"
  (wp: thread_set_pred_tcb_at_sets_true crunch_wps)

lemma cancel_ipc_fault_tcb_at_None[wp]:
  "\<lbrace>\<lambda>s. t \<noteq> t' \<longrightarrow> fault_tcb_at ((=) None) t s\<rbrace>
   cancel_ipc t'
   \<lbrace>\<lambda>_. fault_tcb_at ((=) None) t\<rbrace>"
  apply (simp add: cancel_ipc_def)
  by (wpsimp wp: hoare_vcg_imp_lift thread_set_pred_tcb_at_sets_true gts_wp)

lemma sai_invs[wp]:
  "\<lbrace>invs and ex_nonz_cap_to ntfnptr\<rbrace> send_signal ntfnptr bdg \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: send_signal_def)
  apply (rule hoare_seq_ext [OF _ get_simple_ko_sp])
  apply (case_tac "ntfn_obj ntfn"; simp)
    apply (case_tac "ntfn_bound_tcb ntfn"; simp)
     apply (wp set_ntfn_minor_invs)
     apply (fastforce simp: obj_at_def invs_def valid_pspace_def valid_state_def valid_obj_def
                            valid_ntfn_def)
    apply (rename_tac tptr)
    apply (rule hoare_seq_ext[OF _ gts_sp])
    apply (case_tac "receive_blocked st"; simp)
     apply (clarsimp simp: receive_blocked_def)
     apply (case_tac st; simp)
     apply (wpsimp wp: sts_invs_minor2)
      apply (rule hoare_vcg_conj_lift)
       apply (rule hoare_strengthen_post[OF cancel_ipc_simpler])
       apply (clarsimp simp: st_tcb_at_def obj_at_def)
       apply (case_tac "tcb_state tcb"; simp)
      apply (wpsimp wp: cancel_ipc_cap_to)
     apply (clarsimp simp: invs_def valid_state_def valid_pspace_def)
     apply (subgoal_tac "ex_nonz_cap_to tptr s")
      apply (fastforce simp: st_tcb_def2 is_tcb idle_no_ex_cap pred_neg_def
                      elim!: fault_tcbs_valid_states_not_fault_tcb_states
                             pred_tcb_weakenE)
     apply (clarsimp simp: pred_tcb_at_def obj_at_def)
     apply (fastforce simp: live_def receive_blocked_def intro!: if_live_then_nonz_capD2)
    apply (wpsimp simp: invs_def valid_state_def valid_pspace_def wp: valid_ioports_lift)
    apply (rule valid_objsE[where x=ntfnptr], assumption, fastforce simp: obj_at_def)
    apply (clarsimp simp: valid_obj_def valid_ntfn_def)
    apply (fastforce simp: valid_obj_def valid_ntfn_def state_refs_of_def obj_at_def
                    elim!: delta_sym_refs
                    split: if_splits)
   apply (wpsimp simp: obj_at_def invs_def valid_state_def valid_pspace_def
                   wp: update_waiting_invs)
   apply (erule (1) valid_objsE)
   apply (clarsimp simp: valid_obj_def valid_ntfn_def sc_at_typ2 obj_at_def)
   apply (erule (1) if_live_then_nonz_capD2)
   apply (clarsimp simp: live_def live_sc_def
                  dest!: sym_refs_ko_atD[unfolded obj_at_def, simplified])
   apply fastforce
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def wp: valid_ioports_lift)
  apply (fastforce simp: valid_obj_def valid_ntfn_def state_refs_of_def obj_at_def
                  elim!: delta_sym_refs
                  split: if_splits)
  done

lemma ncof_invs [wp]:
  "\<lbrace>invs\<rbrace> null_cap_on_failure (lookup_cap t ref) \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (simp add: null_cap_on_failure_def | wp)+


lemma ncof_is_a_catch:
  "null_cap_on_failure m = (m <catch> (\<lambda>e. return Structures_A.NullCap))"
  apply (simp add: null_cap_on_failure_def liftM_def catch_def)
  apply (rule bind_cong [OF refl])
  apply (case_tac v, simp_all)
  done


lemma recv_ep_distinct:
  assumes inv: "invs s"
  assumes ep: "obj_at (\<lambda>k. k = Endpoint (Structures_A.endpoint.RecvEP
                                           q)) word1 s"
  shows "distinct q" using assms
  apply -
  apply (drule invs_valid_objs)
  apply (erule(1) obj_at_valid_objsE)
  apply (clarsimp simp: valid_obj_def valid_ep_def)
  done

lemma rfk_invs: "\<lbrace>invs and tcb_at t\<rbrace> reply_from_kernel t r \<lbrace>\<lambda>rv. invs\<rbrace>"
  unfolding reply_from_kernel_def by (cases r; wpsimp)

lemma st_tcb_at_valid_st:
  "\<lbrakk> invs s ; tcb_at t s ; st_tcb_at ((=) st) t s \<rbrakk> \<Longrightarrow> valid_tcb_state st s"
  apply (clarsimp simp add: invs_def valid_state_def valid_pspace_def
                  valid_objs_def tcb_at_def get_tcb_def pred_tcb_at_def
                  obj_at_def)
  apply (drule_tac x=t in bspec)
   apply (erule domI)
  apply (simp add: valid_obj_def valid_tcb_def)
  done

lemma gts_eq_ts:
  "\<lbrace> tcb_at thread \<rbrace> get_thread_state thread \<lbrace>\<lambda>rv. st_tcb_at ((=) rv) thread \<rbrace>"
  apply (rule hoare_strengthen_post)
   apply (rule gts_sp)
  apply (clarsimp simp add: pred_tcb_at_def obj_at_def)
  done

declare lookup_cap_valid [wp]

definition
  "pspace_clear t s \<equiv> s \<lparr> kheap := (kheap s) (t := None) \<rparr>"

lemma pred_tcb_at_update1:
  "x \<noteq> t \<Longrightarrow> pred_tcb_at proj P x (s\<lparr>kheap := (kheap s)(t := v)\<rparr>) = pred_tcb_at proj P x s"
  by (simp add: pred_tcb_at_def obj_at_def)

lemma pred_tcb_at_update2:
  "pred_tcb_at proj P t (s\<lparr>kheap := (kheap s)(t \<mapsto> TCB tcb)\<rparr>) = P (proj (tcb_to_itcb tcb))"
  by (simp add: pred_tcb_at_def obj_at_def)

lemma pred_tcb_clear:
  "pred_tcb_at proj P t (pspace_clear t' s) = (t \<noteq> t' \<and> pred_tcb_at proj P t s)"
  by (simp add: pred_tcb_at_def obj_at_def pspace_clear_def)

lemma pred_tcb_upd_apply:
  "pred_tcb_at proj P t (s\<lparr>kheap := kheap s(r \<mapsto> TCB v)\<rparr>) =
  (if t = r then P (proj (tcb_to_itcb v)) else pred_tcb_at proj P t s)"
  by (simp add: pred_tcb_at_def obj_at_def)

lemmas (in Ipc_AI) transfer_caps_loop_cap_to[wp]
  = transfer_caps_loop_pres [OF cap_insert_ex_cap]

crunch cap_to[wp]: set_extra_badge "ex_nonz_cap_to p"

context Ipc_AI begin

crunch cap_to[wp]: do_ipc_transfer "ex_nonz_cap_to p :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps simp: zipWithM_x_mapM ignore: transfer_caps_loop)

crunches complete_signal, receive_ipc
  for it[wp]:  "\<lambda>s::'state_ext state. P (idle_thread s)"
  (wp: crunch_wps hoare_vcg_all_lift simp: crunch_simps)

end

lemma schedule_tcb_Pmdb[wp]: "\<lbrace>\<lambda>s. P (cdt s)\<rbrace> schedule_tcb param_a \<lbrace>\<lambda>_ s. P (cdt s)\<rbrace>"
  by (wpsimp simp: schedule_tcb_def)

lemma same_caps_tcb_upd_state[simp]:
 "same_caps (TCB (tcb \<lparr>tcb_state := BlockedOnReply r\<rparr>)) = same_caps (TCB tcb)"
 apply (rule ext)
 apply (simp add:tcb_cap_cases_def)
 done

lemma same_caps_simps[simp]:
 "same_caps (CNode sz cs)  = (\<lambda>val. val = CNode sz cs)"
 "same_caps (TCB tcb)      = (\<lambda>val. (\<exists>tcb'. val = TCB tcb'
                                         \<and> (\<forall>(getF, t) \<in> ran tcb_cap_cases. getF tcb' = getF tcb)))"
 "same_caps (Endpoint ep)  = (\<lambda>val. is_ep val)"
 "same_caps (Notification ntfn) = (\<lambda>val. is_ntfn val)"
 "same_caps (Reply rply)  = (\<lambda>val. is_reply val)"
 "same_caps (SchedContext sc n)  = (\<lambda>val. \<exists>sc'. val = SchedContext sc' n)"
 "same_caps (ArchObj ao)   = (\<lambda>val. (\<exists>ao'. val = ArchObj ao'))"
 apply (rule ext)
 apply (case_tac val, (fastforce simp: is_obj_defs)+)+
 done

lemma tcb_at_cte_at_2:
  "tcb_at tcb s \<Longrightarrow> cte_at (tcb, tcb_cnode_index 2) s"
  by (auto simp: obj_at_def cte_at_cases is_tcb)

lemma tcb_at_cte_at_3:
  "tcb_at tcb s \<Longrightarrow> cte_at (tcb, tcb_cnode_index 3) s"
  by (auto simp: obj_at_def cte_at_cases is_tcb)

lemma tcb_at_cte_at_4:
  "tcb_at tcb s \<Longrightarrow> cte_at (tcb, tcb_cnode_index 4) s"
  by (auto simp: obj_at_def cte_at_cases is_tcb)

context Ipc_AI begin
crunch valid_irq_states[wp]: do_ipc_transfer "valid_irq_states :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps  simp: crunch_simps)

crunch cap_refs_respects_device_region[wp]: do_fault_transfer "cap_refs_respects_device_region :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps hoare_vcg_const_Ball_lift
    VSpace_AI.cap_refs_respects_device_region_dmo ball_tcb_cap_casesI
    const_on_failure_wp simp: crunch_simps zipWithM_x_mapM ball_conj_distrib)

crunch cap_refs_respects_device_region[wp]: copy_mrs "cap_refs_respects_device_region"
  (wp: crunch_wps hoare_vcg_const_Ball_lift
    VSpace_AI.cap_refs_respects_device_region_dmo ball_tcb_cap_casesI
    const_on_failure_wp simp: crunch_simps zipWithM_x_mapM ball_conj_distrib)

crunch cap_refs_respects_device_region[wp]: get_receive_slots "cap_refs_respects_device_region"
  (wp: crunch_wps hoare_vcg_const_Ball_lift
    VSpace_AI.cap_refs_respects_device_region_dmo ball_tcb_cap_casesI
    const_on_failure_wp simp: crunch_simps zipWithM_x_mapM )



lemma invs_respects_device_region:
  "invs s \<Longrightarrow> cap_refs_respects_device_region s \<and> pspace_respects_device_region s"
  by (clarsimp simp: invs_def valid_state_def)

end

locale Ipc_AI_cont = Ipc_AI state_ext_t
  for state_ext_t :: "'state_ext::state_ext itself" +
  assumes do_ipc_transfer_pspace_respects_device_region[wp]:
    "\<And> t ep bg grt r.
      \<lbrace>pspace_respects_device_region :: 'state_ext state \<Rightarrow> bool\<rbrace>
      do_ipc_transfer t ep bg grt r
      \<lbrace>\<lambda>rv. pspace_respects_device_region\<rbrace>"
  assumes do_ipc_transfer_cap_refs_respects_device_region[wp]:
    "\<And> t ep bg grt r.
      \<lbrace>cap_refs_respects_device_region and tcb_at t and  valid_objs and valid_mdb\<rbrace>
      do_ipc_transfer t ep bg grt r
      \<lbrace>\<lambda>rv. cap_refs_respects_device_region :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes do_ipc_transfer_state_hyp_refs_of[wp]:
   "\<lbrace>\<lambda>s::'state_ext state. P (state_hyp_refs_of s)\<rbrace>
    do_ipc_transfer t ep bg grt r
    \<lbrace>\<lambda>_ s::'state_ext state. P (state_hyp_refs_of s)\<rbrace>"


lemma complete_signal_invs:
  "\<lbrace>invs and tcb_at tcb and ex_nonz_cap_to tcb\<rbrace> complete_signal ntfnptr tcb \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: complete_signal_def)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (case_tac "ntfn_obj ntfn"; simp)
  apply (subst bind_assoc[symmetric])
  apply (rule_tac B="\<lambda>_. invs and ex_nonz_cap_to tcb" in hoare_seq_ext[rotated])
   apply (wpsimp simp: as_user_def set_object_def get_object_def wp: set_ntfn_minor_invs)
   apply safe
      apply (clarsimp simp: obj_at_def is_tcb)
     apply (fastforce simp: invs_def valid_state_def valid_pspace_def valid_bound_obj_def
                            valid_obj_def valid_ntfn_def is_tcb obj_at_def is_sc_obj_def
                     elim!: valid_objsE
                     split: option.splits)
    apply (fastforce simp: invs_def valid_state_def valid_pspace_def live_def live_ntfn_def
                           tcb_cap_cases_def
                   intro!: ex_cap_to_after_update
                    elim!: if_live_then_nonz_capD)+
  apply (rule hoare_seq_ext_skip, solves wpsimp)+
  apply wpsimp
  done

crunch ntfn_at[wp]: set_message_info "ntfn_at ntfn"

crunch arch[wp]: set_message_info "\<lambda>s. P (arch_state s)"
  (wp: crunch_wps simp: crunch_simps)

lemma set_message_info_valid_arch [wp]:
  "\<lbrace>valid_arch_state\<rbrace> set_message_info a b \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  apply (rule valid_arch_state_lift_aobj_at; wp?)
  unfolding set_message_info_def
  apply (wp as_user.aobj_at)
  done

crunch caps[wp]: set_message_info "\<lambda>s. P (caps_of_state s)"

crunch irq_node[wp]: set_message_info "\<lambda>s. P (interrupt_irq_node s)"
  (simp: crunch_simps)

lemma set_message_info_global_refs [wp]:
  "\<lbrace>valid_global_refs\<rbrace> set_message_info a b \<lbrace>\<lambda>_. valid_global_refs\<rbrace>"
  by (rule valid_global_refs_cte_lift; wp)

crunch irq_node[wp]: set_mrs "\<lambda>s. P (interrupt_irq_node s)"
  (wp: crunch_wps simp: crunch_simps)

crunch interrupt_states[wp]: set_message_info "\<lambda>s. P (interrupt_states s)"
  (simp: crunch_simps )

crunch interrupt_states[wp]: set_mrs "\<lambda>s. P (interrupt_states s)"
  (simp: crunch_simps wp: crunch_wps)

lemma tcb_cap_cases_tcb_context:
  "\<forall>(getF, v)\<in>ran tcb_cap_cases.
         getF (tcb_arch_update (arch_tcb_context_set F) tcb) = getF tcb"
  by (rule ball_tcb_cap_casesI, simp+)

crunch valid_arch_caps[wp]: set_message_info "valid_arch_caps"

lemma valid_bound_tcb_exst[iff]:
 "valid_bound_tcb t (trans_state f s) = valid_bound_tcb t s"
  by (auto simp: valid_bound_obj_def split:option.splits)

crunch bound_tcb[wp]: set_message_info, set_mrs "valid_bound_tcb t"
(wp: valid_bound_tcb_typ_at set_object_typ_at mapM_wp ignore: set_object
 simp: zipWithM_x_mapM)

lemma pspace_clear_update1:
  "t \<noteq> t' \<Longrightarrow>
  pspace_clear t' (s\<lparr>kheap := (kheap s)(t := v)\<rparr>) =
  (pspace_clear t' s) \<lparr>kheap := (kheap (pspace_clear t' s))(t := v)\<rparr>"
  apply (simp add: pspace_clear_def)
  apply (cases s)
  apply simp
  apply (simp add: fun_upd_twist)
  done


lemma pspace_clear_update2:
  "pspace_clear t' (s\<lparr>kheap := (kheap s)(t' := v)\<rparr>) = pspace_clear t' s"
  by (simp add: pspace_clear_def)


lemmas pspace_clear_update = pspace_clear_update1 pspace_clear_update2


lemma clear_revokable [iff]:
  "pspace_clear t (is_original_cap_update f s) = is_original_cap_update f (pspace_clear t s)"
  by (simp add: pspace_clear_def)


lemma maybe_return_sc_cap_to[wp]:
  "\<lbrace>ex_nonz_cap_to p\<rbrace> maybe_return_sc ntfn_ptr tcb_ptr \<lbrace>\<lambda>_. ex_nonz_cap_to p\<rbrace>"
  supply if_cong[cong]
  apply (wpsimp simp: maybe_return_sc_def set_tcb_obj_ref_def set_object_def get_tcb_obj_ref_def
                      thread_get_def get_sk_obj_ref_def get_simple_ko_def get_object_def)
  apply (auto simp: tcb_cap_cases_def intro!: ex_cap_to_after_update)
  done

lemma schedule_tcb_cap_to[wp]:
  "\<lbrace>ex_nonz_cap_to p\<rbrace> schedule_tcb param_a \<lbrace>\<lambda>_. ex_nonz_cap_to p\<rbrace>"
  by (wpsimp simp: schedule_tcb_def)

crunches complete_signal, do_nbrecv_failed_transfer, reply_push, receive_signal
  for cap_to[wp]: "ex_nonz_cap_to p"
  and typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  (ignore: set_object set_tcb_obj_ref
       wp: cap_insert_ex_cap hoare_drop_imps crunch_wps maybeM_inv
     simp: crunch_simps)

crunches get_endpoint
  for inv[wp]: "P"

context Ipc_AI begin

lemma hoare_drop_imp_under_All:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. \<forall>x. Q rv s x\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. \<forall>x. D rv s x \<longrightarrow> Q rv s x\<rbrace>"
  by (auto elim: hoare_strengthen_post)

lemma receive_ipc_cap_to[wp]:
  "receive_ipc thread cap is_blocking reply_cap \<lbrace>ex_nonz_cap_to p :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  supply if_cong[cong]
  by (wpsimp simp: receive_ipc_def
               wp: hoare_drop_imps fail_wp cancel_ipc_cap_to hoare_drop_imp_under_All)

end

crunch ex_nonz_cap_to[wp]: set_message_info "ex_nonz_cap_to p"

lemmas is_derived_not_Null = derived_not_Null(1)

crunch mdb[wp]: set_message_info valid_mdb
  (wp: select_wp crunch_wps mapM_wp')

lemma ep_queue_cap_to:
  "\<lbrakk> ko_at (Endpoint ep) p s; invs s;
     \<lbrakk> live (Endpoint ep) \<longrightarrow> queue_of ep \<noteq> [] \<rbrakk>
        \<Longrightarrow> t \<in> set (queue_of ep) \<rbrakk>
     \<Longrightarrow> ex_nonz_cap_to t s"
  apply (frule sym_refs_ko_atD, fastforce)
  apply (erule obj_at_valid_objsE, fastforce)
  apply (clarsimp simp: valid_obj_def)
  apply (cases ep, simp_all add: queue_of_def valid_ep_def live_def
                                 st_tcb_at_refs_of_rev)
   apply (drule(1) bspec)
   apply (erule st_tcb_ex_cap, clarsimp+)
  apply (drule(1) bspec)
  apply (erule st_tcb_ex_cap, clarsimp+)
  done

crunch pred_tcb_at[wp]: set_message_info "pred_tcb_at proj P t"

lemma reschedule_required_pred_tcb_at:
  "\<lbrace>pred_tcb_at proj P t\<rbrace> reschedule_required \<lbrace>\<lambda>rv. pred_tcb_at proj P t\<rbrace>"
  supply if_cong[cong]
  by (wpsimp simp: reschedule_required_def set_scheduler_action_def tcb_sched_action_def
                   set_tcb_queue_def get_tcb_queue_def thread_get_def
             wp: hoare_drop_imps is_schedulable_wp)

lemma schedule_tcb_pred_tcb_at:
  "\<lbrace>pred_tcb_at proj P t'\<rbrace> schedule_tcb t \<lbrace>\<lambda>rv. pred_tcb_at proj P t'\<rbrace>"
  by (wpsimp simp: schedule_tcb_def wp: reschedule_required_pred_tcb_at)

lemma maybe_return_sc_pred_tcb_at:
  "\<lbrace>pred_tcb_at proj P tcb_ptr' and K (tcb_ptr \<noteq> tcb_ptr')\<rbrace> maybe_return_sc ntfn_ptr tcb_ptr
   \<lbrace>\<lambda>rv. pred_tcb_at proj P tcb_ptr'\<rbrace>"
  apply (wpsimp simp: maybe_return_sc_def set_tcb_obj_ref_def set_object_def
                      get_tcb_obj_ref_def thread_get_def get_sk_obj_ref_def get_simple_ko_def
                      get_object_def)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  done

crunch pred_tcb_at[wp]: sched_context_resume, refill_unblock_check "pred_tcb_at proj P tcb_ptr"
  (wp: crunch_wps simp: crunch_simps is_round_robin_def)

lemma maybe_donate_sc_pred_tcb_at:
  "\<lbrace>pred_tcb_at proj P tcb_ptr' and K (tcb_ptr \<noteq> tcb_ptr')\<rbrace> maybe_donate_sc tcb_ptr ntfn_ptr
   \<lbrace>\<lambda>rv. pred_tcb_at proj P tcb_ptr'\<rbrace>"
  apply (simp add: maybe_donate_sc_def)
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (case_tac sc_opt; simp)
   apply (rule hoare_seq_ext[OF _ gsc_ntfn_sp])
   apply (simp add: maybeM_def)
   apply (case_tac x; simp)
    apply wpsimp
   apply (rule hoare_seq_ext[OF _ gsct_sp])
   apply (rename_tac sc_tcb_opt)
   apply (case_tac sc_tcb_opt; simp)
    apply (wpsimp simp: sched_context_donate_def set_tcb_obj_ref_def set_object_def tcb_release_remove_def
                        update_sched_context_def get_object_def get_tcb_def
                        pred_tcb_at_def obj_at_def get_sc_obj_ref_def get_sched_context_def
                        tcb_sched_action_def set_tcb_queue_def get_tcb_queue_def
                    wp: hoare_vcg_imp_lift hoare_vcg_all_lift)
    apply (fastforce simp: sc_tcb_sc_at_def obj_at_def)
   apply wpsimp
  apply wpsimp
  done

lemma rai_pred_tcb_neq:
  "\<lbrace>pred_tcb_at proj P t' and K (t \<noteq> t')\<rbrace> receive_signal t cap is_blocking
   \<lbrace>\<lambda>rv. pred_tcb_at proj P t'\<rbrace>"
  apply (simp add: receive_signal_def)
  apply (case_tac cap; simp)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (case_tac "ntfn_obj x"; simp)
    apply (case_tac is_blocking; simp)
     apply (wpsimp wp: schedule_tcb_pred_tcb_at maybe_return_sc_pred_tcb_at sts_st_tcb_at_neq)
    apply (wpsimp simp: do_nbrecv_failed_transfer_def)
   apply (case_tac is_blocking; simp)
    apply (wpsimp wp: schedule_tcb_pred_tcb_at maybe_return_sc_pred_tcb_at sts_st_tcb_at_neq)
   apply (wpsimp simp: do_nbrecv_failed_transfer_def)
  apply (wpsimp wp: maybe_donate_sc_pred_tcb_at)
  done

context Ipc_AI begin
crunch ct[wp]: set_mrs "\<lambda>s::'state_ext state. P (cur_thread s)"
  (wp: case_option_wp mapM_wp simp: crunch_simps)
end

crunches receive_signal
  for typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  (ignore: set_object set_tcb_obj_ref
       wp: cap_insert_ex_cap hoare_drop_imps crunch_wps maybeM_inv
     simp: crunch_simps)


context Ipc_AI begin

lemma receive_ipc_typ_at[wp]:
  "\<lbrace>\<lambda>s::'state_ext state. P (typ_at T p s)\<rbrace> receive_ipc thread cap is_blocking reply_cap \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  by (wpsimp simp: receive_ipc_def wp: hoare_drop_imps hoare_drop_imp_under_All)

lemma ri_tcb [wp]:
  "\<lbrace>tcb_at t' :: 'state_ext state \<Rightarrow> bool\<rbrace>
    receive_ipc t cap is_blocking r
   \<lbrace>\<lambda>rv. tcb_at t'\<rbrace>"
  by (simp add: tcb_at_typ, wp)

end

lemma rai_tcb [wp]:
  "\<lbrace>tcb_at t'\<rbrace> receive_signal t cap is_blocking \<lbrace>\<lambda>rv. tcb_at t'\<rbrace>"
  by (simp add: tcb_at_typ) wp

context Ipc_AI begin

lemmas transfer_caps_loop_pred_tcb_at[wp] =
    transfer_caps_loop_pres [OF cap_insert_pred_tcb_at]

end

lemma ep_ntfn_cap_case_helper:
  "(case x of cap.EndpointCap ref bdg r \<Rightarrow> P ref bdg r
           |  cap.NotificationCap ref bdg r \<Rightarrow> Q ref bdg r
           |  _ \<Rightarrow> R)
   = (if is_ep_cap x then P (cap_ep_ptr x) (cap_ep_badge x) (cap_rights x) else
      if is_ntfn_cap x then Q (cap_ep_ptr x) (cap_ep_badge x) (cap_rights x) else
      R)"
  by (cases x, simp_all)

crunches update_sk_obj_ref, do_nbrecv_failed_transfer
  for pred_tcb_at[wp]: "\<lambda>s. P (pred_tcb_at proj P' t s)"

lemmas thread_set_Pmdb = thread_set_no_cdt

end
