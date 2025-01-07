(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Ipc_AI
imports
  ArchFinalise_AI
  "Monads.WPBang"
begin

arch_requalify_consts
  in_device_frame

arch_requalify_facts
  arch_derive_cap_notzombie
  arch_derive_cap_notIRQ
  lookup_ipc_buffer_inv
  set_mi_invs
  as_user_hyp_refs_of

declare lookup_ipc_buffer_inv[wp]
declare set_mi_invs[wp]
declare as_user_hyp_refs_of[wp]

declare if_cong[cong del]

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
  by (rule hoare_strengthen_postE_R, rule lookup_cnode_slot_real_cte, simp add: real_cte_at_cte)

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
  apply fastforce
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
         safe elim!: hoare_strengthen_postE_R)
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

lemma update_cap_data_closedform:
  "update_cap_data pres w cap =
   (case cap of
      EndpointCap r badge rights \<Rightarrow>
        if badge = 0 \<and> \<not> pres then (EndpointCap r (w && mask badge_bits) rights) else NullCap
    | NotificationCap r badge rights \<Rightarrow>
        if badge = 0 \<and> \<not> pres then (NotificationCap r (w && mask badge_bits) rights) else NullCap
    | CNodeCap r bits guard \<Rightarrow>
        if word_bits < fst (update_cnode_cap_data w) + bits
        then NullCap
        else CNodeCap r bits ((\<lambda>g''. drop (size g'' - fst (update_cnode_cap_data w)) (to_bl g''))
                             (snd (update_cnode_cap_data w)))
    | ThreadCap r \<Rightarrow> ThreadCap r
    | DomainCap \<Rightarrow> DomainCap
    | UntypedCap d p n idx \<Rightarrow> UntypedCap d p n idx
    | NullCap \<Rightarrow> NullCap
    | ReplyCap t m rights \<Rightarrow> ReplyCap t m rights
    | IRQControlCap \<Rightarrow> IRQControlCap
    | IRQHandlerCap irq \<Rightarrow> IRQHandlerCap irq
    | Zombie r b n \<Rightarrow> Zombie r b n
    | ArchObjectCap cap \<Rightarrow> arch_update_cap_data pres w cap)"
  by (cases cap,
         simp_all only: cap.simps update_cap_data_def is_ep_cap.simps if_False if_True
                        is_ntfn_cap.simps is_cnode_cap.simps is_arch_cap_def word_size
                        cap_ep_badge.simps badge_update_def o_def cap_rights_update_def
                        simp_thms cap_rights.simps Let_def split_def
                        the_cnode_cap_def fst_conv snd_conv fun_app_def the_arch_cap_def
                  cong: if_cong)


crunch get_extra_cptr
  for inv[wp]: P (wp: dmo_inv loadWord_inv)
crunch set_extra_badge
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
  apply (rule hoare_strengthen_postE_R)
   apply (rule lsfco_cte_at)
  apply (clarsimp simp: cte_wp_at_def)
  done

(* FIXME rename other occurrences *)
lemmas bits_low_high_eq = word_mask_shift_eqI

lemma set_extra_badge_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> set_extra_badge buffer b n \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  by (simp add: set_extra_badge_def store_word_offs_def | wp)+

lemmas set_extra_badge_typ_ats[wp] = abs_typ_at_lifts[OF set_extra_badge_typ_at]

crunch set_extra_badge
  for valid_objs[wp]: valid_objs

crunch set_extra_badge
  for aligned[wp]: pspace_aligned

crunch set_extra_badge
  for dist[wp]: pspace_distinct

crunch set_extra_badge
  for valid_mdb[wp]: valid_mdb

crunch set_extra_badge
  for cte_wp_at[wp]: "cte_wp_at P p"

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

crunch set_extra_badge
  for in_user_frame[wp]: "in_user_frame buffer"
crunch set_extra_badge
  for in_device_frame[wp]: "in_device_frame buffer"

lemma cap_insert_cte_wp_at:
  "\<lbrace>\<lambda>s. cte_wp_at (is_derived (cdt s) src cap) src s \<and> valid_mdb s \<and> valid_objs s
    \<and> (if p = dest then P cap else cte_wp_at (\<lambda>c. P (masked_as_full c cap)) p s)\<rbrace> cap_insert cap src dest \<lbrace>\<lambda>uu. cte_wp_at P p\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (clarsimp split:if_split_asm)
  apply (clarsimp simp:cap_insert_def)
  apply (wp set_cap_cte_wp_at | simp split del: if_split)+
     apply (clarsimp simp:set_untyped_cap_as_full_def split del:if_split)
    apply (wp get_cap_wp)+
   apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (clarsimp simp:cap_insert_def)
  apply (wp set_cap_cte_wp_at | simp split del: if_split)+
    apply (clarsimp simp:set_untyped_cap_as_full_def split del:if_split)
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
  by (wp set_cap_cte_wp_at get_cap_wp hoare_weak_lift_imp
      | simp add: cap_insert_def
      | unfold set_untyped_cap_as_full_def
      | auto simp: cte_wp_at_def dest!:imp)+

crunch cap_insert
  for in_user_frame[wp]: "in_user_frame buffer"
  (wp: crunch_wps ignore: get_cap)

crunch set_extra_badge
  for cdt[wp]: "\<lambda>s. P (cdt s)"

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

crunch set_extra_badge
  for ex_cte_cap_wp_to[wp]: "ex_cte_cap_wp_to P p"
  (rule: ex_cte_cap_to_pres)

lemma cap_insert_assume_null:
  "\<lbrace>P\<rbrace> cap_insert cap src dest \<lbrace>Q\<rbrace> \<Longrightarrow>
   \<lbrace>\<lambda>s. cte_wp_at ((=) cap.NullCap) dest s \<longrightarrow> P s\<rbrace> cap_insert cap src dest \<lbrace>Q\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (erule impCE)
   apply (simp add: cap_insert_def)
   apply (rule bind_wp[OF _ get_cap_sp])+
   apply (clarsimp simp: valid_def cte_wp_at_caps_of_state in_monad
              split del: if_split)
  apply (erule hoare_weaken_pre)
  apply simp
  done

crunch set_extra_badge
  for arch[wp]: "\<lambda>s. P (arch_state s)"

definition
  "valid_message_info mi \<equiv>
     mi_length mi \<le> of_nat msg_max_length \<and>
     mi_extra_caps mi \<le> of_nat msg_max_extra_caps"

abbreviation (input)
  "transfer_caps_srcs caps s \<equiv>
    (\<forall>x \<in> set caps. cte_wp_at (\<lambda>cp. fst x \<noteq> cap.NullCap \<longrightarrow> cp = fst x) (snd x) s
                                           \<and> real_cte_at (snd x) s)"

(* transfer_caps_loop_presM is needed to satisfy assumptions of Ipc_AI_2,
   thus needs to come before Ipc_AI_2 *)
locale Ipc_AI =
  fixes state_ext_t :: "'state_ext::state_ext itself"
  fixes some_t :: "'t itself"
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
   apply (wp eb hoare_vcg_const_imp_lift hoare_vcg_const_Ball_lift hoare_weak_lift_imp
           | assumption | simp split del: if_split)+
      apply (rule cap_insert_assume_null)
      apply (wp x hoare_vcg_const_Ball_lift cap_insert_cte_wp_at hoare_weak_lift_imp)+
      apply (rule hoare_vcg_conj_liftE_R')
       apply (rule derive_cap_is_derived_foo)
      apply (rule_tac Q' ="\<lambda>cap' s. (vo \<longrightarrow> cap'\<noteq> cap.NullCap \<longrightarrow>
          cte_wp_at (is_derived (cdt s) (aa, b) cap') (aa, b) s)
          \<and> (cap'\<noteq> cap.NullCap \<longrightarrow> QM s cap')" for QM
          in hoare_strengthen_postE_R)
        prefer 2
        apply clarsimp
        apply assumption
       apply (rule hoare_vcg_conj_liftE_R')
         apply (rule hoare_vcg_const_imp_liftE_R)
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

lemmas transfer_caps_loop_pres =
    transfer_caps_loop_presM[where vo=False and ex=False and em=False, simplified]

lemma transfer_caps_loop_arch[wp]:
  "\<And>P ep buffer n caps slots mi.
    \<lbrace>\<lambda>s::'state_ext state. P (arch_state s)\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv s. P (arch_state s)\<rbrace>"
  by (rule transfer_caps_loop_pres) wp+

lemma transfer_caps_loop_aobj_at:
  "arch_obj_pred P' \<Longrightarrow>
  \<lbrace>\<lambda>s. P (obj_at P' pd s)\<rbrace> transfer_caps_loop ep buffer n caps slots mi \<lbrace>\<lambda>r s::'state_ext state. P (obj_at P' pd s)\<rbrace>"
  apply (rule hoare_pre)
   apply (rule transfer_caps_loop_presM[where em=False and ex=False and vo=False, simplified, where P="\<lambda>s. P (obj_at P' pd s)"])
    apply (wp cap_insert_aobj_at)
   apply (wpsimp simp: set_extra_badge_def)
  apply assumption
  done

lemma transfer_caps_loop_typ_at[wp]:
   "\<And>P T p ep buffer n caps slots mi.
      \<lbrace>\<lambda>s::'state_ext state. P (typ_at T p s)\<rbrace>
        transfer_caps_loop ep buffer n caps slots mi
      \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by (wp transfer_caps_loop_pres)

lemmas transfer_caps_loop_typ_ats[wp] = abs_typ_at_lifts[OF transfer_caps_loop_typ_at]

end

(* FIXME: can some of these assumptions be proved with lifting lemmas? *)
locale Ipc_AI_2 = Ipc_AI state_ext_t some_t
  for state_ext_t :: "'state_ext::state_ext itself"  and some_t :: "'t itself"+
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
  assumes make_arch_fault_msg_zombies[wp]:
    "\<And>ft t.   make_arch_fault_msg ft t \<lbrace>zombies_final :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_it[wp]:
    "\<And>P ft t. make_arch_fault_msg ft t \<lbrace>\<lambda>s :: 'state_ext state. P (idle_thread s)\<rbrace>"
  assumes make_arch_fault_msg_valid_globals[wp]:
    "\<And>ft t.   make_arch_fault_msg ft t \<lbrace>valid_global_refs :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_valid_reply[wp]:
    "\<And> ft t. make_arch_fault_msg ft t\<lbrace>valid_reply_caps :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_reply_masters[wp]:
    "\<And>ft t. make_arch_fault_msg ft t \<lbrace>valid_reply_masters :: 'state_ext state \<Rightarrow> bool\<rbrace>"
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
    "\<And> P p ft t . make_arch_fault_msg ft t \<lbrace>st_tcb_at P p :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_cap_to[wp]:
    "\<And> ft t p. make_arch_fault_msg ft t \<lbrace>ex_nonz_cap_to p :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_valid_irq_states[wp]:
    "\<And> ft t. make_arch_fault_msg ft t \<lbrace>valid_irq_states :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_cap_refs_respects_device_region[wp]:
    "\<And> ft t. make_arch_fault_msg ft t \<lbrace>cap_refs_respects_device_region :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_pred_tcb[wp]:
    "\<And> Q P (proj :: itcb \<Rightarrow> 't) ft t p. make_arch_fault_msg ft t \<lbrace>\<lambda>s::'state_ext state. Q (pred_tcb_at proj P p s)\<rbrace>"
  assumes make_arch_fault_msg_arch_tcb_at[wp]:
    "\<And> Q P ft t p. make_arch_fault_msg ft t \<lbrace>\<lambda>s::'state_ext state. Q (arch_tcb_at P p s)\<rbrace>"
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
  assumes is_derived_ReplyCap [simp]:
    "\<And>m p t R. is_derived m p (cap.ReplyCap t False R) = (\<lambda>c. is_master_reply_cap c \<and> obj_ref_of c = t)"
  assumes do_ipc_transfer_tcb_caps:
    "\<And>P t ref st ep b gr rt.
      (\<And>c. P c \<Longrightarrow> \<not> is_untyped_cap c) \<Longrightarrow>
        \<lbrace>valid_objs and cte_wp_at P (t, ref) and tcb_at t :: 'state_ext state \<Rightarrow> bool\<rbrace>
          do_ipc_transfer st ep b gr rt
        \<lbrace>\<lambda>rv. cte_wp_at P (t, ref)\<rbrace>"
  assumes setup_caller_cap_valid_global_objs[wp]:
    "\<And>send recv grant.
      \<lbrace>valid_global_objs :: 'state_ext state \<Rightarrow> bool\<rbrace>
        setup_caller_cap send recv grant
      \<lbrace>\<lambda>rv. valid_global_objs\<rbrace>"
  assumes setup_caller_cap_valid_arch[wp]:
    "\<And>send recv grant.
      \<lbrace>valid_arch_state :: 'state_ext state \<Rightarrow> bool\<rbrace>
        setup_caller_cap send recv grant
      \<lbrace>\<lambda>rv. valid_arch_state\<rbrace>"
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
  assumes transfer_caps_loop_valid_arch:
  "\<And>slots caps ep buffer n mi.
    \<lbrace>valid_arch_state and valid_objs and valid_mdb and K (distinct slots)
     and (\<lambda>s. \<forall>x \<in> set slots. real_cte_at x s \<and> cte_wp_at (\<lambda>cap. cap = cap.NullCap) x s)
     and transfer_caps_srcs caps\<rbrace>
    transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. valid_arch_state :: 'state_ext state \<Rightarrow> bool\<rbrace>"

context Ipc_AI_2 begin

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

lemma mask_cap_vs_cap_ref[simp]:
  "vs_cap_ref (mask_cap msk cap) = vs_cap_ref cap"
  by (simp add: mask_cap_def)

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

lemmas invs_valid_objs2 = invs_vobjs_strgs

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

crunch set_extra_badge
  for state_refs_of[wp]: "\<lambda>s. P (state_refs_of s)"
crunch set_extra_badge
  for state_hyp_refs_of[wp]: "\<lambda>s. P (state_hyp_refs_of s)"

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

crunch set_extra_badge
  for if_live[wp]: if_live_then_nonz_cap

lemma tcl_iflive[wp]:
  "\<And>ep buffer n caps slots mi.
    \<lbrace>if_live_then_nonz_cap :: 'state_ext state \<Rightarrow> bool\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  by (wp transfer_caps_loop_pres cap_insert_iflive)

crunch set_extra_badge
  for if_unsafe[wp]: if_unsafe_then_cap

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

crunch set_extra_badge
  for pred_tcb_at[wp]: "\<lambda>s. pred_tcb_at proj P p s"
crunch set_extra_badge
  for idle[wp]: "\<lambda>s. P (idle_thread s)"

lemma (in Ipc_AI) tcl_idle[wp]:
  "\<And>ep buffer n caps slots mi.
    \<lbrace>valid_idle::'state_ext state \<Rightarrow> bool\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  by (wp transfer_caps_loop_pres cap_insert_idle valid_idle_lift)

crunch set_extra_badge
  for cur_tcb[wp]: cur_tcb

lemma (in Ipc_AI_2) tcl_ct[wp]:
  "\<And>ep buffer n caps slots mi.
    \<lbrace>cur_tcb::'state_ext state \<Rightarrow> bool\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. cur_tcb\<rbrace>"
  by (wp transfer_caps_loop_pres)

lemma (in Ipc_AI_2) tcl_it[wp]:
  "\<And>P ep buffer n caps slots mi.
    \<lbrace>\<lambda>s::'state_ext state. P (idle_thread s)\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv s. P (idle_thread s)\<rbrace>"
  by (wp transfer_caps_loop_pres)

lemma (in Ipc_AI_2) derive_cap_objrefs_iszombie:
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

crunch set_extra_badge
  for caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"

lemma set_extra_badge_zombies_final[wp]:
  "\<lbrace>zombies_final\<rbrace> set_extra_badge buffer b n \<lbrace>\<lambda>_. zombies_final\<rbrace>"
  apply (simp add: zombies_final_def cte_wp_at_caps_of_state is_final_cap'_def2)
  apply (wp hoare_vcg_all_lift final_cap_lift)
  done

lemma (in Ipc_AI_2) tcl_zombies[wp]:
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

crunch set_extra_badge
  for irq[wp]: "\<lambda>s. P (interrupt_irq_node s)"

context Ipc_AI_2 begin

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
                                        [where Q="\<lambda>_. valid_reply_caps"],
                                   simplified]

lemmas tcl_reply_masters[wp] = tcl_reply' [THEN hoare_strengthen_post
                                        [where Q="\<lambda>_. valid_reply_masters"],
                                   simplified]

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


crunch set_extra_badge
  for irq_state[wp]: "\<lambda>s. P (interrupt_states s)"

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

crunch set_extra_badge
  for valid_arch_caps[wp]: valid_arch_caps

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

crunch set_extra_badge
  for valid_global_objs[wp]: valid_global_objs


lemma transfer_caps_loop_valid_global_objs[wp]:
  "\<And>ep buffer n caps slots mi.
    \<lbrace>valid_global_objs :: 'state_ext state \<Rightarrow> bool\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. valid_global_objs\<rbrace>"
  by (wp transfer_caps_loop_pres cap_insert_valid_global_objs)

crunch set_extra_badge
  for valid_kernel_mappings[wp]: valid_kernel_mappings


lemma transfer_caps_loop_v_ker_map[wp]:
  "\<And>ep buffer n caps slots mi.
    \<lbrace>valid_kernel_mappings :: 'state_ext state \<Rightarrow> bool\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. valid_kernel_mappings\<rbrace>"
  by (wp transfer_caps_loop_pres)


crunch set_extra_badge
  for equal_kernel_mappings[wp]: equal_kernel_mappings


lemma transfer_caps_loop_eq_ker_map[wp]:
  "\<And>ep buffer n caps slots mi.
    \<lbrace>equal_kernel_mappings :: 'state_ext state \<Rightarrow> bool\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. equal_kernel_mappings\<rbrace>"
  by (wp transfer_caps_loop_pres)


crunch set_extra_badge
  for valid_asid_map[wp]: valid_asid_map


lemma transfer_caps_loop_asid_map[wp]:
  "\<And>ep buffer n caps slots mi.
    \<lbrace>valid_asid_map :: 'state_ext state \<Rightarrow> bool\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. valid_asid_map\<rbrace>"
  by (wp transfer_caps_loop_pres | simp)+


crunch set_extra_badge
  for only_idle[wp]: only_idle


lemma transfer_caps_loop_only_idle[wp]:
  "\<And>ep buffer n caps slots mi.
    \<lbrace>only_idle :: 'state_ext state \<Rightarrow> bool\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. only_idle\<rbrace>"
  by (wp transfer_caps_loop_pres | simp)+

crunch set_extra_badge
  for valid_global_vspace_mappings[wp]: valid_global_vspace_mappings


lemma transfer_caps_loop_valid_global_pd_mappings[wp]:
  "\<And>ep buffer n caps slots mi.
    \<lbrace>valid_global_vspace_mappings :: 'state_ext state \<Rightarrow> bool\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. valid_global_vspace_mappings\<rbrace>"
  by (wp transfer_caps_loop_pres)


crunch set_extra_badge
  for pspace_in_kernel_window[wp]: pspace_in_kernel_window


lemma transfer_caps_loop_pspace_in_kernel_window[wp]:
  "\<And>ep buffer n caps slots mi.
    \<lbrace>pspace_in_kernel_window :: 'state_ext state \<Rightarrow> bool\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. pspace_in_kernel_window\<rbrace>"
  by (wp transfer_caps_loop_pres)


crunch set_extra_badge
  for cap_refs_in_kernel_window[wp]: cap_refs_in_kernel_window

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


crunch store_word_offs
  for valid_ioc[wp]: valid_ioc


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

crunch set_extra_badge
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

crunch transfer_caps_loop
  for valid_cur_fpu[wp]: "valid_cur_fpu ::'state_ext state \<Rightarrow> _"
  (rule: transfer_caps_loop_pres)

lemma transfer_caps_loop_invs[wp]:
  "\<And>slots.
    \<lbrace>\<lambda>s::'state_ext state. invs s
          \<and> (\<forall>x \<in> set slots. ex_cte_cap_wp_to is_cnode_cap x s) \<and> distinct slots
          \<and> (\<forall>x \<in> set slots. real_cte_at x s \<and> cte_wp_at (\<lambda>cap. cap = cap.NullCap) x s)
          \<and> transfer_caps_srcs caps s\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. invs\<rbrace>"
  unfolding invs_def valid_state_def valid_pspace_def
  by (wpsimp wp: valid_irq_node_typ transfer_caps_loop_valid_vspace_objs
                 transfer_caps_loop_valid_arch)

end

(* FIXME: move *)
crunch set_extra_badge
  for valid_vspace_objs[wp]: valid_vspace_objs

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


context Ipc_AI_2 begin

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

context Ipc_AI_2 begin

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

lemma set_mrs_valid_objs [wp]:
  "\<lbrace>valid_objs\<rbrace> set_mrs t a msgs \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  apply (cases a)
   apply (simp add: set_mrs_redux)
   apply (wp thread_set_valid_objs_triv)
          apply (auto simp: tcb_cap_cases_def)[1]
         apply simp+
  apply (simp add: set_mrs_redux zipWithM_x_mapM split_def
                   store_word_offs_def
            split del: if_split)
  apply (wp mapM_wp' thread_set_valid_objs_triv | simp)+
         apply (auto simp: tcb_cap_cases_def)
  done


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


lemma get_tcb_ko_at:
  "(get_tcb t s = Some tcb) = ko_at (TCB tcb) t s"
  by (auto simp: obj_at_def get_tcb_def
           split: option.splits Structures_A.kernel_object.splits)


lemmas get_tcb_ko_atI = get_tcb_ko_at [THEN iffD1]


crunch set_mrs
  for "distinct"[wp]: pspace_distinct
  (wp: mapM_wp simp: zipWithM_x_mapM)


crunch copy_mrs
  for "distinct"[wp]: pspace_distinct
  (wp: mapM_wp' simp: copy_mrs_redux)


crunch set_mrs
  for mdb_P[wp]: "\<lambda>s. P (cdt s)"
  (wp: crunch_wps simp: crunch_simps zipWithM_x_mapM)


crunch set_mrs
  for mdb_R[wp]: "\<lambda>s. P (is_original_cap s)"
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


crunch copy_mrs
  for mdb_P[wp]: "\<lambda>s. P (cdt s)"
  (wp: crunch_wps simp: crunch_simps)


crunch copy_mrs
  for mdb_R[wp]: "\<lambda>s. P (is_original_cap s)"
  (wp: crunch_wps simp: crunch_simps)


crunch copy_mrs
  for mdb[wp]: valid_mdb
  (wp: crunch_wps simp: crunch_simps)


lemma set_mrs_ep_at[wp]:
  "\<lbrace>ep_at x\<rbrace> set_mrs tcb buf msg \<lbrace>\<lambda>rv. ep_at x\<rbrace>"
  by (simp add: ep_at_typ, wp)


lemma copy_mrs_ep_at[wp]:
  "\<lbrace>ep_at x\<rbrace> copy_mrs s sb r rb n \<lbrace>\<lambda>rv. ep_at x\<rbrace>"
  by (simp add: ep_at_typ, wp)

crunch copy_mrs
  for cte_wp_at[wp]: "cte_wp_at P p"
  (wp: crunch_wps)


crunch lookup_extra_caps
  for inv[wp]: "P"
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

context Ipc_AI_2 begin

crunch do_normal_transfer
  for typ_at[wp]: "\<lambda>s::'state_ext state. P (typ_at T p s)"

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


lemma set_mrs_cte_wp_at [wp]:
  "\<lbrace>cte_wp_at P c\<rbrace> set_mrs p' b m \<lbrace>\<lambda>rv. cte_wp_at P c\<rbrace>"
  by (wp set_mrs_thread_set_dmo thread_set_cte_wp_at_trivial
         ball_tcb_cap_casesI | simp)+


lemma set_mrs_ex_nonz_cap_to[wp]:
  "\<lbrace>ex_nonz_cap_to p\<rbrace> set_mrs a b c \<lbrace>\<lambda>rv. ex_nonz_cap_to p\<rbrace>"
  by (wp ex_nonz_cap_to_pres)


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

context Ipc_AI_2 begin

crunch do_ipc_transfer
  for aligned[wp]: "pspace_aligned :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps simp: crunch_simps zipWithM_x_mapM)

crunch do_ipc_transfer
  for "distinct"[wp]: "pspace_distinct :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps simp: crunch_simps zipWithM_x_mapM)

crunch set_message_info
  for vmdb[wp]: "valid_mdb :: 'state_ext state \<Rightarrow> bool"

crunch do_ipc_transfer
  for vmdb[wp]: "valid_mdb :: 'state_ext state \<Rightarrow> bool"
  (ignore: as_user simp: crunch_simps ball_conj_distrib
       wp: crunch_wps hoare_vcg_const_Ball_lift transfer_caps_loop_valid_mdb)

crunch do_ipc_transfer
  for ifunsafe[wp]: "if_unsafe_then_cap :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps hoare_vcg_const_Ball_lift simp: zipWithM_x_mapM ignore: transfer_caps_loop)

crunch do_ipc_transfer
  for iflive[wp]: "if_live_then_nonz_cap :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps simp: zipWithM_x_mapM ignore: transfer_caps_loop)

crunch do_ipc_transfer
  for state_refs_of[wp]: "\<lambda>s::'state_ext state. P (state_refs_of s)"
  (wp: crunch_wps simp: zipWithM_x_mapM ignore: transfer_caps_loop)

crunch do_ipc_transfer
  for ct[wp]: "cur_tcb :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps simp: zipWithM_x_mapM ignore: transfer_caps_loop)

crunch do_ipc_transfer
  for zombies[wp]: "zombies_final :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps hoare_vcg_const_Ball_lift tcl_zombies simp: crunch_simps ball_conj_distrib )

crunch do_ipc_transfer
  for it[wp]: "\<lambda>s::'state_ext state. P (idle_thread s)"
  (wp: crunch_wps simp: crunch_simps zipWithM_x_mapM)

crunch do_ipc_transfer
  for valid_globals[wp]: "valid_global_refs :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps hoare_vcg_const_Ball_lift simp: crunch_simps zipWithM_x_mapM ball_conj_distrib)

crunch do_ipc_transfer
  for arch_tcb_at[wp]: "\<lambda>s::'state_ext state. Q (arch_tcb_at P t s)"
  and arch_state[wp]: "\<lambda>s::'state_ext state. P (arch_state s)"
  and valid_cur_fpu[wp]: "valid_cur_fpu :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps valid_cur_fpu_lift rule: transfer_caps_loop_pres)

end

lemma set_mrs_idle[wp]:
  "\<lbrace>valid_idle\<rbrace> set_mrs param_a param_b param_c \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  by (wp set_mrs_thread_set_dmo thread_set_valid_idle_trivial
         ball_tcb_cap_casesI | simp)+

lemma set_mrs_reply[wp]:
  "\<lbrace>valid_reply_caps\<rbrace> set_mrs a b c \<lbrace>\<lambda>_. valid_reply_caps\<rbrace>"
  by (wp set_mrs_thread_set_dmo thread_set_valid_reply_caps_trivial
         ball_tcb_cap_casesI | simp)+

lemma set_mrs_reply_masters[wp]:
  "\<lbrace>valid_reply_masters\<rbrace> set_mrs a b c \<lbrace>\<lambda>_. valid_reply_masters\<rbrace>"
  by (wp set_mrs_thread_set_dmo thread_set_valid_reply_masters_trivial
         ball_tcb_cap_casesI | simp)+

crunch copy_mrs
  for reply_masters[wp]: valid_reply_masters
  (wp: crunch_wps)

context Ipc_AI_2 begin

crunch do_ipc_transfer
  for reply[wp]: "valid_reply_caps :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps hoare_vcg_const_Ball_lift tcl_reply simp: zipWithM_x_mapM ball_conj_distrib
       ignore: const_on_failure)

crunch do_ipc_transfer
  for reply_masters[wp]: "valid_reply_masters :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps hoare_vcg_const_Ball_lift tcl_reply_masters
      simp: zipWithM_x_mapM ball_conj_distrib )

crunch do_ipc_transfer
  for valid_idle[wp]: "valid_idle :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps simp: zipWithM_x_mapM ignore: transfer_caps_loop)

crunch do_ipc_transfer
  for arch[wp]: "\<lambda>s::'state_ext state. P (arch_state s)"
  (wp: crunch_wps simp: zipWithM_x_mapM ignore: transfer_caps_loop)

crunch do_ipc_transfer
  for typ_at[wp]: "\<lambda>s::'state_ext state. P (typ_at T p s)"
  (wp: crunch_wps simp: zipWithM_x_mapM ignore: transfer_caps_loop)

crunch do_ipc_transfer
  for irq_node[wp]: "\<lambda>s::'state_ext state. P (interrupt_irq_node s)"
  (wp: crunch_wps simp: zipWithM_x_mapM crunch_simps)

(* FIXME: move to KHeap_AI? *)
interpretation
  set_mrs: non_aobj_op "set_mrs t buf msg"
  unfolding set_mrs_def
  apply (unfold_locales)
  by (wpsimp wp: set_object_non_arch get_object_wp mapM_wp'
           simp: zipWithM_x_mapM non_arch_obj_def
         | rule conjI)+

lemma do_ipc_transfer_aobj_at:
  "arch_obj_pred P' \<Longrightarrow>
  \<lbrace>\<lambda>s. P (obj_at P' pd s)\<rbrace> do_ipc_transfer s ep bg grt r \<lbrace>\<lambda>r s :: 'state_ext state. P (obj_at P' pd s)\<rbrace>"
  unfolding
    do_ipc_transfer_def do_normal_transfer_def set_message_info_def transfer_caps_def
    copy_mrs_def do_fault_transfer_def
  apply (wpsimp wp: as_user.aobj_at set_mrs.aobj_at hoare_drop_imps mapM_wp' transfer_caps_loop_aobj_at)
       apply (case_tac f, simp split del: if_split)
          apply (wpsimp wp: as_user.aobj_at hoare_drop_imps)+
  done

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


context Ipc_AI_2 begin

crunch do_ipc_transfer
  for irq_handlers[wp]: "valid_irq_handlers :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps hoare_vcg_const_Ball_lift simp: zipWithM_x_mapM crunch_simps ball_conj_distrib)

crunch do_ipc_transfer
  for valid_global_objs[wp]: "valid_global_objs :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps simp: zipWithM_x_mapM ignore: make_arch_fault_msg)

crunch do_ipc_transfer
  for vspace_objs[wp]: "valid_vspace_objs :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps transfer_caps_loop_valid_vspace_objs simp: zipWithM_x_mapM crunch_simps)

crunch do_ipc_transfer
  for valid_global_vspace_mappings[wp]: "valid_global_vspace_mappings :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps transfer_caps_loop_valid_vspace_objs simp: zipWithM_x_mapM crunch_simps)

crunch do_ipc_transfer
  for arch_caps[wp]: "valid_arch_caps :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps hoare_vcg_const_Ball_lift transfer_caps_loop_valid_arch_caps
   simp: zipWithM_x_mapM crunch_simps ball_conj_distrib )

crunch do_ipc_transfer
  for v_ker_map[wp]: "valid_kernel_mappings :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps simp: zipWithM_x_mapM crunch_simps)

crunch do_ipc_transfer
  for eq_ker_map[wp]: "equal_kernel_mappings :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps simp: zipWithM_x_mapM crunch_simps ignore: set_object)

crunch do_ipc_transfer
  for asid_map[wp]: "valid_asid_map :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps simp: crunch_simps)

end

declare as_user_only_idle [wp]

crunch store_word_offs
  for only_idle[wp]: only_idle

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

context Ipc_AI_2 begin

crunch do_ipc_transfer
  for only_idle[wp]: "only_idle :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps simp: crunch_simps)

crunch do_ipc_transfer
  for pspace_in_kernel_window[wp]: "pspace_in_kernel_window :: 'state_ext state \<Rightarrow> bool"
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

context Ipc_AI_2 begin

crunch do_ipc_transfer
  for cap_refs_in_kernel_window[wp]: "cap_refs_in_kernel_window :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps hoare_vcg_const_Ball_lift ball_tcb_cap_casesI
     simp: zipWithM_x_mapM crunch_simps ball_conj_distrib )

crunch do_ipc_transfer
  for valid_objs[wp]: "valid_objs :: 'state_ext state \<Rightarrow> bool"
  (wp: hoare_vcg_const_Ball_lift simp:ball_conj_distrib )

end

lemma as_user_valid_ioc[wp]:
  "\<lbrace>valid_ioc\<rbrace> as_user r f \<lbrace>\<lambda>_. valid_ioc\<rbrace>"
  apply (simp add: as_user_def split_def)
  apply (wp set_object_valid_ioc_caps)
  apply (clarsimp simp: valid_ioc_def obj_at_def get_tcb_def
                  split: option.splits Structures_A.kernel_object.splits)
  apply (drule spec, drule spec, erule impE, assumption)
  apply (clarsimp simp: cap_of_def tcb_cnode_map_tcb_cap_cases
                        cte_wp_at_cases null_filter_def)
  apply (simp add: tcb_cap_cases_def split: if_split_asm)
  done

context Ipc_AI_2 begin

lemma set_mrs_valid_ioc[wp]:
  "\<And>thread buf msgs.
    \<lbrace>valid_ioc :: 'state_ext state \<Rightarrow> bool\<rbrace>
      set_mrs thread buf msgs
    \<lbrace>\<lambda>_. valid_ioc\<rbrace>"
  apply (simp add: set_mrs_def)
  apply (wp | wpc)+
     apply (simp only: zipWithM_x_mapM_x split_def)
     apply (wp mapM_x_wp' set_object_valid_ioc_caps hoare_weak_lift_imp
        | simp)+
  apply (clarsimp simp: obj_at_def get_tcb_def valid_ioc_def
                  split: option.splits Structures_A.kernel_object.splits)
  apply (drule spec, drule spec, erule impE, assumption)
  apply (clarsimp simp: cap_of_def tcb_cnode_map_tcb_cap_cases
                        cte_wp_at_cases null_filter_def)
  apply (simp add: tcb_cap_cases_def split: if_split_asm)
  done

crunch do_ipc_transfer
  for valid_ioc[wp]: "valid_ioc :: 'state_ext state \<Rightarrow> bool"
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
  by (rule eq_reflection) (simp add: set_mrs_def thread_set_def bind_assoc)

context Ipc_AI_2 begin

lemma set_mrs_vms[wp]:
  notes if_split [split del]
  shows "\<And>thread buf msgs.
    \<lbrace>valid_machine_state::'state_ext state \<Rightarrow> bool\<rbrace>
      set_mrs thread buf msgs
    \<lbrace>\<lambda>_. valid_machine_state\<rbrace>"
  unfolding set_mrs_def2
  by (wpsimp simp: zipWithM_x_mapM_x split_def
               wp: mapM_x_wp_inv hoare_vcg_all_lift hoare_drop_imps)

crunch do_ipc_transfer
  for vms[wp]: "valid_machine_state :: 'state_ext state \<Rightarrow> bool"
  (wp: mapM_UNIV_wp)

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

lemma (in Ipc_AI_2) handle_fault_reply_typ_at[wp]:
  "\<lbrace>\<lambda>s :: 'state_ext state. P (typ_at T p s)\<rbrace> handle_fault_reply ft t label msg \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by(cases ft, simp_all, wp+)

lemma (in Ipc_AI_2) handle_fault_reply_tcb[wp]:
  "\<lbrace>tcb_at t' :: 'state_ext state \<Rightarrow> bool\<rbrace>
     handle_fault_reply ft t label msg
   \<lbrace>\<lambda>rv. tcb_at t'\<rbrace>"
  by (simp add: tcb_at_typ, wp)

lemma (in Ipc_AI_2) handle_fault_reply_cte[wp]:
  "\<lbrace>cte_at t' :: 'state_ext state \<Rightarrow> bool\<rbrace> handle_fault_reply ft t label msg \<lbrace>\<lambda>rv. cte_at t'\<rbrace>"
  by (wp valid_cte_at_typ)

lemma valid_reply_caps_awaiting_reply:
  "\<lbrakk>valid_reply_caps s; kheap s t = Some (TCB tcb);
    has_reply_cap t s; tcb_state tcb = st\<rbrakk> \<Longrightarrow>
   awaiting_reply st"
  apply (simp add: valid_reply_caps_def pred_tcb_at_def)
  apply (fastforce simp: obj_at_def)
  done

lemmas cap_insert_typ_ats [wp] = abs_typ_at_lifts [OF cap_insert_typ_at]

context Ipc_AI_2 begin

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

lemma cap_delete_one_ntfn_at [wp]:
  "\<lbrace>\<lambda>s. P (ntfn_at word s)\<rbrace> cap_delete_one slot \<lbrace>\<lambda>_ s'. P (ntfn_at word s')\<rbrace>"
  by (simp add: ntfn_at_typ, wp)

lemma cap_delete_one_valid_tcb_state:
  "\<lbrace>\<lambda>s. P (valid_tcb_state st s)\<rbrace> cap_delete_one slot \<lbrace>\<lambda>_ s'. P (valid_tcb_state st s')\<rbrace>"
  apply (simp add: valid_tcb_state_def)
  apply (cases st, (wp | simp)+)
  done

lemma cte_wp_at_reply_cap_can_fast_finalise:
  "cte_wp_at ((=) (cap.ReplyCap tcb v R)) slot s \<longrightarrow> cte_wp_at can_fast_finalise slot s"
  by (clarsimp simp: cte_wp_at_caps_of_state can_fast_finalise_def)

context Ipc_AI_2 begin

crunch do_ipc_transfer
  for st_tcb_at[wp]: "st_tcb_at  P t :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps transfer_caps_loop_pres simp: zipWithM_x_mapM)

end

crunch setup_caller_cap
  for tcb_at[wp]: "tcb_at t"


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


crunch set_message_info
  for ex_cap[wp]: "ex_nonz_cap_to p"


lemma tcb_bound_refs_eq_restr:
  "tcb_bound_refs mptr = {x. x \<in> id tcb_bound_refs mptr \<and> snd x = TCBBound}"
  by (auto dest: refs_in_tcb_bound_refs)


lemma update_waiting_invs:
  notes if_split[split del]
  shows
  "\<lbrace>ko_at (Notification ntfn) ntfnptr and invs
     and K (ntfn_obj ntfn = ntfn.WaitingNtfn q \<and> ntfn_bound_tcb ntfn = bound_tcb)\<rbrace>
     update_waiting_ntfn ntfnptr q bound_tcb bdg
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: update_waiting_ntfn_def)
  apply (rule bind_wp[OF _ assert_sp])
  apply (rule hoare_pre)
   apply (wp |simp)+
    apply (simp add: invs_def valid_state_def valid_pspace_def)
    apply (wp valid_irq_node_typ sts_only_idle)
   apply (simp add: valid_tcb_state_def conj_comms)
   apply (simp add: cte_wp_at_caps_of_state)
   apply (wp set_simple_ko_valid_objs hoare_post_imp [OF disjI1]
            valid_irq_node_typ | assumption | simp |
            strengthen reply_cap_doesnt_exist_strg)+
  apply (clarsimp simp: invs_def valid_state_def valid_pspace_def
                        ep_redux_simps neq_Nil_conv
                  cong: list.case_cong if_cong)
  apply (frule(1) sym_refs_obj_atD, clarsimp simp: st_tcb_at_refs_of_rev)
  apply (frule (1) if_live_then_nonz_capD)
   apply (clarsimp simp: live_def)
  apply (frule(1) st_tcb_ex_cap)
   apply simp
  apply (simp add: st_tcb_at_tcb_at)
  apply (frule ko_at_state_refs_ofD)
  apply (frule st_tcb_at_state_refs_ofD)
  apply (erule(1) obj_at_valid_objsE)
  apply (clarsimp simp: valid_obj_def valid_ntfn_def obj_at_def is_ntfn_def)
  apply (rule conjI, clarsimp simp: obj_at_def split: option.splits list.splits)
  apply (rule conjI, clarsimp elim!: pred_tcb_weakenE)
  apply (rule conjI, clarsimp dest!: idle_no_ex_cap)
  apply (rule conjI, erule delta_sym_refs)
    apply (clarsimp dest!: refs_in_ntfn_bound_refs
                    split: if_split_asm if_split)
   apply (simp only: tcb_bound_refs_eq_restr, simp)
   apply (fastforce dest!: refs_in_ntfn_bound_refs symreftype_inverse'
                    simp: valid_obj_def valid_ntfn_def obj_at_def is_tcb
                   split: if_split_asm)
  apply (clarsimp elim!: pred_tcb_weakenE)
  done


lemma cancel_ipc_ex_nonz_tcb_cap:
  "\<lbrace>\<lambda>s. \<exists>ptr. cte_wp_at ((=) (cap.ThreadCap p)) ptr s\<rbrace>
     cancel_ipc t
   \<lbrace>\<lambda>rv. ex_nonz_cap_to p\<rbrace>"
  apply (simp add: ex_nonz_cap_to_def cte_wp_at_caps_of_state
              del: split_paired_Ex)
  apply (wp cancel_ipc_caps_of_state)
  apply (clarsimp simp del: split_paired_Ex split_paired_All)
  apply (intro conjI allI impI)
   apply (rule_tac x="(a, b)" in exI)
   apply (clarsimp simp: cte_wp_at_caps_of_state can_fast_finalise_def)
  apply fastforce
  done


lemma valid_cap_tcb_at_tcb_or_zomb:
  "\<lbrakk> s \<turnstile> cap; t \<in> obj_refs cap; tcb_at t s \<rbrakk>
       \<Longrightarrow> is_thread_cap cap \<or> is_zombie cap"
  by (rule obj_ref_is_tcb)


lemma cancel_ipc_ex_nonz_cap_to_tcb:
  "\<lbrace>\<lambda>s. ex_nonz_cap_to p s \<and> valid_objs s \<and> tcb_at p s\<rbrace>
     cancel_ipc t
   \<lbrace>\<lambda>rv. ex_nonz_cap_to p\<rbrace>"
  apply (wp cancel_ipc_ex_nonz_tcb_cap)
  apply (clarsimp simp: ex_nonz_cap_to_def)
  apply (drule cte_wp_at_norm, clarsimp)
  apply (frule(1) cte_wp_at_valid_objs_valid_cap, clarsimp)
  apply (drule valid_cap_tcb_at_tcb_or_zomb[where t=p])
    apply (simp add: zobj_refs_to_obj_refs)
   apply assumption
  apply (fastforce simp: is_cap_simps)
  done


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
  "\<lbrace>st_tcb_at ((\<noteq>) BlockedOnReply) t and cte_wp_at P p\<rbrace>
    cancel_ipc t
   \<lbrace>\<lambda>r. cte_wp_at P p\<rbrace>"
  apply (simp add: cancel_ipc_def)
  apply (rule hoare_pre)
   apply (wp hoare_pre_cont[where f="reply_cancel_ipc t"] gts_wp | wpc)+
  apply (clarsimp simp: st_tcb_at_def obj_at_def)
  done


lemma sai_invs[wp]:
  "\<lbrace>invs and ex_nonz_cap_to ntfn\<rbrace> send_signal ntfn bdg \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: send_signal_def)
  apply (rule bind_wp [OF _ get_simple_ko_sp])
  apply (case_tac "ntfn_obj ntfna", simp_all)
    apply (case_tac "ntfn_bound_tcb ntfna", simp_all)
     apply (wp set_ntfn_minor_invs)
     apply (clarsimp simp: obj_at_def is_ntfn invs_def valid_pspace_def
                           valid_state_def valid_obj_def valid_ntfn_def)
    apply (rule bind_wp [OF _ gts_sp])
    apply (rule hoare_pre)
     apply (rule hoare_vcg_if_split)
      apply (wp sts_invs_minor | clarsimp split: thread_state.splits)+
      apply (rule hoare_vcg_conj_lift[OF hoare_strengthen_post[OF cancel_ipc_simple]])
       apply (fastforce elim: st_tcb_weakenE)
      apply (wp cancel_ipc_ex_nonz_cap_to_tcb cancel_ipc_simple2 set_ntfn_minor_invs
                hoare_disjI2 cancel_ipc_cte_wp_at_not_reply_state)+
    apply (clarsimp simp: invs_def valid_state_def valid_pspace_def
                          st_tcb_at_tcb_at receive_blocked_def
                          st_tcb_at_reply_cap_valid)
    apply (rule conjI, rule impI)
     apply (clarsimp simp: idle_no_ex_cap st_tcb_at_reply_cap_valid
                    split: thread_state.splits)
     apply (frule (1) st_tcb_ex_cap, fastforce split:thread_state.splits)
     apply (auto simp: st_tcb_at_def obj_at_def idle_no_ex_cap)[1]
    apply (clarsimp simp: valid_ntfn_def obj_at_def is_ntfn_def st_tcb_at_def is_tcb
                   elim!: obj_at_weakenE)
   apply (wp update_waiting_invs, simp)
   apply blast
  apply (wp set_ntfn_minor_invs, simp)
  apply (clarsimp simp add: valid_ntfn_def obj_at_def is_ntfn_def
                     elim!: obj_at_weakenE)
  apply (erule(1) valid_objsE[OF invs_valid_objs])
  apply (clarsimp simp: valid_obj_def valid_ntfn_def)
  done

crunch send_signal
  for typ_at[wp]: "\<lambda>s. P (typ_at T t s)"
(wp: hoare_drop_imps)


lemma tcb_at_typ_at:
  "\<lbrace>typ_at ATCB t\<rbrace> f \<lbrace>\<lambda>_. typ_at ATCB t\<rbrace> \<Longrightarrow> \<lbrace>tcb_at t\<rbrace> f \<lbrace>\<lambda>_. tcb_at t\<rbrace>"
  by (simp add: tcb_at_typ)


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

context Ipc_AI_2 begin

crunch send_ipc
  for typ_at[wp]: "\<lambda>s::'state_ext state. P (typ_at T p s)"
  (wp: hoare_drop_imps simp: crunch_simps)

lemma si_tcb_at [wp]:
  "\<And>t' call bl w gr d t ep.
    \<lbrace>tcb_at t' :: 'state_ext state \<Rightarrow> bool\<rbrace>
      send_ipc call bl w gr d t ep
    \<lbrace>\<lambda>rv. tcb_at t'\<rbrace>"
  by (simp add: tcb_at_typ) wp

crunch handle_fault
  for typ_at[wp]: "\<lambda>s::'state_ext state. P (typ_at T p s)"
  (wp: simp: crunch_simps)

lemma hf_tcb_at [wp]:
  "\<And>t' t x.
    \<lbrace>tcb_at t' :: 'state_ext state \<Rightarrow> bool\<rbrace>
      handle_fault t x
    \<lbrace>\<lambda>rv. tcb_at t'\<rbrace>"
  by (simp add: tcb_at_typ, wp)

lemma sfi_tcb_at [wp]:
  "\<And>t t' f.
    \<lbrace>tcb_at t :: 'state_ext state \<Rightarrow> bool\<rbrace>
      send_fault_ipc t' f
    \<lbrace>\<lambda>_. tcb_at t\<rbrace>"
  by (simp add: tcb_at_typ, wp)

end


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
  "pred_tcb_at proj P t (s\<lparr>kheap := (kheap s)(r \<mapsto> TCB v)\<rparr>) =
  (if t = r then P (proj (tcb_to_itcb v)) else pred_tcb_at proj P t s)"
  by (simp add: pred_tcb_at_def obj_at_def)


crunch setup_caller_cap
  for aligned[wp]: "pspace_aligned"
  and "distinct"[wp]: "pspace_distinct"
  and cur_tcb[wp]: "cur_tcb"
  and state_hyp_refs_of[wp]: "\<lambda>s. P (state_hyp_refs_of s)"
  and valid_cur_fpu[wp]: valid_cur_fpu
  (wp: crunch_wps)

lemma setup_caller_cap_state_refs_of[wp]:
  "\<lbrace>\<lambda>s. P ((state_refs_of s) (sender := {r \<in> state_refs_of s sender. snd r = TCBBound}))\<rbrace>
     setup_caller_cap sender rcvr grant
   \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (simp add: setup_caller_cap_def)
  apply (rule conjI)
  apply (clarify, wp, simp add: fun_upd_def cong: if_cong)+
  done

lemma setup_caller_cap_objs[wp]:
  "\<lbrace>valid_objs and pspace_aligned and
    st_tcb_at (Not \<circ> halted) sender and
    st_tcb_at active rcvr and
    K (sender \<noteq> rcvr)\<rbrace>
   setup_caller_cap sender rcvr grant
   \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: setup_caller_cap_def)
  apply (intro conjI impI)
   apply (rule hoare_pre)
    apply (wp set_thread_state_valid_cap sts_tcb_cap_valid_cases)
   apply (subgoal_tac "s \<turnstile> cap.ReplyCap sender False {AllowGrant, AllowWrite}")
    prefer 2
    apply (fastforce simp: valid_cap_def cap_aligned_def word_bits_def
                           st_tcb_def2 tcb_at_def is_tcb
                     dest: pspace_alignedD get_tcb_SomeD)
   apply (subgoal_tac "tcb_cap_valid (cap.ReplyCap sender False {AllowGrant, AllowWrite})
                                     (rcvr, tcb_cnode_index 3) s")
    prefer 2
    apply (clarsimp simp: tcb_cap_valid_def is_cap_simps
                   split: Structures_A.thread_state.splits
                   elim!: pred_tcb_weakenE)
   apply (clarsimp simp: valid_tcb_state_def st_tcb_def2)
(* \<not> grant *)
  apply (rule hoare_pre)
   apply (wp set_thread_state_valid_cap sts_tcb_cap_valid_cases)
  apply (subgoal_tac "s \<turnstile> cap.ReplyCap sender False {AllowWrite}")
   prefer 2
   apply (fastforce simp: valid_cap_def cap_aligned_def word_bits_def
                          st_tcb_def2 tcb_at_def is_tcb
                          dest: pspace_alignedD get_tcb_SomeD)
  apply (subgoal_tac "tcb_cap_valid (cap.ReplyCap sender False {AllowWrite})
                                    (rcvr, tcb_cnode_index 3) s")
   prefer 2
   apply (clarsimp simp: tcb_cap_valid_def is_cap_simps
                  split: Structures_A.thread_state.splits
                  elim!: pred_tcb_weakenE)
  apply (clarsimp simp: valid_tcb_state_def st_tcb_def2)
  done

context Ipc_AI_2 begin

lemma setup_caller_cap_mdb[wp]:
  "\<And>sender.
    \<lbrace>valid_mdb and valid_objs and pspace_aligned and
          st_tcb_at (Not \<circ> halted) sender and
          K (sender \<noteq> rcvr)\<rbrace>
      setup_caller_cap sender rcvr grant
    \<lbrace>\<lambda>_. valid_mdb :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  unfolding setup_caller_cap_def
  apply (rule hoare_pre)
   apply (wp set_thread_state_valid_cap set_thread_state_cte_wp_at | simp)+
  apply (clarsimp simp: valid_cap_def cap_aligned_def word_bits_def
                        st_tcb_def2 tcb_at_def is_tcb
                        st_tcb_at_reply_cap_valid)
  apply (frule(1) valid_tcb_objs)
  apply (clarsimp dest!:pspace_alignedD get_tcb_SomeD)
  apply (clarsimp simp:valid_tcb_def)
  apply (clarsimp simp:valid_tcb_state_def)
done

end

lemma setup_caller_cap_iflive[wp]:
  "\<lbrace>if_live_then_nonz_cap and st_tcb_at (Not \<circ> halted) sender\<rbrace>
   setup_caller_cap sender rcvr grant
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  unfolding setup_caller_cap_def
  apply (wp cap_insert_iflive)
  apply (clarsimp elim!: st_tcb_ex_cap)
  done


crunch setup_caller_cap
  for zombies[wp]: "zombies_final"


lemma setup_caller_cap_globals[wp]:
  "\<lbrace>valid_objs and valid_global_refs and
    st_tcb_at (Not \<circ> halted) sender\<rbrace>
   setup_caller_cap sender rcvr grant
   \<lbrace>\<lambda>rv. valid_global_refs\<rbrace>"
  unfolding setup_caller_cap_def
  apply wpsimp
  apply (frule st_tcb_at_reply_cap_valid, clarsimp+)
  apply (clarsimp simp: cte_wp_at_caps_of_state cap_range_def)
  done


lemma setup_caller_cap_ifunsafe[wp]:
  "\<lbrace>if_unsafe_then_cap and valid_objs and tcb_at rcvr and ex_nonz_cap_to rcvr\<rbrace>
  setup_caller_cap sender rcvr grant
  \<lbrace>\<lambda>rv. if_unsafe_then_cap\<rbrace>"
  unfolding setup_caller_cap_def
  by (wpsimp wp: cap_insert_ifunsafe ex_cte_cap_to_pres
           simp: ex_nonz_tcb_cte_caps dom_tcb_cap_cases)

lemmas (in Ipc_AI_2) transfer_caps_loop_cap_to[wp]
  = transfer_caps_loop_pres [OF cap_insert_ex_cap]

crunch set_extra_badge
  for cap_to[wp]: "ex_nonz_cap_to p"

context Ipc_AI_2 begin

crunch do_ipc_transfer
  for cap_to[wp]: "ex_nonz_cap_to p :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps simp: zipWithM_x_mapM ignore: transfer_caps_loop)

crunch receive_ipc
  for it[wp]: "\<lambda>s::'state_ext state. P (idle_thread s)"
  (wp: hoare_drop_imps simp: crunch_simps zipWithM_x_mapM)

end

lemma setup_caller_cap_idle[wp]:
  "\<lbrace>valid_idle and (\<lambda>s. st \<noteq> idle_thread s \<and> rt \<noteq> idle_thread s)\<rbrace>
   setup_caller_cap st rt grant
   \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  unfolding setup_caller_cap_def
  apply (wp cap_insert_idle | simp)+
  done


crunch setup_caller_cap
  for typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  (wp: crunch_wps simp: crunch_simps)


crunch setup_caller_cap
  for arch[wp]: "\<lambda>s. P (arch_state s)"
  (wp: crunch_wps simp: crunch_simps)


crunch setup_caller_cap
  for irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"


crunch set_thread_state
  for Pmdb[wp]: "\<lambda>s. P (cdt s)"

lemma setup_caller_cap_reply[wp]:
  "\<lbrace>valid_reply_caps and pspace_aligned and
    st_tcb_at (Not \<circ> awaiting_reply) st and tcb_at rt\<rbrace>
   setup_caller_cap st rt grant
   \<lbrace>\<lambda>rv. valid_reply_caps\<rbrace>"
  unfolding setup_caller_cap_def
  apply wp
   apply (rule_tac Q'="\<lambda>rv s. pspace_aligned s \<and> tcb_at st s \<and>
         st_tcb_at (\<lambda>ts. ts = Structures_A.thread_state.BlockedOnReply) st s \<and>
         \<not> has_reply_cap st s"
                 in hoare_post_imp)
    apply (fastforce simp: valid_cap_def cap_aligned_def
                           tcb_at_def pspace_aligned_def word_bits_def
                    dest!: get_tcb_SomeD
                    elim!: my_BallE [where y=st] pred_tcb_weakenE)
   apply (wp sts_st_tcb_at has_reply_cap_cte_lift)
  apply (strengthen reply_cap_doesnt_exist_strg)
  apply (clarsimp simp: st_tcb_at_tcb_at)+
  apply (clarsimp intro!: tcb_at_cte_at)
  done


lemma setup_caller_cap_reply_masters[wp]:
  "\<lbrace>valid_reply_masters and tcb_at rt\<rbrace>
   setup_caller_cap st rt grant
   \<lbrace>\<lambda>rv. valid_reply_masters\<rbrace>"
  unfolding setup_caller_cap_def
  by (wpsimp simp: is_cap_simps tcb_at_cte_at dom_tcb_cap_cases)


lemma setup_caller_cap_irq_handlers[wp]:
  "\<lbrace>valid_irq_handlers and tcb_at st\<rbrace>
   setup_caller_cap st rt grant
   \<lbrace>\<lambda>rv. valid_irq_handlers\<rbrace>"
  unfolding setup_caller_cap_def
  by (wpsimp simp: is_cap_simps tcb_at_cte_at dom_tcb_cap_cases)

context Ipc_AI_2 begin

lemma setup_caller_cap_valid_arch_caps[wp]:
  "\<lbrace>valid_arch_caps and valid_objs and st_tcb_at (Not o halted) sender\<rbrace>
      setup_caller_cap sender recvr grant
    \<lbrace>\<lambda>rv. valid_arch_caps :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  unfolding setup_caller_cap_def
  apply (wpsimp wp: cap_insert_valid_arch_caps)
  apply (auto elim: st_tcb_at_reply_cap_valid)
  done

end

crunch set_simple_ko
  for irq_handlers[wp]: "valid_irq_handlers"
  (wp: crunch_wps)

crunch setup_caller_cap
  for vspace_objs[wp]: "valid_vspace_objs"

crunch setup_caller_cap
  for v_ker_map[wp]: "valid_kernel_mappings"

crunch setup_caller_cap
  for eq_ker_map[wp]: "equal_kernel_mappings"

crunch setup_caller_cap
  for asid_map[wp]: "valid_asid_map"

crunch setup_caller_cap
  for global_pd_mappings[wp]: "valid_global_vspace_mappings"

crunch setup_caller_cap
  for pspace_in_kernel_window[wp]: "pspace_in_kernel_window"

lemma setup_caller_cap_cap_refs_in_window[wp]:
  "\<lbrace>valid_objs and cap_refs_in_kernel_window and
    st_tcb_at (Not \<circ> halted) sender\<rbrace>
   setup_caller_cap sender rcvr grant
   \<lbrace>\<lambda>rv. cap_refs_in_kernel_window\<rbrace>"
  unfolding setup_caller_cap_def
  apply (rule hoare_pre, wp)
  apply clarsimp
  apply (frule st_tcb_at_reply_cap_valid, clarsimp+)
  apply (clarsimp simp: cte_wp_at_caps_of_state cap_range_def)
  done

crunch setup_caller_cap
  for only_idle[wp]: only_idle
  (wp: sts_only_idle)

crunch setup_caller_cap
  for valid_ioc[wp]: valid_ioc

crunch setup_caller_cap
  for vms[wp]: "valid_machine_state"

crunch setup_caller_cap
  for valid_irq_states[wp]: "valid_irq_states"

crunch setup_caller_cap
  for pspace_respects_device_region[wp]: "pspace_respects_device_region"

crunch setup_caller_cap
  for cap_refs_respects_device_region: "cap_refs_respects_device_region"



lemma same_caps_tcb_upd_state[simp]:
 "same_caps (TCB (tcb \<lparr>tcb_state := BlockedOnReply\<rparr>)) = same_caps (TCB tcb)"
 apply (rule ext)
 apply (simp add:tcb_cap_cases_def)
 done

lemma same_caps_simps[simp]:
 "same_caps (CNode sz cs)  = (\<lambda>val. val = CNode sz cs)"
 "same_caps (TCB tcb)      = (\<lambda>val. (\<exists>tcb'. val = TCB tcb'
                                         \<and> (\<forall>(getF, t) \<in> ran tcb_cap_cases. getF tcb' = getF tcb)))"
 "same_caps (Endpoint ep)  = (\<lambda>val. is_ep val)"
 "same_caps (Notification ntfn) = (\<lambda>val. is_ntfn val)"
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

lemma setup_caller_cap_refs_respects_device_region[wp]:
    "\<lbrace>cap_refs_respects_device_region and
     valid_objs\<rbrace>
    setup_caller_cap tcb cap grant
    \<lbrace>\<lambda>_. cap_refs_respects_device_region\<rbrace>"
  apply (simp add: setup_caller_cap_def set_thread_state_def)+
  apply (intro conjI impI)
   apply (wp set_object_cap_refs_respects_device_region set_object_cte_wp_at | clarsimp )+
   apply (clarsimp dest!: get_tcb_SomeD simp: tcb_cap_cases_def obj_at_def cap_range_def)
   apply (rule tcb_at_cte_at_2)
   apply (simp add: tcb_at_def get_tcb_def)
  apply (wp set_object_cap_refs_respects_device_region set_object_cte_wp_at | clarsimp )+
  apply (clarsimp dest!: get_tcb_SomeD simp: tcb_cap_cases_def obj_at_def cap_range_def)
  apply (rule tcb_at_cte_at_2)
  apply (simp add: tcb_at_def get_tcb_def)
  done



context Ipc_AI_2 begin
crunch do_ipc_transfer
  for valid_irq_states[wp]: "valid_irq_states :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps  simp: crunch_simps)

crunch do_fault_transfer
  for cap_refs_respects_device_region[wp]: "cap_refs_respects_device_region :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps hoare_vcg_const_Ball_lift
    VSpace_AI.cap_refs_respects_device_region_dmo ball_tcb_cap_casesI
    const_on_failure_wp simp: crunch_simps zipWithM_x_mapM ball_conj_distrib)

crunch copy_mrs
  for cap_refs_respects_device_region[wp]: "cap_refs_respects_device_region"
  (wp: crunch_wps hoare_vcg_const_Ball_lift
    VSpace_AI.cap_refs_respects_device_region_dmo ball_tcb_cap_casesI
    const_on_failure_wp simp: crunch_simps zipWithM_x_mapM ball_conj_distrib)


lemma invs_respects_device_region:
  "invs s \<Longrightarrow> cap_refs_respects_device_region s \<and> pspace_respects_device_region s"
  by (clarsimp simp: invs_def valid_state_def)

end

locale Ipc_AI_3 = Ipc_AI_2 state_ext_t some_t
  for state_ext_t :: "'state_ext::state_ext itself"  and some_t :: "'t itself"+
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
  assumes do_ipc_transfer_valid_arch:
    "\<And>ep bg grt r.
      \<lbrace>valid_arch_state and valid_objs and valid_mdb \<rbrace>
      do_ipc_transfer s ep bg grt r
      \<lbrace>\<lambda>rv. valid_arch_state :: 'state_ext state \<Rightarrow> bool\<rbrace>"



lemma complete_signal_invs:
  "\<lbrace>invs and tcb_at tcb\<rbrace>
     complete_signal ntfnptr tcb
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: complete_signal_def)
  apply (rule bind_wp[OF _ get_simple_ko_sp])
  apply (rule hoare_pre)
   apply (wp set_ntfn_minor_invs | wpc | simp)+
   apply (rule_tac Q'="\<lambda>_ s. (state_refs_of s ntfnptr = ntfn_bound_refs (ntfn_bound_tcb ntfn))
                      \<and> (\<exists>T. typ_at T ntfnptr s) \<and> valid_ntfn (ntfn_set_obj ntfn IdleNtfn) s
                      \<and> ((\<exists>y. ntfn_bound_tcb ntfn = Some y) \<longrightarrow> ex_nonz_cap_to ntfnptr s)"
                      in hoare_strengthen_post)
    apply (wp hoare_vcg_all_lift hoare_weak_lift_imp hoare_vcg_ex_lift | wpc
         | simp add: live_def valid_ntfn_def valid_bound_tcb_def split: option.splits)+
    apply ((clarsimp simp: obj_at_def state_refs_of_def)+)[2]
  apply (rule_tac obj_at_valid_objsE[OF _ invs_valid_objs]; clarsimp)
    apply assumption+
  by (fastforce simp: ko_at_state_refs_ofD valid_ntfn_def valid_obj_def obj_at_def is_ntfn live_def elim: if_live_then_nonz_capD[OF invs_iflive])

crunch as_user
  for pspace_respects_device_region[wp]: "pspace_respects_device_region"
  (simp: crunch_simps wp: crunch_wps set_object_pspace_respects_device_region pspace_respects_device_region_dmo)

lemmas [wp] = as_user.valid_arch_state

context Ipc_AI_3 begin
lemma ri_invs':
  fixes Q t cap is_blocking
  notes if_split[split del]
  notes hyp_refs_of_simps[simp del]
  assumes set_endpoint_Q[wp]: "\<And>a b.\<lbrace>Q\<rbrace> set_endpoint a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes set_notification_Q[wp]: "\<And>a b.\<lbrace>Q\<rbrace> complete_signal a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes sts_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> set_thread_state a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes ext_Q[wp]: "\<And>a. \<lbrace>Q and valid_objs\<rbrace> possible_switch_to a \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes scc_Q[wp]: "\<And>a b c. \<lbrace>valid_mdb and Q\<rbrace> setup_caller_cap a b c \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes dit_Q[wp]: "\<And>a b c d e. \<lbrace>valid_mdb and valid_objs and Q\<rbrace> do_ipc_transfer a b c d e \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes failed_transfer_Q[wp]: "\<And>a. \<lbrace>Q\<rbrace> do_nbrecv_failed_transfer a \<lbrace>\<lambda>_. Q\<rbrace>"
  notes dxo_wp_weak[wp del]
  shows
  "\<lbrace>(invs::'state_ext state \<Rightarrow> bool) and Q and st_tcb_at active t and ex_nonz_cap_to t
         and cte_wp_at ((=) cap.NullCap) (t, tcb_cnode_index 3)
         and (\<lambda>s. \<forall>r\<in>zobj_refs cap. ex_nonz_cap_to r s)\<rbrace>
     receive_ipc t cap is_blocking \<lbrace>\<lambda>r s. invs s \<and> Q s\<rbrace>" (is "\<lbrace>?pre\<rbrace> _ \<lbrace>_\<rbrace>")
  apply (simp add: receive_ipc_def split_def)
  apply (cases cap, simp_all)
  apply (rename_tac ep badge rights)
  apply (rule bind_wp[OF _ get_simple_ko_sp])
  apply (rule bind_wp[OF _ gbn_sp])
  apply (rule bind_wp)
  (* set up precondition for old proof *)
   apply (rule_tac P''="ko_at (Endpoint rv) ep and ?pre" in hoare_vcg_if_split)
    apply (wp complete_signal_invs)
   apply (case_tac rv)
     apply (wp | rule hoare_pre, wpc | simp)+
           apply (simp add: invs_def valid_state_def valid_pspace_def)
           apply (rule hoare_pre, wp valid_irq_node_typ)
           apply (simp add: valid_ep_def)
          apply (wp valid_irq_node_typ sts_only_idle sts_typ_ats[simplified ep_at_def2, simplified]
                    failed_transfer_Q[simplified do_nbrecv_failed_transfer_def, simplified]
                 | simp add: live_def do_nbrecv_failed_transfer_def)+
     apply (clarsimp simp: st_tcb_at_tcb_at valid_tcb_state_def invs_def valid_state_def valid_pspace_def)
     apply (rule conjI, clarsimp elim!: obj_at_weakenE simp: is_ep_def)
     apply (rule conjI, clarsimp simp: st_tcb_at_reply_cap_valid)
     apply (rule conjI)
      apply (subgoal_tac "ep \<noteq> t")
       apply (drule obj_at_state_refs_ofD)
       apply (drule active_st_tcb_at_state_refs_ofD)
       apply (erule delta_sym_refs)
        apply (clarsimp split: if_split_asm)
       apply (clarsimp split: if_split_asm if_split)
       apply (fastforce dest!: symreftype_inverse'
                         simp: pred_tcb_at_def2 tcb_bound_refs_def2)
      apply (clarsimp simp: obj_at_def st_tcb_at_def)
     apply (simp add: obj_at_def is_ep_def)
     apply (fastforce dest!: idle_no_ex_cap valid_reply_capsD
                      simp: st_tcb_def2)
    apply (simp add: invs_def valid_state_def valid_pspace_def)
    apply (wp hoare_drop_imps valid_irq_node_typ hoare_post_imp[OF disjI1]
              sts_only_idle do_ipc_transfer_valid_arch
         | simp add: valid_tcb_state_def cap_range_def
         | strengthen reply_cap_doesnt_exist_strg | wpc
         | (wp hoare_vcg_conj_lift | wp dxo_wp_weak | simp)+)+
    apply (clarsimp simp: st_tcb_at_tcb_at neq_Nil_conv)
    apply (frule(1) sym_refs_obj_atD)
    apply (frule(1) hyp_sym_refs_obj_atD)
    apply (frule ko_at_state_refs_ofD)
    apply (frule ko_at_state_hyp_refs_ofD)
    apply (erule(1) obj_at_valid_objsE)
    apply (clarsimp simp: st_tcb_at_refs_of_rev st_tcb_at_tcb_at
                          valid_obj_def ep_redux_simps
                    cong: list.case_cong if_cong)
    apply (frule(1) st_tcb_ex_cap[where P="\<lambda>ts. \<exists>pl. ts = st pl" for st],
           clarsimp+)
    apply (clarsimp simp: valid_ep_def)
    apply (frule active_st_tcb_at_state_refs_ofD)
    apply (frule st_tcb_at_state_refs_ofD
                 [where P="\<lambda>ts. \<exists>pl. ts = st pl" for st])
    apply (subgoal_tac "y \<noteq> t \<and> y \<noteq> idle_thread s \<and> t \<noteq> idle_thread s \<and>
                        idle_thread s \<notin> set ys")
     apply (clarsimp simp: st_tcb_def2 is_ep_def
       conj_comms tcb_at_cte_at_2)
     apply (clarsimp simp: obj_at_def)
     apply (erule delta_sym_refs)
      apply (clarsimp split: if_split_asm)
     apply (clarsimp split: if_split_asm if_split) (* FIXME *)
       apply ((fastforce simp: pred_tcb_at_def2 tcb_bound_refs_def2 is_tcb
                       dest!: symreftype_inverse')+)[3]
    apply (rule conjI)
     apply (clarsimp simp: pred_tcb_at_def2 tcb_bound_refs_def2
                     split: if_split_asm)
     apply (simp add: set_eq_subset)

    apply (rule conjI, clarsimp dest!: idle_no_ex_cap)+
    apply (simp add: idle_not_queued')
   apply (simp add: invs_def valid_state_def valid_pspace_def)
   apply (rule hoare_pre)
    apply (wp hoare_vcg_const_Ball_lift valid_irq_node_typ sts_only_idle
              sts_typ_ats[simplified ep_at_def2, simplified]
              failed_transfer_Q[unfolded do_nbrecv_failed_transfer_def, simplified]
              | simp add: live_def valid_ep_def do_nbrecv_failed_transfer_def
              | wpc)+
   apply (clarsimp simp: valid_tcb_state_def st_tcb_at_tcb_at)
   apply (rule conjI, clarsimp elim!: obj_at_weakenE simp: is_ep_def)
   apply (rule conjI, fastforce simp: st_tcb_def2)
   apply (frule ko_at_state_refs_ofD)
   apply (frule active_st_tcb_at_state_refs_ofD)
   apply (frule(1) sym_refs_ko_atD)
   apply (rule obj_at_valid_objsE, assumption+)
   apply (clarsimp simp: valid_obj_def valid_ep_def)
   apply (rule context_conjI)
    apply (rule notI, (drule(1) bspec)+, (drule obj_at_state_refs_ofD)+, clarsimp)
    apply (clarsimp simp: pred_tcb_at_def2 tcb_bound_refs_def2)
    apply (blast intro: reftype.simps)
   apply (rule conjI, erule delta_sym_refs)
     apply (clarsimp split: if_split_asm if_split)
     apply (rule conjI, rule impI)
      apply (clarsimp simp: pred_tcb_at_def2 obj_at_def)
     apply (fastforce simp: pred_tcb_at_def2 tcb_bound_refs_def2
                     dest!: symreftype_inverse')
    apply (clarsimp split: if_split_asm if_split)
    apply (fastforce simp: pred_tcb_at_def2 tcb_bound_refs_def2
                    dest!: symreftype_inverse')
   apply (fastforce simp: obj_at_def is_ep pred_tcb_at_def2 dest!: idle_no_ex_cap valid_reply_capsD)
  apply (rule hoare_pre)
   apply (wp get_simple_ko_wp | wpc | clarsimp)+
  apply (clarsimp simp: pred_tcb_at_tcb_at)
  done

lemmas ri_invs[wp]
  = ri_invs'[where Q=\<top>,simplified hoare_TrueI, OF TrueI TrueI TrueI,simplified]

end

crunch set_message_info
  for ntfn_at[wp]: "ntfn_at ntfn"

crunch set_message_info
  for typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  (wp: crunch_wps simp: crunch_simps)

crunch set_message_info
  for it[wp]: "\<lambda>s. P (idle_thread s)"
  (wp: crunch_wps simp: crunch_simps)

crunch set_message_info
  for arch[wp]: "\<lambda>s. P (arch_state s)"
  (wp: crunch_wps simp: crunch_simps)

lemma set_message_info_valid_arch [wp]:
  "\<lbrace>valid_arch_state\<rbrace> set_message_info a b \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  unfolding set_message_info_def
  by wp

crunch set_message_info
  for caps[wp]: "\<lambda>s. P (caps_of_state s)"

crunch set_message_info
  for irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"
  (simp: crunch_simps)

lemma set_message_info_global_refs [wp]:
  "\<lbrace>valid_global_refs\<rbrace> set_message_info a b \<lbrace>\<lambda>_. valid_global_refs\<rbrace>"
  by (rule valid_global_refs_cte_lift; wp)

crunch set_mrs
  for irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"
  (wp: crunch_wps simp: crunch_simps)

crunch set_message_info
  for interrupt_states[wp]: "\<lambda>s. P (interrupt_states s)"
  (simp: crunch_simps )

crunch set_mrs
  for interrupt_states[wp]: "\<lambda>s. P (interrupt_states s)"
  (simp: crunch_simps wp: crunch_wps)

lemma tcb_cap_cases_tcb_context:
  "\<forall>(getF, v)\<in>ran tcb_cap_cases.
         getF (tcb_arch_update (arch_tcb_context_set F) tcb) = getF tcb"
  by (rule ball_tcb_cap_casesI, simp+)

crunch set_message_info
  for valid_arch_caps[wp]: "valid_arch_caps"

lemma valid_bound_tcb_exst[iff]:
 "valid_bound_tcb t (trans_state f s) = valid_bound_tcb t s"
  by (auto simp: valid_bound_tcb_def split:option.splits)

(* FIXME: move *)
lemma valid_bound_tcb_typ_at:
  "(\<And>p. \<lbrace>\<lambda>s. typ_at ATCB p s\<rbrace> f \<lbrace>\<lambda>_ s. typ_at ATCB p s\<rbrace>)
   \<Longrightarrow> \<lbrace>\<lambda>s. valid_bound_tcb tcb s\<rbrace> f \<lbrace>\<lambda>_ s. valid_bound_tcb tcb s\<rbrace>"
  apply (clarsimp simp: valid_bound_tcb_def split: option.splits)
  apply (wpsimp wp: hoare_vcg_all_lift tcb_at_typ_at hoare_weak_lift_imp)
  done

crunch set_thread_state, set_message_info, set_mrs, as_user
  for bound_tcb[wp]: "valid_bound_tcb t"
  (rule: valid_bound_tcb_typ_at)

context Ipc_AI_2 begin

lemma rai_invs':
  assumes set_notification_Q[wp]: "\<And>a b.\<lbrace> Q\<rbrace> set_notification a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes sts_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> set_thread_state a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes smi_Q[wp]: "\<And>a b.\<lbrace>Q\<rbrace> set_message_info a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes as_user_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> as_user a b \<lbrace>\<lambda>r::unit. Q\<rbrace>"
  assumes set_mrs_Q[wp]: "\<And>a b c. \<lbrace>Q\<rbrace> set_mrs a b c \<lbrace>\<lambda>_.Q\<rbrace>"
  shows
  "\<lbrace>invs and Q and st_tcb_at active t and ex_nonz_cap_to t
         and (\<lambda>s. \<forall>r\<in>zobj_refs cap. ex_nonz_cap_to r s)
         and (\<lambda>s. \<exists>ntfnptr. is_ntfn_cap cap \<and> cap_ep_ptr cap = ntfnptr \<and>
                     obj_at (\<lambda>ko. \<exists>ntfn. ko = Notification ntfn \<and> (ntfn_bound_tcb ntfn = None
                                                          \<or> ntfn_bound_tcb ntfn = Some t)) ntfnptr s)\<rbrace>
     receive_signal t cap is_blocking
   \<lbrace>\<lambda>r (s::'state_ext state). invs s \<and> Q s\<rbrace>"
  apply (simp add: receive_signal_def)
  apply (cases cap, simp_all)
  apply (rename_tac ntfn badge rights)
  apply (rule bind_wp [OF _ get_simple_ko_sp])
  apply (case_tac "ntfn_obj rv")
    apply (simp add: invs_def valid_state_def valid_pspace_def)
    apply (rule hoare_pre)
     apply (wp set_simple_ko_valid_objs valid_irq_node_typ sts_only_idle
              sts_typ_ats[simplified ntfn_at_def2, simplified] | wpc
          | simp add: live_def valid_ntfn_def do_nbrecv_failed_transfer_def)+
    apply (clarsimp simp: valid_tcb_state_def st_tcb_at_tcb_at)
    apply (rule conjI, clarsimp elim!: obj_at_weakenE simp: is_ntfn_def)
    apply (rule conjI, clarsimp simp: st_tcb_at_reply_cap_valid)
    apply (rule conjI, clarsimp simp: obj_at_def split: option.splits)
    apply (rule conjI, clarsimp simp: valid_bound_tcb_def obj_at_def
                                dest!: st_tcb_at_tcb_at
                                split: option.splits)
    apply (rule conjI)

     apply (subgoal_tac "t \<noteq> ntfn")
      apply (drule ko_at_state_refs_ofD)
      apply (drule active_st_tcb_at_state_refs_ofD)
      apply (erule delta_sym_refs)
       apply (clarsimp split: if_split_asm)
      apply (fastforce simp: pred_tcb_at_def2 tcb_bound_refs_def2 split: if_split_asm)
     apply (clarsimp simp: obj_at_def pred_tcb_at_def)
    apply (simp add: is_ntfn obj_at_def)
    apply (fastforce dest!: idle_no_ex_cap valid_reply_capsD
                    elim!: pred_tcb_weakenE
                    simp: st_tcb_at_reply_cap_valid st_tcb_def2)
   apply (simp add: invs_def valid_state_def valid_pspace_def)
   apply (rule hoare_pre)
    apply (wpsimp wp: set_simple_ko_valid_objs hoare_vcg_const_Ball_lift sts_only_idle
                      valid_irq_node_typ sts_typ_ats[simplified ntfn_at_def2, simplified]
               simp: live_def valid_ntfn_def do_nbrecv_failed_transfer_def)
   apply (clarsimp simp: valid_tcb_state_def st_tcb_at_tcb_at)
   apply (rule conjI, clarsimp elim!: obj_at_weakenE simp: is_ntfn_def)
   apply (rule obj_at_valid_objsE, assumption+)
   apply (clarsimp simp: valid_obj_def valid_ntfn_def)
   apply (frule(1) sym_refs_ko_atD, simp)
   apply (frule ko_at_state_refs_ofD)
   apply (frule active_st_tcb_at_state_refs_ofD)
   apply (rule conjI, clarsimp simp: st_tcb_at_reply_cap_valid)
   apply (rule context_conjI, fastforce simp: pred_tcb_at_def obj_at_def tcb_bound_refs_def2
                                               state_refs_of_def)
   apply (subgoal_tac "ntfn_bound_tcb rv = None")
    apply (rule conjI, clarsimp split: option.splits)
    apply (rule conjI, erule delta_sym_refs)
      apply (fastforce simp: pred_tcb_at_def2 obj_at_def symreftype_inverse'
                      split: if_split_asm)
     apply (fastforce simp: pred_tcb_at_def2 tcb_bound_refs_def2 split: if_split_asm)
    apply (simp add: obj_at_def is_ntfn idle_not_queued)
    apply (fastforce dest: idle_no_ex_cap valid_reply_capsD
                    elim!: pred_tcb_weakenE
                     simp: st_tcb_at_reply_cap_valid st_tcb_def2)
   apply (clarsimp simp: valid_obj_def valid_ntfn_def obj_at_def
                   elim: obj_at_valid_objsE
                  split: option.splits)
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (rule hoare_pre)
   apply (wp set_simple_ko_valid_objs hoare_vcg_const_Ball_lift
             as_user_typ_ats(2)[simplified ntfn_at_def2, simplified]
             valid_irq_node_typ ball_tcb_cap_casesI hoare_weak_lift_imp
             valid_bound_tcb_typ_at[rule_format]
             | simp add: valid_ntfn_def)+
  apply clarsimp
  apply (rule conjI, clarsimp simp: valid_bound_tcb_def obj_at_def pred_tcb_at_def2 is_tcb
                             split: option.splits)
  apply (frule ko_at_state_refs_ofD)
  apply (frule active_st_tcb_at_state_refs_ofD)
  apply (rule conjI, erule delta_sym_refs)
    apply (clarsimp split: if_split_asm)
   apply (clarsimp split: if_split_asm)
  apply (fastforce simp: obj_at_def is_ntfn_def state_refs_of_def
                        valid_idle_def pred_tcb_at_def
                        st_tcb_at_reply_cap_valid
                  dest: valid_reply_capsD)
  done

lemmas rai_invs[wp] = rai_invs'[where Q=\<top>,simplified hoare_TrueI, OF TrueI TrueI TrueI,simplified]

end

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

context Ipc_AI_2 begin
crunch receive_ipc
  for cap_to[wp]: "ex_nonz_cap_to p :: 'state_ext state \<Rightarrow> bool"
  (wp: cap_insert_ex_cap hoare_drop_imps simp: crunch_simps)
end

crunch receive_signal
  for cap_to[wp]: "ex_nonz_cap_to p"
  (wp: crunch_wps)

crunch set_message_info
  for mdb[wp]: valid_mdb
  (wp: crunch_wps mapM_wp')

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

context Ipc_AI_3 begin

lemma si_invs':
  assumes set_endpoint_Q[wp]: "\<And>a b.\<lbrace>Q\<rbrace> set_endpoint a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes ext_Q[wp]: "\<And>a. \<lbrace>Q and valid_objs\<rbrace> possible_switch_to a \<lbrace>\<lambda>_. Q\<rbrace>"
  assumes sts_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> set_thread_state a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes setup_caller_cap_Q[wp]: "\<And>send receive grant. \<lbrace>Q and valid_mdb\<rbrace> setup_caller_cap send receive grant \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes do_ipc_transfer_Q[wp]: "\<And>a b c d e. \<lbrace>Q and valid_objs and valid_mdb\<rbrace> do_ipc_transfer a b c d e \<lbrace>\<lambda>_.Q\<rbrace>"
  notes dxo_wp_weak[wp del]
  shows
  "\<lbrace>invs and Q and st_tcb_at active t and ex_nonz_cap_to epptr and ex_nonz_cap_to t\<rbrace>
     send_ipc bl call badge cg cgr t epptr
   \<lbrace>\<lambda>r (s::'state_ext state). invs s \<and> Q s\<rbrace>"
  apply (simp add: send_ipc_def)
  apply (rule bind_wp [OF _ get_simple_ko_sp])
  apply (case_tac ep, simp_all)
    (* ep=IdleEP, bl *)
    apply (cases bl, simp_all)[1]
     apply (simp add: invs_def valid_state_def valid_pspace_def)
     apply (wpsimp wp: valid_irq_node_typ)
      apply (simp add: live_def valid_ep_def)
      apply (wp valid_irq_node_typ sts_only_idle sts_typ_ats[simplified ep_at_def2, simplified])
     apply (clarsimp simp: valid_tcb_state_def st_tcb_at_tcb_at)+
     apply (rule conjI, clarsimp elim!: obj_at_weakenE simp: is_ep_def)
     apply (rule conjI, clarsimp simp: st_tcb_at_reply_cap_valid)
     apply (rule conjI, clarsimp simp: valid_ep_def pred_tcb_at_tcb_at)
     apply (rule conjI, subgoal_tac "t \<noteq> epptr")
       apply (drule ko_at_state_refs_ofD active_st_tcb_at_state_refs_ofD)+
       apply (erule delta_sym_refs)
        apply (clarsimp split: if_split_asm)
       apply (fastforce simp: pred_tcb_at_def2
                       dest!: refs_in_tcb_bound_refs
                       split: if_split_asm)
      apply (clarsimp simp: pred_tcb_at_def obj_at_def)
     apply (simp add: obj_at_def is_ep)
     apply (fastforce dest: idle_no_ex_cap valid_reply_capsD
                     simp: st_tcb_def2)
     (* ep=IdleEP, \<not>bl *)
    apply wpsimp
   (* ep=SendEP*)
   apply (rename_tac list)
   apply (cases bl, simp_all)[1]
    (* bl *)
    apply (simp add: invs_def valid_state_def valid_pspace_def)
    apply (wpsimp wp: valid_irq_node_typ)
    apply (simp add: live_def valid_ep_def)
    apply (wp hoare_vcg_const_Ball_lift valid_irq_node_typ sts_only_idle
              sts_typ_ats[simplified ep_at_def2, simplified])
    apply (clarsimp simp: valid_tcb_state_def st_tcb_at_tcb_at)
    apply (frule ko_at_state_refs_ofD)
    apply (frule active_st_tcb_at_state_refs_ofD)
    apply (subgoal_tac "t \<noteq> epptr \<and> t \<notin> set list")
     apply (erule obj_at_valid_objsE, clarsimp+)
     apply (clarsimp simp: valid_obj_def valid_ep_def)
     apply (rule conjI, clarsimp simp: obj_at_def is_ep_def)
     apply (rule conjI, clarsimp simp: st_tcb_at_reply_cap_valid)
     apply (rule conjI, clarsimp simp: pred_tcb_at_tcb_at)
     apply (rule conjI, erule delta_sym_refs)
       apply (fastforce split: if_split_asm)
      apply (fastforce simp: pred_tcb_at_def2
                      dest!: refs_in_tcb_bound_refs
                      split: if_split_asm)
     apply (simp add: obj_at_def is_ep idle_not_queued)
     apply (fastforce dest: idle_no_ex_cap valid_reply_capsD
                     simp: st_tcb_def2)
    apply (rule conjI, clarsimp simp: pred_tcb_at_def obj_at_def)
    apply (drule(1) sym_refs_ko_atD, clarsimp simp: st_tcb_at_refs_of_rev)
    apply (drule(1) bspec, clarsimp simp: pred_tcb_at_def obj_at_def)
   (* \<not>bl *)
   apply wpsimp
  (* ep = RecvEP *)
  apply (rename_tac list)
  apply (case_tac list, simp_all add: invs_def valid_state_def valid_pspace_def split del:if_split)
  apply (rename_tac dest queue)
  apply (wp valid_irq_node_typ)
          apply (simp add: if_apply_def2)
          apply (wp hoare_drop_imps sts_st_tcb_at_cases valid_irq_node_typ do_ipc_transfer_tcb_caps
                    sts_only_idle hoare_vcg_if_lift hoare_vcg_disj_lift thread_get_wp'
                    hoare_vcg_all_lift do_ipc_transfer_valid_arch
               | clarsimp simp:is_cap_simps | wpc
               | strengthen reply_cap_doesnt_exist_strg
                            disjI2_strg[where Q="cte_wp_at (\<lambda>cp. is_master_reply_cap cp \<and> R cp) p s"]
               | (wp hoare_vcg_conj_lift hoare_weak_lift_imp | wp dxo_wp_weak | simp)+)+
  apply (clarsimp simp: ep_redux_simps conj_ac cong: list.case_cong if_cong)
  apply (frule(1) sym_refs_ko_atD)
  apply (clarsimp simp: st_tcb_at_refs_of_rev st_tcb_at_tcb_at ep_at_def2)
  apply (frule ko_at_state_refs_ofD)
  apply (frule active_st_tcb_at_state_refs_ofD)
  apply (erule(1) obj_at_valid_objsE)
  apply clarsimp
  apply (subgoal_tac "distinct ([t, dest, epptr, idle_thread s])")
   apply (clarsimp simp: fun_upd_def[symmetric] fun_upd_idem)
   apply (clarsimp simp: valid_obj_def valid_ep_def neq_Nil_conv)
   apply (rule conjI, erule(1) st_tcb_ex_cap)
    apply clarsimp
   apply (simp add: obj_at_def is_ep idle_not_queued')
   apply (subgoal_tac "state_refs_of s t = {r \<in> state_refs_of s t. snd r = TCBBound}")
    apply (subst fun_upd_idem[where x=t], force simp: conj_commute)
    apply (subgoal_tac "sym_refs ((state_refs_of s)(epptr := set queue \<times> {EPRecv}, dest := {r \<in> state_refs_of s dest. snd r = TCBBound}))")
     apply (fastforce elim!: pred_tcb_weakenE st_tcb_at_reply_cap_valid simp: conj_commute)

    apply (erule delta_sym_refs)
     apply (clarsimp simp: fun_upd_def split: if_split_asm)
    apply (fastforce simp: fun_upd_def
                    dest!: symreftype_inverse' st_tcb_at_state_refs_ofD refs_in_tcb_bound_refs
                    split: if_split_asm)
   apply (clarsimp dest!: st_tcb_at_state_refs_ofD simp: sts_refs_of_helper)
   apply fastforce
  apply (drule bound_tcb_at_state_refs_ofD)
  apply (clarsimp simp: tcb_bound_refs_def2)
  apply (rule conjI, clarsimp dest!: st_tcb_at_state_refs_ofD, (auto simp: set_eq_iff)[1])
  apply (rule conjI, clarsimp, (auto simp: set_eq_iff)[1])
  apply (rule conjI, clarsimp simp: idle_no_ex_cap idle_not_queued' idle_no_refs)
  apply (rule conjI, clarsimp dest!: st_tcb_at_tcb_at simp: obj_at_def is_tcb)
  apply (auto dest!: st_tcb_at_state_refs_ofD simp: idle_no_ex_cap idle_not_queued' idle_no_refs)
  done

lemma hf_invs':
  assumes set_endpoint_Q[wp]: "\<And>a b.\<lbrace>Q\<rbrace> set_endpoint a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes sts_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> set_thread_state a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes ext_Q[wp]: "\<And>a. \<lbrace>Q and valid_objs\<rbrace> possible_switch_to a \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes setup_caller_cap_Q[wp]: "\<And>send receive grant. \<lbrace>Q and valid_mdb\<rbrace> setup_caller_cap send receive grant \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes do_ipc_transfer_Q[wp]: "\<And>a b c d e. \<lbrace>Q and valid_objs and valid_mdb\<rbrace> do_ipc_transfer a b c d e \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes thread_set_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> thread_set a b \<lbrace>\<lambda>_.Q\<rbrace>"
  notes si_invs''[wp] = si_invs'[where Q=Q]
  shows
  "\<lbrace>invs and Q and st_tcb_at active t and ex_nonz_cap_to t and (\<lambda>_. valid_fault f)\<rbrace>
   handle_fault t f
   \<lbrace>\<lambda>r (s::'state_ext state). invs s \<and> Q s\<rbrace>"
  apply (cases "valid_fault f"; clarsimp)
  apply (simp add: handle_fault_def)
  apply wp
     apply (simp add: handle_double_fault_def)
     apply (wp sts_invs_minor)
   apply (simp add: send_fault_ipc_def Let_def)
   apply (wpsimp wp: thread_set_invs_trivial
                     thread_set_no_change_tcb_state ex_nonz_cap_to_pres
                     thread_set_cte_wp_at_trivial
                     hoare_vcg_all_liftE_R
          | clarsimp simp: tcb_cap_cases_def
          | erule disjE)+
     apply (wpe lookup_cap_ex_cap)
     apply (wpsimp wp: hoare_vcg_all_liftE_R
        | strengthen reply_cap_doesnt_exist_strg
        | wp (once) hoare_drop_imps)+
  apply (simp add: conj_comms)
  apply (fastforce elim!: pred_tcb_weakenE
               simp: invs_def valid_state_def valid_idle_def st_tcb_def2
                     idle_no_ex_cap pred_tcb_def2
              split: Structures_A.thread_state.splits)
  done

lemmas hf_invs[wp] = hf_invs'[where Q=\<top>,simplified hoare_TrueI, OF TrueI TrueI TrueI TrueI TrueI,simplified]

end

crunch set_message_info
  for pred_tcb_at[wp]: "pred_tcb_at proj P t"

lemma rai_pred_tcb_neq:
  "\<lbrace>pred_tcb_at proj P t' and K (t \<noteq> t')\<rbrace>
     receive_signal t cap is_blocking
   \<lbrace>\<lambda>rv. pred_tcb_at proj P t'\<rbrace>"
  apply (simp add: receive_signal_def)
  apply (rule hoare_pre)
   by (wp sts_st_tcb_at_neq get_simple_ko_wp | wpc | clarsimp simp add: do_nbrecv_failed_transfer_def)+

context Ipc_AI_2 begin
crunch set_mrs
  for ct[wp]: "\<lambda>s::'state_ext state. P (cur_thread s)"
  (wp: case_option_wp mapM_wp simp: crunch_simps)
end

context Ipc_AI_2 begin

crunch receive_ipc
  for typ_at[wp]: "\<lambda>s::'state_ext state. P (typ_at T p s)"
  (wp: hoare_drop_imps simp: crunch_simps)

lemma ri_tcb [wp]:
  "\<lbrace>tcb_at t' :: 'state_ext state \<Rightarrow> bool\<rbrace>
    receive_ipc t cap is_blocking
   \<lbrace>\<lambda>rv. tcb_at t'\<rbrace>"
  by (simp add: tcb_at_typ, wp)

end


crunch receive_signal
  for typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  (wp: crunch_wps simp: crunch_simps)


lemma rai_tcb [wp]:
  "\<lbrace>tcb_at t'\<rbrace> receive_signal t cap is_blocking \<lbrace>\<lambda>rv. tcb_at t'\<rbrace>"
  by (simp add: tcb_at_typ) wp

context Ipc_AI_2 begin

lemmas transfer_caps_loop_pred_tcb_at[wp] =
    transfer_caps_loop_pres [OF cap_insert_pred_tcb_at]

end


lemma setup_caller_cap_makes_simple:
  "\<lbrace>st_tcb_at simple t and K (t \<noteq> t')\<rbrace>
     setup_caller_cap t' t'' grant
   \<lbrace>\<lambda>rv. st_tcb_at simple t\<rbrace>"
  unfolding setup_caller_cap_def
  apply (wp sts_st_tcb_at_cases | simp)+
  done

context Ipc_AI_2 begin

lemma si_blk_makes_simple:
  "\<lbrace>st_tcb_at simple t and K (t \<noteq> t') :: 'state_ext state \<Rightarrow> bool\<rbrace>
     send_ipc True call bdg x gr t' ep
   \<lbrace>\<lambda>rv. st_tcb_at simple t\<rbrace>"
  apply (simp add: send_ipc_def)
  apply (rule bind_wp [OF _ get_simple_ko_inv])
  apply (case_tac epa, simp_all)
    apply (wp sts_st_tcb_at_cases)
    apply clarsimp
   apply (wp sts_st_tcb_at_cases)
   apply clarsimp
  apply (rule hoare_gen_asm[simplified])
  apply (rename_tac list)
  apply (case_tac list, simp_all split del:if_split)
  apply (rule bind_wp [OF _ set_simple_ko_pred_tcb_at])
  apply (rule bind_wp [OF _ gts_sp])
  apply (rename_tac recv_state)
  apply (case_tac recv_state, simp_all split del: if_split)
  apply (wp sts_st_tcb_at_cases setup_caller_cap_makes_simple
            hoare_drop_imps
            | simp add: if_apply_def2 split del: if_split)+
  done

end

lemma ep_ntfn_cap_case_helper:
  "(case x of cap.EndpointCap ref bdg r \<Rightarrow> P ref bdg r
           |  cap.NotificationCap ref bdg r \<Rightarrow> Q ref bdg r
           |  _ \<Rightarrow> R)
   = (if is_ep_cap x then P (cap_ep_ptr x) (cap_ep_badge x) (cap_rights x) else
      if is_ntfn_cap x then Q (cap_ep_ptr x) (cap_ep_badge x) (cap_rights x) else
      R)"
  by (cases x, simp_all)

context Ipc_AI_2 begin

lemma sfi_makes_simple:
  "\<lbrace>st_tcb_at simple t and K (t \<noteq> t') :: 'state_ext state \<Rightarrow> bool\<rbrace>
     send_fault_ipc t' ft
   \<lbrace>\<lambda>rv. st_tcb_at simple t\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: send_fault_ipc_def Let_def ep_ntfn_cap_case_helper
             cong: if_cong)
  apply (wp si_blk_makes_simple hoare_drop_imps
            thread_set_no_change_tcb_state
       | simp)+
  done

lemma hf_makes_simple:
  "\<lbrace>st_tcb_at simple t' and K (t \<noteq> t') :: 'state_ext state \<Rightarrow> bool\<rbrace>
     handle_fault t ft
   \<lbrace>\<lambda>rv. st_tcb_at simple t'\<rbrace>"
  unfolding handle_fault_def
  by (wpsimp wp: sfi_makes_simple sts_st_tcb_at_cases hoare_drop_imps simp: handle_double_fault_def)

end

crunch complete_signal
  for pred_tcb_at[wp]: "pred_tcb_at proj t p"

context Ipc_AI_2 begin

lemma ri_makes_simple:
  "\<lbrace>st_tcb_at simple t' and K (t \<noteq> t') :: 'state_ext state \<Rightarrow> bool\<rbrace>
     receive_ipc t cap is_blocking
   \<lbrace>\<lambda>rv. st_tcb_at simple t'\<rbrace>" (is "\<lbrace>?pre\<rbrace> _ \<lbrace>_\<rbrace>")
  apply (rule hoare_gen_asm)
  apply (simp add: receive_ipc_def split_def)
  apply (case_tac cap, simp_all)
  apply (rule bind_wp [OF _ get_simple_ko_sp])
  apply (rule bind_wp [OF _ gbn_sp])
  apply (rule bind_wp)
   apply (rename_tac ep I DO rv CARE NOT)
   apply (rule_tac P''="ko_at (Endpoint rv) ep and ?pre" in hoare_vcg_if_split)
    apply (wp complete_signal_invs)
   apply (case_tac rv, simp_all)
     apply (rule hoare_pre, wpc)
       apply (wp sts_st_tcb_at_cases, simp)
      apply (simp add: do_nbrecv_failed_transfer_def, wp)
     apply clarsimp
    apply (rule bind_wp [OF _ assert_sp])
    apply (rule bind_wp [where Q'="\<lambda>s. st_tcb_at simple t'"])
     apply (rule bind_wp [OF _ gts_sp])
     apply (rule hoare_pre)
      apply (wp setup_caller_cap_makes_simple sts_st_tcb_at_cases
                hoare_vcg_all_lift hoare_vcg_const_imp_lift
                hoare_drop_imps
           | wpc | simp)+
     apply (fastforce simp: pred_tcb_at_def obj_at_def)
    apply (wp, simp)
   apply (wp sts_st_tcb_at_cases | rule hoare_pre, wpc | simp add: do_nbrecv_failed_transfer_def)+
   apply (wp get_simple_ko_wp | wpc | simp)+
  done

end

lemma rai_makes_simple:
  "\<lbrace>st_tcb_at simple t' and K (t \<noteq> t')\<rbrace>
     receive_signal t cap is_blocking
   \<lbrace>\<lambda>rv. st_tcb_at simple t'\<rbrace>"
   by (rule rai_pred_tcb_neq)


lemma thread_set_Pmdb:
  "\<lbrace>\<lambda>s. P (cdt s)\<rbrace> thread_set f t \<lbrace>\<lambda>rv s. P (cdt s)\<rbrace>"
  unfolding thread_set_def by wpsimp

end
