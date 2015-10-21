(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory Ipc_AI
imports Finalise_AI
begin

declare if_cong[cong del]

lemmas lookup_slot_wrapper_defs[simp] =
   lookup_source_slot_def lookup_target_slot_def lookup_pivot_slot_def


lemma get_mi_inv[wp]: "\<lbrace>I\<rbrace> get_message_info a \<lbrace>\<lambda>x. I\<rbrace>"
  by (simp add: get_message_info_def user_getreg_inv | wp)+



lemma set_mi_tcb [wp]:
  "\<lbrace> tcb_at t \<rbrace> set_message_info receiver msg \<lbrace>\<lambda>rv. tcb_at t\<rbrace>"
  by (simp add: set_message_info_def) wp

lemma mask_mask:
  "mask_cap R (mask_cap R' c) = mask_cap (R \<inter> R') c"
  by (auto simp: mask_cap_def cap_rights_update_def acap_rights_update_def
                 validate_vm_rights_inter Int_assoc Int_commute[of R']
          split: cap.splits arch_cap.splits)


lemma lsfco_real_cte_at:
  "\<lbrace>valid_objs and valid_cap cn\<rbrace> 
  lookup_slot_for_cnode_op f cn idx depth 
  \<lbrace>\<lambda>rv. real_cte_at rv\<rbrace>,-"
  apply (simp add: lookup_slot_for_cnode_op_def split_def)
  apply (rule conjI)
   prefer 2
   apply clarsimp
   apply (rule hoare_pre)
    apply wp
  apply (clarsimp simp: unlessE_def whenE_def split del: split_if)
  apply (rule hoare_pre)
   apply (wp resolve_address_bits_real_cte_at | wpcw)+
  apply simp
  done

lemma lsfco_cte_at: 
  "\<lbrace>valid_objs and valid_cap cn\<rbrace> 
  lookup_slot_for_cnode_op f cn idx depth 
  \<lbrace>\<lambda>rv. cte_at rv\<rbrace>,-"
  by (rule hoare_post_imp_R, rule lsfco_real_cte_at, simp add: real_cte_at_cte)

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
  "cte_wp_at (op = cap) = cte_wp_at (\<lambda>c. c = cap)"
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
  \<lbrace>\<lambda>rv s. \<forall>x \<in> set rv. cte_wp_at (op = cap.NullCap) x s\<rbrace>"
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
  apply (wp hoare_drop_imps lsfco_real_cte_at lookup_cap_valid | simp | rule get_cap_wp)+
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
  by (cases c) (auto simp: mask_cap_def cap_rights_update_def)


lemma update_cap_data_closedform:
  "update_cap_data pres w cap =
   (case cap of
     cap.EndpointCap r badge rights \<Rightarrow>
       if badge = 0 \<and> \<not> pres then (cap.EndpointCap r (w && mask 28) rights) else cap.NullCap
   | cap.AsyncEndpointCap r badge rights \<Rightarrow>
       if badge = 0 \<and> \<not> pres then (cap.AsyncEndpointCap r (w && mask 28) rights) else cap.NullCap
   | cap.CNodeCap r bits guard \<Rightarrow>
       if word_bits < unat ((w >> 3) && mask 5) + bits
       then cap.NullCap
       else cap.CNodeCap r bits ((\<lambda>g''. drop (size g'' - unat ((w >> 3) && mask 5)) (to_bl g'')) ((w >> 8) && mask 18))
   | cap.ThreadCap r \<Rightarrow> cap.ThreadCap r
   | cap.DomainCap \<Rightarrow> cap.DomainCap
   | cap.UntypedCap p n idx \<Rightarrow> cap.UntypedCap p n idx
   | cap.NullCap \<Rightarrow> cap.NullCap
   | cap.ReplyCap t m \<Rightarrow> cap.ReplyCap t m
   | cap.IRQControlCap \<Rightarrow> cap.IRQControlCap
   | cap.IRQHandlerCap irq \<Rightarrow> cap.IRQHandlerCap irq
   | cap.Zombie r b n \<Rightarrow> cap.Zombie r b n
   | cap.ArchObjectCap cap \<Rightarrow> cap.ArchObjectCap (arch_update_cap_data w cap))"
  apply (cases cap,
         simp_all only: cap.simps update_cap_data_def is_ep_cap.simps if_False if_True
                        is_aep_cap.simps is_cnode_cap.simps is_arch_cap_def word_size
                        cap_ep_badge.simps badge_update_def o_def cap_rights_update_def
                        simp_thms cap_rights.simps Let_def split_def
                        the_cnode_cap_def fst_conv snd_conv fun_app_def the_arch_cap_def
                  cong: if_cong)
  apply auto
  done


lemma update_cap_Null:
  "update_cap_data p D c \<noteq> cap.NullCap \<Longrightarrow> c \<noteq> cap.NullCap"
  by (auto simp: update_cap_data_closedform is_cap_defs)


lemma ensure_no_children_wp:
  "\<lbrace>\<lambda>s. descendants_of p (cdt s) = {} \<longrightarrow> P s\<rbrace> ensure_no_children p \<lbrace>\<lambda>_. P\<rbrace>, -"
  apply (simp add: ensure_no_children_descendants valid_def validE_R_def validE_def)
  apply (auto simp: in_monad)
  done


lemma cap_asid_PageCap_None [simp]:
  "cap_asid (cap.ArchObjectCap (arch_cap.PageCap r R pgsz None)) = None"
  by (simp add: cap_asid_def)


lemma arch_derive_cap_is_derived:
  "\<lbrace>\<lambda>s. cte_wp_at (\<lambda>cap . cap_master_cap cap =
                          cap_master_cap (cap.ArchObjectCap c') \<and> 
                          cap_aligned cap \<and> 
                          cap_asid cap = cap_asid (cap.ArchObjectCap c') \<and>
                          vs_cap_ref cap = vs_cap_ref (cap.ArchObjectCap c')) p s\<rbrace>
     arch_derive_cap c'
   \<lbrace>\<lambda>rv s. cte_wp_at (is_derived (cdt s) p (cap.ArchObjectCap rv)) p s\<rbrace>, -"
  unfolding arch_derive_cap_def
  apply(cases c', simp_all add: is_cap_simps cap_master_cap_def)
      apply((wp throwError_validE_R
             | clarsimp simp: is_derived_def is_cap_simps cap_master_cap_def
                              cap_aligned_def is_aligned_no_overflow is_pt_cap_def
                              cap_asid_def vs_cap_ref_def
             | erule cte_wp_at_weakenE
             | rule conjI
             | simp split: arch_cap.split_asm cap.split_asm option.splits)+)
  done


lemma derive_cap_is_derived:
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
  apply(wp, simp add: o_def)
  apply(rule hoare_pre, wp hoare_drop_imps arch_derive_cap_is_derived)
  apply(clarify, drule cte_wp_at_eqD, clarify)
  apply(frule(1) cte_wp_at_valid_objs_valid_cap)
  apply(erule cte_wp_at_weakenE)
  apply(clarsimp simp: valid_cap_def)
  done


lemma arch_derive_cap_cte:
  "\<lbrace>\<lambda>s. cte_wp_at (\<lambda>c. c \<noteq> cap.NullCap \<and> is_derived (cdt s) p (cap.ArchObjectCap c') c) p s\<rbrace>
    arch_derive_cap c'
  \<lbrace>\<lambda>rv s. cte_wp_at (\<lambda>c. c \<noteq> cap.NullCap \<and> is_derived (cdt s) p (cap.ArchObjectCap rv) c) p s\<rbrace>, -"
  unfolding arch_derive_cap_def
  apply(cases c', simp_all add: is_cap_simps)
      apply(rule hoare_pre, wp ensure_no_children_wp, clarsimp)+
    apply wp?
    apply(erule cte_wp_at_weakenE)
    apply(case_tac c, (clarsimp simp: is_derived_def cap_master_cap_def is_cap_simps 
                                      cap_asid_def is_pt_cap_def vs_cap_ref_def
                               split: cap.splits arch_cap.splits)+)
   apply(rule hoare_pre, wpc, wp, clarsimp)+
  done


lemma derive_cap_cte:
  "\<lbrace>\<lambda>s. c' \<noteq> cap.NullCap \<and> \<not>is_zombie c' \<and> c' \<noteq> cap.IRQControlCap \<longrightarrow> 
        (is_untyped_cap c' \<longrightarrow> descendants_of p (cdt s) = {}) \<longrightarrow>
        cte_wp_at (\<lambda>c. c \<noteq> cap.NullCap \<and> is_derived (cdt s) p c' c) p s\<rbrace>
    derive_cap p c'
  \<lbrace>\<lambda>rv s. rv \<noteq> cap.NullCap \<longrightarrow> 
          cte_wp_at (\<lambda>c. c \<noteq> cap.NullCap \<and> is_derived (cdt s) p rv c) p s\<rbrace>, -"
  unfolding derive_cap_def 
  apply (cases c', simp_all add: is_cap_simps)
          apply ((rule hoare_pre, wp ensure_no_children_wp, simp)+)[11]
  apply (rule hoare_pre, wp)
   apply (simp add: o_def)
   apply (wp arch_derive_cap_cte)
  apply assumption
  done


lemma is_derived_cap_rights [simp]:
  "is_derived m p (cap_rights_update R c) = is_derived m p c"
  apply (rule ext)
  apply (simp add: cap_rights_update_def is_derived_def is_cap_simps)
  apply (case_tac x, simp_all)
           apply (simp add: cap_master_cap_def bits_of_def is_cap_simps
                             vs_cap_ref_def
                     split: cap.split)+
  apply (simp add: is_cap_simps is_page_cap_def
             cong: arch_cap.case_cong)
  apply (simp split: arch_cap.split cap.split
                add: is_cap_simps acap_rights_update_def is_pt_cap_def)
  done


lemma is_derived_mask [simp]:
  "is_derived m p (mask_cap R c) = is_derived m p c"
  by (simp add: mask_cap_def)


lemma is_derived_cap_data:
  "\<lbrakk> update_cap_data pres D c \<noteq> cap.NullCap; is_derived (cdt s) p c c' \<rbrakk> \<Longrightarrow> 
  is_derived (cdt s) p (update_cap_data pres D c) c'"
  apply (case_tac c)
  apply (simp_all add: is_derived_def cap_master_cap_simps split del: split_if
                     split: split_if_asm)
    apply (clarsimp dest!:cap_master_cap_eqDs
      simp:update_cap_data_closedform cap_master_cap_simps
      is_cap_simps vs_cap_ref_def  arch_update_cap_data_def
      split:if_splits)+
  apply (case_tac c')
   apply (clarsimp dest!:cap_master_cap_eqDs 
     simp:cap_master_cap_simps cap_asid_def split:arch_cap.splits option.splits)+
  done


lemma is_derived_remove_rights [simp]:
  "is_derived m p (remove_rights R c) = is_derived m p c"
  by (simp add: remove_rights_def) 


definition
  "valid_message_info mi \<equiv>
     mi_length mi \<le> of_nat msg_max_length \<and>
     mi_extra_caps mi \<le> of_nat msg_max_extra_caps"


lemma data_to_message_info_valid:
  "valid_message_info (data_to_message_info w)"
  apply (simp add: valid_message_info_def data_to_message_info_def)
  apply (rule conjI)
  apply (simp add: word_and_le1 msg_max_length_def msg_max_extra_caps_def Let_def not_less)+
  done


lemma get_mi_valid[wp]:
  "\<lbrace>valid_mdb\<rbrace> get_message_info a \<lbrace>\<lambda>rv s. valid_message_info rv\<rbrace>"
  apply (simp add: get_message_info_def)
  apply (wp | simp add: data_to_message_info_valid)+
  done


crunch inv[wp]: get_extra_cptr P (wp: dmo_inv loadWord_inv)


lemma get_extra_cptrs_inv[wp]:
  "\<lbrace>P\<rbrace> get_extra_cptrs buf mi \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (cases buf, simp_all del: upt.simps)
  apply (wp mapM_wp' dmo_inv loadWord_inv
             | simp add: load_word_offs_def del: upt.simps)+
  done


lemma mapM_length[wp]:
  "\<lbrace>\<lambda>s. P (length xs)\<rbrace> mapM f xs \<lbrace>\<lambda>rv s. P (length rv)\<rbrace>"
  apply (induct xs arbitrary: P)
   apply (simp add: mapM_def sequence_def)
   apply wp
   apply simp
  apply (simp add: mapM_Cons)
  apply wp
   apply simp
   apply assumption
  apply wp
  done


lemma get_extra_cptrs_length[wp]:
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


lemma cap_insert_ep_at[wp]:
  "\<lbrace>ep_at ep\<rbrace> cap_insert cap src dest \<lbrace>\<lambda>rv. ep_at ep\<rbrace>"
  by (simp add: ep_at_typ, wp)


lemma cap_master_cap_remove_rights[simp]:
  "cap_master_cap (cap_rights_update rights cap) = cap_master_cap cap"
  apply (simp add: cap_rights_update_def 
                   acap_rights_update_def
            split: cap.split arch_cap.split)
  apply (simp add: cap_master_cap_def)
  done


lemma cap_badge_rights_update[simp]:
  "cap_badge (cap_rights_update rights cap) = cap_badge cap"
  by (simp add: cap_rights_update_def split: cap.split)


lemma cap_asid_rights_update [simp]:
  "cap_asid (cap_rights_update R c) = cap_asid c"
  apply (simp add: cap_rights_update_def acap_rights_update_def split: cap.splits arch_cap.splits)
  apply (clarsimp simp: cap_asid_def)
  done


lemma get_cap_cte_wp_at_rv:
  "\<lbrace>cte_wp_at (\<lambda>cap. P cap cap) p\<rbrace> get_cap p \<lbrace>\<lambda>rv. cte_wp_at (P rv) p\<rbrace>"
  apply (wp get_cap_wp)
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  done


lemma lsfco_cte_wp_at_univ:
  "\<lbrace>valid_objs and valid_cap root and K (\<forall>cap rv. P cap rv)\<rbrace>
      lookup_slot_for_cnode_op f root idx depth
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
  apply (rule word_eqI)
  apply (case_tac "n < bits")
   apply (cut_tac x=n in word_eqD[OF low])
   apply (simp add: word_size)
  apply (cut_tac x="n - bits" in word_eqD[OF high])
  apply (simp add: nth_shiftr)
  done


lemma cap_rights_update_vs_cap_ref[simp]:
  "vs_cap_ref (cap_rights_update rs cap) = vs_cap_ref cap"
  by (simp add: vs_cap_ref_def cap_rights_update_def
                acap_rights_update_def
         split: cap.split arch_cap.split)


lemma mask_cap_vs_cap_ref[simp]:
  "vs_cap_ref (mask_cap msk cap) = vs_cap_ref cap"
  by (simp add: mask_cap_def)


lemma set_extra_badge_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> set_extra_badge buffer b n \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  by (simp add: set_extra_badge_def store_word_offs_def | wp)+


lemmas set_extra_badge_typ_ats[wp] = abs_typ_at_lifts[OF set_extra_badge_typ_at]

crunch valid_objs [wp]: set_extra_badge valid_objs

crunch aligned [wp]: set_extra_badge pspace_aligned

crunch dist [wp]: set_extra_badge pspace_distinct

crunch valid_mdb [wp]: set_extra_badge valid_mdb

crunch cte_wp_at [wp]: set_extra_badge "cte_wp_at P p"


crunch inv[wp]: get_extra_cptr P (wp: dmo_inv loadWord_inv)

lemma impEM:
  "\<lbrakk>P \<longrightarrow> Q; P; \<lbrakk>P; Q\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  by auto


lemma derive_cap_is_derived_foo:
  "\<lbrace>\<lambda>s. \<forall>cap'. (cte_wp_at (\<lambda>capa.
                 cap_master_cap capa = cap_master_cap cap \<and>
                 (cap_badge capa, cap_badge cap) \<in> capBadge_ordering False \<and>
                 cap_asid capa = cap_asid cap \<and> vs_cap_ref capa = vs_cap_ref cap)
      slot s \<and> valid_objs s \<and> cap' \<noteq> cap.NullCap
          \<longrightarrow> cte_at slot s )
            \<and> (s \<turnstile> cap \<longrightarrow> s \<turnstile> cap')
            \<and> (cap' \<noteq> cap.NullCap \<longrightarrow> cap \<noteq> cap.NullCap \<and> \<not> is_zombie cap \<and> cap \<noteq> cap.IRQControlCap)
          \<longrightarrow> Q cap' s \<rbrace>
      derive_cap slot cap \<lbrace>Q\<rbrace>,-"
  apply (clarsimp simp add: validE_R_def validE_def valid_def
                     split: sum.splits)
  apply (frule in_inv_by_hoareD[OF derive_cap_inv], clarsimp)
  apply (erule allE)
  apply (erule impEM)
   apply (frule use_validE_R[OF _ cap_derive_not_null_helper, OF _ _ imp_refl])
    apply (wp derive_cap_inv)
    apply (intro conjI)
     apply (clarsimp simp:cte_wp_at_caps_of_state)+
     apply (erule(1) use_validE_R[OF _ derive_cap_valid_cap])
    apply simp
  apply simp
  done


lemma cap_rights_update_NullCap[simp]:
  "(cap_rights_update rs cap = cap.NullCap) = (cap = cap.NullCap)"
  by (simp add: cap_rights_update_def split: cap.split)


crunch in_user_frame[wp]: set_extra_badge "in_user_frame buffer"


lemma cap_insert_cte_wp_at:
  "\<lbrace>\<lambda>s. cte_wp_at (is_derived (cdt s) src cap) src s \<and> valid_mdb s \<and> valid_objs s
    \<and> (if p = dest then P cap else cte_wp_at (\<lambda>c. P (masked_as_full c cap)) p s)\<rbrace> cap_insert cap src dest \<lbrace>\<lambda>uu. cte_wp_at P p\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (clarsimp split:split_if_asm)
  apply (clarsimp simp:cap_insert_def)
  apply (wp set_cap_cte_wp_at | simp split del: split_if)+
     apply (clarsimp simp:set_untyped_cap_as_full_def split del:if_splits)
    apply (wp get_cap_wp)
   apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (clarsimp simp:cap_insert_def)
  apply (wp set_cap_cte_wp_at | simp split del: split_if)+
    apply (clarsimp simp:set_untyped_cap_as_full_def split del:if_splits)
   apply (wp set_cap_cte_wp_at get_cap_wp)
  apply (clarsimp simp:cte_wp_at_caps_of_state)
  apply (frule(1) caps_of_state_valid)
  apply (intro conjI impI)
    apply (clarsimp simp:masked_as_full_def split:if_splits)+
   apply (clarsimp simp:valid_mdb_def is_derived_def)
   apply (drule(4) untyped_incD)
   apply (clarsimp simp:is_cap_simps cap_aligned_def
      dest!:valid_cap_aligned split:split_if_asm)
    apply (drule_tac y = "of_nat fa" in word_plus_mono_right[OF _ is_aligned_no_overflow',rotated])
     apply (simp add:word_of_nat_less unat_power_lower32)
    apply (clarsimp simp:p_assoc_help)
   apply (drule(1) caps_of_state_valid)+
   apply (clarsimp simp:valid_cap_def valid_untyped_def max_free_index_def)
  apply (clarsimp simp:masked_as_full_def split:if_splits)
  apply (erule impEM)
    apply (clarsimp simp: is_derived_def split:if_splits)
     apply (clarsimp simp:is_cap_simps vs_cap_ref_def cap_master_cap_simps)
   apply (clarsimp simp:is_cap_simps cap_master_cap_simps dest!:cap_master_cap_eqDs)
  apply (erule impEM)
    apply (clarsimp simp: is_derived_def split:if_splits)
     apply (clarsimp simp:is_cap_simps vs_cap_ref_def cap_master_cap_simps)
   apply (clarsimp simp:is_cap_simps cap_master_cap_simps dest!:cap_master_cap_eqDs)
   apply (clarsimp simp:is_derived_def is_cap_simps cap_master_cap_simps)
  done


lemma set_cap_in_user_frame[wp]:
  "\<lbrace>in_user_frame buffer\<rbrace> set_cap cap ref \<lbrace>\<lambda>_. in_user_frame buffer\<rbrace>"
  by (simp add: in_user_frame_def) (wp hoare_vcg_ex_lift set_cap_typ_at)


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

(* FIXME: name conflicts with WordLemmaBucket.in_emptyE. *)
lemma in_emptyE: "\<lbrakk>A={}; \<exists>x. x\<in> A\<rbrakk> \<Longrightarrow> P" by clarsimp

lemma caps_of_state_orth_original:
  "caps_of_state(s\<lparr>is_original_cap := M \<rparr>) = caps_of_state s"
  by (rule Invariants_AI.revokable_update.caps_of_state_update)


lemma is_derived_cap_rights2[simp]:
  "is_derived m p c (cap_rights_update R c') = is_derived m p c c'"
  apply (case_tac c')
  apply (simp_all add:cap_rights_update_def)
  apply (clarsimp simp:is_derived_def is_cap_simps cap_master_cap_def 
    vs_cap_ref_def split:cap.splits )+
  apply (rename_tac acap1 acap2)
  apply (case_tac acap1)
   apply (simp_all add:acap_rights_update_def)
  done


lemma weak_derived_update_rights:
  "valid_cap cap s \<Longrightarrow> weak_derived cap (cap_rights_update R cap)"
  apply (case_tac cap)
  apply (clarsimp simp:weak_derived_def same_object_as_def
    is_cap_simps cap_rights_update_def acap_rights_update_def copy_of_def)+
  apply (rename_tac arch_cap)
  apply (case_tac arch_cap)
  apply (simp_all add: cap_asid_def cap_vptr_def)
  apply (clarsimp simp:valid_cap_def cap_aligned_def)
  apply (erule is_aligned_no_overflow)
  done


lemma masked_as_full_null_cap[simp]:
  "(masked_as_full x x = cap.NullCap) = (x = cap.NullCap)"
  "(cap.NullCap  = masked_as_full x x) = (x = cap.NullCap)"
  by (case_tac x,simp_all add:masked_as_full_def)+


lemma transfer_caps_loop_mi_label[wp]:
  "\<lbrace>\<lambda>s. P (mi_label mi)\<rbrace>
     transfer_caps_loop ep diminish buffer n caps slots mi
   \<lbrace>\<lambda>mi' s. P (mi_label mi')\<rbrace>"
  apply (induct caps arbitrary: n slots mi)
   apply simp
   apply wp
   apply simp
  apply (clarsimp split del: split_if)
  apply (rule hoare_pre)
   apply (wp const_on_failure_wp hoare_drop_imps | assumption)+
  apply simp
  done


lemma cap_insert_real_cte_at[wp]:
  "\<lbrace>real_cte_at p\<rbrace> cap_insert cap src dest \<lbrace>\<lambda>rv. real_cte_at p\<rbrace>"
  by (simp add: cap_table_at_typ, wp)


lemma valid_remove_rights_If[simp]:
  "valid_cap cap s \<Longrightarrow> valid_cap (if P then remove_rights rs cap else cap) s"
  by simp


declare const_on_failure_wp [wp]


crunch ex_cte_cap_wp_to [wp]: set_extra_badge "ex_cte_cap_wp_to P p"
  (lift: ex_cte_cap_to_pres)


lemma return_value_any_R:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. \<forall>x. Q x s\<rbrace>,- \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,-"
  by (erule hoare_post_imp_R, simp)


lemma cap_insert_assume_null:
  "\<lbrace>P\<rbrace> cap_insert cap src dest \<lbrace>Q\<rbrace> \<Longrightarrow>
   \<lbrace>\<lambda>s. cte_wp_at (op = cap.NullCap) dest s \<longrightarrow> P s\<rbrace> cap_insert cap src dest \<lbrace>Q\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (erule impCE)
   apply (simp add: cap_insert_def)
   apply (rule hoare_seq_ext[OF _ get_cap_sp])+
   apply (clarsimp simp: valid_def cte_wp_at_caps_of_state in_monad
              split del: split_if)
  apply (erule hoare_pre(1))
  apply simp
  done


lemma transfer_caps_loop_presM:
  assumes x: "\<And>cap src dest.
              \<lbrace>\<lambda>s. P s \<and> (vo \<longrightarrow> valid_objs s \<and> valid_mdb s \<and> real_cte_at dest s \<and> s \<turnstile> cap \<and> tcb_cap_valid cap dest s
                                   \<and> real_cte_at src s
                                   \<and> cte_wp_at (is_derived (cdt s) src cap) src s \<and> cap \<noteq> cap.NullCap)
                       \<and> (em \<longrightarrow> cte_wp_at (op = cap.NullCap) dest s)
                       \<and> (ex \<longrightarrow> ex_cte_cap_wp_to (appropriate_cte_cap cap) dest s)\<rbrace>
                 cap_insert cap src dest \<lbrace>\<lambda>rv. P\<rbrace>"
  assumes eb: "\<And>b n. \<lbrace>P\<rbrace> set_extra_badge buffer b n \<lbrace>\<lambda>_. P\<rbrace>"
  shows      "\<lbrace>\<lambda>s. P s \<and> (vo \<longrightarrow> valid_objs s \<and> valid_mdb s \<and> distinct slots \<and>
                                 (\<forall>x \<in> set slots.  cte_wp_at (\<lambda>cap. cap = cap.NullCap) x s \<and> real_cte_at x s) \<and>
                                 (\<forall>x \<in> set caps. valid_cap (fst x) s \<and>
                                  cte_wp_at (\<lambda>cp. fst x \<noteq> cap.NullCap \<longrightarrow> cp \<noteq> fst x \<longrightarrow> cp = masked_as_full (fst x) (fst x)) (snd x) s
                                           \<and> real_cte_at (snd x) s))
                       \<and> (ex \<longrightarrow> (\<forall>x \<in> set slots. ex_cte_cap_wp_to is_cnode_cap x s))\<rbrace>
                  transfer_caps_loop ep diminish buffer n caps slots mi
              \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (induct caps arbitrary: slots n mi)
   apply (simp, wp, simp)
  apply (clarsimp simp add: Let_def split_def whenE_def
                      cong: if_cong list.case_cong split del: split_if)
  apply (rule hoare_pre)
   apply (wp eb hoare_vcg_const_imp_lift hoare_vcg_const_Ball_lift static_imp_wp
           | assumption | simp split del: split_if)+
      apply (rule cap_insert_assume_null)
      apply (wp x hoare_vcg_const_Ball_lift cap_insert_cte_wp_at static_imp_wp)
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
      apply (wp derive_cap_is_derived_foo)
  apply (clarsimp simp: cte_wp_at_caps_of_state
                        ex_cte_cap_to_cnode_always_appropriate_strg
                        real_cte_tcb_valid caps_of_state_valid
             split del: split_if)
  apply (clarsimp simp: remove_rights_def caps_of_state_valid
                        neq_Nil_conv cte_wp_at_caps_of_state
                        imp_conjR[symmetric] conj_comms
                 split del: if_splits)
  apply (intro conjI)
   apply clarsimp
   apply (case_tac "cap = a",clarsimp)
   apply (clarsimp simp:masked_as_full_def is_cap_simps)
   apply (clarsimp simp: cap_master_cap_simps split:if_splits)
  apply (clarsimp split del:if_splits)
  apply (intro conjI)
    apply (clarsimp split:if_splits)
   apply (clarsimp)
  apply (rule ballI)
  apply (drule(1) bspec)
  apply clarsimp
  apply (intro conjI)
   apply (case_tac "capa = ac",clarsimp+)
  apply (case_tac "capa = ac")
   apply (clarsimp simp:masked_as_full_def is_cap_simps split:if_splits)+
  done

abbreviation (input)
  "transfer_caps_srcs caps s \<equiv>
    (\<forall>x \<in> set caps. cte_wp_at (\<lambda>cp. fst x \<noteq> cap.NullCap \<longrightarrow> cp = fst x) (snd x) s
                                           \<and> real_cte_at (snd x) s)"

lemmas transfer_caps_loop_pres =
    transfer_caps_loop_presM[where vo=False and ex=False and em=False, simplified]

lemma transfer_caps_loop_typ_at[wp]:
   "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace>
      transfer_caps_loop ep diminish buffer n caps slots mi
    \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by (wp transfer_caps_loop_pres)

lemma transfer_loop_aligned[wp]:
  "\<lbrace>pspace_aligned\<rbrace>
     transfer_caps_loop ep diminish buffer n caps slots mi
   \<lbrace>\<lambda>rv. pspace_aligned\<rbrace>"
  by (wp transfer_caps_loop_pres)

lemma transfer_loop_distinct[wp]:
  "\<lbrace>pspace_distinct\<rbrace>
     transfer_caps_loop ep diminish buffer n caps slots mi
   \<lbrace>\<lambda>rv. pspace_distinct\<rbrace>"
  by (wp transfer_caps_loop_pres)

lemma invs_valid_objs2:
  "invs s \<longrightarrow> valid_objs s"
  by clarsimp

lemma transfer_caps_loop_valid_objs[wp]:
  "\<lbrace>valid_objs and valid_mdb and (\<lambda>s. \<forall>slot \<in> set slots. real_cte_at slot s \<and> cte_wp_at (\<lambda>cap. cap = cap.NullCap) slot s)
            and transfer_caps_srcs caps and K (distinct slots)\<rbrace>
      transfer_caps_loop ep diminish buffer n caps slots mi
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
  "\<lbrace>\<lambda>s. valid_mdb s \<and> valid_objs s \<and> pspace_aligned s \<and> pspace_distinct s
       \<and> (\<forall>slot \<in> set slots. real_cte_at slot s \<and> cte_wp_at (\<lambda>cap. cap = cap.NullCap) slot s)
       \<and> transfer_caps_srcs caps s \<and> distinct slots\<rbrace>
     transfer_caps_loop ep diminish buffer n caps slots mi
   \<lbrace>\<lambda>rv. valid_mdb\<rbrace>"
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

lemma tcl_state_refs_of[wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace>
     transfer_caps_loop ep diminish buffer n caps slots mi
   \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  by (wp transfer_caps_loop_pres)

crunch if_live [wp]: set_extra_badge if_live_then_nonz_cap

lemma tcl_iflive[wp]:
  "\<lbrace>if_live_then_nonz_cap\<rbrace>
     transfer_caps_loop ep diminish buffer n caps slots mi
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  by (wp transfer_caps_loop_pres cap_insert_iflive)

crunch if_unsafe [wp]: set_extra_badge if_unsafe_then_cap

lemma tcl_ifunsafe[wp]:
  "\<lbrace>\<lambda>s. if_unsafe_then_cap s \<and> (\<forall>x\<in>set slots. ex_cte_cap_wp_to is_cnode_cap x s)\<rbrace>
     transfer_caps_loop ep diminish buffer n caps slots mi
   \<lbrace>\<lambda>rv. if_unsafe_then_cap\<rbrace>"
  by (wp transfer_caps_loop_presM[where vo=False and em=False and ex=True, simplified]
            cap_insert_ifunsafe | simp)+

lemma get_cap_global_refs[wp]:
  "\<lbrace>valid_global_refs\<rbrace> get_cap p \<lbrace>\<lambda>c s. global_refs s \<inter> cap_range c = {}\<rbrace>"
  apply (rule hoare_pre)
   apply (rule get_cap_wp)
  apply (clarsimp simp: valid_refs_def2 valid_global_refs_def cte_wp_at_caps_of_state)
  apply (blast intro: ranI)
  done

lemma cap_range_update [simp]:
  "cap_range (cap_rights_update R cap) = cap_range cap"
  by (simp add: cap_range_def cap_rights_update_def acap_rights_update_def
         split: cap.splits arch_cap.splits)

lemma derive_cap_idle[wp]:
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


crunch pred_tcb_at [wp]: set_extra_badge "\<lambda>s. pred_tcb_at proj P p s"
crunch idle [wp]: set_extra_badge "\<lambda>s. P (idle_thread s)"

lemma tcl_idle[wp]:
  "\<lbrace>valid_idle\<rbrace> transfer_caps_loop ep diminish buffer n caps slots mi \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  by (wp transfer_caps_loop_pres cap_insert_idle valid_idle_lift)

crunch cur_tcb [wp]: set_extra_badge cur_tcb

lemma tcl_ct[wp]:
  "\<lbrace>cur_tcb\<rbrace> transfer_caps_loop ep diminish buffer n caps slots mi \<lbrace>\<lambda>rv. cur_tcb\<rbrace>"
  by (wp transfer_caps_loop_pres)

crunch it[wp]: cap_insert "\<lambda>s. P (idle_thread s)"
  (wp: crunch_wps simp: crunch_simps)

lemma tcl_it[wp]:
  "\<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> transfer_caps_loop ep diminish buffer n caps slots mi
   \<lbrace>\<lambda>rv s. P (idle_thread s)\<rbrace>"
  by (wp transfer_caps_loop_pres)


lemma arch_derive_cap_objrefs_iszombie:
  "\<lbrace>\<lambda>s . P (set_option (aobj_ref cap)) False s\<rbrace>
     arch_derive_cap cap
   \<lbrace>\<lambda>rv s. P (set_option (aobj_ref rv)) False s\<rbrace>,-"
  apply(cases cap, simp_all add: is_zombie_def arch_derive_cap_def)
      apply(rule hoare_pre, wpc?, wp, simp)+
  done


lemma derive_cap_objrefs_iszombie:
  "\<lbrace>\<lambda>s. \<not> is_zombie cap \<longrightarrow> P (obj_refs cap) False s\<rbrace>
     derive_cap slot cap
   \<lbrace>\<lambda>rv s. rv \<noteq> cap.NullCap \<longrightarrow> P (obj_refs rv) (is_zombie rv) s\<rbrace>,-"
  apply (cases cap, simp_all add: derive_cap_def is_zombie_def)
          apply (rule hoare_pre,
                 (wp | simp add: o_def arch_derive_cap_objrefs_iszombie)+)+
  done


lemma obj_refs_remove_rights[simp]:
  "obj_refs (remove_rights rs cap) = obj_refs cap"
  by (simp add: remove_rights_def cap_rights_update_def
                acap_rights_update_def
         split: cap.splits arch_cap.splits)


lemma is_zombie_rights[simp]:
  "is_zombie (remove_rights rs cap) = is_zombie cap"
  by (simp add: is_zombie_def remove_rights_def cap_rights_update_def
         split: cap.splits)


crunch caps_of_state [wp]: set_extra_badge "\<lambda>s. P (caps_of_state s)"


lemma set_extra_badge_zombies_final[wp]: 
  "\<lbrace>zombies_final\<rbrace> set_extra_badge buffer b n \<lbrace>\<lambda>_. zombies_final\<rbrace>"
  apply (simp add: zombies_final_def cte_wp_at_caps_of_state is_final_cap'_def2)
  apply (wp hoare_vcg_all_lift final_cap_lift)
  done  


lemma tcl_zombies[wp]:
  "\<lbrace>zombies_final and valid_objs and valid_mdb and K (distinct slots)
          and (\<lambda>s. \<forall>slot \<in> set slots. real_cte_at slot s \<and> cte_wp_at (\<lambda>cap. cap = cap.NullCap) slot s )
          and transfer_caps_srcs caps\<rbrace>
     transfer_caps_loop ep diminish buffer n caps slots mi
   \<lbrace>\<lambda>rv. zombies_final\<rbrace>"
  apply (rule hoare_pre)
   apply (rule transfer_caps_loop_presM[where vo=True and em=False and ex=False])
     apply (wp cap_insert_zombies)
     apply clarsimp
     apply (case_tac "(a, b) = (ab, bb)")
      apply (clarsimp simp: cte_wp_at_caps_of_state is_derived_def)
      apply (simp split: split_if_asm)
      apply (clarsimp simp: is_cap_simps cap_master_cap_def
                     split: cap.split_asm)+
      apply fastforce
     apply (frule(3) zombies_finalD3)
      apply (clarsimp simp: is_derived_def is_cap_simps cap_master_cap_simps
                     vs_cap_ref_def split: split_if_asm dest!:cap_master_cap_eqDs)
      apply (drule_tac a=r in equals0D)
      apply (drule master_cap_obj_refs, simp)
     apply (clarsimp simp: cte_wp_at_caps_of_state is_derived_def
                           is_cap_simps cap_master_cap_def
                    split: split_if_asm cap.split_asm)
     apply fastforce
    apply wp
  apply (clarsimp simp:cte_wp_at_caps_of_state)
  apply (drule(1) bspec,clarsimp)
  apply (fastforce dest!:caps_of_state_valid)
  done


lemma derive_cap_valid_globals [wp]:
  "\<lbrace>valid_global_refs\<rbrace> derive_cap r cap \<lbrace>\<lambda>rv. valid_global_refs\<rbrace>"
  by (rule valid_global_refs_cte_lift) wp


crunch arch [wp]: set_extra_badge "\<lambda>s. P (arch_state s)"


crunch irq [wp]: set_extra_badge "\<lambda>s. P (interrupt_irq_node s)"


lemma transfer_caps_loop_valid_globals [wp]:
  "\<lbrace>valid_global_refs and valid_objs and valid_mdb and K (distinct slots)
       and (\<lambda>s. \<forall>slot \<in> set slots. real_cte_at slot s \<and> cte_wp_at (\<lambda>cap. cap = cap.NullCap) slot s)
       and transfer_caps_srcs caps\<rbrace>
  transfer_caps_loop ep diminish buffer n caps slots mi 
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
  "\<lbrace>\<lambda>s. P (arch_state s)\<rbrace> transfer_caps_loop ep diminish buffer n caps slots mi \<lbrace>\<lambda>rv s. P (arch_state s)\<rbrace>"
  by (rule transfer_caps_loop_pres) wp


lemma transfer_caps_loop_valid_arch[wp]:
  "\<lbrace>valid_arch_state\<rbrace> transfer_caps_loop ep diminish buffer n caps slots mi \<lbrace>\<lambda>rv. valid_arch_state\<rbrace>"
  by (rule valid_arch_state_lift) wp


lemma derive_cap_not_reply:
  "\<lbrace>\<top>\<rbrace> derive_cap slot cap \<lbrace>\<lambda>rv s. \<not> is_reply_cap rv\<rbrace>, -"
  apply (rule hoare_pre)
  apply (wpc | wp
       | clarsimp simp: derive_cap_def arch_derive_cap_def is_reply_cap_def)+
  done


lemma tcl_reply':
  "\<lbrace>valid_reply_caps and valid_reply_masters and valid_objs and valid_mdb and K(distinct slots)
         and (\<lambda>s. \<forall>x \<in> set slots. real_cte_at x s \<and> cte_wp_at (\<lambda>cap. cap = cap.NullCap) x s)
         and transfer_caps_srcs caps\<rbrace>
   transfer_caps_loop ep diminish buffer n caps slots mi
   \<lbrace>\<lambda>rv. valid_reply_caps and valid_reply_masters\<rbrace>"
  apply (rule hoare_pre)
   apply (rule transfer_caps_loop_presM[where vo=True and em=False and ex=False])
     apply wp
      apply (clarsimp simp: real_cte_at_cte)
      apply (clarsimp simp: cte_wp_at_caps_of_state is_derived_def)
     apply (clarsimp simp: real_cte_at_cte)
     apply (clarsimp simp: cte_wp_at_caps_of_state is_derived_def is_cap_simps)
     apply (frule(1) valid_reply_mastersD[OF caps_of_state_cteD])
     apply (frule(1) tcb_cap_valid_caps_of_stateD)
     apply (frule(1) caps_of_state_valid)
     apply (clarsimp simp: tcb_cap_valid_def valid_cap_def is_cap_simps)
     apply (clarsimp simp: obj_at_def is_tcb is_cap_table cap_master_cap_def)
    apply (wp valid_reply_caps_st_cte_lift valid_reply_masters_cte_lift|simp)+
    apply (clarsimp simp:cte_wp_at_caps_of_state | intro conjI ballI)+
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


lemma transfer_caps_loop_irq_node[wp]:
  "\<lbrace>\<lambda>s. P (interrupt_irq_node s)\<rbrace>
     transfer_caps_loop ep diminish buffer n caps slots mi
   \<lbrace>\<lambda>rv s. P (interrupt_irq_node s)\<rbrace>"
  by (rule transfer_caps_loop_pres) wp


lemma cap_master_cap_irqs:
  "cap_irqs cap = (case cap_master_cap cap
       of cap.IRQHandlerCap irq \<Rightarrow> {irq}
         | _ \<Rightarrow> {})"
  by (simp add: cap_master_cap_def split: cap.split)


crunch irq_state [wp]: set_extra_badge "\<lambda>s. P (interrupt_states s)"


lemma transfer_caps_loop_irq_handlers[wp]:
  "\<lbrace>valid_irq_handlers and valid_objs and valid_mdb and K (distinct slots)
         and (\<lambda>s. \<forall>x \<in> set slots. real_cte_at x s \<and> cte_wp_at (\<lambda>cap. cap = cap.NullCap) x s)
         and transfer_caps_srcs caps\<rbrace>
   transfer_caps_loop ep diminish buffer n caps slots mi
   \<lbrace>\<lambda>rv. valid_irq_handlers\<rbrace>"
  apply (rule hoare_pre)
   apply (rule transfer_caps_loop_presM[where vo=True and em=False and ex=False])
     apply wp
     apply (clarsimp simp: cte_wp_at_caps_of_state)
     apply (clarsimp simp: is_derived_def split: split_if_asm)
     apply (simp add: cap_master_cap_irqs)+
    apply (wp valid_irq_handlers_lift)
   apply (clarsimp simp:cte_wp_at_caps_of_state|intro conjI ballI)+
   apply (drule(1) bspec,clarsimp)
   apply (frule(1) caps_of_state_valid)
   apply (fastforce simp:valid_cap_def)
  apply (drule(1) bspec)
  apply clarsimp
  done


crunch valid_arch_objs [wp]: set_extra_badge valid_arch_objs


lemma transfer_caps_loop_arch_objs[wp]:
  "\<lbrace>valid_arch_objs\<rbrace>
   transfer_caps_loop ep diminish buffer n caps slots mi
   \<lbrace>\<lambda>rv. valid_arch_objs\<rbrace>"
  by (rule transfer_caps_loop_pres) wp

crunch valid_arch_caps [wp]: set_extra_badge valid_arch_caps


lemma transfer_caps_loop_valid_arch_caps[wp]:
  "\<lbrace>valid_arch_caps and valid_objs and valid_mdb and K(distinct slots)
           and (\<lambda>s. \<forall>x \<in> set slots. real_cte_at x s \<and> cte_wp_at (\<lambda>cap. cap = cap.NullCap) x s)
           and transfer_caps_srcs caps\<rbrace>
     transfer_caps_loop ep diminish buffer n caps slots mi
   \<lbrace>\<lambda>rv. valid_arch_caps\<rbrace>"
  apply (wp transfer_caps_loop_presM[where vo=True and em=False and ex=False]
            cap_insert_valid_arch_caps)
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
  "\<lbrace>valid_global_objs\<rbrace>
     transfer_caps_loop ep diminish buffer n caps slots mi
   \<lbrace>\<lambda>rv. valid_global_objs\<rbrace>"
  by (wp transfer_caps_loop_pres cap_insert_valid_global_objs)


crunch valid_kernel_mappings [wp]: set_extra_badge valid_kernel_mappings


lemma transfer_caps_loop_v_ker_map[wp]:
  "\<lbrace>valid_kernel_mappings\<rbrace>
     transfer_caps_loop ep diminish buffer n caps slots mi
   \<lbrace>\<lambda>rv. valid_kernel_mappings\<rbrace>"
  by (wp transfer_caps_loop_pres)


crunch equal_kernel_mappings [wp]: set_extra_badge equal_kernel_mappings


lemma transfer_caps_loop_eq_ker_map[wp]:
  "\<lbrace>equal_kernel_mappings\<rbrace>
     transfer_caps_loop ep diminish buffer n caps slots mi
   \<lbrace>\<lambda>rv. equal_kernel_mappings\<rbrace>"
  by (wp transfer_caps_loop_pres)


crunch valid_asid_map [wp]: set_extra_badge valid_asid_map


lemma transfer_caps_loop_asid_map[wp]:
  "\<lbrace>valid_asid_map\<rbrace>
     transfer_caps_loop ep diminish buffer n caps slots mi
   \<lbrace>\<lambda>rv. valid_asid_map\<rbrace>"
  by (wp transfer_caps_loop_pres | simp)+


crunch only_idle [wp]: set_extra_badge only_idle


lemma transfer_caps_loop_only_idle[wp]:
  "\<lbrace>only_idle\<rbrace>
     transfer_caps_loop ep diminish buffer n caps slots mi
   \<lbrace>\<lambda>rv. only_idle\<rbrace>"
  by (wp transfer_caps_loop_pres | simp)+


crunch valid_global_pd_mappings [wp]: set_extra_badge valid_global_pd_mappings


lemma transfer_caps_loop_valid_global_pd_mappings[wp]:
  "\<lbrace>valid_global_pd_mappings\<rbrace>
     transfer_caps_loop ep diminish buffer n caps slots mi
   \<lbrace>\<lambda>rv. valid_global_pd_mappings\<rbrace>"
  by (wp transfer_caps_loop_pres)


crunch pspace_in_kernel_window [wp]: set_extra_badge pspace_in_kernel_window


lemma transfer_caps_loop_pspace_in_kernel_window[wp]:
  "\<lbrace>pspace_in_kernel_window\<rbrace>
     transfer_caps_loop ep diminish buffer n caps slots mi
   \<lbrace>\<lambda>rv. pspace_in_kernel_window\<rbrace>"
  by (wp transfer_caps_loop_pres)


crunch cap_refs_in_kernel_window[wp]: set_extra_badge cap_refs_in_kernel_window

lemma transfer_caps_loop_cap_refs_in_kernel_window [wp]:
  "\<lbrace>cap_refs_in_kernel_window and valid_objs and valid_mdb and K (distinct slots)
       and (\<lambda>s. \<forall>slot \<in> set slots. real_cte_at slot s \<and> cte_wp_at (\<lambda>cap. cap = cap.NullCap) slot s )
       and transfer_caps_srcs caps\<rbrace>
  transfer_caps_loop ep diminish buffer n caps slots mi 
  \<lbrace>\<lambda>rv. cap_refs_in_kernel_window\<rbrace>"
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
  "\<lbrace>\<lambda>s. valid_ioc s\<rbrace>
    transfer_caps_loop ep diminish buffer n caps slots mi
   \<lbrace>\<lambda>_. valid_ioc\<rbrace>"
  by (wp transfer_caps_loop_pres | simp add: set_extra_badge_def)+


lemma storeWord_um_inv:
  "\<lbrace>\<lambda>s. underlying_memory s = um\<rbrace>
   storeWord a v
   \<lbrace>\<lambda>_ s. is_aligned a 2 \<and> x \<in> {a,a+1,a+2,a+3} \<or> underlying_memory s x = um x\<rbrace>"
  apply (simp add: storeWord_def is_aligned_mask)
  apply wp
  apply simp
  done


lemma store_word_offs_vms[wp]:
  "\<lbrace>valid_machine_state\<rbrace> store_word_offs ptr offs v \<lbrace>\<lambda>_. valid_machine_state\<rbrace>"
proof -
  have aligned_offset_ignore:
    "\<And>(l::word32) (p::word32) sz. l<4 \<Longrightarrow> p && mask 2 = 0 \<Longrightarrow>
       p+l && ~~ mask (pageBitsForSize sz) = p && ~~ mask (pageBitsForSize sz)"
  proof -
    fix l p sz
    assume al: "(p::word32) && mask 2 = 0"
    assume "(l::word32) < 4" hence less: "l<2^2" by simp
    have le: "2 \<le> pageBitsForSize sz" by (case_tac sz, simp_all)
    show "?thesis l p sz"
      by (rule is_aligned_add_helper[simplified is_aligned_mask,
          THEN conjunct2, THEN mask_out_first_mask_some,
          where n=2, OF al less le])
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
    apply (subgoal_tac "(ptr + of_nat offs * 4) && ~~ mask (pageBitsForSize x) =
                        p && ~~ mask (pageBitsForSize x)", simp)
    apply (simp only: is_aligned_mask[of _ 2])
    apply (elim disjE, simp_all)
    apply (rule aligned_offset_ignore[symmetric], simp+)+
    done
qed

lemma set_extra_badge_vms[wp]:
  "\<lbrace>valid_machine_state\<rbrace> set_extra_badge buffer b n \<lbrace>\<lambda>_. valid_machine_state\<rbrace>"
by (simp add: set_extra_badge_def) wp


lemma transfer_caps_loop_vms[wp]:
  "\<lbrace>\<lambda>s. valid_machine_state s\<rbrace>
    transfer_caps_loop ep diminish buffer n caps slots mi
   \<lbrace>\<lambda>_. valid_machine_state\<rbrace>"
  by (wp transfer_caps_loop_pres)

crunch valid_irq_states[wp]: set_extra_badge "valid_irq_states"
  (ignore: do_machine_op)

lemma transfer_caps_loop_valid_irq_states[wp]:
  "\<lbrace>\<lambda>s. valid_irq_states s\<rbrace>
    transfer_caps_loop ep diminish buffer n caps slots mi
   \<lbrace>\<lambda>_. valid_irq_states\<rbrace>"
  apply(wp transfer_caps_loop_pres)
  done

lemma transfer_caps_loop_invs[wp]:
  "\<lbrace>\<lambda>s. invs s
          \<and> (\<forall>x \<in> set slots. ex_cte_cap_wp_to is_cnode_cap x s) \<and> distinct slots
          \<and> (\<forall>x \<in> set slots. real_cte_at x s \<and> cte_wp_at (\<lambda>cap. cap = cap.NullCap) x s)
          \<and> transfer_caps_srcs caps s\<rbrace> 
     transfer_caps_loop ep diminish buffer n caps slots mi
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (rule hoare_pre)
   apply (wp valid_irq_node_typ | simp)+
  done


lemma zipWith_append2:
  "length ys + 1 < n \<Longrightarrow>
   zipWith f [0 ..< n] (ys @ [y]) = zipWith f [0 ..< n] ys @ [f (length ys) y]"
  apply (simp add: zipWith_def zip_append2)
  apply (subst upt_conv_Cons, erule Suc_lessD)
  apply simp
  apply (subst zip_take_triv[OF order_refl, symmetric], fastforce)
  done


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
  apply (cases buf, simp_all add: split_def unlessE_def)
   apply (wp | simp)+
  done


lemma transfer_caps_mi_label[wp]:
  "\<lbrace>\<lambda>s. P (mi_label mi)\<rbrace>
     transfer_caps mi caps ep receiver recv_buf diminish
   \<lbrace>\<lambda>mi' s. P (mi_label mi')\<rbrace>"
  apply (simp add: transfer_caps_def)
  apply (wp | wpc)+
  apply simp
  done


lemma transfer_cap_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace>
   transfer_caps mi caps ep receiver recv_buf diminish
   \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  apply (simp add: transfer_caps_def split_def split del: split_if |
         wp cap_insert_typ_at hoare_drop_imps|wpc)+
  done


lemma transfer_cap_tcb[wp]:
  "\<lbrace>tcb_at t\<rbrace>
    transfer_caps mi caps ep receiver recv_buf diminish
   \<lbrace>\<lambda>rv. tcb_at t\<rbrace>"
  by (simp add: tcb_at_typ, wp)


lemma cte_refs_mask[simp]:
  "cte_refs (mask_cap rs cap) = cte_refs cap"
  by (rule ext, cases cap, simp_all add: mask_cap_def cap_rights_update_def)


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
  apply (simp add: lookup_cap_def split_def)
  apply (rule hoare_pre, wp)
  apply simp
  done


lemma is_cnode_cap_mask[simp]:
  "is_cnode_cap (mask_cap rs cap) = is_cnode_cap cap"
  by (auto simp: mask_cap_def cap_rights_update_def
          split: cap.split)


lemma get_rs_cap_to[wp]:
  "\<lbrace>\<top>\<rbrace> get_receive_slots rcvr buf
   \<lbrace>\<lambda>rv s. \<forall>x \<in> set rv. ex_cte_cap_wp_to is_cnode_cap x s\<rbrace> "
  apply (cases buf, simp_all add: split_def whenE_def split del: split_if)
   apply (wp | simp | rule hoare_drop_imps)+
  done


lemma derive_cap_notzombie[wp]:
  "\<lbrace>\<top>\<rbrace> derive_cap slot cap \<lbrace>\<lambda>rv s. \<not> is_zombie rv\<rbrace>,-"
  apply (cases cap, simp_all add: derive_cap_def is_zombie_def)
          apply (rule hoare_pre, (wp | simp add: o_def)+)+
  done


lemma derive_cap_notIRQ[wp]:
  "\<lbrace>\<top>\<rbrace> derive_cap slot cap \<lbrace>\<lambda>rv s. rv \<noteq> cap.IRQControlCap\<rbrace>,-"
  apply (cases cap, simp_all add: derive_cap_def)
          apply (rule hoare_pre, (wp | simp add: o_def)+)+
  done


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


lemma is_zombie_update_cap_data[simp]:
  "is_zombie (update_cap_data P data cap) = is_zombie cap"
  by (simp add: update_cap_data_closedform is_zombie_def
         split: cap.splits)


lemma random_helper[simp]:
  "is_zombie (case ct_send_data ct of None \<Rightarrow> mask_cap ms cap
                 | Some w \<Rightarrow> update_cap_data P w (mask_cap ms cap))
     = is_zombie cap"
  by (simp split: option.splits)


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
  apply (rule hoare_pre)
   apply (wpc|wp|simp)+
  done


lemma get_mrs_inv[wp]:
  "\<lbrace>P\<rbrace> get_mrs t buf info \<lbrace>\<lambda>rv. P\<rbrace>"
  by (simp add: get_mrs_def load_word_offs_def
          | wp dmo_inv loadWord_inv mapM_wp' | wpc)+



lemma copy_mrs_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> copy_mrs s sb r rb n \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  apply (simp add: copy_mrs_def load_word_offs_def
                   store_word_offs_def set_object_def
              cong: option.case_cong
              split del: split_if)
  apply (wp hoare_vcg_split_case_option mapM_wp')
   apply (wp hoare_drop_imps mapM_wp')
   apply simp_all
  done


lemmas copy_mrs_typ_ats[wp] = abs_typ_at_lifts[OF copy_mrs_typ_at]


lemma copy_mrs_tcb[wp]:
  "\<lbrace> tcb_at t \<rbrace> copy_mrs s sb r rb n \<lbrace>\<lambda>rv. tcb_at t \<rbrace>"
  by (simp add: tcb_at_typ, wp)

lemma copy_mrs_aep_at[wp]:
  "\<lbrace> aep_at p \<rbrace> copy_mrs s sb r rb n \<lbrace>\<lambda>rv. aep_at p \<rbrace>"
  by (simp add: aep_at_typ, wp)


lemmas copy_mrs_redux =
   copy_mrs_def bind_assoc[symmetric]
   thread_set_def[simplified, symmetric]

lemma store_word_offs_invs[wp]:
  "\<lbrace>invs\<rbrace> store_word_offs p x w \<lbrace>\<lambda>_. invs\<rbrace>"
  by (wp | simp add: store_word_offs_def)+

lemma copy_mrs_invs[wp]:
  "\<lbrace> invs and tcb_at r and tcb_at s \<rbrace> copy_mrs s sb r rb n \<lbrace>\<lambda>rv. invs \<rbrace>"
  apply (simp add: copy_mrs_redux)
  apply wp
   apply (rule_tac P="invs" in hoare_triv)
   apply (case_tac sb, simp)
   apply (case_tac rb, simp)
   apply (simp split del: split_if)
   apply (rule mapM_wp [where S=UNIV, simplified])
   apply wp
  apply (rule hoare_strengthen_post)
   apply (rule mapM_wp [where S=UNIV, simplified])
   apply wp
   apply simp+
  done

lemma set_mrs_valid_objs [wp]:
  "\<lbrace>valid_objs\<rbrace> set_mrs t a msgs \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  apply (cases a)
   apply (simp add: set_mrs_redux)
   apply (wp thread_set_valid_objs_triv)
       apply (auto simp: tcb_cap_cases_def)[1]
      apply simp+
  apply (simp add: set_mrs_redux zipWithM_x_mapM split_def
                   store_word_offs_def
            split del: split_if)
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
                split del: split_if)
  apply (wp mapM_wp' | wpc)+
  apply (wp thread_set_caps_of_state_trivial2 | simp)+
  done


lemma set_mrs_mdb [wp]:
  "\<lbrace>valid_mdb\<rbrace> set_mrs t b m \<lbrace>\<lambda>_. valid_mdb\<rbrace>"
  by (rule valid_mdb_lift, wp)


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


lemma valid_msg_length_strengthen:
  "valid_message_info mi \<longrightarrow> unat (mi_length mi) \<le> msg_max_length"
  apply (clarsimp simp: valid_message_info_def)
  apply (subgoal_tac "unat (mi_length mi) \<le> unat (of_nat msg_max_length :: word32)")
   apply (clarsimp simp: unat_of_nat msg_max_length_def)
  apply (clarsimp simp: un_ui_le word_le_def)
  done


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
             | wp_once hoare_drop_imps
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


lemma copy_mrs_in_user_frame[wp]:
  "\<lbrace>in_user_frame p\<rbrace> copy_mrs t buf t' buf' n \<lbrace>\<lambda>rv. in_user_frame p\<rbrace>"
  by (simp add: in_user_frame_def) (wp hoare_vcg_ex_lift)


crunch typ_at[wp]: do_normal_transfer "\<lambda>s. P (typ_at T p s)"

lemma do_normal_tcb[wp]:
  "\<lbrace>tcb_at t\<rbrace>
     do_normal_transfer sender send_buf ep badge
             can_grant receiver recv_buf diminish
   \<lbrace>\<lambda>rv. tcb_at t\<rbrace>"
  by (simp add: tcb_at_typ, wp)


lemma make_fault_message_inv[wp]:
  "\<lbrace>P\<rbrace> make_fault_msg ft t \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (cases ft, simp_all split del: split_if)
     apply (wp as_user_inv getRestartPC_inv mapM_wp'
              | simp add: getRegister_def)+
  done

lemma do_fault_transfer_invs[wp]:
  "\<lbrace>invs and tcb_at receiver\<rbrace>
      do_fault_transfer badge sender receiver recv_buf
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (simp add: do_fault_transfer_def split_def | wp
    | clarsimp split: option.split)+

lemma valid_recv_ep_tcb:
  "\<lbrakk> valid_ep (Structures_A.endpoint.RecvEP (a # lista)) s \<rbrakk> \<Longrightarrow> tcb_at a s"
  by (simp add: valid_ep_def tcb_at_def)


lemma lookup_ipc_buffer_in_user_frame[wp]:
  "\<lbrace>valid_objs and tcb_at t\<rbrace> lookup_ipc_buffer b t
   \<lbrace>case_option (\<lambda>_. True) in_user_frame\<rbrace>"
  apply (simp add: lookup_ipc_buffer_def)
  apply (wp get_cap_wp thread_get_wp | wpc | simp)+
  apply (clarsimp simp add: obj_at_def is_tcb)
  apply (subgoal_tac "in_user_frame (xa + (tcb_ipc_buffer tcb &&
                                           mask (pageBitsForSize xc))) s", simp)
  apply (drule (1) cte_wp_valid_cap)
  apply (clarsimp simp add: valid_cap_def cap_aligned_def in_user_frame_def)
  apply (thin_tac "case_option a b c" for a b c)
  apply (rule_tac x=xc in exI)
  apply (subgoal_tac "(xa + (tcb_ipc_buffer tcb && mask (pageBitsForSize xc)) &&
            ~~ mask (pageBitsForSize xc)) = xa", simp)
  apply (rule is_aligned_add_helper[THEN conjunct2], assumption)
  apply (rule and_mask_less')
  apply (case_tac xc, simp_all)
  done


crunch aligned[wp]: do_ipc_transfer "pspace_aligned"
  (wp: crunch_wps simp: crunch_simps zipWithM_x_mapM)


crunch "distinct"[wp]: do_ipc_transfer "pspace_distinct"
  (wp: crunch_wps simp: crunch_simps zipWithM_x_mapM)


lemma get_receive_slots_real_ctes[wp]:
  "\<lbrace>valid_objs\<rbrace> get_receive_slots  rcvr buf \<lbrace>\<lambda>rv s. \<forall>x \<in> set rv. real_cte_at x s\<rbrace>"
  apply (cases buf, simp_all add: split_def whenE_def split del: split_if)
   apply (wp lookup_cap_valid | simp | rule hoare_drop_imps)+
  done


crunch vmdb[wp]: set_message_info "valid_mdb"


crunch vmdb[wp]: do_ipc_transfer "valid_mdb"
  (ignore: as_user simp: crunch_simps ball_conj_distrib
       wp: crunch_wps hoare_vcg_const_Ball_lift transfer_caps_loop_valid_mdb)




lemma copy_mrs_thread_set_dmo:
  assumes ts: "\<And>c. \<lbrace>Q\<rbrace> thread_set (\<lambda>tcb. tcb\<lparr>tcb_context := c tcb\<rparr>) r \<lbrace>\<lambda>rv. Q\<rbrace>"
  assumes dmo: "\<And>x y. \<lbrace>Q\<rbrace> do_machine_op (storeWord x y) \<lbrace>\<lambda>rv. Q\<rbrace>"
               "\<And>x y. \<lbrace>Q\<rbrace> do_machine_op (loadWord x) \<lbrace>\<lambda>rv. Q\<rbrace>"
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


crunch ifunsafe[wp]: do_ipc_transfer "if_unsafe_then_cap"
  (wp: crunch_wps hoare_vcg_const_Ball_lift simp: zipWithM_x_mapM ignore: transfer_caps_loop)

crunch iflive[wp]: do_ipc_transfer "if_live_then_nonz_cap"
  (wp: crunch_wps simp: zipWithM_x_mapM ignore: transfer_caps_loop)

crunch state_refs_of[wp]: do_ipc_transfer "\<lambda>s. P (state_refs_of s)"
  (wp: crunch_wps simp: zipWithM_x_mapM ignore: transfer_caps_loop)

crunch ct[wp]: do_ipc_transfer "cur_tcb"
  (wp: crunch_wps simp: zipWithM_x_mapM ignore: transfer_caps_loop)


crunch zombies[wp]: do_ipc_transfer "zombies_final"
  (wp: crunch_wps hoare_vcg_const_Ball_lift tcl_zombies simp: crunch_simps ball_conj_distrib )

crunch it[wp]: do_ipc_transfer "\<lambda>s. P (idle_thread s)"
  (wp: crunch_wps simp: crunch_simps zipWithM_x_mapM)


crunch valid_globals[wp]: do_ipc_transfer "valid_global_refs"
  (wp: crunch_wps hoare_vcg_const_Ball_lift simp: crunch_simps zipWithM_x_mapM ball_conj_distrib)


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


crunch reply_masters[wp]: copy_mrs valid_reply_masters
  (wp: crunch_wps)


crunch reply[wp]: do_ipc_transfer "valid_reply_caps"
  (wp: crunch_wps hoare_vcg_const_Ball_lift tcl_reply simp: zipWithM_x_mapM ball_conj_distrib
       ignore: const_on_failure)


crunch reply_masters[wp]: do_ipc_transfer "valid_reply_masters"
  (wp: crunch_wps hoare_vcg_const_Ball_lift tcl_reply_masters
      simp: zipWithM_x_mapM ball_conj_distrib )


crunch valid_idle[wp]: do_ipc_transfer "valid_idle"
  (wp: crunch_wps simp: zipWithM_x_mapM ignore: transfer_caps_loop)


crunch arch[wp]: do_ipc_transfer "\<lambda>s. P (arch_state s)"
  (wp: crunch_wps simp: zipWithM_x_mapM ignore: transfer_caps_loop)


crunch typ_at[wp]: do_ipc_transfer "\<lambda>s. P (typ_at T p s)"
  (wp: crunch_wps simp: zipWithM_x_mapM ignore: transfer_caps_loop)


lemma do_ipc_transfer_valid_arch[wp]:
  "\<lbrace>valid_arch_state\<rbrace> do_ipc_transfer s ep bg grt r dim \<lbrace>\<lambda>rv. valid_arch_state\<rbrace>"
  by (rule valid_arch_state_lift) wp


crunch irq_node[wp]: do_ipc_transfer "\<lambda>s. P (interrupt_irq_node s)"
  (wp: crunch_wps simp: zipWithM_x_mapM crunch_simps)


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
  apply wp
  done


crunch irq_handlers[wp]: do_ipc_transfer "valid_irq_handlers"
  (wp: crunch_wps hoare_vcg_const_Ball_lift simp: zipWithM_x_mapM crunch_simps ball_conj_distrib )


declare store_word_offs_arch_objs [wp]


declare set_mrs_arch_objs [wp]


declare as_user_arch_obj [wp]


crunch arch_objs[wp]: do_ipc_transfer "valid_arch_objs"
  (wp: crunch_wps simp: zipWithM_x_mapM crunch_simps)


lemmas set_mrs_valid_global_objs[wp]
    = set_mrs_thread_set_dmo [OF thread_set_valid_globals do_machine_op_valid_global_objs]


lemma as_user_valid_global_objs [wp]:
  "\<lbrace>valid_global_objs\<rbrace> as_user t m \<lbrace>\<lambda>_. valid_global_objs\<rbrace>"
  by (wp as_user_wp_thread_set_helper, simp)


crunch valid_global_objs[wp]: do_ipc_transfer "valid_global_objs"
  (wp: crunch_wps simp: zipWithM_x_mapM)


lemma as_user_valid_arch_caps [wp]:
  "\<lbrace>valid_arch_caps\<rbrace> as_user t m \<lbrace>\<lambda>_. valid_arch_caps\<rbrace>"
  apply (wp as_user_wp_thread_set_helper thread_set_arch_caps_trivial
            | rule ball_tcb_cap_casesI | simp)+
  done


lemmas set_mrs_valid_arch_caps[wp]
    = set_mrs_thread_set_dmo [OF thread_set_arch_caps_trivial
                                 do_machine_op_valid_arch_caps,
                                 OF ball_tcb_cap_casesI, simplified]


crunch arch_caps[wp]: do_ipc_transfer "valid_arch_caps"
  (wp: crunch_wps hoare_vcg_const_Ball_lift transfer_caps_loop_valid_arch_caps
   simp: zipWithM_x_mapM crunch_simps ball_conj_distrib )


crunch v_ker_map[wp]: do_ipc_transfer "valid_kernel_mappings"
  (wp: crunch_wps simp: zipWithM_x_mapM crunch_simps)

crunch eq_ker_map[wp]: do_ipc_transfer "equal_kernel_mappings"
  (wp: crunch_wps set_object_equal_mappings
       simp: zipWithM_x_mapM crunch_simps
     ignore: set_object)

declare as_user_asid_map [wp]

crunch asid_map [wp]: do_ipc_transfer valid_asid_map
  (wp: crunch_wps simp: crunch_simps vs_refs_def)

declare as_user_only_idle [wp]

crunch only_idle [wp]: store_word_offs only_idle

lemma set_mrs_only_idle [wp]:
  "\<lbrace>only_idle\<rbrace> set_mrs t b m \<lbrace>\<lambda>_. only_idle\<rbrace>"
  apply (simp add: set_mrs_def split_def zipWithM_x_mapM
                   set_object_def
              cong: option.case_cong
               del: upt.simps)
  apply (wp mapM_wp'|wpc)+
  apply (clarsimp simp del: fun_upd_apply)
   apply (erule only_idle_tcb_update)
    apply (drule get_tcb_SomeD)
    apply (fastforce simp: obj_at_def)
   apply simp
  done

crunch only_idle [wp]: do_ipc_transfer only_idle
  (wp: crunch_wps simp: crunch_simps)

lemma as_user_global_pd_mappings [wp]:
  "\<lbrace>valid_global_pd_mappings\<rbrace> as_user t m \<lbrace>\<lambda>_. valid_global_pd_mappings\<rbrace>"
  by (wp as_user_wp_thread_set_helper, simp)

lemmas set_mrs_global_pd_mappings[wp]
    = set_mrs_thread_set_dmo[OF thread_set_global_pd_mappings do_machine_op_global_pd_mappings]

crunch global_pd_mappings [wp]: do_ipc_transfer "valid_global_pd_mappings"
  (wp: crunch_wps simp: crunch_simps)

lemma as_user_pspace_in_kernel_window[wp]:
  "\<lbrace>pspace_in_kernel_window\<rbrace> as_user t m \<lbrace>\<lambda>rv. pspace_in_kernel_window\<rbrace>"
  by (wp as_user_wp_thread_set_helper | simp)+

lemmas set_mrs_pspace_in_kernel_window[wp]
    = set_mrs_thread_set_dmo[OF thread_set_pspace_in_kernel_window
                                do_machine_op_pspace_in_kernel_window]

crunch pspace_in_kernel_window[wp]: do_ipc_transfer "pspace_in_kernel_window"
  (wp: crunch_wps simp: crunch_simps)

lemma as_user_cap_refs_in_kernel_window[wp]:
  "\<lbrace>cap_refs_in_kernel_window\<rbrace> as_user t m \<lbrace>\<lambda>rv. cap_refs_in_kernel_window\<rbrace>"
  by (wp as_user_wp_thread_set_helper ball_tcb_cap_casesI
            thread_set_cap_refs_in_kernel_window
            | simp)+

lemmas set_mrs_cap_refs_in_kernel_window[wp]
    = set_mrs_thread_set_dmo[OF thread_set_cap_refs_in_kernel_window
                                do_machine_op_cap_refs_in_kernel_window]

crunch cap_refs_in_kernel_window[wp]: do_ipc_transfer "cap_refs_in_kernel_window"
  (wp: crunch_wps hoare_vcg_const_Ball_lift ball_tcb_cap_casesI
     simp: zipWithM_x_mapM crunch_simps ball_conj_distrib )

crunch valid_objs[wp]: do_ipc_transfer "valid_objs"
  (wp: hoare_vcg_const_Ball_lift simp:ball_conj_distrib )

lemma as_user_valid_ioc[wp]:
  "\<lbrace>valid_ioc\<rbrace> as_user r f \<lbrace>\<lambda>_. valid_ioc\<rbrace>"
  apply (simp add: as_user_def split_def)
  apply (wp set_object_valid_ioc_caps)
  apply (clarsimp simp: valid_ioc_def obj_at_def get_tcb_def
                  split: option.splits Structures_A.kernel_object.splits)
  apply (drule spec, drule spec, erule impE, assumption)
  apply (clarsimp simp: cap_of_def tcb_cnode_map_tcb_cap_cases
                        cte_wp_at_cases null_filter_def)
  apply (simp add: tcb_cap_cases_def split: split_if_asm)
  done

lemma set_mrs_valid_ioc[wp]:
  "\<lbrace>valid_ioc\<rbrace> set_mrs thread buf msgs \<lbrace>\<lambda>_. valid_ioc\<rbrace>"
  apply (simp add: set_mrs_def)
  apply (wp | wpc)+
  apply (simp only: zipWithM_x_mapM_x split_def)
  apply (wp mapM_x_wp[where S="UNIV", simplified] set_object_valid_ioc_caps static_imp_wp)
   apply (rule hoare_strengthen_post, wp set_object_valid_ioc_caps, simp)
  apply wp
  apply (clarsimp simp: obj_at_def get_tcb_def valid_ioc_def
                  split: option.splits Structures_A.kernel_object.splits)
  apply (intro conjI impI allI)
   apply (drule spec, drule spec, erule impE, assumption)
   apply (clarsimp simp: cap_of_def tcb_cnode_map_tcb_cap_cases
                         cte_wp_at_cases null_filter_def)
   apply (simp add: tcb_cap_cases_def split: split_if_asm)
  apply (drule spec, drule spec, erule impE, assumption)
  apply (clarsimp simp: cap_of_def tcb_cnode_map_tcb_cap_cases
                        cte_wp_at_cases null_filter_def)
  apply (simp add: tcb_cap_cases_def split: split_if_asm)
  done

crunch valid_ioc[wp]: do_ipc_transfer "valid_ioc" (wp: mapM_UNIV_wp)

lemma as_user_machine_state[wp]:
  "\<lbrace>\<lambda>s. P(machine_state s)\<rbrace> as_user r f \<lbrace>\<lambda>_. \<lambda>s. P(machine_state s)\<rbrace>"
  by (wp | simp add: as_user_def split_def)+

lemma as_user_vms[wp]:
  "\<lbrace>\<lambda>s. valid_machine_state s\<rbrace> as_user r f \<lbrace>\<lambda>_ s. valid_machine_state s\<rbrace>"
  by (simp add: valid_machine_state_def)
     (wp hoare_vcg_all_lift hoare_vcg_disj_lift)

lemma set_mrs_def2:
  "set_mrs thread buf msgs \<equiv>
   do thread_set
        (\<lambda>tcb. tcb\<lparr>tcb_context := 
                     \<lambda>reg. if reg \<in> set (take (length msgs) msg_registers)
                           then msgs ! the_index msg_registers reg
                           else tcb_context tcb reg\<rparr>)
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

lemma set_mrs_vms[wp]:
  "\<lbrace>valid_machine_state\<rbrace> set_mrs thread buf msgs \<lbrace>\<lambda>_. valid_machine_state\<rbrace>"
  apply (simp add: set_mrs_def2)
  apply (wp | wpc)+
   apply (simp only: zipWithM_x_mapM_x split_def)
   apply (wp mapM_x_wp_inv hoare_vcg_all_lift hoare_drop_imps)
   apply simp_all
  done

crunch vms[wp]: do_ipc_transfer valid_machine_state (wp: mapM_UNIV_wp)

lemma do_ipc_transfer_invs[wp]:
  "\<lbrace>invs and tcb_at r and tcb_at s\<rbrace>
   do_ipc_transfer s ep bg grt r dim
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: do_ipc_transfer_def)
  apply (wp|wpc)+
      apply (simp add: do_normal_transfer_def transfer_caps_def bind_assoc)
      apply (wp|wpc)+
         apply (rule hoare_vcg_all_lift)
         apply (rule hoare_drop_imps)
         apply wp
         apply (subst ball_conj_distrib)
         apply (wp get_rs_cte_at2 thread_get_wp static_imp_wp
                   hoare_vcg_ball_lift hoare_vcg_all_lift hoare_vcg_conj_lift)
  apply (rule hoare_strengthen_post[of P _ "\<lambda>_. P" for P])
   apply (wp lookup_ipc_buffer_inv)
  apply (clarsimp simp: obj_at_def is_tcb invs_valid_objs)
  done

lemma dit_tcb_at [wp]:
  "\<lbrace>tcb_at t\<rbrace> do_ipc_transfer s ep bg grt r dim \<lbrace>\<lambda>rv. tcb_at t\<rbrace>"
  by (simp add: tcb_at_typ) wp


lemma dit_cte_at [wp]:
  "\<lbrace>cte_at t\<rbrace> do_ipc_transfer s ep bg grt r dim \<lbrace>\<lambda>rv. cte_at t\<rbrace>"
  by (wp valid_cte_at_typ)


lemma handle_fault_reply_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> handle_fault_reply ft t label msg \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by(cases ft, simp_all, wp)


lemma handle_fault_reply_tcb[wp]:
  "\<lbrace>tcb_at t'\<rbrace> handle_fault_reply ft t label msg \<lbrace>\<lambda>rv. tcb_at t'\<rbrace>"
  by (simp add: tcb_at_typ, wp)


lemma handle_fault_reply_cte[wp]:
  "\<lbrace>cte_at t'\<rbrace> handle_fault_reply ft t label msg \<lbrace>\<lambda>rv. cte_at t'\<rbrace>"
  by (wp valid_cte_at_typ)


lemma valid_reply_caps_awaiting_reply:
  "\<lbrakk>valid_reply_caps s; kheap s t = Some (TCB tcb);
    has_reply_cap t s; tcb_state tcb = st\<rbrakk> \<Longrightarrow>
   awaiting_reply st"
  apply (simp add: valid_reply_caps_def pred_tcb_at_def)
  apply (fastforce simp: obj_at_def)
  done


lemmas cap_insert_typ_ats [wp] = abs_typ_at_lifts [OF cap_insert_typ_at]

lemma transfer_caps_loop_cte_wp_at:
  assumes imp: "\<And>cap. P cap \<Longrightarrow> \<not> is_untyped_cap cap"
  shows "\<lbrace>cte_wp_at P sl and K (sl \<notin> set slots) and (\<lambda>s. \<forall>x \<in> set slots. cte_at x s)\<rbrace>
   transfer_caps_loop ep diminish buffer n caps slots mi
   \<lbrace>\<lambda>rv. cte_wp_at P sl\<rbrace>"
  apply (induct caps arbitrary: slots n mi)
   apply (simp, wp, simp)
  apply (clarsimp simp: Let_def split_def whenE_def
                  cong: if_cong list.case_cong
             split del: split_if)
  apply (rule hoare_pre)
   apply (wp hoare_vcg_const_imp_lift hoare_vcg_const_Ball_lift 
              derive_cap_is_derived_foo
             hoare_drop_imps
        | assumption | simp split del: split_if)+
      apply (wp hoare_vcg_conj_lift cap_insert_weak_cte_wp_at2)
       apply (erule imp)
      apply (wp hoare_vcg_ball_lift            
             | clarsimp simp: is_cap_simps split del:split_if
             | unfold derive_cap_def arch_derive_cap_def
             | wpc 
             | rule conjI
             | case_tac slots)+
  done


lemma transfer_caps_tcb_caps:
  assumes imp: "\<And>c. P c \<Longrightarrow> \<not> is_untyped_cap c"
  shows  "\<lbrace>valid_objs and cte_wp_at P (t, ref) and tcb_at t\<rbrace>
     transfer_caps mi caps ep receiver recv_buf diminish
   \<lbrace>\<lambda>rv. cte_wp_at P (t, ref)\<rbrace>"
  apply (simp add: transfer_caps_def)
  apply (wp hoare_vcg_const_Ball_lift hoare_vcg_const_imp_lift 
            transfer_caps_loop_cte_wp_at 
         | wpc | simp)+
  apply (erule imp)
  apply (wp hoare_vcg_conj_lift hoare_vcg_const_imp_lift hoare_vcg_all_lift
            )
    apply (rule_tac Q = "\<lambda>rv s.  ( \<forall>x\<in>set rv. real_cte_at x s )
      \<and> cte_wp_at P (t, ref) s \<and> tcb_at t s"
       in hoare_strengthen_post)
     apply (wp get_rs_real_cte_at)
     apply clarsimp
     apply (drule(1) bspec)
     apply (clarsimp simp:obj_at_def is_tcb is_cap_table)
    apply (rule hoare_post_imp)
     apply (rule_tac Q="\<lambda>x. real_cte_at x s" in ballEI, assumption)
     apply (erule real_cte_at_cte)
    apply (rule get_receive_slots_real_ctes)
   apply clarsimp
 done


crunch cte_wp_at[wp]: do_fault_transfer "cte_wp_at P p"



lemma transfer_caps_non_null_cte_wp_at:
  assumes imp: "\<And>c. P c \<Longrightarrow> \<not> is_untyped_cap c"
  shows  "\<lbrace>valid_objs and cte_wp_at (P and (op \<noteq> cap.NullCap)) ptr\<rbrace>
     transfer_caps mi caps ep receiver recv_buf diminish
   \<lbrace>\<lambda>_. cte_wp_at (P and (op \<noteq> cap.NullCap)) ptr\<rbrace>"
  unfolding transfer_caps_def
  apply simp
  apply (rule hoare_pre)
   apply (wp hoare_vcg_ball_lift transfer_caps_loop_cte_wp_at static_imp_wp 
     | wpc | clarsimp simp:imp)+
   apply (rule hoare_strengthen_post
            [where Q="\<lambda>rv s'. (cte_wp_at (op \<noteq> cap.NullCap) ptr) s'
	                   \<and> (\<forall>x\<in>set rv. cte_wp_at (op = cap.NullCap) x s')",
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


lemma do_normal_transfer_non_null_cte_wp_at:
  assumes imp: "\<And>c. P c \<Longrightarrow> \<not> is_untyped_cap c"
  shows  "\<lbrace>valid_objs and cte_wp_at (P and (op \<noteq> cap.NullCap)) ptr\<rbrace>
   do_normal_transfer st send_buffer ep b gr rt recv_buffer dim
   \<lbrace>\<lambda>_. cte_wp_at (P and (op \<noteq> cap.NullCap)) ptr\<rbrace>"
  unfolding do_normal_transfer_def
  apply simp
  apply (wp transfer_caps_non_null_cte_wp_at
    | clarsimp simp:imp)+
  done


lemma do_ipc_transfer_non_null_cte_wp_at:
  assumes imp: "\<And>c. P c \<Longrightarrow> \<not> is_untyped_cap c"
  shows
  "\<lbrace>valid_objs and cte_wp_at (P and (op \<noteq> cap.NullCap)) ptr\<rbrace>
   do_ipc_transfer st ep b gr rt dim
   \<lbrace>\<lambda>_. cte_wp_at (P and (op \<noteq> cap.NullCap)) ptr\<rbrace>"
  unfolding do_ipc_transfer_def
  apply (wp do_normal_transfer_non_null_cte_wp_at hoare_drop_imp hoare_allI
    | wpc | simp add:imp)+
  done


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


lemma cap_delete_one_aep_at [wp]:
  "\<lbrace>\<lambda>s. P (aep_at word s)\<rbrace> cap_delete_one slot \<lbrace>\<lambda>_ s'. P (aep_at word s')\<rbrace>"
  by (simp add: aep_at_typ, wp)


lemma cap_delete_one_valid_tcb_state:
  "\<lbrace>\<lambda>s. P (valid_tcb_state st s)\<rbrace> cap_delete_one slot \<lbrace>\<lambda>_ s'. P (valid_tcb_state st s')\<rbrace>"
  apply (simp add: valid_tcb_state_def)
  apply (cases st, (wp | simp)+)
  done


lemma cte_wp_at_reply_cap_can_fast_finalise:
  "cte_wp_at (op = (cap.ReplyCap tcb v)) slot s \<longrightarrow> cte_wp_at can_fast_finalise slot s"
  by (clarsimp simp: cte_wp_at_caps_of_state can_fast_finalise_def)


lemma is_derived_ReplyCap [simp]:
  "\<And>m p. is_derived m p (cap.ReplyCap t False) = (\<lambda>c. is_master_reply_cap c \<and> obj_ref_of c = t)"
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
   do_normal_transfer st sb ep badge grant rt rb dim
   \<lbrace>\<lambda>rv. cte_wp_at P (t, ref)\<rbrace>"
  apply (simp add: do_normal_transfer_def)
  apply (rule hoare_pre)
   apply (wp hoare_drop_imps transfer_caps_tcb_caps
     | simp add:imp)+
  done


lemma do_ipc_transfer_tcb_caps:
  assumes imp: "\<And>c. P c \<Longrightarrow> \<not> is_untyped_cap c"
  shows
  "\<lbrace>valid_objs and cte_wp_at P (t, ref) and tcb_at t\<rbrace>
   do_ipc_transfer st ep b gr rt dim
   \<lbrace>\<lambda>rv. cte_wp_at P (t, ref)\<rbrace>"
  apply (simp add: do_ipc_transfer_def)
  apply (rule hoare_pre)
  apply (wp do_normal_transfer_tcb_caps hoare_drop_imps
       | wpc | simp add:imp)+
  done

lemma set_mrs_pred_tcb [wp]:
  "\<lbrace>pred_tcb_at proj P t\<rbrace> set_mrs r t' mrs \<lbrace>\<lambda>rv. pred_tcb_at proj P t\<rbrace>"
  apply (rule set_mrs_thread_set_dmo)
   apply (rule thread_set_no_change_tcb_pred)
   apply (wp | simp add: tcb_to_itcb_def)+
  done

crunch pred_tcb[wp]: do_ipc_transfer "pred_tcb_at proj P t"
  (wp: crunch_wps transfer_caps_loop_pres simp: zipWithM_x_mapM)


crunch tcb_at[wp]: setup_caller_cap "tcb_at t"


definition
  "queue_of ep \<equiv> case ep of
     Structures_A.IdleEP \<Rightarrow> []
   | Structures_A.SendEP q \<Rightarrow> q
   | Structures_A.RecvEP q \<Rightarrow> q"


primrec
  threads_of_aep :: "aep \<Rightarrow> obj_ref list"
where
  "threads_of_aep (aep.WaitingAEP ts) = ts"
| "threads_of_aep (aep.IdleAEP)       = []"
| "threads_of_aep (aep.ActiveAEP x) = []"


primrec
  threads_of :: "Structures_A.kernel_object \<Rightarrow> obj_ref list"
where
  "threads_of (AsyncEndpoint x) = threads_of_aep (aep_obj x)"
| "threads_of (TCB x)           = []"
| "threads_of (Endpoint x)      = queue_of x"


crunch ex_cap[wp]: set_message_info "ex_nonz_cap_to p"


lemma tcb_bound_refs_eq_restr:
  "tcb_bound_refs mptr = {x. x \<in> id tcb_bound_refs mptr \<and> snd x = TCBBound}"
  by (auto dest: refs_in_tcb_bound_refs)


lemma update_waiting_invs:
  notes split_if[split del]
  shows
  "\<lbrace>ko_at (AsyncEndpoint aep) aepptr and invs
     and K (aep_obj aep = aep.WaitingAEP q \<and> aep_bound_tcb aep = bound_tcb)\<rbrace>
     update_waiting_aep aepptr q bound_tcb bdg
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: update_waiting_aep_def)
  apply (rule hoare_seq_ext[OF _ assert_sp])
  apply (rule hoare_pre)
   apply (wp |simp)+
    apply (simp add: invs_def valid_state_def valid_pspace_def)
    apply (wp valid_irq_node_typ sts_only_idle)
   apply (simp add: valid_tcb_state_def conj_comms)
   apply (simp add: cte_wp_at_caps_of_state)

   apply (wp set_aep_valid_objs hoare_post_imp [OF disjI1]
             valid_irq_node_typ | assumption |
             strengthen reply_cap_doesnt_exist_strg)+
  apply (clarsimp simp: invs_def valid_state_def valid_pspace_def
                        ep_redux_simps neq_Nil_conv
                  cong: list.case_cong if_cong)
  apply (frule(1) sym_refs_obj_atD, clarsimp simp: st_tcb_at_refs_of_rev)
  apply (frule (1) if_live_then_nonz_capD)
   apply clarsimp
  apply (frule(1) st_tcb_ex_cap)
   apply simp
  apply (simp add: st_tcb_at_tcb_at)
  apply (frule ko_at_state_refs_ofD)
  apply (frule st_tcb_at_state_refs_ofD)
  apply (erule(1) obj_at_valid_objsE)
  apply (clarsimp simp: valid_obj_def valid_aep_def obj_at_def is_aep_def
             split del: split_if)
  apply (rule conjI, clarsimp simp: obj_at_def split: option.splits list.splits)
  apply (rule conjI, clarsimp elim!: pred_tcb_weakenE) 
  apply (rule conjI, clarsimp dest!: idle_no_ex_cap)
  apply (rule conjI, erule delta_sym_refs)
    apply (clarsimp dest!: refs_in_aep_bound_refs
                    split: split_if_asm split_if)
   apply (simp only: tcb_bound_refs_eq_restr, simp)
   apply (fastforce dest!: refs_in_aep_bound_refs symreftype_inverse'
                  elim!: valid_objsE simp: valid_obj_def valid_aep_def obj_at_def is_tcb
                 split: split_if_asm split_if)
  apply (clarsimp elim!: pred_tcb_weakenE)
  done


lemma ipc_cancel_ex_nonz_tcb_cap:
  "\<lbrace>\<lambda>s. \<exists>ptr. cte_wp_at (op = (cap.ThreadCap p)) ptr s\<rbrace>
     ipc_cancel t
   \<lbrace>\<lambda>rv. ex_nonz_cap_to p\<rbrace>"
  apply (simp add: ex_nonz_cap_to_def cte_wp_at_caps_of_state
              del: split_paired_Ex)
  apply (wp ipc_cancel_caps_of_state)
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


lemma ipc_cancel_ex_nonz_cap_to_tcb:
  "\<lbrace>\<lambda>s. ex_nonz_cap_to p s \<and> valid_objs s \<and> tcb_at p s\<rbrace>
     ipc_cancel t
   \<lbrace>\<lambda>rv. ex_nonz_cap_to p\<rbrace>"
  apply (wp ipc_cancel_ex_nonz_tcb_cap)
  apply (clarsimp simp: ex_nonz_cap_to_def)
  apply (drule cte_wp_at_norm, clarsimp)
  apply (frule(1) cte_wp_at_valid_objs_valid_cap, clarsimp)
  apply (drule valid_cap_tcb_at_tcb_or_zomb[where t=p])
    apply (simp add: zobj_refs_to_obj_refs)
   apply assumption
  apply (fastforce simp: is_cap_simps)
  done


lemma ipc_cancel_simple2:
  "\<lbrace>K (\<forall>st. simple st \<longrightarrow> P st)\<rbrace>
     ipc_cancel t
   \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  apply (rule hoare_assume_pre)
  apply (rule hoare_chain, rule ipc_cancel_simple, simp_all)
  apply (clarsimp simp: st_tcb_def2)
  apply fastforce
  done


lemma ipc_cancel_cte_wp_at_not_reply_state:
  "\<lbrace>st_tcb_at (op \<noteq> BlockedOnReply) t and cte_wp_at P p\<rbrace>
    ipc_cancel t 
   \<lbrace>\<lambda>r. cte_wp_at P p\<rbrace>"
  apply (simp add: ipc_cancel_def)
  apply (rule hoare_pre)
   apply (wp hoare_pre_cont[where a="reply_ipc_cancel t"] gts_wp | wpc)+
  apply (clarsimp simp: st_tcb_at_def obj_at_def)
  done


crunch idle[wp]: ipc_cancel "\<lambda>s. P (idle_thread s)"
  (wp: crunch_wps select_wp simp: crunch_simps unless_def)


lemma sai_invs[wp]:
  "\<lbrace>invs and ex_nonz_cap_to aep\<rbrace> send_async_ipc aep bdg \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: send_async_ipc_def)
  apply (rule hoare_seq_ext [OF _ get_aep_sp])
  apply (case_tac "aep_obj aepa", simp_all)
    apply (case_tac "aep_bound_tcb aepa", simp_all)
     apply (wp set_aep_minor_invs)
     apply (clarsimp simp: obj_at_def is_aep invs_def valid_pspace_def 
                           valid_state_def valid_obj_def valid_aep_def)
    apply (rule hoare_seq_ext [OF _ gts_sp])
    apply (rule hoare_pre)
     apply (rule hoare_vcg_split_if)
      apply (wp sts_invs_minor | clarsimp split: thread_state.splits)+
      apply (rule hoare_vcg_conj_lift[OF hoare_strengthen_post[OF ipc_cancel_simple]])
       apply (fastforce elim: st_tcb_weakenE)
      apply (wp ipc_cancel_ex_nonz_cap_to_tcb ipc_cancel_simple2 set_aep_minor_invs
                hoare_disjI2 ipc_cancel_cte_wp_at_not_reply_state)
    apply (clarsimp simp: invs_def valid_state_def valid_pspace_def
                          st_tcb_at_tcb_at receive_blocked_def
                          st_tcb_at_reply_cap_valid)
    apply (rule conjI, rule impI)
     apply (clarsimp simp: idle_no_ex_cap st_tcb_at_reply_cap_valid
                    split: thread_state.splits)
     apply (frule (1) st_tcb_ex_cap, fastforce split:thread_state.splits)
     apply (auto simp: st_tcb_at_def obj_at_def idle_no_ex_cap)[1]
    apply (clarsimp simp: valid_aep_def obj_at_def is_aep_def st_tcb_at_def is_tcb
                   elim!: obj_at_weakenE)
   apply (wp update_waiting_invs, simp)
   apply blast
  apply (wp set_aep_minor_invs, simp)
  apply (clarsimp simp add: valid_aep_def obj_at_def is_aep_def
                     elim!: obj_at_weakenE)
  apply (erule(1) valid_objsE[OF invs_valid_objs])
  apply (clarsimp simp: valid_obj_def valid_aep_def)
  done


crunch pred_tcb_at[wp]: set_async_ep "pred_tcb_at proj P t"

crunch typ_at[wp]: send_async_ipc "\<lambda>s. P (typ_at T t s)"
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
  apply (cases r, simp_all add: reply_from_kernel_def)
  apply (wp | simp | clarsimp)+
  done


lemma st_tcb_at_valid_st: 
  "\<lbrakk> invs s ; tcb_at t s ; st_tcb_at (op= st) t s \<rbrakk> \<Longrightarrow> valid_tcb_state st s"
  apply (clarsimp simp add: invs_def valid_state_def valid_pspace_def 
                  valid_objs_def tcb_at_def get_tcb_def pred_tcb_at_def 
                  obj_at_def)
  apply (drule_tac x=t in bspec)
   apply (erule domI)
  apply (simp add: valid_obj_def valid_tcb_def)
  done


lemma gts_eq_ts: 
  "\<lbrace> tcb_at thread \<rbrace> get_thread_state thread \<lbrace>\<lambda>rv. st_tcb_at (op= rv) thread \<rbrace>"
  apply (rule hoare_strengthen_post)
   apply (rule gts_sp)
  apply (clarsimp simp add: pred_tcb_at_def obj_at_def)
  done


declare lookup_cap_valid [wp]

crunch typ_at[wp]: send_ipc "\<lambda>s. P (typ_at T p s)"
  (wp: hoare_drop_imps simp: crunch_simps)


lemma si_tcb_at [wp]:
  "\<lbrace>tcb_at t'\<rbrace> send_ipc call bl w d t ep \<lbrace>\<lambda>rv. tcb_at t'\<rbrace>"
  by (simp add: tcb_at_typ) wp


crunch typ_at[wp]: handle_fault "\<lambda>s. P (typ_at T p s)"
  (wp: simp: crunch_simps) 


lemma hf_tcb_at [wp]:
  "\<lbrace>tcb_at t'\<rbrace> handle_fault t x \<lbrace>\<lambda>rv. tcb_at t'\<rbrace>"
  by (simp add: tcb_at_typ, wp)


lemma sfi_tcb_at [wp]:
  "\<lbrace>tcb_at t\<rbrace> send_fault_ipc t' f \<lbrace>\<lambda>_. tcb_at t\<rbrace>"
  by (simp add: tcb_at_typ, wp)


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


crunch aligned[wp]: setup_caller_cap "pspace_aligned"
  (wp: crunch_wps)

crunch "distinct"[wp]: setup_caller_cap "pspace_distinct"
  (wp: crunch_wps)

crunch cur_tcb[wp]: setup_caller_cap "cur_tcb"


lemma setup_caller_cap_state_refs_of[wp]:
  "\<lbrace>\<lambda>s. P ((state_refs_of s) (sender := {r \<in> state_refs_of s sender. snd r = TCBBound}))\<rbrace>
     setup_caller_cap sender rcvr
   \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (simp add: setup_caller_cap_def)
  apply wp
  apply (simp add: fun_upd_def cong: if_cong)
  done


lemma setup_caller_cap_objs[wp]:
  "\<lbrace>valid_objs and pspace_aligned and
    st_tcb_at (Not \<circ> halted) sender and
    st_tcb_at active rcvr and
    K (sender \<noteq> rcvr)\<rbrace>
   setup_caller_cap sender rcvr
   \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  apply (simp add: setup_caller_cap_def)
  apply (rule hoare_pre)
   apply (wp set_thread_state_valid_cap sts_tcb_cap_valid_cases)
  apply (subgoal_tac "s \<turnstile> cap.ReplyCap sender False")
   prefer 2
   apply (fastforce simp: valid_cap_def cap_aligned_def word_bits_def
                         st_tcb_def2 tcb_at_def is_tcb
                   dest: pspace_alignedD get_tcb_SomeD)
  apply (subgoal_tac "tcb_cap_valid (cap.ReplyCap sender False) (rcvr, tcb_cnode_index 3) s")
   prefer 2
   apply (clarsimp simp: tcb_cap_valid_def is_cap_simps
                  split: Structures_A.thread_state.splits
                  elim!: pred_tcb_weakenE)
  apply (clarsimp simp: valid_tcb_state_def st_tcb_def2)
  done


lemma setup_caller_cap_mdb[wp]:
  "\<lbrace>valid_mdb and valid_objs and pspace_aligned and
    st_tcb_at (Not \<circ> halted) sender and
    K (sender \<noteq> rcvr)\<rbrace>
   setup_caller_cap sender rcvr
   \<lbrace>\<lambda>_. valid_mdb\<rbrace>"
  apply (simp add: setup_caller_cap_def)
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


lemma setup_caller_cap_iflive[wp]:
  "\<lbrace>if_live_then_nonz_cap and st_tcb_at (Not \<circ> halted) sender\<rbrace>
   setup_caller_cap sender rcvr
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  apply (simp add: setup_caller_cap_def)
  apply (wp cap_insert_iflive)
  apply (clarsimp elim!: st_tcb_ex_cap)
  done


crunch zombies[wp]: setup_caller_cap "zombies_final"


lemma setup_caller_cap_globals[wp]:
  "\<lbrace>valid_objs and valid_global_refs and
    st_tcb_at (Not \<circ> halted) sender\<rbrace>
   setup_caller_cap sender rcvr
   \<lbrace>\<lambda>rv. valid_global_refs\<rbrace>"
  apply (simp add: setup_caller_cap_def)
  apply (rule hoare_pre, wp)
  apply clarsimp
  apply (frule st_tcb_at_reply_cap_valid, clarsimp+)
  apply (clarsimp simp: cte_wp_at_caps_of_state cap_range_def)
  done


lemma setup_caller_cap_ifunsafe[wp]:
  "\<lbrace>if_unsafe_then_cap and valid_objs and tcb_at rcvr and ex_nonz_cap_to rcvr\<rbrace> setup_caller_cap sender rcvr \<lbrace>\<lambda>rv. if_unsafe_then_cap\<rbrace>"
  apply (simp add: setup_caller_cap_def)
  apply (wp cap_insert_ifunsafe ex_cte_cap_to_pres)
   apply (clarsimp simp: ex_nonz_tcb_cte_caps dom_tcb_cap_cases)
  apply clarsimp
  done


lemmas transfer_caps_loop_cap_to[wp] = transfer_caps_loop_pres [OF cap_insert_ex_cap]


crunch cap_to[wp]: set_extra_badge "ex_nonz_cap_to p"


crunch cap_to[wp]: do_ipc_transfer "ex_nonz_cap_to p"
  (wp: crunch_wps 
    simp: zipWithM_x_mapM ignore: transfer_caps_loop)


crunch it[wp]: receive_ipc "\<lambda>s. P (idle_thread s)"
  (wp: hoare_drop_imps simp: crunch_simps zipWithM_x_mapM)


lemma setup_caller_cap_idle[wp]:
  "\<lbrace>valid_idle and (\<lambda>s. st \<noteq> idle_thread s \<and> rt \<noteq> idle_thread s)\<rbrace>
   setup_caller_cap st rt
   \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  apply (simp add: setup_caller_cap_def)
  apply (wp cap_insert_idle | simp)+
  done


crunch typ_at[wp]: setup_caller_cap "\<lambda>s. P (typ_at T p s)"
  (wp: crunch_wps simp: crunch_simps)


crunch arch[wp]: setup_caller_cap "\<lambda>s. P (arch_state s)"
  (wp: crunch_wps simp: crunch_simps)


crunch irq_node[wp]: setup_caller_cap "\<lambda>s. P (interrupt_irq_node s)"


crunch Pmdb[wp]: set_thread_state "\<lambda>s. P (cdt s)"


lemma setup_caller_cap_valid_arch [wp]:
  "\<lbrace>valid_arch_state\<rbrace> setup_caller_cap x y \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  by (rule valid_arch_state_lift) wp


lemma setup_caller_cap_reply[wp]:
  "\<lbrace>valid_reply_caps and pspace_aligned and
    st_tcb_at (Not \<circ> awaiting_reply) st and tcb_at rt\<rbrace>
   setup_caller_cap st rt
   \<lbrace>\<lambda>rv. valid_reply_caps\<rbrace>"
  apply (simp add: setup_caller_cap_def)
  apply wp
    apply (rule_tac Q="\<lambda>rv s. pspace_aligned s \<and> tcb_at st s \<and>
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
  apply (strengthen reply_cap_doesnt_exist_strg)
  apply (clarsimp split: option.split)
  done


lemma setup_caller_cap_reply_masters[wp]:
  "\<lbrace>valid_reply_masters and tcb_at rt\<rbrace>
   setup_caller_cap st rt
   \<lbrace>\<lambda>rv. valid_reply_masters\<rbrace>"
  unfolding setup_caller_cap_def
  by (wp | simp add: is_cap_simps tcb_at_cte_at dom_tcb_cap_cases)+


lemma setup_caller_cap_irq_handlers[wp]:
  "\<lbrace>valid_irq_handlers and tcb_at st\<rbrace>
   setup_caller_cap st rt
   \<lbrace>\<lambda>rv. valid_irq_handlers\<rbrace>"
  unfolding setup_caller_cap_def
  by (wp | simp add: is_cap_simps tcb_at_cte_at dom_tcb_cap_cases)+


lemma setup_caller_cap_valid_arch_caps[wp]:
  "\<lbrace>valid_arch_caps and valid_objs
           and st_tcb_at (Not o halted) sender\<rbrace>
     setup_caller_cap sender recvr
   \<lbrace>\<lambda>rv. valid_arch_caps\<rbrace>"
  apply (simp add: setup_caller_cap_def)
  apply (rule hoare_pre)
   apply (wp cap_insert_valid_arch_caps | simp)+
  apply (auto elim: st_tcb_at_reply_cap_valid)
  done


lemma setup_caller_cap_valid_global_objs[wp]:
  "\<lbrace>valid_global_objs\<rbrace> setup_caller_cap send recv \<lbrace>\<lambda>rv. valid_global_objs\<rbrace>"
  apply (wp valid_global_objs_lift valid_ao_at_lift)
  apply (simp_all add: setup_caller_cap_def)
   apply (wp sts_obj_at_impossible | simp add: tcb_not_empty_table)+
  done


crunch irq_handlers[wp]: set_endpoint "valid_irq_handlers"
  (wp: crunch_wps)

crunch arch_objs [wp]: setup_caller_cap "valid_arch_objs"

crunch v_ker_map[wp]: setup_caller_cap "valid_kernel_mappings"

crunch eq_ker_map[wp]: setup_caller_cap "equal_kernel_mappings"

crunch asid_map [wp]: setup_caller_cap "valid_asid_map"

crunch global_pd_mappings[wp]: setup_caller_cap "valid_global_pd_mappings"

crunch pspace_in_kernel_window[wp]: setup_caller_cap "pspace_in_kernel_window"

lemma setup_caller_cap_cap_refs_in_window[wp]:
  "\<lbrace>valid_objs and cap_refs_in_kernel_window and
    st_tcb_at (Not \<circ> halted) sender\<rbrace>
   setup_caller_cap sender rcvr
   \<lbrace>\<lambda>rv. cap_refs_in_kernel_window\<rbrace>"
  apply (simp add: setup_caller_cap_def)
  apply (rule hoare_pre, wp)
  apply clarsimp
  apply (frule st_tcb_at_reply_cap_valid, clarsimp+)
  apply (clarsimp simp: cte_wp_at_caps_of_state cap_range_def)
  done

crunch only_idle [wp]: setup_caller_cap only_idle
  (wp: sts_only_idle)

crunch valid_ioc[wp]: setup_caller_cap valid_ioc

crunch vms[wp]: setup_caller_cap "valid_machine_state"

crunch valid_irq_states[wp]: setup_caller_cap "valid_irq_states"

crunch valid_irq_states[wp]: do_ipc_transfer "valid_irq_states"
  (wp: crunch_wps simp: crunch_simps)
(*
lemma as_user_obj_at_aep:
  "\<lbrace>obj_at P aepptr\<rbrace> as_user t m \<lbrace>obj_at P aepptr\<rbrace>"
*)

lemma complete_async_ipc_invs:
  "\<lbrace>invs and tcb_at tcb\<rbrace>
     complete_async_ipc aepptr tcb
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: complete_async_ipc_def)
  apply (rule hoare_seq_ext[OF _ get_aep_sp])
  apply (rule hoare_pre)
   apply (wp set_aep_minor_invs | wpc | simp)+
   apply (rule_tac Q="\<lambda>_ s. (state_refs_of s aepptr = aep_bound_refs (aep_bound_tcb aep)) 
                      \<and> (\<exists>T. typ_at T aepptr s) \<and> valid_aep (aep_set_obj aep IdleAEP) s 
                      \<and> ((\<exists>y. aep_bound_tcb aep = Some y) \<longrightarrow> ex_nonz_cap_to aepptr s)" 
                      in hoare_strengthen_post) 
    apply (wp hoare_vcg_all_lift static_imp_wp hoare_vcg_ex_lift | wpc | simp add: valid_aep_def valid_bound_tcb_def split: option.splits)+
    apply ((clarsimp simp: obj_at_def state_refs_of_def)+)[2]
  apply (auto simp: is_aep ko_at_state_refs_ofD valid_aep_def valid_obj_def
              elim: if_live_then_nonz_capD[OF invs_iflive] obj_at_weakenE 
                    obj_at_valid_objsE[OF _ invs_valid_objs])
  done

lemma ri_invs':
  notes split_if[split del]
  assumes set_endpoint_Q[wp]: "\<And>a b.\<lbrace>Q\<rbrace> set_endpoint a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes set_async_ep_Q[wp]: "\<And>a b.\<lbrace>Q\<rbrace> complete_async_ipc a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes sts_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> set_thread_state a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes ext_Q[wp]: "\<And>a (s::'a::state_ext state). \<lbrace>Q and valid_objs\<rbrace> do_extended_op (switch_if_required_to a) \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes scc_Q[wp]: "\<And>a b. \<lbrace>valid_mdb and Q\<rbrace> setup_caller_cap a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes dit_Q[wp]: "\<And>a b c d e f. \<lbrace>valid_mdb and valid_objs and Q\<rbrace> do_ipc_transfer a b c d e f \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes failed_transfer_Q[wp]: "\<And>a. \<lbrace>Q\<rbrace> do_nbwait_failed_transfer a \<lbrace>\<lambda>_. Q\<rbrace>"
  notes dxo_wp_weak[wp del]
  shows
  "\<lbrace>(invs::'a::state_ext state \<Rightarrow> bool) and Q and st_tcb_at active t and ex_nonz_cap_to t
         and cte_wp_at (op = cap.NullCap) (t, tcb_cnode_index 3)
         and (\<lambda>s. \<forall>r\<in>zobj_refs cap. ex_nonz_cap_to r s)\<rbrace>
     receive_ipc t cap is_blocking \<lbrace>\<lambda>r s. invs s \<and> Q s\<rbrace>" (is "\<lbrace>?pre\<rbrace> _ \<lbrace>_\<rbrace>")
  apply (simp add: receive_ipc_def split_def)
  apply (cases cap, simp_all)
  apply (rename_tac ep badge rights)
  apply (rule hoare_seq_ext[OF _ get_endpoint_sp])
  apply (rule hoare_seq_ext[OF _ gba_sp])
  apply (rule hoare_seq_ext)
  (* set up precondition for old proof *)
   apply (rule_tac R="ko_at (Endpoint x) ep and ?pre" in hoare_vcg_split_if)
    apply (wp complete_async_ipc_invs)
   apply (case_tac x)
    apply (wp | rule hoare_pre, wpc | simp)+
     apply (simp add: invs_def valid_state_def valid_pspace_def)
     apply (rule hoare_pre, wp valid_irq_node_typ)
      apply (simp add: valid_ep_def)
      apply (wp valid_irq_node_typ sts_only_idle 
                failed_transfer_Q[simplified do_nbwait_failed_transfer_def, simplified] 
            | simp add: do_nbwait_failed_transfer_def split del: split_if)+
     apply (clarsimp simp: st_tcb_at_tcb_at valid_tcb_state_def invs_def valid_state_def valid_pspace_def)
     apply (rule conjI, clarsimp elim!: obj_at_weakenE simp: is_ep_def)
     apply (rule conjI, clarsimp simp: st_tcb_at_reply_cap_valid)
     apply (rule conjI)
      apply (subgoal_tac "ep \<noteq> t")
       apply (drule obj_at_state_refs_ofD)
       apply (drule active_st_tcb_at_state_refs_ofD)
       apply (erule delta_sym_refs)
        apply (clarsimp split: split_if_asm)
       apply (clarsimp split: split_if_asm split_if)
       apply (fastforce dest!: symreftype_inverse' 
                         simp: pred_tcb_at_def2 tcb_bound_refs_def2)
      apply (clarsimp simp: obj_at_def st_tcb_at_def)
     apply (simp add: obj_at_def is_ep_def)
     apply (fastforce dest!: idle_no_ex_cap valid_reply_capsD
                      simp: st_tcb_def2)
    apply (simp add: invs_def valid_state_def valid_pspace_def)
    apply (wp hoare_drop_imps valid_irq_node_typ hoare_post_imp[OF disjI1]
              sts_only_idle 
         | simp add: valid_tcb_state_def
         | strengthen reply_cap_doesnt_exist_strg | wpc
         | (wp hoare_vcg_conj_lift | wp dxo_wp_weak | simp)+)+
    apply (clarsimp simp: st_tcb_at_tcb_at neq_Nil_conv)
    apply (frule(1) sym_refs_obj_atD)
    apply (frule ko_at_state_refs_ofD)
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
     apply (clarsimp simp: st_tcb_def2 obj_at_def is_ep_def)
     apply (erule delta_sym_refs)
      apply (clarsimp split: split_if_asm)
     apply (clarsimp split: split_if_asm split_if) 
       apply ((fastforce simp: pred_tcb_at_def2 tcb_bound_refs_def2 is_tcb
                       dest!: symreftype_inverse')+)[3]
    apply (rule conjI)
     apply (clarsimp simp: pred_tcb_at_def2 tcb_bound_refs_def2
                     split: split_if_asm)
     apply (simp add: set_eq_subset)

    apply (rule conjI, clarsimp dest!: idle_no_ex_cap)+
    apply (simp add: idle_not_queued')
   apply (simp add: invs_def valid_state_def valid_pspace_def)
   apply (rule hoare_pre)
    apply (wp hoare_vcg_const_Ball_lift valid_irq_node_typ sts_only_idle 
              failed_transfer_Q[unfolded do_nbwait_failed_transfer_def, simplified]
              | simp add: valid_ep_def do_nbwait_failed_transfer_def | wpc)+
   apply (clarsimp simp: valid_tcb_state_def st_tcb_at_tcb_at)
   apply (frule ko_at_state_refs_ofD)
   apply (frule active_st_tcb_at_state_refs_ofD)
   apply (frule(1) sym_refs_ko_atD)
   apply (rule obj_at_valid_objsE, assumption+)
   apply (clarsimp simp: valid_obj_def valid_ep_def)
   apply (rule context_conjI)
    apply (rule notI, (drule(1) bspec)+, (drule obj_at_state_refs_ofD)+, clarsimp)
    apply (clarsimp simp: pred_tcb_at_def2 tcb_bound_refs_def2)
    apply (blast intro: reftype.simps)
   apply (rule conjI, clarsimp elim!: obj_at_weakenE simp: is_ep_def)
   apply (rule conjI, fastforce simp: st_tcb_def2)
   apply (rule conjI, erule delta_sym_refs)
     apply (clarsimp split: split_if_asm split_if)
     apply (rule conjI, rule impI)
      apply (clarsimp simp: pred_tcb_at_def2 obj_at_def)
     apply (fastforce simp: pred_tcb_at_def2 tcb_bound_refs_def2
                     dest!: symreftype_inverse')
    apply (clarsimp split: split_if_asm split_if)
    apply (fastforce simp: pred_tcb_at_def2 tcb_bound_refs_def2
                    dest!: symreftype_inverse')
   apply (fastforce simp: obj_at_def is_ep pred_tcb_at_def2 dest!: idle_no_ex_cap valid_reply_capsD)
  apply (rule hoare_pre)
   apply (wp get_aep_wp | wpc | clarsimp)+
  apply (clarsimp simp: pred_tcb_at_tcb_at)
  done

lemmas ri_invs[wp] = ri_invs'[where Q=\<top>,simplified hoare_post_taut, OF TrueI TrueI TrueI,simplified]

crunch aep_at[wp]: set_message_info "aep_at aep"

crunch typ_at[wp]: set_message_info "\<lambda>s. P (typ_at T p s)"
  (wp: crunch_wps simp: crunch_simps)

crunch it[wp]: set_message_info "\<lambda>s. P (idle_thread s)"
  (wp: crunch_wps simp: crunch_simps)

crunch arch[wp]: set_message_info "\<lambda>s. P (arch_state s)"
  (wp: crunch_wps simp: crunch_simps)

lemma set_message_info_valid_arch [wp]:
  "\<lbrace>valid_arch_state\<rbrace> set_message_info a b \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  by (rule valid_arch_state_lift) wp

crunch caps[wp]: set_message_info "\<lambda>s. P (caps_of_state s)"

crunch irq_node[wp]: set_message_info "\<lambda>s. P (interrupt_irq_node s)"
  (simp: crunch_simps)

lemma set_message_info_global_refs [wp]:
  "\<lbrace>valid_global_refs\<rbrace> set_message_info a b \<lbrace>\<lambda>_. valid_global_refs\<rbrace>"
  by (rule valid_global_refs_cte_lift) wp

lemma set_mrs_valid_arch [wp]:
  "\<lbrace>valid_arch_state\<rbrace> set_mrs a b c \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  by (rule valid_arch_state_lift) wp

crunch irq_node[wp]: set_mrs "\<lambda>s. P (interrupt_irq_node s)"
  (wp: crunch_wps simp: crunch_simps)

lemma set_mrs_global_refs [wp]:
  "\<lbrace>valid_global_refs\<rbrace> set_mrs a b c \<lbrace>\<lambda>_. valid_global_refs\<rbrace>"
  by (rule valid_global_refs_cte_lift) wp

crunch interrupt_states[wp]: set_message_info "\<lambda>s. P (interrupt_states s)"
  (simp: crunch_simps )

crunch interrupt_states[wp]: set_mrs "\<lambda>s. P (interrupt_states s)"
  (simp: crunch_simps wp: crunch_wps)

lemma tcb_cap_cases_tcb_context:
  "\<forall>(getF, v)\<in>ran tcb_cap_cases.
         getF (tcb_context_update F tcb) = getF tcb"
  by (rule ball_tcb_cap_casesI, simp+)

crunch valid_arch_caps[wp]: set_message_info "valid_arch_caps"

lemma valid_bound_tcb_exst[iff]:
 "valid_bound_tcb t (trans_state f s) = valid_bound_tcb t s"
  by (auto simp: valid_bound_tcb_def split:option.splits)

(* joel move *)
lemma valid_bound_tcb_typ_at:
  "\<forall>p. \<lbrace>\<lambda>s. typ_at ATCB p s\<rbrace> f \<lbrace>\<lambda>_ s. typ_at ATCB p s\<rbrace>
   \<Longrightarrow> \<lbrace>\<lambda>s. valid_bound_tcb tcb s\<rbrace> f \<lbrace>\<lambda>_ s. valid_bound_tcb tcb s\<rbrace>"
  apply (clarsimp simp: valid_bound_tcb_def split: option.splits)
  apply (wp hoare_vcg_all_lift tcb_at_typ_at static_imp_wp)
  apply (fastforce)
  done

crunch bound_tcb[wp]: set_thread_state, set_message_info, set_mrs "valid_bound_tcb t"
(wp: valid_bound_tcb_typ_at set_object_typ_at mapM_wp ignore: set_object
 simp: zipWithM_x_mapM)

lemma rai_invs':
  assumes set_async_ep_Q[wp]: "\<And>a b.\<lbrace> Q\<rbrace> set_async_ep a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes sts_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> set_thread_state a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes smi_Q[wp]: "\<And>a b.\<lbrace>Q\<rbrace> set_message_info a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes as_user_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> as_user a b \<lbrace>\<lambda>r::unit. Q\<rbrace>"
  assumes set_mrs_Q[wp]: "\<And>a b c. \<lbrace>Q\<rbrace> set_mrs a b c \<lbrace>\<lambda>_.Q\<rbrace>"
  shows
  "\<lbrace>invs and Q and st_tcb_at active t and ex_nonz_cap_to t
         and (\<lambda>s. \<forall>r\<in>zobj_refs cap. ex_nonz_cap_to r s)
         and (\<lambda>s. \<exists>aepptr. is_aep_cap cap \<and> cap_ep_ptr cap = aepptr \<and>
                     obj_at (\<lambda>ko. \<exists>aep. ko = AsyncEndpoint aep \<and> (aep_bound_tcb aep = None
                                                          \<or> aep_bound_tcb aep = Some t)) aepptr s)\<rbrace>
     receive_async_ipc t cap is_blocking
   \<lbrace>\<lambda>r s. invs s \<and> Q s\<rbrace>"
  apply (simp add: receive_async_ipc_def)
  apply (cases cap, simp_all)
  apply (rename_tac aep badge rights)
  apply (rule hoare_seq_ext [OF _ get_aep_sp])
  apply (case_tac "aep_obj x")
    apply (simp add: invs_def valid_state_def valid_pspace_def)
    apply (rule hoare_pre)
     apply (wp set_aep_valid_objs valid_irq_node_typ sts_only_idle
              | simp add: valid_aep_def do_nbwait_failed_transfer_def | wpc)+
    apply (clarsimp simp: valid_tcb_state_def st_tcb_at_tcb_at)
    apply (rule conjI, clarsimp elim!: obj_at_weakenE simp: is_aep_def)
    apply (rule conjI, clarsimp simp: st_tcb_at_reply_cap_valid)
    apply (rule conjI, clarsimp simp: obj_at_def split: option.splits)
    apply (rule conjI, clarsimp simp: valid_bound_tcb_def obj_at_def
                                dest!: st_tcb_at_tcb_at
                                split: option.splits)
    apply (rule conjI)
     apply (subgoal_tac "t \<noteq> aep")
      apply (drule ko_at_state_refs_ofD)
      apply (drule active_st_tcb_at_state_refs_ofD)
      apply (erule delta_sym_refs)
       apply (clarsimp split: split_if_asm)
      apply (fastforce simp: pred_tcb_at_def2 tcb_bound_refs_def2 split: split_if_asm)
     apply (clarsimp simp: obj_at_def pred_tcb_at_def)
    apply (simp add: is_aep obj_at_def)
    apply (fastforce dest!: idle_no_ex_cap valid_reply_capsD
                    elim!: pred_tcb_weakenE
                    simp: st_tcb_at_reply_cap_valid st_tcb_def2)
   apply (simp add: invs_def valid_state_def valid_pspace_def)
   apply (rule hoare_pre)
    apply (wp set_aep_valid_objs hoare_vcg_const_Ball_lift
              valid_irq_node_typ sts_only_idle
              | simp add: valid_aep_def do_nbwait_failed_transfer_def | wpc)+
   apply (clarsimp simp: valid_tcb_state_def st_tcb_at_tcb_at)
   apply (rule conjI, clarsimp elim!: obj_at_weakenE simp: is_aep_def)
   apply (rule obj_at_valid_objsE, assumption+)
   apply (clarsimp simp: valid_obj_def valid_aep_def)
   apply (frule(1) sym_refs_ko_atD, simp)
   apply (frule ko_at_state_refs_ofD)
   apply (frule active_st_tcb_at_state_refs_ofD)
   apply (rule conjI, clarsimp simp: st_tcb_at_reply_cap_valid)
   apply (rule context_conjI, fastforce simp: pred_tcb_at_def obj_at_def
                                              tcb_bound_refs_def2 state_refs_of_def)
   apply (subgoal_tac "aep_bound_tcb x = None")
    apply (rule conjI, clarsimp split: option.splits)
    apply (rule conjI, erule delta_sym_refs)
      apply (fastforce simp: pred_tcb_at_def2 obj_at_def symreftype_inverse'
                      split: split_if_asm)
     apply (fastforce simp: pred_tcb_at_def2 tcb_bound_refs_def2 split: split_if_asm)
    apply (simp add: obj_at_def is_aep idle_not_queued)
    apply (fastforce dest: idle_no_ex_cap valid_reply_capsD
                    elim!: pred_tcb_weakenE
                     simp: st_tcb_at_reply_cap_valid st_tcb_def2)
   apply (clarsimp simp: valid_obj_def valid_aep_def obj_at_def
                   elim: obj_at_valid_objsE
                  split: option.splits)
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (rule hoare_pre)
   apply (wp set_aep_valid_objs hoare_vcg_const_Ball_lift
             valid_irq_node_typ ball_tcb_cap_casesI static_imp_wp
             | simp add: valid_aep_def)+
  apply clarsimp
  apply (rule conjI, clarsimp simp: valid_bound_tcb_def obj_at_def pred_tcb_at_def2 is_tcb
                             split: option.splits)
  apply (frule ko_at_state_refs_ofD)
  apply (frule active_st_tcb_at_state_refs_ofD)
  apply (rule conjI, erule delta_sym_refs)
    apply (clarsimp split: split_if_asm)
   apply (clarsimp split: split_if_asm)
  apply (fastforce simp: obj_at_def is_aep_def state_refs_of_def
                        valid_idle_def pred_tcb_at_def
                        st_tcb_at_reply_cap_valid
                  dest: valid_reply_capsD)
  done

lemmas rai_invs[wp] = rai_invs'[where Q=\<top>,simplified hoare_post_taut, OF TrueI TrueI TrueI,simplified]

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


crunch cap_to[wp]: receive_ipc "ex_nonz_cap_to p"
  (wp: cap_insert_ex_cap hoare_drop_imps simp: crunch_simps)


crunch cap_to[wp]: receive_async_ipc "ex_nonz_cap_to p"
  (wp: crunch_wps)


crunch ex_nonz_cap_to[wp]: set_message_info "ex_nonz_cap_to p"


lemma is_derived_not_Null [simp]:
  "\<not>is_derived m p c cap.NullCap"
  by (auto simp add: is_derived_def cap_master_cap_simps dest: cap_master_cap_eqDs)

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
  apply (cases ep, simp_all add: queue_of_def valid_ep_def
                                 st_tcb_at_refs_of_rev)
   apply (drule(1) bspec)
   apply (erule st_tcb_ex_cap, clarsimp+)
  apply (drule(1) bspec)
  apply (erule st_tcb_ex_cap, clarsimp+)
  done

lemma si_invs':
  assumes set_endpoint_Q[wp]: "\<And>a b.\<lbrace>Q\<rbrace> set_endpoint a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes ext_Q[wp]: "\<And>a. \<lbrace>Q and valid_objs\<rbrace> do_extended_op (attempt_switch_to a) \<lbrace>\<lambda>_. Q\<rbrace>"
  assumes sts_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> set_thread_state a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes setup_caller_cap_Q[wp]: "\<And>send receive. \<lbrace>Q and valid_mdb\<rbrace> setup_caller_cap send receive \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes do_ipc_transfer_Q[wp]: "\<And>a b c d e f. \<lbrace>Q and valid_objs and valid_mdb\<rbrace> do_ipc_transfer a b c d e f \<lbrace>\<lambda>_.Q\<rbrace>"
  notes dxo_wp_weak[wp del]
  shows
  "\<lbrace>invs and Q and st_tcb_at active t
         and ex_nonz_cap_to ep and ex_nonz_cap_to t\<rbrace>
    send_ipc bl call ba cg t ep \<lbrace>\<lambda>r s. invs s \<and> Q s\<rbrace>"
  apply (simp add: send_ipc_def)
  apply (rule hoare_seq_ext [OF _ get_endpoint_sp])
  apply (case_tac epa, simp_all)
    apply (cases bl, simp_all)[1]
     apply (simp add: invs_def valid_state_def valid_pspace_def)
     apply (wp valid_irq_node_typ)
     apply (simp add: valid_ep_def)
     apply (rule hoare_pre, wp valid_irq_node_typ sts_only_idle)
     apply (clarsimp simp: valid_tcb_state_def st_tcb_at_tcb_at)
     apply (rule conjI, clarsimp elim!: obj_at_weakenE simp: is_ep_def)
     apply (rule conjI, clarsimp simp: st_tcb_at_reply_cap_valid)
     apply (rule conjI, subgoal_tac "t \<noteq> ep")
       apply (drule ko_at_state_refs_ofD active_st_tcb_at_state_refs_ofD)+
       apply (erule delta_sym_refs)
        apply (clarsimp split: split_if_asm)
       apply (fastforce simp: pred_tcb_at_def2
                       dest!: refs_in_tcb_bound_refs
                       split: split_if_asm)
      apply (clarsimp simp: pred_tcb_at_def obj_at_def)
     apply (simp add: obj_at_def is_ep)
     apply (fastforce dest: idle_no_ex_cap valid_reply_capsD
                     simp: st_tcb_def2)
    apply (wp, simp)
   apply (rename_tac list)
   apply (cases bl, simp_all)[1]
    apply (simp add: invs_def valid_state_def valid_pspace_def)
    apply (wp valid_irq_node_typ)
    apply (simp add: valid_ep_def)
    apply (rule hoare_pre, wp hoare_vcg_const_Ball_lift
                              valid_irq_node_typ sts_only_idle)
    apply (clarsimp simp: valid_tcb_state_def st_tcb_at_tcb_at)
    apply (frule ko_at_state_refs_ofD)
    apply (frule active_st_tcb_at_state_refs_ofD)
    apply (subgoal_tac "t \<noteq> ep \<and> t \<notin> set list")
     apply (erule obj_at_valid_objsE, clarsimp+)
     apply (clarsimp simp: valid_obj_def valid_ep_def)
     apply (rule conjI, clarsimp simp: obj_at_def is_ep_def)
     apply (rule conjI, clarsimp simp: st_tcb_at_reply_cap_valid)
     apply (rule conjI, erule delta_sym_refs)
       apply (fastforce split: split_if_asm)
      apply (fastforce simp: pred_tcb_at_def2
                      dest!: refs_in_tcb_bound_refs
                      split: split_if_asm)
     apply (simp add: obj_at_def is_ep idle_not_queued)
     apply (fastforce dest: idle_no_ex_cap valid_reply_capsD
                     simp: st_tcb_def2)
    apply (rule conjI, clarsimp simp: pred_tcb_at_def obj_at_def)
    apply (drule(1) sym_refs_ko_atD, clarsimp simp: st_tcb_at_refs_of_rev)
    apply (drule(1) bspec, clarsimp simp: pred_tcb_at_def obj_at_def)
   apply (wp, simp)
  apply (rename_tac list)
  apply (case_tac list, simp_all)
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (rule hoare_pre)
   apply (wp valid_irq_node_typ)
          apply (simp add: if_apply_def2)
          apply (wp hoare_drop_imps sts_st_tcb_at_cases valid_irq_node_typ do_ipc_transfer_tcb_caps
                    sts_only_idle hoare_vcg_if_lift hoare_vcg_disj_lift thread_get_wp' hoare_vcg_all_lift
               | clarsimp simp:is_cap_simps  | wpc
               | strengthen reply_cap_doesnt_exist_strg
                            disjI2_strg[where Q="cte_wp_at (\<lambda>cp. is_master_reply_cap cp \<and> R cp) p s"]
               | (wp hoare_vcg_conj_lift static_imp_wp | wp dxo_wp_weak | simp)+)+
  apply (clarsimp simp: ep_redux_simps conj_ac cong: list.case_cong if_cong)
  apply (frule(1) sym_refs_ko_atD)
  apply (clarsimp simp: st_tcb_at_refs_of_rev st_tcb_at_tcb_at)
  apply (frule ko_at_state_refs_ofD)
  apply (frule active_st_tcb_at_state_refs_ofD)
  apply (erule(1) obj_at_valid_objsE)
  apply clarsimp
  apply (subgoal_tac "distinct ([t, a, ep, idle_thread s])")
   apply (clarsimp simp: fun_upd_def[symmetric] fun_upd_idem)
   apply (clarsimp simp: valid_obj_def valid_ep_def neq_Nil_conv
                         fun_upd_triv)
   apply (rule conjI, erule(1) st_tcb_ex_cap)
    apply clarsimp
   apply (simp add: obj_at_def is_ep idle_not_queued')
   apply (subgoal_tac "state_refs_of s t = {r \<in> state_refs_of s t. snd r = TCBBound}")
    apply (subst fun_upd_idem[where x=t], force simp: conj_ac)
    apply (subgoal_tac "sym_refs ((state_refs_of s)(ep := set lista \<times> {EPRecv}, a := {r \<in> state_refs_of s a. snd r = TCBBound}))")
     apply (fastforce elim!: pred_tcb_weakenE st_tcb_at_reply_cap_valid simp: conj_ac)

    apply (erule delta_sym_refs)
     apply (clarsimp simp: fun_upd_def split: split_if_asm)
    apply (fastforce simp: fun_upd_def
                    dest!: symreftype_inverse' st_tcb_at_state_refs_ofD refs_in_tcb_bound_refs 
                    split: split_if_asm)
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
  assumes ext_Q[wp]: "\<And>a. \<lbrace>Q and valid_objs\<rbrace> do_extended_op (attempt_switch_to a) \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes setup_caller_cap_Q[wp]: "\<And>send receive. \<lbrace>Q and valid_mdb\<rbrace> setup_caller_cap send receive \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes do_ipc_transfer_Q[wp]: "\<And>a b c d e f. \<lbrace>Q and valid_objs and valid_mdb\<rbrace> do_ipc_transfer a b c d e f \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes thread_set_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> thread_set a b \<lbrace>\<lambda>_.Q\<rbrace>"
  notes si_invs''[wp] = si_invs'[where Q=Q]
  shows
  "\<lbrace>invs and Q and st_tcb_at active t and ex_nonz_cap_to t and (\<lambda>_. valid_fault f)\<rbrace>
   handle_fault t f
   \<lbrace>\<lambda>r s. invs s \<and> Q s\<rbrace>"
  apply (simp add: handle_fault_def)
  apply wp
    apply (simp add: handle_double_fault_def)
    apply (wp sts_invs_minor)
   apply (simp add: send_fault_ipc_def Let_def)
   apply wp
     apply (rule_tac P="invs and Q and st_tcb_at active t and ex_nonz_cap_to t and
                        (\<lambda>_. valid_fault f) and (\<lambda>s. t \<noteq> idle_thread s) and
                        (\<lambda>s. \<forall>r \<in> zobj_refs handler_cap. ex_nonz_cap_to r s)"
                   in hoare_trivE)
     apply (case_tac handler_cap)
               apply (strengthen reply_cap_doesnt_exist_strg
            | clarsimp simp: tcb_cap_cases_def
            | rule conjI
            | wp hoare_drop_imps
                 thread_set_no_change_tcb_state ex_nonz_cap_to_pres
                 thread_set_cte_wp_at_trivial
            | fastforce elim!: pred_tcb_weakenE
                       simp: invs_def valid_state_def valid_idle_def st_tcb_def2
                    split: Structures_A.thread_state.splits)+
              apply (rule hoare_pre_imp[rotated])
               apply (rule_tac P="valid_fault f" in hoare_gen_asm)
               apply (wp thread_set_invs_trivial)
                     apply (strengthen reply_cap_doesnt_exist_strg
             | clarsimp simp: tcb_cap_cases_def
             | rule conjI
             | wp hoare_drop_imps
                  thread_set_no_change_tcb_state ex_nonz_cap_to_pres
                  thread_set_cte_wp_at_trivial
             | fastforce elim!: pred_tcb_weakenE 
                        simp: invs_def valid_state_def valid_idle_def pred_tcb_def2 
                              valid_pspace_def idle_no_ex_cap
                     split: Structures_A.thread_state.splits)+
  done


lemmas hf_invs[wp] = hf_invs'[where Q=\<top>,simplified hoare_post_taut, OF TrueI TrueI TrueI TrueI TrueI,simplified]


crunch pred_tcb_at[wp]: set_message_info "pred_tcb_at proj P t"


lemma rai_pred_tcb_neq:
  "\<lbrace>pred_tcb_at proj P t' and K (t \<noteq> t')\<rbrace> 
  receive_async_ipc t cap is_blocking
  \<lbrace>\<lambda>rv. pred_tcb_at proj P t'\<rbrace>"
  apply (simp add: receive_async_ipc_def)
  apply (rule hoare_pre)
   by (wp sts_st_tcb_at_neq get_aep_wp | wpc | clarsimp simp add: do_nbwait_failed_transfer_def)+

crunch ct[wp]: set_mrs "\<lambda>s. P (cur_thread s)" 
  (wp: case_option_wp mapM_wp)


lemma get_ep_ko [wp]:
  "\<lbrace>\<top>\<rbrace> get_endpoint e \<lbrace>\<lambda>rv. ko_at (Endpoint rv) e\<rbrace>"
  apply (rule hoare_strengthen_post)
  apply (rule get_endpoint_sp)
  apply simp
  done


crunch typ_at[wp]: receive_ipc "\<lambda>s. P (typ_at T p s)"
  (wp: hoare_drop_imps simp: crunch_simps)


lemma ri_tcb [wp]:
  "\<lbrace>tcb_at t'\<rbrace> receive_ipc t cap is_blocking \<lbrace>\<lambda>rv. tcb_at t'\<rbrace>"
  by (simp add: tcb_at_typ, wp)


crunch typ_at[wp]: receive_async_ipc "\<lambda>s. P (typ_at T p s)"
  (wp: crunch_wps simp: crunch_simps)


lemma rai_tcb [wp]:
  "\<lbrace>tcb_at t'\<rbrace> receive_async_ipc t cap is_blocking \<lbrace>\<lambda>rv. tcb_at t'\<rbrace>"
  by (simp add: tcb_at_typ) wp


lemmas transfer_caps_loop_pred_tcb_at[wp] =
    transfer_caps_loop_pres [OF cap_insert_pred_tcb_at]


crunch pred_tcb_at[wp]: do_ipc_transfer "pred_tcb_at proj P t"
  (wp: crunch_wps simp: crunch_simps zipWithM_x_mapM)


lemma setup_caller_cap_makes_simple:
  "\<lbrace>st_tcb_at simple t and K (t \<noteq> t')\<rbrace>
     setup_caller_cap t' t''
   \<lbrace>\<lambda>rv. st_tcb_at simple t\<rbrace>"
  apply (simp add: setup_caller_cap_def)
  apply (wp sts_st_tcb_at_cases | simp)+
  done


lemma si_blk_makes_simple:
  "\<lbrace>st_tcb_at simple t and K (t \<noteq> t')\<rbrace>
     send_ipc True call bdg x t' ep
   \<lbrace>\<lambda>rv. st_tcb_at simple t\<rbrace>"
  apply (simp add: send_ipc_def)
  apply (rule hoare_seq_ext [OF _ get_ep_inv])
  apply (case_tac epa, simp_all)
    apply (wp sts_st_tcb_at_cases)
    apply clarsimp
   apply (wp sts_st_tcb_at_cases)
   apply clarsimp
  apply (rule hoare_gen_asm[simplified])
  apply (rename_tac list)
  apply (case_tac list, simp_all)
  apply (rule hoare_seq_ext [OF _ set_ep_pred_tcb_at])
  apply (rule hoare_seq_ext [OF _ gts_sp])
  apply (case_tac recv_state, simp_all split del: split_if)
  apply (wp sts_st_tcb_at_cases setup_caller_cap_makes_simple
            hoare_drop_imps
            | simp add: if_apply_def2 split del: split_if)+
  done


lemma ep_aep_cap_case_helper:
  "(case x of cap.EndpointCap ref bdg r \<Rightarrow> P ref bdg r
           |  cap.AsyncEndpointCap ref bdg r \<Rightarrow> Q ref bdg r
           |  _ \<Rightarrow> R)
   = (if is_ep_cap x then P (cap_ep_ptr x) (cap_ep_badge x) (cap_rights x) else
      if is_aep_cap x then Q (cap_ep_ptr x) (cap_ep_badge x) (cap_rights x) else
      R)"
  by (cases x, simp_all)


lemma sfi_makes_simple:
  "\<lbrace>st_tcb_at simple t and K (t \<noteq> t')\<rbrace>
     send_fault_ipc t' ft
   \<lbrace>\<lambda>rv. st_tcb_at simple t\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: send_fault_ipc_def Let_def ep_aep_cap_case_helper
             cong: if_cong)
  apply (wp si_blk_makes_simple hoare_drop_imps
            thread_set_no_change_tcb_state
       | simp)+
  done


lemma hf_makes_simple:
  "\<lbrace>st_tcb_at simple t' and K (t \<noteq> t')\<rbrace>
     handle_fault t ft
   \<lbrace>\<lambda>rv. st_tcb_at simple t'\<rbrace>"
  apply (simp add: handle_fault_def)
  apply wp
     apply (simp add: handle_double_fault_def)
     apply (wp sfi_makes_simple sts_st_tcb_at_cases hoare_drop_imps)
  apply clarsimp
  done

crunch pred_tcb_at[wp]: complete_async_ipc "pred_tcb_at proj t p"

lemma ri_makes_simple:
  "\<lbrace>st_tcb_at simple t' and K (t \<noteq> t')\<rbrace>
     receive_ipc t cap is_blocking
   \<lbrace>\<lambda>rv. st_tcb_at simple t'\<rbrace>" (is "\<lbrace>?pre\<rbrace> _ \<lbrace>_\<rbrace>")
  apply (rule hoare_gen_asm)
  apply (simp add: receive_ipc_def split_def)
  apply (case_tac cap, simp_all)
  apply (rule hoare_seq_ext [OF _ get_endpoint_sp])
  apply (rule hoare_seq_ext [OF _ gba_sp])
  apply (rule hoare_seq_ext)
   apply (rename_tac ep I DO x CARE NOT)
   apply (rule_tac R="ko_at (Endpoint x) ep and ?pre" in hoare_vcg_split_if)
    apply (wp complete_async_ipc_invs)
   apply (case_tac x, simp_all)
     apply (rule hoare_pre, wpc)
       apply (wp sts_st_tcb_at_cases, simp)
      apply (simp add: do_nbwait_failed_transfer_def, wp)
     apply clarsimp
    apply (rule hoare_seq_ext [OF _ assert_sp])
    apply (rule hoare_seq_ext [where B="\<lambda>s. st_tcb_at simple t'"])
     apply (rule hoare_seq_ext [OF _ gts_sp])
     apply (rule hoare_pre)
      apply (wp setup_caller_cap_makes_simple sts_st_tcb_at_cases
                hoare_vcg_all_lift hoare_vcg_const_imp_lift
                hoare_drop_imps
           | wpc | simp)+
     apply (fastforce simp: pred_tcb_at_def obj_at_def)
    apply (wp, simp)
   apply (wp sts_st_tcb_at_cases | rule hoare_pre, wpc | simp add: do_nbwait_failed_transfer_def)+
   apply (wp get_aep_wp | wpc | simp)+
  done


lemma rai_makes_simple:
  "\<lbrace>st_tcb_at simple t' and K (t \<noteq> t')\<rbrace>
     receive_async_ipc t cap is_blocking
   \<lbrace>\<lambda>rv. st_tcb_at simple t'\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: receive_async_ipc_def)
  apply (rule hoare_pre)
   by (wp get_aep_wp sts_st_tcb_at_cases | wpc | simp add: do_nbwait_failed_transfer_def)+


lemma thread_set_Pmdb:
  "\<lbrace>\<lambda>s. P (cdt s)\<rbrace> thread_set f t \<lbrace>\<lambda>rv s. P (cdt s)\<rbrace>"
  apply (simp add: thread_set_def)
  apply (wp set_object_Pmdb)
  apply simp
  done


end
