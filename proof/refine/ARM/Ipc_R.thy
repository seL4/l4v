(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Ipc_R
imports Finalise_R Reply_R
begin

context begin interpretation Arch . (*FIXME: arch_split*)

lemmas lookup_slot_wrapper_defs'[simp] =
   lookupSourceSlot_def lookupTargetSlot_def lookupPivotSlot_def

lemma get_mi_corres: "corres ((=) \<circ> message_info_map)
                      (tcb_at t) (tcb_at' t)
                      (get_message_info t) (getMessageInfo t)"
  apply (rule corres_guard_imp)
    apply (unfold get_message_info_def getMessageInfo_def fun_app_def)
    apply (simp add: ARM_H.msgInfoRegister_def
             ARM.msgInfoRegister_def ARM_A.msg_info_register_def)
    apply (rule corres_split_eqr [OF _ user_getreg_corres])
       apply (rule corres_trivial, simp add: message_info_from_data_eqv)
      apply (wp | simp)+
  done


lemma get_mi_inv'[wp]: "\<lbrace>I\<rbrace> getMessageInfo a \<lbrace>\<lambda>x. I\<rbrace>"
  by (simp add: getMessageInfo_def, wp)

definition
  "get_send_cap_relation rv rv' \<equiv>
   (case rv of Some (c, cptr) \<Rightarrow> (\<exists>c' cptr'. rv' = Some (c', cptr') \<and>
                                            cte_map cptr = cptr' \<and>
                                            cap_relation c c')
             | None \<Rightarrow> rv' = None)"

lemma cap_relation_mask:
  "\<lbrakk> cap_relation c c'; msk' = rights_mask_map msk \<rbrakk> \<Longrightarrow>
  cap_relation (mask_cap msk c) (maskCapRights msk' c')"
  by simp

lemma lsfco_cte_at':
  "\<lbrace>valid_objs' and valid_cap' cap\<rbrace>
  lookupSlotForCNodeOp f cap idx depth
  \<lbrace>\<lambda>rv. cte_at' rv\<rbrace>, -"
  apply (simp add: lookupSlotForCNodeOp_def)
  apply (rule conjI)
   prefer 2
   apply clarsimp
   apply (wp)
  apply (clarsimp simp: split_def unlessE_def
             split del: if_split)
  apply (wp hoare_drop_imps throwE_R)
  done

declare unifyFailure_wp [wp]

(* FIXME: move *)
lemma unifyFailure_wp_E [wp]:
  "\<lbrace>P\<rbrace> f -, \<lbrace>\<lambda>_. E\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> unifyFailure f -, \<lbrace>\<lambda>_. E\<rbrace>"
  unfolding validE_E_def
  by (erule unifyFailure_wp)+

(* FIXME: move *)
lemma unifyFailure_wp2 [wp]:
  assumes x: "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. Q\<rbrace>"
  shows      "\<lbrace>P\<rbrace> unifyFailure f \<lbrace>\<lambda>_. Q\<rbrace>"
  by (wp x, simp)

definition
  ct_relation :: "captransfer \<Rightarrow> cap_transfer \<Rightarrow> bool"
where
 "ct_relation ct ct' \<equiv>
    ct_receive_root ct = to_bl (ctReceiveRoot ct')
  \<and> ct_receive_index ct = to_bl (ctReceiveIndex ct')
  \<and> ctReceiveDepth ct' = unat (ct_receive_depth ct)"

(* MOVE *)
lemma valid_ipc_buffer_ptr_aligned_2:
  "\<lbrakk>valid_ipc_buffer_ptr' a s;  is_aligned y 2 \<rbrakk> \<Longrightarrow> is_aligned (a + y) 2"
  unfolding valid_ipc_buffer_ptr'_def
  apply clarsimp
  apply (erule (1) aligned_add_aligned)
  apply (simp add: msg_align_bits)
  done

(* MOVE *)
lemma valid_ipc_buffer_ptr'D2:
  "\<lbrakk>valid_ipc_buffer_ptr' a s; y < max_ipc_words * 4; is_aligned y 2\<rbrakk> \<Longrightarrow> typ_at' UserDataT (a + y && ~~ mask pageBits) s"
  unfolding valid_ipc_buffer_ptr'_def
  apply clarsimp
  apply (subgoal_tac "(a + y) && ~~ mask pageBits = a  && ~~ mask pageBits")
   apply simp
  apply (rule mask_out_first_mask_some [where n = msg_align_bits])
   apply (erule is_aligned_add_helper [THEN conjunct2])
   apply (erule order_less_le_trans)
   apply (simp add: msg_align_bits max_ipc_words )
  apply simp
  done

lemma load_ct_corres:
  "corres ct_relation \<top> (valid_ipc_buffer_ptr' buffer) (load_cap_transfer buffer) (loadCapTransfer buffer)"
  apply (simp add: load_cap_transfer_def loadCapTransfer_def
                   captransfer_from_words_def
                   capTransferDataSize_def capTransferFromWords_def
                   msgExtraCapBits_def word_size add.commute add.left_commute
                   msg_max_length_def msg_max_extra_caps_def word_size_def
                   msgMaxLength_def msgMaxExtraCaps_def msgLengthBits_def wordSize_def wordBits_def
              del: upt.simps)
  apply (rule corres_guard_imp)
    apply (rule corres_split_deprecated [OF _ load_word_corres])
      apply (rule corres_split_deprecated [OF _ load_word_corres])
        apply (rule corres_split_deprecated [OF _ load_word_corres])
          apply (rule_tac P=\<top> and P'=\<top> in corres_inst)
          apply (clarsimp simp: ct_relation_def)
         apply (wp no_irq_loadWord)+
   apply simp
  apply (simp add: conj_comms)
  apply safe
       apply (erule valid_ipc_buffer_ptr_aligned_2, simp add: is_aligned_def)+
    apply (erule valid_ipc_buffer_ptr'D2, simp add: max_ipc_words, simp add: is_aligned_def)+
  done

lemma get_recv_slot_corres:
  "corres (\<lambda>xs ys. ys = map cte_map xs)
    (tcb_at receiver and valid_objs and pspace_aligned)
    (tcb_at' receiver and valid_objs' and pspace_aligned' and pspace_distinct' and
     case_option \<top> valid_ipc_buffer_ptr' recv_buf)
    (get_receive_slots receiver recv_buf)
    (getReceiveSlots receiver recv_buf)"
  apply (cases recv_buf)
   apply (simp add: getReceiveSlots_def)
  apply (simp add: getReceiveSlots_def split_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_deprecated [OF _ load_ct_corres])
      apply (rule corres_empty_on_failure)
      apply (rule corres_splitEE)
         prefer 2
         apply (rule corres_unify_failure)
          apply (rule lookup_cap_corres)
          apply (simp add: ct_relation_def)
         apply simp
        apply (rule corres_splitEE)
           prefer 2
           apply (rule corres_unify_failure)
            apply (simp add: ct_relation_def)
            apply (erule lsfc_corres [OF _ refl])
           apply simp
          apply (simp add: split_def liftE_bindE unlessE_whenE)
          apply (rule corres_split_deprecated [OF _ get_cap_corres])
            apply (rule corres_split_norE)
               apply (rule corres_trivial, simp add: returnOk_def)
              apply (rule corres_whenE)
                apply (case_tac cap, auto)[1]
               apply (rule corres_trivial, simp)
              apply simp
             apply (wp lookup_cap_valid lookup_cap_valid' lsfco_cte_at | simp)+
  done

lemma get_recv_slot_inv'[wp]:
  "\<lbrace> P \<rbrace> getReceiveSlots receiver buf \<lbrace>\<lambda>rv'. P \<rbrace>"
  apply (case_tac buf)
   apply (simp add: getReceiveSlots_def)
  apply (simp add: getReceiveSlots_def
                   split_def unlessE_def)
  apply (wp | simp)+
  done

lemma get_rs_cte_at'[wp]:
  "\<lbrace>\<top>\<rbrace>
   getReceiveSlots receiver recv_buf
   \<lbrace>\<lambda>rv s. \<forall>x \<in> set rv. cte_wp_at' (\<lambda>c. cteCap c = capability.NullCap) x s\<rbrace>"
  apply (cases recv_buf)
   apply (simp add: getReceiveSlots_def)
   apply (wp,simp)
  apply (clarsimp simp add: getReceiveSlots_def
                            split_def whenE_def unlessE_whenE)
  apply wp
     apply simp
     apply (rule getCTE_wp)
    apply (simp add: cte_wp_at_ctes_of cong: conj_cong)
    apply wp+
  apply simp
  done

lemma get_rs_real_cte_at'[wp]:
  "\<lbrace>valid_objs'\<rbrace>
   getReceiveSlots receiver recv_buf
   \<lbrace>\<lambda>rv s. \<forall>x \<in> set rv. real_cte_at' x s\<rbrace>"
  apply (cases recv_buf)
   apply (simp add: getReceiveSlots_def)
   apply (wp,simp)
  apply (clarsimp simp add: getReceiveSlots_def
                            split_def whenE_def unlessE_whenE)
  apply wp
     apply simp
     apply (wp hoare_drop_imps)[1]
    apply simp
    apply (wp lookup_cap_valid')+
  apply simp
  done

declare word_div_1 [simp]
declare word_minus_one_le [simp]
declare word32_minus_one_le [simp]

lemma load_word_offs_corres':
  "\<lbrakk> y < unat max_ipc_words; y' = of_nat y * 4 \<rbrakk> \<Longrightarrow>
  corres (=) \<top> (valid_ipc_buffer_ptr' a) (load_word_offs a y) (loadWordUser (a + y'))"
  apply simp
  apply (erule load_word_offs_corres)
  done

declare loadWordUser_inv [wp]

lemma getExtraCptrs_inv[wp]:
  "\<lbrace>P\<rbrace> getExtraCPtrs buf mi \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (cases mi, cases buf, simp_all add: getExtraCPtrs_def)
  apply (wp dmo_inv' mapM_wp' loadWord_inv)
  done

lemma badge_derived_mask [simp]:
  "badge_derived' (maskCapRights R c) c' = badge_derived' c c'"
  by (simp add: badge_derived'_def)

declare derived'_not_Null [simp]

lemma maskCapRights_vsCapRef[simp]:
  "vsCapRef (maskCapRights msk cap) = vsCapRef cap"
  unfolding vsCapRef_def
  apply (cases cap, simp_all add: maskCapRights_def isCap_simps Let_def)
  apply (rename_tac arch_capability)
  apply (case_tac arch_capability;
         simp add: maskCapRights_def ARM_H.maskCapRights_def isCap_simps Let_def)
  done

lemma corres_set_extra_badge:
  "b' = b \<Longrightarrow>
  corres dc (in_user_frame buffer)
         (valid_ipc_buffer_ptr' buffer and
          (\<lambda>_. msg_max_length + 2 + n < unat max_ipc_words))
         (set_extra_badge buffer b n) (setExtraBadge buffer b' n)"
  apply (rule corres_gen_asm2)
  apply (drule store_word_offs_corres [where a=buffer and w=b])
  apply (simp add: set_extra_badge_def setExtraBadge_def buffer_cptr_index_def
                   bufferCPtrOffset_def Let_def)
  apply (simp add: word_size word_size_def wordSize_def wordBits_def
                   bufferCPtrOffset_def buffer_cptr_index_def msgMaxLength_def
                   msg_max_length_def msgLengthBits_def store_word_offs_def
                   add.commute add.left_commute)
  done

end

crunches setExtraBadge
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n n p s)"
  and valid_pspace'[wp]: valid_pspace'
  and cte_wp_at'[wp]: "cte_wp_at' P p"
  and ipc_buffer'[wp]: "valid_ipc_buffer_ptr' buffer"

global_interpretation setExtraBadge: typ_at_all_props' "setExtraBadge buffer badge n"
  by typ_at_props'

crunch inv'[wp]: getExtraCPtr P (wp: dmo_inv' loadWord_inv)

lemmas unifyFailure_discard2
    = corres_injection[OF id_injection unifyFailure_injection, simplified]

lemma deriveCap_not_null:
  "\<lbrace>\<top>\<rbrace> deriveCap slot cap \<lbrace>\<lambda>rv. K (rv \<noteq> NullCap \<longrightarrow> cap \<noteq> NullCap)\<rbrace>,-"
  apply (simp add: deriveCap_def split del: if_split)
  apply (case_tac cap)
          apply (simp_all add: Let_def isCap_simps)
  apply wp
  apply simp
  done

lemma deriveCap_derived_foo:
  "\<lbrace>\<lambda>s. \<forall>cap'. (cte_wp_at' (\<lambda>cte. badge_derived' cap (cteCap cte)
                     \<and> capASID cap = capASID (cteCap cte) \<and> cap_asid_base' cap = cap_asid_base' (cteCap cte)
                     \<and> cap_vptr' cap = cap_vptr' (cteCap cte)) slot s
              \<and> valid_objs' s \<and> cap' \<noteq> NullCap \<longrightarrow> cte_wp_at' (is_derived' (ctes_of s) slot cap' \<circ> cteCap) slot s)
        \<and> (cte_wp_at' (untyped_derived_eq cap \<circ> cteCap) slot s
            \<longrightarrow> cte_wp_at' (untyped_derived_eq cap' \<circ> cteCap) slot s)
        \<and> (s \<turnstile>' cap \<longrightarrow> s \<turnstile>' cap') \<and> (cap' \<noteq> NullCap \<longrightarrow> cap \<noteq> NullCap) \<longrightarrow> Q cap' s\<rbrace>
    deriveCap slot cap \<lbrace>Q\<rbrace>,-"
  using deriveCap_derived[where slot=slot and c'=cap] deriveCap_valid[where slot=slot and c=cap]
        deriveCap_untyped_derived[where slot=slot and c'=cap] deriveCap_not_null[where slot=slot and cap=cap]
  apply (clarsimp simp: validE_R_def validE_def valid_def split: sum.split)
  apply (frule in_inv_by_hoareD[OF deriveCap_inv])
  apply (clarsimp simp: o_def)
  apply (drule spec, erule mp)
  apply safe
     apply fastforce
    apply (drule spec, drule(1) mp)
    apply fastforce
   apply (drule spec, drule(1) mp)
   apply fastforce
  apply (drule spec, drule(1) bspec, simp)
  done

lemma valid_mdb_untyped_incD':
  "valid_mdb' s \<Longrightarrow> untyped_inc' (ctes_of s)"
  by (simp add: valid_mdb'_def valid_mdb_ctes_def)

lemma cteInsert_cte_wp_at:
  "\<lbrace>\<lambda>s. cte_wp_at' (\<lambda>c. is_derived' (ctes_of s) src cap (cteCap c)) src s
       \<and> valid_mdb' s \<and> valid_objs' s
       \<and> (if p = dest then P cap
            else cte_wp_at' (\<lambda>c. P (maskedAsFull (cteCap c) cap)) p s)\<rbrace>
    cteInsert cap src dest
   \<lbrace>\<lambda>uu. cte_wp_at' (\<lambda>c. P (cteCap c)) p\<rbrace>"
  apply (simp add: cteInsert_def)
  apply (wp updateMDB_weak_cte_wp_at updateCap_cte_wp_at_cases getCTE_wp static_imp_wp
         | clarsimp simp: comp_def
         | unfold setUntypedCapAsFull_def)+
  apply (drule cte_at_cte_wp_atD)
  apply (elim exE)
  apply (rule_tac x=cte in exI)
  apply clarsimp
  apply (drule cte_at_cte_wp_atD)
  apply (elim exE)
  apply (rule_tac x=ctea in exI)
  apply clarsimp
  apply (cases "p=dest")
   apply (clarsimp simp: cte_wp_at'_def)
  apply (cases "p=src")
   apply clarsimp
   apply (intro conjI impI)
    apply ((clarsimp simp: cte_wp_at'_def maskedAsFull_def split: if_split_asm)+)[2]
  apply clarsimp
  apply (rule conjI)
   apply (clarsimp simp: maskedAsFull_def cte_wp_at_ctes_of split:if_split_asm)
   apply (erule disjE) prefer 2 apply simp
   apply (clarsimp simp: is_derived'_def isCap_simps)
   apply (drule valid_mdb_untyped_incD')
   apply (case_tac cte, case_tac cteb, clarsimp)
   apply (drule untyped_incD', (simp add: isCap_simps)+)
   apply (frule(1) ctes_of_valid'[where p = p])
   apply (clarsimp simp:valid_cap'_def capAligned_def split:if_splits)
    apply (drule_tac y ="of_nat fb"  in word_plus_mono_right[OF _  is_aligned_no_overflow',rotated])
      apply simp+
     apply (rule word_of_nat_less)
     apply simp
    apply (simp add:p_assoc_help)
   apply (simp add: max_free_index_def)
  apply (clarsimp simp: maskedAsFull_def is_derived'_def badge_derived'_def
                        isCap_simps capMasterCap_def cte_wp_at_ctes_of
                  split: if_split_asm capability.splits)
  done

lemma cteInsert_weak_cte_wp_at3:
  assumes imp:"\<And>c. P c \<Longrightarrow> \<not> isUntypedCap c"
  shows " \<lbrace>\<lambda>s. if p = dest then P cap
            else cte_wp_at' (\<lambda>c. P (cteCap c)) p s\<rbrace>
    cteInsert cap src dest
   \<lbrace>\<lambda>uu. cte_wp_at' (\<lambda>c. P (cteCap c)) p\<rbrace>"
  by (wp updateMDB_weak_cte_wp_at updateCap_cte_wp_at_cases getCTE_wp' static_imp_wp
         | clarsimp simp: comp_def cteInsert_def
         | unfold setUntypedCapAsFull_def
         | auto simp: cte_wp_at'_def dest!: imp)+

lemma maskedAsFull_null_cap[simp]:
  "(maskedAsFull x y = capability.NullCap) = (x = capability.NullCap)"
  "(capability.NullCap  = maskedAsFull x y) = (x = capability.NullCap)"
  by (case_tac x, auto simp:maskedAsFull_def isCap_simps )

context begin interpretation Arch . (*FIXME: arch_split*)

lemma maskCapRights_eq_null:
  "(RetypeDecls_H.maskCapRights r xa = capability.NullCap) =
   (xa = capability.NullCap)"
  apply (cases xa; simp add: maskCapRights_def isCap_simps)
  apply (rename_tac arch_capability)
  apply (case_tac arch_capability)
      apply (simp_all add: ARM_H.maskCapRights_def isCap_simps)
  done

lemma cte_refs'_maskedAsFull[simp]:
  "cte_refs' (maskedAsFull a b) = cte_refs' a"
  apply (rule ext)+
  apply (case_tac a)
   apply (clarsimp simp:maskedAsFull_def isCap_simps)+
 done

lemma tc_loop_corres:
  "\<lbrakk> list_all2 (\<lambda>(cap, slot) (cap', slot'). cap_relation cap cap'
             \<and> slot' = cte_map slot) caps caps';
      mi' = message_info_map mi \<rbrakk> \<Longrightarrow>
   corres ((=) \<circ> message_info_map)
      (\<lambda>s. valid_objs s \<and> pspace_aligned s \<and> pspace_distinct s \<and> valid_mdb s
         \<and> valid_list s
         \<and> (case ep of Some x \<Rightarrow> ep_at x s | _ \<Rightarrow> True)
         \<and> (\<forall>x \<in> set slots. cte_wp_at (\<lambda>cap. cap = cap.NullCap) x s \<and>
                             real_cte_at x s)
         \<and> (\<forall>(cap, slot) \<in> set caps. valid_cap cap s \<and>
                    cte_wp_at (\<lambda>cp'. (cap \<noteq> cap.NullCap \<longrightarrow> cp'\<noteq>cap \<longrightarrow> cp' = masked_as_full cap cap )) slot s )
         \<and> distinct slots
         \<and> in_user_frame buffer s)
      (\<lambda>s. valid_pspace' s
         \<and> (case ep of Some x \<Rightarrow> ep_at' x s | _ \<Rightarrow> True)
         \<and> (\<forall>x \<in> set (map cte_map slots).
             cte_wp_at' (\<lambda>cte. cteCap cte = NullCap) x s
                   \<and> real_cte_at' x s)
         \<and> distinct (map cte_map slots)
         \<and> valid_ipc_buffer_ptr' buffer s
         \<and> (\<forall>(cap, slot) \<in> set caps'. valid_cap' cap s \<and>
                    cte_wp_at' (\<lambda>cte. cap \<noteq> NullCap \<longrightarrow> cteCap cte \<noteq> cap \<longrightarrow> cteCap cte = maskedAsFull cap cap) slot s)
         \<and> 2 + msg_max_length + n + length caps' < unat max_ipc_words)
      (transfer_caps_loop ep buffer n caps slots mi)
      (transferCapsToSlots ep buffer n caps'
         (map cte_map slots) mi')"
  (is "\<lbrakk> list_all2 ?P caps caps'; ?v \<rbrakk> \<Longrightarrow> ?corres")
proof (induct caps caps' arbitrary: slots n mi mi' rule: list_all2_induct)
  case Nil
  show ?case using Nil.prems by (case_tac mi, simp)
next
  case (Cons x xs y ys slots n mi mi')
  note if_weak_cong[cong] if_cong [cong del]
  assume P: "?P x y"
  show ?case using Cons.prems P
    apply (clarsimp split del: if_split)
    apply (simp add: Let_def split_def word_size liftE_bindE
                     word_bits_conv[symmetric] split del: if_split)
    apply (rule corres_const_on_failure)
    apply (simp add: dc_def[symmetric] split del: if_split)
    apply (rule corres_guard_imp)
      apply (rule corres_if3)
        apply (case_tac "fst x", auto simp add: isCap_simps)[1]
       apply (rule corres_split_deprecated [OF _ corres_set_extra_badge])
          apply (drule conjunct1)
          apply simp
          apply (rule corres_rel_imp, rule Cons.hyps, simp_all)[1]
          apply (case_tac mi, simp)
         apply (clarsimp simp: is_cap_simps)
        apply (simp add: split_def)
        apply (wp hoare_vcg_const_Ball_lift)
       apply (subgoal_tac "obj_ref_of (fst x) = capEPPtr (fst y)")
        prefer 2
        apply (clarsimp simp: is_cap_simps)
       apply (simp add: split_def)
       apply (wp hoare_vcg_const_Ball_lift)
      apply (rule_tac P="slots = []" and Q="slots \<noteq> []" in corres_disj_division)
        apply simp
       apply (rule corres_trivial, simp add: returnOk_def)
       apply (case_tac mi, simp)
      apply (simp add: list_case_If2 split del: if_split)
      apply (rule corres_splitEE)
         prefer 2
         apply (rule unifyFailure_discard2)
          apply (case_tac mi, clarsimp)
         apply (rule derive_cap_corres)
          apply (simp add: remove_rights_def)
         apply clarsimp
        apply (rule corres_split_norE)
           apply (simp add: liftE_bindE)
           apply (rule corres_split_nor)
              prefer 2
              apply (rule cins_corres, simp_all add: hd_map)[1]
             apply (simp add: tl_map)
             apply (rule corres_rel_imp, rule Cons.hyps, simp_all)[1]
            apply (wp valid_case_option_post_wp hoare_vcg_const_Ball_lift
                        hoare_vcg_const_Ball_lift cap_insert_weak_cte_wp_at)
             apply (wp hoare_vcg_const_Ball_lift | simp add:split_def del: imp_disj1)+
             apply (wp cap_insert_cte_wp_at)
           apply (wp valid_case_option_post_wp hoare_vcg_const_Ball_lift
                     cteInsert_valid_pspace
                     | simp add: split_def)+
           apply (wp cteInsert_weak_cte_wp_at hoare_valid_ipc_buffer_ptr_typ_at')+
           apply (wp hoare_vcg_const_Ball_lift cteInsert_cte_wp_at  valid_case_option_post_wp
             | simp add:split_def)+
          apply (rule corres_whenE)
            apply (case_tac cap', auto)[1]
           apply (rule corres_trivial, simp)
           apply (case_tac mi, simp)
          apply simp
         apply (unfold whenE_def)
         apply wp+
        apply (clarsimp simp: conj_comms ball_conj_distrib split del: if_split)
        apply (rule_tac Q' ="\<lambda>cap' s. (cap'\<noteq> cap.NullCap \<longrightarrow>
          cte_wp_at (is_derived (cdt s) (a, b) cap') (a, b) s
          \<and> QM s cap')" for QM
          in hoare_post_imp_R)
        prefer 2
         apply clarsimp
         apply assumption
        apply (subst imp_conjR)
        apply (rule hoare_vcg_conj_liftE_R)
        apply (rule derive_cap_is_derived)
       apply (wp derive_cap_is_derived_foo)+
      apply (simp split del: if_split)
      apply (rule_tac Q' ="\<lambda>cap' s. (cap'\<noteq> capability.NullCap \<longrightarrow>
         cte_wp_at' (\<lambda>c. is_derived' (ctes_of s) (cte_map (a, b)) cap' (cteCap c)) (cte_map (a, b)) s
         \<and> QM s cap')" for QM
        in hoare_post_imp_R)
      prefer 2
       apply clarsimp
       apply assumption
      apply (subst imp_conjR)
      apply (rule hoare_vcg_conj_liftE_R)
       apply (rule hoare_post_imp_R[OF deriveCap_derived])
       apply (clarsimp simp:cte_wp_at_ctes_of)
      apply (wp deriveCap_derived_foo)
     apply (clarsimp simp: cte_wp_at_caps_of_state remove_rights_def
                           real_cte_tcb_valid if_apply_def2
                split del: if_split)
     apply (rule conjI, (clarsimp split del: if_split)+)
     apply (clarsimp simp:conj_comms split del:if_split)
     apply (intro conjI allI)
       apply (clarsimp split:if_splits)
       apply (case_tac "cap = fst x",simp+)
      apply (clarsimp simp:masked_as_full_def is_cap_simps cap_master_cap_simps)
    apply (clarsimp split del: if_split)
    apply (intro conjI)
           apply (clarsimp simp:neq_Nil_conv)
        apply (drule hd_in_set)
        apply (drule(1) bspec)
        apply (clarsimp split:if_split_asm)
      apply (fastforce simp:neq_Nil_conv)
      apply (intro ballI conjI)
       apply (clarsimp simp:neq_Nil_conv)
      apply (intro impI)
      apply (drule(1) bspec[OF _ subsetD[rotated]])
       apply (clarsimp simp:neq_Nil_conv)
     apply (clarsimp split:if_splits)
    apply clarsimp
    apply (intro conjI)
     apply (drule(1) bspec,clarsimp)+
    subgoal for \<dots> aa _ _ capa
     by (case_tac "capa = aa"; clarsimp split:if_splits simp:masked_as_full_def is_cap_simps)
   apply (case_tac "isEndpointCap (fst y) \<and> capEPPtr (fst y) = the ep \<and> (\<exists>y. ep = Some y)")
    apply (clarsimp simp:conj_comms split del:if_split)
   apply (subst if_not_P)
    apply clarsimp
   apply (clarsimp simp:valid_pspace'_def cte_wp_at_ctes_of split del:if_split)
   apply (intro conjI)
    apply (case_tac  "cteCap cte = fst y",clarsimp simp: badge_derived'_def)
    apply (clarsimp simp: maskCapRights_eq_null maskedAsFull_def badge_derived'_def isCap_simps
                    split: if_split_asm)
  apply (clarsimp split del: if_split)
  apply (case_tac "fst y = capability.NullCap")
    apply (clarsimp simp: neq_Nil_conv split del: if_split)+
  apply (intro allI impI conjI)
     apply (clarsimp split:if_splits)
    apply (clarsimp simp:image_def)+
   apply (thin_tac "\<forall>x\<in>set ys. Q x" for Q)
   apply (drule(1) bspec)+
   apply clarsimp+
  apply (drule(1) bspec)
  apply (rule conjI)
   apply clarsimp+
  apply (case_tac "cteCap cteb = ab")
   by (clarsimp simp: isCap_simps maskedAsFull_def split:if_splits)+
qed

declare constOnFailure_wp [wp]

lemma transferCapsToSlots_pres1[crunch_rules]:
  assumes x: "\<And>cap src dest. \<lbrace>P\<rbrace> cteInsert cap src dest \<lbrace>\<lambda>rv. P\<rbrace>"
  assumes eb: "\<And>b n. \<lbrace>P\<rbrace> setExtraBadge buffer b n \<lbrace>\<lambda>_. P\<rbrace>"
  shows      "\<lbrace>P\<rbrace> transferCapsToSlots ep buffer n caps slots mi \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (induct caps arbitrary: slots n mi)
   apply simp
  apply (simp add: Let_def split_def whenE_def
             cong: if_cong list.case_cong
             split del: if_split)
  apply (rule hoare_pre)
   apply (wp x eb | assumption | simp split del: if_split | wpc
             | wp (once) hoare_drop_imps)+
  done

lemma cteInsert_cte_cap_to':
  "\<lbrace>ex_cte_cap_to' p and cte_wp_at' (\<lambda>cte. cteCap cte = NullCap) dest\<rbrace>
   cteInsert cap src dest
   \<lbrace>\<lambda>rv. ex_cte_cap_to' p\<rbrace>"
  apply (simp add: ex_cte_cap_to'_def)
  apply (rule hoare_pre)
   apply (rule hoare_use_eq_irq_node' [OF cteInsert_ksInterruptState])
   apply (clarsimp simp:cteInsert_def)
    apply (wp hoare_vcg_ex_lift  updateMDB_weak_cte_wp_at updateCap_cte_wp_at_cases
      setUntypedCapAsFull_cte_wp_at getCTE_wp static_imp_wp)
   apply (clarsimp simp:cte_wp_at_ctes_of)
   apply (rule_tac x = "cref" in exI)
     apply (rule conjI)
     apply clarsimp+
  done

declare maskCapRights_eq_null[simp]

crunch ex_cte_cap_wp_to' [wp]: setExtraBadge "ex_cte_cap_wp_to' P p"
  (rule: ex_cte_cap_to'_pres)

crunch valid_objs' [wp]: setExtraBadge valid_objs'
crunch aligned' [wp]: setExtraBadge pspace_aligned'
crunch distinct' [wp]: setExtraBadge pspace_distinct'

lemma cteInsert_assume_Null:
  "\<lbrace>P\<rbrace> cteInsert cap src dest \<lbrace>Q\<rbrace> \<Longrightarrow>
   \<lbrace>\<lambda>s. cte_wp_at' (\<lambda>cte. cteCap cte = NullCap) dest s \<longrightarrow> P s\<rbrace>
   cteInsert cap src dest
   \<lbrace>Q\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (erule impCE)
   apply (simp add: cteInsert_def)
   apply (rule hoare_seq_ext[OF _ getCTE_sp])+
   apply (rule hoare_name_pre_state)
   apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (erule hoare_pre(1))
  apply simp
  done

crunch mdb'[wp]: setExtraBadge valid_mdb'

lemma cteInsert_weak_cte_wp_at2:
  assumes weak:"\<And>c cap. P (maskedAsFull c cap) = P c"
  shows
    "\<lbrace>\<lambda>s. if p = dest then P cap else cte_wp_at' (\<lambda>c. P (cteCap c)) p s\<rbrace>
     cteInsert cap src dest
     \<lbrace>\<lambda>uu. cte_wp_at' (\<lambda>c. P (cteCap c)) p\<rbrace>"
  apply (rule hoare_pre)
   apply (rule hoare_use_eq_irq_node' [OF cteInsert_ksInterruptState])
   apply (clarsimp simp:cteInsert_def)
    apply (wp hoare_vcg_ex_lift  updateMDB_weak_cte_wp_at updateCap_cte_wp_at_cases
      setUntypedCapAsFull_cte_wp_at getCTE_wp static_imp_wp)
   apply (clarsimp simp:cte_wp_at_ctes_of weak)
   apply auto
  done

lemma transferCapsToSlots_presM:
  assumes x: "\<And>cap src dest. \<lbrace>\<lambda>s. P s \<and> (emx \<longrightarrow> cte_wp_at' (\<lambda>cte. cteCap cte = NullCap) dest s \<and> ex_cte_cap_to' dest s)
                                       \<and> (vo \<longrightarrow> valid_objs' s \<and> valid_cap' cap s \<and> real_cte_at' dest s)
                                       \<and> (drv \<longrightarrow> cte_wp_at' (is_derived' (ctes_of s) src cap \<circ> cteCap) src s
                                               \<and> cte_wp_at' (untyped_derived_eq cap o cteCap) src s
                                               \<and> valid_mdb' s)
                                       \<and> (pad \<longrightarrow> pspace_aligned' s \<and> pspace_distinct' s)\<rbrace>
                                           cteInsert cap src dest \<lbrace>\<lambda>rv. P\<rbrace>"
  assumes eb: "\<And>b n. \<lbrace>P\<rbrace> setExtraBadge buffer b n \<lbrace>\<lambda>_. P\<rbrace>"
  shows      "\<lbrace>\<lambda>s. P s
                 \<and> (emx \<longrightarrow> (\<forall>x \<in> set slots. ex_cte_cap_to' x s \<and> cte_wp_at' (\<lambda>cte. cteCap cte = NullCap) x s) \<and> distinct slots)
                 \<and> (vo \<longrightarrow> valid_objs' s \<and> (\<forall>x \<in> set slots. real_cte_at' x s \<and> cte_wp_at' (\<lambda>cte. cteCap cte = NullCap) x s)
                           \<and> (\<forall>x \<in> set caps. s \<turnstile>' fst x ) \<and> distinct slots)
                 \<and> (pad \<longrightarrow> pspace_aligned' s \<and> pspace_distinct' s)
                 \<and> (drv \<longrightarrow> vo \<and> pspace_aligned' s \<and> pspace_distinct' s \<and> valid_mdb' s
                         \<and> length slots \<le> 1
                         \<and> (\<forall>x \<in> set caps. s \<turnstile>' fst x \<and> (slots \<noteq> []
                              \<longrightarrow> cte_wp_at' (\<lambda>cte. fst x \<noteq> NullCap \<longrightarrow> cteCap cte = fst x) (snd x) s)))\<rbrace>
                 transferCapsToSlots ep buffer n caps slots mi
              \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (induct caps arbitrary: slots n mi)
   apply (simp, wp, simp)
  apply (simp add: Let_def split_def whenE_def
             cong: if_cong list.case_cong split del: if_split)
  apply (rule hoare_pre)
   apply (wp eb hoare_vcg_const_Ball_lift hoare_vcg_const_imp_lift
           | assumption | wpc)+
     apply (rule cteInsert_assume_Null)
     apply (wp x hoare_vcg_const_Ball_lift cteInsert_cte_cap_to' static_imp_wp)
       apply (rule cteInsert_weak_cte_wp_at2,clarsimp)
      apply (wp hoare_vcg_const_Ball_lift static_imp_wp)+
       apply (rule cteInsert_weak_cte_wp_at2,clarsimp)
      apply (wp hoare_vcg_const_Ball_lift cteInsert_cte_wp_at static_imp_wp
          deriveCap_derived_foo)+
  apply (thin_tac "\<And>slots. PROP P slots" for P)
  apply (clarsimp simp: cte_wp_at_ctes_of remove_rights_def
                        real_cte_tcb_valid if_apply_def2
             split del: if_split)
  apply (rule conjI)
   apply (clarsimp simp:cte_wp_at_ctes_of untyped_derived_eq_def)
  apply (intro conjI allI)
     apply (clarsimp simp:Fun.comp_def cte_wp_at_ctes_of)+
  apply (clarsimp simp:valid_capAligned)
  done

lemmas transferCapsToSlots_pres2
    = transferCapsToSlots_presM[where vo=False and emx=True
                                  and drv=False and pad=False, simplified]

lemma transferCapsToSlots_aligned'[wp]:
  "\<lbrace>pspace_aligned'\<rbrace>
     transferCapsToSlots ep buffer n caps slots mi
   \<lbrace>\<lambda>rv. pspace_aligned'\<rbrace>"
  by (wp transferCapsToSlots_pres1)

lemma transferCapsToSlots_distinct'[wp]:
  "\<lbrace>pspace_distinct'\<rbrace>
     transferCapsToSlots ep buffer n caps slots mi
   \<lbrace>\<lambda>rv. pspace_distinct'\<rbrace>"
  by (wp transferCapsToSlots_pres1)

lemma transferCapsToSlots_typ_at'[wp]:
   "\<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace>
      transferCapsToSlots ep buffer n caps slots mi
    \<lbrace>\<lambda>rv s. P (typ_at' T p s)\<rbrace>"
  by (wp transferCapsToSlots_pres1 setExtraBadge_typ_at')

lemma transferCapsToSlots_valid_objs[wp]:
  "\<lbrace>valid_objs' and valid_mdb' and (\<lambda>s. \<forall>x \<in> set slots. real_cte_at' x s \<and> cte_wp_at' (\<lambda>cte. cteCap cte = capability.NullCap) x s)
       and (\<lambda>s. \<forall>x \<in> set caps. s \<turnstile>' fst x) and K(distinct slots)\<rbrace>
       transferCapsToSlots ep buffer n caps slots mi
   \<lbrace>\<lambda>rv. valid_objs'\<rbrace>"
  apply (rule hoare_pre)
   apply (rule transferCapsToSlots_presM[where vo=True and emx=False and drv=False and pad=False])
    apply (wp | simp)+
  done

abbreviation(input)
  "transferCaps_srcs caps s \<equiv> \<forall>x\<in>set caps. cte_wp_at' (\<lambda>cte. fst x \<noteq> NullCap \<longrightarrow> cteCap cte = fst x) (snd x) s"

lemma transferCapsToSlots_mdb[wp]:
  "\<lbrace>\<lambda>s. valid_pspace' s \<and> distinct slots
          \<and> length slots \<le> 1
          \<and> (\<forall>x \<in> set slots. ex_cte_cap_to' x s \<and> cte_wp_at' (\<lambda>cte. cteCap cte = capability.NullCap) x s)
          \<and> (\<forall>x \<in> set slots. real_cte_at' x s)
          \<and> transferCaps_srcs caps s\<rbrace>
    transferCapsToSlots ep buffer n caps slots mi
   \<lbrace>\<lambda>rv. valid_mdb'\<rbrace>"
  apply (wp transferCapsToSlots_presM[where drv=True and vo=True and emx=True and pad=True])
    apply clarsimp
    apply (frule valid_capAligned)
    apply (clarsimp simp: cte_wp_at_ctes_of is_derived'_def badge_derived'_def)
   apply wp
  apply (clarsimp simp: valid_pspace'_def)
  apply (clarsimp simp:cte_wp_at_ctes_of)
  apply (drule(1) bspec,clarify)
  apply (case_tac cte)
  apply (clarsimp dest!:ctes_of_valid_cap' split:if_splits)
  apply (fastforce simp:valid_cap'_def)
  done

crunch no_0' [wp]: setExtraBadge no_0_obj'

lemma transferCapsToSlots_no_0_obj' [wp]:
  "\<lbrace>no_0_obj'\<rbrace> transferCapsToSlots ep buffer n caps slots mi \<lbrace>\<lambda>rv. no_0_obj'\<rbrace>"
  by (wp transferCapsToSlots_pres1)

crunches transferCapsToSlots
  for reply_projs[wp]: "\<lambda>s. P (replyNexts_of s) (replyPrevs_of s) (replyTCBs_of s) (replySCs_of s)"
  and pred_tcb_at'[wp]: "pred_tcb_at' proj P p"
  and valid_replies' [wp]: valid_replies'

lemma transferCapsToSlots_vp[wp]:
  "\<lbrace>\<lambda>s. valid_pspace' s \<and> distinct slots
          \<and> length slots \<le> 1
          \<and> (\<forall>x \<in> set slots. ex_cte_cap_to' x s \<and> cte_wp_at' (\<lambda>cte. cteCap cte = capability.NullCap) x s)
          \<and> (\<forall>x \<in> set slots. real_cte_at' x s)
          \<and> transferCaps_srcs caps s\<rbrace>
    transferCapsToSlots ep buffer n caps slots mi
   \<lbrace>\<lambda>rv. valid_pspace'\<rbrace>"
  apply (simp add: valid_pspace'_def | wp)+
  apply (fastforce simp: cte_wp_at_ctes_of dest: ctes_of_valid')
  done

crunches setExtraBadge, doIPCTransfer
  for sch_act [wp]: "\<lambda>s. P (ksSchedulerAction s)"
  (wp: crunch_wps mapME_wp' simp: zipWithM_x_mapM)

crunches setExtraBadge
  for ksCurThread[wp]: "\<lambda>s. P (ksCurThread s)"
  and ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  and obj_at' [wp]: "\<lambda>s. P' (obj_at' P p s)"
  and queues [wp]: "\<lambda>s. P (ksReadyQueues s)"
  and queuesL1 [wp]: "\<lambda>s. P (ksReadyQueuesL1Bitmap s)"
  and queuesL2 [wp]: "\<lambda>s. P (ksReadyQueuesL2Bitmap s)"

lemma tcts_sch_act[wp]:
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>
     transferCapsToSlots ep buffer n caps slots mi
   \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  by (wp sch_act_wf_lift tcb_in_cur_domain'_lift transferCapsToSlots_pres1)

lemma tcts_vq[wp]:
  "\<lbrace>Invariants_H.valid_queues\<rbrace> transferCapsToSlots ep buffer n caps slots mi \<lbrace>\<lambda>rv. Invariants_H.valid_queues\<rbrace>"
  by (wp valid_queues_lift transferCapsToSlots_pres1)

lemma tcts_vq'[wp]:
  "\<lbrace>valid_queues'\<rbrace> transferCapsToSlots ep buffer n caps slots mi \<lbrace>\<lambda>rv. valid_queues'\<rbrace>"
  by (wp valid_queues_lift' transferCapsToSlots_pres1)

crunch state_refs_of' [wp]: setExtraBadge "\<lambda>s. P (state_refs_of' s)"

lemma tcts_state_refs_of'[wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of' s)\<rbrace>
     transferCapsToSlots ep buffer n caps slots mi
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  by (wp transferCapsToSlots_pres1)

crunch if_live' [wp]: setExtraBadge if_live_then_nonz_cap'

lemma tcts_iflive[wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s \<and> distinct slots \<and>
         (\<forall>x\<in>set slots.
             ex_cte_cap_to' x s \<and> cte_wp_at' (\<lambda>cte. cteCap cte = capability.NullCap) x s)\<rbrace>
  transferCapsToSlots ep buffer n caps slots mi
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  by (wp transferCapsToSlots_pres2 | simp)+

crunches setExtraBadge
  for valid_idle'[wp]: valid_idle'
  and if_unsafe'[wp]: if_unsafe_then_cap'

lemma tcts_ifunsafe[wp]:
  "\<lbrace>\<lambda>s. if_unsafe_then_cap' s \<and> distinct slots \<and>
         (\<forall>x\<in>set slots.  cte_wp_at' (\<lambda>cte. cteCap cte = capability.NullCap) x s \<and>
             ex_cte_cap_to' x s)\<rbrace> transferCapsToSlots ep buffer n caps slots mi
   \<lbrace>\<lambda>rv. if_unsafe_then_cap'\<rbrace>"
  by (wp transferCapsToSlots_pres2 | simp)+

lemma tcts_idle'[wp]:
  "\<lbrace>\<lambda>s. valid_idle' s\<rbrace> transferCapsToSlots ep buffer n caps slots mi
   \<lbrace>\<lambda>rv. valid_idle'\<rbrace>"
  apply (rule hoare_pre)
   apply (wp transferCapsToSlots_pres1)
  apply simp
  done

lemma tcts_ct[wp]:
  "\<lbrace>cur_tcb'\<rbrace> transferCapsToSlots ep buffer n caps slots mi \<lbrace>\<lambda>rv. cur_tcb'\<rbrace>"
  by (wp transferCapsToSlots_pres1 cur_tcb_lift)

crunch valid_arch_state' [wp]: setExtraBadge valid_arch_state'

lemma transferCapsToSlots_valid_arch [wp]:
  "\<lbrace>valid_arch_state'\<rbrace> transferCapsToSlots ep buffer n caps slots mi \<lbrace>\<lambda>rv. valid_arch_state'\<rbrace>"
  by (rule transferCapsToSlots_pres1; wp)

crunch valid_global_refs' [wp]: setExtraBadge valid_global_refs'

lemma transferCapsToSlots_valid_globals [wp]:
  "\<lbrace>valid_global_refs' and valid_objs' and valid_mdb' and pspace_distinct' and pspace_aligned' and K (distinct slots)
         and K (length slots \<le> 1)
         and (\<lambda>s. \<forall>x \<in> set slots. real_cte_at' x s \<and> cte_wp_at' (\<lambda>cte. cteCap cte = capability.NullCap) x s)
  and transferCaps_srcs caps\<rbrace>
  transferCapsToSlots ep buffer n caps slots mi
  \<lbrace>\<lambda>rv. valid_global_refs'\<rbrace>"
  apply (wp transferCapsToSlots_presM[where vo=True and emx=False and drv=True and pad=True] | clarsimp)+
  apply (clarsimp simp:cte_wp_at_ctes_of)
  apply (drule(1) bspec,clarsimp)
  apply (case_tac cte,clarsimp)
  apply (frule(1) CSpace_I.ctes_of_valid_cap')
  apply (fastforce simp:valid_cap'_def)
  done

crunch irq_node' [wp]: setExtraBadge "\<lambda>s. P (irq_node' s)"

lemma transferCapsToSlots_irq_node'[wp]:
  "\<lbrace>\<lambda>s. P (irq_node' s)\<rbrace> transferCapsToSlots ep buffer n caps slots mi \<lbrace>\<lambda>rv s. P (irq_node' s)\<rbrace>"
   by (wp transferCapsToSlots_pres1)

lemma valid_irq_handlers_ctes_ofD:
  "\<lbrakk> ctes_of s p = Some cte; cteCap cte = IRQHandlerCap irq; valid_irq_handlers' s \<rbrakk>
       \<Longrightarrow> irq_issued' irq s"
  by (auto simp: valid_irq_handlers'_def cteCaps_of_def ran_def)

crunch valid_irq_handlers' [wp]: setExtraBadge valid_irq_handlers'

lemma transferCapsToSlots_irq_handlers[wp]:
  "\<lbrace>valid_irq_handlers' and valid_objs' and valid_mdb' and pspace_distinct' and pspace_aligned'
         and K(distinct slots \<and> length slots \<le> 1)
         and (\<lambda>s. \<forall>x \<in> set slots. real_cte_at' x s \<and> cte_wp_at' (\<lambda>cte. cteCap cte = capability.NullCap) x s)
         and transferCaps_srcs caps\<rbrace>
     transferCapsToSlots ep buffer n caps slots mi
  \<lbrace>\<lambda>rv. valid_irq_handlers'\<rbrace>"
  apply (wp transferCapsToSlots_presM[where vo=True and emx=False and drv=True and pad=False])
     apply (clarsimp simp: is_derived'_def cte_wp_at_ctes_of badge_derived'_def)
     apply (erule(2) valid_irq_handlers_ctes_ofD)
    apply wp
  apply (clarsimp simp:cte_wp_at_ctes_of | intro ballI conjI)+
  apply (drule(1) bspec,clarsimp)
  apply (case_tac cte,clarsimp)
  apply (frule(1) CSpace_I.ctes_of_valid_cap')
  apply (fastforce simp:valid_cap'_def)
  done

crunch irq_state' [wp]: setExtraBadge "\<lambda>s. P (ksInterruptState s)"

lemma setExtraBadge_irq_states'[wp]:
  "\<lbrace>valid_irq_states'\<rbrace> setExtraBadge buffer b n \<lbrace>\<lambda>_. valid_irq_states'\<rbrace>"
  apply (wp valid_irq_states_lift')
   apply (simp add: setExtraBadge_def storeWordUser_def)
   apply (wpsimp wp: no_irq dmo_lift' no_irq_storeWord)
  apply assumption
  done

lemma transferCapsToSlots_irq_states' [wp]:
  "\<lbrace>valid_irq_states'\<rbrace> transferCapsToSlots ep buffer n caps slots mi \<lbrace>\<lambda>_. valid_irq_states'\<rbrace>"
  by (wp transferCapsToSlots_pres1)

crunch valid_pde_mappings' [wp]: setExtraBadge valid_pde_mappings'

lemma transferCapsToSlots_pde_mappings'[wp]:
  "\<lbrace>valid_pde_mappings'\<rbrace> transferCapsToSlots ep buffer n caps slots mi \<lbrace>\<lambda>rv. valid_pde_mappings'\<rbrace>"
  by (wp transferCapsToSlots_pres1)

lemma transferCapsToSlots_irqs_masked'[wp]:
  "\<lbrace>irqs_masked'\<rbrace> transferCapsToSlots ep buffer n caps slots mi \<lbrace>\<lambda>rv. irqs_masked'\<rbrace>"
  by (wp transferCapsToSlots_pres1 irqs_masked_lift)

lemma storeWordUser_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> storeWordUser a w \<lbrace>\<lambda>_. valid_machine_state'\<rbrace>"
proof -
  have aligned_offset_ignore:
    "\<And>(l::word32) (p::word32) sz. l<4 \<Longrightarrow> p && mask 2 = 0 \<Longrightarrow>
       p+l && ~~ mask pageBits = p && ~~ mask pageBits"
  proof -
    fix l p sz
    assume al: "(p::word32) && mask 2 = 0"
    assume "(l::word32) < 4" hence less: "l<2^2" by simp
    have le: "2 \<le> pageBits" by (simp add: pageBits_def)
    show "?thesis l p sz"
      by (rule is_aligned_add_helper[simplified is_aligned_mask,
          THEN conjunct2, THEN mask_out_first_mask_some,
          where n=2, OF al less le])
  qed

  show ?thesis
    apply (simp add: valid_machine_state'_def storeWordUser_def
                     doMachineOp_def split_def)
    apply wp
    apply clarsimp
    apply (drule use_valid)
    apply (rule_tac x=p in storeWord_um_inv, simp+)
    apply (drule_tac x=p in spec)
    apply (erule disjE, simp_all)
    apply (erule conjE)
    apply (erule disjE, simp)
    apply (simp add: pointerInUserData_def word_size)
    apply (subgoal_tac "a && ~~ mask pageBits = p && ~~ mask pageBits", simp)
    apply (simp only: is_aligned_mask[of _ 2])
    apply (elim disjE, simp_all)
      apply (rule aligned_offset_ignore[symmetric], simp+)+
    done
qed

lemma setExtraBadge_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> setExtraBadge buffer b n \<lbrace>\<lambda>_. valid_machine_state'\<rbrace>"
by (simp add: setExtraBadge_def) wp

lemma transferCapsToSlots_vms[wp]:
  "\<lbrace>\<lambda>s. valid_machine_state' s\<rbrace>
   transferCapsToSlots ep buffer n caps slots mi
   \<lbrace>\<lambda>_ s. valid_machine_state' s\<rbrace>"
  by (wp transferCapsToSlots_pres1)

crunches setExtraBadge, transferCapsToSlots
  for pspace_domain_valid[wp]: "pspace_domain_valid"

crunch ct_not_inQ[wp]: setExtraBadge "ct_not_inQ"

lemma tcts_ct_not_inQ[wp]:
  "\<lbrace>ct_not_inQ\<rbrace>
   transferCapsToSlots ep buffer n caps slots mi
   \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  by (wp transferCapsToSlots_pres1)

crunch gsUntypedZeroRanges[wp]: setExtraBadge "\<lambda>s. P (gsUntypedZeroRanges s)"
crunch ctes_of[wp]: setExtraBadge "\<lambda>s. P (ctes_of s)"

lemma tcts_zero_ranges[wp]:
  "\<lbrace>\<lambda>s. untyped_ranges_zero' s \<and> valid_pspace' s \<and> distinct slots
          \<and> (\<forall>x \<in> set slots. ex_cte_cap_to' x s \<and> cte_wp_at' (\<lambda>cte. cteCap cte = capability.NullCap) x s)
          \<and> (\<forall>x \<in> set slots. real_cte_at' x s)
          \<and> length slots \<le> 1
          \<and> transferCaps_srcs caps s\<rbrace>
    transferCapsToSlots ep buffer n caps slots mi
  \<lbrace>\<lambda>rv. untyped_ranges_zero'\<rbrace>"
  apply (wp transferCapsToSlots_presM[where emx=True and vo=True
      and drv=True and pad=True])
    apply (clarsimp simp: cte_wp_at_ctes_of)
   apply (simp add: cteCaps_of_def)
   apply (rule hoare_pre, wp untyped_ranges_zero_lift)
   apply (simp add: o_def)
  apply (clarsimp simp: valid_pspace'_def ball_conj_distrib[symmetric])
  apply (drule(1) bspec)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (case_tac cte, clarsimp)
  apply (frule(1) ctes_of_valid_cap')
  apply auto[1]
  done

crunches setExtraBadge, transferCapsToSlots
  for ct_idle_or_in_cur_domain'[wp]: ct_idle_or_in_cur_domain'
  and ksDomSchedule[wp]: "\<lambda>s. P (ksDomSchedule s)"
  and ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"
  and ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  and replies_of'[wp]: "\<lambda>s. P (replies_of' s)"

crunches transferCapsToSlots
  for valid_release_queue[wp]: valid_release_queue
  and valid_release_queue'[wp]: valid_release_queue'
  (wp: crunch_wps)

lemma transferCapsToSlots_invs[wp]:
  "\<lbrace>\<lambda>s. invs' s \<and> distinct slots
        \<and> (\<forall>x \<in> set slots. cte_wp_at' (\<lambda>cte. cteCap cte = NullCap) x s)
        \<and> (\<forall>x \<in> set slots. ex_cte_cap_to' x s)
        \<and> (\<forall>x \<in> set slots. real_cte_at' x s)
        \<and> length slots \<le> 1
        \<and> transferCaps_srcs caps s\<rbrace>
   transferCapsToSlots ep buffer n caps slots mi
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def valid_dom_schedule'_def)
  apply (wp valid_irq_node_lift)
  apply fastforce
  done

lemma grs_distinct'[wp]:
  "\<lbrace>\<top>\<rbrace> getReceiveSlots t buf \<lbrace>\<lambda>rv s. distinct rv\<rbrace>"
  apply (cases buf, simp_all add: getReceiveSlots_def
                                  split_def unlessE_def)
   apply (wp, simp)
  apply (wp | simp only: distinct.simps list.simps empty_iff)+
  apply simp
  done

lemma tc_corres:
  "\<lbrakk> info' = message_info_map info;
    list_all2 (\<lambda>x y. cap_relation (fst x) (fst y) \<and> snd y = cte_map (snd x))
         caps caps' \<rbrakk>
  \<Longrightarrow>
   corres ((=) \<circ> message_info_map)
   (tcb_at receiver and valid_objs and
    pspace_aligned and pspace_distinct and valid_mdb
    and valid_list
    and (\<lambda>s. case ep of Some x \<Rightarrow> ep_at x s | _ \<Rightarrow> True)
    and case_option \<top> in_user_frame recv_buf
    and (\<lambda>s. valid_message_info info)
    and transfer_caps_srcs caps)
   (tcb_at' receiver and valid_objs' and valid_replies' and
    pspace_aligned' and pspace_distinct' and no_0_obj' and valid_mdb'
    and (\<lambda>s. case ep of Some x \<Rightarrow> ep_at' x s | _ \<Rightarrow> True)
    and case_option \<top> valid_ipc_buffer_ptr' recv_buf
    and transferCaps_srcs caps'
    and (\<lambda>s. length caps' \<le> msgMaxExtraCaps))
   (transfer_caps info caps ep receiver recv_buf)
   (transferCaps info' caps' ep receiver recv_buf)"
  apply (simp add: transfer_caps_def transferCaps_def
                   getThreadCSpaceRoot)
  apply (rule corres_assume_pre)
  apply (rule corres_guard_imp)
    apply (rule corres_split_deprecated [OF _ get_recv_slot_corres])
      apply (rule_tac x=recv_buf in option_corres)
       apply (rule_tac P=\<top> and P'=\<top> in corres_inst)
       apply (case_tac info, simp)
      apply simp
      apply (rule corres_rel_imp, rule tc_loop_corres,
             simp_all add: split_def)[1]
      apply (case_tac info, simp)
     apply (wp hoare_vcg_all_lift get_rs_cte_at static_imp_wp
                | simp only: ball_conj_distrib)+
   apply (simp add: cte_map_def tcb_cnode_index_def split_def)
   apply (clarsimp simp: valid_pspace'_def valid_ipc_buffer_ptr'_def2
                        split_def
                  cong: option.case_cong)
   apply (drule(1) bspec)
   apply (clarsimp simp:cte_wp_at_caps_of_state)
   apply (frule(1) Invariants_AI.caps_of_state_valid)
   apply (fastforce simp:valid_cap_def)
  apply (cases info)
  apply (clarsimp simp: msg_max_extra_caps_def valid_message_info_def
                        max_ipc_words msg_max_length_def
                        msgMaxExtraCaps_def msgExtraCapBits_def
                        shiftL_nat valid_pspace'_def)
  apply (drule(1) bspec)
  apply (clarsimp simp:cte_wp_at_ctes_of)
  apply (case_tac cte,clarsimp)
  apply (frule(1) ctes_of_valid_cap')
  apply (fastforce simp:valid_cap'_def)
  done

end

crunches transferCaps
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n n p s)"

global_interpretation transferCaps: typ_at_all_props' "transferCaps info caps endpoint receiver receiveBuffer"
  by typ_at_props'

context begin interpretation Arch . (*FIXME: arch_split*)

lemma isIRQControlCap_mask [simp]:
  "isIRQControlCap (maskCapRights R c) = isIRQControlCap c"
  apply (case_tac c)
            apply (clarsimp simp: isCap_simps maskCapRights_def Let_def)+
      apply (rename_tac arch_capability)
      apply (case_tac arch_capability)
          apply (clarsimp simp: isCap_simps ARM_H.maskCapRights_def
                                maskCapRights_def Let_def)+
  done

lemma isPageCap_maskCapRights[simp]:
  "isArchCap isPageCap (RetypeDecls_H.maskCapRights R c) = isArchCap isPageCap c"
  apply (case_tac c; simp add: isCap_simps isArchCap_def maskCapRights_def)
  apply (rename_tac arch_capability)
  apply (case_tac arch_capability; simp add: isCap_simps ARM_H.maskCapRights_def)
  done

lemma is_derived_mask' [simp]:
  "is_derived' m p (maskCapRights R c) = is_derived' m p c"
  apply (rule ext)
  apply (simp add: is_derived'_def badge_derived'_def)
  done

lemma updateCapData_ordering:
  "\<lbrakk> (x, capBadge cap) \<in> capBadge_ordering P; updateCapData p d cap \<noteq> NullCap \<rbrakk>
    \<Longrightarrow> (x, capBadge (updateCapData p d cap)) \<in> capBadge_ordering P"
  apply (cases cap, simp_all add: updateCapData_def isCap_simps Let_def
                                  capBadge_def ARM_H.updateCapData_def
                           split: if_split_asm)
   apply fastforce+
  done

lemma lookup_cap_to'[wp]:
  "\<lbrace>\<top>\<rbrace> lookupCap t cref \<lbrace>\<lambda>rv s. \<forall>r\<in>cte_refs' rv (irq_node' s). ex_cte_cap_to' r s\<rbrace>,-"
  by (simp add: lookupCap_def lookupCapAndSlot_def | wp)+

lemma grs_cap_to'[wp]:
  "\<lbrace>\<top>\<rbrace> getReceiveSlots t buf \<lbrace>\<lambda>rv s. \<forall>x \<in> set rv. ex_cte_cap_to' x s\<rbrace>"
  apply (cases buf; simp add: getReceiveSlots_def split_def unlessE_def)
   apply (wp, simp)
  apply (wp | simp | rule hoare_drop_imps)+
  done

lemma grs_length'[wp]:
  "\<lbrace>\<lambda>s. 1 \<le> n\<rbrace> getReceiveSlots receiver recv_buf \<lbrace>\<lambda>rv s. length rv \<le> n\<rbrace>"
  apply (simp add: getReceiveSlots_def split_def unlessE_def)
  apply (rule hoare_pre)
   apply (wp | wpc | simp)+
  done

lemma transferCaps_invs' [wp]:
  "\<lbrace>invs' and transferCaps_srcs caps\<rbrace>
    transferCaps mi caps ep receiver recv_buf
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: transferCaps_def Let_def split_def)
  apply (wp get_rs_cte_at' hoare_vcg_const_Ball_lift
             | wpcw | clarsimp)+
  done

lemma get_mrs_inv'[wp]:
  "\<lbrace>P\<rbrace> getMRs t buf info \<lbrace>\<lambda>rv. P\<rbrace>"
  by (simp add: getMRs_def load_word_offs_def getRegister_def
          | wp dmo_inv' loadWord_inv mapM_wp'
            asUser_inv det_mapM[where S=UNIV] | wpc)+

end

crunches copyMRs
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n n p s)"
  (wp: crunch_wps)

global_interpretation copyMRs: typ_at_all_props' "copyMRs s sb r rb n"
  by typ_at_props'

context begin interpretation Arch . (*FIXME: arch_split*)

lemma copy_mrs_invs'[wp]:
  "\<lbrace> invs' and tcb_at' s and tcb_at' r \<rbrace> copyMRs s sb r rb n \<lbrace>\<lambda>rv. invs' \<rbrace>"
  including no_pre
  apply (simp add: copyMRs_def)
  apply (wp dmo_invs' no_irq_mapM no_irq_storeWord|
         simp add: split_def)
   apply (case_tac sb, simp_all)[1]
    apply wp+
   apply (case_tac rb, simp_all)[1]
   apply (wp mapM_wp dmo_invs' no_irq_mapM no_irq_storeWord no_irq_loadWord)
   apply blast
  apply (rule hoare_strengthen_post)
   apply (rule mapM_wp)
    apply (wp | simp | blast)+
  done

crunch aligned'[wp]: transferCaps pspace_aligned'
  (wp: crunch_wps simp: zipWithM_x_mapM)
crunch distinct'[wp]: transferCaps pspace_distinct'
  (wp: crunch_wps simp: zipWithM_x_mapM)

crunch aligned'[wp]: copyMRs pspace_aligned'
  (wp: crunch_wps simp: crunch_simps wp: crunch_wps)
crunch distinct'[wp]: copyMRs pspace_distinct'
  (wp: crunch_wps simp: crunch_simps wp: crunch_wps)

lemma set_mrs_valid_objs' [wp]:
  "\<lbrace>valid_objs'\<rbrace> setMRs t a msgs \<lbrace>\<lambda>rv. valid_objs'\<rbrace>"
  apply (simp add: setMRs_def zipWithM_x_mapM split_def)
  apply (wp asUser_valid_objs crunch_wps)
  done

crunch valid_objs'[wp]: copyMRs valid_objs'
  (wp: crunch_wps simp: crunch_simps)


lemma setMRs_invs_bits[wp]:
  "\<lbrace>valid_pspace'\<rbrace> setMRs t buf mrs \<lbrace>\<lambda>rv. valid_pspace'\<rbrace>"
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>
     setMRs t buf mrs \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>
     setMRs t buf mrs \<lbrace>\<lambda>rv s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  "\<lbrace>Invariants_H.valid_queues\<rbrace> setMRs t buf mrs \<lbrace>\<lambda>rv. Invariants_H.valid_queues\<rbrace>"
  "\<lbrace>valid_queues'\<rbrace> setMRs t buf mrs \<lbrace>\<lambda>rv. valid_queues'\<rbrace>"
  "\<lbrace>\<lambda>s. P (state_refs_of' s)\<rbrace>
     setMRs t buf mrs
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  "\<lbrace>if_live_then_nonz_cap'\<rbrace> setMRs t buf mrs \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  "\<lbrace>ex_nonz_cap_to' p\<rbrace> setMRs t buf mrs \<lbrace>\<lambda>rv. ex_nonz_cap_to' p\<rbrace>"
  "\<lbrace>cur_tcb'\<rbrace> setMRs t buf mrs \<lbrace>\<lambda>rv. cur_tcb'\<rbrace>"
  "\<lbrace>if_unsafe_then_cap'\<rbrace> setMRs t buf mrs \<lbrace>\<lambda>rv. if_unsafe_then_cap'\<rbrace>"
  by (simp add: setMRs_def zipWithM_x_mapM split_def storeWordUser_def | wp crunch_wps)+

crunch no_0_obj'[wp]: setMRs no_0_obj'
  (wp: crunch_wps simp: crunch_simps)

lemma copyMRs_invs_bits[wp]:
  "\<lbrace>valid_pspace'\<rbrace> copyMRs s sb r rb n \<lbrace>\<lambda>rv. valid_pspace'\<rbrace>"
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace> copyMRs s sb r rb n
      \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  "\<lbrace>Invariants_H.valid_queues\<rbrace> copyMRs s sb r rb n \<lbrace>\<lambda>rv. Invariants_H.valid_queues\<rbrace>"
  "\<lbrace>valid_queues'\<rbrace> copyMRs s sb r rb n \<lbrace>\<lambda>rv. valid_queues'\<rbrace>"
  "\<lbrace>\<lambda>s. P (state_refs_of' s)\<rbrace>
      copyMRs s sb r rb n
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  "\<lbrace>if_live_then_nonz_cap'\<rbrace> copyMRs s sb r rb n \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  "\<lbrace>ex_nonz_cap_to' p\<rbrace> copyMRs s sb r rb n \<lbrace>\<lambda>rv. ex_nonz_cap_to' p\<rbrace>"
  "\<lbrace>cur_tcb'\<rbrace> copyMRs s sb r rb n \<lbrace>\<lambda>rv. cur_tcb'\<rbrace>"
  "\<lbrace>if_unsafe_then_cap'\<rbrace> copyMRs s sb r rb n \<lbrace>\<lambda>rv. if_unsafe_then_cap'\<rbrace>"
  by (simp add: copyMRs_def  storeWordUser_def | wp mapM_wp' | wpc)+

crunch no_0_obj'[wp]: copyMRs no_0_obj'
  (wp: crunch_wps simp: crunch_simps)

lemma mi_map_length[simp]: "msgLength (message_info_map mi) = mi_length mi"
  by (cases mi, simp)

crunch cte_wp_at'[wp]: copyMRs "cte_wp_at' P p"
  (wp: crunch_wps)

lemma lookupExtraCaps_srcs[wp]:
  "\<lbrace>\<top>\<rbrace> lookupExtraCaps thread buf info \<lbrace>transferCaps_srcs\<rbrace>,-"
  apply (simp add: lookupExtraCaps_def lookupCapAndSlot_def
                   split_def lookupSlotForThread_def
                   getSlotCap_def)
  apply (wp mapME_set[where R=\<top>] getCTE_wp')
       apply (rule_tac P=\<top> in hoare_trivE_R)
       apply (simp add: cte_wp_at_ctes_of)
      apply (wp | simp)+
  done

crunch inv[wp]: lookupExtraCaps "P"
  (wp: crunch_wps mapME_wp' simp: crunch_simps)

lemma invs_mdb_strengthen':
  "invs' s \<longrightarrow> valid_mdb' s" by auto

lemma lookupExtraCaps_length:
  "\<lbrace>\<lambda>s. unat (msgExtraCaps mi) \<le> n\<rbrace> lookupExtraCaps thread send_buf mi \<lbrace>\<lambda>rv s. length rv \<le> n\<rbrace>,-"
  apply (simp add: lookupExtraCaps_def getExtraCPtrs_def)
  apply (rule hoare_pre)
   apply (wp mapME_length | wpc)+
  apply (clarsimp simp: upto_enum_step_def Suc_unat_diff_1 word_le_sub1)
  done

lemma getMessageInfo_msgExtraCaps[wp]:
  "\<lbrace>\<top>\<rbrace> getMessageInfo t \<lbrace>\<lambda>rv s. unat (msgExtraCaps rv) \<le> msgMaxExtraCaps\<rbrace>"
  apply (simp add: getMessageInfo_def)
  apply wp
   apply (simp add: messageInfoFromWord_def Let_def msgMaxExtraCaps_def
                    shiftL_nat)
   apply (subst nat_le_Suc_less_imp)
    apply (rule unat_less_power)
     apply (simp add: word_bits_def msgExtraCapBits_def)
    apply (rule and_mask_less'[unfolded mask_2pm1])
    apply (simp add: msgExtraCapBits_def)
   apply wpsimp+
  done

lemma lcs_corres:
  "cptr = to_bl cptr' \<Longrightarrow>
  corres (lfr \<oplus> (\<lambda>a b. cap_relation (fst a) (fst b) \<and> snd b = cte_map (snd a)))
    (valid_objs and pspace_aligned and tcb_at thread)
    (valid_objs' and pspace_distinct' and pspace_aligned' and tcb_at' thread)
    (lookup_cap_and_slot thread cptr) (lookupCapAndSlot thread cptr')"
  unfolding lookup_cap_and_slot_def lookupCapAndSlot_def
  apply (simp add: liftE_bindE split_def)
  apply (rule corres_guard_imp)
    apply (rule_tac r'="\<lambda>rv rv'. rv' = cte_map (fst rv)"
                 in corres_splitEE)
       apply (rule corres_split_deprecated[OF _ getSlotCap_corres])
          apply (rule corres_returnOkTT, simp)
         apply simp
        apply wp+
      apply (rule corres_rel_imp, rule lookup_slot_corres)
      apply (simp add: split_def)
     apply (wp | simp add: liftE_bindE[symmetric])+
  done

lemma lec_corres:
  "\<lbrakk> info' = message_info_map info; buffer = buffer'\<rbrakk> \<Longrightarrow>
  corres (fr \<oplus> list_all2 (\<lambda>x y. cap_relation (fst x) (fst y) \<and> snd y = cte_map (snd x)))
   (valid_objs and pspace_aligned and tcb_at thread and (\<lambda>_. valid_message_info info))
   (valid_objs' and pspace_distinct' and pspace_aligned' and tcb_at' thread
        and case_option \<top> valid_ipc_buffer_ptr' buffer')
   (lookup_extra_caps thread buffer info) (lookupExtraCaps thread buffer' info')"
  unfolding lookupExtraCaps_def lookup_extra_caps_def
  apply (rule corres_gen_asm)
  apply (cases "mi_extra_caps info = 0")
   apply (cases info)
   apply (simp add: Let_def returnOk_def getExtraCPtrs_def
                    liftE_bindE upto_enum_step_def mapM_def
                    sequence_def doMachineOp_return mapME_Nil
             split: option.split)
  apply (cases info)
  apply (rename_tac w1 w2 w3 w4)
  apply (simp add: Let_def liftE_bindE)
  apply (cases buffer')
   apply (simp add: getExtraCPtrs_def mapME_Nil)
   apply (rule corres_returnOk)
   apply simp
  apply (simp add: msgLengthBits_def msgMaxLength_def word_size field_simps
                   getExtraCPtrs_def upto_enum_step_def upto_enum_word
                   word_size_def msg_max_length_def liftM_def
                   Suc_unat_diff_1 word_le_sub1 mapM_map_simp
                   upt_lhs_sub_map[where x=buffer_cptr_index]
                   wordSize_def wordBits_def
              del: upt.simps)
  apply (rule corres_guard_imp)
    apply (rule corres_split')

       apply (rule_tac S = "\<lambda>x y. x = y \<and> x < unat w2"
               in corres_mapM_list_all2
         [where Q = "\<lambda>_. valid_objs and pspace_aligned and tcb_at thread" and r = "(=)"
            and Q' = "\<lambda>_. valid_objs' and pspace_aligned' and pspace_distinct' and tcb_at' thread
              and case_option \<top> valid_ipc_buffer_ptr' buffer'" and r'="(=)" ])
            apply simp
           apply simp
          apply simp
          apply (rule corres_guard_imp)
            apply (rule load_word_offs_corres')
             apply (clarsimp simp: buffer_cptr_index_def msg_max_length_def
                                   max_ipc_words valid_message_info_def
                                   msg_max_extra_caps_def word_le_nat_alt)
            apply (simp add: buffer_cptr_index_def msg_max_length_def)
           apply simp
          apply simp
         apply (simp add: load_word_offs_word_def)
         apply (wp | simp)+
       apply (subst list_all2_same)
       apply (clarsimp simp: max_ipc_words field_simps)
      apply (simp add: mapME_def, fold mapME_def)[1]
      apply (rule corres_mapME [where S = Id and r'="(\<lambda>x y. cap_relation (fst x) (fst y) \<and> snd y = cte_map (snd x))"])
            apply simp
           apply simp
          apply simp
          apply (rule corres_cap_fault [OF lcs_corres])
          apply simp
         apply simp
         apply (wp | simp)+
      apply (simp add: set_zip_same Int_lower1)
     apply (wp mapM_wp [OF _ subset_refl] | simp)+
  done

crunches copyMRs
  for ctes_of[wp]: "\<lambda>s. P (ctes_of s)"
  and reply_projs[wp]: "\<lambda>s. P (replyNexts_of s) (replyPrevs_of s) (replyTCBs_of s) (replySCs_of s)"
  and valid_replies' [wp]: valid_replies'
  (wp: threadSet_ctes_of crunch_wps)

lemma copyMRs_valid_mdb[wp]:
  "\<lbrace>valid_mdb'\<rbrace> copyMRs t buf t' buf' n \<lbrace>\<lambda>rv. valid_mdb'\<rbrace>"
  by (simp add: valid_mdb'_def copyMRs_ctes_of)

lemma do_normal_transfer_corres:
  "corres dc
  (tcb_at sender and tcb_at receiver and (pspace_aligned:: det_state \<Rightarrow> bool)
   and valid_objs and cur_tcb and valid_mdb and valid_list and pspace_distinct
   and (\<lambda>s. case ep of Some x \<Rightarrow> ep_at x s | _ \<Rightarrow> True)
   and case_option \<top> in_user_frame send_buf
   and case_option \<top> in_user_frame recv_buf)
  (tcb_at' sender and tcb_at' receiver and valid_objs' and valid_replies'
   and pspace_aligned' and pspace_distinct' and cur_tcb'
   and valid_mdb' and no_0_obj'
   and (\<lambda>s. case ep of Some x \<Rightarrow> ep_at' x s | _ \<Rightarrow> True)
   and case_option \<top> valid_ipc_buffer_ptr' send_buf
   and case_option \<top> valid_ipc_buffer_ptr' recv_buf)
  (do_normal_transfer sender send_buf ep badge can_grant receiver recv_buf)
  (doNormalTransfer sender send_buf ep badge can_grant receiver recv_buf)"
  apply (simp add: do_normal_transfer_def doNormalTransfer_def)
  apply (rule corres_guard_imp)

    apply (rule corres_split_mapr [OF _ get_mi_corres])
      apply (rule_tac F="valid_message_info mi" in corres_gen_asm)
      apply (rule_tac r'="list_all2 (\<lambda>x y. cap_relation (fst x) (fst y) \<and> snd y = cte_map (snd x))"
                  in corres_split_deprecated)
         prefer 2
         apply (rule corres_if[OF refl])
          apply (rule corres_split_catch)
             apply (rule corres_trivial, simp)
            apply (rule lec_corres, simp+)
           apply wp+
         apply (rule corres_trivial, simp)
        apply simp
        apply (rule corres_split_eqr [OF _ copy_mrs_corres])
          apply (rule corres_split_deprecated [OF _ tc_corres])
              apply (rename_tac mi' mi'')
              apply (rule_tac F="mi_label mi' = mi_label mi"
                        in corres_gen_asm)
              apply (rule corres_split_nor [OF _ set_mi_corres])
                 apply (simp add: badge_register_def badgeRegister_def)
                 apply (fold dc_def)
                 apply (rule user_setreg_corres)
                apply (case_tac mi', clarsimp)
               apply wp
             apply simp+
           apply ((wp valid_case_option_post_wp hoare_vcg_const_Ball_lift
                     hoare_case_option_wp
                     hoare_valid_ipc_buffer_ptr_typ_at' copyMRs_typ_at'
                     hoare_vcg_const_Ball_lift lookupExtraCaps_length
                   | simp add: if_apply_def2)+)
      apply (wp static_imp_wp | strengthen valid_msg_length_strengthen)+
   apply clarsimp
  apply auto
  done

lemma corres_liftE_lift:
  "corres r1 P P' m m' \<Longrightarrow>
  corres (f1 \<oplus> r1) P P' (liftE m) (withoutFailure m')"
  by simp

lemmas corres_ipc_thread_helper =
  corres_split_eqrE [OF _  corres_liftE_lift [OF gct_corres]]

lemmas corres_ipc_info_helper =
  corres_split_maprE [where f = message_info_map, OF _
                                corres_liftE_lift [OF get_mi_corres]]

end

crunches doNormalTransfer
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n n p s)"
  (wp: crunch_wps)

global_interpretation doNormalTransfer: typ_at_all_props' "doNormalTransfer s sb e b g r rb"
  by typ_at_props'

lemma doNormal_invs'[wp]:
  "\<lbrace>tcb_at' sender and tcb_at' receiver and invs'\<rbrace>
    doNormalTransfer sender send_buf ep badge
             can_grant receiver recv_buf \<lbrace>\<lambda>r. invs'\<rbrace>"
  apply (simp add: doNormalTransfer_def)
  apply (wp hoare_vcg_const_Ball_lift | simp)+
  done

crunch aligned'[wp]: doNormalTransfer pspace_aligned'
  (wp: crunch_wps)
crunch distinct'[wp]: doNormalTransfer pspace_distinct'
  (wp: crunch_wps)

lemma transferCaps_urz[wp]:
  "\<lbrace>untyped_ranges_zero' and valid_pspace'
      and (\<lambda>s. (\<forall>x\<in>set caps. cte_wp_at' (\<lambda>cte. fst x \<noteq> capability.NullCap \<longrightarrow> cteCap cte = fst x) (snd x) s))\<rbrace>
    transferCaps tag caps ep receiver recv_buf
  \<lbrace>\<lambda>r. untyped_ranges_zero'\<rbrace>"
  apply (simp add: transferCaps_def)
  apply (rule hoare_pre)
   apply (wp hoare_vcg_all_lift hoare_vcg_const_imp_lift
      | wpc
      | simp add: ball_conj_distrib)+
  apply clarsimp
  done

crunch gsUntypedZeroRanges[wp]: doNormalTransfer "\<lambda>s. P (gsUntypedZeroRanges s)"
  (wp: crunch_wps transferCapsToSlots_pres1 ignore: constOnFailure)

lemmas asUser_urz = untyped_ranges_zero_lift[OF asUser_gsUntypedZeroRanges]

crunch urz[wp]: doNormalTransfer "untyped_ranges_zero'"
  (ignore: asUser wp: crunch_wps asUser_urz hoare_vcg_const_Ball_lift)

lemma msgFromLookupFailure_map[simp]:
  "msgFromLookupFailure (lookup_failure_map lf)
     = msg_from_lookup_failure lf"
  by (cases lf, simp_all add: lookup_failure_map_def msgFromLookupFailure_def)

context begin interpretation Arch . (*FIXME: arch_split*)

lemma getRestartPCs_corres:
  "corres (=) (tcb_at t) (tcb_at' t)
                 (as_user t getRestartPC) (asUser t getRestartPC)"
  apply (rule corres_as_user')
  apply (rule corres_Id, simp, simp)
  apply (rule no_fail_getRestartPC)
  done

lemma user_mapM_getRegister_corres:
  "corres (=) (tcb_at t) (tcb_at' t)
     (as_user t (mapM getRegister regs))
     (asUser t (mapM getRegister regs))"
  apply (rule corres_as_user')
  apply (rule corres_Id [OF refl refl])
  apply (rule no_fail_mapM)
  apply (simp add: getRegister_def)
  done

lemma make_arch_fault_msg_corres:
  "corres (=) (tcb_at t) (tcb_at' t)
  (make_arch_fault_msg f t)
  (makeArchFaultMessage (arch_fault_map f) t)"
  apply (cases f, clarsimp simp: makeArchFaultMessage_def split: arch_fault.split)
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqr[OF _ getRestartPCs_corres])
      apply (rule corres_trivial, simp add: arch_fault_map_def)
     apply (wp+, auto)
  done

lemma mk_ft_msg_corres:
  "corres (=) (tcb_at t and valid_objs and pspace_aligned and pspace_distinct) (tcb_at' t)
     (make_fault_msg ft t)
     (makeFaultMessage (fault_map ft) t)"
  apply (cases ft, simp_all add: makeFaultMessage_def split del: if_split)
     apply (rule corres_guard_imp)
       apply (rule corres_split_eqr [OF _ getRestartPCs_corres])
         apply (rule corres_trivial, simp add: fromEnum_def enum_bool)
        apply (wp | simp)+
    apply (simp add: ARM_H.syscallMessage_def)
    apply (rule corres_guard_imp)
      apply (rule corres_split_eqr [OF _ user_mapM_getRegister_corres])
        apply (rule corres_trivial, simp)
       apply (wp | simp)+
   apply (simp add: ARM_H.exceptionMessage_def)
   apply (rule corres_guard_imp)
     apply (rule corres_split_eqr [OF _ user_mapM_getRegister_corres])
       apply (rule corres_trivial, simp)
      apply (wp | simp)+
   apply (clarsimp simp: threadGet_getObject)
   apply (rule corres_guard_imp)
     apply (rule corres_split_deprecated[OF _ assert_get_tcb_corres])
       apply (rename_tac tcb tcb')
       apply (rule_tac P="\<lambda>s. (bound (tcb_sched_context tcb) \<longrightarrow> sc_at (the (tcb_sched_context tcb)) s)
                              \<and> pspace_aligned s \<and> pspace_distinct s"
                    in corres_inst)
       apply (case_tac "tcb_sched_context tcb"
              ; case_tac "tcbSchedContext tcb'"
              ; clarsimp simp: tcb_relation_def)
       apply (rule corres_split')
          apply (rule_tac Q="sc_at' (the (tcbSchedContext tcb'))" and P'=\<top> in corres_cross_add_guard)
           apply (fastforce dest!: state_relationD intro!: sc_at_cross simp: obj_at'_def)[1]
          apply (rule corres_guard_imp)
            apply (rule schedContextUpdateConsumed_corres)
           apply (wpsimp simp: sched_context_update_consumed_def setTimeArg_def)+
    apply (fastforce dest!: valid_tcb_objs simp: valid_tcb_def valid_bound_obj_def obj_at_def)
   apply clarsimp
  apply (corressimp corres: make_arch_fault_msg_corres)
  done

crunches makeFaultMessage
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n n p s)"

end

global_interpretation makeFaultMessage: typ_at_all_props' "makeFaultMessage x t"
  by typ_at_props'

lemmas threadget_fault_corres =
          threadget_corres [where r = fault_rel_optionation
                              and f = tcb_fault and f' = tcbFault,
                            simplified tcb_relation_def, simplified]

context begin interpretation Arch . (*FIXME: arch_split*)

crunches make_fault_msg
  for in_user_Frame[wp]: "in_user_frame buffer"

lemma makeFaultMessage_valid_ipc_buffer_ptr'[wp]:
  "makeFaultMessage x thread \<lbrace>valid_ipc_buffer_ptr' p\<rbrace>"
  unfolding valid_ipc_buffer_ptr'_def2
  apply (wpsimp wp: hoare_vcg_all_lift)
  done

lemma do_fault_transfer_corres:
  "corres dc
    (valid_objs and pspace_distinct and pspace_aligned
     and obj_at (\<lambda>ko. \<exists>tcb ft. ko = TCB tcb \<and> tcb_fault tcb = Some ft) sender
     and tcb_at receiver and case_option \<top> in_user_frame recv_buf)
    (tcb_at' sender and tcb_at' receiver and
     case_option \<top> valid_ipc_buffer_ptr' recv_buf)
    (do_fault_transfer badge sender receiver recv_buf)
    (doFaultTransfer badge sender receiver recv_buf)"
  apply (clarsimp simp: do_fault_transfer_def doFaultTransfer_def split_def
                        ARM_H.badgeRegister_def badge_register_def)
  apply (rule_tac Q="\<lambda>fault. valid_objs and pspace_distinct and pspace_aligned and
                             K (\<exists>f. fault = Some f) and
                             tcb_at sender and tcb_at receiver and
                             case_option \<top> in_user_frame recv_buf"
              and Q'="\<lambda>fault'. tcb_at' sender and tcb_at' receiver and
                               case_option \<top> valid_ipc_buffer_ptr' recv_buf"
               in corres_split')
     apply (rule corres_guard_imp)
       apply (rule threadget_fault_corres)
      apply (clarsimp simp: obj_at_def is_tcb)+
    apply (rule corres_assume_pre)
    apply (fold assert_opt_def | unfold haskell_fail_def)+
    apply (rule corres_assert_opt_assume)
     apply (clarsimp split: option.splits
                      simp: fault_rel_optionation_def assert_opt_def
                            map_option_case)
     defer
     defer
     apply (clarsimp simp: fault_rel_optionation_def)
    apply (wp thread_get_wp)
    apply (clarsimp simp: obj_at_def is_tcb)
   apply wp
   apply (rule corres_guard_imp)
      apply (rule corres_split_eqr [OF _ mk_ft_msg_corres])
        apply (rule corres_split_eqr [OF _ set_mrs_corres [OF refl]])
          apply (rule corres_split_nor [OF _ set_mi_corres])
             apply (rule user_setreg_corres)
            apply simp
           apply (wp | simp)+
   apply (rule corres_guard_imp)
      apply (rule corres_split_eqr [OF _ mk_ft_msg_corres])
        apply (rule corres_split_eqr [OF _ set_mrs_corres [OF refl]])
          apply (rule corres_split_nor [OF _ set_mi_corres])
             apply (rule user_setreg_corres)
            apply simp
           apply (wp | simp)+
  done

crunches makeFaultMessage
  for iflive[wp]: if_live_then_nonz_cap'
  and idle'[wp]: valid_idle'

crunches makeFaultMessage
  for invs'[wp]: invs'

lemma doFaultTransfer_invs[wp]:
  "\<lbrace>invs' and tcb_at' receiver and tcb_at' sender\<rbrace>
   doFaultTransfer badge sender receiver recv_buf
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (wpsimp simp: doFaultTransfer_def split_def split: option.split)
  done

lemma dit_corres:
  "corres dc
     (tcb_at s and tcb_at r and valid_objs and pspace_aligned
        and valid_list
        and pspace_distinct and valid_mdb and cur_tcb
        and (\<lambda>s. case ep of Some x \<Rightarrow> ep_at x s | _ \<Rightarrow> True))
     (tcb_at' s and tcb_at' r and valid_pspace' and cur_tcb'
        and (\<lambda>s. case ep of Some x \<Rightarrow> ep_at' x s | _ \<Rightarrow> True))
     (do_ipc_transfer s ep bg grt r)
     (doIPCTransfer s ep bg grt r)"
  apply (simp add: do_ipc_transfer_def doIPCTransfer_def)
  apply (rule_tac Q="%receiveBuffer sa. tcb_at s sa \<and> valid_objs sa \<and>
                       pspace_aligned sa \<and> tcb_at r sa \<and>
                       cur_tcb sa \<and> valid_mdb sa \<and> valid_list sa \<and> pspace_distinct sa \<and>
                       (case ep of None \<Rightarrow> True | Some x \<Rightarrow> ep_at x sa) \<and>
                       case_option (\<lambda>_. True) in_user_frame receiveBuffer sa \<and>
                       obj_at (\<lambda>ko. \<exists>tcb. ko = TCB tcb
                                    \<comment> \<open>\<exists>ft. tcb_fault tcb = Some ft\<close>) s sa"
               in corres_split')
     apply (rule corres_guard_imp)
       apply (rule lipcb_corres')
      apply auto[2]
    apply (rule corres_split' [OF _ _ thread_get_sp threadGet_inv])
     apply (rule corres_guard_imp)
       apply (rule threadget_fault_corres)
      apply simp
     defer
     apply (rule corres_guard_imp)
       apply (subst case_option_If)+
       apply (rule corres_if3)
         apply (simp add: fault_rel_optionation_def)
        apply (rule corres_split_eqr [OF _ lipcb_corres'])
          apply (simp add: dc_def[symmetric])
          apply (rule do_normal_transfer_corres)
         apply (wp | simp add: valid_pspace'_def)+
       apply (simp add: dc_def[symmetric])
       apply (rule do_fault_transfer_corres)
      apply (clarsimp simp: obj_at_def)
     apply (erule ignore_if)
    apply (wp|simp add: obj_at_def is_tcb valid_pspace'_def)+
  done

crunches doIPCTransfer
  for ifunsafe[wp]: "if_unsafe_then_cap'"
  and iflive[wp]: "if_live_then_nonz_cap'"
  and sch_act_wf[wp]: "\<lambda>s. sch_act_wf (ksSchedulerAction s) s"
  and vq[wp]: "valid_queues"
  and vq'[wp]: "valid_queues'"
  and state_refs_of[wp]: "\<lambda>s. P (state_refs_of' s)"
  and ct[wp]: "cur_tcb'"
  and idle'[wp]: "valid_idle'"
  and typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n n p s)"
  and irq_node'[wp]: "\<lambda>s. P (irq_node' s)"
  and valid_arch_state'[wp]: "valid_arch_state'"
  and vrq[wp]: valid_release_queue
  (wp: crunch_wps
   simp: zipWithM_x_mapM ball_conj_distrib)

crunches doIPCTransfer
  for vrq'[wp]: valid_release_queue'
  (wp: crunch_wps threadSet_vrq'_inv
   simp: zipWithM_x_mapM ball_conj_distrib
   ignore: threadSet)

end

global_interpretation doIPCTransfer: typ_at_all_props' "doIPCTransfer s e b g r"
  by typ_at_props'

context begin interpretation Arch . (*FIXME: arch_split*)

lemmas dit_irq_node'[wp] = valid_irq_node_lift [OF doIPCTransfer_irq_node' doIPCTransfer_typ_at']

declare asUser_global_refs' [wp]

lemma lec_valid_cap' [wp]:
  "\<lbrace>valid_objs'\<rbrace> lookupExtraCaps thread xa mi \<lbrace>\<lambda>rv s. (\<forall>x\<in>set rv. s \<turnstile>' fst x)\<rbrace>, -"
  apply (rule hoare_pre, rule hoare_post_imp_R)
    apply (rule hoare_vcg_conj_lift_R[where R=valid_objs' and S="\<lambda>_. valid_objs'"])
     apply (rule lookupExtraCaps_srcs)
    apply wp
   apply (clarsimp simp: cte_wp_at_ctes_of)
   apply (fastforce)
  apply simp
  done

declare asUser_irq_handlers'[wp]

crunches doIPCTransfer
  for objs'[wp]: "valid_objs'"
  and global_refs'[wp]: "valid_global_refs'"
  and irq_handlers'[wp]: "valid_irq_handlers'"
  and irq_states'[wp]: "valid_irq_states'"
  and pde_mappings'[wp]: "valid_pde_mappings'"
  and irqs_masked'[wp]: "irqs_masked'"
  (wp: crunch_wps hoare_vcg_const_Ball_lift
   simp: zipWithM_x_mapM ball_conj_distrib
   rule: irqs_masked_lift)

lemma doIPCTransfer_invs[wp]:
  "\<lbrace>invs' and tcb_at' s and tcb_at' r\<rbrace>
   doIPCTransfer s ep bg grt r
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: doIPCTransfer_def)
  apply (wpsimp wp: hoare_drop_imp)
  done

lemma handle_fault_reply_registers_corres:
  "corres (=) (tcb_at t) (tcb_at' t)
           (do t' \<leftarrow> arch_get_sanitise_register_info t;
               y \<leftarrow> as_user t
                (zipWithM_x
                  (\<lambda>r v. setRegister r
                          (sanitise_register t' r v))
                  msg_template msg);
               return (label = 0)
            od)
           (do t' \<leftarrow> getSanitiseRegisterInfo t;
               y \<leftarrow> asUser t
                (zipWithM_x
                  (\<lambda>r v. setRegister r (sanitiseRegister t' r v))
                  msg_template msg);
               return (label = 0)
            od)"
  apply (rule corres_guard_imp)
    apply (clarsimp simp: arch_get_sanitise_register_info_def getSanitiseRegisterInfo_def)
       apply (rule corres_split_deprecated)
       apply (rule corres_trivial, simp)
      apply (rule corres_as_user')
      apply(simp add: setRegister_def sanitise_register_def
                      sanitiseRegister_def syscallMessage_def)
      apply(subst zipWithM_x_modify)+
      apply(rule corres_modify')
       apply (simp|wp)+
  done

lemma handle_fault_reply_corres:
  "ft' = fault_map ft \<Longrightarrow>
   corres (=) (tcb_at t) (tcb_at' t)
          (handle_fault_reply ft t label msg)
          (handleFaultReply ft' t label msg)"
  apply (cases ft; simp add: handleFaultReply_def handle_arch_fault_reply_def
                             handleArchFaultReply_def syscallMessage_def exceptionMessage_def
                        split: arch_fault.split)
  by (rule handle_fault_reply_registers_corres)+

crunches handleFaultReply
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n n p s)"
  and ct'[wp]: "\<lambda>s. P (ksCurThread s)"
  and nosch[wp]: "\<lambda>s. P (ksSchedulerAction s)"

end

global_interpretation handleFaultReply: typ_at_all_props' "handleFaultReply x t l m"
  by typ_at_props'

lemma doIPCTransfer_sch_act_simple [wp]:
  "\<lbrace>sch_act_simple\<rbrace> doIPCTransfer sender endpoint badge grant receiver \<lbrace>\<lambda>_. sch_act_simple\<rbrace>"
  by (simp add: sch_act_simple_def, wp)

crunches isFinalCapability
  for cur' [wp]: "\<lambda>s. P (cur_tcb' s)"
  (simp: crunch_simps unless_when
     wp: crunch_wps getObject_inv loadObject_default_inv)

lemma finaliseCapTrue_standin_tcb_at' [wp]:
  "\<lbrace>tcb_at' x\<rbrace> finaliseCapTrue_standin cap v2 \<lbrace>\<lambda>_. tcb_at' x\<rbrace>"
  by (rule finaliseCapTrue_standin_tcbDomain_obj_at')

crunches finaliseCapTrue_standin
  for ct'[wp]: "\<lambda>s. P (ksCurThread s)"
  (wp: crunch_wps simp: crunch_simps)

lemma finaliseCapTrue_standin_cur':
  "\<lbrace>\<lambda>s. cur_tcb' s\<rbrace> finaliseCapTrue_standin cap v2 \<lbrace>\<lambda>_ s'. cur_tcb' s'\<rbrace>"
  unfolding cur_tcb'_def
  by (wp_pre, wps, wp, assumption)

lemma cteDeleteOne_cur' [wp]:
  "\<lbrace>\<lambda>s. cur_tcb' s\<rbrace> cteDeleteOne slot \<lbrace>\<lambda>_ s'. cur_tcb' s'\<rbrace>"
  apply (simp add: cteDeleteOne_def unless_def when_def)
  apply (wp hoare_drop_imps finaliseCapTrue_standin_cur' isFinalCapability_cur'
         | simp add: split_def | wp (once) cur_tcb_lift)+
  done

lemma handleFaultReply_cur' [wp]:
  "\<lbrace>\<lambda>s. cur_tcb' s\<rbrace> handleFaultReply x0 thread label msg \<lbrace>\<lambda>_ s'. cur_tcb' s'\<rbrace>"
  apply (clarsimp simp add: cur_tcb'_def)
  apply (rule hoare_lift_Pf2 [OF _ handleFaultReply_ct'])
  apply (wp)
  done

lemma replyRemove_valid_objs'[wp]:
  "replyRemove replyPtr tcbPtr \<lbrace>valid_objs'\<rbrace>"
  unfolding replyRemove_def
  by (wpsimp wp: updateReply_valid_objs' replyUnlink_valid_objs'
                 hoare_vcg_if_lift hoare_drop_imps
           simp: valid_reply'_def split_del: if_split)

lemma emptySlot_weak_sch_act[wp]:
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>
   emptySlot slot irq
   \<lbrace>\<lambda>_ s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  by (wp weak_sch_act_wf_lift tcb_in_cur_domain'_lift)

lemma cancelAllIPC_weak_sch_act_wf[wp]:
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>
   cancelAllIPC epptr
   \<lbrace>\<lambda>_ s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp add: cancelAllIPC_def)
  apply (wp rescheduleRequired_weak_sch_act_wf hoare_drop_imp | wpc | simp)+
  done

lemma cancelAllSignals_weak_sch_act_wf[wp]:
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>
   cancelAllSignals ntfnptr
   \<lbrace>\<lambda>_ s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp add: cancelAllSignals_def)
  apply (wp rescheduleRequired_weak_sch_act_wf hoare_drop_imp | wpc | simp)+
  done

lemma setSchedContext_weak_sch_act_wf:
  "setSchedContext p sc \<lbrace> \<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s \<rbrace>"
  apply (wp weak_sch_act_wf_lift)
  done

lemma setReply_weak_sch_act_wf:
  "setReply p r \<lbrace> \<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s \<rbrace>"
  apply (wp weak_sch_act_wf_lift)
  done

crunches replyUnlink
  for nosch[wp]: "\<lambda>s. P (ksSchedulerAction s)"
  (simp: crunch_simps wp: crunch_wps)

crunches unbindMaybeNotification, schedContextMaybeUnbindNtfn, isFinalCapability,
         cleanReply
  for sch_act_not[wp]: "sch_act_not t"
  (wp: crunch_wps simp: crunch_simps)

crunches replyRemove, replyRemoveTCB
  for weak_sch_act_wf[wp]: "\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s"
  (simp: crunch_simps wp: crunch_wps)

lemma cancelSignal_weak_sch_act_wf[wp]:
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s \<and> sch_act_not threadPtr s\<rbrace>
   cancelSignal threadPtr ntfnPtr
   \<lbrace>\<lambda>_ s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  unfolding cancelSignal_def Let_def
  by (wpsimp wp: gts_wp' | wp (once) hoare_drop_imp)+

lemma cancelIPC_weak_sch_act_wf[wp]:
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s \<and> sch_act_not tptr s\<rbrace>
   cancelIPC tptr
   \<lbrace>\<lambda>_ s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  unfolding cancelIPC_def blockedCancelIPC_def Let_def getBlockingObject_def
  apply (wpsimp wp: gts_wp' threadSet_weak_sch_act_wf hoare_vcg_all_lift
         | wp (once) hoare_drop_imps)+
  done

lemma replyClear_weak_sch_act_wf[wp]:
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>
   replyClear rptr tptr
   \<lbrace>\<lambda>_ s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  unfolding replyClear_def
  apply (wpsimp wp: gts_wp' simp: pred_tcb_at'_eq_commute)
  apply (auto simp: pred_tcb_at'_def obj_at'_def weak_sch_act_wf_def)
  done

crunches finaliseCapTrue_standin
  for weak_sch_act_wf[wp]: "\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s"
  (simp: crunch_simps wp: crunch_wps)

(* This is currently unused. It should be provable if we add `sch_act_simple` to the preconditions *)
lemma cteDeleteOne_weak_sch_act[wp]:
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>
   cteDeleteOne sl
   \<lbrace>\<lambda>_ s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp add: cteDeleteOne_def unless_def)
  apply (wp hoare_drop_imps finaliseCapTrue_standin_cur' isFinalCapability_cur'
         | simp add: split_def)+
  oops

context begin interpretation Arch . (*FIXME: arch_split*)

crunches handleFaultReply
  for pred_tcb_at'[wp]: "pred_tcb_at' proj P t"
  and valid_queues[wp]: "Invariants_H.valid_queues"
  and valid_queues'[wp]: "valid_queues'"
  and tcb_in_cur_domain'[wp]: "tcb_in_cur_domain' t"

crunches unbindNotification
  for sch_act_wf[wp]: "\<lambda>s. sch_act_wf (ksSchedulerAction s) s"
  (wp: sbn_sch_act')

lemma possibleSwitchTo_valid_queues[wp]:
  "\<lbrace>Invariants_H.valid_queues and valid_objs' and
    (\<lambda>s. sch_act_wf (ksSchedulerAction s) s) and st_tcb_at' runnable' t\<rbrace>
   possibleSwitchTo t
   \<lbrace>\<lambda>rv. Invariants_H.valid_queues\<rbrace>"
  by (wpsimp wp: hoare_drop_imps hoare_vcg_if_lift2
           simp: inReleaseQueue_def possibleSwitchTo_def curDomain_def bitmap_fun_defs)

lemma cancelAllIPC_valid_queues':
  "cancelAllIPC t \<lbrace> valid_queues' \<rbrace>"
  apply (clarsimp simp: cancelAllIPC_def)
  apply (fold restartThreadIfNoFault_def)
  apply (fold cancelAllIPC_loop_body_def)
  apply (wpsimp wp: mapM_x_wp' get_ep_inv' getEndpoint_wp)
  done

lemma cancelAllSignals_valid_queues':
  "cancelAllSignals t \<lbrace> valid_queues' \<rbrace>"
  apply (clarsimp simp: cancelAllSignals_def)
  apply (wpsimp wp: mapM_x_wp' getNotification_wp)
  done

crunches cteDeleteOne
  for valid_queues'[wp]: valid_queues'
  (simp: crunch_simps inQ_def
     wp: crunch_wps sts_st_tcb' getObject_inv loadObject_default_inv
         threadSet_valid_queues')

crunches handleFaultReply
  for valid_objs'[wp]: valid_objs'

lemma bind_sc_reply_weak_valid_sched_action[wp]:
  "bind_sc_reply a b \<lbrace>weak_valid_sched_action\<rbrace>"
  unfolding bind_sc_reply_def by wpsimp

lemma bind_sc_reply_invs[wp]:
  "\<lbrace> \<lambda>s. invs s
         \<and> reply_at reply_ptr s
         \<and> sc_at sc_ptr s
         \<and> ex_nonz_cap_to reply_ptr s
         \<and> ex_nonz_cap_to sc_ptr s
         \<and> reply_sc_reply_at (\<lambda>sc_ptr'. sc_ptr' = None) reply_ptr s
         \<and> reply_ptr \<in> fst ` replies_blocked s
         \<and> reply_ptr \<notin> fst ` replies_with_sc s \<rbrace>
    bind_sc_reply sc_ptr reply_ptr
   \<lbrace> \<lambda>rv. invs \<rbrace>"
  unfolding bind_sc_reply_def
  supply if_weak_cong[cong del] if_split[split del]
  apply (rule hoare_seq_ext[OF _ gscrpls_sp])
  apply (rename_tac sc_replies')
  apply (case_tac sc_replies'; simp)
   apply (wpsimp wp: sched_context_donate_invs)
     apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                     wp: valid_irq_node_typ set_reply_sc_valid_replies_already_BlockedOnReply
                         valid_ioports_lift)
    apply (wpsimp wp: set_sc_replies_valid_replies update_sched_context_valid_idle)
   apply clarsimp
   apply (clarsimp simp: invs_def valid_state_def valid_pspace_def
                          reply_sc_reply_at_def obj_at_def state_refs_of_def get_refs_def2
                          sc_replies_sc_at_def pred_tcb_at_def is_tcb is_reply is_sc_obj_def
                  split: if_splits
                  elim!: delta_sym_refs)
   apply safe
        apply fastforce
       apply fastforce
      apply (clarsimp simp: valid_idle_def)
     apply (rule replies_with_sc_upd_replies_new_valid_replies)
       apply fastforce
      apply (clarsimp simp: image_def)
      apply (rule_tac x="(reply_ptr, b)" in bexI; fastforce)
     apply (clarsimp simp: image_def)
    apply (fastforce simp: invs_def valid_state_def valid_pspace_def
                           reply_sc_reply_at_def obj_at_def state_refs_of_def get_refs_def2
                           sc_replies_sc_at_def pred_tcb_at_def is_tcb is_reply is_sc_obj_def
                    split: if_splits
                    elim!: delta_sym_refs)
   apply (clarsimp simp: idle_sc_no_ex_cap)
  apply wpsimp
     apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                     wp: valid_irq_node_typ set_reply_sc_valid_replies_already_BlockedOnReply
                         valid_ioports_lift valid_sc_typ_list_all_reply)
    apply (wpsimp wp: set_sc_replies_valid_replies update_sched_context_valid_idle)
   apply (wpsimp simp: get_simple_ko_def get_object_def
                   wp: valid_sc_typ_list_all_reply valid_ioports_lift)
  apply (subgoal_tac "list_all (\<lambda>r. reply_at r s) (a # list) \<and> reply_ptr \<notin> set (a # list) \<and> distinct (a # list)")
   apply (clarsimp simp: invs_def valid_pspace_def valid_state_def)
   apply (intro conjI)
     apply (rule replies_with_sc_upd_replies_valid_replies_add_one, simp)
       apply (clarsimp simp:replies_blocked_def image_def, fastforce)
      apply simp
     apply (clarsimp simp:sc_replies_sc_at_def obj_at_def)
    apply (erule delta_sym_refs)
     apply (clarsimp split: if_splits
                     elim!: delta_sym_refs)
    apply (clarsimp simp: reply_sc_reply_at_def obj_at_def state_refs_of_def get_refs_def2
                          pred_tcb_at_def is_tcb is_reply is_sc_obj sc_at_pred_n_def
                   split: if_splits
                   elim!: delta_sym_refs)
    apply (safe; clarsimp?)
    apply (rename_tac rp1 tl s tptr scp sc r1 r2 n1)
    apply (subgoal_tac "(rp1,scp) \<in> replies_with_sc s \<and> (rp1,sc_ptr) \<in> replies_with_sc s")
     apply (clarsimp dest!: valid_replies_2_inj_onD )
    apply (intro conjI)
     apply (subgoal_tac "valid_reply r1 s")
      apply (clarsimp simp: valid_reply_def refs_of_def obj_at_def is_sc_obj_def
                     split: option.splits)
      apply (rename_tac ko n2)
      apply (case_tac ko; clarsimp simp: get_refs_def)
      apply (erule disjE, clarsimp split: option.splits)+
      apply (clarsimp simp: replies_with_sc_def sc_replies_sc_at_def obj_at_def split: option.splits)
     apply (erule valid_objs_valid_reply, assumption)
    apply(clarsimp simp: replies_with_sc_def sc_replies_sc_at_def obj_at_def)
    apply (metis cons_set_intro)
   apply (fastforce simp: idle_sc_no_ex_cap tcb_at_def is_tcb_def
                    dest: pred_tcb_at_tcb_at get_tcb_SomeD)
  apply (clarsimp simp del: distinct.simps list.pred_inject insert_iff)
  apply (frule sc_replies_sc_at_subset_fst_replies_with_sc)
  apply (frule invs_valid_objs)
  apply (intro conjI)
    apply (erule replies_blocked_list_all_reply_at)
    apply (meson dual_order.trans invs_valid_replies valid_replies_defs(1))
   apply fastforce
  apply (erule (1) valid_objs_sc_replies_distinct)
  done

(* FIXME RT: move to AInvs *)
crunches bind_sc_reply
  for pspace_distinct[wp]: pspace_distinct
  and pspace_aligned[wp]: pspace_aligned

lemma bind_sc_reply_valid_objs[wp]:
  "\<lbrace>valid_objs and reply_at reply_ptr and sc_at sc_ptr and
    sc_replies_sc_at (\<lambda>a. reply_ptr \<notin> set a) sc_ptr\<rbrace>
   bind_sc_reply sc_ptr reply_ptr
   \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  unfolding bind_sc_reply_def
  apply (wpsimp wp: hoare_list_all_lift)
  apply (drule (1) valid_objs_ko_at)
  by (clarsimp simp: valid_obj_def valid_sched_context_def sc_at_pred_n_def obj_at_def)

lemma replyPush_corres:
  "can_donate = can_donate' \<Longrightarrow>
   corres dc (valid_replies and pspace_aligned and pspace_distinct and valid_objs
              and K (caller \<noteq> idle_thread_ptr) and tcb_at callee
              and st_tcb_at (\<lambda>st. reply_object st = None) caller and ex_nonz_cap_to reply_ptr
              and reply_sc_reply_at (\<lambda>tptr. tptr = None) reply_ptr
              and reply_tcb_reply_at (\<lambda>tptr. tptr = None) reply_ptr
              and weak_valid_sched_action and scheduler_act_not caller
              and (\<lambda>s. reply_ptr \<notin> fst ` replies_with_sc s)
              and (\<lambda>s. sym_refs (\<lambda>p. if p = caller
                                     then tcb_non_st_state_refs_of s caller
                                     else state_refs_of s p)))
   (valid_release_queue_iff and valid_objs' and valid_queues and valid_queues'
    and valid_replies'_sc_asrt reply_ptr)
   (reply_push caller callee reply_ptr can_donate)
   (replyPush caller callee reply_ptr can_donate')"
  unfolding reply_push_def replyPush_def
  apply clarsimp
  apply (rule corres_stateAssert_implied[where P'=\<top>, simplified])
   apply (rule stronger_corres_guard_imp)
     apply (simp add: get_tcb_obj_ref_def)
     apply (rule corres_split_eqr [OF _ threadget_corres])
        apply (rule corres_split_eqr [OF _ threadget_corres])
           apply (rule corres_split [OF replyTCB_update_corres])
             apply (rule corres_split [OF sts_corres])
                apply simp
               apply (rule corres_when2, clarsimp)
               apply (rule corres_split [OF bindScReply_corres schedContextDonate_corres])
                apply (wpsimp wp: sc_at_typ_at)
               apply wpsimp
              apply simp
              apply (wpsimp wp: sts_valid_replies hoare_vcg_imp_lift'
                                hoare_vcg_all_lift sts_in_replies_blocked
                                set_thread_state_weak_valid_sched_action)
             apply (wpsimp wp: hoare_vcg_imp_lift' sts_invs_minor')
            apply clarsimp
            apply (wpsimp wp: hoare_vcg_imp_lift' hoare_vcg_all_lift)
           apply (clarsimp simp: valid_tcb_state'_def cong: conj_cong)
           apply (wpsimp wp: hoare_vcg_imp_lift' hoare_vcg_all_lift updateReply_valid_objs')
          apply (clarsimp simp: tcb_relation_def)
         apply (wpsimp wp: thread_get_wp)
        apply (wpsimp wp: threadGet_wp)
       apply (clarsimp simp: tcb_relation_def)
      apply (wpsimp wp: thread_get_wp')
     apply (wpsimp wp: threadGet_wp)
    apply clarsimp
    apply (frule reply_tcb_reply_at)
    apply (subgoal_tac "caller \<noteq> reply_ptr")
     apply (subgoal_tac "caller \<noteq> idle_thread_ptr")
      apply (clarsimp simp: st_tcb_at_tcb_at cong: conj_cong)
      apply (erule obj_at_weakenE)
      apply (frule valid_objs_valid_tcbs, clarsimp)
      apply (clarsimp simp: is_tcb)
      apply (frule (1) valid_objs_ko_at[where ptr=caller])
      apply (clarsimp simp: valid_obj_def valid_tcb_def)
      apply (subst sc_at_ppred_exm; clarsimp)
      apply (clarsimp simp: replies_with_sc_def image_def obj_at_def is_sc_obj)
      apply (rule conjI)
       apply (erule replies_blocked_upd_tcb_st_valid_replies_not_blocked;
              fastforce intro!: not_BlockedOnReply_not_in_replies_blocked
                         elim!: st_tcb_weakenE)
      subgoal for s s' tcb
        by (erule delta_sym_refs; clarsimp split: if_splits
            ; fastforce dest: reply_tcb_reply_at_ReplyTCB_in_state_refs_of
                              st_tcb_at_TCBReply_in_state_refs_of)
     apply (clarsimp simp: valid_obj_def valid_tcb_def)
    apply (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def)
    apply (clarsimp simp: obj_at_def is_tcb is_reply)
   apply clarsimp
   apply (frule reply_tcb_reply_at)
   apply (frule valid_objs'_valid_tcbs')
   apply (frule cross_relF[OF _ tcb_at'_cross_rel[where t=caller]], fastforce, clarsimp)
   apply (frule cross_relF[OF _ tcb_at'_cross_rel[where t=callee]], fastforce, clarsimp)
   apply (frule cross_relF[OF _ reply_at'_cross_rel[where t=reply_ptr]], fastforce, clarsimp)
   apply (prop_tac "obj_at' (\<lambda>t. valid_bound_sc' (tcbSchedContext t) s') caller s'")
    apply (erule valid_tcbs'_obj_at'[rotated])
     apply (clarsimp simp: valid_tcb'_def)
    apply clarsimp
   apply (clarsimp simp: valid_reply'_def obj_at'_def)
  apply (clarsimp simp: sym_refs_asrt_def)
  done

crunches handle_fault_reply
  for pspace_aligned[wp]: pspace_aligned
  and pspace_distinct[wp]: pspace_distinct

lemma setReleaseQueue_corres:
   "corres dc \<top> (\<lambda>s. g (ksReleaseQueue s) = qs)
      (modify (release_queue_update g))
      (setReleaseQueue qs)"
  unfolding setReleaseQueue_def
  apply (rule corres_modify)
  by (auto simp: state_relation_def release_queue_relation_def cdt_relation_def)

lemma threadSet_valid_release_queue_inv:
  "\<forall>obj. tcbInReleaseQueue (f obj) = tcbInReleaseQueue obj \<Longrightarrow>
   threadSet f t \<lbrace>valid_release_queue\<rbrace>"
  by (wpsimp wp: threadSet_valid_release_queue)

lemma threadSet_valid_release_queue'_inv:
  "\<forall>obj. tcbInReleaseQueue (f obj) = tcbInReleaseQueue obj \<Longrightarrow>
   threadSet f t \<lbrace>valid_release_queue'\<rbrace>"
  apply (wpsimp wp: threadSet_valid_release_queue')
  by (auto simp: valid_release_queue'_def obj_at'_def)

crunches handleFaultReply, doIPCTransfer
  for valid_release_queue[wp]: valid_release_queue
  and valid_release_queue'[wp]: valid_release_queue'
  (wp: crunch_wps threadSet_valid_release_queue_inv threadSet_valid_release_queue'_inv
   ignore: threadSet
   simp: crunch_simps)

lemma refillReady_sp:
  "\<lbrace>P\<rbrace>
   refillReady scp
   \<lbrace>\<lambda>rv s. P s \<and> (\<exists>ko. ko_at' ko scp s \<and> rv = (rTime (refillHd ko) \<le> ksCurTime s + kernelWCETTicks))\<rbrace>"
  apply (wpsimp wp: refillReady_wp)
  by fastforce

lemma refillSufficient_sp:
  "\<lbrace>P\<rbrace>
  refillSufficient scp k
  \<lbrace>\<lambda>rv s. P s \<and> (\<exists>ko. ko_at' ko scp s \<and> rv = (sufficientRefills k (scRefills ko) (scRefillHead ko)))\<rbrace>"
  unfolding refillSufficient_def getRefills_def
  apply wpsimp
  by (clarsimp simp: sufficientRefills_def obj_at'_def)

lemma isValidTimeoutHandler_sp:
  "\<lbrace>P\<rbrace>
   isValidTimeoutHandler x
   \<lbrace>\<lambda>rv s. P s \<and> (\<exists>ko. ko_at' ko x s \<and> rv = (is_EndpointCap (cteCap (tcbTimeoutHandler ko))))\<rbrace>"
  unfolding isValidTimeoutHandler_def
  apply (wpsimp wp: getTCB_wp)
  by (auto simp: is_EndpointCap_def)

declare no_fail_getSlotCap [wp]

lemma cteInsert_sch_act_wf[wp]:
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>
     cteInsert newCap srcSlot destSlot
   \<lbrace>\<lambda>_ s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
by (wp sch_act_wf_lift tcb_in_cur_domain'_lift)

crunches doIPCTransfer, possibleSwitchTo
  for pred_tcb_at'[wp]: "pred_tcb_at' proj P t"
  (wp: mapM_wp' crunch_wps simp: zipWithM_x_mapM)

lemma setSchedulerAction_ct_in_domain:
 "\<lbrace>\<lambda>s. ct_idle_or_in_cur_domain' s
   \<and>  p \<noteq> ResumeCurrentThread \<rbrace> setSchedulerAction p
  \<lbrace>\<lambda>_. ct_idle_or_in_cur_domain'\<rbrace>"
  by (simp add:setSchedulerAction_def | wp)+

crunches doIPCTransfer, possibleSwitchTo
  for ct_idle_or_in_cur_domain'[wp]: ct_idle_or_in_cur_domain'
  and ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  and ksDomSchedule[wp]: "\<lambda>s. P (ksDomSchedule s)"
  (wp: crunch_wps setSchedulerAction_ct_in_domain simp: zipWithM_x_mapM)

crunch tcbDomain_obj_at'[wp]: doIPCTransfer "obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t"
  (wp: crunch_wps constOnFailure_wp simp: crunch_simps)

lemma tcbEPFindIndex_corres:
  "corres (=) (tcb_at t and (\<lambda>s. \<forall>t \<in> set list. tcb_at t s) and K (n < length list))
              (tcb_at' t and (\<lambda>s. \<forall>t \<in> set list. tcb_at' t s))
              (tcb_ep_find_index t list n) (tcbEPFindIndex t list n)"
  apply (rule corres_gen_asm')
  apply (induct n)
   apply (subst tcb_ep_find_index.simps)
   apply (subst tcbEPFindIndex.simps)
   apply (rule corres_split_eqr)
      apply (rule corres_split_eqr)
         apply (rule corres_if, simp)
          apply (rule corres_trivial, simp)
         apply (rule corres_trivial, simp)
        apply (rule threadget_corres, simp add: tcb_relation_def)
       apply wpsimp
      apply wpsimp
     apply (rule threadget_corres, simp add: tcb_relation_def)
    apply wpsimp
   apply wpsimp
  apply (subst tcb_ep_find_index.simps)
  apply (subst tcbEPFindIndex.simps)
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqr)
       apply (rule corres_split_eqr)
          apply (rule corres_if, simp)
           apply (rule corres_if, simp)
            apply (rule corres_trivial, simp)
           apply simp
          apply (rule corres_trivial, simp)
         apply (rule threadget_corres, simp add: tcb_relation_def)
        apply (wp thread_get_wp)
       apply (wp threadGet_wp)
      apply (rule threadget_corres, simp add: tcb_relation_def)
     apply (wp thread_get_wp)
    apply (wpsimp wp: threadGet_wp)
   apply (fastforce simp: projectKO_eq projectKO_tcb obj_at'_def)+
  done

(* The condition `reply_ptr \<notin> fst ` replies_with_sc s` is provable in the presence of
   sym_refs, but sym_refs may not hold at a call of reply_push. If we had sym_refs
   for replies <-> scs only, then that would be enough and should be true at any call of
   reply_push. *)
lemma reply_push_valid_objs:
  "\<lbrace>valid_objs and valid_replies and
    reply_tcb_reply_at (\<lambda>tptr. tptr = None) reply_ptr and
    (\<lambda>s. reply_ptr \<notin> fst ` replies_with_sc s)\<rbrace>
   reply_push caller callee reply_ptr can_donate
   \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  supply if_split [split del]
  unfolding reply_push_def get_tcb_obj_ref_def
  apply simp
  apply (rule hoare_seq_ext[OF _ thread_get_sp])
  apply (rule hoare_seq_ext[OF _ thread_get_sp])
  apply (wpsimp wp: hoare_vcg_if_lift2 hoare_vcg_imp_lift' hoare_vcg_disj_lift
                    get_tcb_obj_ref_wp)
  apply (subgoal_tac "tcb_at caller s \<and> reply_at reply_ptr s", clarsimp)
   apply (subgoal_tac "sc_at y s", clarsimp)
    apply (subst sc_at_ppred_exm)
     apply (clarsimp simp: obj_at_def valid_obj_def valid_tcb_def)
    apply (clarsimp simp: replies_with_sc_def image_def obj_at_def is_sc_obj)
   apply (frule obj_at_ko_at[where p = caller], clarsimp)
   apply (drule (1) valid_objs_ko_at)
   apply (clarsimp simp: obj_at_def valid_obj_def valid_tcb_def)
  apply (clarsimp simp: obj_at_def is_tcb sk_obj_at_pred_def is_reply)
  done

lemma tcbEPAppend_corres:
  "corres (=) (\<lambda>s. tcb_at t s \<and> (\<forall>t \<in> set qs. tcb_at t s))
              (\<lambda>s. tcb_at' t s \<and> (\<forall>t \<in> set qs. tcb_at' t s))
              (tcb_ep_append t qs) (tcbEPAppend t qs)"
  apply (clarsimp simp: tcb_ep_append_def tcbEPAppend_def null_def split del: if_split)
  apply (rule corres_guard_imp)
    apply (rule corres_if; clarsimp?)
    apply (rule_tac corres_split[OF tcbEPFindIndex_corres])
      apply wpsimp+
  done

lemma tcbEPFindIndex_inv[wp]:
  "tcbEPFindIndex t list n \<lbrace>P\<rbrace>"
  apply (rule hoare_weaken_pre)
   apply (induct n)
    apply (subst tcbEPFindIndex.simps, wpsimp)
   apply (subst tcbEPFindIndex.simps, wpsimp, assumption)
      apply wpsimp+
  done

crunches tcbEPAppend
  for ep_at'[wp]: "ep_at' epptr"

(* FIXME RT: move to AInvs *)
crunches reply_push
  for pspace_aligned[wp]: pspace_aligned
  and pspace_distinct[wp]: pspace_distinct
  (wp: crunch_wps simp: crunch_simps)

crunches bindScReply
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  (simp: crunch_simps)

crunches replyPush
  for pspace_aligned'[wp]: pspace_aligned'
  and pspace_distinct'[wp]: pspace_distinct'
  and if_unsafe_then_cap'[wp]: "if_unsafe_then_cap'"
  and valid_global_refs'[wp]: "valid_global_refs'"
  and valid_arch_state'[wp]: "valid_arch_state'"
  and valid_irq_node'[wp]: "\<lambda>s. valid_irq_node' (irq_node' s) s"
  and valid_irq_handlers'[wp]: "valid_irq_handlers'"
  and valid_irq_states'[wp]: "valid_irq_states'"
  and valid_machine_state'[wp]: "valid_machine_state'"
  and valid_release_queue'[wp]: "valid_release_queue'"
  and ct_not_inQ[wp]: "ct_not_inQ"
  and ct_idle_or_in_cur_domain'[wp]: "ct_idle_or_in_cur_domain'"
  and valid_pde_mappings'[wp]: "valid_pde_mappings'"
  and pspace_domain_valid[wp]: "pspace_domain_valid"
  and ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  and valid_dom_schedule'[wp]: "valid_dom_schedule'"
  and cur_tcb'[wp]: "cur_tcb'"
  and no_0_obj'[wp]: no_0_obj'
  and valid_mdb'[wp]: valid_mdb'
  and tcb_at'[wp]: "tcb_at' t"
  and cte_wp_at'[wp]: "cte_wp_at' P p"
  and ctes_of[wp]: "\<lambda>s. P (ctes_of s)"
  and vrq[wp]: valid_release_queue
  and valid_queues'[wp]: valid_queues'
  (wp: crunch_wps hoare_vcg_all_lift valid_irq_node_lift simp: crunch_simps valid_mdb'_def)

crunches setQueue
  for valid_tcb_state'[wp]: "valid_tcb_state' ts"

lemma tcbSchedEnqueue_valid_tcb_state'[wp]:
  "tcbSchedEnqueue t \<lbrace>valid_tcb_state' ts\<rbrace>"
  by (wpsimp simp: tcbSchedEnqueue_def)

lemma replyPush_valid_objs'[wp]:
  "replyPush callerPtr calleePtr replyPtr canDonate \<lbrace>valid_objs'\<rbrace>"
  supply if_split [split del]
  unfolding replyPush_def updateReply_def bind_assoc
  apply (wpsimp wp: schedContextDonate_valid_objs' updateReply_valid_objs'
                    hoare_vcg_if_lift2 threadGet_wp hoare_vcg_imp_lift')
  apply (clarsimp simp: obj_at'_def projectKOs)
  apply (intro conjI impI; (fastforce simp: obj_at'_def projectKOs valid_tcb_state'_def)?)
  by (insert reply_ko_at_valid_objs_valid_reply';
      fastforce simp: valid_reply'_def obj_at'_def projectKOs valid_bound_obj'_def)+

lemma replyPush_valid_replies'[wp]:
  "\<lbrace>valid_replies' and pspace_distinct' and pspace_aligned'
    and st_tcb_at' (Not \<circ> is_replyState) callerPtr\<rbrace>
   replyPush callerPtr calleePtr replyPtr canDonate
   \<lbrace>\<lambda>_. valid_replies'\<rbrace>"
  apply (solves wp | simp (no_asm_use) add: replyPush_def split del: if_split cong: conj_cong |
         wp hoare_vcg_if_lift hoare_vcg_imp_lift' hoare_vcg_ex_lift
            sts'_valid_replies'_except_Blocked updateReply_valid_replies'_except
            sts_st_tcb' threadGet_wp)+
  apply (auto simp: pred_tcb_at'_def obj_at'_def projectKOs)
  done

lemma replyPush_valid_queues[wp]:
  "\<lbrace>valid_queues and valid_objs'\<rbrace>
   replyPush callerPtr calleePtr replyPtr canDonate
   \<lbrace>\<lambda>_. valid_queues\<rbrace>"
  supply if_split [split del]
  unfolding replyPush_def updateReply_def bind_assoc
  apply (rule hoare_seq_ext[OF _ stateAssert_inv])
  apply simp
  apply (rule hoare_seq_ext[OF _ threadGet_sp'])
  apply (rule hoare_seq_ext[OF _ threadGet_sp'])
  apply (rule hoare_seq_ext[OF _ get_reply_sp'])
  apply (wpsimp wp: schedContextDonate_valid_queues
                    threadGet_wp hoare_vcg_if_lift2 hoare_vcg_imp_lift')
  apply (clarsimp simp: ko_at_obj_at'[where P=\<top>])
  apply (clarsimp simp: valid_reply'_def dest!: reply_ko_at_valid_objs_valid_reply')
  done

crunches reply_unlink_tcb
  for sc_replies_sc_at[wp]: "\<lambda>s. Q (sc_replies_sc_at P scp s)"
  (wp: crunch_wps)

crunches doIPCTransfer
  for reply_projs[wp]: "\<lambda>s. P (replyNexts_of s) (replyPrevs_of s) (replyTCBs_of s) (replySCs_of s)"
  (wp: crunch_wps simp: crunch_simps)

lemma sendIPC_corres:
(* call is only true if called in handleSyscall SysCall, which is always blocking. *)
  assumes "call \<longrightarrow> bl"
  shows
  "corres dc (all_invs_but_fault_tcbs and fault_tcbs_valid_states_except_set {t} and valid_list
              and valid_sched_action and ep_at ep and ex_nonz_cap_to t and st_tcb_at active t
              and scheduler_act_not t and (\<lambda>s. cd \<longrightarrow> bound_sc_tcb_at (\<lambda>a. \<exists>y. a = Some y) t s))
             invs'
             (send_ipc bl call bg cg cgr cd t ep) (sendIPC bl call bg cg cgr cd t ep)"
  apply (insert assms)
  apply add_sym_refs
  apply (unfold send_ipc_def sendIPC_def Let_def)
  apply (rule corres_stateAssert_assume)
   apply (clarsimp split del: if_split)
   apply (rule stronger_corres_guard_imp)
     apply (rule corres_split [OF get_ep_corres, where
              R="\<lambda>rv. all_invs_but_fault_tcbs and valid_list and st_tcb_at active t
                      and ep_at ep and valid_sched_action
                      and valid_ep rv and obj_at (\<lambda>ob. ob = Endpoint rv) ep
                      and ex_nonz_cap_to t and scheduler_act_not t
                      and (\<lambda>s. cd \<longrightarrow> bound_sc_tcb_at (\<lambda>a. \<exists>y. a = Some y) t s)"
              and
              R'="\<lambda>rv'. invs' and tcb_at' t and sch_act_not t
                              and ep_at' ep and valid_ep' rv'
                              and ko_at' (rv' :: endpoint) ep
                              and (\<lambda>s'. sym_refs (state_refs_of' s'))"])
       apply (rename_tac ep' rv)
       apply (case_tac ep')
         apply (case_tac bl; simp add: ep_relation_def)
         apply (rule corres_guard_imp)
           apply (rule corres_split [OF sts_corres set_ep_corres])
              apply simp
             apply (simp add: ep_relation_def)
            apply wp+
          apply (clarsimp simp: st_tcb_at_tcb_at valid_tcb_state_def
                                invs_def valid_state_def valid_pspace_def)
         apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def)
         \<comment> \<open>concludes IdleEP\<close>
        apply (simp add: ep_relation_def)
        apply (case_tac bl; simp add: ep_relation_def)
        apply (rule corres_guard_imp)
          apply (rule corres_split [OF sts_corres], simp)
            apply (rule corres_split [OF tcbEPAppend_corres])
              apply (rule set_ep_corres)
              apply (simp add: ep_relation_def)
             apply (wpsimp wp: hoare_vcg_ball_lift)+
         apply (clarsimp simp: st_tcb_at_tcb_at valid_tcb_state_def invs_def valid_state_def valid_pspace_def valid_ep_def)
        apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def valid_ep'_def)
        \<comment> \<open>concludes SendEP\<close>
       apply (simp add: ep_relation_def)
       apply (rename_tac list)
       apply (rule_tac F="list \<noteq> []" in corres_req, simp add: valid_ep_def)
       apply (case_tac list, simp)
       apply (clarsimp split del: if_split)
        \<comment> \<open>start corres logic\<close>
       apply (rename_tac t' tl)
       apply (rule corres_guard_imp)
         apply (rule corres_split [OF set_ep_corres])
            apply (clarsimp simp: ep_relation_def split: list.splits)
           apply (simp add: isReceive_def split del:if_split)
           apply (rule corres_split [OF gts_corres])
             apply (rule stronger_corres_guard_imp)
               apply (rule_tac
                      F="\<exists>reply_opt pl. recv_state = Structures_A.BlockedOnReceive ep reply_opt pl"
                      in corres_gen_asm)
               apply (clarsimp simp: case_bool_If case_option_If if3_fold
                           simp del: dc_simp split del: if_split cong: if_cong)
               apply (rule corres_split [OF dit_corres])
                 apply (rule corres_split[where r'=dc])
                    apply (clarsimp simp: maybeM_def)
                    apply (rule corres_option_split[OF refl corres_return_trivial])
                    apply (rule replyUnlinkTcb_corres)
                   apply (simp only: get_tcb_obj_ref_def)
                   apply (rule corres_split [OF threadget_corres[where r="(=)"]])
                      apply (clarsimp simp: tcb_relation_def)
                     apply (rule corres_split [OF threadget_corres[where r=fault_rel_optionation]])
                        apply (clarsimp simp: tcb_relation_def)
                       apply (rule corres_split [OF corres_if[where r=dc], where r=dc])
                            apply (clarsimp simp: fault_rel_optionation_def)
                           apply (rule corres_if, clarsimp)
                            apply (rule replyPush_corres, simp)
                           apply (rule sts_corres, simp)
                          apply (rule corres_when, simp)
                          apply (rule corres_split [OF threadget_corres[where r="(=)"]])
                             apply (clarsimp simp: tcb_relation_def)
                            apply (simp, rule schedContextDonate_corres)
                           prefer 3 \<comment> \<open>deferring Hoare triples\<close>
                           apply (rule corres_split [OF sts_corres possibleSwitchTo_corres])
                             apply clarsimp
                            \<comment> \<open>starting Hoare triples\<close>
                            apply (wpsimp wp: set_thread_state_valid_sched_action)
                           apply wpsimp
                          apply (wpsimp wp: thread_get_wp')
                         apply (wpsimp wp: threadGet_wp)
                        apply (rule_tac Q="\<lambda>_. valid_objs and pspace_aligned and pspace_distinct
                                 and tcb_at t' and valid_sched_action"
                               in hoare_strengthen_post[rotated])
                         apply clarsimp
                        apply (wpsimp wp: set_thread_state_valid_sched_action sched_context_donate_valid_sched_action
                                          thread_get_wp' reply_push_valid_objs)
                       apply (rule_tac Q="\<lambda>_. valid_objs' and valid_release_queue_iff and
                                valid_queues and valid_queues'"
                              in hoare_strengthen_post[rotated])
                        apply clarsimp
                       apply (wpsimp wp: threadGet_wp schedContextDonate_valid_objs')
                      apply (wpsimp wp: thread_get_wp')
                     apply (wpsimp wp: threadGet_wp)
                    apply (wpsimp wp: thread_get_wp')
                   apply (wpsimp wp: threadGet_wp)
                  apply (rule_tac Q="\<lambda>_. valid_objs and pspace_aligned and pspace_distinct and
                           scheduler_act_not t and valid_sched_action and valid_replies and
                           st_tcb_at active t and tcb_at t' and scheduler_act_not t' and
                           (\<lambda>s. reply_opt \<noteq> None \<longrightarrow> reply_at (the reply_opt) s \<and>
                                ex_nonz_cap_to (the reply_opt) s \<and>
                                reply_tcb_reply_at (\<lambda>tptr. tptr = None) (the reply_opt) s \<and>
                                reply_sc_reply_at (\<lambda>tptr. tptr = None) (the reply_opt) s \<and>
                                the reply_opt \<notin> fst ` replies_with_sc s \<and>
                                sym_refs (state_refs_of s)) and
                           K (t \<noteq> idle_thread_ptr) and
                           (\<lambda>s. cd \<longrightarrow> bound_sc_tcb_at (\<lambda>a. \<exists>y. a = Some y) t s)"
                         in hoare_strengthen_post[rotated])
                   apply (prop_tac "reply_opt \<noteq> None
                                    \<longrightarrow> sym_refs
                                          (\<lambda>p. if p = t
                                               then tcb_non_st_state_refs_of s t
                                               else state_refs_of s p)")
                    subgoal
                      apply clarsimp
                      apply (erule delta_sym_refs)
                       by (auto simp: state_refs_of_def get_refs_def2
                                      pred_tcb_at_def obj_at_def
                               split: if_split_asm option.splits)
                   apply (prop_tac "st_tcb_at (\<lambda>st. reply_object st = None) t s")
                    apply (fastforce elim!: pred_tcb_weakenE)
                   apply (clarsimp simp: st_tcb_at_tcb_at cong: conj_cong)
                   apply (frule valid_sched_action_weak_valid_sched_action, simp)
                   apply (frule valid_objs_valid_tcbs, simp)
                   apply (subgoal_tac "(cd \<longrightarrow> bound_sc_tcb_at (\<lambda>a. sc_at (the a) s) t s)")
                    apply (clarsimp simp: obj_at_def is_tcb pred_tcb_at_def)
                   apply (drule pred_tcb_at_ko_atD, clarsimp)
                   apply (frule (1) valid_objs_ko_at)
                   apply (clarsimp simp: pred_tcb_at_def obj_at_def valid_obj_def valid_tcb_def)
                  apply (wpsimp wp: reply_unlink_tcb_valid_sched_action
                                    reply_unlink_tcb_valid_replies_BlockedOnReceive
                                    reply_unlink_tcb_sym_refs_BlockedOnReceive
                                    reply_unlink_tcb_reply_tcb_reply_at[where P=id, simplified]
                                    reply_unlink_tcb_st_tcb_at'
                                    replies_with_sc_lift)
                 apply (rule_tac Q="\<lambda>_. tcb_at' t and tcb_at' t' and valid_release_queue and
                                        valid_release_queue' and
                                        valid_queues and valid_objs' and
                                        valid_queues' and
                                        (\<lambda>s. reply_opt \<noteq> None \<longrightarrow>
                                             reply_at' (the reply_opt) s \<and>
                                             replySCs_of s (the reply_opt) = None)"
                        in hoare_strengthen_post[rotated])
                  apply (clarsimp cong: conj_cong)
                  apply (frule valid_objs'_valid_tcbs')
                  apply (drule obj_at_ko_at')+
                  apply (blast dest: no_replySC_valid_replies'_sc_asrt)
                 apply wpsimp
                apply (wpfix add: reply_object.simps(1))
                apply (rule_tac Q="\<lambda>_. valid_objs and pspace_aligned and pspace_distinct and
                         valid_replies and
                         scheduler_act_not t and valid_sched_action
                         and st_tcb_at active t and tcb_at t' and
                         if_live_then_nonz_cap and scheduler_act_not t' and
                         K (t \<noteq> idle_thread_ptr) and
                         (\<lambda>s. cd \<longrightarrow> bound_sc_tcb_at (\<lambda>a. \<exists>y. a = Some y) t s) and
                         (\<lambda>s. reply_opt \<noteq> None
                           \<longrightarrow> st_tcb_at ((=) (Structures_A.thread_state.BlockedOnReceive ep reply_opt pl)) t' s
                               \<and> ex_nonz_cap_to (the reply_opt) s
                               \<and> reply_tcb_reply_at ((=) (Some t')) (the reply_opt) s
                               \<and> reply_sc_reply_at (\<lambda>a. a = None) (the reply_opt) s
                               \<and> the reply_opt \<notin> fst ` replies_with_sc s) and
                         (\<lambda>s. sym_refs
                                (\<lambda>x. if x = t'
                                     then {r \<in> state_refs_of s x.
                                             snd r = TCBBound \<or> snd r = TCBSchedContext \<or>
                                             snd r = TCBYieldTo \<or> snd r = TCBReply}
                                     else state_refs_of s x))"
                       in hoare_strengthen_post[rotated])
                 apply (clarsimp split: option.splits cong: conj_cong)
                 apply (intro conjI)
                     apply (erule valid_objs_valid_tcbs)
                    apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb, fastforce)
                   apply fastforce
                  apply (fastforce simp: reply_tcb_reply_at_def obj_at_def st_tcb_at_def)
                 apply (clarsimp simp: sk_obj_at_pred_def obj_at_def is_reply)
                apply (wpsimp wp: hoare_vcg_imp_lift hoare_vcg_all_lift simp: iff_conv_conj_imp)
               apply (wpfix add: Structures_H.thread_state.sel)
               apply (rule_tac Q="\<lambda>_. tcb_at' t and tcb_at' t' and valid_release_queue and
                                      valid_release_queue' and valid_queues and valid_objs' and
                                      valid_queues' and (\<lambda>s. reply_opt \<noteq> None \<longrightarrow> reply_at' (the reply_opt) s \<and>
                                      replySCs_of s (the reply_opt) = None)"
                      in hoare_strengthen_post[rotated])
                apply (fastforce split: option.splits)
               apply (wpsimp wp: hoare_vcg_imp_lift)
              apply assumption
             apply (prop_tac "(tcb_at' t and tcb_at' t' and valid_pspace' and cur_tcb' and
                               ep_at' ep and valid_release_queue and valid_release_queue' and
                               valid_queues and valid_objs' and valid_mdb' and valid_queues') s'",
                    assumption)
             apply clarsimp
             apply (case_tac reply_opt; clarsimp)
             apply (subgoal_tac "reply_at' a s'", simp)
              apply (frule (1) replySCs_of_cross, simp)
             apply (erule cross_relF[OF _ reply_at'_cross_rel])
             apply (clarsimp simp: obj_at_def reply_sc_reply_at_def is_reply)
            apply (wpsimp wp: gts_wp)
           apply (wpsimp wp: gts_wp')
          apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' hoare_vcg_disj_lift)
         apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' hoare_vcg_disj_lift)
        \<comment> \<open>end of main Hoare triples\<close>
        apply (subgoal_tac "tcb_at t' s")
         apply (subgoal_tac "t' \<noteq> ep")
          apply (clarsimp simp: invs_def valid_state_def valid_pspace_def valid_sched_def
                                valid_sched_action_def pred_tcb_at_eq_commute)
          apply (prop_tac "(t', EPRecv) \<in> state_refs_of s ep")
           apply (clarsimp simp: state_refs_of_def obj_at_def)
          apply (frule (1) sym_refsD, simp)
          apply (frule TCBBlockedRecv_in_state_refs_of)
          apply (clarsimp simp: invs_def pred_tcb_at_eq_commute st_tcb_at_tcb_at cong: conj_cong)
          apply (intro conjI impI)
                apply (clarsimp simp: valid_ep_def split: list.splits)
               apply (erule (1) if_live_then_nonz_capD)
               apply (clarsimp simp: obj_at_def live_def)
              apply (erule weak_valid_sched_action_scheduler_action_not)
              apply (clarsimp simp: obj_at_def pred_tcb_at_def)
             apply (clarsimp, erule (1) FalseI[OF idle_no_ex_cap], clarsimp simp: valid_idle_def)
            apply (case_tac "reply_object x"; simp)
            apply (subgoal_tac "data = Some a", simp)
             apply (subgoal_tac "reply_tcb_reply_at ((=) (Some t')) a s", simp)
              apply (subgoal_tac "reply_sc_reply_at (\<lambda>a. a = None) a s", simp)
               apply (intro conjI)
                apply (clarsimp simp: sk_obj_at_pred_def obj_at_def)
                apply (erule (1) if_live_then_nonz_capD2)
                apply (clarsimp simp: live_def live_reply_def)
               apply clarsimp
               apply (frule (1) valid_repliesD1_simp, clarsimp simp: replies_blocked_def)
               apply (subst (asm) identity_eq[where x="Structures_A.thread_state.BlockedOnReply aa" for aa, symmetric])+
               apply (frule (1) st_tcb_reply_state_refs)
               apply (clarsimp simp: pred_tcb_at_def obj_at_def reply_tcb_reply_at_def)
              apply (subst identity_eq)
              apply (erule (1) valid_replies_ReceiveD[rotated])
               apply (subst identity_eq, assumption, simp)
             apply (subst identity_eq)
             apply (erule st_tcb_recv_reply_state_refs[rotated])
             apply (subst identity_eq, assumption)
            apply (clarsimp simp: obj_at_def pred_tcb_at_def)
           subgoal for t' _ s
             (*RT FIXME: The proof of this subgoal is copied completely from si_invs'.
                         It would be nice to turn this into a separate lemma. *)
             apply (rule delta_sym_refs, assumption)
              apply (fastforce simp: obj_at_def state_refs_of_def split: list.splits if_splits)
             apply clarsimp
             apply (intro conjI)
              apply (fastforce simp: valid_obj_def valid_ep_def is_tcb obj_at_def
                              split: list.splits if_splits)
             apply (clarsimp, intro conjI)
              apply (clarsimp simp: obj_at_def split: if_splits)
              apply (erule (1) pspace_valid_objsE)
              apply (fastforce simp: state_refs_of_def)
             apply (clarsimp simp: obj_at_def split: if_splits)
              apply (subgoal_tac "st_tcb_at (\<lambda>st. \<exists>r pl. st = Structures_A.BlockedOnReceive ep r pl) t' s")
               apply (clarsimp simp: st_tcb_at_def obj_at_def state_refs_of_def get_refs_def2
                              split: if_splits)
              apply (erule (1) valid_objsE)
              apply (clarsimp simp: valid_obj_def valid_ep_def st_tcb_at_def obj_at_def)
             apply (clarsimp simp: sym_refs_ko_atD obj_at_def split: list.splits)
             done
          apply (clarsimp simp: obj_at_def pred_tcb_at_def)
         apply (clarsimp simp: obj_at_def is_tcb)
        apply (clarsimp simp: valid_ep_def)
       apply (subgoal_tac "tcb_at' t' s")
        apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def )
        apply (clarsimp simp: valid_ep'_def split: list.splits)
       apply (clarsimp simp: valid_ep'_def)
       \<comment> \<open>concludes RecvEP\<close>
      apply wpsimp
     apply (wpsimp wp: get_ep_ko')
    apply (clarsimp simp: obj_at_def is_ep)
   apply simp
   apply (frule cross_relF[OF _ tcb_at'_cross_rel[where t=t]]; clarsimp)
   apply (frule cross_relF[OF _ ep_at'_cross_rel[where t=ep]]; clarsimp)
   apply (frule cross_relF[OF _ sch_act_not_cross_rel[where t=t]]; clarsimp)
  apply (clarsimp simp: sym_refs_asrt_def)
  done

end

crunches maybeReturnSc
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p' s)"
  and sc_at'_n[wp]: "\<lambda>s. Q (sc_at'_n n p s)"

global_interpretation maybeReturnSc: typ_at_all_props' "maybeReturnSc ntfnPtr tcbPtr"
  by typ_at_props'

global_interpretation setMessageInfo: typ_at_all_props' "setMessageInfo t info"
  by typ_at_props'

context begin interpretation Arch . (*FIXME: arch_split*)

crunches cancel_ipc
  for cur[wp]: "cur_tcb"
  and ntfn_at[wp]: "ntfn_at t"
  (wp: select_wp crunch_wps simp: crunch_simps ignore: set_object)

lemma valid_sched_weak_strg:
  "valid_sched s \<longrightarrow> weak_valid_sched_action s"
  by (simp add: valid_sched_def valid_sched_action_def)

lemma runnable_tsr:
  "thread_state_relation ts ts' \<Longrightarrow> runnable' ts' = runnable ts"
  by (case_tac ts, auto)

lemma idle_tsr:
  "thread_state_relation ts ts' \<Longrightarrow> idle' ts' = idle ts"
  by (case_tac ts, auto)

crunches cancelIPC
  for cur[wp]: cur_tcb'
  (wp: crunch_wps gts_wp' simp: crunch_simps)

lemma setCTE_weak_sch_act_wf[wp]:
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>
   setCTE c cte
   \<lbrace>\<lambda>rv s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp add: weak_sch_act_wf_def)
  apply (wp hoare_vcg_all_lift hoare_convert_imp setCTE_pred_tcb_at' setCTE_tcb_in_cur_domain')
  done

lemma getTCBSc_corres:
  "corres (\<lambda>x y. \<exists>n. sc_relation x n y)
          (\<lambda>s. bound_sc_tcb_at (\<lambda>sc. \<exists>y. sc = Some y \<and> sc_at y s) t s)
          (\<lambda>s. bound_sc_tcb_at' (\<lambda>sc. \<exists>y. sc = Some y \<and> sc_at' y s) t s)
          (get_tcb_sc t) (getTCBSc t)"
  unfolding get_tcb_sc_def getTCBSc_def
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqr)
       apply clarsimp
       apply (rule corres_assert_opt_assume_l)
       apply (rule corres_assert_assume_r)
       apply (rule get_sc_corres)
      apply (clarsimp simp: get_tcb_obj_ref_def)
      apply (rule threadget_corres, simp add: tcb_relation_def)
     apply (clarsimp simp: get_tcb_obj_ref_def)
     apply (wp thread_get_wp)
    apply (wp threadGet_wp)
   apply clarsimp
   apply (fastforce simp: pred_tcb_at_def obj_at_def is_tcb_def)
  apply (clarsimp simp: pred_tcb_at'_def obj_at'_def)
  done

lemma getScTime_corres:
  "corres (=) (invs and active_sc_valid_refills and active_sc_tcb_at t) valid_objs'
              (get_sc_time t) (getScTime t)"
  apply (simp only: get_sc_time_def getScTime_def)
  apply (rule stronger_corres_guard_imp)
    apply (rule corres_split_deprecated[OF _ getTCBSc_corres])
      apply clarsimp
      apply (rule_tac s'=s' in conjunct2[OF refill_hd_relation2, symmetric])
        apply simp+
     apply (wpsimp wp: thread_get_wp simp: get_tcb_sc_def get_tcb_obj_ref_def)
    apply (wpsimp wp: threadGet_wp simp: getTCBSc_def)
   apply (clarsimp simp: vs_all_heap_simps obj_at_kh_kheap_simps is_sc_obj_def)
   apply (erule_tac x=ref' in valid_objsE[OF invs_valid_objs]; simp add: valid_obj_def)
   apply (drule_tac scp=ref' in active_sc_valid_refillsE[rotated])
    apply (clarsimp simp: is_sc_active_def is_sc_active_kh_simp[symmetric])
   apply (fastforce simp: vs_all_heap_simps pred_map_def cfg_valid_refills_def rr_valid_refills_def
                          sp_valid_refills_def sc_refill_cfgs_of_scs_def map_project_def)
  apply clarsimp
  apply (rule context_conjI)
   apply (prop_tac "tcb_at' t s'")
    apply (rule tcb_at_cross; fastforce simp: vs_all_heap_simps obj_at_def is_tcb_def)
   apply (clarsimp simp: vs_all_heap_simps pred_tcb_at'_def state_relation_def)
   apply (drule (1) pspace_relation_absD)
   apply (clarsimp simp: other_obj_relation_def)
   apply (clarsimp split: kernel_object.splits)
   apply (fastforce simp: valid_obj'_def valid_tcb'_def valid_bound_obj'_def
                          obj_at'_def projectKOs tcb_relation_def
                   split: option.splits)+
  done

lemma tcbReleaseEnqueue_corres:
  "corres dc (invs and valid_release_q and active_sc_valid_refills and active_sc_tcb_at t) valid_objs'
             (tcb_release_enqueue t) (tcbReleaseEnqueue t)"
  apply (clarsimp simp: tcb_release_enqueue_def tcbReleaseEnqueue_def setReleaseQueue_def)
  apply (rule stronger_corres_guard_imp)
    apply (rule corres_split_eqr)
       apply (rule corres_split_eqr)
          apply (rule corres_split_eqr)
             apply (rule corres_split_deprecated)
                apply (rule corres_add_noop_lhs2)
                apply (rule corres_split_deprecated)
                   apply (rule threadSet_corres_noop; clarsimp simp: tcb_relation_def)
                  apply (rule corres_modify)
                  apply (clarsimp simp: state_relation_def release_queue_relation_def swp_def)
                 apply wp
                apply wp
               apply (rule corres_when, simp)
               apply (rule reprogram_timer_corres)
              apply (rule hoare_strengthen_post[OF hoare_post_taut], simp)
             apply (rule_tac Q="\<lambda>_. P and P" for P in hoare_triv)
             apply wpsimp
            apply (rule_tac r'="(=)" and S="(=)" in corres_mapM_list_all2; clarsimp)
               apply (clarsimp simp: list.rel_eq)
               apply wpfix
               apply (rule_tac P="\<lambda>s. invs s \<and> active_sc_valid_refills s \<and>
                                      (\<forall>x \<in> set (y#ys). active_sc_tcb_at x s)"
                            in corres_guard1_imp)
                apply (rule getScTime_corres, simp)
              apply wpsimp
             apply (wpsimp simp: getScTime_def getTCBSc_def wp: hoare_drop_imps)
            apply (clarsimp simp: list.rel_eq)
           apply wpsimp
          apply (wpsimp wp: mapM_wp_lift threadGet_wp
                      simp: getScTime_def getTCBSc_def obj_at'_def)
         apply (rule release_queue_corres)
        apply wp
       apply wpsimp
      apply (rule getScTime_corres)
     apply wpsimp
    apply (wpsimp wp: threadGet_wp simp: getScTime_def getTCBSc_def)
   apply (clarsimp simp: valid_release_q_def)
  apply (clarsimp simp: obj_at'_def)
  done

lemma postpone_corres:
  "corres dc (\<lambda>s. invs s \<and> valid_release_q s \<and> active_sc_valid_refills s \<and> is_active_sc ptr s
                         \<and> sc_tcb_sc_at (\<lambda>sc. \<exists>t. sc = Some t \<and> not_queued t s) ptr s)
             (valid_queues and valid_objs')
             (SchedContext_A.postpone ptr) (postpone ptr)"
  apply (rule stronger_corres_guard_imp)
    apply (clarsimp simp: SchedContext_A.postpone_def postpone_def get_sc_obj_ref_def)
    apply (rule_tac r'="\<lambda>sc sca. \<exists>n. sc_relation sc n sca" in corres_split_deprecated)
       apply (rule corres_assert_opt_assume_l)
       apply (rule corres_split_deprecated)
          apply (rule corres_split_deprecated)
             apply (rule reprogram_timer_corres)
            apply (clarsimp simp: sc_relation_def)
            apply (rule tcbReleaseEnqueue_corres)
           apply wp
          apply wp
         apply (clarsimp simp: sc_relation_def)
         apply (rule_tac P="tcb_at (the (sc_tcb rv))" in corres_guard1_imp)
          apply (rule tcbSchedDequeue_corres)
         apply clarsimp
        apply (wp tcb_sched_dequeue_not_queued_inv)
        apply (subgoal_tac "scTCB rv' = sc_tcb rv")
         apply clarsimp
         apply assumption
        apply (clarsimp simp: sc_relation_def)
       apply wpsimp
      apply (rule get_sc_corres)
     apply wp
    apply wp
   apply (clarsimp simp: vs_all_heap_simps valid_obj_def obj_at_def is_obj_defs sc_at_ppred_def)
   apply (frule invs_sym_refs)
   apply (drule_tac p=ptr in sym_refs_ko_atD[rotated])
    apply (simp add: obj_at_def)
   apply (fastforce simp: valid_obj_def valid_sched_context_def obj_at_def
                          is_obj_defs get_refs_def refs_of_rev
                    dest: invs_valid_objs )
  apply clarsimp
  apply (subst sc_at_cross, fastforce+)
   apply (fastforce dest: invs_valid_objs simp: vs_all_heap_simps obj_at_def is_sc_obj_def valid_obj_def)
  apply clarsimp
  apply (subst tcb_at_cross, fastforce+)
   apply (clarsimp simp: state_relation_def pspace_relation_def)
   apply (erule_tac x=ptr in ballE)
    apply (clarsimp simp: vs_all_heap_simps split: if_splits kernel_object.splits)
    apply (fastforce simp: obj_at_def obj_at'_def projectKOs sc_at_ppred_def
                           is_obj_defs valid_obj_def valid_sched_context_def sc_relation_def
                     dest: invs_valid_objs)
   apply (clarsimp simp: vs_all_heap_simps)
  apply clarsimp
  done

lemma schedContextResume_corres:
  "corres dc (invs and valid_ready_qs and valid_release_q
                   and active_sc_valid_refills and sc_tcb_sc_at (\<lambda>sc. sc \<noteq> None) ptr) invs'
             (sched_context_resume ptr) (schedContextResume ptr)"
  apply (simp only: sched_context_resume_def schedContextResume_def)
  apply (rule stronger_corres_guard_imp)
    apply clarsimp
    apply (rule_tac r'="\<lambda>sc sca. \<exists>n. sc_relation sc n sca" in corres_split_deprecated)
       apply (rename_tac sc sca)
       apply (rule corres_assert_opt_assume_l)
       apply (rule corres_assert_assume_r)
       apply (rule corres_split_eqr)
          apply (rule corres_when)
           apply clarsimp
          apply (rule corres_symb_exec_l)
             apply (rule_tac F="runnable ts \<and> sc_active sc" in corres_gen_asm)
             apply (rule corres_split_eqr)
                apply (rule corres_split_eqr)
                   apply (rule corres_when)
                    apply clarsimp
                   apply (rule corres_symb_exec_l)
                      apply (rule corres_symb_exec_l)
                         apply (rule corres_symb_exec_l)
                            apply (rule corres_assert_assume_l)
                            apply (rule postpone_corres)
                           apply (wpsimp simp: get_tcb_queue_def)
                          apply wp
                         apply (clarsimp simp: no_fail_def get_tcb_queue_def gets_def get_def)
                        prefer 2
                        apply (wp thread_get_wp)
                       apply (wp thread_get_exs_valid)
                        apply (clarsimp simp: obj_at_def is_tcb_def)
                       apply clarsimp
                      apply (clarsimp simp: no_fail_def obj_at_def thread_get_def
                                            gets_the_def get_tcb_def gets_def get_def
                                            assert_opt_def bind_def return_def)
                     prefer 2
                     apply (wp thread_get_wp)
                    apply (wp thread_get_exs_valid)
                     apply (clarsimp simp: obj_at_def is_tcb_def)
                    apply clarsimp
                   apply (clarsimp simp: no_fail_def obj_at_def thread_get_def
                                         gets_the_def get_tcb_def gets_def get_def
                                         assert_opt_def bind_def return_def)
                  apply (rule refillSufficient_corres, simp)
                 apply wp
                apply (wpsimp simp: refillSufficient_def getRefills_def)
               apply (rule refillReady_corres, simp)
              apply wp
             apply (wpsimp simp: refillReady_def getCurTime_def)
            apply (rule thread_get_exs_valid)
            apply (erule conjunct1)
           apply (wp thread_get_wp)
           apply (clarsimp cong: conj_cong)
           apply assumption
          apply clarsimp
          apply (rule no_fail_pre)
           apply (wpsimp simp: thread_get_def)
          apply (clarsimp simp: tcb_at_def)
         apply (clarsimp simp: sc_relation_def)
         apply (rule corres_guard_imp)
           apply (rule isSchedulable_corres)
          apply (prop_tac "(valid_objs and tcb_at (the (sc_tcb sc))
                                       and pspace_aligned and pspace_distinct) s")
           apply assumption
          apply clarsimp
         apply assumption
        apply (wp is_schedulable_wp)
       apply (wp isSchedulable_wp)
      apply (rule get_sc_corres)
     apply wp
    apply wp
   apply (subgoal_tac "sc_tcb_sc_at (\<lambda>t. bound_sc_tcb_at (\<lambda>sc. sc = Some ptr) (the t) s) ptr s ")
    apply (clarsimp simp: sc_at_ppred_def obj_at_def is_sc_obj_def bound_sc_tcb_at_def is_tcb_def)
    apply (intro conjI impI; (clarsimp simp: invs_def valid_state_def; fail)?)
          apply (fastforce simp: invs_def valid_state_def valid_pspace_def valid_obj_def)
         apply (clarsimp simp: is_schedulable_bool_def get_tcb_def obj_at_kh_kheap_simps)
         apply (fastforce dest!: active_sc_valid_refillsE
                           simp: valid_refills_def vs_all_heap_simps rr_valid_refills_def
                          split: if_splits)
        apply (fastforce simp: is_schedulable_bool_def get_tcb_def is_sc_active_def
                               vs_all_heap_simps)
       apply (prop_tac "is_active_sc ptr s")
        apply (fastforce simp: vs_all_heap_simps is_schedulable_bool_def get_tcb_def
                               is_sc_active_def)
       apply (fastforce simp: vs_all_heap_simps valid_ready_qs_2_def
                              valid_ready_queued_thread_2_def in_ready_q_def)+
     apply (clarsimp simp: is_schedulable_bool_def get_tcb_def)
    apply (clarsimp simp: is_schedulable_bool_def get_tcb_def is_sc_active_def split: option.splits)
   apply (clarsimp simp: sc_at_ppred_def obj_at_def)
   apply (drule invs_sym_refs)
   apply (drule sym_refs_ko_atD[rotated], simp add: obj_at_def)
   apply (clarsimp simp: pred_tcb_at_def obj_at_def refs_of_rev)
  apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def)
  apply (intro conjI impI allI)
    apply (fastforce simp: sc_at_ppred_def obj_at_def is_sc_obj_def valid_obj_def
                     dest: invs_valid_objs intro!: sc_at_cross)
   apply clarsimp
  apply (clarsimp simp: state_relation_def obj_at_def sc_at_ppred_def)
  apply (drule (1) pspace_relation_absD)
  apply (clarsimp split: if_splits)
  apply (clarsimp simp: sc_relation_def split: kernel_object.splits)
  apply (simp only: sc_relation_def eq_commute[where a="Some P" for P])
  apply (clarsimp simp: obj_at'_def projectKO_eq projectKO_sc)
  done

lemma getScTime_wp:
  "\<lbrace>\<lambda>s. \<forall>tcb. ko_at' tcb tptr s \<longrightarrow> (tcbSchedContext tcb \<noteq> None) \<longrightarrow>
        (\<forall>sc. ko_at' sc (the (tcbSchedContext tcb)) s \<longrightarrow>
          P (rTime (refillHd sc)) s)\<rbrace>
   getScTime tptr \<lbrace>P\<rbrace>"
  apply (wpsimp simp: getScTime_def getTCBSc_def wp: threadGet_wp)
  by (clarsimp simp: tcb_at'_ex_eq_all)

lemma refillUnblockCheck_corres:
 "corres dc \<top> \<top> (refill_unblock_check a) (refillUnblockCheck b)"
  unfolding refillUnblockCheck_def refill_unblock_check_def
  sorry (* refillUnblockCheck_corres *)

lemma updateRefillHd_valid_objs':
  "\<lbrace>valid_objs' and active_sc_at' scPtr\<rbrace> updateRefillHd scPtr f \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  apply (clarsimp simp: updateRefillHd_def2 updateSchedContext_def)
  apply (wpsimp wp: )
  apply (frule (1) sc_ko_at_valid_objs_valid_sc')
  apply (clarsimp simp: valid_sched_context'_def active_sc_at'_def obj_at'_real_def ko_wp_at'_def
                        valid_sched_context_size'_def objBits_def objBitsKO_def projectKO_sc
                        length_replaceAt)
  done

lemma getCTE_cap_to_refs[wp]:
  "\<lbrace>\<top>\<rbrace> getCTE p \<lbrace>\<lambda>rv s. \<forall>r\<in>zobj_refs' (cteCap rv). ex_nonz_cap_to' r s\<rbrace>"
  apply (rule hoare_strengthen_post [OF getCTE_sp])
  apply (clarsimp simp: ex_nonz_cap_to'_def)
  apply (fastforce elim: cte_wp_at_weakenE')
  done

lemma lookupCap_cap_to_refs[wp]:
  "\<lbrace>\<top>\<rbrace> lookupCap t cref \<lbrace>\<lambda>rv s. \<forall>r\<in>zobj_refs' rv. ex_nonz_cap_to' r s\<rbrace>,-"
  apply (simp add: lookupCap_def lookupCapAndSlot_def split_def
                   getSlotCap_def)
  apply (wp | simp)+
  done

lemma arch_stt_objs' [wp]:
  "\<lbrace>valid_objs'\<rbrace> Arch.switchToThread t \<lbrace>\<lambda>rv. valid_objs'\<rbrace>"
  apply (simp add: ARM_H.switchToThread_def)
  apply wp
  done

lemma cteInsert_ct'[wp]:
  "\<lbrace>cur_tcb'\<rbrace> cteInsert a b c \<lbrace>\<lambda>rv. cur_tcb'\<rbrace>"
  by (wp sch_act_wf_lift valid_queues_lift cur_tcb_lift tcb_in_cur_domain'_lift)

lemma maybeDonateSc_corres:
  "corres dc (tcb_at tcb_ptr and ntfn_at ntfn_ptr and invs and weak_valid_sched_action
              and valid_ready_qs and active_sc_valid_refills and valid_release_q
              and current_time_bounded 2 and ex_nonz_cap_to tcb_ptr)
             (tcb_at' tcb_ptr and ntfn_at' ntfn_ptr and invs' and ex_nonz_cap_to' tcb_ptr)
             (maybe_donate_sc tcb_ptr ntfn_ptr)
             (maybeDonateSc tcb_ptr ntfn_ptr)"
  unfolding maybeDonateSc_def maybe_donate_sc_def
  apply (simp add: get_tcb_obj_ref_def get_sk_obj_ref_def liftM_def maybeM_def get_sc_obj_ref_def)
  apply add_sym_refs
  apply (rule corres_stateAssert_assume)
   apply (rule stronger_corres_guard_imp)
     apply (rule corres_split_deprecated[OF _ threadget_corres, where r'="(=)"])
        apply (rule corres_when, simp)
        apply (rule corres_split_deprecated[OF _ get_ntfn_corres])
          apply (rule corres_option_split)
            apply (clarsimp simp: ntfn_relation_def)
           apply (rule corres_return_trivial)
          apply (simp add: get_tcb_obj_ref_def liftM_def maybeM_def)
          apply (rule corres_split_deprecated[OF _ get_sc_corres])
            apply (rule corres_when)
             apply (clarsimp simp: sc_relation_def)
            apply (rule corres_split_deprecated[OF _ schedContextDonate_corres])
              apply (rule corres_split_deprecated[OF _ getCurSc_corres])
                apply (rule corres_split_deprecated[OF _ corres_when])
                    apply (rule schedContextResume_corres, simp)
                  apply clarsimp
                  apply (rule refillUnblockCheck_corres)
                 apply (wpsimp wp: refill_unblock_check_valid_release_q
                                   refill_unblock_check_active_sc_valid_refills)
                apply (wpsimp wp: refillUnblockCheck_invs')
               apply wpsimp
              apply wpsimp
             apply (rule_tac Q="\<lambda>_. invs and valid_ready_qs and
                       active_sc_valid_refills and valid_release_q and
                       sc_not_in_release_q xa and active_sc_valid_refills and
                       current_time_bounded 2 and sc_tcb_sc_at ((=) (Some tcb_ptr)) xa"
                    in hoare_strengthen_post[rotated])
              apply (fastforce simp: sc_at_pred_n_def obj_at_def)
             apply (wpsimp wp: sched_context_donate_invs
                               sched_context_donate_sc_not_in_release_q
                               sched_context_donate_sc_tcb_sc_at)
            apply (wpsimp wp: schedContextDonate_invs')
           apply (wpsimp wp: get_simple_ko_wp getNotification_wp)+
       apply (clarsimp simp: tcb_relation_def)
      apply (wpsimp wp: thread_get_wp' threadGet_wp)+
    apply (clarsimp simp: tcb_at_kh_simps pred_map_eq_normalise invs_def valid_state_def valid_pspace_def
                   split: option.splits cong: conj_cong)
    apply (rename_tac sc_ptr)
    apply (subgoal_tac "sc_at sc_ptr s", clarsimp)
     apply (subgoal_tac "pred_map_eq None (tcb_scps_of s) tcb_ptr", clarsimp)
  apply (intro conjI)
        apply (clarsimp simp: obj_at_def)
        apply (drule (1) ntfn_sc_sym_refsD; clarsimp simp: obj_at_def)
        apply (erule (1) if_live_then_nonz_capD2)
        apply (clarsimp simp: live_def live_sc_def)
       apply (erule (1) weak_valid_sched_action_no_sc_sched_act_not)
      apply (erule (1) valid_release_q_no_sc_not_in_release_q)
     apply clarsimp
     apply (drule heap_refs_retractD[OF sym_refs_retract_tcb_scps, rotated], simp)
     apply (clarsimp simp: vs_all_heap_simps obj_at_def)
    apply (clarsimp simp: vs_all_heap_simps obj_at_def)
   apply (frule valid_objs_ko_at[where ptr=ntfn_ptr, rotated], clarsimp)
   apply (clarsimp simp: valid_obj_def valid_ntfn_def)
  apply (clarsimp simp: tcb_at'_ex_eq_all split: option.splits)
  apply (rename_tac sc_ptr)
  apply (subgoal_tac "sc_at' sc_ptr s'", clarsimp)
   apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def)
   apply (intro conjI)
     apply (clarsimp simp: pred_tcb_at'_def obj_at'_def)
    apply (subgoal_tac "obj_at' (\<lambda>ntfn. ntfnSc ntfn = Some sc_ptr) ntfn_ptr s'")
     apply (frule ntfnSc_sym_refsD)
      apply (frule state_refs_of_cross_eq; clarsimp)
     apply (erule if_live_then_nonz_capE')
     apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def projectKO_sc live_sc'_def)
    apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def)
   apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def)
  apply (frule ntfn_ko_at_valid_objs_valid_ntfn', clarsimp)
  apply (clarsimp simp: valid_ntfn'_def)
  apply (clarsimp simp: sym_refs_asrt_def)
  done

lemma setReleaseQueue_valid_release_queue[wp]:
  "\<lbrace>\<lambda>s. \<forall>t. t \<in> set Q \<longrightarrow> obj_at' (tcbInReleaseQueue) t s\<rbrace>
   setReleaseQueue Q
   \<lbrace>\<lambda>_. valid_release_queue\<rbrace>"
  apply (clarsimp simp: valid_release_queue_def)
  by (wpsimp wp: hoare_vcg_imp_lift' hoare_vcg_all_lift)

lemma setReleaseQueue_valid_queues[wp]:
  "setReleaseQueue Q \<lbrace>valid_queues\<rbrace>"
  by (wpsimp simp: valid_queues_def)

lemma getScTime_tcb_at'[wp]:
  "\<lbrace>\<top>\<rbrace> getScTime tptr \<lbrace>\<lambda>_. tcb_at' tptr\<rbrace>"
  by (wpsimp wp: getScTime_wp)

lemma tcbReleaseEnqueue_vrq[wp]:
  "tcbReleaseEnqueue tcbPtr \<lbrace>valid_release_queue\<rbrace>"
  unfolding tcbReleaseEnqueue_def
  apply wpsimp
          apply (wpsimp wp: threadSet_enqueue_vrq)
         apply ((wpsimp wp: hoare_vcg_imp_lift' hoare_vcg_all_lift)+)[4]
     apply (rule_tac Q="\<lambda>r. tcb_at' tcbPtr and (\<lambda>s. \<forall>x. x \<in> set qs \<longrightarrow> obj_at' tcbInReleaseQueue x s)
                        and K (length qs = length r)"
            in hoare_strengthen_post[rotated])
      apply (fastforce dest: in_set_zip1)
     apply (wpsimp wp: mapM_wp_inv)
    apply wpsimp
   apply (wpsimp wp_del: getScTime_inv, wpsimp)
  apply (clarsimp simp: valid_release_queue_def)
  done

lemma tcbReleaseEnqueue_vrq'[wp]:
  "tcbReleaseEnqueue tcbPtr \<lbrace>valid_release_queue'\<rbrace>"
  unfolding tcbReleaseEnqueue_def
  apply wpsimp
          apply (wpsimp wp: threadSet_enqueue_vrq')
         apply ((wpsimp wp: hoare_vcg_imp_lift' hoare_vcg_all_lift)+)[4]
     apply (rule_tac Q="\<lambda>r. tcb_at' tcbPtr and (\<lambda>s. \<forall>x. obj_at' tcbInReleaseQueue x s \<longrightarrow> x \<in> set qs)
                            and K (length qs = length r)"
            in hoare_strengthen_post[rotated])
      apply clarsimp
      apply (drule_tac x=x in spec, clarsimp)
      apply (subst (asm) fst_image_set_zip[symmetric], assumption)
      apply (fastforce simp: image_def)
     apply (wpsimp wp: mapM_wp_inv)
    apply wpsimp
   apply (wpsimp wp_del: getScTime_inv, wpsimp)
  apply (clarsimp simp: valid_release_queue'_def)
  done

lemma tcbReleaseEnqueue_valid_queues[wp]:
  "tcbReleaseEnqueue tcbPtr \<lbrace>valid_queues\<rbrace>"
  unfolding tcbReleaseEnqueue_def
  apply (wpsimp wp: threadSet_valid_queues)
         apply (clarsimp cong: conj_cong simp: inQ_def)
         by (wpsimp wp: mapM_wp_inv)+

lemma tcbReleaseEnqueue_valid_queues'[wp]:
  "tcbReleaseEnqueue tcbPtr \<lbrace>valid_queues'\<rbrace>"
  unfolding tcbReleaseEnqueue_def
  apply (wpsimp wp: threadSet_valid_queues')
         apply (clarsimp cong: conj_cong simp: inQ_def)
         by (wpsimp wp: mapM_wp_inv)+

lemma postpone_vrq[wp]:
  "\<lbrace>valid_release_queue and valid_objs' and obj_at' (\<lambda>a. \<exists>y. scTCB a = Some y) scPtr\<rbrace>
   postpone scPtr
   \<lbrace>\<lambda>_. valid_release_queue\<rbrace>"
  unfolding postpone_def
  by (wpsimp wp: getNotification_wp threadGet_wp)

lemma postpone_vrq'[wp]:
  "\<lbrace>valid_release_queue' and valid_objs' and obj_at' (\<lambda>a. \<exists>y. scTCB a = Some y) scPtr\<rbrace>
   postpone scPtr
   \<lbrace>\<lambda>_. valid_release_queue'\<rbrace>"
  unfolding postpone_def
  by (wpsimp wp: getNotification_wp threadGet_wp)

lemma postpone_vq[wp]:
  "\<lbrace>valid_queues and valid_objs'\<rbrace>
   postpone scPtr
   \<lbrace>\<lambda>_. valid_queues\<rbrace>"
  unfolding postpone_def
  apply (wpsimp wp: getNotification_wp threadGet_wp tcbSchedDequeue_valid_queues)
  apply (subst obj_at'_conj[symmetric])
  apply (erule (1) valid_objs_valid_tcbE')
  by (clarsimp simp: valid_tcb'_def)

crunches postpone
  for valid_queues'[wp]: valid_queues'

crunches setReleaseQueue, tcbReleaseEnqueue, postpone, schedContextResume
  for valid_objs'[wp]: valid_objs'
  (wp: crunch_wps)

lemma schedContextResume_vrq[wp]:
  "\<lbrace>valid_release_queue and valid_objs' and obj_at' (\<lambda>a. \<exists>y. scTCB a = Some y) scPtr\<rbrace>
   schedContextResume scPtr
   \<lbrace>\<lambda>_. valid_release_queue\<rbrace>"
  unfolding schedContextResume_def
  by (wpsimp wp: hoare_vcg_if_lift2 hoare_drop_imp)

lemma schedContextResume_vrq'[wp]:
  "\<lbrace>valid_release_queue' and valid_objs'\<rbrace> schedContextResume scPtr \<lbrace>\<lambda>_. valid_release_queue'\<rbrace>"
  unfolding schedContextResume_def
  apply (wpsimp | wpsimp wp: hoare_vcg_if_lift2 hoare_drop_imp)+
  by (clarsimp simp: obj_at'_def)

lemma schedContextResume_vq[wp]:
  "\<lbrace>valid_queues and valid_objs'\<rbrace> schedContextResume scPtr \<lbrace>\<lambda>_. valid_queues\<rbrace>"
  unfolding schedContextResume_def
  by (wpsimp wp: hoare_vcg_if_lift2 hoare_drop_imp)

crunches schedContextResume
  for valid_queues'[wp]: valid_queues'
  (wp: crunch_wps)

lemma updateSchedContext_sc_obj_at':
  "\<lbrace>if scPtr = scPtr' then (\<lambda>s. \<forall>ko. ko_at' ko scPtr' s \<longrightarrow> P (f ko)) else obj_at' P scPtr'\<rbrace>
   updateSchedContext scPtr f
   \<lbrace>\<lambda>rv. obj_at' P scPtr'\<rbrace>"
  supply if_split [split del]
  apply (simp add: updateSchedContext_def)
  apply (wpsimp wp: set_sc'.obj_at')
  apply (clarsimp split: if_splits simp: obj_at'_real_def ko_wp_at'_def)
  done

lemma refillPopHead_bound_tcb_sc_at[wp]:
  "refillPopHead scPtr \<lbrace>obj_at' (\<lambda>a. \<exists>y. scTCB a = Some y) t\<rbrace>"
  supply if_split [split del]
  unfolding refillPopHead_def
  apply (wpsimp wp: updateSchedContext_sc_obj_at' getRefillNext_wp)
  by (clarsimp simp: obj_at'_real_def ko_wp_at'_def split: if_split)

lemma updateRefillHd_bound_tcb_sc_at[wp]:
  "updateRefillHd scPtr f \<lbrace>obj_at' (\<lambda>a. \<exists>y. scTCB a = Some y) t\<rbrace>"
  supply if_split [split del]
  unfolding updateRefillHd_def
  apply (wpsimp wp: set_sc'.obj_at')
  by (clarsimp simp: obj_at'_real_def ko_wp_at'_def split: if_split)

crunches refillUnblockCheck
  for bound_tcb_sc_at[wp]: "obj_at' (\<lambda>a. \<exists>y. scTCB a = Some y) t"
  (wp: crunch_wps simp: crunch_simps)

lemma maybeDonateSc_valid_release_queue[wp]:
  "\<lbrace>valid_objs' and valid_release_queue\<rbrace>
   maybeDonateSc tcbPtr ntfnPtr
   \<lbrace>\<lambda>_. valid_release_queue\<rbrace>"
  unfolding maybeDonateSc_def
  apply wpsimp
  apply (rule_tac Q="\<lambda>_. valid_release_queue and valid_objs'
                         and obj_at' (\<lambda>a. \<exists>y. scTCB a = Some y) x2"
         in hoare_strengthen_post[rotated], clarsimp)
       apply (wpsimp wp: getNotification_wp threadGet_wp schedContextDonate_valid_objs')+
  by (clarsimp simp: obj_at'_def)

lemma maybeDonateSc_valid_objs'[wp]:
  "\<lbrace>valid_objs' and valid_release_queue'\<rbrace>
   maybeDonateSc tptr nptr
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  unfolding maybeDonateSc_def
  apply (wpsimp wp: getNotification_wp threadGet_wp schedContextDonate_valid_objs')
  by (clarsimp simp: obj_at'_def)

lemma maybeDonateSc_vrq'[wp]:
  "\<lbrace>valid_objs' and valid_release_queue'\<rbrace>
   maybeDonateSc tptr nptr
   \<lbrace>\<lambda>_. valid_release_queue'\<rbrace>"
  unfolding maybeDonateSc_def
  apply (wpsimp wp: getNotification_wp threadGet_wp schedContextDonate_valid_objs')
  by (clarsimp simp: obj_at'_def)

lemma maybeDonateSc_valid_queues[wp]:
  "\<lbrace>valid_queues and valid_objs'\<rbrace>
   maybeDonateSc tptr nptr
   \<lbrace>\<lambda>_. valid_queues\<rbrace>"
  unfolding maybeDonateSc_def
  apply (wpsimp wp: getNotification_wp threadGet_wp schedContextDonate_valid_queues
                    schedContextDonate_valid_objs')
  by (clarsimp simp: obj_at'_def)

lemma maybeDonateSc_valid_queues'[wp]:
  "\<lbrace>valid_queues' and valid_objs'\<rbrace>
   maybeDonateSc tptr nptr
   \<lbrace>\<lambda>_. valid_queues'\<rbrace>"
  unfolding maybeDonateSc_def
  apply (wpsimp wp: getNotification_wp threadGet_wp schedContextDonate_valid_queues')
  by (clarsimp simp: obj_at'_def)

lemma tcbFault_update_ex_nonz_cap_to'[wp]:
  "threadSet (tcbFault_update x) t' \<lbrace>ex_nonz_cap_to' t\<rbrace>"
  unfolding ex_nonz_cap_to'_def
  by (wpsimp wp: threadSet_cte_wp_at'T hoare_vcg_ex_lift;
      fastforce simp: tcb_cte_cases_def)

crunches cancelIPC
  for ex_nonz_cap_to'[wp]: "ex_nonz_cap_to' t"
  (wp: crunch_wps simp: crunch_simps ignore: threadSet)

lemma thread_state_tcb_in_WaitingNtfn'_q:
  "\<lbrakk>ko_at' ntfn ntfnPtr s; ntfnObj ntfn = Structures_H.ntfn.WaitingNtfn q; valid_objs' s;
    sym_refs (state_refs_of' s); t \<in> set q\<rbrakk>
   \<Longrightarrow> st_tcb_at' is_BlockedOnNotification t s"
  apply (clarsimp simp: sym_refs_def)
  apply (erule_tac x = ntfnPtr in allE)
  apply (drule_tac x = "(t, NTFNSignal)" in bspec)
   apply (clarsimp simp: state_refs_of'_def obj_at'_def refs_of'_def projectKOs)
  apply (subgoal_tac "tcb_at' t s")
   apply (clarsimp simp: state_refs_of'_def refs_of'_def obj_at'_real_def ko_wp_at'_def
                         projectKO_tcb tcb_st_refs_of'_def tcb_bound_refs'_def get_refs_def)
   apply (erule disjE)
    apply (case_tac "tcbState obj"; clarsimp split: if_splits)
    apply (clarsimp simp: pred_tcb_at'_def obj_at'_real_def ko_wp_at'_def projectKO_tcb)
   apply (clarsimp split: option.splits)
  apply (drule (1) ntfn_ko_at_valid_objs_valid_ntfn')
  apply (clarsimp simp: valid_ntfn'_def)
  done

lemma sendSignal_corres:
  "corres dc (einvs and ntfn_at ep and current_time_bounded 2) (invs' and ntfn_at' ep)
             (send_signal ep bg) (sendSignal ep bg)"
  apply (simp add: send_signal_def sendSignal_def Let_def)
  apply add_sym_refs
  apply (rule corres_stateAssert_assume)
   apply (rule corres_guard_imp)
     apply (rule corres_split_deprecated [OF _ get_ntfn_corres,
                 where
                 R  = "\<lambda>rv. einvs and ntfn_at ep and valid_ntfn rv and
                            ko_at (Structures_A.Notification rv) ep
                            and current_time_bounded 2" and
                 R' = "\<lambda>rv'. invs' and ntfn_at' ep and
                             valid_ntfn' rv' and ko_at' rv' ep"])
       defer
       apply (wp get_simple_ko_ko_at get_ntfn_ko')+
     apply (simp add: invs_valid_objs invs_valid_objs')+
   apply (clarsimp simp: sym_refs_asrt_def)
  apply add_sym_refs
  apply (case_tac "ntfn_obj ntfn"; simp)
    \<comment> \<open>IdleNtfn\<close>
    apply (clarsimp simp add: ntfn_relation_def)
    apply (case_tac "ntfnBoundTCB nTFN"; simp)
     apply (rule corres_guard_imp[OF set_ntfn_corres])
       apply (clarsimp simp add: ntfn_relation_def)+
    apply (rule corres_guard_imp)
      apply (rule corres_split_deprecated[OF _ gts_corres])
        apply (rule corres_if)
          apply (fastforce simp: receive_blocked_def receiveBlocked_def
                                 thread_state_relation_def
                          split: Structures_A.thread_state.splits
                                 Structures_H.thread_state.splits)
         apply (rule corres_split_deprecated[OF _ cancel_ipc_corres])
           apply (rule corres_split_deprecated[OF _ sts_corres])
              apply (simp add: badgeRegister_def badge_register_def)
              apply (rule corres_split_deprecated[OF _ user_setreg_corres])
                apply (rule corres_split_deprecated[OF _ maybeDonateSc_corres])
                  apply (rule corres_split_deprecated[OF _ isSchedulable_corres])
                    apply (rule corres_when, simp)
                    apply (rule possibleSwitchTo_corres)
                   apply ((wpsimp wp: hoare_drop_imp)+)[2]
                 apply (clarsimp simp: pred_conj_def, strengthen valid_objs_valid_tcbs)
                 apply (wpsimp wp: maybe_donate_sc_valid_sched_action)
                apply (clarsimp simp: pred_conj_def, strengthen valid_objs'_valid_tcbs')
                apply (wpsimp+)[3]
             apply (clarsimp simp: thread_state_relation_def)
            apply (simp add: pred_conj_def)
            apply (strengthen valid_sched_action_weak_valid_sched_action)
            apply (wpsimp wp: sts_cancel_ipc_Running_invs set_thread_state_valid_sched_action
                              set_thread_state_valid_ready_qs
                              set_thread_state_valid_release_q)
           apply (wpsimp wp: sts_invs')
          apply (rename_tac ntfn ntfn' tptr st st')
          apply (rule_tac Q="\<lambda>_. invs and tcb_at tptr and ntfn_at ep and
                   st_tcb_at
                     ((=) Structures_A.thread_state.Running or
                      (=) Structures_A.thread_state.Inactive or
                      (=) Structures_A.thread_state.Restart or
                      (=) Structures_A.thread_state.IdleThreadState) tptr and
                   ex_nonz_cap_to tptr and fault_tcb_at ((=) None) tptr and
                   valid_sched and scheduler_act_not tptr and active_sc_valid_refills
                   and current_time_bounded 2"
                 in hoare_strengthen_post[rotated])
           apply (clarsimp simp: invs_def valid_state_def valid_pspace_def valid_sched_def pred_disj_def)
          apply (wpsimp wp: cancel_ipc_simple_except_awaiting_reply cancel_ipc_ex_nonz_cap_to_tcb)
         apply (clarsimp cong: conj_cong simp: pred_conj_def valid_tcb_state'_def pred_tcb_at'_eq_commute)
         apply (rule_tac Q="\<lambda>_. invs' and tcb_at' a and ntfn_at' ep and
                                (\<lambda>s. a \<noteq> ksIdleThread s) and ex_nonz_cap_to' a and
                                st_tcb_at' simple' a"
                in hoare_strengthen_post[rotated])
          apply (fastforce simp: invs'_def valid_state'_def valid_pspace'_def pred_tcb_at'_def
                                 obj_at'_def)
         apply (wpsimp wp: cancelIPC_invs')
        apply (rule set_ntfn_corres, clarsimp simp: ntfn_relation_def)
       apply (wpsimp wp: gts_wp gts_wp')+
     apply (frule (1) valid_objs_ko_at[OF invs_valid_objs])
     apply (clarsimp simp: valid_obj_def valid_ntfn_def receive_blocked_equiv
                           is_blocked_on_receive_def)
     apply (frule (1) valid_sched_scheduler_act_not, simp)
     apply (frule st_tcb_ex_cap; clarsimp)
     apply (clarsimp simp: invs_def valid_sched_def valid_state_def valid_pspace_def)
    apply (clarsimp simp: valid_ntfn'_def)
    apply (intro conjI)
     apply (clarsimp simp: valid_idle'_def invs'_def valid_state'_def idle_tcb'_def obj_at'_def
                           pred_tcb_at'_def receiveBlocked_def)
    apply (rule if_live_then_nonz_capE', clarsimp)
    apply (clarsimp simp: pred_tcb_at'_def obj_at'_real_def ko_wp_at'_def projectKO_tcb)
    apply (clarsimp simp: receiveBlocked_equiv is_BlockedOnReceive_def)
   \<comment> \<open>WaitingNtfn\<close>
   apply (clarsimp simp: ntfn_relation_def Let_def update_waiting_ntfn_def)
   apply (rename_tac list)
   apply (rule corres_guard_imp)
     apply (rule_tac F="list \<noteq> []" in corres_gen_asm)
     apply (simp add: list_case_helper split del: if_split)
     apply (rule corres_split_deprecated [OF _ set_ntfn_corres])
        apply (rule corres_split_deprecated [OF _ sts_corres])
           apply (simp add: badgeRegister_def badge_register_def)
           apply (rule corres_split_deprecated [OF _ user_setreg_corres])
             apply (rule corres_split_deprecated[OF _ maybeDonateSc_corres])
               apply (rule corres_split_deprecated[OF _ isSchedulable_corres])
                 apply (rule corres_when, simp)
                 apply (rule possibleSwitchTo_corres)
                apply ((wpsimp wp: hoare_drop_imp)+)[2]
              apply (clarsimp simp: pred_conj_def, strengthen valid_objs_valid_tcbs)
              apply (wpsimp wp: maybe_donate_sc_valid_sched_action)
             apply (clarsimp simp: pred_conj_def, strengthen valid_objs'_valid_tcbs')
             apply (wpsimp+)[3]
          apply (clarsimp simp: thread_state_relation_def)
         apply (simp add: pred_conj_def)
         apply (strengthen valid_sched_action_weak_valid_sched_action)
         apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                         wp: sts_valid_replies sts_only_idle sts_fault_tcbs_valid_states
                             set_thread_state_valid_sched_action
                             set_thread_state_valid_ready_qs set_thread_state_valid_release_q)
        apply (wpsimp wp: sts_invs')
       apply (clarsimp simp: ntfn_relation_def split: list.splits)
      apply (clarsimp cong: conj_cong, wpsimp)
     apply (clarsimp cong: conj_cong, wpsimp wp: set_ntfn_minor_invs' hoare_vcg_all_lift hoare_vcg_imp_lift)
    apply (clarsimp cong: conj_cong)
    apply (frule valid_objs_ko_at[rotated], clarsimp)
    apply (clarsimp simp: valid_obj_def valid_ntfn_def invs_def valid_state_def valid_pspace_def
                          valid_sched_def obj_at_def)
    apply (frule valid_objs_valid_tcbs, simp)
    apply (frule (3) st_in_waitingntfn)
    apply (subgoal_tac "hd list \<noteq> ep", simp)
     apply (rule conjI)
      apply (clarsimp split: list.splits option.splits)
      apply (case_tac list; fastforce)
     apply (drule_tac x="hd list" in bspec, simp)+
     apply (intro conjI)
           apply (frule (4) ex_nonz_cap_to_tcb_in_waitingntfn, fastforce)
          apply (subgoal_tac "live (Notification ntfn)")
           apply (frule (2) if_live_then_nonz_capD2, simp)
          apply (clarsimp simp: live_def live_ntfn_def)
         apply (erule replies_blocked_upd_tcb_st_valid_replies, clarsimp)
         apply (clarsimp simp: replies_blocked_def st_tcb_at_def obj_at_def)
        apply (erule fault_tcbs_valid_states_not_fault_tcb_states)
        apply (clarsimp simp: st_tcb_at_def obj_at_def pred_neg_def)
       apply (erule delta_sym_refs_remove_only[where tp=TCBSignal], clarsimp)
        apply (rule subset_antisym, clarsimp)
        apply (clarsimp simp: state_refs_of_def is_tcb get_refs_def tcb_st_refs_of_def pred_tcb_at_def
                              obj_at_def)
        apply (force split: option.splits)
       apply (rule subset_antisym)
        apply (clarsimp simp: subset_remove ntfn_q_refs_of_def get_refs_def tcb_st_refs_of_def pred_tcb_at_def
                              obj_at_def state_refs_of_def)
        apply (clarsimp split: list.splits option.splits)
        apply (case_tac list; fastforce)
       apply (clarsimp simp: subset_remove ntfn_q_refs_of_def get_refs_def tcb_st_refs_of_def pred_tcb_at_def
                             obj_at_def state_refs_of_def)
       apply (clarsimp split: list.splits)
       apply (case_tac list; fastforce)
      apply (frule (3) not_idle_tcb_in_waitingntfn, fastforce)
     apply (rule valid_sched_scheduler_act_not_better, clarsimp simp: valid_sched_def)
     apply (clarsimp simp: st_tcb_at_def obj_at_def pred_neg_def)
    apply (clarsimp simp: st_tcb_at_def obj_at_def)
    apply (drule_tac x="hd list" in bspec; clarsimp)+
   apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def valid_tcb_state'_def
                   cong: conj_cong)
   apply (frule_tac t="hd list" in thread_state_tcb_in_WaitingNtfn'_q; assumption?)
    apply (clarsimp simp: valid_ntfn'_def)
   apply (intro conjI)
         apply clarsimp
        apply (clarsimp simp: valid_ntfn'_def)
       apply (erule (4) ex_nonz_cap_to'_tcb_in_WaitingNtfn'_q)
       apply (clarsimp simp: valid_ntfn'_def)
      apply (clarsimp simp: pred_tcb_at'_def obj_at'_def is_BlockedOnNotification_def)
     apply (clarsimp simp: valid_ntfn'_def)
     apply (drule_tac x="hd list" in bspec, rule hd_in_set, simp)+
     apply (clarsimp simp: valid_idle'_def invs'_def valid_state'_def idle_tcb'_def obj_at'_def
                           pred_tcb_at'_def receiveBlocked_def)
    apply (case_tac list; clarsimp simp: valid_ntfn'_def split: list.splits option.splits)
   apply (clarsimp)
   apply (erule if_live_then_nonz_capE')
   apply (clarsimp simp: ko_wp_at'_def obj_at'_real_def projectKO_ntfn live_ntfn'_def)
  \<comment> \<open>ActiveNtfn\<close>
  apply (clarsimp simp add: ntfn_relation_def Let_def)
  apply (rule corres_guard_imp)
    apply (rule set_ntfn_corres)
    apply (clarsimp simp: ntfn_relation_def combine_ntfn_badges_def)+
  done

lemma possibleSwitchTo_ksQ':
  "\<lbrace>\<lambda>s. t' \<notin> set (ksReadyQueues s p) \<and> sch_act_not t' s \<and> t' \<noteq> t\<rbrace>
     possibleSwitchTo t
   \<lbrace>\<lambda>_ s. t' \<notin> set (ksReadyQueues s p)\<rbrace>"
  apply (simp add: possibleSwitchTo_def curDomain_def bitmap_fun_defs inReleaseQueue_def)
  apply (wp static_imp_wp rescheduleRequired_ksQ' tcbSchedEnqueue_ksQ threadGet_wp
         | wpc
         | simp split del: if_split)+
  apply (auto simp: obj_at'_def)
  done

lemma possibleSwitchTo_iflive[wp]:
  "\<lbrace>if_live_then_nonz_cap' and ex_nonz_cap_to' t
           and (\<lambda>s. sch_act_wf (ksSchedulerAction s) s)\<rbrace>
     possibleSwitchTo t
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  apply (simp add: possibleSwitchTo_def curDomain_def inReleaseQueue_def)
  apply wpsimp
      apply (simp only: imp_conv_disj, wp hoare_vcg_all_lift hoare_vcg_disj_lift)
    apply (wp threadGet_wp)+
  by (fastforce simp: obj_at'_def projectKOs)

crunches replyUnlink, cleanReply
  for irqs_masked'[wp]: "irqs_masked'"
  (wp: crunch_wps)

lemma replyRemoveTCB_irqs_masked'[wp]:
  "replyRemoveTCB t \<lbrace> irqs_masked' \<rbrace>"
  unfolding replyRemoveTCB_def
  by (wpsimp wp: hoare_drop_imps gts_wp'|rule conjI)+

crunches sendSignal
  for ct'[wp]: "\<lambda>s. P (ksCurThread s)"
  and it'[wp]: "\<lambda>s. P (ksIdleThread s)"
  and irqs_masked'[wp]: "irqs_masked'"
  (wp: crunch_wps simp: crunch_simps o_def)

lemma ct_in_state_activatable_imp_simple'[simp]:
  "ct_in_state' activatable' s \<Longrightarrow> ct_in_state' simple' s"
  apply (simp add: ct_in_state'_def)
  apply (erule pred_tcb'_weakenE)
  apply (case_tac st; simp)
  done

lemma setThreadState_nonqueued_state_update:
  "\<lbrace>\<lambda>s. invs' s \<and> st_tcb_at' simple' t s
               \<and> simple' st
               \<and> (st \<noteq> Inactive \<longrightarrow> ex_nonz_cap_to' t s)
               \<and> (t = ksIdleThread s \<longrightarrow> idle' st)
               \<and> (\<not> runnable' st \<longrightarrow> sch_act_simple s)\<rbrace>
  setThreadState st t \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def valid_dom_schedule'_def)
  apply (rule hoare_pre, wp valid_irq_node_lift
                            sts_valid_queues
                            setThreadState_ct_not_inQ)
  apply (clarsimp simp: pred_tcb_at' pred_tcb_at'_eq_commute)
  apply (rule conjI, fastforce simp: valid_tcb_state'_def)
  apply (clarsimp simp: list_refs_of_replies'_def o_def pred_tcb_at'_def obj_at'_def)
  done

lemma cteDeleteOne_reply_cap_to'[wp]:
  "\<lbrace>ex_nonz_cap_to' p and
    cte_wp_at' (\<lambda>c. isReplyCap (cteCap c)) slot\<rbrace>
   cteDeleteOne slot
   \<lbrace>\<lambda>rv. ex_nonz_cap_to' p\<rbrace>"
  apply (simp add: cteDeleteOne_def ex_nonz_cap_to'_def unless_def)
  apply (rule hoare_seq_ext [OF _ getCTE_sp])
  apply (rule hoare_assume_pre)
  apply (subgoal_tac "isReplyCap (cteCap cte)")
   apply (wp hoare_vcg_ex_lift emptySlot_cte_wp_cap_other isFinalCapability_inv
        | clarsimp simp: finaliseCap_def isCap_simps | simp
        | wp (once) hoare_drop_imps)+
(*   apply (fastforce simp: cte_wp_at_ctes_of)
  apply (clarsimp simp: cte_wp_at_ctes_of isCap_simps)
  done*)
oops (* RT fixme: I think this is no longer true, and it currently isn't used anywhere*)

crunches possibleSwitchTo, asUser, doIPCTransfer
  for vms'[wp]: "valid_machine_state'"
  (wp: crunch_wps simp: zipWithM_x_mapM_x)

crunches activateIdleThread, isFinalCapability
  for nosch[wp]:  "\<lambda>s. P (ksSchedulerAction s)"
  (ignore: setNextPC simp: Let_def)

crunches asUser, setMRs, doIPCTransfer, possibleSwitchTo
  for pspace_domain_valid[wp]: "pspace_domain_valid"
  (wp: crunch_wps simp: zipWithM_x_mapM_x)

crunches doIPCTransfer, possibleSwitchTo
  for ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"
  (wp: crunch_wps simp: zipWithM_x_mapM)

lemma setThreadState_not_rct[wp]:
  "setThreadState st t
   \<lbrace>\<lambda>s. ksSchedulerAction s \<noteq> ResumeCurrentThread \<rbrace>"
  by (wpsimp wp: setThreadState_def)

lemma cancelAllIPC_not_rct[wp]:
  "\<lbrace>\<lambda>s. ksSchedulerAction s \<noteq> ResumeCurrentThread \<rbrace>
   cancelAllIPC epptr
   \<lbrace>\<lambda>_ s. ksSchedulerAction s \<noteq> ResumeCurrentThread \<rbrace>"
  apply (simp add: cancelAllIPC_def)
  apply (wpsimp wp: getEndpoint_wp)
  done

lemma cancelAllSignals_not_rct[wp]:
  "\<lbrace>\<lambda>s. ksSchedulerAction s \<noteq> ResumeCurrentThread \<rbrace>
   cancelAllSignals epptr
   \<lbrace>\<lambda>_ s. ksSchedulerAction s \<noteq> ResumeCurrentThread \<rbrace>"
  apply (simp add: cancelAllSignals_def)
  apply (wpsimp wp: getNotification_wp)
  done

crunches finaliseCapTrue_standin
  for not_rct[wp]: "\<lambda>s. ksSchedulerAction s \<noteq> ResumeCurrentThread"
  (simp: crunch_simps wp: crunch_wps)

crunches cleanReply
  for schedulerAction[wp]: "\<lambda>s. P (ksSchedulerAction s)"
  (simp: crunch_simps)

lemma replyUnlink_ResumeCurrentThread_imp_notct[wp]:
  "\<lbrace>\<lambda>s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t'\<rbrace>
   replyUnlink a b
   \<lbrace>\<lambda>_ s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t'\<rbrace>"
  apply (clarsimp simp: replyUnlink_def updateReply_def)
  apply (wpsimp wp: set_reply'.set_wp gts_wp')
  done

lemma replyRemoveTCB_ResumeCurrentThread_imp_notct[wp]:
  "\<lbrace>\<lambda>s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t'\<rbrace>
   replyRemoveTCB tptr
   \<lbrace>\<lambda>_ s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t'\<rbrace>"
  apply (clarsimp simp: replyRemoveTCB_def)
  apply (rule hoare_seq_ext_skip, solves \<open>wpsimp wp: getEndpoint_wp\<close>)+
  apply (rule hoare_seq_ext_skip)
   apply (clarsimp simp: when_def)
   apply (intro conjI impI)
    apply (wpsimp wp: set_sc'.set_wp set_reply'.set_wp hoare_vcg_imp_lift')+
  done

(* FIXME RT: This is not actually being used currently. I'll keep it here just in case *)
lemma cteDeleteOne_ResumeCurrentThread_imp_notct:
  "cteDeleteOne slot \<lbrace>\<lambda>s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t'\<rbrace>"
  (is "valid ?pre _ _")
  apply (simp add: cteDeleteOne_def unless_def split_def)
  apply wp
       apply (wp hoare_convert_imp)[1]
      apply wp
     apply (rule_tac Q="\<lambda>_. ?pre" in hoare_post_imp, clarsimp)
     apply (wpsimp wp: hoare_convert_imp isFinalCapability_inv)+
  done

lemma cancelSignal_ResumeCurrentThread_imp_notct[wp]:
  "cancelSignal t ntfn \<lbrace>\<lambda>s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t'\<rbrace>"
  (is "\<lbrace>?PRE t'\<rbrace> _ \<lbrace>_\<rbrace>")
  apply (simp add: cancelSignal_def)
  apply wp[1]
       apply (wp hoare_convert_imp)+
       apply (rule_tac P="\<lambda>s. ksSchedulerAction s \<noteq> ResumeCurrentThread"
                       in hoare_weaken_pre)
        apply (wpc)
         apply (wp | simp)+
      apply (wpc, wp+)
    apply (rule_tac Q="\<lambda>_. ?PRE t'" in hoare_post_imp, clarsimp)
    apply (wpsimp wp: stateAssert_wp)+
  done

lemma blockedCancelIPC_ResumeCurrentThread_imp_notct[wp]:
  "blockedCancelIPC a b c \<lbrace>\<lambda>s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t'\<rbrace>"
  unfolding blockedCancelIPC_def getBlockingObject_def
  apply (wpsimp wp: hoare_vcg_imp_lift' getEndpoint_wp)
  done

crunches cancelIPC
  for ResumeCurrentThread_imp_notct[wp]: "\<lambda>s. ksSchedulerAction s = ResumeCurrentThread
                                          \<longrightarrow> ksCurThread s \<noteq> t"

lemma tcbEPFindIndex_wp:
  "\<lbrace>\<lambda>s. (\<forall>i j. 0 \<le> i \<and> i \<le> Suc sz \<longrightarrow>
               (\<forall>tcb tcba. ko_at' tcb tptr s \<and> ko_at' tcba (queue ! j) s \<longrightarrow>
                           (Suc j = i \<longrightarrow> tcbPriority tcba \<ge> tcbPriority tcb) \<longrightarrow>
                           (i < j \<and> j \<le> sz \<longrightarrow> tcbPriority tcba < tcbPriority tcb) \<longrightarrow> Q i s))\<rbrace>
   tcbEPFindIndex tptr queue sz \<lbrace>Q\<rbrace>"
  apply (induct sz; subst tcbEPFindIndex.simps)
   apply (wpsimp wp: threadGet_wp)
   apply (clarsimp simp: obj_at'_def projectKO_eq projectKO_tcb)
  apply (wpsimp wp: threadGet_wp | assumption)+
  apply (clarsimp simp: obj_at'_def projectKO_eq projectKO_tcb)
  done

crunches tcbEPAppend, tcbEPDequeue
  for inv[wp]: P

lemma tcbEPAppend_rv_wf:
  "\<lbrace>\<top>\<rbrace> tcbEPAppend t q \<lbrace>\<lambda>rv s. set rv = set (t#q)\<rbrace>"
  apply (simp only: tcbEPAppend_def)
  apply (wp tcbEPFindIndex_wp)
  apply (auto simp: null_def set_append[symmetric])
  done

lemma tcbEPAppend_rv_wf':
  "\<lbrace>P (set (t#q))\<rbrace> tcbEPAppend t q \<lbrace>\<lambda>rv. P (set rv)\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (frule use_valid[OF _ tcbEPAppend_rv_wf], simp, simp)
  apply (frule use_valid[OF _ tcbEPAppend_inv, where P = "P (set (t#q))"], simp+)
  done

lemma tcbEPAppend_rv_wf'':
  "\<lbrace>P (ep_q_refs_of' (updateEpQueue ep (t#q))) and K (ep \<noteq> IdleEP)\<rbrace>
   tcbEPAppend t q
   \<lbrace>\<lambda>rv. P (ep_q_refs_of' (updateEpQueue ep rv))\<rbrace>"
  by (cases ep; wpsimp wp: tcbEPAppend_rv_wf' simp: updateEpQueue_def)

lemma tcbEPDequeue_rv_wf:
  "\<lbrace>\<lambda>_. t \<in> set q \<and> distinct q\<rbrace> tcbEPDequeue t q \<lbrace>\<lambda>rv s. set rv = set q - {t}\<rbrace>"
  apply (wpsimp simp: tcbEPDequeue_def)
  apply (fastforce dest: findIndex_member)
  done

lemma tcbEPDequeue_rv_wf':
  "\<lbrace>P (set q - {t}) and K (t \<in> set q \<and> distinct q)\<rbrace> tcbEPDequeue t q \<lbrace>\<lambda>rv. P (set rv)\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (frule use_valid[OF _ tcbEPDequeue_rv_wf], simp, simp)
  apply (frule use_valid[OF _ tcbEPDequeue_inv, where P = "P (set q - {t})"], simp+)
  done

lemma tcbEPDequeue_rv_wf'':
  "\<lbrace>P (ep_q_refs_of' (updateEpQueue ep q)) and K (t \<in> set q \<and> distinct q \<and> ep \<noteq> IdleEP)\<rbrace>
   tcbEPDequeue t q
   \<lbrace>\<lambda>rv. P (ep_q_refs_of' (updateEpQueue ep (t#rv)))\<rbrace>"
  by (cases ep; wpsimp wp: tcbEPDequeue_rv_wf' simp: Times_Diff_distrib1 insert_absorb updateEpQueue_def)

lemma tcbEPAppend_not_null[wp]:
  "\<lbrace>\<top>\<rbrace> tcbEPAppend t q \<lbrace>\<lambda>rv _. rv \<noteq> []\<rbrace>"
  by (wpsimp simp: tcbEPAppend_def split_del: if_split)

lemma tcbEPAppend_distinct[wp]:
  "\<lbrace>\<lambda>s. distinct q \<and> t \<notin> set q\<rbrace> tcbEPAppend t q \<lbrace>\<lambda>q' s. distinct q'\<rbrace>"
  apply (simp only: tcbEPAppend_def)
  apply (wpsimp wp: tcbEPFindIndex_wp)
  apply (auto simp: set_take_disj_set_drop_if_distinct dest: in_set_dropD in_set_takeD)
  done

lemma tcbEPAppend_valid_SendEP:
  "\<lbrace>valid_ep' (SendEP (t#q)) and K (t \<notin> set q)\<rbrace> tcbEPAppend t q \<lbrace>\<lambda>q'. valid_ep' (SendEP q')\<rbrace>"
  apply (simp only: tcbEPAppend_def)
  apply (case_tac q; wpsimp wp: tcbEPFindIndex_wp)
  apply (fastforce simp: valid_ep'_def set_take_disj_set_drop_if_distinct
                   dest: in_set_takeD in_set_dropD)
  done

lemma tcbEPAppend_valid_RecvEP:
  "\<lbrace>valid_ep' (RecvEP (t#q)) and K (t \<notin> set q)\<rbrace> tcbEPAppend t q \<lbrace>\<lambda>q'. valid_ep' (RecvEP q')\<rbrace>"
  apply (simp only: tcbEPAppend_def)
  apply (case_tac q; wpsimp wp: tcbEPFindIndex_wp)
  apply (fastforce simp: valid_ep'_def set_take_disj_set_drop_if_distinct
                   dest: in_set_takeD in_set_dropD)
  done

lemma tcbEPAppend_valid_ep':
  "\<lbrace>valid_ep' (updateEpQueue ep (t#q)) and K (ep \<noteq> IdleEP \<and> t \<notin> set q)\<rbrace>
   tcbEPAppend t q
   \<lbrace>\<lambda>q'. valid_ep' (updateEpQueue ep q')\<rbrace>"
  by (cases ep) (wpsimp wp: tcbEPAppend_valid_SendEP tcbEPAppend_valid_RecvEP simp: updateEpQueue_def)+

lemma tcbEPDequeue_valid_SendEP:
  "\<lbrace>valid_ep' (SendEP q) and K (t \<in> set q)\<rbrace> tcbEPDequeue t q \<lbrace>\<lambda>q'. valid_ep' (SendEP (t#q'))\<rbrace>"
  apply (wpsimp simp: tcbEPDequeue_def valid_ep'_def)
  apply (fastforce simp: findIndex_def findIndex'_app
                   dest: in_set_takeD in_set_dropD findIndex_member)
  done

lemma tcbEPDequeue_valid_RecvEP:
  "\<lbrace>valid_ep' (RecvEP q) and K (t \<in> set q)\<rbrace> tcbEPDequeue t q \<lbrace>\<lambda>q'. valid_ep' (RecvEP (t#q'))\<rbrace>"
  apply (wpsimp simp: tcbEPDequeue_def valid_ep'_def)
  apply (fastforce simp: findIndex_def findIndex'_app
                   dest: in_set_takeD in_set_dropD findIndex_member)
  done

lemma tcbEPDequeue_valid_ep':
  "\<lbrace>valid_ep' (updateEpQueue ep q) and K (ep \<noteq> IdleEP \<and> t \<in> set q)\<rbrace>
   tcbEPDequeue t q
   \<lbrace>\<lambda>q'. valid_ep' (updateEpQueue ep (t#q'))\<rbrace>"
  by (cases ep) (wpsimp wp: tcbEPDequeue_valid_SendEP tcbEPDequeue_valid_RecvEP simp: updateEpQueue_def)+

crunches doIPCTransfer
  for urz[wp]: "untyped_ranges_zero'"
  (ignore: threadSet wp: threadSet_urz crunch_wps simp: zipWithM_x_mapM)

crunches receiveIPC
  for gsUntypedZeroRanges[wp]: "\<lambda>s. P (gsUntypedZeroRanges s)"
  (wp: crunch_wps transferCapsToSlots_pres1 hoare_vcg_all_lift
   simp: crunch_simps zipWithM_x_mapM ignore: constOnFailure)

lemmas possibleSwitchToTo_cteCaps_of[wp]
    = cteCaps_of_ctes_of_lift[OF possibleSwitchTo_ctes_of]

lemma setThreadState_Running_invs':
  "\<lbrace>\<lambda>s. invs' s \<and> tcb_at' t s \<and> ex_nonz_cap_to' t s
        \<and> st_tcb_at' (Not \<circ> is_BlockedOnReply) t s\<rbrace>
   setThreadState Running t
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (wpsimp wp: sts_invs')
  apply (simp add: invs'_def valid_state'_def valid_dom_schedule'_def pred_tcb_at'_eq_commute)
  apply (fastforce dest: global'_no_ex_cap
                   simp: o_def pred_tcb_at'_def obj_at'_def)
  done

lemma setThreadState_BlockedOnReceive_invs':
  "\<lbrace>\<lambda>s. invs' s \<and> tcb_at' t s \<and> ep_at' eptr s \<and> ex_nonz_cap_to' t s \<and>
        valid_bound_reply' rptr s \<and> sch_act_not t s \<and> t \<noteq> ksIdleThread s \<and>
        st_tcb_at' (Not \<circ> is_BlockedOnReply) t s\<rbrace>
   setThreadState (BlockedOnReceive eptr cg rptr) t
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def valid_dom_schedule'_def)
  apply (wpsimp wp: sts_sch_act' setThreadState_ct_not_inQ valid_irq_node_lift simp: pred_tcb_at'_eq_commute)
  apply (clarsimp dest: global'_no_ex_cap
                  simp: valid_tcb_state'_def comp_def pred_tcb_at'_def obj_at'_def)
  done

lemma ksReleaseQueue_ksReprogramTimer_update:
  "ksReleaseQueue_update (\<lambda>_. fv) (ksReprogramTimer_update (\<lambda>_. gv) s) =
   ksReprogramTimer_update (\<lambda>_. gv) (ksReleaseQueue_update (\<lambda>_. fv) s)"
  by simp

lemma ksPSpace_ksReprogramTimer_update:
  "ksPSpace_update (\<lambda>_. fv) (ksReprogramTimer_update (\<lambda>_. gv) s) =
   ksReprogramTimer_update (\<lambda>_. gv) (ksPSpace_update (\<lambda>_. fv) s)"
  by simp

lemma tcbReleaseEnqueue_invs'[wp]:
  "tcbReleaseEnqueue tcb \<lbrace>invs'\<rbrace>"
  apply (clarsimp simp: getScTime_def getTCBSc_def tcbReleaseEnqueue_def
                        getReleaseQueue_def setReleaseQueue_def setReprogramTimer_def)
  apply (clarsimp simp add: invs'_def valid_state'_def valid_dom_schedule'_def split del: if_split)
  apply (wp threadSet_valid_pspace'T threadSet_sch_actT_P[where P=False, simplified]
           threadSet_iflive'T threadSet_ifunsafe'T threadSet_idle'T threadSet_not_inQ
           valid_irq_node_lift valid_irq_handlers_lift'' threadSet_ct_idle_or_in_cur_domain'
           threadSet_cur untyped_ranges_zero_lift threadSet_valid_queues threadSet_valid_queues'
         | rule refl threadSet_wp [THEN hoare_vcg_conj_lift]
         | clarsimp simp: tcb_cte_cases_def cteCaps_of_def)+
     apply (clarsimp simp: ksReleaseQueue_ksReprogramTimer_update
                           ksPSpace_ksReprogramTimer_update if_cancel_eq_True)
     apply (wpsimp wp: mapM_wp_lift getScTime_wp threadGet_wp)+
  apply (clarsimp simp: invs'_def valid_state'_def comp_def obj_at'_def inQ_def cteCaps_of_def)
  apply (intro conjI)
      apply (clarsimp simp: valid_release_queue_def obj_at'_def projectKOs objBitsKO_def)+
   apply (intro conjI impI; clarsimp)
       apply (auto split: if_splits elim: ps_clear_domE)[3]
    apply (drule_tac x=a in spec, drule mp)
     apply (rule_tac ys=rvs in tup_in_fst_image_set_zipD)
     apply (clarsimp simp: image_def)
     apply (rule_tac x="(a,b)" in bexI)
      apply (auto split: if_splits elim: ps_clear_domE)[3]
   apply (drule_tac x=a in spec, drule mp)
    apply (rule_tac ys=rvs in tup_in_fst_image_set_zipD)
    apply (clarsimp simp: image_def)
    apply (rule_tac x="(a,b)" in bexI)
     apply (auto split: if_splits elim: ps_clear_domE)[3]
  apply (clarsimp simp: valid_release_queue'_def)
  apply (erule_tac x=t in allE)
  apply (drule mp)
   apply (fastforce simp: obj_at'_def projectKO_eq projectKO_tcb objBitsKO_def inQ_def
                    elim: ps_clear_domE split: if_splits)
  apply (clarsimp simp: image_def in_set_conv_decomp zip_append1)
  apply (rule_tac x="hd (drop (length ys) rvs)" in exI)
  apply (case_tac "drop (length ys) rvs"; fastforce dest: list_all2_lengthD)
  done

crunches postpone, schedContextResume
  for invs'[wp]: invs'
  (wp: crunch_wps)

lemma maybeDonateSc_invs':
  "\<lbrace>invs' and ex_nonz_cap_to' tptr\<rbrace> maybeDonateSc tptr nptr \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp only: maybeDonateSc_def)
  apply (wpsimp wp: refillUnblockCheck_invs' schedContextDonate_invs'
                    getNotification_wp threadGet_wp)
  apply (clarsimp simp: pred_tcb_at'_def obj_at'_def projectKOs sym_refs_asrt_def)
  apply (rename_tac tcb)
  apply (rule_tac x=tcb in exI, clarsimp)
  apply (erule if_live_then_nonz_capE'[OF invs_iflive'])
  apply (drule_tac ko="ntfn :: notification" for ntfn in sym_refs_ko_atD'[rotated])
   apply (fastforce simp: obj_at'_def projectKOs)
  apply (auto simp: refs_of_rev' ko_wp_at'_def live_sc'_def)
  done

lemma simple'_not_is_BlockedOnReply:
  "simple' st \<Longrightarrow> \<not> is_BlockedOnReply st"
  by (clarsimp simp: is_BlockedOnReply_def)

lemma sai_invs'[wp]:
  "\<lbrace>invs' and ex_nonz_cap_to' ntfnptr\<rbrace> sendSignal ntfnptr badge \<lbrace>\<lambda>y. invs'\<rbrace>"
  (is "valid ?pre _ _")
  apply (simp add: sendSignal_def)
  apply (rule hoare_seq_ext[OF _ stateAssert_sp])
  apply (rule hoare_seq_ext[OF _ get_ntfn_sp'])
  apply (rule_tac Q="?pre and ko_at' nTFN ntfnptr and valid_ntfn' nTFN and sym_refs_asrt
                          and (\<lambda>s. sym_refs (state_refs_of' s))" in hoare_weaken_pre)
   apply (case_tac "ntfnObj nTFN"; clarsimp)
     \<comment> \<open>IdleNtfn\<close>
     apply (case_tac "ntfnBoundTCB nTFN"; clarsimp)
      apply (wp setNotification_invs')
      apply (clarsimp simp: valid_ntfn'_def)
     apply (wp isSchedulable_wp)
           apply (rule_tac Q="\<lambda>_. invs'" in hoare_strengthen_post[rotated])
            apply (clarsimp simp: isSchedulable_bool_def isSchedulable_bool_runnableE)
           apply (wpsimp wp: maybeDonateSc_invs' setThreadState_Running_invs'
                             setNotification_invs' gts_wp' cancelIPC_simple
                       simp: o_def
                  | strengthen pred_tcb'_weakenE[mk_strg I _ O],
                    rule simple'_not_is_BlockedOnReply, assumption)+
     apply (clarsimp simp: valid_ntfn'_def cong: conj_cong)
     apply (erule if_live_then_nonz_capE'[OF invs_iflive'])
     apply (drule_tac ko="ntfn :: notification" for ntfn in sym_refs_ko_atD'[rotated])
      apply fastforce
     apply (fastforce simp: refs_of_rev' ko_wp_at'_def)
    \<comment> \<open>ActiveNtfn\<close>
    apply (wpsimp wp: setNotification_invs' simp: valid_ntfn'_def)
   \<comment> \<open>WaitingNtfn\<close>
   apply (rename_tac list)
   apply (case_tac list; clarsimp)
   apply (wp isSchedulable_wp)
       apply (rule_tac Q="\<lambda>_. invs'" in hoare_strengthen_post[rotated])
        apply (clarsimp simp: isSchedulable_bool_def isSchedulable_bool_runnableE)
       apply (wp maybeDonateSc_invs' setThreadState_Running_invs' setNotification_invs')+
   apply (clarsimp cong: conj_cong simp: valid_ntfn'_def)
   apply (rule conjI)
    apply (clarsimp split: option.splits list.splits)
   apply (rule conjI)
    apply (erule if_live_then_nonz_capE'[OF invs_iflive'])
    apply (drule_tac ko="ntfn :: notification" for ntfn in sym_refs_ko_atD'[rotated])
     apply fastforce
    apply (fastforce simp: refs_of_rev' ko_wp_at'_def)
   apply (erule (1) thread_state_tcb_in_WaitingNtfn'_q[THEN pred_tcb'_weakenE]; fastforce?)
  \<comment> \<open>resolve added preconditions\<close>
  apply (clarsimp simp: sym_refs_asrt_def)
  apply (erule_tac x=ntfnptr in valid_objsE'[OF invs_valid_objs'])
   apply (fastforce simp: obj_at'_def projectKOs)
  apply (fastforce simp: valid_obj'_def valid_ntfn'_def)
  done

lemma rfk_corres:
  "corres dc (tcb_at t and invs) (tcb_at' t and invs')
             (reply_from_kernel t r) (replyFromKernel t r)"
  apply (case_tac r)
  apply (clarsimp simp: replyFromKernel_def reply_from_kernel_def
                        badge_register_def badgeRegister_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqr [OF _ lipcb_corres])
      apply (rule corres_split_deprecated [OF _ user_setreg_corres])
        apply (rule corres_split_eqr [OF _ set_mrs_corres])
           apply (rule set_mi_corres)
           apply (wp hoare_case_option_wp hoare_valid_ipc_buffer_ptr_typ_at'
                  | clarsimp)+
  done

lemma rfk_invs':
  "\<lbrace>invs' and tcb_at' t\<rbrace> replyFromKernel t r \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: replyFromKernel_def)
  apply (cases r)
  apply wpsimp
  done

crunch nosch[wp]: replyFromKernel "\<lambda>s. P (ksSchedulerAction s)"

lemma complete_signal_corres:
  "corres dc (ntfn_at ntfnptr and tcb_at tcb and pspace_aligned and valid_objs
             \<comment> \<open>and obj_at (\<lambda>ko. ko = Notification ntfn \<and> Ipc_A.isActive ntfn) ntfnptr*\<close> )
             (ntfn_at' ntfnptr and tcb_at' tcb and valid_pspace' and obj_at' isActive ntfnptr)
             (complete_signal ntfnptr tcb) (completeSignal ntfnptr tcb)"
  apply (simp add: complete_signal_def completeSignal_def)
  apply (rule corres_guard_imp)
    apply (rule_tac R'="\<lambda>ntfn. ntfn_at' ntfnptr and tcb_at' tcb and valid_pspace'
                         and valid_ntfn' ntfn and (\<lambda>_. isActive ntfn)"
                                in corres_split_deprecated [OF _ get_ntfn_corres])
      apply (rule corres_gen_asm2)
      apply (case_tac "ntfn_obj rv")
        apply (clarsimp simp: ntfn_relation_def isActive_def
                       split: ntfn.splits Structures_H.notification.splits)+
      apply (rule corres_guard2_imp)
       apply (simp add: badgeRegister_def badge_register_def)
       apply (rule corres_split_deprecated[OF set_ntfn_corres user_setreg_corres])
         apply (clarsimp simp: ntfn_relation_def)
        apply (wp set_simple_ko_valid_objs get_simple_ko_wp getNotification_wp | clarsimp simp: valid_ntfn'_def)+
  apply (clarsimp simp: valid_pspace'_def)
  apply (rename_tac ntfn)
  apply (frule_tac P="(\<lambda>k. k = ntfn)" in obj_at_valid_objs', assumption)
  apply (clarsimp simp: projectKOs valid_obj'_def valid_ntfn'_def obj_at'_def)
  done

lemma ntfn_relation_par_inj:
  "ntfn_relation ntfn ntfn' \<Longrightarrow> ntfn_sc ntfn = ntfnSc ntfn'"
  by (simp add: ntfn_relation_def)

lemma set_sc_obj_ref_ko_not_tcb_at[wp]:
  "set_sc_obj_ref f scp v \<lbrace>\<lambda>s. \<not> ko_at (TCB tcb) t s\<rbrace>"
  by (wpsimp simp: update_sched_context_def set_object_def obj_at_def pred_neg_def
               wp: get_object_wp)

lemma set_sc_obj_ref_valid_tcb[wp]:
  "set_sc_obj_ref f scp v \<lbrace>valid_tcb ptr tcb\<rbrace>"
  by (wpsimp wp: get_object_wp simp: update_sched_context_def)

lemma set_sc_obj_ref_valid_tcbs[wp]:
  "set_sc_obj_ref f scp v \<lbrace>valid_tcbs\<rbrace>"
  unfolding valid_tcbs_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift')

lemma valid_tcbs_valid_tcbE:
  assumes "tcb_at t s"
          "valid_tcbs s"
          "\<And>tcb. ko_at (TCB tcb) t s \<Longrightarrow> valid_tcb t tcb s \<Longrightarrow> R s (TCB tcb)"
  shows "obj_at (R s) t s"
  using assms
  apply (clarsimp simp: obj_at_def)
  apply (rename_tac ko)
  apply (case_tac ko; clarsimp simp: is_tcb_def)
  apply (rename_tac tcb)
  apply (prop_tac "valid_tcb t tcb s")
   apply (clarsimp simp: valid_tcbs_def)
   apply (drule_tac x=t in spec)
   apply (drule_tac x=tcb in spec)
   apply (clarsimp simp: obj_at_def)
  apply clarsimp
  done

lemma thread_set_weak_valid_sched_action2:
  "\<lbrace>weak_valid_sched_action and scheduler_act_not tptr\<rbrace> thread_set f tptr \<lbrace>\<lambda>rv. weak_valid_sched_action\<rbrace>"
  apply (wpsimp wp: thread_set_wp simp: obj_at_kh_kheap_simps vs_all_heap_simps fun_upd_def
                    weak_valid_sched_action_def)
  apply (clarsimp simp: weak_valid_sched_action_def scheduler_act_not_def)
  apply (rule_tac x=ref' in exI; clarsimp)
  done

lemma notQueued_cross_rel:
  "cross_rel (not_queued t) (notQueued t)"
  unfolding cross_rel_def state_relation_def
  by (clarsimp simp: notQueued_def ready_queues_relation_def not_queued_def)

lemma valid_tcb_sched_context_update_empty[elim!]:
  "valid_tcb tp tcb s \<Longrightarrow> valid_tcb tp (tcb_sched_context_update Map.empty tcb) s"
  by (auto simp: valid_tcb_def tcb_cap_cases_def)

lemma valid_tcb'_SchedContext_update_empty[elim!]:
  "valid_tcb' tcb s' \<Longrightarrow> valid_tcb' (tcbSchedContext_update Map.empty tcb) s'"
  by (auto simp: valid_tcb'_def valid_cap'_def tcb_cte_cases_def)

lemma maybeReturnSc_corres:
  "corres dc
   (ntfn_at ntfnPtr and tcb_at thread and valid_tcbs and pspace_aligned
      and scheduler_act_not thread
      and pspace_distinct and weak_valid_sched_action
      and not_queued thread and not_in_release_q thread
      and (\<lambda>s. sym_refs (state_refs_of s)))
   (valid_tcbs' and valid_queues and valid_queues' and valid_release_queue_iff)
   (maybe_return_sc ntfnPtr thread)
   (maybeReturnSc ntfnPtr thread)"
  unfolding maybe_return_sc_def maybeReturnSc_def
  apply add_sym_refs
  apply (rule corres_stateAssert_assume)
   apply (clarsimp simp: liftM_def get_sk_obj_ref_def get_tcb_obj_ref_def
                         set_tcb_obj_ref_thread_set)
   apply (rule stronger_corres_guard_imp)
     apply (rule corres_split_deprecated [OF _ get_ntfn_corres])
       apply (frule ntfn_relation_par_inj[symmetric], simp)
       apply (rule corres_split_deprecated [OF _ threadget_corres[where r="(=)"]])
          apply (rule corres_when2, simp)
          apply (rule corres_assert_opt_assume_l)
          apply (rule corres_split_deprecated [OF _ threadset_corresT])
               apply (rule_tac Q'="\<top>" in corres_symb_exec_r')
                  apply (rule corres_split_deprecated)
                     prefer 2
                     apply (rule update_sc_no_reply_stack_update_ko_at'_corres
                                 [where f'="scTCB_update (\<lambda>_. None)"])
                        apply ((clarsimp simp: sc_relation_def objBits_def objBitsKO_def)+)[4]
                    apply (rule corres_split_deprecated [OF _ gct_corres])
                      apply (rule corres_when [OF _ rescheduleRequired_corres], simp)
                     apply (wpsimp wp: hoare_vcg_imp_lift')+
              apply (clarsimp simp: tcb_relation_def)
             apply (rule ball_tcb_cap_casesI; simp)
            apply (clarsimp simp: tcb_cte_cases_def)
           apply (wpsimp wp: hoare_vcg_imp_lift' thread_set_weak_valid_sched_action2)
          apply (wpsimp wp: hoare_drop_imp threadSet_valid_queues_no_state
                            threadSet_valid_queues' threadSet_valid_release_queue
                            threadSet_valid_tcbs'
                            threadSet_valid_release_queue')
         apply (clarsimp simp: tcb_relation_def)
        apply (wpsimp wp: thread_get_wp threadGet_wp)+
       apply (frule ntfn_relation_par_inj, simp)
      apply (wpsimp wp: get_simple_ko_wp getNotification_wp)+
    apply (rule valid_tcbs_valid_tcbE, simp, simp)
    apply (clarsimp simp: valid_tcb_def valid_bound_obj_def split: option.splits)
   apply (rule cross_rel_srE [OF tcb_at'_cross_rel [where t=thread]]; simp)
   apply (rule cross_rel_srE [OF ntfn_at'_cross_rel [where t=ntfnPtr]], simp)
   apply (rule cross_rel_srE [OF notQueued_cross_rel [where t=thread]], simp)
   apply clarsimp
   apply (subgoal_tac "\<exists>tcb. ko_at' (tcb :: tcb) thread s'", clarsimp)
    apply (rule_tac x=tcb in exI, clarsimp)
    apply (clarsimp simp: notQueued_def)
    apply (clarsimp simp: valid_release_queue'_def inQ_def)
    apply (intro conjI)
      apply clarsimp
     apply (clarsimp simp: obj_at'_def valid_release_queue'_def)
    apply (subgoal_tac "valid_tcb' tcb s'")
     apply (clarsimp simp: valid_tcb'_def valid_bound_obj'_def split: option.splits)
    apply (clarsimp simp: valid_tcbs'_def obj_at'_real_def ko_wp_at'_def projectKO_tcb)
   apply (clarsimp simp: obj_at'_def)
  apply (clarsimp simp: sym_refs_asrt_def)
  done

lemma tcbEPDequeue_corres:
  "qs = qs' \<Longrightarrow> corres (=) \<top> \<top> (tcb_ep_dequeue t qs) (tcbEPDequeue t qs')"
  by (clarsimp simp: tcb_ep_dequeue_def tcbEPDequeue_def)

lemma doNBRecvFailedTransfer_corres:
  "corres dc (pspace_aligned and pspace_distinct and tcb_at thread) \<top>
             (do_nbrecv_failed_transfer thread) (doNBRecvFailedTransfer thread)"
  apply (rule corres_cross[where Q' = "tcb_at' thread", OF tcb_at'_cross_rel], simp)
  apply (clarsimp simp: do_nbrecv_failed_transfer_def doNBRecvFailedTransfer_def)
  apply (rule corres_guard_imp)
    apply (clarsimp simp: badge_register_def badgeRegister_def)
    apply (rule user_setreg_corres)
   apply clarsimp+
  done

crunches maybe_return_sc
  for tcb_at[wp]: "tcb_at thread"
  (wp: crunch_wps simp: crunch_simps)

lemma maybeReturnSc_valid_objs'[wp]:
  "maybeReturnSc ntfnPtr tcbPtr \<lbrace>valid_objs'\<rbrace>"
  apply (clarsimp simp: maybeReturnSc_def)
  apply (wpsimp wp: threadSet_valid_objs' threadGet_wp getNotification_wp
                    hoare_vcg_all_lift hoare_vcg_imp_lift')
  apply (clarsimp dest!: ntfn_ko_at_valid_objs_valid_ntfn'
                   simp: obj_at'_def projectKOs)
  apply (rename_tac tcb)
  apply (rule_tac x=tcb in exI)
  apply clarsimp
  apply (rename_tac sc sc_ptr)
  apply (prop_tac "ko_at' sc (the (tcbSchedContext tcb)) s")
   apply (clarsimp simp: obj_at'_def projectKOs)
  apply (fastforce dest!: sc_ko_at_valid_objs_valid_sc'
                    simp: valid_sched_context'_def valid_sched_context_size'_def objBits_simps)
  done

lemma maybeReturnSc_valid_tcbs'[wp]:
  "maybeReturnSc ntfnPtr tcbPtr \<lbrace>valid_tcbs'\<rbrace>"
  apply (clarsimp simp: maybeReturnSc_def)
  apply (wpsimp wp: threadSet_valid_tcbs' threadGet_wp getNotification_wp
                    hoare_vcg_all_lift hoare_vcg_imp_lift')
  apply (fastforce simp: obj_at'_def projectKOs)
  done

lemma maybe_return_sc_valid_tcbs[wp]:
  "\<lbrace>valid_tcbs and tcb_at tcb_ptr\<rbrace>
   maybe_return_sc ntfn_ptr tcb_ptr
   \<lbrace>\<lambda>_. valid_tcbs\<rbrace>"
  apply (clarsimp simp: maybe_return_sc_def)
  apply (wpsimp wp: set_object_valid_tcbs thread_get_wp get_simple_ko_wp
              simp: set_tcb_obj_ref_def get_tcb_obj_ref_def get_sk_obj_ref_def)
  apply (clarsimp simp: obj_at_def is_tcb_def valid_tcbs_def)
  apply (fastforce simp: get_tcb_def
                  split: Structures_A.kernel_object.splits)
  done

lemma maybeReturnSc_valid_queues:
  "\<lbrace>valid_queues and valid_tcbs'\<rbrace>
   maybeReturnSc ntfnPtr tcbPtr
   \<lbrace>\<lambda>_. valid_queues\<rbrace>"
  apply (clarsimp simp: maybeReturnSc_def)
  apply (wpsimp wp: hoare_drop_imps)
     apply (wpsimp wp: threadSet_valid_queues_new hoare_vcg_if_lift2
                       getNotification_wp threadGet_wp)+
  apply (clarsimp simp: obj_at'_def inQ_def)
  done

crunches maybeReturnSc
  for valid_queues'[wp]: valid_queues'
  and valid_release_queue[wp]: valid_release_queue
  (wp: crunch_wps simp: crunch_simps inQ_def)

lemma maybeReturnSc_valid_release_queue':
  "\<lbrace>valid_release_queue' and valid_tcbs'\<rbrace>
   maybeReturnSc ntfnPtr tcbPtr
   \<lbrace>\<lambda>_. valid_release_queue'\<rbrace>"
  (is "valid ?pre _ _")
  apply (clarsimp simp: maybeReturnSc_def liftM_def)
  apply (rule hoare_seq_ext[OF _ stateAssert_sp])
  apply (rule hoare_seq_ext[OF _ get_ntfn_sp'])
  apply (rule hoare_seq_ext[OF _ threadGet_sp])
  apply (rule hoare_when_cases; clarsimp)
  apply (rule_tac B="\<lambda>_. ?pre" in hoare_seq_ext[rotated])
   apply (wpsimp wp: threadSet_valid_release_queue' threadSet_valid_objs')
   apply (clarsimp simp: obj_at'_def valid_release_queue'_def)
  apply wpsimp
  done

lemma maybe_return_sc_weak_valid_sched_action:
  "\<lbrace>weak_valid_sched_action and scheduler_act_not tcb_ptr and tcb_at tcb_ptr\<rbrace>
   maybe_return_sc ntfn_ptr tcb_ptr
   \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  apply (clarsimp simp: maybe_return_sc_def)
  apply (wpsimp wp: set_object_wp thread_get_wp get_simple_ko_wp
              simp: set_tcb_obj_ref_def get_tcb_obj_ref_def get_sk_obj_ref_def)
  apply (clarsimp simp: obj_at_def is_tcb_def)
  apply (rename_tac tcb, case_tac tcb; clarsimp)
  apply (fastforce simp: weak_valid_sched_action_def scheduler_act_not_def vs_all_heap_simps)
  done

lemma maybeReturnSc_invs':
  "\<lbrace>invs' and (\<lambda>s. tptr \<noteq> ksIdleThread s)\<rbrace> maybeReturnSc nptr tptr \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (wpsimp wp: setSchedContext_invs' simp: maybeReturnSc_def)
      apply (clarsimp simp add: invs'_def valid_state'_def split del: if_split)
      apply (wp threadSet_valid_pspace'T threadSet_sch_actT_P[where P=False, simplified]
                threadSet_ctes_of threadSet_iflive'T threadSet_ifunsafe'T threadSet_idle'T
                threadSet_not_inQ valid_irq_node_lift valid_irq_handlers_lift'' threadSet_cur
                threadSet_ct_idle_or_in_cur_domain' untyped_ranges_zero_lift threadSet_cap_to'
                threadSet_valid_queues threadSet_valid_queues' threadSet_valid_release_queue
                threadSet_valid_release_queue' threadGet_wp getNotification_wp
                hoare_vcg_imp_lift' hoare_vcg_all_lift valid_dom_schedule'_lift
             | clarsimp simp: tcb_cte_cases_def cteCaps_of_def)+
  apply (clarsimp simp: obj_at'_def projectKOs)
  apply (rename_tac ntfn tcb)
  apply (rule_tac x=tcb in exI)
  apply (clarsimp simp: invs'_def valid_state'_def inQ_def comp_def eq_commute[where a="Some _"])
  apply (intro conjI impI allI; clarsimp?)
        apply (fastforce simp: valid_release_queue'_def obj_at'_def projectKOs)
       apply (fastforce simp: valid_release_queue'_def obj_at'_def projectKOs)
      apply (clarsimp simp: untyped_ranges_zero_inv_def cteCaps_of_def comp_def)
     apply (clarsimp simp: valid_idle'_def obj_at'_def projectKOs sym_refs_asrt_def)
     apply (drule_tac ko="tcb" and p=tptr in sym_refs_ko_atD'[rotated])
      apply (fastforce simp: obj_at'_def projectKOs)
     apply (clarsimp simp: ko_wp_at'_def refs_of_rev')
    apply (fastforce elim: if_live_then_nonz_capE' simp: ko_wp_at'_def live_sc'_def)
   apply (fastforce simp: valid_pspace'_def valid_obj'_def valid_sched_context'_def)
  apply (fastforce simp: valid_obj'_def valid_sched_context_size'_def objBits_def objBitsKO_def)
  done

crunches doIPCTransfer
  for pspace_aligned'[wp]: pspace_aligned'
  and pspace_distinct'[wp]: pspace_distinct'
  and no_0_obj'[wp]: no_0_obj'
  and vrq[wp]: valid_release_queue
  and vrq'[wp]: valid_release_queue'
  (wp: crunch_wps simp: zipWithM_x_mapM_x)

definition receiveIPC_preamble where
  "receiveIPC_preamble replyCap thread \<equiv>
    case replyCap of NullCap \<Rightarrow> return Nothing
                 | ReplyCap r _ \<Rightarrow>
                 (do tptrOpt <- liftM replyTCB (getReply (r));
                     when (tptrOpt \<noteq> Nothing \<and> tptrOpt \<noteq> Some thread) $ cancelIPC (the tptrOpt);
                     return (Just r)
                  od)
                 | _ \<Rightarrow> haskell_fail []"

crunches maybe_return_sc
  for ep_at[wp]: "ep_at epptr"
  (wp: crunch_wps simp: crunch_simps)

lemma thread_set_cap_to_fault_helper:
  "(a, b, c) \<in> ran tcb_cap_cases \<Longrightarrow> a (tcb_fault_update h tcb) = a tcb"
  by (clarsimp simp: tcb_cap_cases_def, fastforce)

crunches cancel_ipc
  for ep_at[wp]: "ep_at epptr"
  and reply_at[wp]: "reply_at rptr"
  and ex_nonz_cap_to[wp]: "ex_nonz_cap_to t"
  (simp: crunch_simps thread_set_cap_to_fault_helper
     wp: crunch_wps thread_set_cap_to)

crunches doIPCTransfer
  for replySCs_of[wp]: "\<lambda>s. P (replySCs_of s)"
  and replyTCBs_of[wp]: "\<lambda>s. P (replyTCBs_of s)"
  (wp: crunch_wps simp: zipWithM_x_mapM_x)

crunches receive_ipc_preamble
  for ep_at[wp]: "ep_at epptr"
  and valid_list[wp]: valid_list
  and tcb_at[wp]: "tcb_at t"
  and ex_nonz_cap_to[wp]: "ex_nonz_cap_to epptr"
  and idle_thread[wp]: "\<lambda>s. P (idle_thread s)"
  and cte_wp_at[wp]: "cte_wp_at P x"

crunches receiveIPC_preamble
  for ep_at'[wp]: "ep_at' epptr"
  and tcb_at'[wp]: "tcb_at' t"
  and invs'[wp]: invs'

lemma receiveIPC_preamble_vbreply'[wp]:
  "\<lbrace>\<top>\<rbrace> receiveIPC_preamble replyCap thread \<lbrace>valid_bound_reply'\<rbrace>"
  unfolding receiveIPC_preamble_def
  by (case_tac replyCap; wpsimp)

lemma receiveIPC_preamble_corres:
  assumes "cap_relation reply_cap replyCap"
      and "is_reply_cap reply_cap \<or> (reply_cap = cap.NullCap)"
  shows "corres (=) (invs and valid_ready_qs and valid_cap reply_cap) invs'
     (receive_ipc_preamble reply_cap thread)
     (receiveIPC_preamble replyCap thread)"
  supply if_split [split del]
  apply (insert assms)
  apply (clarsimp simp: receive_ipc_preamble_def receiveIPC_preamble_def)
  apply (case_tac reply_cap; simp add: is_reply_cap_def)
  apply (rule stronger_corres_guard_imp)
    apply (clarsimp simp: liftM_def)
    apply (rule corres_split[OF get_reply_corres])
      apply (rule corres_split[OF _ corres_return_eq_same[OF refl], where r'=dc])
        apply (rule corres_when2)
         apply (clarsimp simp: reply_relation_def)
         apply (rename_tac r, case_tac "replyTCB r"; simp)
        apply (rename_tac r r')
        apply (subgoal_tac "replyTCB r' = reply_tcb r", simp)
         apply (rule cancel_ipc_corres)
        apply (clarsimp simp: reply_relation_def)
       apply wpsimp
      apply wpsimp
     apply (wpsimp wp: get_simple_ko_wp)
    apply (wpsimp wp: getReply_wp)
   apply (clarsimp simp: valid_cap_def)
   apply (frule (1) valid_objs_ko_at[OF invs_valid_objs])
   apply (clarsimp simp: valid_obj_def valid_reply_def)
  apply (clarsimp simp: valid_cap_def)
  apply (erule cross_relF[OF _ reply_at'_cross_rel])
  apply fastforce
  done

lemma ri_preamble_vbreply:
  "receive_ipc_preamble_rv reply_cap replyOpt s \<Longrightarrow> valid_bound_reply replyOpt s"
  by (case_tac replyOpt; clarsimp elim!: reply_at_ppred_reply_at)

lemma ri_preamble_not_in_sc:
  "\<lbrakk>sym_refs (state_refs_of s);
    valid_replies s;
    receive_ipc_preamble_rv reply_cap replyOpt s\<rbrakk>
   \<Longrightarrow> valid_bound_obj (\<lambda>a b. a \<notin> fst ` replies_with_sc b) replyOpt s"
  apply (case_tac replyOpt; simp)
  apply (erule (1) no_tcb_not_in_replies_with_sc, simp)
  done

lemma receiveIPC_corres_helper:
  "(do replyOpt <-
                 case replyCap of capability.NullCap \<Rightarrow> return Nothing
                 | capability.ReplyCap r v18 \<Rightarrow> return (Just r)
                 | _ \<Rightarrow> haskell_fail [];
                 y <-
                 when (\<exists>y. replyOpt = Some y)
                  (do tptrOpt <- liftM replyTCB (getReply (the replyOpt));
                      when ((\<exists>y. tptrOpt = Some y) \<and> tptrOpt \<noteq> Some thread)
                       (cancelIPC (the tptrOpt))
                   od);
                 f replyOpt
          od) = (do replyOpt <-
                 case replyCap of capability.NullCap \<Rightarrow> return Nothing
                 | capability.ReplyCap r _ \<Rightarrow>
                 (do tptrOpt <- liftM replyTCB (getReply (r));
                     when (tptrOpt \<noteq> Nothing \<and> tptrOpt \<noteq> Some thread) $ cancelIPC (the tptrOpt);
                     return (Just r)
                  od)
                 | _ \<Rightarrow> haskell_fail [];
                 f replyOpt
          od)"
  by (case_tac replyCap; simp add: bind_assoc)

lemma receiveIPC_corres:
  assumes "is_ep_cap cap" and "cap_relation cap cap'" and "cap_relation reply_cap replyCap"
    and "is_reply_cap reply_cap \<or> (reply_cap = cap.NullCap)"
  shows
    "corres dc (einvs and valid_cap cap
              and valid_cap reply_cap
              and st_tcb_at active thread
              and not_queued thread and not_in_release_q thread and scheduler_act_not thread
              and tcb_at thread and ex_nonz_cap_to thread
              and cte_wp_at (\<lambda>c. c = cap.NullCap) (thread, tcb_cnode_index 3)
              and (\<lambda>s. \<forall>r\<in>zobj_refs reply_cap. ex_nonz_cap_to r s))
             (invs' and tcb_at' thread and valid_cap' cap' and valid_cap' replyCap)
             (receive_ipc thread cap isBlocking reply_cap) (receiveIPC thread cap' isBlocking replyCap)"
    (is "corres _ (_ and ?tat and ?tex and ?slot3 and ?rrefs) _ _ _")
  supply if_split [split del]
  apply (insert assms)
  apply (rule corres_cross_add_abs_guard[where Q="K (thread \<noteq> idle_thread_ptr)"])
   apply (clarsimp simp: invs_def valid_state_def valid_pspace_def)
   apply (frule (1) idle_no_ex_cap)
   apply (clarsimp simp: valid_idle_def)
  apply (simp add: receive_ipc_def receiveIPC_def)
  apply add_sym_refs
  apply (case_tac cap, simp_all add: isEndpointCap_def)
  apply (rename_tac epptr badge right)
  apply (rule corres_stateAssert_assume)
   apply (rule stronger_corres_guard_imp)
     apply (subst receiveIPC_corres_helper)
     apply (clarsimp simp: receive_ipc_preamble_def[symmetric] receiveIPC_preamble_def[symmetric])
     apply (rule corres_split[OF receiveIPC_preamble_corres], simp, simp)
       apply (rule corres_split[OF get_ep_corres])
         apply (rename_tac ep ep')
         apply (rule corres_split[OF gbn_corres])
           apply (rule_tac r'="ntfn_relation" in corres_split)
              apply (rule corres_option_split[OF _ corres_returnTT get_ntfn_corres]; clarsimp)
              apply (clarsimp simp: ntfn_relation_def default_notification_def default_ntfn_def)
             apply (rule corres_if)
               apply (clarsimp simp: ntfn_relation_def Ipc_A.isActive_def Endpoint_H.isActive_def
                              split: Structures_A.ntfn.splits Structures_H.notification.splits)
              apply (simp only: )
              apply (rule complete_signal_corres)
             apply (rule corres_split[where r'=dc])
                apply (rule corres_when; simp)
                apply (rule maybeReturnSc_corres)
               apply (rule_tac P="einvs and ?tat and ?slot3 and ?tex and ep_at epptr
                        and valid_ep ep and ko_at (Endpoint ep) epptr
                        and receive_ipc_preamble_rv reply_cap replyOpt and ?rrefs" and
                      P'="invs' and tcb_at' thread and ep_at' epptr
                          and valid_ep' ep' and valid_bound_reply' replyOpt"
                      in corres_inst)
               apply (rule_tac P'="valid_bound_obj' valid_replies'_sc_asrt replyOpt" and
                               P=\<top> in corres_add_guard)
                apply (case_tac replyOpt; simp)
                apply (erule valid_replies_sc_cross; clarsimp elim!: reply_at_ppred_reply_at)
               apply (case_tac ep)
                 \<comment> \<open>IdleEP\<close>
                 apply (simp add: ep_relation_def)
                 apply (fold dc_def)[1]
                 apply (rule corres_guard_imp)
                   apply (case_tac isBlocking; simp)
                    apply (rule corres_split[OF sts_corres], simp)
                      apply (rule corres_split[OF corres_when set_ep_corres], clarsimp)
                         apply (rule replyTCB_update_corres)
                        prefer 6 \<comment> \<open> defer wp until corres complete \<close>
                        apply (rule corres_guard_imp, rule doNBRecvFailedTransfer_corres, clarsimp)
                        apply simp
                       apply (simp add: ep_relation_def) \<comment> \<open> corres logic done \<close>
                      apply wpsimp+
                  apply (clarsimp simp: invs_def valid_state_def valid_pspace_def
                                        valid_tcb_state_def st_tcb_at_tcb_at
                                 split: option.splits)
                  apply (fastforce elim: ri_preamble_vbreply reply_at_ppred_reply_at)
                 apply fastforce
                \<comment> \<open>SendEP\<close>
                apply (simp add: ep_relation_def get_tcb_obj_ref_def)
                apply (rename_tac list)
                apply (rule_tac F="list \<noteq> []" in corres_req)
                 apply (clarsimp simp: valid_ep_def)
                apply (case_tac list, simp_all)[1]
                apply (rename_tac sender queue)
                apply (rule corres_guard_imp)
                  apply (rule corres_split[OF set_ep_corres])
                     apply (clarsimp simp: ep_relation_def split: list.splits)
                    apply (rule corres_split[OF gts_corres])
                      apply (rule_tac F="\<exists>data. sender_state = Structures_A.thread_state.BlockedOnSend epptr data"
                             in corres_gen_asm)
                      apply (clarsimp simp: isSend_def case_bool_If
                                            case_option_If if3_fold
                                      cong: if_cong)
                      apply (rule corres_split[OF dit_corres])
                        apply (rule corres_split[OF threadget_fault_corres])
                          apply (simp cong: if_cong)
                          apply (fold dc_def)[1]
                          apply (rule_tac P="valid_objs and valid_mdb and valid_list
                                             and valid_sched and valid_replies and valid_idle
                                             and cur_tcb
                                             and pspace_aligned and pspace_distinct
                                             and st_tcb_at is_blocked_on_send sender and ?tat
                                             and receive_ipc_preamble_rv reply_cap replyOpt
                                             and valid_bound_obj (\<lambda>r s. r \<notin> fst ` replies_with_sc s) replyOpt
                                             and (\<lambda>s. sym_refs (\<lambda>p. if p = sender
                                                                    then tcb_non_st_state_refs_of s sender
                                                                    else state_refs_of s p))
                                             and ?rrefs and ?slot3"
                                      and P'="tcb_at' sender and tcb_at' thread and cur_tcb'
                                              and valid_queues
                                              and valid_queues'
                                              and valid_release_queue
                                              and valid_release_queue'
                                              and valid_objs'
                                              and valid_bound_obj' valid_replies'_sc_asrt replyOpt
                                              and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s)"
                                       in corres_guard_imp [OF corres_if])
                              apply (simp add: fault_rel_optionation_def)
                             apply (rule corres_if2)
                               apply simp
                              apply (rule corres_split_eqr[OF replyPush_corres threadget_corres])
                                 apply (clarsimp simp: fault_rel_optionation_def split: option.splits)
                                apply (clarsimp simp: tcb_relation_def)
                               prefer 3 \<comment> \<open> defer wp until corres complete \<close>
                               apply (rule sts_corres, simp)
                              prefer 3 \<comment> \<open> defer wp until corres complete \<close>
                              apply (rule corres_split[OF sts_corres], simp)
                                apply (rule possibleSwitchTo_corres)
                               apply (wpsimp wp: set_thread_state_valid_sched_action)
                              apply wpsimp
                             apply wpsimp
                            apply wpsimp
                           apply clarsimp
                           apply (frule valid_objs_valid_tcbs)
                           apply (frule pred_tcb_at_tcb_at)
                           apply (frule (1) valid_sched_scheduler_act_not_better[OF _ st_tcb_weakenE])
                            apply (clarsimp simp: is_blocked_on_send_def)
                           apply (frule (1) not_idle_thread', clarsimp simp: is_blocked_on_send_def)
                           apply (clarsimp simp: valid_sched_def valid_idle_def
                                          split: if_splits cong: conj_cong)
                           apply (subgoal_tac "replyOpt \<noteq> None \<longrightarrow> the replyOpt \<notin> fst ` replies_with_sc s")
                            apply (prop_tac "st_tcb_at (\<lambda>st. reply_object st = None) sender s")
                             apply (fastforce elim!: pred_tcb_weakenE simp: is_blocked_on_send_def)
                            apply (frule valid_sched_action_weak_valid_sched_action)
                            apply (clarsimp simp: valid_sched_def split: if_splits cong: conj_cong)
                            apply fastforce
                           apply (fastforce simp: image_def)
                          apply (clarsimp, frule valid_objs'_valid_tcbs')
                          apply (clarsimp simp: valid_sched_def split: if_splits
                                          cong: conj_cong)
                          apply (case_tac replyOpt; simp)
                         apply wpsimp
                        apply wpsimp
                       apply (wpsimp wp: do_ipc_transfer_tcb_caps hoare_vcg_ball_lift
                                         valid_bound_obj_lift)
                      apply (wpsimp wp: valid_replies'_sc_asrt_lift valid_bound_obj'_lift)
                      apply (rule_tac Q="\<lambda>_ s. sch_act_wf (ksSchedulerAction s) s"
                             in hoare_post_imp, erule sch_act_wf_weak)
                      apply wpsimp
                     apply (wpsimp wp: gts_st_tcb_at)
                    apply wpsimp
                   apply (wpsimp wp: hoare_vcg_ball_lift valid_bound_obj_lift)
                  apply (clarsimp simp: pred_conj_def cong: conj_cong)
                  apply (wpsimp wp: valid_replies'_sc_asrt_lift valid_bound_obj'_lift)
                 apply (clarsimp simp: invs_def valid_state_def st_tcb_at_tcb_at
                                       valid_ep_def valid_pspace_def)
                 apply (prop_tac "sender \<noteq> epptr")
                  apply (fastforce simp: valid_ep_def obj_at_def is_obj_defs)
                 apply (prop_tac "st_tcb_at (\<lambda>st. \<exists>data. st = Structures_A.BlockedOnSend epptr data) sender s")
                  apply (drule (1) sym_refs_ko_atD)
                  apply (fastforce simp: st_tcb_at_refs_of_rev elim: st_tcb_weakenE)
                 apply (extract_conjunct \<open>rule delta_sym_refs\<close>)
                  subgoal
                    apply (erule delta_sym_refs)
                     by (auto simp: ko_at_state_refs_ofD get_refs_def2
                                    pred_tcb_at_def obj_at_def valid_ep_def
                             split: list.splits if_splits)
                 apply (clarsimp split: list.split)
                 apply (frule (2) ri_preamble_not_in_sc)
                 apply (frule_tac y=sender in valid_sched_scheduler_act_not_better)
                  apply (fastforce simp: st_tcb_at_refs_of_rev elim: st_tcb_weakenE)
                 apply (fastforce simp: st_tcb_at_refs_of_rev elim: st_tcb_weakenE)
                apply (fastforce simp: valid_ep'_def invs'_def valid_state'_def split: list.split)
               \<comment> \<open>RecvEP\<close>
               apply (simp add: ep_relation_def)
               apply (fold dc_def)[1]
               apply (rule_tac corres_guard_imp)
                 apply (case_tac isBlocking; simp)
                  apply (rule corres_split[OF sts_corres], simp)
                    apply (rule corres_split [where r=dc])
                       apply (rule corres_when[OF _ replyTCB_update_corres], simp)
                      apply (rule corres_split[OF tcbEPAppend_corres set_ep_corres])
                        apply (simp add: ep_relation_def)
                       apply (wpsimp wp: hoare_vcg_ball_lift)+
                 apply (rule corres_guard_imp[OF doNBRecvFailedTransfer_corres]; clarsimp)
                apply (clarsimp simp: invs_def valid_pspace_def valid_state_def valid_ep_def)
                apply (fastforce elim: ri_preamble_vbreply reply_at_ppred_reply_at)
               apply (clarsimp simp: invs'_def valid_pspace'_def valid_state'_def valid_ep'_def)
               apply fastforce
              \<comment> \<open> end of ep cases \<close>
              apply (rule_tac Q="\<lambda>_. einvs and ?tat and ?slot3 and ?tex and
                               ko_at (Endpoint ep) epptr and
                               receive_ipc_preamble_rv reply_cap replyOpt and ?rrefs"
                     in hoare_strengthen_post[rotated])
               apply (clarsimp, intro conjI)
                apply (clarsimp simp: obj_at_def is_ep)
               apply (frule (1) valid_objs_ko_at[OF invs_valid_objs])
               apply (clarsimp simp: valid_obj_def)
              apply (wpsimp wp: hoare_cte_wp_caps_of_state_lift valid_case_option_post_wp hoare_vcg_ball_lift)
             apply (wpsimp wp: maybeReturnSc_invs' valid_case_option_post_wp)
            apply simp
            apply (wpsimp wp: get_simple_ko_wp)
           apply simp
           apply (wpsimp wp: getNotification_wp)
          apply (wpsimp wp: get_tcb_obj_ref_wp)
         apply (wpsimp wp: gbn_wp')
        apply (drule_tac s=reply in sym, simp)
        apply (wpsimp wp: get_simple_ko_wp)
       apply (wpsimp wp: getEndpoint_wp)
      apply simp
      apply (rule_tac Q="\<lambda>r. invs and ep_at epptr and valid_list
                             and scheduler_act_not thread and (\<lambda>s. thread \<noteq> idle_thread s)
                             and valid_sched and ?tat and ?tex and ?slot3
                             and receive_ipc_preamble_rv reply_cap r
                             and not_queued thread and not_in_release_q thread and ?rrefs"
             in hoare_strengthen_post[rotated])
       apply (subgoal_tac "\<forall>tcb. ko_at (TCB tcb) thread s \<longrightarrow>
                                   (case tcb_bound_notification tcb of
                                     None \<Rightarrow> \<lambda>_. True
                                     | Some x \<Rightarrow> ntfn_at x) s")
        apply (fastforce simp: invs_def valid_state_def valid_pspace_def split: if_split)
       apply (clarsimp, frule (1) valid_objs_ko_at[OF invs_valid_objs])
       apply (clarsimp simp: valid_obj_def valid_tcb_def valid_bound_obj_def case_option_ext)
      apply (wpsimp wp: receive_ipc_preamble_invs receive_ipc_preamble_valid_sched
                        receive_ipc_preamble_rv hoare_vcg_ball_lift)
     apply (rule_tac Q="\<lambda>replyOpt. ep_at' epptr and tcb_at' thread and invs' and
                            (\<lambda>_. thread \<noteq> idle_thread_ptr) and valid_bound_reply' replyOpt"
            in hoare_strengthen_post[rotated])
      apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def split: if_split)[1]
      apply (subgoal_tac "thread \<noteq> ksIdleThread s \<and> (\<forall>ko. ko_at' ko epptr s \<longrightarrow> valid_ep' ko s) \<and>
                          (\<forall>ntfn. bound_tcb_at' ((=) ntfn) thread s \<longrightarrow> valid_bound_ntfn' ntfn s)",
             clarsimp)
       apply (clarsimp simp: valid_bound_ntfn'_def case_option_ext)
       apply (intro conjI; intro allI impI)
        apply (intro conjI; intro allI impI)
         apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def)
        apply clarsimp
       apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def)
      apply (intro conjI; clarsimp)
        apply (clarsimp simp: valid_idle'_def)
       apply (erule ep_ko_at_valid_objs_valid_ep', clarsimp)
      apply (clarsimp simp: pred_tcb_at'_def, frule obj_at_ko_at'[where p=thread], clarsimp)
      apply (frule tcb_ko_at_valid_objs_valid_tcb', clarsimp)
      apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def valid_tcb'_def)
     apply wpsimp
    apply clarsimp
    apply (clarsimp simp: valid_cap_def valid_idle_def invs_def valid_state_def valid_sched_def)
   apply (clarsimp simp: valid_cap'_def)
  apply (simp add: sym_refs_asrt_def)
  done

lemma scheduleTCB_corres:
  "corres dc
          (valid_tcbs and weak_valid_sched_action and pspace_aligned and pspace_distinct
           and tcb_at tcbPtr)
          (valid_tcbs' and valid_queues and valid_queues' and valid_release_queue_iff)
          (schedule_tcb tcbPtr)
          (scheduleTCB tcbPtr)"
  apply (clarsimp simp: schedule_tcb_def scheduleTCB_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split [OF gct_corres])
      apply (rule corres_split [OF get_sa_corres], rename_tac sched_action)
        apply (rule corres_split [OF isSchedulable_corres])
          apply (clarsimp simp: when_def)
          apply (intro conjI impI; (clarsimp simp: sched_act_relation_def)?)
           apply (rule rescheduleRequired_corres)
          apply (case_tac sched_act; clarsimp)
         apply (wpsimp wp: isSchedulable_wp)+
  done

lemma as_user_refs_of[wp]:
  "as_user thread f \<lbrace>\<lambda>s. obj_at (\<lambda>ko. P (refs_of ko)) ptr s\<rbrace>"
  apply (clarsimp simp: as_user_def)
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: obj_at_def)
  apply (erule rsubst[where P=P])
  apply (clarsimp simp: get_tcb_def get_refs_def2 tcb_st_refs_of_def
                 split: Structures_A.kernel_object.splits)
  done

lemma receiveSignal_corres:
 "\<lbrakk> is_ntfn_cap cap; cap_relation cap cap' \<rbrakk> \<Longrightarrow>
  corres dc ((invs and weak_valid_sched_action and scheduler_act_not thread and valid_ready_qs
                   and st_tcb_at active thread and active_sc_valid_refills and valid_release_q
                   and current_time_bounded 2 and (\<lambda>s. thread = cur_thread s) and not_queued thread
                   and not_in_release_q thread and ex_nonz_cap_to thread) and valid_cap cap)
            (invs' and tcb_at' thread and ex_nonz_cap_to' thread and valid_cap' cap')
            (receive_signal thread cap isBlocking) (receiveSignal thread cap' isBlocking)"
  (is "\<lbrakk>_;_\<rbrakk> \<Longrightarrow> corres _ (?pred and _) _ _ _")
  apply (simp add: receive_signal_def receiveSignal_def)
  apply add_sym_refs
  apply (rule corres_stateAssert_assume)
   apply (case_tac cap, simp_all add: isEndpointCap_def)
   apply (rename_tac cap_ntfn_ptr badge rights)
   apply (rule_tac Q="\<lambda>rv. ?pred and tcb_at thread and ntfn_at cap_ntfn_ptr
                           and valid_ntfn rv and obj_at ((=) (Notification rv)) cap_ntfn_ptr"
               and Q'="\<lambda>rv'. invs' and valid_release_queue_iff and ex_nonz_cap_to' thread
                             and tcb_at' thread and ntfn_at' cap_ntfn_ptr
                             and valid_ntfn' rv' and ko_at' rv' cap_ntfn_ptr"
                in corres_split')
      apply (corressimp corres: get_ntfn_corres
                          simp: ntfn_at_def2 valid_cap_def st_tcb_at_tcb_at valid_cap'_def)
     defer
     apply (wpsimp wp: get_simple_ko_wp)
     apply (fastforce simp: valid_cap_def obj_at_def valid_obj_def
                      dest: invs_valid_objs)
    apply (wpsimp wp: getNotification_wp)
    apply (fastforce simp: obj_at'_def projectKOs valid_obj'_def
                     dest: invs_valid_objs')
   apply (clarsimp simp: sym_refs_asrt_def)
  apply (case_tac "ntfn_obj rv"; clarsimp simp: ntfn_relation_def)
    apply (case_tac isBlocking; simp)
     apply (rule corres_guard_imp)
       apply (rule corres_split_deprecated[OF _ sts_corres])
          apply (rule corres_split_deprecated[OF _ set_ntfn_corres])
             apply (rule maybeReturnSc_corres)
            apply (wpsimp wp: maybe_return_sc_weak_valid_sched_action)
            apply (clarsimp simp: ntfn_relation_def)
           apply wpsimp
          apply wpsimp
         apply (clarsimp simp: thread_state_relation_def)
        apply (wpsimp wp: set_thread_state_weak_valid_sched_action)
       apply wpsimp
      apply clarsimp
      apply (rule conjI, fastforce simp: valid_tcb_state_def valid_ntfn_def)+
      apply (erule delta_sym_refs[OF invs_sym_refs]; clarsimp split: if_split_asm)
        apply (fastforce simp: state_refs_of_def get_refs_def tcb_st_refs_of_def
                               pred_tcb_at_def obj_at_def is_obj_defs
                        split: if_split_asm option.splits)+
     apply (fastforce simp: valid_tcb_state'_def)
    apply (corressimp corres: doNBRecvFailedTransfer_corres)
    apply fastforce
   \<comment> \<open>WaitingNtfn\<close>
   apply (case_tac isBlocking; simp)
    apply (rule corres_guard_imp)
      apply (rule corres_split_deprecated[OF _ sts_corres])
         apply (rule corres_split_deprecated[OF _ tcbEPAppend_corres])
           apply (rule corres_split_deprecated[OF _ set_ntfn_corres])
              apply (rule maybeReturnSc_corres)
             apply (wpsimp wp: maybe_return_sc_weak_valid_sched_action)
             apply (clarsimp simp: ntfn_relation_def)
            apply wpsimp
           apply wpsimp
          apply wpsimp
         apply wpsimp
        apply (clarsimp simp: thread_state_relation_def)
       apply (wpsimp wp: set_thread_state_weak_valid_sched_action)
      apply (wpsimp wp: hoare_vcg_ball_lift2)
     apply clarsimp
     apply (rule conjI, fastforce simp: valid_tcb_state_def valid_ntfn_def)+
     apply (erule delta_sym_refs[OF invs_sym_refs]; clarsimp split: if_split_asm)
       apply (fastforce simp: state_refs_of_def get_refs_def tcb_st_refs_of_def
                              pred_tcb_at_def obj_at_def is_obj_defs
                       split: if_split_asm option.splits)+
    apply (fastforce simp: valid_tcb_state'_def valid_ntfn'_def)
   apply (corressimp corres: doNBRecvFailedTransfer_corres)
   apply fastforce
  \<comment> \<open>ActiveNtfn\<close>
  apply (rule corres_guard_imp)
    apply (clarsimp simp: badge_register_def badgeRegister_def)
    apply (rule corres_split_deprecated[OF _ user_setreg_corres])
      apply (rule corres_split_deprecated[OF _ set_ntfn_corres])
         apply (rule maybeDonateSc_corres)
        apply (clarsimp simp: ntfn_relation_def)
       apply (wpsimp wp: set_ntfn_minor_invs)
      apply (wpsimp wp: set_ntfn_minor_invs')
     apply (wpsimp wp: hoare_vcg_imp_lift'
                 simp: valid_ntfn_def)
    apply (wpsimp wp: hoare_vcg_imp_lift')
   apply (fastforce intro: if_live_then_nonz_capD2
                     simp: obj_at_def live_def live_ntfn_def valid_ntfn_def)
  apply (fastforce intro!: if_live_then_nonz_capE'
                     simp: valid_ntfn'_def obj_at'_def projectKOs live_ntfn'_def ko_wp_at'_def)
  done

declare lookup_cap_valid' [wp]

lemma thread_set_fault_valid_sched_except_blocked_except_released_ipc_qs[wp]:
  "thread_set (tcb_fault_update f) t \<lbrace>valid_sched_except_blocked_except_released_ipc_qs\<rbrace>"
  by (wpsimp wp: thread_set_fault_valid_sched_pred simp: valid_sched_2_def)

lemma send_fault_ipc_corres:
  assumes "fr f f'"
  assumes "cap_relation cap cap'"
  shows
  "corres (fr \<oplus> (=))
          (invs and valid_list and valid_sched_action
                and st_tcb_at active thread and scheduler_act_not thread
                and (\<lambda>s. can_donate \<longrightarrow> bound_sc_tcb_at (\<lambda>sc. sc \<noteq> None) thread s)
                and valid_cap cap and K (valid_fault_handler cap) and K (valid_fault f))
          (invs' and valid_cap' cap')
          (send_fault_ipc thread cap f can_donate)
          (sendFaultIPC thread cap' f' can_donate)"
  using assms
  apply (clarsimp simp: send_fault_ipc_def sendFaultIPC_def)
  apply (rule corres_gen_asm)
  apply (rule corres_gen_asm)
  apply (cases cap; simp add: valid_fault_handler_def tcb_relation_def)
  apply (rule stronger_corres_guard_imp)
    apply (rule corres_split_deprecated)
       apply (rule corres_split_deprecated)
          apply clarsimp
         apply (rule sendIPC_corres, clarsimp)
        apply wp
       apply wp
      apply (rule threadset_corres; clarsimp simp: tcb_relation_def fault_rel_optionation_def)
     apply (wpsimp wp: threadSet_invs_trivial thread_set_invs_but_fault_tcbs
                       thread_set_no_change_tcb_state thread_set_no_change_tcb_sched_context
                       thread_set_cte_wp_at_trivial ex_nonz_cap_to_pres hoare_weak_lift_imp
                 simp: ran_tcb_cap_cases valid_cap_def)+
   apply (frule pred_tcb_at_tcb_at, clarsimp)
   apply (erule (1) st_tcb_ex_cap[OF _ invs_iflive])
   apply (case_tac st; clarsimp)
  apply (clarsimp, frule pred_tcb_at_tcb_at)
  apply (frule cross_relF[OF _ tcb_at'_cross_rel[where t=thread]], fastforce)
  apply (fastforce simp: invs'_def valid_state'_def valid_tcb_def valid_release_queue_def
                         valid_release_queue'_def valid_cap'_def obj_at'_def inQ_def)
  done

lemma gets_the_noop_corres:
  assumes P: "\<And>s. P s \<Longrightarrow> f s \<noteq> None"
  shows "corres dc P P' (gets_the f) (return x)"
  apply (clarsimp simp: corres_underlying_def gets_the_def
                        return_def gets_def bind_def get_def)
  apply (clarsimp simp: assert_opt_def return_def dest!: P)
  done

end

crunches sendFaultIPC, receiveIPC, receiveSignal
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n n p s)"
  (wp: crunch_wps hoare_vcg_all_lift simp: crunch_simps)

global_interpretation sendFaultIPC: typ_at_all_props' "sendFaultIPC t cap f d"
  by typ_at_props'
global_interpretation receiveIPC: typ_at_all_props' "receiveIPC t cap b r"
  by typ_at_props'
global_interpretation receiveSignal: typ_at_all_props' "receiveSignal t cap b"
  by typ_at_props'

lemma setCTE_valid_queues[wp]:
  "\<lbrace>Invariants_H.valid_queues\<rbrace> setCTE ptr val \<lbrace>\<lambda>rv. Invariants_H.valid_queues\<rbrace>"
  by (wp valid_queues_lift setCTE_pred_tcb_at')

crunch vq[wp]: cteInsert "Invariants_H.valid_queues"
  (wp: crunch_wps)

lemma getSlotCap_cte_wp_at:
  "\<lbrace>\<top>\<rbrace> getSlotCap sl \<lbrace>\<lambda>rv. cte_wp_at' (\<lambda>c. cteCap c = rv) sl\<rbrace>"
  apply (simp add: getSlotCap_def)
  apply (wp getCTE_wp)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  done

lemma cteInsert_cap_to':
  "\<lbrace>ex_nonz_cap_to' p and cte_wp_at' (\<lambda>c. cteCap c = NullCap) dest\<rbrace>
     cteInsert cap src dest
   \<lbrace>\<lambda>rv. ex_nonz_cap_to' p\<rbrace>"
  apply (simp    add: cteInsert_def ex_nonz_cap_to'_def
                      updateCap_def setUntypedCapAsFull_def
           split del: if_split)
  apply (rule hoare_pre, rule hoare_vcg_ex_lift)
   apply (wp updateMDB_weak_cte_wp_at
             setCTE_weak_cte_wp_at
           | simp
           | rule hoare_drop_imps)+
  apply (wp getCTE_wp)
  apply clarsimp
  apply (rule_tac x=cref in exI)
  apply (rule conjI)
   apply (clarsimp simp: cte_wp_at_ctes_of)+
  done

context begin interpretation Arch . (*FIXME: arch_split*)

crunches setExtraBadge, doIPCTransfer
  for cap_to'[wp]: "ex_nonz_cap_to' p"
  (ignore: transferCapsToSlots
       wp: crunch_wps transferCapsToSlots_pres2 cteInsert_cap_to' hoare_vcg_const_Ball_lift
     simp: zipWithM_x_mapM ball_conj_distrib)

lemma st_tcb_idle':
  "\<lbrakk>valid_idle' s; st_tcb_at' P t s\<rbrakk> \<Longrightarrow>
   (t = ksIdleThread s) \<longrightarrow> P IdleThreadState"
  by (clarsimp simp: valid_idle'_def pred_tcb_at'_def obj_at'_def idle_tcb'_def)


crunches setExtraBadge, receiveIPC
  for it[wp]: "\<lambda>s. P (ksIdleThread s)"
  and irqs_masked' [wp]: "irqs_masked'"
  (ignore: transferCapsToSlots
       wp: transferCapsToSlots_pres2 crunch_wps hoare_vcg_all_lift
     simp: crunch_simps ball_conj_distrib)

crunches copyMRs, doIPCTransfer
  for ksQ'[wp]: "\<lambda>s. P (ksReadyQueues s)"
  and ct'[wp]: "\<lambda>s. P (ksCurThread s)"
  (wp: mapM_wp' hoare_drop_imps simp: crunch_simps)

lemma asUser_ct_not_inQ[wp]:
  "\<lbrace>ct_not_inQ\<rbrace> asUser tptr f \<lbrace>\<lambda>rv. ct_not_inQ\<rbrace>"
  apply (simp add: asUser_def split_def)
  apply (wp hoare_drop_imps threadSet_not_inQ | simp)+
  done

crunches copyMRs, doIPCTransfer
  for ct_not_inQ[wp]: "ct_not_inQ"
  (wp: mapM_wp' hoare_drop_imps simp: crunch_simps)

lemma ntfn_q_refs_no_bound_refs':
  "rf : ntfn_q_refs_of' (ntfnObj ob) \<Longrightarrow> rf ~: ntfn_bound_refs' (ntfnBoundTCB ob')"
  by (auto simp add: ntfn_q_refs_of'_def ntfn_bound_refs'_def
           split: Structures_H.ntfn.splits)

lemma completeSignal_invs':
  "\<lbrace>invs' and tcb_at' tcb\<rbrace>
   completeSignal ntfnptr tcb
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: completeSignal_def)
  apply (rule hoare_seq_ext[OF _ get_ntfn_sp'])
  apply (wpsimp wp: set_ntfn_minor_invs')
    apply (wpsimp wp: hoare_vcg_ex_lift static_imp_wp simp: valid_ntfn'_def)
   apply wpsimp
  apply clarsimp
  apply (intro conjI impI)
    apply (fastforce dest: ntfn_ko_at_valid_objs_valid_ntfn'
                     simp: valid_ntfn'_def)
   apply (fastforce intro: if_live_then_nonz_capE'
                     simp: ko_wp_at'_def obj_at'_def projectKOs live_ntfn'_def)
  done

lemma maybeReturnSc_ex_nonz_cap_to'[wp]:
  "maybeReturnSc nptr tptr \<lbrace>ex_nonz_cap_to' t\<rbrace>"
  by (wpsimp wp: hoare_drop_imps threadSet_cap_to'
           simp: maybeReturnSc_def tcb_cte_cases_def cteCaps_of_def)

lemma maybeReturnSc_st_tcb_at'[wp]:
  "maybeReturnSc nptr tptr \<lbrace>\<lambda>s. P (st_tcb_at' Q t s)\<rbrace>"
  by (wpsimp wp: hoare_drop_imps threadSet_cap_to' threadSet_pred_tcb_no_state
           simp: maybeReturnSc_def tcb_cte_cases_def cteCaps_of_def)

crunches scheduleTCB
  for invs'[wp]: invs'
  and ex_nonz_cap_to'[wp]: "ex_nonz_cap_to' p"
  and valid_ntfn'[wp]: "valid_ntfn' ntfn"
  and valid_bound_tcb'[wp]: "valid_bound_tcb' tcb"
  and valid_bound_sc'[wp]: "valid_bound_sc' sc"
  (wp: hoare_drop_imps)

crunches doNBRecvFailedTransfer
  for invs'[wp]: invs'

(* t = ksCurThread s *)
lemma rai_invs'[wp]:
  "\<lbrace>invs' and sch_act_not t
          and st_tcb_at' active' t
          and ex_nonz_cap_to' t
          and valid_cap' cap
          and (\<lambda>s. \<forall>r \<in> zobj_refs' cap. ex_nonz_cap_to' r s)
          and (\<lambda>s. \<exists>ntfnptr. isNotificationCap cap
                 \<and> capNtfnPtr cap = ntfnptr
                 \<and> obj_at' (\<lambda>ko. ntfnBoundTCB ko = None \<or> ntfnBoundTCB ko = Some t) ntfnptr s)\<rbrace>
   receiveSignal t cap isBlocking
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: receiveSignal_def doNBRecvFailedTransfer_def)
  apply (rule hoare_seq_ext [OF _ stateAssert_sp])
  apply (rule hoare_seq_ext [OF _ get_ntfn_sp'])
  apply (rename_tac ep)
  apply (case_tac "ntfnObj ep"; clarsimp)
    \<comment> \<open>IdleNtfn\<close>
    apply (wpsimp wp: setNotification_invs' maybeReturnSc_invs' sts_invs_minor' simp: live_ntfn'_def)
    apply (clarsimp simp: pred_tcb_at' cong: conj_cong)
    apply (fastforce simp: valid_idle'_def idle_tcb'_def valid_tcb_state'_def  valid_ntfn'_def
                           valid_bound_obj'_def valid_obj'_def valid_cap'_def isCap_simps
                           pred_tcb_at'_def obj_at'_def projectKOs
                     dest: invs_valid_idle' invs_valid_objs' split: option.splits)
   \<comment> \<open>ActiveNtfn\<close>
   apply (wpsimp wp: maybeDonateSc_invs' setNotification_invs' hoare_vcg_imp_lift')
   apply (fastforce simp: valid_obj'_def valid_ntfn'_def isCap_simps
                          pred_tcb_at'_def obj_at'_def projectKOs
                    dest: invs_valid_objs')
  \<comment> \<open>WaitingNtfn\<close>
  apply (wpsimp wp: setNotification_invs' maybeReturnSc_invs')
     apply (rule_tac R="\<lambda>_ _. ntfnBoundTCB ep = None" in hoare_post_add)
     apply (clarsimp simp: valid_ntfn'_def cong: conj_cong)
       apply (wpsimp wp: maybeReturnSc_invs' tcbEPAppend_rv_wf' sts_invs_minor'
                         hoare_vcg_ball_lift hoare_drop_imps)+
  apply (frule invs_valid_objs')
  apply (erule valid_objsE')
   apply (fastforce simp: obj_at'_def projectKOs)
  apply (clarsimp simp: valid_obj'_def valid_ntfn'_def valid_tcb_state'_def valid_cap'_def
                        isCap_simps sym_refs_asrt_def pred_tcb_at'_def obj_at'_def projectKOs)
  apply (rule conjI, clarsimp)
  apply (rule conjI, clarsimp)
  apply (rule conjI, clarsimp)
  apply (rule context_conjI)
   apply (clarsimp simp: invs'_def valid_state'_def valid_idle'_def
                         idle_tcb'_def obj_at'_def projectKOs)
  apply (drule_tac ko=ep in sym_refs_ko_atD'[rotated])
   apply (fastforce simp: obj_at'_def projectKOs)
  apply (auto simp: tcb_st_refs_of'_def tcb_bound_refs'_def refs_of_rev' get_refs_def ko_wp_at'_def
             split: thread_state.splits option.splits)
  done

lemma updateReply_reply_at'_wp:
  "\<lbrace>\<lambda>s. P (if p = rptr then True else reply_at' p s)\<rbrace>
   updateReply rptr f
   \<lbrace>\<lambda>rv s. P (reply_at' p s)\<rbrace>"
  apply (rule hoare_weaken_pre, rule updateReply_obj_at')
  apply (clarsimp simp: obj_at'_real_def split: if_splits)
  done

crunches setThreadState
  for tcbSCs_of[wp]: "\<lambda>s. P (tcbSCs_of s)"
  (ignore: threadSet wp: threadSet_tcbSCs_of_inv)

crunches replyUnlink
  for tcbSCs_of[wp]: "\<lambda>s. P (tcbSCs_of s)"
  and scs_of'[wp]: "\<lambda>s. P (scs_of' s)"

lemma replyUnlink_misc_heaps[wp]:
  "replyUnlink rPtr tPtr \<lbrace>\<lambda>s. P (tcbSCs_of s) (scTCBs_of s) (scReplies_of s) (replySCs_of s)\<rbrace>"
  by (rule hoare_weaken_pre, wps, wp, simp)

lemma schedContextUpdateConsumed_scReplies_of[wp]:
  "schedContextUpdateConsumed scPtr \<lbrace>\<lambda>s. P (scReplies_of s) \<rbrace>"
  unfolding schedContextUpdateConsumed_def
  apply (wpsimp simp: setSchedContext_def)
  apply (clarsimp simp: opt_map_def if_distrib)
  apply (erule subst[where P=P, rotated], rule ext)
  apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def split: option.splits)
  done

lemma schedContextUpdateConsumed_sc_tcbs_of[wp]:
  "schedContextUpdateConsumed scPtr \<lbrace>\<lambda>s. P (scTCBs_of s)\<rbrace>"
  unfolding schedContextUpdateConsumed_def
  apply (wpsimp simp: setSchedContext_def)
  apply (clarsimp simp: opt_map_def if_distrib)
  apply (erule subst[where P=P, rotated], rule ext)
  apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def split: option.splits)
  done

crunches schedContextUpdateConsumed
  for tcbSCs_of[wp]: "\<lambda>s. P (tcbSCs_of s)"

crunches doIPCTransfer
  for replySCs_of[wp]: "\<lambda>s. P (replySCs_of s)"
  (wp: crunch_wps simp: crunch_simps)

lemma schedContextUpdateConsumed_misc_heaps[wp]:
  "schedContextUpdateConsumed scPtr
   \<lbrace>\<lambda>s. P (scReplies_of s) (replySCs_of s) (tcbSCs_of s) (scTCBs_of s)\<rbrace>"
  by (rule hoare_weaken_pre, wps, wp, simp)

crunches doIPCTransfer
  for scs_replies_of[wp]: "\<lambda>s. P (scReplies_of s) (replySCs_of s)"
  (wp: crunch_wps ignore: setSchedContext simp: zipWithM_x_mapM)

crunches doIPCTransfer
  for scs_tcbs_of[wp]: "\<lambda>s. P (tcbSCs_of s) (scTCBs_of s)"
  (wp: crunch_wps threadSet_tcbSCs_of_inv ignore: threadSet simp: zipWithM_x_mapM)

crunches setEndpoint
  for misc_heaps[wp]: "\<lambda>s. P (scReplies_of s) (replySCs_of s) (tcbSCs_of s) (scTCBs_of s)"
  (wp: crunch_wps)

lemma replyPush_sym_refs_list_refs_of_replies':
  "\<lbrace>(\<lambda>s. sym_refs (list_refs_of_replies' s))
    and valid_replies'
    and valid_objs'
    and (\<lambda>s. replyTCBs_of s replyPtr = None) and sym_heap_scReplies\<rbrace>
   replyPush callerPtr calleePtr replyPtr canDonate
   \<lbrace>\<lambda>_ s. sym_refs (list_refs_of_replies' s)\<rbrace>"
  supply if_split [split del]
  unfolding replyPush_def
  apply wpsimp
        apply (wpsimp wp: bindsym_heap_scReplies_list_refs_of_replies'
                          hoare_vcg_if_lift2 hoare_vcg_imp_lift' hoare_vcg_all_lift)
       apply (rule_tac Q="(\<lambda>_ s. sym_refs (list_refs_of_replies' s) \<and>
        (\<forall>rptr scp. (scReplies_of s) scp = Some rptr
                     \<longrightarrow> replySCs_of s rptr = Some scp) \<and>
        \<not> is_reply_linked replyPtr s \<and> replySCs_of s replyPtr = None)"
      in hoare_strengthen_post[rotated])
        apply (fastforce split: if_splits simp del: comp_apply)

       apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift'
                         updateReply_list_refs_of_replies'_inv threadGet_wp)+
  apply (frule valid_replies'_no_tcb_not_linked; clarsimp)
  apply (intro conjI)
    apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def)
   apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def)
  apply (clarsimp simp: sym_heap_def pred_map_eq)
  done

lemma replyPush_if_live_then_nonz_cap':
  "\<lbrace> if_live_then_nonz_cap' and valid_objs' and valid_idle' and
     ex_nonz_cap_to' replyPtr and ex_nonz_cap_to' callerPtr and ex_nonz_cap_to' calleePtr and
     sym_heap_tcbSCs and sym_heap_scReplies and (\<lambda>s. callerPtr \<noteq> ksIdleThread s)\<rbrace>
   replyPush callerPtr calleePtr replyPtr canDonate
   \<lbrace>\<lambda>_. if_live_then_nonz_cap'\<rbrace>"
  supply if_split [split del]
  unfolding replyPush_def  bind_assoc
  apply (rule hoare_seq_ext[OF _ stateAssert_inv])
  apply simp
  apply (rule hoare_seq_ext[OF _ threadGet_sp'])
  apply (rule hoare_seq_ext[OF _ threadGet_sp'])
  apply (wpsimp wp: schedContextDonate_if_live_then_nonz_cap' bindScReply_if_live_then_nonz_cap')
    apply (rule_tac Q="\<lambda>_. if_live_then_nonz_cap' and ex_nonz_cap_to' replyPtr and
             valid_objs' and reply_at' replyPtr and ex_nonz_cap_to' calleePtr and
             (if (\<exists>y. scPtrOptDonated = Some y) \<and> scPtrOptCallee = None \<and> canDonate
             then \<lambda>s. ex_nonz_cap_to' (the scPtrOptDonated) s \<and>
                       (\<forall>rp. (scReplies_of s) (the scPtrOptDonated) = Some rp \<longrightarrow>
                             (replySCs_of s) rp  = Some (the scPtrOptDonated))
             else \<top>)" in hoare_strengthen_post[rotated], clarsimp split: if_splits simp: pred_map_eq)
    apply (wpsimp wp: hoare_vcg_if_lift2 hoare_vcg_imp_lift' hoare_vcg_all_lift)
   apply (clarsimp cong: conj_cong)
   apply (wpsimp wp: updateReply_iflive'_weak updateReply_reply_at'_wp updateReply_valid_objs'
                     hoare_vcg_all_lift hoare_vcg_imp_lift' updateReply_obj_at')
  apply clarsimp
  apply (intro conjI)
   apply (clarsimp simp: valid_reply'_def obj_at'_def)
  apply (intro allI impI, clarsimp)
  apply (rename_tac s scp)
  apply (subgoal_tac "sc_at' scp s \<and> (scTCBs_of s) scp = Some callerPtr \<and> callerPtr \<noteq> idle_thread_ptr")
   apply (intro conjI)
    apply (erule if_live_then_nonz_capE')
    apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def projectKO_sc pred_map_def pred_map_eq_def live_sc'_def)
    apply (clarsimp simp: sym_heap_def)
  apply (intro conjI)
    apply (frule obj_at_ko_at'[where p=callerPtr], clarsimp)
    apply (frule (1) tcb_ko_at_valid_objs_valid_tcb')
    apply (clarsimp simp: valid_tcb'_def)
   apply (subgoal_tac "(tcbSCs_of s) callerPtr = Some scp")
    apply (clarsimp simp: sym_heap_def)
   apply (clarsimp simp: opt_map_def obj_at'_real_def ko_wp_at'_def projectKOs)
  apply (clarsimp simp: valid_idle'_def)
  done

lemma bindScReply_valid_idle':
  "\<lbrace>valid_idle' and K (scPtr \<noteq> idle_sc_ptr)\<rbrace>
   bindScReply scPtr replyPtr
   \<lbrace>\<lambda>_. valid_idle'\<rbrace>"
  unfolding bindScReply_def
  by (wpsimp wp: hoare_vcg_imp_lift' hoare_vcg_all_lift set_reply'.obj_at')

lemma replyPush_valid_idle':
  "\<lbrace>valid_idle'
    and valid_pspace'
    and (\<lambda>s. callerPtr \<noteq> ksIdleThread s)
    and sym_heap_tcbSCs\<rbrace>
   replyPush callerPtr calleePtr replyPtr canDonate
   \<lbrace>\<lambda>_. valid_idle'\<rbrace>"
  apply (simp only: replyPush_def)
  supply if_split [split del]
  apply wpsimp
         apply (wpsimp wp: schedContextDonate_valid_idle' bindScReply_valid_idle')+
       apply (wpsimp wp: hoare_vcg_if_lift2 hoare_vcg_imp_lift')
      apply (wpsimp wp: hoare_vcg_if_lift2 hoare_vcg_imp_lift')
     apply (wpsimp wp: threadGet_wp)+
  apply (clarsimp simp: tcb_at'_ex_eq_all valid_pspace'_def)
  apply (subgoal_tac "\<forall>kob. valid_reply' kob s \<longrightarrow> valid_reply' (replyTCB_update (\<lambda>_. Some callerPtr) kob) s")
   apply (subgoal_tac "calleePtr \<noteq> idle_thread_ptr", simp)
    apply (subgoal_tac "y \<noteq> idle_sc_ptr", simp)
     apply (erule (3) not_idle_scTCB)
     apply (frule (1) tcb_ko_at_valid_objs_valid_tcb')
     apply (clarsimp simp: valid_tcb'_def)
    apply (frule (2) not_idle_tcbSC[where p=callerPtr])
      apply (clarsimp simp: valid_idle'_def)
     apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def)
    apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def)
   apply (clarsimp simp: valid_idle'_def idle_tcb'_def obj_at'_real_def ko_wp_at'_def)
  apply (clarsimp simp: valid_reply'_def)
  done

lemma replyPush_untyped_ranges_zero'[wp]:
  "replyPush callerPtr calleePtr replyPtr canDonate \<lbrace>untyped_ranges_zero'\<rbrace>"
  apply (clarsimp simp: untyped_ranges_zero_inv_null_filter_cteCaps_of)
  apply (rule hoare_lift_Pf[where f="ctes_of"])
   apply wp+
  done

lemma replyPush_sch_act_wf:
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s \<and> sch_act_not callerPtr s\<rbrace>
   replyPush callerPtr calleePtr replyPtr canDonate
   \<lbrace>\<lambda>_ s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  unfolding replyPush_def
  by (wpsimp wp: sts_sch_act' hoare_vcg_all_lift hoare_vcg_if_lift hoare_drop_imps)

lemma replyPush_invs':
  "\<lbrace>invs' and sym_heap_tcbSCs and sym_heap_scReplies and
    st_tcb_at' (Not \<circ> is_replyState) callerPtr and
    sch_act_not callerPtr and ex_nonz_cap_to' callerPtr and ex_nonz_cap_to' calleePtr and
    ex_nonz_cap_to' replyPtr and (\<lambda>s. replyTCBs_of s replyPtr = None)\<rbrace>
   replyPush callerPtr calleePtr replyPtr canDonate
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  unfolding invs'_def valid_state'_def valid_pspace'_def
  apply (wpsimp wp: replyPush_sch_act_wf replyPush_if_live_then_nonz_cap'
                    replyPush_valid_idle' replyPush_sym_refs_list_refs_of_replies'
              simp: valid_pspace'_def)
  apply (frule global'_no_ex_cap; clarsimp simp: valid_pspace'_def)
  done

lemma setEndpoint_invs':
  "\<lbrace>invs' and valid_ep' ep and ex_nonz_cap_to' eptr\<rbrace> setEndpoint eptr ep \<lbrace>\<lambda>_. invs'\<rbrace>"
  by (wpsimp simp: invs'_def valid_state'_def valid_dom_schedule'_def comp_def)

crunches maybeReturnSc, cancelIPC
  for sch_act_not[wp]: "sch_act_not t"
  and sch_act_simple[wp]: "sch_act_simple"
  (wp: crunch_wps hoare_drop_imps simp: crunch_simps)

crunches maybeReturnSc, doIPCTransfer
  for replyTCB_obj_at'[wp]: "\<lambda>s. P (obj_at' (\<lambda>reply. P' (replyTCB reply)) t s)"
  and reply_projs[wp]: "\<lambda>s. P (replyNexts_of s) (replyPrevs_of s) (replyTCBs_of s) (replySCs_of s)"
  (wp: crunch_wps constOnFailure_wp simp: crunch_simps)

lemma replyUnlink_replyTCBs_of_None[wp]:
  "\<lbrace>\<lambda>s. r \<noteq> rptr \<longrightarrow> replyTCBs_of s rptr = None\<rbrace>
   replyUnlink r t
   \<lbrace>\<lambda>_ s. replyTCBs_of s rptr = None\<rbrace>"
  apply (wpsimp wp: updateReply_wp_all gts_wp' simp: replyUnlink_def)
  done

lemma cancelIPC_replyTCBs_of_None:
  "\<lbrace>\<lambda>s. reply_at' rptr s \<and> (replyTCBs_of s rptr \<noteq> None \<longrightarrow> replyTCBs_of s rptr = Some t)\<rbrace>
   cancelIPC t
   \<lbrace>\<lambda>rv s. replyTCBs_of s rptr = None\<rbrace>"
  unfolding cancelIPC_def blockedCancelIPC_def getBlockingObject_def
  apply (clarsimp simp: sym_refs_asrt_def)
  apply (rule hoare_seq_ext[OF _ stateAssert_sp])
  apply (rule hoare_seq_ext[OF _ stateAssert_sp])
  apply (rule hoare_seq_ext[OF _ gts_sp'])
  apply (case_tac state; clarsimp)
         \<comment> \<open>BlockedOnReceive\<close>
         apply (wpsimp wp: getEndpoint_wp
                           hoare_vcg_all_lift hoare_vcg_imp_lift')
         apply (clarsimp simp: pred_tcb_at'_def obj_at'_def projectKOs)
         apply (drule_tac ko="ko :: reply" for ko in sym_refs_ko_atD'[rotated])
          apply (fastforce simp: obj_at'_def projectKOs)
         apply (clarsimp simp: tcb_st_refs_of'_def tcb_bound_refs'_def
                               refs_of_rev' get_refs_def ko_wp_at'_def opt_map_def
                        split: option.splits if_splits)
        \<comment> \<open>BlockedOnReply\<close>
        apply (wp gts_wp' updateReply_obj_at'_inv
                  hoare_vcg_all_lift hoare_vcg_const_imp_lift hoare_vcg_imp_lift'
               | rule threadSet_pred_tcb_no_state
               | simp add: replyRemoveTCB_def cleanReply_def if_fun_split)+
        apply (clarsimp simp: pred_tcb_at'_def obj_at'_def projectKOs)
        apply (drule_tac p=rptr and ko="ko :: reply" for ko in sym_refs_ko_atD'[rotated])
         apply (fastforce simp: obj_at'_def projectKOs)
        apply (clarsimp simp: tcb_st_refs_of'_def tcb_bound_refs'_def
                              refs_of_rev' get_refs_def ko_wp_at'_def opt_map_def
                       split: option.splits)
       \<comment> \<open>Other thread states\<close>
       apply (all \<open>wpsimp simp: cancelSignal_def sym_refs_asrt_def wp: hoare_drop_imps\<close>)
       apply (all \<open>clarsimp simp: pred_tcb_at'_def obj_at'_def projectKOs\<close>)
       apply (all \<open>drule_tac p=rptr and ko="ko :: reply" for ko in sym_refs_ko_atD'[rotated]\<close>)
             apply (fastforce simp: tcb_bound_refs'_def tcb_st_refs_of'_def refs_of_rev'
                                    get_refs_def ko_wp_at'_def obj_at'_def projectKOs
                             split: option.splits)+
  done

crunches cancelSignal, replyRemoveTCB, replyUnlink
  for ep_obj_at'[wp]: "obj_at' (P :: endpoint \<Rightarrow> bool) eptr"
  (wp: crunch_wps simp: crunch_simps)

lemma blockedCancelIPC_notin_epQueue:
  "\<lbrace>valid_objs' and obj_at' (\<lambda>ep. ep \<noteq> IdleEP \<longrightarrow> t \<notin> set (epQueue ep)) eptr\<rbrace>
    blockedCancelIPC state tptr reply_opt
   \<lbrace>\<lambda>rv. obj_at' (\<lambda>ep. ep \<noteq> IdleEP \<longrightarrow> t \<notin> set (epQueue ep)) eptr\<rbrace>"
  unfolding blockedCancelIPC_def getBlockingObject_def
  apply (wpsimp wp: set_ep'.obj_at' getEndpoint_wp)
  apply (fastforce simp: valid_obj'_def valid_ep'_def obj_at'_def projectKOs
                  intro: set_remove1[where y=tptr] split: endpoint.splits list.splits)
  done

lemma cancelIPC_notin_epQueue:
  "\<lbrace>valid_objs' and obj_at' (\<lambda>ep. ep \<noteq> IdleEP \<longrightarrow> t \<notin> set (epQueue ep)) eptr\<rbrace>
    cancelIPC tptr
   \<lbrace>\<lambda>rv. obj_at' (\<lambda>ep. ep \<noteq> IdleEP \<longrightarrow> t \<notin> set (epQueue ep)) eptr\<rbrace>"
  unfolding cancelIPC_def
  by (wpsimp wp: blockedCancelIPC_notin_epQueue hoare_drop_imps threadSet_valid_objs')

crunches rescheduleRequired
  for scs_tcbs_of[wp]: "\<lambda>s. P (tcbSCs_of s) (scTCBs_of s)"
  (wp: crunch_wps threadSet_tcbSCs_of_inv ignore: threadSet)

lemma maybeReturnSc_sym_heap_tcbSCs[wp]:
  "\<lbrace>sym_heap_tcbSCs and valid_objs'\<rbrace>
   maybeReturnSc y t
   \<lbrace>\<lambda>_. sym_heap_tcbSCs\<rbrace>"
  supply opt_mapE [rule del]
  unfolding maybeReturnSc_def
  apply (simp add: liftM_def)
  apply (rule hoare_seq_ext[OF _ stateAssert_sp])
  apply (rule hoare_seq_ext[OF _ get_ntfn_sp'])
  apply (wpsimp wp: setSchedContext_scTCBs_of threadSet_tcbSCs_of | wps)+
   apply (wpsimp wp: threadGet_wp)
  apply (clarsimp simp: tcb_at'_ex_eq_all)
  apply (drule sym, simp)
  apply (subgoal_tac "(tcbSCs_of s) t = Some (the (tcbSchedContext tcb))")
   apply (clarsimp simp: sym_heap_def)
   apply (subst (asm) sym_heap_symmetric[simplified sym_heap_def], simp)
  apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def opt_map_def projectKOs)
  done

lemma maybeReturnSc_sym_heap_scReplies[wp]:
  "maybeReturnSc y t \<lbrace>sym_heap_scReplies\<rbrace>"
  unfolding maybeReturnSc_def
  apply (simp add: liftM_def)
  apply (rule hoare_seq_ext[OF _ stateAssert_sp])
  apply (rule hoare_seq_ext[OF _ get_ntfn_sp'])
  apply (wpsimp wp: setSchedContext_scReplies_of | wps)+
   apply (wpsimp wp: threadGet_wp)
  apply (clarsimp simp: tcb_at'_ex_eq_all)
  apply (drule sym, simp)
  apply (erule back_subst)
  apply (rule arg_cong2[where f=sym_heap, OF _ refl], rule ext)
  apply (clarsimp simp: pred_map_eq_def pred_map_def obj_at'_real_def ko_wp_at'_def opt_map_def
                        projectKOs)
  done

crunches cleanReply
  for scTCBs_of[wp]: "\<lambda>s. P (scTCBs_of s)"
  and tcbSCs_of[wp]: "\<lambda>s. P (tcbSCs_of s)"

lemma replyRemoveTCB_scTCBs_of[wp]:
  "replyRemoveTCB tptr \<lbrace>\<lambda>s. P (scTCBs_of s)\<rbrace>"
  unfolding replyRemoveTCB_def
  apply (wpsimp wp: setSchedContext_scTCBs_of gts_wp')
  apply (erule back_subst[where P=P], rule ext, clarsimp)
  by (clarsimp simp: opt_map_def obj_at'_real_def ko_wp_at'_def)

lemma replyRemoveTCB_tcbSCs_of[wp]:
  "replyRemoveTCB tptr \<lbrace>\<lambda>s. P (tcbSCs_of s)\<rbrace>"
  unfolding replyRemoveTCB_def
  by (wpsimp wp: setSchedContext_scTCBs_of gts_wp')

lemma replyRemoveTCB_sym_heap_tcbSCs[wp]:
  "replyRemoveTCB tptr \<lbrace>sym_heap_tcbSCs\<rbrace>"
  by (rule hoare_weaken_pre, wps, wpsimp, simp)

crunches cancelIPC
  for sym_heap_tcbSCs[wp]: sym_heap_tcbSCs
  (wp: crunch_wps threadSet_tcbSCs_of_inv ignore: setSchedContext threadSet)

lemma cleanReply_sym_heap_scReplies :
  "\<lbrace>\<lambda>s. sym_heap (scReplies_of s) (\<lambda>a. if a = rptr then None else replySCs_of s a)\<rbrace>
   cleanReply rptr
   \<lbrace>\<lambda>_. sym_heap_scReplies\<rbrace>"
  unfolding cleanReply_def
  apply (clarsimp simp: bind_assoc updateReply_def)
  apply (wpsimp wp: hoare_drop_imp | wps)+
  done

lemma replyRemoveTCB_sym_heap_scReplies [wp]:
  "\<lbrace>sym_heap_scReplies and (\<lambda>s. sym_refs (list_refs_of_replies' s))\<rbrace>
   replyRemoveTCB t
   \<lbrace>\<lambda>_. sym_heap_scReplies\<rbrace>"
  supply if_split [split del]
  unfolding replyRemoveTCB_def
  apply (clarsimp simp: bind_assoc updateReply_def)
  apply wpsimp
         apply (wpsimp wp: cleanReply_sym_heap_scReplies)
        apply wp
         apply wps
         apply wpsimp
        apply (rule_tac Q="\<lambda>_ s. (replySCs_of s) (the (replyPrev reply)) = None \<and>
                 sym_heap (scReplies_of s) (\<lambda>a. if a = rptr then None else replySCs_of s a)"
               in hoare_strengthen_post[rotated], clarsimp)
        apply wpsimp
       apply (rule_tac Q="\<lambda>_ s. (replyPrev reply \<noteq> None \<longrightarrow>
                reply_at' (the (replyPrev reply)) s \<longrightarrow>
                (replySCs_of s) (the (replyPrev reply)) = None) \<and>
                sym_heap (scReplies_of s) (\<lambda>a. if a = rptr then None else replySCs_of s a)"
              in hoare_strengthen_post[rotated])
        apply (clarsimp split: if_splits simp: obj_at'_def)
       apply (wp hoare_vcg_if_lift2 hoare_vcg_imp_lift' hoare_vcg_all_lift)
         apply wps
         apply (wpsimp wp: setSchedContext_scReplies_of)
        apply wpsimp
       apply wp
        apply wps
        apply wpsimp
       apply wpsimp
      apply wpsimp
     apply (rule_tac Q="\<lambda>replya s. sym_heap_scReplies s \<and> sym_refs (list_refs_of_replies' s)"
            in hoare_strengthen_post[rotated])
      apply (clarsimp split: if_splits)
      apply (intro conjI; intro allI impI)
       apply clarsimp
       apply (intro conjI; intro allI impI)
         apply (clarsimp simp: isHead_to_head)
         apply (intro conjI; intro allI impI)
          apply clarsimp
          apply (subgoal_tac "replyPrevs_of s r = Some ya")
           apply (rule replyNexts_Some_replySCs_None)
           apply (simp add: sym_refs_replyNext_replyPrev_sym[symmetric])
          apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def projectKOs opt_map_def)
         apply (intro conjI; intro allI impI)
          apply clarsimp
          apply (drule ko_at'_inj, assumption, simp)
          apply (clarsimp simp: isHead_to_head)
          apply (subgoal_tac "replyPrevs_of s r = Some rPtr")
           apply (insert replyNexts_Some_replySCs_None)
           apply (simp add: sym_refs_replyNext_replyPrev_sym[symmetric])
           apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def projectKOs opt_map_def)
          apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def projectKOs opt_map_def)
         apply clarsimp
         apply (subgoal_tac "replyPrevs_of s r = Some ya")
          apply (rule replyNexts_Some_replySCs_None)
          apply (simp add: sym_refs_replyNext_replyPrev_sym[symmetric])
         apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def projectKOs opt_map_def)
        apply (clarsimp simp: isHead_to_head)
        apply (erule sym_heap_remove_only)
        apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def projectKOs opt_map_def pred_map_eq)
       apply (clarsimp simp: isHead_to_head)
       apply (erule rsubst2[where P=sym_heap, OF _ refl])
       apply (rule ext, clarsimp split: if_split)
       apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def projectKOs opt_map_def)
      apply (intro conjI, intro allI impI)
       apply clarsimp
       apply (subgoal_tac "replyPrevs_of s r = Some y")
        apply (rule replyNexts_Some_replySCs_None)
        apply (simp add: sym_refs_replyNext_replyPrev_sym[symmetric])
       apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def projectKOs opt_map_def)
      apply (erule rsubst2[where P=sym_heap, OF _ refl])
      apply (rule ext, clarsimp split: if_split)
      apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def projectKOs opt_map_def)
     apply (wpsimp wp: hoare_drop_imp)+
  done

crunches blockedCancelIPC, cancelSignal
  for sym_heap_scReplies[wp]: sym_heap_scReplies
  (wp: crunch_wps  ignore: setSchedContext setReply updateReply)

lemma cancelIPC_sym_heap_scReplies [wp]:
  "\<lbrace>sym_heap_scReplies and (\<lambda>s. sym_refs (list_refs_of_replies' s))\<rbrace>
   cancelIPC t
   \<lbrace>\<lambda>_. sym_heap_scReplies\<rbrace>"
  unfolding cancelIPC_def
  by (wpsimp wp: gts_wp', simp add: comp_def)

(* t = ksCurThread s *)
lemma ri_invs' [wp]:
  "\<lbrace>invs' and sch_act_not t
          and st_tcb_at' active' t
          and ex_nonz_cap_to' t
          and (\<lambda>s. \<forall>r \<in> zobj_refs' replyCap. ex_nonz_cap_to' r s)
          and (\<lambda>s. \<forall>r \<in> zobj_refs' cap. ex_nonz_cap_to' r s)
          and valid_cap' replyCap\<rbrace>
  receiveIPC t cap isBlocking replyCap
  \<lbrace>\<lambda>_. invs'\<rbrace>" (is "\<lbrace>?pre\<rbrace> _ \<lbrace>_\<rbrace>")
  supply if_split [split del]
  apply (clarsimp simp: receiveIPC_def sym_refs_asrt_def split: if_split)
  apply (rule hoare_seq_ext[OF _ stateAssert_sp])
  apply (rule hoare_seq_ext)
   apply (rule hoare_seq_ext)
    \<comment> \<open>After getEndpoint, the following holds regardless of the type of ep\<close>
    apply (rule_tac B="\<lambda>ep s. invs' s \<and> ex_nonz_cap_to' t s \<and> ex_nonz_cap_to' (capEPPtr cap) s \<and>
                              sym_heap_tcbSCs s \<and> sym_heap_scReplies s \<and>
                              st_tcb_at' simple' t s \<and> sch_act_not t s \<and> t \<noteq> ksIdleThread s \<and>
                              (\<forall>x. replyOpt = Some x \<longrightarrow> ex_nonz_cap_to' x s \<and>
                                                         reply_at' x s \<and> replyTCBs_of s x = None) \<and>
                              ko_at' ep (capEPPtr cap) s \<and>
                              (ep_at' (capEPPtr cap) s \<longrightarrow>
                               obj_at' (\<lambda>ep. ep \<noteq> IdleEP \<longrightarrow> t \<notin> set (epQueue ep)) (capEPPtr cap) s)"
                 in hoare_seq_ext)
     apply (rule_tac R1="\<lambda>s. \<forall>rptr. replyOpt = Some rptr \<longrightarrow> \<not> is_reply_linked rptr s"
            in hoare_pre_add[THEN iffD2])
      apply clarsimp
      apply (frule valid_replies'_no_tcb; clarsimp)
     apply (rename_tac ep)
     apply (case_tac ep; clarsimp)
       \<comment> \<open>RecvEP\<close>
       apply (wpsimp wp: completeSignal_invs' setEndpoint_invs' setThreadState_BlockedOnReceive_invs'
                         maybeReturnSc_invs' updateReply_replyTCB_invs' tcbEPAppend_valid_RecvEP
                         getNotification_wp gbn_wp' hoare_vcg_all_lift hoare_vcg_const_imp_lift
                   simp: if_fun_split
              | wp (once) hoare_false_imp)+
       apply (clarsimp simp: pred_tcb_at')
       apply (erule valid_objsE'[OF invs_valid_objs'])
        apply (fastforce simp: obj_at'_def projectKOs)
       apply (fastforce simp: valid_obj'_def valid_ep'_def pred_tcb_at'_def obj_at'_def )
      \<comment> \<open>IdleEP\<close>
      apply (wpsimp wp: completeSignal_invs' setEndpoint_invs' setThreadState_BlockedOnReceive_invs'
                        maybeReturnSc_invs' updateReply_replyTCB_invs' getNotification_wp gbn_wp'
                        hoare_vcg_all_lift hoare_vcg_const_imp_lift
                  simp: if_fun_split
             | wp (once) hoare_false_imp)+
      apply (fastforce simp: valid_obj'_def valid_ep'_def pred_tcb_at'_def obj_at'_def projectKOs)
     \<comment> \<open>SendEP\<close>
     apply (wpsimp wp: replyPush_invs' completeSignal_invs' sts_invs' setThreadState_st_tcb
                       threadGet_wp)
               apply (rename_tac sender queue senderState badge canGrant canGrantReply)
               apply (rule_tac Q="\<lambda>_. invs' and tcb_at' t and sch_act_not sender
                                      and st_tcb_at' (Not \<circ> is_replyState) sender
                                      and (\<lambda>s. sender \<noteq> ksIdleThread s)
                                      and sym_heap_tcbSCs and sym_heap_scReplies
                                      and ex_nonz_cap_to' sender and ex_nonz_cap_to' t
                                      and (\<lambda>s. \<forall>x. replyOpt = Some x \<longrightarrow> reply_at' x s \<and>
                                                     replyTCBs_of s x = None \<and> ex_nonz_cap_to' x s)"
                      in hoare_strengthen_post[rotated])
                apply (clarsimp simp: pred_tcb_at'_eq_commute)
                apply (fastforce simp: pred_tcb_at'_def obj_at'_real_def ko_wp_at'_def
                                       is_BlockedOnReply_def is_BlockedOnReceive_def)
               apply (wpsimp wp: hoare_vcg_imp_lift' setEndpoint_invs' maybeReturnSc_invs' hoare_vcg_all_lift
                                 getNotification_wp gbn_wp')+
     apply (clarsimp split: if_split cong: conj_cong imp_cong)
     apply (drule pred_tcb_at', clarsimp)
     apply (rename_tac sender queue ntfna ntfnb ntfnc)
     apply (frule ep_ko_at_valid_objs_valid_ep', clarsimp)
     apply (frule invs_valid_objs')
     apply (subgoal_tac "st_tcb_at' isBlockedOnSend sender s")
      apply (frule_tac t=sender in pred_tcb_at', clarsimp)
      apply (subgoal_tac "st_tcb_at' (Not \<circ> is_replyState) sender s")
       apply (clarsimp simp: o_def)
       apply (subgoal_tac "sch_act_not sender s \<and> sender \<noteq> ksIdleThread s
                           \<and> ex_nonz_cap_to' sender s \<and>
                           valid_ep' (case queue of [] \<Rightarrow> Structures_H.endpoint.IdleEP
                                      | a # list \<Rightarrow> Structures_H.endpoint.SendEP queue) s", clarsimp)
       apply (intro conjI)
          apply (erule sch_act_wf_not_runnable_sch_act_not, fastforce, clarsimp simp: isBlockedOnSend_equiv is_BlockedOnSend_def)
         apply (frule (1) st_tcb_idle'[OF invs_valid_idle'], clarsimp simp: isBlockedOnSend_equiv is_BlockedOnSend_def)
        apply (erule st_tcb_ex_cap''; clarsimp simp: isBlockedOnSend_equiv is_BlockedOnSend_def)
       apply (clarsimp simp: valid_ep'_def pred_tcb_at'_def obj_at'_real_def ko_wp_at'_def
                      split: list.splits)
      apply (fastforce elim!: pred_tcb'_weakenE
                        simp: isBlockedOnSend_def is_BlockedOnReply_def
                              is_BlockedOnReceive_def)
     apply (clarsimp simp: valid_ep'_def pred_tcb_at'_def obj_at'_real_def ko_wp_at'_def
                           isSend_equiv isBlockedOnSend_equiv, fastforce)
    \<comment> \<open>Resolve common precondition\<close>
    apply (simp (no_asm_use) cong: conj_cong
           | wpsimp wp: cancelIPC_st_tcb_at'_different_thread cancelIPC_notin_epQueue
                        cancelIPC_replyTCBs_of_None hoare_vcg_all_lift getEndpoint_wp
                        hoare_drop_imp[where R="\<lambda>_ s. \<exists>ko. ko_at' ko _ s"] hoare_vcg_imp_lift')+
  apply (rename_tac s)
  apply (clarsimp simp: comp_def invs'_def valid_state'_def valid_pspace'_def if_distribR
                  cong: conj_cong imp_cong)
  apply (frule (2) sym_refs_tcbSCs)
  apply (frule (2) sym_refs_scReplies)
  apply (prop_tac "\<forall>ep. ko_at' ep (capEPPtr cap) s \<longrightarrow> ep \<noteq> IdleEP \<longrightarrow> t \<notin> set (epQueue ep)")
   apply (clarsimp simp: pred_tcb_at'_def obj_at'_def projectKOs)
   apply (drule_tac ko="ko :: endpoint" for ko in sym_refs_ko_atD'[rotated])
    apply (fastforce simp: obj_at'_def projectKOs)
   apply (fastforce simp: ep_q_refs_of'_def refs_of_rev' ko_wp_at'_def split: endpoint.splits)
  apply (prop_tac "\<forall>r g. replyCap = ReplyCap r g \<longrightarrow> \<not>obj_at' (\<lambda>a. replyTCB a = Some t) r s")
   apply (clarsimp simp: pred_tcb_at'_def obj_at'_def projectKOs)
   apply (drule_tac ko="ko :: reply" for ko in sym_refs_ko_atD'[rotated])
    apply (fastforce simp: obj_at'_def projectKOs)
   apply (fastforce simp: refs_of_rev' ko_wp_at'_def tcb_bound_refs'_def get_refs_def
                   split: option.splits)
  apply (prop_tac "ex_nonz_cap_to' (capEPPtr cap) s \<and> st_tcb_at' simple' t s \<and>
                      t \<noteq> ksIdleThread s \<and> (ep_at' (capEPPtr cap) s \<longrightarrow>
                      obj_at' (\<lambda>ep. ep \<noteq> Structures_H.endpoint.IdleEP \<longrightarrow> t \<notin> set (epQueue ep))
                      (capEPPtr cap) s)")
   apply (fastforce simp: valid_idle'_def idle_tcb'_def pred_tcb_at'_def obj_at'_def projectKOs
                          isCap_simps isSend_def)
  apply (fastforce simp: opt_map_def obj_at'_def projectKOs valid_cap'_def split: if_split)
  done

lemma bindScReply_st_tcb_at'[wp]:
  "\<lbrace>\<lambda>s. P (st_tcb_at' P' t s)\<rbrace>
   bindScReply scPtr replyPtr
   \<lbrace>\<lambda>_ s. P (st_tcb_at' P' t s)\<rbrace>"
  apply (clarsimp simp: bindScReply_def)
  by (wpsimp wp: crunch_wps)

lemma replyPush_st_tcb_at'_not_caller:
  "\<lbrace>\<lambda>s. P (st_tcb_at' P' t s) \<and> t \<noteq> callerPtr\<rbrace>
   replyPush callerPtr calleePtr replyPtr canDonate
   \<lbrace>\<lambda>_ s. P (st_tcb_at' P' t s)\<rbrace>"
  apply (clarsimp simp: replyPush_def)
  by (wpsimp wp: sts_st_tcb_at'_cases_strong hoare_vcg_imp_lift)

lemma replyUnlink_invs':
  "\<lbrace>\<lambda>s. invs' s \<and> tcbPtr \<noteq> ksIdleThread s
        \<and> (replyTCBs_of s replyPtr = Some tcbPtr \<longrightarrow> \<not> is_reply_linked replyPtr s)\<rbrace>
   replyUnlink replyPtr tcbPtr
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  unfolding invs'_def valid_state'_def valid_dom_schedule'_def
  by wpsimp

lemma asUser_pred_tcb_at'[wp]:
  "asUser tptr f \<lbrace>\<lambda>s. P (pred_tcb_at' proj test t s)\<rbrace>"
  unfolding asUser_def
  by (wpsimp wp: mapM_wp' threadSet_pred_tcb_no_state crunch_wps
           simp: tcb_to_itcb'_def)

lemma setCTE_pred_tcb_at':
  "setCTE ptr val \<lbrace>\<lambda>s. P (pred_tcb_at' proj test t s)\<rbrace> "
  apply (simp add: setCTE_def pred_tcb_at'_def)
  apply (rule setObject_cte_obj_at_tcb'; simp add: tcb_to_itcb'_def)
  done

crunches doIPCTransfer
  for pred_tcb_at''[wp]: "\<lambda>s. P (pred_tcb_at' proj test t s)"
  (wp: setCTE_pred_tcb_at' getCTE_wp mapM_wp' simp: cte_wp_at'_def zipWithM_x_mapM)

lemma si_invs'_helper2:
  "\<lbrace>\<lambda>s. invs' s \<and> sch_act_not t s \<and> st_tcb_at' active' t s \<and>
        st_tcb_at' (Not \<circ> is_BlockedOnReply) d s \<and>
        ex_nonz_cap_to' t s \<and> ex_nonz_cap_to' d s \<and>
        sym_heap_tcbSCs s \<and> sym_heap_scReplies s \<and>
        (\<forall>reply. replyObject recvState = Some reply \<longrightarrow> ex_nonz_cap_to' reply s \<and> reply_at' reply s
                 \<and> replyTCBs_of s reply = None) \<and>
        (cd \<and> scOptDest = Nothing \<longrightarrow> bound_sc_tcb_at' ((=) None) d s \<and>
        (\<exists>scptr. bound_sc_tcb_at' (\<lambda>scp. scp = (Some scptr)) t s \<and> ex_nonz_cap_to' scptr s)) \<and>
        t \<noteq> d\<rbrace>
   if call \<or> (\<exists>y. fault = Some y)
   then if (cg \<or> cgr) \<and> (\<exists>y. replyObject recvState = Some y)
        then replyPush t d (the (replyObject recvState)) cd
        else setThreadState Structures_H.thread_state.Inactive t
   else when (cd \<and> scOptDest = None) (do
          scOptSrc <- threadGet tcbSchedContext t;
          schedContextDonate (the scOptSrc) d
        od)
  \<lbrace>\<lambda>b s. invs' s \<and> tcb_at' d s \<and> ex_nonz_cap_to' d s \<and> st_tcb_at' (Not \<circ> is_BlockedOnReply) d s\<rbrace>"
  apply (wpsimp wp: ex_nonz_cap_to_pres' schedContextDonate_invs' replyPush_invs' sts_invs_minor'
                    replyPush_st_tcb_at'_not_caller sts_st_tcb' threadGet_wp)
  apply (frule_tac P'="(\<lambda>st'. \<forall>rptr. st' \<noteq> BlockedOnReply rptr)" in pred_tcb'_weakenE)
   apply (clarsimp simp: is_BlockedOnReply_def)
  apply (frule pred_tcb_at')
  apply (frule_tac t=d in pred_tcb_at')
  apply (frule_tac P'="Not \<circ> is_replyState" in pred_tcb'_weakenE)
   apply (fastforce simp: is_BlockedOnReply_def is_BlockedOnReceive_def)
  apply (frule invs_valid_objs')
  apply (frule invs_valid_idle')
  apply (subgoal_tac "t \<noteq> ksIdleThread s")
   apply (clarsimp simp: tcb_at'_ex_eq_all o_def)
   apply (intro conjI)
    apply (clarsimp simp: pred_tcb_at'_def obj_at'_real_def ko_wp_at'_def projectKO_tcb)
   apply (rule not_idle_scTCB, clarsimp, clarsimp, clarsimp)
    apply (frule not_idle_tcbSC[where p=t], clarsimp, clarsimp)
      apply (clarsimp simp: valid_idle'_def)
     apply (clarsimp simp: valid_state'_def pred_tcb_at'_def obj_at'_def valid_tcb_state'_def)
    apply (clarsimp simp: pred_tcb_at'_def obj_at'_real_def ko_wp_at'_def projectKO_tcb)
   apply (frule (1) tcb_ko_at_valid_objs_valid_tcb')
   apply (clarsimp simp: valid_tcb'_def pred_tcb_at'_def obj_at'_real_def ko_wp_at'_def projectKO_tcb)
  apply (fastforce simp: invs'_def valid_state'_def dest: global'_no_ex_cap)
  done

lemma replyUnlink_obj_at_tcb_none:
  "\<lbrace>K (rptr' = rptr)\<rbrace>
   replyUnlink rptr tptr
   \<lbrace>\<lambda>_. obj_at' (\<lambda>reply. replyTCB reply = None) rptr'\<rbrace>"
  apply (simp add: replyUnlink_def)
  apply (wpsimp wp: updateReply_wp_all gts_wp')
  by (auto simp: obj_at'_def projectKOs objBitsKO_def)

(* FIXME RT: si_invs' already exists, and should perhaps be renamed *)
lemma si_invs'2[wp]:
  "\<lbrace>invs' and st_tcb_at' active' t
          and sch_act_not t
          and (\<lambda>s. cd \<longrightarrow> bound_sc_tcb_at' (\<lambda>a. a \<noteq> None) t s)
          and ex_nonz_cap_to' ep and ex_nonz_cap_to' t\<rbrace>
   sendIPC bl call ba cg cgr cd t ep
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  supply if_split[split del]
  apply (simp add: sendIPC_def)
  apply (rule hoare_seq_ext[OF _ stateAssert_sp])
  apply (rule hoare_seq_ext [OF _ get_ep_sp'])
  apply (rename_tac ep')
  apply (case_tac ep')
    \<comment> \<open>ep' = RecvEP\<close>
    apply (rename_tac list)
    apply (case_tac list; simp)
    apply (wpsimp wp: possibleSwitchTo_invs')
             apply (wpsimp wp: setThreadState_st_tcb setThreadState_Running_invs')
            apply (wpsimp wp: si_invs'_helper2)
           apply wpsimp
          apply (wpsimp wp: threadGet_wp)
         apply (rule_tac Q="\<lambda>_ s. invs' s \<and> st_tcb_at' active' t s \<and> sch_act_not t s \<and>
                                  st_tcb_at' (Not \<circ> is_BlockedOnReply) a s \<and>
                                  ex_nonz_cap_to' t s \<and> ex_nonz_cap_to' a s \<and>
                                  (\<forall>x. replyObject recvState = Some x \<longrightarrow>
                                         ex_nonz_cap_to' x s \<and> reply_at' x s \<and>
                                         replyTCBs_of s x = None) \<and>
                                  sym_heap_tcbSCs s \<and> sym_heap_scReplies s \<and>
                                  (cd \<longrightarrow> (\<exists>scptr. bound_sc_tcb_at' (\<lambda>scp. scp = Some scptr) t s \<and>
                                                   ex_nonz_cap_to' scptr s)) \<and>
                                  t \<noteq> a"
                in hoare_strengthen_post[rotated])
          apply (fastforce simp: obj_at'_def projectKO_eq projectKO_tcb
                                 pred_tcb_at'_def invs'_def valid_state'_def
                          dest!: global'_no_ex_cap)
         apply (wpsimp wp: replyUnlink_invs' replyUnlink_st_tcb_at' replyUnlink_obj_at_tcb_none
                           hoare_vcg_ex_lift hoare_vcg_imp_lift')
        apply (rule_tac Q="\<lambda>_ s. invs' s \<and> st_tcb_at' active' t s \<and> sch_act_not t s \<and>
                                 st_tcb_at' is_BlockedOnReceive a s \<and>
                                 ex_nonz_cap_to' t s \<and> ex_nonz_cap_to' a s \<and> a \<noteq> t \<and>
                                 sym_heap_tcbSCs s \<and> sym_heap_scReplies s \<and>
                                 (\<forall>x. replyObject recvState = Some x \<longrightarrow>
                                        ex_nonz_cap_to' x s \<and> reply_at' x s \<and>
                                        (replyTCBs_of s x = Some a \<longrightarrow>
                                         \<not> is_reply_linked x s)) \<and>
                                 (cd \<longrightarrow> (\<exists>scptr. bound_sc_tcb_at' (\<lambda>scp. scp = Some scptr) t s \<and> ex_nonz_cap_to' scptr s))"
               in hoare_strengthen_post[rotated])
         apply (auto simp: obj_at'_def projectKO_eq projectKO_tcb
                           pred_tcb_at'_def invs'_def valid_state'_def
                           is_BlockedOnReceive_def is_BlockedOnReply_def
                    dest!: global'_no_ex_cap)[1]
        apply (wpsimp simp: invs'_def valid_state'_def valid_dom_schedule'_def valid_pspace'_def
                            comp_def sym_refs_asrt_def
                        wp: hoare_vcg_all_lift hoare_vcg_ex_lift hoare_vcg_imp_lift' gts_wp')+
    apply (intro conjI; clarsimp?)
           apply (force simp: obj_at'_def projectKO_eq projectKO_ep valid_obj'_def valid_ep'_def
                        elim: valid_objsE' split: list.splits)
          apply (fastforce simp: pred_tcb_at'_eq_commute pred_tcb_at'_def obj_at'_def
                                 is_BlockedOnReceive_def isReceive_def
                          split: thread_state.splits)
         apply (fastforce simp: pred_tcb_at'_def ko_wp_at'_def obj_at'_def
                                projectKO_eq projectKO_tcb isReceive_def
                          elim: if_live_then_nonz_capE' split: thread_state.splits)
        apply (fastforce simp: pred_tcb_at'_def ko_wp_at'_def obj_at'_def
                               projectKO_eq projectKO_tcb isReceive_def
                        split: thread_state.splits)
       apply (erule (2) sym_refs_tcbSCs)
      apply (erule (2) sym_refs_scReplies)
     apply (simp flip: conj_assoc, rule conjI)
      apply (subgoal_tac "ko_wp_at' live' xb s \<and> reply_at' xb s", clarsimp)
       apply (erule (1) if_live_then_nonz_capE')
      apply (clarsimp simp: pred_tcb_at'_def obj_at'_def projectKO_eq projectKO_tcb)
      apply (drule_tac p=a and ko="obja" in sym_refs_ko_atD'[rotated])
       apply (clarsimp simp: obj_at'_def projectKO_eq projectKO_tcb)
      apply (clarsimp simp: isReceive_def refs_of_rev' ko_wp_at'_def live_reply'_def
                     split: thread_state.splits)
     apply (rule impI)
     apply (drule (1) valid_replies'_other_state; clarsimp simp: isReceive_def)
    apply (clarsimp simp: pred_tcb_at'_def obj_at'_def projectKO_eq projectKO_tcb)
    apply (erule if_live_then_nonz_capE')
    apply (drule_tac ko=obj and p=t in sym_refs_ko_atD'[rotated])
     apply (clarsimp simp: obj_at'_def projectKO_eq projectKO_tcb)
    apply (clarsimp simp: ko_wp_at'_def obj_at'_def projectKO_eq  projectKO_tcb
                          refs_of_rev' live_sc'_def valid_idle'_def idle_tcb'_def)
   apply (clarsimp simp: pred_tcb_at'_def obj_at'_def isReceive_def is_BlockedOnReply_def)
  \<comment> \<open>epa = IdleEP\<close>
   apply (cases bl)
    apply (wpsimp wp: sts_sch_act' sts_valid_queues setThreadState_ct_not_inQ
                simp: invs'_def valid_state'_def valid_dom_schedule'_def valid_ep'_def)
    apply (fastforce simp: valid_tcb_state'_def valid_idle'_def pred_tcb_at'_def obj_at'_def
                           projectKO_eq projectKO_tcb idle_tcb'_def comp_def)
   apply wpsimp
  \<comment> \<open>ep' = SendEP\<close>
  apply (cases bl)
   apply (wpsimp wp: tcbEPAppend_valid_SendEP sts_sch_act' sts_valid_queues setThreadState_ct_not_inQ
                     sts'_valid_replies'
               simp: invs'_def valid_state'_def valid_dom_schedule'_def valid_pspace'_def
                     valid_ep'_def sym_refs_asrt_def)
   apply (erule valid_objsE'[where x=ep], fastforce simp: obj_at'_def projectKO_eq projectKO_ep)
   apply (drule_tac ko="SendEP xa" in sym_refs_ko_atD'[rotated])
    apply (fastforce simp: obj_at'_def projectKO_eq projectKO_ep)
   apply (clarsimp simp: comp_def obj_at'_def pred_tcb_at'_def valid_idle'_def
                         valid_tcb_state'_def valid_obj'_def valid_ep'_def
                         idle_tcb'_def projectKO_eq projectKO_tcb)
   apply (fastforce simp: ko_wp_at'_def refs_of_rev')
  apply wpsimp
  done

lemma sfi_invs_plus':
  "\<lbrace>invs' and st_tcb_at' active' t
          and sch_act_not t
          and (\<lambda>s. canDonate \<longrightarrow> bound_sc_tcb_at' (\<lambda>a. a \<noteq> None) t s)
          and ex_nonz_cap_to' t
          and (\<lambda>s. \<exists>n\<in>dom tcb_cte_cases. \<exists>cte. cte_wp_at' (\<lambda>cte. cteCap cte = cap) (t + n) s)\<rbrace>
      sendFaultIPC t cap f canDonate
   \<lbrace>\<lambda>_. invs'\<rbrace>,
   \<lbrace>\<lambda>_. invs' and st_tcb_at' active' t
              and sch_act_not t
              and (\<lambda>s. canDonate \<longrightarrow> bound_sc_tcb_at' (\<lambda>a. a \<noteq> None) t s)
              and ex_nonz_cap_to' t
              and (\<lambda>s. \<exists>n\<in>dom tcb_cte_cases. cte_wp_at' (\<lambda>cte. cteCap cte = cap) (t + n) s)\<rbrace>"
  apply (simp add: sendFaultIPC_def)
  apply (wp threadSet_invs_trivial threadSet_pred_tcb_no_state
            threadSet_cap_to'
           | wpc | simp)+
  apply (intro conjI impI allI; (fastforce simp: inQ_def)?)
   apply (clarsimp simp: invs'_def valid_state'_def valid_release_queue'_def obj_at'_def)
  apply (fastforce simp: ex_nonz_cap_to'_def cte_wp_at'_def)
  done

lemma hf_corres:
  assumes "fr f f'"
  shows "corres dc (invs and valid_list and valid_sched_action
                         and scheduler_act_not t and st_tcb_at active t
                         and ex_nonz_cap_to t and K (valid_fault f))
                   (invs' and sch_act_not t and st_tcb_at' active' t and ex_nonz_cap_to' t)
                   (handle_fault t f) (handleFault t f')"
  using assms
  apply (simp add: handle_fault_def handleFault_def)
  apply (rule corres_gen_asm)
  apply (rule corres_guard_imp)
    apply (rule corres_split_deprecated)
       apply (rule corres_split_eqr)
          apply (rule corres_split_eqr)
             apply (clarsimp simp: handle_no_fault_def handleNoFaultHandler_def unless_def when_def)
             apply (rule sts_corres, simp)
            apply (rule corres_split_catch[OF _ send_fault_ipc_corres])
                 apply fastforce+
             apply wp
            apply wp
           apply (rule_tac Q="\<lambda>_ s. invs s \<and> tcb_at t s" in hoare_strengthen_post[rotated])
            apply (clarsimp simp: invs_def valid_state_def valid_pspace_def)
           apply wp
          apply (rule hoare_strengthen_post[OF catch_wp[OF _ sfi_invs_plus']])
           apply wpsimp
          apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def)
         apply (simp only: get_tcb_obj_ref_def)
         apply (rule threadget_corres, clarsimp simp: tcb_relation_def)
        apply (wp gbn_inv get_tcb_obj_ref_wp)
       apply (wp hoare_vcg_imp_lift' threadGet_wp)
      apply (rule corres_rel_imp[OF assert_get_tcb_corres])
      apply (clarsimp simp: tcb_relation_def)
     apply wp
    apply (wp getObject_tcb_wp)
   apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb_def get_tcb_def cong: conj_cong)
   apply (intro conjI)
     apply (fastforce dest: invs_valid_objs simp: valid_obj_def valid_tcb_def tcb_cap_cases_def)
    apply (fastforce dest: invs_valid_objs simp: valid_obj_def valid_tcb_def tcb_cap_cases_def)
   apply (rule_tac x=3 in exI)
   apply (fastforce simp: caps_of_state_tcb_index_trans get_tcb_def tcb_cnode_map_def)
  apply (clarsimp simp: valid_tcb_def ran_tcb_cap_cases)
  apply (clarsimp simp: pred_tcb_at'_def obj_at'_def projectKOs)
  apply (drule_tac p=t and k="ko :: tcb" for ko in ko_at_valid_objs'[rotated, OF invs_valid_objs'])
    apply (fastforce simp: obj_at'_def projectKOs)+
  apply (rule conjI)
   apply (clarsimp simp: valid_obj'_def valid_tcb'_def tcb_cte_cases_def)
  apply (rule_tac x="0x30" in bexI)
   apply (auto elim: cte_wp_at_tcbI' simp: objBitsKO_def return_def tcb_cte_cases_def)
  done

lemma handleTimeout_corres:
  assumes "fr f f'"
  shows "corres dc (invs and valid_list and valid_sched_action
                         and scheduler_act_not t and st_tcb_at active t
                         and cte_wp_at is_ep_cap (t,tcb_cnode_index 4) and K (valid_fault f))
                   invs'
                   (handle_timeout t f) (handleTimeout t f')"
  (is "corres _ ?G ?G' _ _")
  using assms
  apply (clarsimp simp: handle_timeout_def handleTimeout_def)
  apply (rule corres_gen_asm)
  apply (rule_tac Q="?G" and Q'="?G' and obj_at' (isEndpointCap \<circ> cteCap \<circ> tcbTimeoutHandler) t"
               in stronger_corres_guard_imp)
    apply (rule corres_symb_exec_r)
       apply (rule corres_assert_assume_r)
       apply (rule corres_guard_imp)
         apply (rule corres_split_deprecated[OF _ assert_get_tcb_corres])
           apply (rule corres_assert_assume_l)
           apply (rule corres_split_deprecated)
              apply clarsimp
             apply (rule corres_split_catch[OF _ send_fault_ipc_corres])
                  apply (fastforce simp: tcb_relation_def)+
              apply (wp getTCB_wp)+
        apply (fastforce simp: pred_tcb_at_def cte_wp_at_def obj_at_def is_tcb_def get_cap_def gets_the_def
                               get_object_def get_tcb_def valid_obj_def valid_tcb_def bind_def
                               return_def tcb_cap_cases_def tcb_cnode_map_def simpler_gets_def
                         dest: invs_valid_objs)
       apply assumption
      apply (wpsimp wp: getTCB_wp simp: isValidTimeoutHandler_def)
      apply (fastforce simp: isCap_simps pred_tcb_at'_def obj_at'_def projectKOs
                             valid_obj'_def valid_tcb'_def tcb_cte_cases_def
                       dest: invs_valid_objs')
     apply (wpsimp wp: hoare_drop_imps simp: isValidTimeoutHandler_def)+
  apply (frule cross_relF[OF _ tcb_at'_cross_rel[where t=t]], fastforce)
  apply (clarsimp simp: pred_tcb_at_def pred_tcb_at'_def obj_at_def obj_at'_def
                        is_tcb_def projectKOs state_relation_def pspace_relation_def)
  apply (erule_tac x=t in ballE)
   apply (auto simp: other_obj_relation_def tcb_relation_def cap_relation_def
                     cte_wp_at_caps_of_state caps_of_state_def tcb_cnode_map_def
                     get_object_def get_tcb_def get_cap_def simpler_gets_def
                     return_def bind_def is_cap_simps isCap_simps gets_the_def)
  done

lemma hf_invs' [wp]:
  "\<lbrace>invs' and sch_act_not t
          and st_tcb_at' active' t
          and ex_nonz_cap_to' t\<rbrace>
   handleFault t f
   \<lbrace>\<lambda>r. invs'\<rbrace>"
  apply (simp add: handleFault_def handleNoFaultHandler_def sendFaultIPC_def)
  apply (wpsimp wp: sts_invs_minor' threadSet_invs_trivialT threadSet_pred_tcb_no_state getTCB_wp
                    threadGet_wp threadSet_cap_to' hoare_vcg_all_lift hoare_vcg_imp_lift'
        | fastforce simp: tcb_cte_cases_def)+
  apply (clarsimp simp: invs'_def valid_state'_def inQ_def)
  apply (subgoal_tac "st_tcb_at' (\<lambda>st'. tcb_st_refs_of' st' = {}) t s \<and> t \<noteq> ksIdleThread s")
   apply (rule_tac x=ko in exI)
   apply (clarsimp simp: pred_tcb_at'_def obj_at'_def)
   apply (intro conjI impI allI; clarsimp?)
    apply (clarsimp simp: valid_release_queue'_def obj_at'_def)
   apply (clarsimp simp: ex_nonz_cap_to'_def return_def fail_def oassert_opt_def
                         projectKO_def projectKO_tcb
                  split: option.splits)
   apply (rule_tac x="t+0x30" in exI)
   apply (fastforce elim: cte_wp_at_tcbI' simp: objBitsKO_def)
  apply (fastforce simp: pred_tcb_at'_def obj_at'_def valid_idle'_def idle_tcb'_def)
  done

lemma gts_st_tcb':
  "\<lbrace>\<top>\<rbrace> getThreadState t \<lbrace>\<lambda>r. st_tcb_at' (\<lambda>st. st = r) t\<rbrace>"
  apply (rule hoare_strengthen_post)
  apply (rule gts_sp')
  apply simp
  done

lemma si_blk_makes_simple':
  "\<lbrace>st_tcb_at' simple' t and K (t \<noteq> t')\<rbrace>
     sendIPC True call bdg cg cgr cd t' ep
   \<lbrace>\<lambda>rv. st_tcb_at' simple' t\<rbrace>"
  apply (simp add: sendIPC_def)
  apply (rule hoare_seq_ext [OF _ stateAssert_sp])
  apply (rule hoare_seq_ext [OF _ get_ep_inv'])
  sorry (* si_blk_makes_simple' *)
  (*
  apply (case_tac xa, simp_all)
    apply (rename_tac list)
    apply (case_tac list, simp_all add: case_bool_If case_option_If
                             split del: if_split cong: if_cong)
    apply (rule hoare_pre)
     apply (wp sts_st_tcb_at'_cases setupCallerCap_pred_tcb_unchanged
               hoare_drop_imps)
    apply (clarsimp simp: pred_tcb_at' del: disjCI)
   apply (wp sts_st_tcb_at'_cases)
   apply clarsimp
  apply (wp sts_st_tcb_at'_cases)
  apply clarsimp
  done *)

lemma si_blk_makes_runnable':
  "\<lbrace>st_tcb_at' runnable' t and K (t \<noteq> t')\<rbrace>
     sendIPC True call bdg cg cgr cd t' ep
   \<lbrace>\<lambda>rv. st_tcb_at' runnable' t\<rbrace>"
  apply (simp add: sendIPC_def)
  apply (rule hoare_seq_ext [OF _ stateAssert_sp])
  apply (rule hoare_seq_ext [OF _ get_ep_inv'])
  sorry (* si_blk_makes_runnable' *)
  (*
  apply (case_tac xa, simp_all)
    apply (rename_tac list)
    apply (case_tac list, simp_all add: case_bool_If case_option_If
                             split del: if_split cong: if_cong)
    apply (rule hoare_pre)
     apply (wp sts_st_tcb_at'_cases setupCallerCap_pred_tcb_unchanged
               hoare_vcg_const_imp_lift hoare_drop_imps
              | simp)+
    apply (clarsimp del: disjCI simp: pred_tcb_at' elim!: pred_tcb'_weakenE)
   apply (wp sts_st_tcb_at'_cases)
   apply clarsimp
  apply (wp sts_st_tcb_at'_cases)
  apply clarsimp
  done *)

crunches possibleSwitchTo, completeSignal
  for pred_tcb_at'[wp]: "pred_tcb_at' proj P t"

crunches replyRemove
  for ksSchedulerAction[wp]: "\<lambda>s. P (ksSchedulerAction s)"
  (simp: crunch_simps)

crunch inv[wp]: getSanitiseRegisterInfo P

lemma handleFaultReply_invs[wp]:
  "\<lbrace>invs' and tcb_at' t\<rbrace> handleFaultReply x t label msg \<lbrace>\<lambda>rv. invs'\<rbrace>"
  unfolding handleFaultReply_def
  by (cases x; wpsimp simp: handleArchFaultReply_def split: arch_fault.split)

lemma doReplyTransfer_corres:
  "corres dc
     (einvs and reply_at reply and tcb_at sender)
     invs'
     (do_reply_transfer sender reply grant)
     (doReplyTransfer sender reply grant)"
  supply if_split [split del]
  apply (simp add: do_reply_transfer_def doReplyTransfer_def cong: option.case_cong)
  apply (rule stronger_corres_guard_imp)
    apply (rule corres_split [OF getReply_TCB_corres])
      apply (simp add: maybeM_def)
      apply (rule corres_option_split [OF refl corres_return_trivial])
      apply (rename_tac recv_opt receiverOpt recvr)
      apply (rule_tac Q="\<lambda>s. einvs s \<and> tcb_at sender s \<and> tcb_at recvr s \<and>
                             reply_tcb_reply_at (\<lambda>xa. xa = Some recvr) reply s" and
                      Q'="invs'"
             in corres_split [OF _ _ gts_sp gts_sp' ])
       apply (rule gts_corres, rename_tac ts ts')
      apply (case_tac ts; simp add: isReply_def)
      apply (rule stronger_corres_guard_imp)
        apply (rule corres_assert_assume_l)
        apply (rule corres_split [OF replyRemove_corres])
          apply (rule corres_split [OF threadget_fault_corres])
            apply (rule corres_split)
               apply (rule_tac P="tcb_at sender and tcb_at recvr and valid_objs and pspace_aligned and
                                  valid_list and pspace_distinct and valid_mdb and cur_tcb" and
                               P'="tcb_at' sender and tcb_at' recvr and valid_pspace' and cur_tcb' and
                                   valid_release_queue and valid_release_queue'"
                      in corres_guard_imp)
                 apply (simp add: fault_rel_optionation_def)
                 apply (rule corres_option_split; simp)
                  apply (rule corres_split [OF dit_corres sts_corres])
                    apply (clarsimp simp: thread_state_relation_def)
                   prefer 3
                   apply (rule corres_split_mapr [OF _ get_mi_corres])
                     apply (rule corres_split_eqr [OF _ lipcb_corres'])
                       apply (rule corres_split_eqr [OF _ get_mrs_corres])
                          apply (simp (no_asm) del: dc_simp)
                          apply (rule corres_split_eqr [OF _ handle_fault_reply_corres])
                             apply (rule corres_split [OF threadset_corresT sts_corres])
                                  apply (clarsimp simp: tcb_relation_def fault_rel_optionation_def)
                                 apply (clarsimp simp: tcb_cap_cases_def)
                                apply (clarsimp simp: tcb_cte_cases_def)
                               apply (clarsimp simp: thread_state_relation_def split: if_split)
                              (* solving hoare_triples *)
                              apply (clarsimp simp: valid_tcb_state_def)
                              apply (rule_tac Q="\<lambda>_. valid_objs and pspace_aligned and
                                                     pspace_distinct and tcb_at recvr" in
                                      hoare_strengthen_post[rotated])
                               apply (clarsimp simp: valid_objs_valid_tcbs)
                              apply (wpsimp wp: thread_set_fault_valid_objs)
                             apply (wpsimp wp: threadSet_valid_tcbs' threadSet_valid_release_queue_inv
                                               threadSet_valid_release_queue'_inv)
                            apply simp
                           apply (clarsimp simp: pred_conj_def cong: conj_cong)
                           apply wpsimp+
                          apply (strengthen valid_objs'_valid_tcbs')
                          apply wpsimp+
                  apply (strengthen valid_objs_valid_tcbs)
                  apply wpsimp+
                 apply (strengthen valid_objs'_valid_tcbs')
                 apply wpsimp
                apply (clarsimp split: option.splits)
               apply (clarsimp split: option.splits simp: valid_pspace'_def)
              apply (clarsimp simp: isRunnable_def get_tcb_obj_ref_def)
              (* solve remaining corres goals *)
              apply (rule corres_split [OF gts_corres])
                apply (rule corres_split [OF threadget_corres[where r="(=)"]])
                   apply (simp add: tcb_relation_def)
                  apply (rename_tac scopt scopt')
                  apply (rule corres_when)
                   apply (case_tac state; simp add: thread_state_relation_def)
                  apply (rule corres_assert_opt_assume_l)
                  apply (rule_tac Q="valid_sched_action and tcb_at recvr
                                     and sc_tcb_sc_at (\<lambda>a. a \<noteq> None) (the scopt) and
                                     active_sc_at (the scopt) and valid_refills (the scopt) and
                                     valid_release_q and active_sc_valid_refills and
                                     (\<lambda>s. sc_tcb_sc_at (\<lambda>sc. \<exists>t. sc = Some t \<and> not_queued t s) (the scopt) s) and
                                     invs and valid_list and scheduler_act_not recvr
                                     and st_tcb_at active recvr"
                              and Q'="invs' and tcb_at' recvr and sc_at' (the scopt)"
                              and P'="invs' and sc_at' (the scopt') and tcb_at' recvr"
                              and P="valid_sched_action and tcb_at recvr and
                                     sc_tcb_sc_at (\<lambda>a. a \<noteq> None) (the scopt) and
                                     active_sc_at (the scopt) and valid_refills (the scopt) and
                                     valid_release_q and active_sc_valid_refills and
                                     (\<lambda>s. sc_tcb_sc_at (\<lambda>sc. \<exists>t. sc = Some t \<and> not_queued t s) (the scopt) s) and
                                     invs and valid_list and scheduler_act_not recvr and st_tcb_at active recvr"
                         in stronger_corres_guard_imp)

                    (* this next section by somewhat complicated symbolic executions *)
                    apply (rule corres_symb_exec_l [OF _ _ get_sched_context_sp], rename_tac sc)
                      apply (rule corres_symb_exec_l [OF _ _ gets_sp], rename_tac ct)
                        apply (rule corres_symb_exec_r [OF _ refillReady_sp], rename_tac ready)
                          apply (rule corres_symb_exec_r [OF _ refillSufficient_sp], rename_tac suff)
                            apply (rule_tac Q="\<lambda>_. ready = sc_refill_ready ct sc \<and> suff = sc_refill_sufficient 0 sc" in corres_cross_add_guard[rotated])
                             apply (rule_tac corres_gen_asm2)
                             apply (rule stronger_corres_guard_imp)
                               apply (rule corres_if, simp)
                                apply (rule possibleSwitchTo_corres)
                               apply (rule corres_symb_exec_r[OF _ get_sc_sp'], rename_tac sc')
                                 apply (rule_tac Q="\<lambda>_. sc_badge sc = scBadge sc'" in corres_cross_add_guard[rotated])
                                  apply (rule_tac corres_gen_asm2)
                                  apply (rule_tac Q="\<lambda>s. active_sc_valid_refills s \<and>
                                           is_active_sc (the scopt') s \<and>
                                           sc_tcb_sc_at (\<lambda>sc. \<exists>t. sc = Some t \<and> not_queued t s) (the scopt) s \<and>
                                           invs s \<and> valid_release_q s \<and> tcb_at recvr s \<and>
                                           valid_list s \<and> valid_sched_action s \<and>
                                           scheduler_act_not recvr s \<and> st_tcb_at active recvr s"
                                         in corres_guard_imp)
                                    apply (rule corres_symb_exec_l [OF _ _ gets_the_get_tcb_sp], rename_tac tcb)
                                      apply (rule_tac Q'="\<lambda>s. invs' s \<and> (\<forall>ko. ko_at' ko recvr s \<longrightarrow>
                                               capability.is_EndpointCap (cteCap (tcbTimeoutHandler ko)) =
                                               is_ep_cap (tcb_timeout_handler tcb)) \<and> tcb_at' recvr s"
                                             and P'="\<lambda>s. invs' s \<and> tcb_at' recvr s"
                                             in stronger_corres_guard_imp)
                                        apply (rule corres_symb_exec_r [OF _ isValidTimeoutHandler_sp], rename_tac isHV)
                                          apply (rule corres_symb_exec_r, rename_tac isT)
                                             apply (rule_tac F="isHV = is_ep_cap (tcb_timeout_handler tcb) \<and>
                                                      isT = (case fault of None \<Rightarrow> False | Some a \<Rightarrow> is_timeout_fault a)"
                                                    in corres_gen_asm2)
                                             apply (rule corres_if2[OF _ handleTimeout_corres, rotated])
                                               apply (clarsimp)
                                              apply (simp, rule postpone_corres)
                                             apply simp
                                            apply wpsimp
                                            apply (clarsimp simp: fault_rel_optionation_def if_distribR)
                                            apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def)
                                            apply (auto simp: is_timeout_fault_def fault_map_def split: ExceptionTypes_A.fault.splits)[1]

                                           (* solve final hoare triple goals *)
                                           apply wpsimp
                                          apply wpsimp
                                         apply (wpsimp wp: hoare_drop_imp simp: isValidTimeoutHandler_def)
                                        apply (wpsimp simp: isValidTimeoutHandler_def)
                                       apply (clarsimp split: if_split simp: valid_fault_def)
                                       apply (clarsimp simp: tcb_cnode_map_def obj_at_def TCB_cte_wp_at_obj_at)
                                      apply (clarsimp simp: obj_at_def)
                                      apply (frule (1) pspace_relation_absD[OF _ state_relation_pspace_relation])
                                      apply (clarsimp simp: other_obj_relation_def obj_at'_def projectKOs tcb_relation_def)
                                      apply (case_tac "cteCap (tcbTimeoutHandler ko)";
                                             case_tac "tcb_timeout_handler tcb"; simp)
                                     apply (wpsimp simp: tcb_at_def)
                                    apply (wpsimp simp: tcb_at_def)
                                   apply (assumption)
                                  apply clarsimp
                                  apply (subgoal_tac "invs' s \<and> tcb_at' recvr s \<and> obj_at' (\<lambda>sc'. sc_badge sc = scBadge sc') (the scopt') s")
                                   apply (clarsimp simp: obj_at'_def)
                                  apply (assumption)
                                 apply (clarsimp simp: obj_at'_def)
                                apply wpsimp
                               apply wpsimp

                              apply (clarsimp simp: invs_def valid_state_def valid_pspace_def active_sc_at_equiv
                                             split: if_split)
                             apply (clarsimp simp: invs_def valid_state_def valid_pspace_def invs'_def
                                                   valid_state'_def valid_pspace'_def
                                            split: if_split)
                             apply (frule (1) valid_objs_ko_at, clarsimp simp: valid_obj_def)
                             apply (clarsimp simp: obj_at_def)
                             apply (frule (1) pspace_relation_absD[OF _ state_relation_pspace_relation])
                             apply (clarsimp simp: other_obj_relation_def obj_at'_def projectKOs sc_relation_def)
                            apply (clarsimp simp: invs_def valid_state_def valid_pspace_def invs'_def valid_state'_def valid_pspace'_def)
                            apply (frule (1) valid_objs_ko_at, clarsimp simp: valid_obj_def)
                            apply (prop_tac "sc_relation sc n ko")
                             apply (clarsimp simp: obj_at_def)
                             apply (frule (1) pspace_relation_absD[OF _ state_relation_pspace_relation])
                             apply (clarsimp simp: other_obj_relation_def obj_at'_def projectKOs )
                            apply (frule (1) sc_ko_at_valid_objs_valid_sc', clarsimp)
                            apply (subgoal_tac "0 < scRefillMax ko")
                             apply (subgoal_tac "sc_valid_refills sc")
                              apply (prop_tac "koa=ko", erule (1) ko_at'_inj, simp only:)
                              apply (subgoal_tac "sc_valid_refills' ko")
                               apply (simp add: sc_refill_ready_relation sc_refill_sufficient_relation state_relation_def active_sc_at_equiv)
                              apply (metis valid_sched_context'_def sc_valid_refills_scRefillCount)
                             apply (subst (asm) active_sc_at_equiv)
                             apply (frule (1) active_sc_valid_refillsE)
                             apply (clarsimp simp: valid_refills_def2 obj_at_def)
                            apply (clarsimp simp: obj_at_def vs_all_heap_simps active_sc_def
                                                  sc_relation_def)
                           apply wpsimp
                          apply (wpsimp simp: refillSufficient_def getRefills_def obj_at'_def)
                         apply (wpsimp simp: refillReady_wp)
                        apply (simp add: refillReady_def, rule no_ofail_gets_the)
                        apply wpsimp
                       apply wpsimp
                      apply (clarsimp simp: obj_at_def sc_at_pred_n_def get_sched_context_exs_valid)
                     apply (rule get_sched_context_exs_valid)
                     apply (clarsimp simp: sc_at_pred_n_def obj_at_def)
                    apply (wpsimp wp: get_sched_context_no_fail)
                    apply (clarsimp simp: sc_at_pred_n_def obj_at_def is_sc_obj)
                    apply (frule_tac sc=sc and n=n in valid_objs_valid_sched_context_size[OF invs_valid_objs], fastforce, simp)
                   apply simp
                  apply clarsimp
                 apply (wpsimp wp: thread_get_wp')
                apply (wpsimp wp: threadGet_wp)
               apply (wpsimp wp: gts_wp)
              apply (wpsimp wp: gts_wp')
             apply (rule_tac Q="\<lambda>_. tcb_at recvr and valid_sched_action and invs and valid_list
                                    and valid_release_q and scheduler_act_not recvr
                                    and active_sc_valid_refills
                                    and active_if_bound_sc_tcb_at recvr
                                    and not_queued recvr"
                    in hoare_strengthen_post[rotated])
              apply (clarsimp simp: obj_at_def is_tcb)
              apply (subgoal_tac "pred_map (\<lambda>a. a = Some y) (tcb_scps_of s) recvr")
               apply (subgoal_tac "pred_map (\<lambda>a. a = Some recvr) (sc_tcbs_of s) y")
                apply (intro conjI)
                    apply (clarsimp simp: vs_all_heap_simps sc_at_kh_simps)
                   apply (clarsimp simp: vs_all_heap_simps)
                  apply (erule active_sc_valid_refillsE[rotated], clarsimp simp: vs_all_heap_simps)
                 apply (clarsimp simp: vs_all_heap_simps sc_at_kh_simps)
                apply (clarsimp simp: vs_all_heap_simps pred_tcb_at_def obj_at_def runnable_eq)
               apply (simp add: sc_at_kh_simps pred_map_eq_normalise heap_refs_inv_def2)
               apply (erule heap_refs_retractD[rotated], clarsimp)
              apply (clarsimp simp: vs_all_heap_simps)
             apply (wpsimp wp: set_thread_state_valid_sched_action set_thread_state_valid_release_q
                               sts_invs_minor2)
                 apply (rule_tac Q="\<lambda>_ s.
                           st_tcb_at inactive recvr s \<and>
                           invs s \<and> valid_list s \<and> scheduler_act_not recvr s \<and>
                           ex_nonz_cap_to recvr s \<and>
                           recvr \<noteq> idle_thread s \<and>
                           fault_tcb_at ((=) None) recvr s \<and>
                           valid_release_q s \<and>
                           active_sc_valid_refills s \<and>
                           heap_refs_inv (sc_tcbs_of s) (tcb_scps_of s) \<and>
                           (pred_map_eq None (tcb_scps_of s) recvr \<or> active_sc_tcb_at recvr s) \<and>
                           not_queued recvr s \<and> not_in_release_q recvr s"
                        in hoare_strengthen_post[rotated])
                  apply (clarsimp split: if_split simp: pred_tcb_at_def obj_at_def)
                 apply (wpsimp wp: thread_set_no_change_tcb_state thread_set_cap_to
                                   thread_set_no_change_tcb_state
                                   thread_set_pred_tcb_at_sets_true simp: ran_tcb_cap_cases)
                apply simp
                apply (wpsimp wp: hoare_drop_imp)
               apply wpsimp
              apply wpsimp
             apply wpsimp
            apply (rule_tac Q="\<lambda>_. tcb_at' recvr and invs'" in hoare_strengthen_post[rotated])
             apply (clarsimp simp: tcb_at'_ex_eq_all invs'_def valid_state'_def valid_pspace'_def)
             apply (frule (1) tcb_ko_at_valid_objs_valid_tcb', clarsimp simp: valid_tcb'_def)
            apply (wpsimp wp: sts_invs')
             apply (rule_tac Q="\<lambda>_. invs' and ex_nonz_cap_to' recvr and tcb_at' recvr
                                    and (st_tcb_at' (\<lambda>st. st = Inactive) recvr)"
                    in hoare_strengthen_post[rotated])
              apply (clarsimp simp: pred_tcb_at'_def obj_at'_def projectKOs)
              apply (fastforce dest: global'_no_ex_cap simp: invs'_def valid_state'_def split: if_split)
             apply wpsimp
            apply (wpsimp wp: sts_invs')
                apply (rule_tac Q="\<lambda>_. invs' and sch_act_not recvr and ex_nonz_cap_to' recvr and tcb_at' recvr
                                       and (st_tcb_at' (\<lambda>st. st = Inactive) recvr)"
                       in hoare_strengthen_post[rotated])
                 apply (clarsimp simp: pred_tcb_at'_def obj_at'_def projectKOs)
                 apply (fastforce dest: global'_no_ex_cap simp: invs'_def valid_state'_def split: if_split)
                apply (wpsimp wp: threadSet_fault_invs' threadSet_pred_tcb_no_state)
               apply wpsimp+
           apply (wpsimp wp: thread_get_wp')
          apply (wpsimp wp: threadGet_wp)
         apply (rule_tac Q="\<lambda>_. tcb_at sender and tcb_at recvr and invs and valid_list and
                   valid_sched and scheduler_act_not recvr and not_in_release_q recvr and
                   active_if_bound_sc_tcb_at recvr and st_tcb_at inactive recvr and
                   ex_nonz_cap_to recvr and not_queued recvr"
                in hoare_strengthen_post[rotated])
          apply (clarsimp simp: valid_sched_def invs_def valid_state_def valid_pspace_def
                                pred_tcb_at_def obj_at_def
                         dest!: idle_no_ex_cap)
         apply (wpsimp wp: reply_remove_valid_sched reply_remove_active_if_bound_sc_tcb_at reply_remove_invs)
        apply (rule_tac Q="\<lambda>_. tcb_at' sender and invs' and sch_act_not recvr and ex_nonz_cap_to' recvr and tcb_at' recvr
                               and st_tcb_at' (\<lambda>a. a = Structures_H.thread_state.Inactive) recvr"
               in hoare_strengthen_post[rotated])
         apply (clarsimp simp: obj_at'_def invs'_def valid_state'_def valid_pspace'_def)
        apply (wpsimp simp: valid_pspace'_def wp: replyRemove_invs')
       apply (clarsimp simp: invs_def valid_state_def valid_pspace_def valid_sched_def cong: conj_cong)
       apply (rename_tac recvr ts_reply s s')
       apply (subgoal_tac "ts_reply = reply", simp)
        apply (rule conjI, fastforce)
        apply (rule context_conjI)
         apply (clarsimp simp: tcb_at_kh_simps pred_map_def)
        apply (subgoal_tac "\<not> pred_map runnable (tcb_sts_of s) recvr")
         apply (intro conjI)
             apply (rule weak_valid_sched_action_contrap; simp add: valid_sched_action_def)
            apply (rule valid_release_q_not_in_release_q_not_runnable; clarsimp simp: tcb_at_kh_simps pred_map_def)
           apply (erule (1) released_ipc_queuesE1)
          apply (erule (1) st_tcb_ex_cap, clarsimp)
         apply (erule valid_ready_qs_not_queued_not_runnable, clarsimp)
         apply (clarsimp simp: tcb_at_kh_simps pred_map_def)
        apply (clarsimp simp: tcb_at_kh_simps pred_map_def)
       apply (erule (2) reply_tcb_sym_refsD)
      apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def cong: conj_cong)
      apply (intro conjI)
         apply (erule cross_relF[OF _ tcb_at'_cross_rel[where t=sender]], fastforce)
        apply (erule (1) st_tcb_ex_cap'', simp)
       apply (clarsimp simp: pred_tcb_at'_def obj_at'_def)
      apply (wpsimp wp: get_simple_ko_wp)+
   apply (clarsimp split: option.split simp: invs_def valid_state_def valid_pspace_def)
   apply (frule (1) valid_objs_ko_at)
   apply (clarsimp simp: valid_obj_def valid_reply_def obj_at_def reply_tcb_reply_at_def)
  apply (clarsimp split: option.split
                   simp: invs_def valid_state_def valid_pspace_def invs'_def valid_state'_def
                         valid_pspace'_def)
  apply (frule cross_relF[OF _ reply_at'_cross_rel[where t=reply]]; clarsimp)
  apply (frule (1) reply_ko_at_valid_objs_valid_reply')
  apply (clarsimp simp: valid_reply'_def)
  done

end

end
