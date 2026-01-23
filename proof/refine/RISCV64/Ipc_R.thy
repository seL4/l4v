(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Ipc_R
imports Finalise_R
begin

context begin interpretation Arch . (*FIXME: arch-split*)

lemmas lookup_slot_wrapper_defs'[simp] =
   lookupSourceSlot_def lookupTargetSlot_def lookupPivotSlot_def

lemma getMessageInfo_corres: "corres ((=) \<circ> message_info_map)
                      (tcb_at t and pspace_aligned and pspace_distinct) \<top>
                      (get_message_info t) (getMessageInfo t)"
  apply (rule corres_guard_imp)
    apply (unfold get_message_info_def getMessageInfo_def fun_app_def)
    apply (simp add: RISCV64_H.msgInfoRegister_def
             RISCV64.msgInfoRegister_def RISCV64_A.msg_info_register_def)
    apply (rule corres_split_eqr[OF asUser_getRegister_corres])
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
  apply (wpsimp wp: hoare_drop_imps throwE_R)
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
lemma valid_ipc_buffer_ptr_aligned_word_size_bits:
  "\<lbrakk>valid_ipc_buffer_ptr' a s;  is_aligned y word_size_bits \<rbrakk> \<Longrightarrow> is_aligned (a + y) word_size_bits"
  unfolding valid_ipc_buffer_ptr'_def
  apply clarsimp
  apply (erule (1) aligned_add_aligned)
  apply (simp add: msg_align_bits word_size_bits_def)
  done

(* MOVE *)
lemma valid_ipc_buffer_ptr'D2:
  "\<lbrakk>valid_ipc_buffer_ptr' a s; y < max_ipc_words * word_size; is_aligned y word_size_bits\<rbrakk> \<Longrightarrow> typ_at' UserDataT (a + y && ~~ mask pageBits) s"
  unfolding valid_ipc_buffer_ptr'_def
  apply clarsimp
  apply (subgoal_tac "(a + y) && ~~ mask pageBits = a  && ~~ mask pageBits")
   apply simp
  apply (rule mask_out_first_mask_some [where n = msg_align_bits])
   apply (erule is_aligned_add_helper [THEN conjunct2])
   apply (erule order_less_le_trans)
   apply (simp add: msg_align_bits max_ipc_words word_size_def)
  apply simp
  done

lemma loadCapTransfer_corres:
  notes msg_max_words_simps = max_ipc_words_def msgMaxLength_def msgMaxExtraCaps_def msgLengthBits_def
                              capTransferDataSize_def msgExtraCapBits_def
  shows
  "corres ct_relation \<top> (valid_ipc_buffer_ptr' buffer) (load_cap_transfer buffer) (loadCapTransfer buffer)"
  apply (simp add: load_cap_transfer_def loadCapTransfer_def
                   captransfer_from_words_def
                   capTransferDataSize_def capTransferFromWords_def
                   msgExtraCapBits_def word_size add.commute add.left_commute
                   msg_max_length_def msg_max_extra_caps_def word_size_def
                   msgMaxLength_def msgMaxExtraCaps_def msgLengthBits_def wordSize_def wordBits_def
              del: upt.simps)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF load_word_corres])
      apply (rule corres_split[OF load_word_corres])
        apply (rule corres_split[OF load_word_corres])
          apply (rule_tac P=\<top> and P'=\<top> in corres_inst)
          apply (clarsimp simp: ct_relation_def)
         apply (wp no_irq_loadWord)+
   apply simp
  apply (simp add: conj_comms)
  apply safe
       apply (erule valid_ipc_buffer_ptr_aligned_word_size_bits, simp add: is_aligned_def word_size_bits_def)+
    apply (erule valid_ipc_buffer_ptr'D2,
              simp add: msg_max_words_simps word_size_def word_size_bits_def,
              simp add: word_size_bits_def is_aligned_def)+
  done

lemma getReceiveSlots_corres:
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
    apply (rule corres_split[OF loadCapTransfer_corres])
      apply (rule corres_empty_on_failure)
      apply (rule corres_splitEE)
         apply (rule corres_unify_failure)
          apply (rule lookup_cap_corres)
          apply (simp add: ct_relation_def)
         apply simp
        apply (rule corres_splitEE)
           apply (rule corres_unify_failure)
            apply (simp add: ct_relation_def)
            apply (erule lookupSlotForCNodeOp_corres [OF _ refl])
           apply simp
          apply (simp add: split_def liftE_bindE unlessE_whenE)
          apply (rule corres_split[OF get_cap_corres])
            apply (rule corres_split_norE)
               apply (rule corres_whenE)
                 apply (case_tac cap, auto)[1]
                apply (rule corres_trivial, simp)
               apply simp
              apply (rule corres_trivial, simp add: returnOk_def)
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
declare word64_minus_one_le [simp]

lemma loadWordUser_corres':
  "\<lbrakk> y < unat max_ipc_words; y' = of_nat y * 8 \<rbrakk> \<Longrightarrow>
  corres (=) \<top> (valid_ipc_buffer_ptr' a) (load_word_offs a y) (loadWordUser (a + y'))"
  apply simp
  apply (erule loadWordUser_corres)
  done

declare loadWordUser_inv [wp]

lemma getExtraCptrs_inv[wp]:
  "\<lbrace>P\<rbrace> getExtraCPtrs buf mi \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (cases mi, cases buf, simp_all add: getExtraCPtrs_def)
  apply (wp dmo_inv' mapM_wp' loadWord_inv)
  done

lemma getSlotCap_cte_wp_at_rv:
  "\<lbrace>cte_wp_at' (\<lambda>cte. P (cteCap cte) cte) p\<rbrace>
     getSlotCap p
   \<lbrace>\<lambda>rv. cte_wp_at' (P rv) p\<rbrace>"
  apply (simp add: getSlotCap_def)
  apply (wp getCTE_ctes_wp)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  done

lemma badge_derived_mask [simp]:
  "badge_derived' (maskCapRights R c) c' = badge_derived' c c'"
  by (simp add: badge_derived'_def)

declare derived'_not_Null [simp]

lemma maskCapRights_vs_cap_ref'[simp]:
  "vs_cap_ref' (maskCapRights msk cap) = vs_cap_ref' cap"
  unfolding vs_cap_ref'_def
  apply (cases cap, simp_all add: maskCapRights_def isCap_simps Let_def)
  apply (rename_tac arch_capability)
  apply (case_tac arch_capability;
         simp add: maskCapRights_def RISCV64_H.maskCapRights_def isCap_simps Let_def)
  done

lemma corres_set_extra_badge:
  "b' = b \<Longrightarrow>
  corres dc (in_user_frame buffer)
         (valid_ipc_buffer_ptr' buffer and
          (\<lambda>_. msg_max_length + 2 + n < unat max_ipc_words))
         (set_extra_badge buffer b n) (setExtraBadge buffer b' n)"
  apply (rule corres_gen_asm2)
  apply (drule storeWordUser_corres [where a=buffer and w=b])
  apply (simp add: set_extra_badge_def setExtraBadge_def buffer_cptr_index_def
                   bufferCPtrOffset_def Let_def)
  apply (simp add: word_size word_size_def wordSize_def wordBits_def
                   bufferCPtrOffset_def buffer_cptr_index_def msgMaxLength_def
                   msg_max_length_def msgLengthBits_def store_word_offs_def
                   add.commute add.left_commute)
  done

crunch setExtraBadge
  for typ_at': "\<lambda>s. P (typ_at' T p s)"
lemmas setExtraBadge_typ_ats' [wp] = typ_at_lifts [OF setExtraBadge_typ_at']
crunch setExtraBadge
  for valid_pspace'[wp]: valid_pspace'
crunch setExtraBadge
  for cte_wp_at'[wp]: "cte_wp_at' P p"
crunch setExtraBadge
  for ipc_buffer'[wp]: "valid_ipc_buffer_ptr' buffer"

crunch getExtraCPtr
  for inv'[wp]: P (wp: dmo_inv' loadWord_inv)

lemmas unifyFailure_discard2
    = corres_injection[OF id_injection unifyFailure_injection, simplified]

lemma deriveCap_not_null:
  "\<lbrace>\<top>\<rbrace> deriveCap slot cap \<lbrace>\<lambda>rv. K (rv \<noteq> NullCap \<longrightarrow> cap \<noteq> NullCap)\<rbrace>,-"
  apply (simp add: deriveCap_def split del: if_split)
  by (case_tac cap; wpsimp simp: isCap_simps)

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
  apply (wp updateMDB_weak_cte_wp_at updateCap_cte_wp_at_cases getCTE_wp hoare_weak_lift_imp
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
    apply (simp add:p_assoc_help mask_def)
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
  by (wp updateMDB_weak_cte_wp_at updateCap_cte_wp_at_cases getCTE_wp' hoare_weak_lift_imp
         | clarsimp simp: comp_def cteInsert_def
         | unfold setUntypedCapAsFull_def
         | auto simp: cte_wp_at'_def dest!: imp)+

lemma maskedAsFull_null_cap[simp]:
  "(maskedAsFull x y = capability.NullCap) = (x = capability.NullCap)"
  "(capability.NullCap  = maskedAsFull x y) = (x = capability.NullCap)"
  by (case_tac x, auto simp:maskedAsFull_def isCap_simps)

lemma maskCapRights_eq_null:
  "(RetypeDecls_H.maskCapRights r xa = capability.NullCap) =
   (xa = capability.NullCap)"
  apply (cases xa; simp add: maskCapRights_def isCap_simps)
  apply (rename_tac arch_capability)
  apply (case_tac arch_capability)
      apply (simp_all add: RISCV64_H.maskCapRights_def isCap_simps)
  done

lemma cte_refs'_maskedAsFull[simp]:
  "cte_refs' (maskedAsFull a b) = cte_refs' a"
  apply (rule ext)+
  apply (case_tac a)
   apply (clarsimp simp:maskedAsFull_def isCap_simps)+
 done

lemma set_extra_badge_valid_arch_state[wp]:
  "set_extra_badge buffer badge n \<lbrace> valid_arch_state \<rbrace>"
  unfolding set_extra_badge_def
  by wp

lemma transferCapsToSlots_corres:
  "\<lbrakk> list_all2 (\<lambda>(cap, slot) (cap', slot'). cap_relation cap cap'
             \<and> slot' = cte_map slot) caps caps';
      mi' = message_info_map mi \<rbrakk> \<Longrightarrow>
   corres ((=) \<circ> message_info_map)
      (\<lambda>s. valid_objs s \<and> pspace_aligned s \<and> pspace_distinct s \<and> valid_mdb s
         \<and> valid_list s \<and> valid_arch_state s
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
      apply (rule corres_if2)
        apply (case_tac "fst x", auto simp add: isCap_simps)[1]
       apply (rule corres_split[OF corres_set_extra_badge])
          apply (clarsimp simp: is_cap_simps)
         apply (drule conjunct1)
         apply simp
         apply (rule corres_rel_imp, rule Cons.hyps, simp_all)[1]
         apply (case_tac mi, simp)
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
         apply (rule unifyFailure_discard2)
          apply (case_tac mi, clarsimp)
         apply (rule deriveCap_corres)
          apply (simp add: remove_rights_def)
         apply clarsimp
        apply (rule corres_split_norE)
           apply (rule corres_whenE)
             apply (case_tac cap', auto)[1]
            apply (rule corres_trivial, simp)
            apply (case_tac mi, simp)
           apply simp
          apply (simp add: liftE_bindE)
          apply (rule corres_split_nor)
             apply (rule cteInsert_corres, simp_all add: hd_map)[1]
            apply (simp add: tl_map)
            apply (rule corres_rel_imp, rule Cons.hyps, simp_all)[1]
           apply (wp valid_case_option_post_wp hoare_vcg_const_Ball_lift
                     hoare_vcg_const_Ball_lift cap_insert_derived_valid_arch_state
                     cap_insert_weak_cte_wp_at)
            apply (wp hoare_vcg_const_Ball_lift | simp add:split_def del: imp_disj1)+
            apply (wp cap_insert_cte_wp_at)
           apply (wp valid_case_option_post_wp hoare_vcg_const_Ball_lift
                     cteInsert_valid_pspace
                     | simp add: split_def)+
           apply (wp cteInsert_weak_cte_wp_at hoare_valid_ipc_buffer_ptr_typ_at')+
          apply (wpsimp wp: hoare_vcg_const_Ball_lift cteInsert_cte_wp_at  valid_case_option_post_wp
                      simp: split_def)
         apply (unfold whenE_def)
         apply wp+
       apply (clarsimp simp: conj_comms ball_conj_distrib split del: if_split)
       apply (rule_tac Q' ="\<lambda>cap' s. (cap'\<noteq> cap.NullCap \<longrightarrow>
         cte_wp_at (is_derived (cdt s) (a, b) cap') (a, b) s
         \<and> QM s cap')" for QM
         in hoare_strengthen_postE_R)
        prefer 2
        apply clarsimp
        apply assumption
       apply (subst imp_conjR)
       apply (rule hoare_vcg_conj_liftE_R')
        apply (rule derive_cap_is_derived)
       apply (wp derive_cap_is_derived_foo)+
      apply (simp split del: if_split)
      apply (rule_tac Q' ="\<lambda>cap' s. (cap'\<noteq> capability.NullCap \<longrightarrow>
         cte_wp_at' (\<lambda>c. is_derived' (ctes_of s) (cte_map (a, b)) cap' (cteCap c)) (cte_map (a, b)) s
         \<and> QM s cap')" for QM
        in hoare_strengthen_postE_R)
       prefer 2
       apply clarsimp
       apply assumption
      apply (subst imp_conjR)
      apply (rule hoare_vcg_conj_liftE_R')
       apply (rule hoare_strengthen_postE_R[OF deriveCap_derived])
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
      setUntypedCapAsFull_cte_wp_at getCTE_wp hoare_weak_lift_imp)
   apply (clarsimp simp:cte_wp_at_ctes_of)
   apply (rule_tac x = "cref" in exI)
     apply (rule conjI)
     apply clarsimp+
  done

declare maskCapRights_eq_null[simp]

crunch setExtraBadge
  for ex_cte_cap_wp_to'[wp]: "ex_cte_cap_wp_to' P p"
  (rule: ex_cte_cap_to'_pres)

crunch setExtraBadge
  for valid_objs'[wp]: valid_objs'
crunch setExtraBadge
  for aligned'[wp]: pspace_aligned'
crunch setExtraBadge
  for distinct'[wp]: pspace_distinct'

lemma cteInsert_assume_Null:
  "\<lbrace>P\<rbrace> cteInsert cap src dest \<lbrace>Q\<rbrace> \<Longrightarrow>
   \<lbrace>\<lambda>s. cte_wp_at' (\<lambda>cte. cteCap cte = NullCap) dest s \<longrightarrow> P s\<rbrace>
   cteInsert cap src dest
   \<lbrace>Q\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (erule impCE)
   apply (simp add: cteInsert_def)
   apply (rule bind_wp[OF _ stateAssert_sp])
   apply (rule bind_wp[OF _ getCTE_sp])+
   apply (rule hoare_name_pre_state)
   apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (erule hoare_weaken_pre)
  apply simp
  done

crunch setExtraBadge
  for mdb'[wp]: valid_mdb'

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
      setUntypedCapAsFull_cte_wp_at getCTE_wp hoare_weak_lift_imp)
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
     apply (wp x hoare_vcg_const_Ball_lift cteInsert_cte_cap_to' hoare_weak_lift_imp)
       apply (rule cteInsert_weak_cte_wp_at2,clarsimp)
      apply (wp hoare_vcg_const_Ball_lift hoare_weak_lift_imp)+
       apply (rule cteInsert_weak_cte_wp_at2,clarsimp)
      apply (wp hoare_vcg_const_Ball_lift cteInsert_cte_wp_at hoare_weak_lift_imp
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

crunch transferCapsToSlots
  for pspace_aligned'[wp]: pspace_aligned'
crunch transferCapsToSlots
  for pspace_canonical'[wp]: pspace_canonical'
crunch transferCapsToSlots
  for pspace_in_kernel_mappings'[wp]: pspace_in_kernel_mappings'
crunch transferCapsToSlots
  for pspace_distinct'[wp]: pspace_distinct'

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
  apply (wpsimp wp: transferCapsToSlots_presM[where drv=True and vo=True and emx=True and pad=True])
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

crunch setExtraBadge
  for no_0'[wp]: no_0_obj'

lemma transferCapsToSlots_no_0_obj' [wp]:
  "\<lbrace>no_0_obj'\<rbrace> transferCapsToSlots ep buffer n caps slots mi \<lbrace>\<lambda>rv. no_0_obj'\<rbrace>"
  by (wp transferCapsToSlots_pres1)

lemma transferCapsToSlots_vp[wp]:
  "\<lbrace>\<lambda>s. valid_pspace' s \<and> distinct slots
          \<and> length slots \<le> 1
          \<and> (\<forall>x \<in> set slots. ex_cte_cap_to' x s \<and> cte_wp_at' (\<lambda>cte. cteCap cte = capability.NullCap) x s)
          \<and> (\<forall>x \<in> set slots. real_cte_at' x s)
          \<and> transferCaps_srcs caps s\<rbrace>
    transferCapsToSlots ep buffer n caps slots mi
   \<lbrace>\<lambda>rv. valid_pspace'\<rbrace>"
  apply (rule hoare_pre)
   apply (simp add: valid_pspace'_def | wp)+
  apply (fastforce simp: cte_wp_at_ctes_of dest: ctes_of_valid')
  done

crunch setExtraBadge, doIPCTransfer
  for sch_act [wp]: "\<lambda>s. P (ksSchedulerAction s)"
  (wp: crunch_wps mapME_wp' simp: zipWithM_x_mapM)
crunch setExtraBadge
  for pred_tcb_at' [wp]: "\<lambda>s. pred_tcb_at' proj P p s"
  and ksCurThread[wp]: "\<lambda>s. P (ksCurThread s)"
  and ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  and obj_at' [wp]: "\<lambda>s. P' (obj_at' P p s)"
  and queues [wp]: "\<lambda>s. P (ksReadyQueues s)"
  and queuesL1 [wp]: "\<lambda>s. P (ksReadyQueuesL1Bitmap s)"
  and queuesL2 [wp]: "\<lambda>s. P (ksReadyQueuesL2Bitmap s)"
  (simp: storeWordUser_def)


lemma tcts_sch_act[wp]:
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>
     transferCapsToSlots ep buffer n caps slots mi
   \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  by (wp sch_act_wf_lift tcb_in_cur_domain'_lift transferCapsToSlots_pres1)

crunch setExtraBadge
  for state_refs_of'[wp]: "\<lambda>s. P (state_refs_of' s)"

lemma tcts_state_refs_of'[wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of' s)\<rbrace>
     transferCapsToSlots ep buffer n caps slots mi
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  by (wp transferCapsToSlots_pres1)

crunch setExtraBadge
  for if_live'[wp]: if_live_then_nonz_cap'

lemma tcts_iflive[wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s \<and> distinct slots \<and>
         (\<forall>x\<in>set slots.
             ex_cte_cap_to' x s \<and> cte_wp_at' (\<lambda>cte. cteCap cte = capability.NullCap) x s)\<rbrace>
  transferCapsToSlots ep buffer n caps slots mi
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  by (wp transferCapsToSlots_pres2 | simp)+

crunch setExtraBadge
  for if_unsafe'[wp]: if_unsafe_then_cap'

lemma tcts_ifunsafe[wp]:
  "\<lbrace>\<lambda>s. if_unsafe_then_cap' s \<and> distinct slots \<and>
         (\<forall>x\<in>set slots.  cte_wp_at' (\<lambda>cte. cteCap cte = capability.NullCap) x s \<and>
             ex_cte_cap_to' x s)\<rbrace> transferCapsToSlots ep buffer n caps slots mi
   \<lbrace>\<lambda>rv. if_unsafe_then_cap'\<rbrace>"
  by (wp transferCapsToSlots_pres2 | simp)+

crunch ensureNoChildren
  for it[wp]: "\<lambda>s. P (ksIdleThread s)"

crunch deriveCap
  for idle'[wp]: "valid_idle'"

crunch setExtraBadge
  for valid_idle'[wp]: valid_idle'

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

crunch setExtraBadge
  for valid_arch_state'[wp]: valid_arch_state'

lemma transferCapsToSlots_valid_arch [wp]:
  "\<lbrace>valid_arch_state'\<rbrace> transferCapsToSlots ep buffer n caps slots mi \<lbrace>\<lambda>rv. valid_arch_state'\<rbrace>"
  by (rule transferCapsToSlots_pres1; wp)

crunch setExtraBadge
  for valid_global_refs'[wp]: valid_global_refs'

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

crunch setExtraBadge
  for irq_node'[wp]: "\<lambda>s. P (irq_node' s)"

lemma transferCapsToSlots_irq_node'[wp]:
  "\<lbrace>\<lambda>s. P (irq_node' s)\<rbrace> transferCapsToSlots ep buffer n caps slots mi \<lbrace>\<lambda>rv s. P (irq_node' s)\<rbrace>"
   by (wp transferCapsToSlots_pres1)

lemma valid_irq_handlers_ctes_ofD:
  "\<lbrakk> ctes_of s p = Some cte; cteCap cte = IRQHandlerCap irq; valid_irq_handlers' s \<rbrakk>
       \<Longrightarrow> irq_issued' irq s"
  by (auto simp: valid_irq_handlers'_def cteCaps_of_def ran_def)

crunch setExtraBadge
  for valid_irq_handlers'[wp]: valid_irq_handlers'

lemma transferCapsToSlots_irq_handlers[wp]:
  "\<lbrace>valid_irq_handlers' and valid_objs' and valid_mdb' and pspace_distinct' and pspace_aligned'
         and K(distinct slots \<and> length slots \<le> 1)
         and (\<lambda>s. \<forall>x \<in> set slots. real_cte_at' x s \<and> cte_wp_at' (\<lambda>cte. cteCap cte = capability.NullCap) x s)
         and transferCaps_srcs caps\<rbrace>
     transferCapsToSlots ep buffer n caps slots mi
  \<lbrace>\<lambda>rv. valid_irq_handlers'\<rbrace>"
  apply (wpsimp wp: transferCapsToSlots_presM[where vo=True and emx=False and drv=True and pad=False])
     apply (clarsimp simp: is_derived'_def cte_wp_at_ctes_of badge_derived'_def)
     apply (erule(2) valid_irq_handlers_ctes_ofD)
    apply wp
  apply (clarsimp simp:cte_wp_at_ctes_of | intro ballI conjI)+
  apply (drule(1) bspec,clarsimp)
  apply (case_tac cte,clarsimp)
  apply (frule(1) CSpace_I.ctes_of_valid_cap')
  apply (fastforce simp:valid_cap'_def)
  done

crunch setExtraBadge
  for irq_state'[wp]: "\<lambda>s. P (ksInterruptState s)"

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

lemma transferCapsToSlots_irqs_masked'[wp]:
  "\<lbrace>irqs_masked'\<rbrace> transferCapsToSlots ep buffer n caps slots mi \<lbrace>\<lambda>rv. irqs_masked'\<rbrace>"
  by (wp transferCapsToSlots_pres1 irqs_masked_lift)

lemma storeWordUser_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> storeWordUser a w \<lbrace>\<lambda>_. valid_machine_state'\<rbrace>"
proof -
  have aligned_offset_ignore:
    "\<And>(l::machine_word) (p::machine_word) sz. l<8 \<Longrightarrow> p && mask 3 = 0 \<Longrightarrow>
       p+l && ~~ mask pageBits = p && ~~ mask pageBits"
  proof -
    fix l p sz
    assume al: "(p::machine_word) && mask 3 = 0"
    assume "(l::machine_word) < 8" hence less: "l<2^3" by simp
    have le: "3 \<le> pageBits" by (simp add: pageBits_def)
    show "?thesis l p sz"
      by (rule is_aligned_add_helper[simplified is_aligned_mask,
          THEN conjunct2, THEN mask_out_first_mask_some,
          where n=3, OF al less le])
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
    apply (simp only: is_aligned_mask[of _ 3])
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

crunch setExtraBadge, transferCapsToSlots
  for pspace_domain_valid[wp]: "pspace_domain_valid"

crunch setExtraBadge
  for ct_not_inQ[wp]: "ct_not_inQ"

lemma tcts_ct_not_inQ[wp]:
  "\<lbrace>ct_not_inQ\<rbrace>
   transferCapsToSlots ep buffer n caps slots mi
   \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  by (wp transferCapsToSlots_pres1)

crunch setExtraBadge
  for gsUntypedZeroRanges[wp]: "\<lambda>s. P (gsUntypedZeroRanges s)"
crunch setExtraBadge
  for ctes_of[wp]: "\<lambda>s. P (ctes_of s)"

lemma tcts_zero_ranges[wp]:
  "\<lbrace>\<lambda>s. untyped_ranges_zero' s \<and> valid_pspace' s \<and> distinct slots
          \<and> (\<forall>x \<in> set slots. ex_cte_cap_to' x s \<and> cte_wp_at' (\<lambda>cte. cteCap cte = capability.NullCap) x s)
          \<and> (\<forall>x \<in> set slots. real_cte_at' x s)
          \<and> length slots \<le> 1
          \<and> transferCaps_srcs caps s\<rbrace>
    transferCapsToSlots ep buffer n caps slots mi
  \<lbrace>\<lambda>rv. untyped_ranges_zero'\<rbrace>"
  apply (wpsimp wp: transferCapsToSlots_presM[where emx=True and vo=True
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

crunch setExtraBadge
  for ct_idle_or_in_cur_domain'[wp]: ct_idle_or_in_cur_domain'
crunch transferCapsToSlots
  for ct_idle_or_in_cur_domain'[wp]: ct_idle_or_in_cur_domain'
crunch transferCapsToSlots
  for ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
crunch setExtraBadge
  for ksDomSchedule[wp]: "\<lambda>s. P (ksDomSchedule s)"
crunch setExtraBadge
  for ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"
crunch transferCapsToSlots
  for ksDomSchedule[wp]: "\<lambda>s. P (ksDomSchedule s)"
crunch transferCapsToSlots
  for ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"

crunch transferCapsToSlots
  for sym_heap_sched_pointers[wp]: sym_heap_sched_pointers
  and valid_sched_pointers[wp]: valid_sched_pointers
  and valid_bitmaps[wp]: valid_bitmaps
  (rule: sym_heap_sched_pointers_lift)

lemma transferCapsToSlots_invs[wp]:
  "\<lbrace>\<lambda>s. invs' s \<and> distinct slots
          \<and> (\<forall>x \<in> set slots. cte_wp_at' (\<lambda>cte. cteCap cte = NullCap) x s)
          \<and> (\<forall>x \<in> set slots. ex_cte_cap_to' x s)
          \<and> (\<forall>x \<in> set slots. real_cte_at' x s)
          \<and> length slots \<le> 1
          \<and> transferCaps_srcs caps s\<rbrace>
    transferCapsToSlots ep buffer n caps slots mi
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def)
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

lemma transferCaps_corres:
  "\<lbrakk> info' = message_info_map info;
    list_all2 (\<lambda>x y. cap_relation (fst x) (fst y) \<and> snd y = cte_map (snd x))
         caps caps' \<rbrakk>
  \<Longrightarrow>
   corres ((=) \<circ> message_info_map)
   (tcb_at receiver and valid_objs and
    pspace_aligned and pspace_distinct and valid_mdb
    and valid_list and valid_arch_state
    and (\<lambda>s. case ep of Some x \<Rightarrow> ep_at x s | _ \<Rightarrow> True)
    and case_option \<top> in_user_frame recv_buf
    and (\<lambda>s. valid_message_info info)
    and transfer_caps_srcs caps)
   (tcb_at' receiver and valid_objs' and
    pspace_aligned' and pspace_distinct' and pspace_canonical' and pspace_in_kernel_mappings'
    and no_0_obj' and valid_mdb'
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
    apply (rule corres_split[OF getReceiveSlots_corres])
      apply (rule_tac x=recv_buf in option_corres)
       apply (rule_tac P=\<top> and P'=\<top> in corres_inst)
       apply (case_tac info, simp)
      apply simp
      apply (rule corres_rel_imp, rule transferCapsToSlots_corres,
             simp_all add: split_def)[1]
      apply (case_tac info, simp)
     apply (wp hoare_vcg_all_lift get_rs_cte_at hoare_weak_lift_imp
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

crunch transferCaps
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"

lemmas transferCaps_typ_ats[wp] = typ_at_lifts [OF transferCaps_typ_at']

lemma isIRQControlCap_mask [simp]:
  "isIRQControlCap (maskCapRights R c) = isIRQControlCap c"
  apply (case_tac c)
            apply (clarsimp simp: isCap_simps maskCapRights_def Let_def)+
      apply (rename_tac arch_capability)
      apply (case_tac arch_capability)
          apply (clarsimp simp: isCap_simps RISCV64_H.maskCapRights_def
                                maskCapRights_def Let_def)+
  done

lemma isFrameCap_maskCapRights[simp]:
" isArchCap isFrameCap (RetypeDecls_H.maskCapRights R c) = isArchCap isFrameCap c"
  apply (case_tac c; simp add: isCap_simps isArchCap_def maskCapRights_def)
  apply (rename_tac arch_capability)
  apply (case_tac arch_capability; simp add: isCap_simps RISCV64_H.maskCapRights_def)
  done

lemma capReplyMaster_mask[simp]:
  "isReplyCap c \<Longrightarrow> capReplyMaster (maskCapRights R c) = capReplyMaster c"
  by (clarsimp simp: isCap_simps maskCapRights_def)

lemma is_derived_mask' [simp]:
  "is_derived' m p (maskCapRights R c) = is_derived' m p c"
  apply (rule ext)
  apply (simp add: is_derived'_def badge_derived'_def)
  done

lemma updateCapData_ordering:
  "\<lbrakk> (x, capBadge cap) \<in> capBadge_ordering P; updateCapData p d cap \<noteq> NullCap \<rbrakk>
    \<Longrightarrow> (x, capBadge (updateCapData p d cap)) \<in> capBadge_ordering P"
  apply (cases cap, simp_all add: updateCapData_def isCap_simps Let_def
                                  capBadge_def RISCV64_H.updateCapData_def
                           split: if_split_asm)
   apply fastforce+
  done

lemma updateCapData_capReplyMaster:
  "isReplyCap cap \<Longrightarrow> capReplyMaster (updateCapData p d cap) = capReplyMaster cap"
  by (clarsimp simp: isCap_simps updateCapData_def split del: if_split)

lemma updateCapData_is_Reply[simp]:
  "(updateCapData p d cap = ReplyCap x y z) = (cap = ReplyCap x y z)"
  by (rule ccontr,
      clarsimp simp: isCap_simps updateCapData_def Let_def
                     RISCV64_H.updateCapData_def
          split del: if_split
              split: if_split_asm)

lemma updateCapDataIRQ:
  "updateCapData p d cap \<noteq> NullCap \<Longrightarrow>
  isIRQControlCap (updateCapData p d cap) = isIRQControlCap cap"
  apply (cases cap, simp_all add: updateCapData_def isCap_simps Let_def
                                  RISCV64_H.updateCapData_def
                           split: if_split_asm)
  done

lemma updateCapData_vs_cap_ref'[simp]:
  "vs_cap_ref' (updateCapData pr D c) = vs_cap_ref' c"
  by (rule ccontr,
      clarsimp simp: isCap_simps updateCapData_def Let_def
                     RISCV64_H.updateCapData_def
                     vs_cap_ref'_def
          split del: if_split
              split: if_split_asm)

lemma isFrameCap_updateCapData[simp]:
  "isArchCap isFrameCap (updateCapData pr D c) = isArchCap isFrameCap c"
  apply (case_tac c; simp add:updateCapData_def isCap_simps isArchCap_def)
   apply (rename_tac arch_capability)
   apply (case_tac arch_capability; simp add: RISCV64_H.updateCapData_def isCap_simps isArchCap_def)
  apply (clarsimp split:capability.splits simp:Let_def)
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


lemma copyMRs_typ_at':
  "\<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> copyMRs s sb r rb n \<lbrace>\<lambda>rv s. P (typ_at' T p s)\<rbrace>"
  by (simp add: copyMRs_def | wp mapM_wp [where S=UNIV, simplified] | wpc)+

lemmas copyMRs_typ_at_lifts[wp] = typ_at_lifts [OF copyMRs_typ_at']

lemma copy_mrs_invs'[wp]:
  "\<lbrace> invs' and tcb_at' s and tcb_at' r \<rbrace> copyMRs s sb r rb n \<lbrace>\<lambda>rv. invs' \<rbrace>"
  including classic_wp_pre
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

crunch transferCaps
  for aligned'[wp]: pspace_aligned'
  (wp: crunch_wps simp: zipWithM_x_mapM)
crunch transferCaps
  for distinct'[wp]: pspace_distinct'
  (wp: crunch_wps simp: zipWithM_x_mapM)

crunch setMRs
  for aligned'[wp]: pspace_aligned'
  (wp: crunch_wps simp: crunch_simps)
crunch setMRs
  for distinct'[wp]: pspace_distinct'
  (wp: crunch_wps simp: crunch_simps)
crunch copyMRs
  for aligned'[wp]: pspace_aligned'
  (wp: crunch_wps simp: crunch_simps)
crunch copyMRs
  for pspace_canonical'[wp]: pspace_canonical'
  (wp: crunch_wps simp: crunch_simps)
crunch copyMRs
  for pspace_in_kernel_mappings'[wp]: pspace_in_kernel_mappings'
  (wp: crunch_wps simp: crunch_simps)
crunch copyMRs
  for distinct'[wp]: pspace_distinct'
  (wp: crunch_wps simp: crunch_simps)
crunch setMessageInfo
  for aligned'[wp]: pspace_aligned'
  (wp: crunch_wps simp: crunch_simps)
crunch setMessageInfo
  for distinct'[wp]: pspace_distinct'
  (wp: crunch_wps simp: crunch_simps)

crunch storeWordUser
  for valid_objs'[wp]: valid_objs'
crunch storeWordUser
  for valid_pspace'[wp]: valid_pspace'

lemma set_mrs_valid_objs' [wp]:
  "\<lbrace>valid_objs'\<rbrace> setMRs t a msgs \<lbrace>\<lambda>rv. valid_objs'\<rbrace>"
  apply (simp add: setMRs_def zipWithM_x_mapM split_def)
  apply (wp asUser_valid_objs crunch_wps)
  done

crunch copyMRs
  for valid_objs'[wp]: valid_objs'
  (wp: crunch_wps simp: crunch_simps)

lemma setMRs_invs_bits[wp]:
  "\<lbrace>valid_pspace'\<rbrace> setMRs t buf mrs \<lbrace>\<lambda>rv. valid_pspace'\<rbrace>"
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>
     setMRs t buf mrs \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>
     setMRs t buf mrs \<lbrace>\<lambda>rv s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  "\<lbrace>\<lambda>s. P (state_refs_of' s)\<rbrace>
     setMRs t buf mrs
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  "\<lbrace>if_live_then_nonz_cap'\<rbrace> setMRs t buf mrs \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  "\<lbrace>ex_nonz_cap_to' p\<rbrace> setMRs t buf mrs \<lbrace>\<lambda>rv. ex_nonz_cap_to' p\<rbrace>"
  "\<lbrace>cur_tcb'\<rbrace> setMRs t buf mrs \<lbrace>\<lambda>rv. cur_tcb'\<rbrace>"
  "\<lbrace>if_unsafe_then_cap'\<rbrace> setMRs t buf mrs \<lbrace>\<lambda>rv. if_unsafe_then_cap'\<rbrace>"
  by (simp add: setMRs_def zipWithM_x_mapM split_def storeWordUser_def | wp crunch_wps)+

crunch setMRs
  for no_0_obj'[wp]: no_0_obj'
  (wp: crunch_wps simp: crunch_simps)

lemma copyMRs_invs_bits[wp]:
  "\<lbrace>valid_pspace'\<rbrace> copyMRs s sb r rb n \<lbrace>\<lambda>rv. valid_pspace'\<rbrace>"
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace> copyMRs s sb r rb n
      \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  "\<lbrace>\<lambda>s. P (state_refs_of' s)\<rbrace>
      copyMRs s sb r rb n
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  "\<lbrace>if_live_then_nonz_cap'\<rbrace> copyMRs s sb r rb n \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  "\<lbrace>ex_nonz_cap_to' p\<rbrace> copyMRs s sb r rb n \<lbrace>\<lambda>rv. ex_nonz_cap_to' p\<rbrace>"
  "\<lbrace>cur_tcb'\<rbrace> copyMRs s sb r rb n \<lbrace>\<lambda>rv. cur_tcb'\<rbrace>"
  "\<lbrace>if_unsafe_then_cap'\<rbrace> copyMRs s sb r rb n \<lbrace>\<lambda>rv. if_unsafe_then_cap'\<rbrace>"
  by (simp add: copyMRs_def  storeWordUser_def | wp mapM_wp' | wpc)+

crunch copyMRs
  for no_0_obj'[wp]: no_0_obj'
  (wp: crunch_wps simp: crunch_simps)

lemma mi_map_length[simp]: "msgLength (message_info_map mi) = mi_length mi"
  by (cases mi, simp)

crunch copyMRs
  for cte_wp_at'[wp]: "cte_wp_at' P p"
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

crunch lookupExtraCaps
  for inv[wp]: "P"
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

lemma lookupCapAndSlot_corres:
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
       apply (rule corres_rel_imp, rule lookupSlotForThread_corres)
       apply (simp add: split_def)
      apply (rule corres_split[OF getSlotCap_corres])
         apply simp
        apply (rule corres_returnOkTT, simp)
       apply wp+
   apply (wp | simp add: liftE_bindE[symmetric])+
  done

lemma lookupExtraCaps_corres:
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
    apply (rule corres_underlying_split)

       apply (rule_tac S = "\<lambda>x y. x = y \<and> x < unat w2"
               in corres_mapM_list_all2
         [where Q = "\<lambda>_. valid_objs and pspace_aligned and tcb_at thread" and r = "(=)"
            and Q' = "\<lambda>_. valid_objs' and pspace_aligned' and pspace_distinct' and tcb_at' thread
              and case_option \<top> valid_ipc_buffer_ptr' buffer'" and r'="(=)" ])
            apply simp
           apply simp
          apply simp
          apply (rule corres_guard_imp)
            apply (rule loadWordUser_corres')
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
          apply (rule corres_cap_fault [OF lookupCapAndSlot_corres])
          apply simp
         apply simp
         apply (wp | simp)+
      apply (simp add: set_zip_same Int_lower1)
     apply (wp mapM_wp [OF _ subset_refl] | simp)+
  done

crunch copyMRs
  for ctes_of[wp]: "\<lambda>s. P (ctes_of s)"
  (ignore: threadSet
       wp: threadSet_ctes_of crunch_wps)

lemma copyMRs_valid_mdb[wp]:
  "\<lbrace>valid_mdb'\<rbrace> copyMRs t buf t' buf' n \<lbrace>\<lambda>rv. valid_mdb'\<rbrace>"
  by (simp add: valid_mdb'_def copyMRs_ctes_of)

crunch copy_mrs
  for valid_arch_state[wp]: valid_arch_state
  (wp: crunch_wps)

lemma doNormalTransfer_corres:
  "corres dc
  (tcb_at sender and tcb_at receiver and (pspace_aligned:: det_state \<Rightarrow> bool)
   and valid_objs and cur_tcb and valid_mdb and valid_list and valid_arch_state and pspace_distinct
   and (\<lambda>s. case ep of Some x \<Rightarrow> ep_at x s | _ \<Rightarrow> True)
   and case_option \<top> in_user_frame send_buf
   and case_option \<top> in_user_frame recv_buf)
  (tcb_at' sender and tcb_at' receiver and valid_objs'
   and pspace_aligned' and pspace_distinct' and pspace_canonical' and cur_tcb'
   and valid_mdb' and no_0_obj' and pspace_in_kernel_mappings'
   and (\<lambda>s. case ep of Some x \<Rightarrow> ep_at' x s | _ \<Rightarrow> True)
   and case_option \<top> valid_ipc_buffer_ptr' send_buf
   and case_option \<top> valid_ipc_buffer_ptr' recv_buf)
  (do_normal_transfer sender send_buf ep badge can_grant receiver recv_buf)
  (doNormalTransfer sender send_buf ep badge can_grant receiver recv_buf)"
  apply (simp add: do_normal_transfer_def doNormalTransfer_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_mapr[OF getMessageInfo_corres])
      apply (rule_tac F="valid_message_info mi" in corres_gen_asm)
      apply (rule_tac r'="list_all2 (\<lambda>x y. cap_relation (fst x) (fst y) \<and> snd y = cte_map (snd x))"
                  in corres_split)
         apply (rule corres_if[OF refl])
          apply (rule corres_split_catch)
             apply (rule lookupExtraCaps_corres; simp)
            apply (rule corres_trivial, simp)
           apply wp+
         apply (rule corres_trivial, simp)
        apply simp
        apply (rule corres_split_eqr[OF copyMRs_corres])
          apply (rule corres_split)
             apply (rule transferCaps_corres; simp)
            apply (rename_tac mi' mi'')
            apply (rule_tac F="mi_label mi' = mi_label mi"
                      in corres_gen_asm)
            apply (rule corres_split_nor[OF setMessageInfo_corres])
               apply (case_tac mi', clarsimp)
              apply (simp add: badge_register_def badgeRegister_def)
              apply (fold dc_def)
              apply (rule asUser_setRegister_corres)
             apply wp
            apply simp+
            apply ((wp valid_case_option_post_wp hoare_vcg_const_Ball_lift
                      hoare_case_option_wp
                      hoare_valid_ipc_buffer_ptr_typ_at' copyMRs_typ_at'
                      hoare_vcg_const_Ball_lift lookupExtraCaps_length
                    | simp add: if_apply_def2)+)
     apply (wp hoare_weak_lift_imp | strengthen valid_msg_length_strengthen)+
   apply clarsimp
  apply auto
  done

lemma corres_liftE_lift:
  "corres r1 P P' m m' \<Longrightarrow>
  corres (f1 \<oplus> r1) P P' (liftE m) (withoutFailure m')"
  by simp

lemmas corres_ipc_thread_helper =
  corres_split_eqrE[OF corres_liftE_lift [OF getCurThread_corres]]

lemmas corres_ipc_info_helper =
  corres_split_maprE [where f = message_info_map, OF _
                                corres_liftE_lift [OF getMessageInfo_corres]]

crunch doNormalTransfer
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"

lemmas doNormal_lifts[wp] = typ_at_lifts [OF doNormalTransfer_typ_at']

lemma doNormal_invs'[wp]:
  "\<lbrace>tcb_at' sender and tcb_at' receiver and invs'\<rbrace>
    doNormalTransfer sender send_buf ep badge
             can_grant receiver recv_buf \<lbrace>\<lambda>r. invs'\<rbrace>"
  apply (simp add: doNormalTransfer_def)
  apply (wp hoare_vcg_const_Ball_lift | simp)+
  done

crunch doNormalTransfer
  for aligned'[wp]: pspace_aligned'
  (wp: crunch_wps)
crunch doNormalTransfer
  for distinct'[wp]: pspace_distinct'
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

crunch doNormalTransfer
  for gsUntypedZeroRanges[wp]: "\<lambda>s. P (gsUntypedZeroRanges s)"
  (wp: crunch_wps transferCapsToSlots_pres1 ignore: constOnFailure)

lemmas asUser_urz = untyped_ranges_zero_lift[OF asUser_gsUntypedZeroRanges]

crunch doNormalTransfer
  for urz[wp]: "untyped_ranges_zero'"
  (ignore: asUser wp: crunch_wps asUser_urz hoare_vcg_const_Ball_lift)

lemma msgFromLookupFailure_map[simp]:
  "msgFromLookupFailure (lookup_failure_map lf)
     = msg_from_lookup_failure lf"
  by (cases lf, simp_all add: lookup_failure_map_def msgFromLookupFailure_def)

lemma asUser_getRestartPC_corres:
  "corres (=) (tcb_at t and pspace_aligned and pspace_distinct) \<top>
              (as_user t getRestartPC) (asUser t getRestartPC)"
  apply (rule asUser_corres')
  apply (rule corres_Id, simp, simp)
  apply (rule no_fail_getRestartPC)
  done

lemma asUser_mapM_getRegister_corres:
  "corres (=) (tcb_at t and pspace_aligned and pspace_distinct) \<top>
     (as_user t (mapM getRegister regs))
     (asUser t (mapM getRegister regs))"
  apply (rule asUser_corres')
  apply (rule corres_Id [OF refl refl])
  apply (rule no_fail_mapM)
  apply (simp add: getRegister_def)
  done

lemma makeArchFaultMessage_corres:
  "corres (=) (tcb_at t and pspace_aligned and pspace_distinct) \<top>
  (make_arch_fault_msg f t)
  (makeArchFaultMessage (arch_fault_map f) t)"
  apply (cases f, clarsimp simp: makeArchFaultMessage_def split: arch_fault.split)
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqr[OF asUser_getRestartPC_corres])
      apply (rule corres_trivial, simp add: arch_fault_map_def)
     apply (wp+, auto)
  done

lemma makeFaultMessage_corres:
  "corres (=) (tcb_at t and pspace_aligned and pspace_distinct) \<top>
     (make_fault_msg ft t)
     (makeFaultMessage (fault_map ft) t)"
  apply (cases ft, simp_all add: makeFaultMessage_def split del: if_split)
     apply (rule corres_guard_imp)
       apply (rule corres_split_eqr[OF asUser_getRestartPC_corres])
         apply (rule corres_trivial, simp add: fromEnum_def enum_bool)
        apply (wp | simp)+
    apply (simp add: RISCV64_H.syscallMessage_def)
    apply (rule corres_guard_imp)
      apply (rule corres_split_eqr[OF asUser_mapM_getRegister_corres])
        apply (rule corres_trivial, simp)
       apply (wp | simp)+
   apply (simp add: RISCV64_H.exceptionMessage_def)
   apply (rule corres_guard_imp)
     apply (rule corres_split_eqr[OF asUser_mapM_getRegister_corres])
       apply (rule corres_trivial, simp)
      apply (wp | simp)+
  apply (rule makeArchFaultMessage_corres)
  done

lemma makeFaultMessage_inv[wp]:
  "\<lbrace>P\<rbrace> makeFaultMessage ft t \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (cases ft, simp_all add: makeFaultMessage_def)
     apply (wp asUser_inv mapM_wp' det_mapM[where S=UNIV]
               det_getRestartPC getRestartPC_inv
             | clarsimp simp: getRegister_def makeArchFaultMessage_def
                        split: arch_fault.split)+
  done

lemmas threadget_fault_corres =
          threadGet_corres [where r = fault_rel_optionation
                              and f = tcb_fault and f' = tcbFault,
                            simplified tcb_relation_def, simplified]

lemma doFaultTransfer_corres:
  "corres dc
    (obj_at (\<lambda>ko. \<exists>tcb ft. ko = TCB tcb \<and> tcb_fault tcb = Some ft) sender
     and tcb_at receiver and case_option \<top> in_user_frame recv_buf
     and pspace_aligned and pspace_distinct)
    (case_option \<top> valid_ipc_buffer_ptr' recv_buf)
    (do_fault_transfer badge sender receiver recv_buf)
    (doFaultTransfer badge sender receiver recv_buf)"
  apply (clarsimp simp: do_fault_transfer_def doFaultTransfer_def split_def
                        RISCV64_H.badgeRegister_def badge_register_def)
  apply (rule_tac Q="\<lambda>fault. K (\<exists>f. fault = Some f) and
                             tcb_at sender and tcb_at receiver and
                             case_option \<top> in_user_frame recv_buf and
                             pspace_aligned and pspace_distinct"
              and Q'="\<lambda>fault'. case_option \<top> valid_ipc_buffer_ptr' recv_buf"
               in corres_underlying_split)
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
     apply (rule corres_split_eqr[OF makeFaultMessage_corres])
       apply (rule corres_split_eqr[OF setMRs_corres [OF refl]])
         apply (rule corres_split_nor[OF setMessageInfo_corres])
            apply simp
           apply (rule asUser_setRegister_corres)
          apply (wp | simp)+
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqr[OF makeFaultMessage_corres])
      apply (rule corres_split_eqr[OF setMRs_corres [OF refl]])
        apply (rule corres_split_nor[OF setMessageInfo_corres])
           apply simp
          apply (rule asUser_setRegister_corres)
         apply (wp | simp)+
  done

lemma doFaultTransfer_invs[wp]:
  "\<lbrace>invs' and tcb_at' receiver\<rbrace>
      doFaultTransfer badge sender receiver recv_buf
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  by (simp add: doFaultTransfer_def split_def | wp
    | clarsimp split: option.split)+

lemma lookupIPCBuffer_valid_ipc_buffer [wp]:
  "\<lbrace>valid_objs'\<rbrace> VSpace_H.lookupIPCBuffer b s \<lbrace>case_option \<top> valid_ipc_buffer_ptr'\<rbrace>"
  unfolding lookupIPCBuffer_def RISCV64_H.lookupIPCBuffer_def
  supply raw_tcb_cte_cases_simps[simp] (* FIXME arch-split: legacy, try use tcb_cte_cases_neqs *)
  apply (simp add: Let_def getSlotCap_def getThreadBufferSlot_def
                   locateSlot_conv threadGet_def comp_def)
  apply (wp getCTE_wp getObject_tcb_wp | wpc)+
  apply (clarsimp simp del: imp_disjL)
  apply (drule obj_at_ko_at')
  apply (clarsimp simp del: imp_disjL)
  apply (rule_tac x = ko in exI)
  apply (frule ko_at_cte_ipcbuffer[simplified cteSizeBits_def])
  apply (clarsimp simp: cte_wp_at_ctes_of shiftl_t2n' simp del: imp_disjL)
  apply (rename_tac ref rg sz d m)
  apply (clarsimp simp: valid_ipc_buffer_ptr'_def)
  apply (frule (1) ko_at_valid_objs')
   apply (clarsimp simp: projectKO_opts_defs split: kernel_object.split_asm)
  apply (clarsimp simp add: valid_obj'_def valid_tcb'_def
                            isCap_simps cte_level_bits_def field_simps)
  apply (drule bspec [OF _ ranI [where a = "4 << cteSizeBits"]])
   apply (simp add: cteSizeBits_def)
  apply (clarsimp simp add: valid_cap'_def frame_at'_def)
  apply (rule conjI)
   apply (rule aligned_add_aligned)
     apply (clarsimp simp add: capAligned_def)
     apply assumption
    apply (erule is_aligned_andI1)
   apply (rule order_trans[rotated])
    apply (rule pbfs_atleast_pageBits)
   apply (simp add: bit_simps msg_align_bits)
  apply (clarsimp simp: capAligned_def)
  apply (drule_tac x = "(tcbIPCBuffer ko && mask (pageBitsForSize sz))  >> pageBits" in spec)
  apply (simp add: shiftr_shiftl1 )
  apply (subst (asm) mask_out_add_aligned)
   apply (erule is_aligned_weaken [OF _ pbfs_atleast_pageBits])
  apply (erule mp)
  apply (rule shiftr_less_t2n)
  apply (clarsimp simp: pbfs_atleast_pageBits)
  apply (rule and_mask_less')
  apply (simp add: word_bits_conv pbfs_less_wb'[unfolded word_bits_conv])
  done

lemma doIPCTransfer_corres:
  "corres dc
     (tcb_at s and tcb_at r and valid_objs and pspace_aligned
        and valid_list and valid_arch_state
        and pspace_distinct and valid_mdb and cur_tcb
        and (\<lambda>s. case ep of Some x \<Rightarrow> ep_at x s | _ \<Rightarrow> True))
     (tcb_at' s and tcb_at' r and valid_pspace' and cur_tcb'
        and (\<lambda>s. case ep of Some x \<Rightarrow> ep_at' x s | _ \<Rightarrow> True))
     (do_ipc_transfer s ep bg grt r)
     (doIPCTransfer s ep bg grt r)"
  apply (simp add: do_ipc_transfer_def doIPCTransfer_def)
  apply (rule_tac Q="\<lambda>receiveBuffer sa. tcb_at s sa \<and> valid_objs sa \<and>
                       pspace_aligned sa \<and> pspace_distinct sa \<and> tcb_at r sa \<and>
                       cur_tcb sa \<and> valid_mdb sa \<and> valid_list sa \<and> valid_arch_state sa \<and>
                       (case ep of None \<Rightarrow> True | Some x \<Rightarrow> ep_at x sa) \<and>
                       case_option (\<lambda>_. True) in_user_frame receiveBuffer sa \<and>
                       obj_at (\<lambda>ko. \<exists>tcb. ko = TCB tcb
                                    \<comment> \<open>\<exists>ft. tcb_fault tcb = Some ft\<close>) s sa"
               in corres_underlying_split)
     apply (rule corres_guard_imp)
       apply (rule lookupIPCBuffer_corres')
      apply auto[2]
    apply (rule corres_underlying_split [OF _ _ thread_get_sp threadGet_inv])
     apply (rule corres_guard_imp)
       apply (rule threadget_fault_corres)
      apply simp
     defer
     apply (rule corres_guard_imp)
       apply (subst case_option_If)+
       apply (rule corres_if2)
         apply (simp add: fault_rel_optionation_def)
        apply (rule corres_split_eqr[OF lookupIPCBuffer_corres'])
          apply (simp add: dc_def[symmetric])
          apply (rule doNormalTransfer_corres)
         apply (wp | simp add: valid_pspace'_def)+
       apply (simp add: dc_def[symmetric])
       apply (rule doFaultTransfer_corres)
      apply (clarsimp simp: obj_at_def)
     apply (erule ignore_if)
    apply (wp|simp add: obj_at_def is_tcb valid_pspace'_def)+
  done


crunch doIPCTransfer
  for ifunsafe[wp]: "if_unsafe_then_cap'"
  (wp: crunch_wps hoare_vcg_const_Ball_lift get_rs_cte_at' ignore: transferCapsToSlots
    simp: zipWithM_x_mapM ball_conj_distrib )
crunch doIPCTransfer
  for iflive[wp]: "if_live_then_nonz_cap'"
  (wp: crunch_wps hoare_vcg_const_Ball_lift get_rs_cte_at' ignore: transferCapsToSlots
    simp: zipWithM_x_mapM ball_conj_distrib )
lemma valid_pspace_valid_objs'[elim!]:
  "valid_pspace' s \<Longrightarrow> valid_objs' s"
  by (simp add: valid_pspace'_def)
crunch doIPCTransfer
  for vp[wp]: "valid_pspace'"
  (wp: crunch_wps hoare_vcg_const_Ball_lift get_rs_cte_at' wp: transferCapsToSlots_vp simp:ball_conj_distrib )
crunch doIPCTransfer
  for sch_act_wf[wp]: "\<lambda>s. sch_act_wf (ksSchedulerAction s) s"
  (wp: crunch_wps get_rs_cte_at' ignore: transferCapsToSlots  simp: zipWithM_x_mapM)
crunch doIPCTransfer
  for state_refs_of[wp]: "\<lambda>s. P (state_refs_of' s)"
  (wp: crunch_wps get_rs_cte_at' ignore: transferCapsToSlots  simp: zipWithM_x_mapM)
crunch doIPCTransfer
  for ct[wp]: "cur_tcb'"
  (wp: crunch_wps get_rs_cte_at' ignore: transferCapsToSlots  simp: zipWithM_x_mapM)
crunch doIPCTransfer
  for idle'[wp]: "valid_idle'"
  (wp: crunch_wps get_rs_cte_at' ignore: transferCapsToSlots  simp: zipWithM_x_mapM)

crunch doIPCTransfer
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps  simp: zipWithM_x_mapM)
lemmas dit'_typ_ats[wp] = typ_at_lifts [OF doIPCTransfer_typ_at']

crunch doIPCTransfer
  for irq_node'[wp]: "\<lambda>s. P (irq_node' s)"
  (wp: crunch_wps simp: crunch_simps)

lemmas dit_irq_node'[wp]
    = valid_irq_node_lift [OF doIPCTransfer_irq_node' doIPCTransfer_typ_at']

crunch doIPCTransfer
  for valid_arch_state'[wp]: "valid_arch_state'"
  (wp: crunch_wps simp: crunch_simps)

(* Levity: added (20090126 19:32:26) *)
declare asUser_global_refs' [wp]

lemma lec_valid_cap' [wp]:
  "\<lbrace>valid_objs'\<rbrace> lookupExtraCaps thread xa mi \<lbrace>\<lambda>rv s. (\<forall>x\<in>set rv. s \<turnstile>' fst x)\<rbrace>, -"
  apply (rule hoare_pre, rule hoare_strengthen_postE_R)
    apply (rule hoare_vcg_conj_liftE_R[where P'=valid_objs' and Q'="\<lambda>_. valid_objs'"])
     apply (rule lookupExtraCaps_srcs)
    apply wp
   apply (clarsimp simp: cte_wp_at_ctes_of)
   apply (fastforce elim: ctes_of_valid')
  apply simp
  done

crunch doIPCTransfer
  for objs'[wp]: "valid_objs'"
   (    wp: crunch_wps hoare_vcg_const_Ball_lift
            transferCapsToSlots_valid_objs
      simp: zipWithM_x_mapM ball_conj_distrib )

crunch doIPCTransfer
  for global_refs'[wp]: "valid_global_refs'"
  (wp: crunch_wps hoare_vcg_const_Ball_lift threadSet_global_refsT
       transferCapsToSlots_valid_globals
      simp: zipWithM_x_mapM ball_conj_distrib)

declare asUser_irq_handlers' [wp]

crunch doIPCTransfer
  for irq_handlers'[wp]: "valid_irq_handlers'"
  (wp: crunch_wps hoare_vcg_const_Ball_lift threadSet_irq_handlers'
       transferCapsToSlots_irq_handlers
       simp: zipWithM_x_mapM ball_conj_distrib )

crunch doIPCTransfer
  for irq_states'[wp]: "valid_irq_states'"
  (wp: crunch_wps no_irq no_irq_mapM no_irq_storeWord no_irq_loadWord
       no_irq_case_option simp: crunch_simps zipWithM_x_mapM)

crunch doIPCTransfer
  for irqs_masked'[wp]: "irqs_masked'"
  (wp: crunch_wps simp: crunch_simps rule: irqs_masked_lift)

lemma doIPCTransfer_invs[wp]:
  "\<lbrace>invs' and tcb_at' s and tcb_at' r\<rbrace>
   doIPCTransfer s ep bg grt r
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: doIPCTransfer_def)
  apply (wpsimp wp: hoare_drop_imp)
  done

lemma sanitise_register_corres:
  "foldl (\<lambda>s (a, b). UserContext ((user_regs s)(a := sanitise_register x a b))) s
          (zip msg_template msg) =
   foldl (\<lambda>s (a, b). UserContext ((user_regs s)(a := sanitiseRegister y a b))) s
          (zip msg_template msg)"
  apply (rule foldl_cong)
    apply simp
   apply simp
  apply (clarsimp)
  apply (rule arg_cong)
  apply (clarsimp simp: sanitise_register_def sanitiseRegister_def)
  done

lemma handle_fault_reply_registers_corres:
  "corres (=) (tcb_at t and pspace_aligned and pspace_distinct) \<top>
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
    apply (rule corres_split)
       apply (rule asUser_corres')
       apply(simp add: setRegister_def syscallMessage_def)
       apply(subst zipWithM_x_modify)+
       apply(rule corres_modify')
        apply (clarsimp simp: sanitise_register_corres|wp)+
  done

lemma handleFaultReply_corres:
  "ft' = fault_map ft \<Longrightarrow>
   corres (=) (tcb_at t and pspace_aligned and pspace_distinct) \<top>
     (handle_fault_reply ft t label msg)
     (handleFaultReply ft' t label msg)"
  apply (cases ft)
     apply(simp_all add: handleFaultReply_def
                         handle_arch_fault_reply_def handleArchFaultReply_def
                         syscallMessage_def exceptionMessage_def
                    split: arch_fault.split)
   by (rule handle_fault_reply_registers_corres)+

crunch handleFaultReply
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"

lemmas hfr_typ_ats[wp] = typ_at_lifts [OF handleFaultReply_typ_at']

crunch handleFaultReply
  for ct'[wp]: "\<lambda>s. P (ksCurThread s)"

lemma doIPCTransfer_sch_act_simple [wp]:
  "\<lbrace>sch_act_simple\<rbrace> doIPCTransfer sender endpoint badge grant receiver \<lbrace>\<lambda>_. sch_act_simple\<rbrace>"
  by (simp add: sch_act_simple_def, wp)

lemma possibleSwitchTo_invs'[wp]:
  "\<lbrace>invs' and st_tcb_at' runnable' t
          and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t)\<rbrace>
   possibleSwitchTo t \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: possibleSwitchTo_def curDomain_def)
  apply (wp tcbSchedEnqueue_invs' ssa_invs')
       apply (rule hoare_post_imp[OF _ rescheduleRequired_sa_cnt])
      apply (wpsimp wp: ssa_invs' threadGet_wp)+
  apply (clarsimp dest!: obj_at_ko_at' simp: tcb_in_cur_domain'_def obj_at'_def)
  done

crunch isFinalCapability
  for cur'[wp]: "\<lambda>s. P (cur_tcb' s)"
  (simp: crunch_simps unless_when
     wp: crunch_wps getObject_inv loadObject_default_inv)

crunch deleteCallerCap
  for ct'[wp]: "\<lambda>s. P (ksCurThread s)"
  (simp: crunch_simps unless_when
     wp: crunch_wps getObject_inv loadObject_default_inv)

lemma getThreadCallerSlot_inv:
  "\<lbrace>P\<rbrace> getThreadCallerSlot t \<lbrace>\<lambda>_. P\<rbrace>"
  by (simp add: getThreadCallerSlot_def, wp)

lemma finaliseCapTrue_standin_tcb_at' [wp]:
  "\<lbrace>tcb_at' x\<rbrace> finaliseCapTrue_standin cap v2 \<lbrace>\<lambda>_. tcb_at' x\<rbrace>"
  apply (simp add: finaliseCapTrue_standin_def Let_def)
  apply (safe)
       apply (wp getObject_ntfn_inv
            | wpc
            | simp)+
  done

lemma finaliseCapTrue_standin_cur':
  "\<lbrace>\<lambda>s. cur_tcb' s\<rbrace> finaliseCapTrue_standin cap v2 \<lbrace>\<lambda>_ s'. cur_tcb' s'\<rbrace>"
  apply (simp add: cur_tcb'_def)
  apply (rule hoare_lift_Pf2 [OF _ finaliseCapTrue_standin_ct'])
  apply (wp)
  done

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

lemma capClass_Reply:
  "capClass cap = ReplyClass tcb \<Longrightarrow> isReplyCap cap \<and> capTCBPtr cap = tcb"
  apply (cases cap, simp_all add: isCap_simps)
  apply (rename_tac arch_capability)
  apply (case_tac arch_capability, simp_all)
  done

lemma reply_cap_end_mdb_chain:
  "\<lbrakk> cte_wp_at (is_reply_cap_to t) slot s; invs s;
     invs' s';
     (s, s') \<in> state_relation; ctes_of s' (cte_map slot) = Some cte \<rbrakk>
      \<Longrightarrow> (mdbPrev (cteMDBNode cte) \<noteq> nullPointer
            \<and> mdbNext (cteMDBNode cte) = nullPointer)
           \<and> cte_wp_at' (\<lambda>cte. isReplyCap (cteCap cte) \<and> capReplyMaster (cteCap cte))
                    (mdbPrev (cteMDBNode cte)) s'"
  apply (clarsimp simp only: cte_wp_at_reply_cap_to_ex_rights)
  apply (frule(1) pspace_relation_ctes_ofI[OF state_relation_pspace_relation],
         clarsimp+)
  apply (subgoal_tac "\<exists>slot' rights'. caps_of_state s slot' = Some (cap.ReplyCap t True rights')
                          \<and> descendants_of slot' (cdt s) = {slot}")
   apply (elim state_relationE exE)
   apply (clarsimp simp: cdt_relation_def
               simp del: split_paired_All)
   apply (drule spec, drule(1) mp[OF _ caps_of_state_cte_at])
   apply (frule(1) pspace_relation_cte_wp_at[OF _ caps_of_state_cteD],
          clarsimp+)
   apply (clarsimp simp: descendants_of'_def cte_wp_at_ctes_of)
   apply (frule_tac f="\<lambda>S. cte_map slot \<in> S" in arg_cong, simp(no_asm_use))
   apply (frule invs_mdb'[unfolded valid_mdb'_def])
   apply (rule context_conjI)
    apply (clarsimp simp: nullPointer_def valid_mdb_ctes_def)
    apply (erule(4) subtree_prev_0)
   apply (rule conjI)
    apply (rule ccontr)
    apply (frule valid_mdb_no_loops, simp add: no_loops_def)
    apply (drule_tac x="cte_map slot" in spec)
    apply (erule notE, rule r_into_trancl, rule ccontr)
    apply (clarsimp simp: mdb_next_unfold valid_mdb_ctes_def nullPointer_def)
    apply (rule valid_dlistEn, assumption+)
    apply (subgoal_tac "ctes_of s' \<turnstile> cte_map slot \<leadsto> mdbNext (cteMDBNode cte)")
     apply (frule(3) class_linksD)
     apply (clarsimp simp: isCap_simps dest!: capClass_Reply[OF sym])
     apply (drule_tac f="\<lambda>S. mdbNext (cteMDBNode cte) \<in> S" in arg_cong)
     apply (simp, erule notE, rule subtree.trans_parent, assumption+)
     apply (case_tac ctea, case_tac cte')
     apply (clarsimp simp add: parentOf_def isMDBParentOf_CTE)
     apply (simp add: sameRegionAs_def2 isCap_simps)
     apply (erule subtree.cases)
      apply (clarsimp simp: parentOf_def isMDBParentOf_CTE)
     apply (clarsimp simp: parentOf_def isMDBParentOf_CTE)
    apply (simp add: mdb_next_unfold)
   apply (erule subtree.cases)
    apply (clarsimp simp: valid_mdb_ctes_def)
    apply (erule_tac cte=ctea in valid_dlistEn, assumption)
     apply (simp add: mdb_next_unfold)
    apply (clarsimp simp: mdb_next_unfold isCap_simps)
   apply (drule_tac f="\<lambda>S. c' \<in> S" in arg_cong)
   apply (clarsimp simp: no_loops_direct_simp valid_mdb_no_loops)
  apply (frule invs_mdb)
  apply (drule invs_valid_reply_caps)
  apply (clarsimp simp: valid_mdb_def reply_mdb_def
                        valid_reply_caps_def reply_caps_mdb_def
                        cte_wp_at_caps_of_state
              simp del: split_paired_All)
  apply (erule_tac x=slot in allE, erule_tac x=t in allE, erule impE, fast)
  apply (elim exEI)
  apply clarsimp
  apply (subgoal_tac "P" for P, rule sym, rule equalityI, assumption)
   apply clarsimp
   apply (erule(4) unique_reply_capsD)
  apply (simp add: descendants_of_def)
  apply (rule r_into_trancl)
  apply (simp add: cdt_parent_rel_def is_cdt_parent_def)
  done

lemma unbindNotification_valid_objs'_strengthen:
  "valid_tcb' tcb s \<longrightarrow> valid_tcb' (tcbBoundNotification_update Map.empty tcb) s"
  "valid_ntfn' ntfn s \<longrightarrow> valid_ntfn' (ntfnBoundTCB_update Map.empty ntfn) s"
  by (simp_all add: unbindNotification_valid_objs'_helper' unbindNotification_valid_objs'_helper)

crunch cteDeleteOne
  for valid_objs'[wp]: "valid_objs'"
  (simp: crunch_simps unless_def
   wp: crunch_wps getObject_inv loadObject_default_inv)

crunch handleFaultReply
  for nosch[wp]: "\<lambda>s. P (ksSchedulerAction s)"

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

crunch finaliseCapTrue_standin
  for weak_sch_act_wf[wp]: "\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s"
 (ignore: setThreadState
    simp: crunch_simps
      wp: crunch_wps getObject_inv loadObject_default_inv)

lemma cteDeleteOne_weak_sch_act[wp]:
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>
   cteDeleteOne sl
   \<lbrace>\<lambda>_ s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp add: cteDeleteOne_def unless_def)
  apply (wp hoare_drop_imps finaliseCapTrue_standin_cur' isFinalCapability_cur'
         | simp add: split_def)+
  done

crunch emptySlot
  for weak_sch_act_wf[wp]: "\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s"

crunch handleFaultReply
  for pred_tcb_at'[wp]: "pred_tcb_at' proj P t"
crunch handleFaultReply
  for tcb_in_cur_domain'[wp]: "tcb_in_cur_domain' t"

crunch unbindNotification
  for sch_act_wf[wp]: "\<lambda>s. sch_act_wf (ksSchedulerAction s) s"
(wp: sbn_sch_act')

crunch handleFaultReply
  for valid_objs'[wp]: valid_objs'

lemma cte_wp_at_is_reply_cap_toI:
  "cte_wp_at ((=) (cap.ReplyCap t False rights)) ptr s
   \<Longrightarrow> cte_wp_at (is_reply_cap_to t) ptr s"
  by (fastforce simp: cte_wp_at_reply_cap_to_ex_rights)

crunch handle_fault_reply
  for pspace_alignedp[wp]: pspace_aligned
  and pspace_distinct[wp]: pspace_distinct

crunch cteDeleteOne, doIPCTransfer, handleFaultReply
  for sym_heap_sched_pointers[wp]: sym_heap_sched_pointers
  and valid_sched_pointers[wp]: valid_sched_pointers
  and pspace_aligned'[wp]: pspace_aligned'
  and pspace_distinct'[wp]: pspace_distinct'
  (rule: sym_heap_sched_pointers_lift wp: crunch_wps simp: crunch_simps)

lemma doReplyTransfer_corres:
  "corres dc
     (einvs and tcb_at receiver and tcb_at sender
           and cte_wp_at ((=) (cap.ReplyCap receiver False rights)) slot)
     (invs' and tcb_at' sender and tcb_at' receiver
            and valid_pspace' and cte_at' (cte_map slot))
     (do_reply_transfer sender receiver slot grant)
     (doReplyTransfer sender receiver (cte_map slot) grant)"
  apply (simp add: do_reply_transfer_def doReplyTransfer_def cong: option.case_cong)
  apply (rule corres_underlying_split [OF _ _ gts_sp gts_sp'])
   apply (rule corres_guard_imp)
     apply (rule getThreadState_corres, (clarsimp simp add: st_tcb_at_tcb_at invs_distinct invs_psp_aligned)+)
  apply (rule_tac F = "awaiting_reply state" in corres_req)
   apply (clarsimp simp add: st_tcb_at_def obj_at_def is_tcb)
   apply (fastforce simp: invs_def valid_state_def intro: has_reply_cap_cte_wpD
                   dest: has_reply_cap_cte_wpD
                  dest!: valid_reply_caps_awaiting_reply cte_wp_at_is_reply_cap_toI)
  apply (case_tac state, simp_all add: bind_assoc)
  apply (simp add: isReply_def liftM_def)
  apply (rule corres_symb_exec_r[OF _ getCTE_sp getCTE_inv, rotated])
   apply (rule no_fail_pre, wp)
   apply clarsimp
  apply (rename_tac mdbnode)
  apply (rule_tac P="Q" and Q="Q" and P'="Q'" and Q'="(\<lambda>s. Q' s \<and> R' s)" for Q Q' R'
            in stronger_corres_guard_imp[rotated])
    apply assumption
   apply (rule conjI, assumption)
   apply (clarsimp simp: cte_wp_at_ctes_of)
   apply (drule cte_wp_at_is_reply_cap_toI)
   apply (erule(4) reply_cap_end_mdb_chain)
  apply (rule corres_assert_assume[rotated], simp)
  apply (simp add: getSlotCap_def)
  apply (rule corres_symb_exec_r[OF _ getCTE_sp getCTE_inv, rotated])
   apply (rule no_fail_pre, wp)
   apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (rule corres_assert_assume[rotated])
   apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF threadget_fault_corres])
      apply (case_tac rv, simp_all add: fault_rel_optionation_def bind_assoc)[1]
       apply (rule corres_split[OF doIPCTransfer_corres])
         apply (rule corres_split[OF cap_delete_one_corres])
           apply (rule corres_split[OF setThreadState_corres])
              apply simp
             apply (rule possibleSwitchTo_corres)
            apply (wp set_thread_state_runnable_valid_sched
                      set_thread_state_runnable_weak_valid_sched_action sts_st_tcb_at' sts_st_tcb'
                      sts_valid_objs' delete_one_tcbDomain_obj_at'
                   | simp add: valid_tcb_state'_def
                   | strengthen valid_queues_in_correct_ready_q valid_sched_valid_queues
                                valid_queues_ready_qs_distinct)+
        apply (strengthen cte_wp_at_reply_cap_can_fast_finalise)
        apply (wp hoare_vcg_conj_lift)
         apply (rule hoare_strengthen_post [OF do_ipc_transfer_non_null_cte_wp_at])
          prefer 2
          apply (erule cte_wp_at_weakenE)
          apply (fastforce)
         apply (clarsimp simp:is_cap_simps)
        apply (wp weak_valid_sched_action_lift)+
       apply (rule_tac Q'="\<lambda>_ s. valid_objs' s \<and> cur_tcb' s \<and> tcb_at' receiver s
                                \<and> sch_act_wf (ksSchedulerAction s) s
                                \<and> sym_heap_sched_pointers s \<and> valid_sched_pointers s
                                \<and> pspace_aligned' s \<and> pspace_distinct' s"
                    in hoare_post_imp, simp add: sch_act_wf_weak)
       apply (wp tcb_in_cur_domain'_lift)
      defer
      apply (simp)
      apply (wp)+
    apply (clarsimp simp: invs_psp_aligned invs_distinct)
    apply (rule conjI, erule invs_valid_objs)
    apply (rule conjI, clarsimp)+
    apply (rule conjI)
     apply (erule cte_wp_at_weakenE)
     apply (clarsimp)
     apply (rule conjI, rule refl)
     apply (fastforce)
    apply (clarsimp simp: invs_def valid_sched_def valid_sched_action_def invs_psp_aligned invs_distinct)
   apply (simp)
   apply (auto simp: invs'_def valid_state'_def)[1]

  apply (rule corres_guard_imp)
    apply (rule corres_split[OF cap_delete_one_corres])
      apply (rule corres_split_mapr[OF getMessageInfo_corres])
        apply (rule corres_split_eqr[OF lookupIPCBuffer_corres'])
          apply (rule corres_split_eqr[OF getMRs_corres])
            apply (simp(no_asm) del: dc_simp)
            apply (rule corres_split_eqr[OF handleFaultReply_corres])
               apply simp
              apply (rule corres_split)
                 apply (rule threadset_corresT;
                        clarsimp simp add: tcb_relation_def fault_rel_optionation_def cteSizeBits_def
                                           tcb_cap_cases_def tcb_cte_cases_def inQ_def)
                apply (rule_tac Q="valid_sched and cur_tcb and tcb_at receiver and pspace_aligned and pspace_distinct"
                            and Q'="tcb_at' receiver and cur_tcb'
                                      and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s)
                                      and valid_objs'
                                      and sym_heap_sched_pointers and valid_sched_pointers
                                      and pspace_aligned' and pspace_distinct'"
                              in corres_guard_imp)
                  apply (case_tac rvb, simp_all)[1]
                   apply (rule corres_guard_imp)
                     apply (rule corres_split[OF setThreadState_corres])
                        apply (clarsimp simp: tcb_relation_def)
                       apply (fold dc_def, rule possibleSwitchTo_corres)
                      apply simp
                      apply (wp hoare_weak_lift_imp hoare_weak_lift_imp_conj set_thread_state_runnable_weak_valid_sched_action sts_st_tcb_at'
                                sts_st_tcb' sts_valid_objs'
                             | force simp: valid_sched_def valid_sched_action_def valid_tcb_state'_def)+
                  apply (rule corres_guard_imp)
                    apply (rule setThreadState_corres)
                    apply (clarsimp simp: tcb_relation_def)
                   apply (wp threadSet_cur weak_sch_act_wf_lift_linear threadSet_pred_tcb_no_state
                             thread_set_not_state_valid_sched
                             threadSet_tcbDomain_triv threadSet_valid_objs'
                             threadSet_sched_pointers threadSet_valid_sched_pointers
                        | simp add: valid_tcb_state'_def)+
     apply (rule_tac Q'="\<lambda>_. valid_sched and cur_tcb and tcb_at sender and tcb_at receiver and
                            valid_objs and pspace_aligned and pspace_distinct"
                     in hoare_strengthen_post [rotated], clarsimp)
     apply (wp)
     apply (rule hoare_chain [OF cap_delete_one_invs])
      apply (assumption)
     apply (rule conjI, clarsimp)
     apply (clarsimp simp add: invs_def valid_state_def valid_pspace_def)
    apply (rule_tac Q'="\<lambda>_. tcb_at' sender and tcb_at' receiver and invs'"
                    in hoare_strengthen_post [rotated])
     apply (solves\<open>auto simp: invs'_def valid_state'_def\<close>)
    apply wp
   apply clarsimp
   apply (rule conjI)
    apply (erule cte_wp_at_weakenE)
    apply (clarsimp simp add: can_fast_finalise_def)
   apply (erule(1) emptyable_cte_wp_atD)
   apply (rule allI, rule impI)
   apply (clarsimp simp add: is_master_reply_cap_def)
  apply (clarsimp)
  done

(* when we cannot talk about reply cap rights explicitly (for instance, when a schematic ?rights
   would be generated too early *)
lemma doReplyTransfer_corres':
  "corres dc
     (einvs and tcb_at receiver and tcb_at sender
           and cte_wp_at (is_reply_cap_to receiver) slot)
     (invs' and tcb_at' sender and tcb_at' receiver
            and valid_pspace' and cte_at' (cte_map slot))
     (do_reply_transfer sender receiver slot grant)
     (doReplyTransfer sender receiver (cte_map slot) grant)"
  using doReplyTransfer_corres[of receiver sender _ slot]
  by (fastforce simp add: cte_wp_at_reply_cap_to_ex_rights corres_underlying_def)

lemma valid_pspace'_splits[elim!]:
  "valid_pspace' s \<Longrightarrow> valid_objs' s"
  "valid_pspace' s \<Longrightarrow> pspace_aligned' s"
  "valid_pspace' s \<Longrightarrow> pspace_canonical' s"
  "valid_pspace' s \<Longrightarrow> pspace_in_kernel_mappings' s"
  "valid_pspace' s \<Longrightarrow> pspace_distinct' s"
  "valid_pspace' s \<Longrightarrow> valid_mdb' s"
  "valid_pspace' s \<Longrightarrow> no_0_obj' s"
  by (simp add: valid_pspace'_def)+

lemma sts_valid_pspace_hangers:
  "\<lbrace>valid_pspace' and tcb_at' t and valid_tcb_state' st\<rbrace> setThreadState st t \<lbrace>\<lambda>rv. valid_objs'\<rbrace>"
  "\<lbrace>valid_pspace' and tcb_at' t and valid_tcb_state' st\<rbrace> setThreadState st t \<lbrace>\<lambda>rv. pspace_distinct'\<rbrace>"
  "\<lbrace>valid_pspace' and tcb_at' t and valid_tcb_state' st\<rbrace> setThreadState st t \<lbrace>\<lambda>rv. pspace_aligned'\<rbrace>"
  "\<lbrace>valid_pspace' and tcb_at' t and valid_tcb_state' st\<rbrace> setThreadState st t \<lbrace>\<lambda>rv. pspace_canonical'\<rbrace>"
  "\<lbrace>valid_pspace' and tcb_at' t and valid_tcb_state' st\<rbrace> setThreadState st t \<lbrace>\<lambda>rv. pspace_in_kernel_mappings'\<rbrace>"
  "\<lbrace>valid_pspace' and tcb_at' t and valid_tcb_state' st\<rbrace> setThreadState st t \<lbrace>\<lambda>rv. valid_mdb'\<rbrace>"
  "\<lbrace>valid_pspace' and tcb_at' t and valid_tcb_state' st\<rbrace> setThreadState st t \<lbrace>\<lambda>rv. no_0_obj'\<rbrace>"
  by (safe intro!: hoare_strengthen_post [OF sts'_valid_pspace'_inv])

declare no_fail_getSlotCap [wp]

lemma setupCallerCap_corres:
  "corres dc
     (st_tcb_at (Not \<circ> halted) sender and tcb_at receiver and
      st_tcb_at (Not \<circ> awaiting_reply) sender and valid_reply_caps and
      valid_objs and pspace_distinct and pspace_aligned and valid_mdb
      and valid_list and valid_arch_state and
      valid_reply_masters and cte_wp_at (\<lambda>c. c = cap.NullCap) (receiver, tcb_cnode_index 3))
     (tcb_at' sender and tcb_at' receiver and valid_pspace'
                and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s))
     (setup_caller_cap sender receiver grant)
     (setupCallerCap sender receiver grant)"
  supply if_split[split del]
  apply (simp add: setup_caller_cap_def setupCallerCap_def
                   getThreadReplySlot_def locateSlot_conv
                   getThreadCallerSlot_def)
  apply (rule stronger_corres_guard_imp)
    apply (rule corres_split_nor)
       apply (rule setThreadState_corres)
       apply (simp split: option.split)
      apply (rule corres_symb_exec_r)
         apply (rule_tac F="\<exists>r. cteCap masterCTE = capability.ReplyCap sender True r
                             \<and> mdbNext (cteMDBNode masterCTE) = nullPointer"
                      in corres_gen_asm2, clarsimp simp add: isCap_simps)
         apply (rule corres_symb_exec_r)
            apply (rule_tac F="rv = capability.NullCap"
                         in corres_gen_asm2, simp)
            apply (rule cteInsert_corres)
              apply (simp split: if_splits)
             apply (simp add: cte_map_def tcbReplySlot_def
                              tcb_cnode_index_def cte_level_bits_def)
            apply (simp add: cte_map_def tcbCallerSlot_def
                             tcb_cnode_index_def cte_level_bits_def)
           apply (rule_tac Q'="\<lambda>rv. cte_at' (receiver + 2 ^ cte_level_bits * tcbCallerSlot)"
                    in hoare_post_add)

           apply (wp, (wp getSlotCap_wp)+)
          apply blast
         apply (rule no_fail_pre, wp)
         apply (clarsimp simp: cte_wp_at'_def cte_at'_def)
        apply (rule_tac Q'="\<lambda>rv. cte_at' (sender + 2 ^ cte_level_bits * tcbReplySlot)"
                     in hoare_post_add)
        apply (wp, (wp getCTE_wp')+)
       apply blast
      apply (rule no_fail_pre, wp)
      apply (clarsimp simp: cte_wp_at_ctes_of)
     apply (wp sts_valid_pspace_hangers
                 | simp add: cte_wp_at_ctes_of)+
   apply (clarsimp simp: valid_tcb_state_def st_tcb_at_reply_cap_valid
                         st_tcb_at_tcb_at st_tcb_at_caller_cap_null
                  split: option.split)
  apply (clarsimp simp: valid_tcb_state'_def valid_cap'_def capAligned_reply_tcbI)
  apply (frule(1) st_tcb_at_reply_cap_valid, simp, clarsimp)
  apply (clarsimp simp: cte_wp_at_ctes_of cte_wp_at_caps_of_state)
  apply (drule pspace_relation_cte_wp_at[rotated, OF caps_of_state_cteD],
         erule valid_pspace'_splits, clarsimp+)+
  apply (clarsimp simp: cte_wp_at_ctes_of cte_map_def tcbReplySlot_def
                        tcbCallerSlot_def tcb_cnode_index_def
                        is_cap_simps)
  apply (auto intro: reply_no_descendants_mdbNext_null[OF not_waiting_reply_slot_no_descendants]
               simp: cte_level_bits_def)
  done

crunch getThreadCallerSlot
  for tcb_at'[wp]: "tcb_at' t"

lemma getThreadReplySlot_tcb_at'[wp]:
  "\<lbrace>tcb_at' t\<rbrace> getThreadReplySlot tcb \<lbrace>\<lambda>_. tcb_at' t\<rbrace>"
  by (simp add: getThreadReplySlot_def, wp)

lemma setupCallerCap_tcb_at'[wp]:
  "\<lbrace>tcb_at' t\<rbrace> setupCallerCap sender receiver grant \<lbrace>\<lambda>_. tcb_at' t\<rbrace>"
  by (simp add: setupCallerCap_def, wp hoare_drop_imp)

crunch setupCallerCap
  for ct'[wp]: "\<lambda>s. P (ksCurThread s)"
  (wp: crunch_wps)

lemma cteInsert_sch_act_wf[wp]:
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>
     cteInsert newCap srcSlot destSlot
   \<lbrace>\<lambda>_ s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
by (wp sch_act_wf_lift tcb_in_cur_domain'_lift)

lemma setupCallerCap_sch_act [wp]:
  "\<lbrace>\<lambda>s. sch_act_not t s \<and> sch_act_wf (ksSchedulerAction s) s\<rbrace>
  setupCallerCap t r g \<lbrace>\<lambda>_ s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp add: setupCallerCap_def getSlotCap_def getThreadCallerSlot_def
            getThreadReplySlot_def locateSlot_conv)
  apply (wp getCTE_wp' sts_sch_act' hoare_drop_imps hoare_vcg_all_lift)
  apply clarsimp
  done

lemma possibleSwitchTo_weak_sch_act_wf[wp]:
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s \<and> st_tcb_at' runnable' t s\<rbrace>
      possibleSwitchTo t \<lbrace>\<lambda>rv s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp add: possibleSwitchTo_def setSchedulerAction_def threadGet_def curDomain_def
                   bitmap_fun_defs)
  apply (wp rescheduleRequired_weak_sch_act_wf
            weak_sch_act_wf_lift_linear[where f="tcbSchedEnqueue t"]
            getObject_tcb_wp hoare_weak_lift_imp
           | wpc)+
  apply (clarsimp simp: obj_at'_def projectKOs weak_sch_act_wf_def ps_clear_def tcb_in_cur_domain'_def)
  done

lemmas transferCapsToSlots_pred_tcb_at' =
    transferCapsToSlots_pres1 [OF cteInsert_pred_tcb_at']

crunch doIPCTransfer, possibleSwitchTo
  for pred_tcb_at'[wp]: "pred_tcb_at' proj P t"
  (wp: mapM_wp' crunch_wps simp: zipWithM_x_mapM)

lemma setSchedulerAction_ct_in_domain:
 "\<lbrace>\<lambda>s. ct_idle_or_in_cur_domain' s
   \<and>  p \<noteq> ResumeCurrentThread \<rbrace> setSchedulerAction p
  \<lbrace>\<lambda>_. ct_idle_or_in_cur_domain'\<rbrace>"
  by (simp add:setSchedulerAction_def | wp)+

crunch setupCallerCap, doIPCTransfer, possibleSwitchTo
  for ct_idle_or_in_cur_domain'[wp]: ct_idle_or_in_cur_domain'
  (wp: crunch_wps setSchedulerAction_ct_in_domain simp: zipWithM_x_mapM)
crunch setupCallerCap, doIPCTransfer, possibleSwitchTo
  for ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  and ksDomSchedule[wp]: "\<lambda>s. P (ksDomSchedule s)"
  (wp: crunch_wps simp: zipWithM_x_mapM)

crunch doIPCTransfer
  for tcbDomain_obj_at'[wp]: "obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t"
  (wp: crunch_wps constOnFailure_wp simp: crunch_simps)

crunch possibleSwitchTo
  for tcb_at'[wp]: "tcb_at' t"
  (wp: crunch_wps)

crunch possibleSwitchTo
  for valid_pspace'[wp]: valid_pspace'
  (wp: crunch_wps)

lemma sendIPC_corres:
(* call is only true if called in handleSyscall SysCall, which
   is always blocking. *)
  assumes "call \<longrightarrow> bl"
  shows
  "corres dc (einvs and st_tcb_at active t and ep_at ep and ex_nonz_cap_to t)
             (invs' and  sch_act_not t and tcb_at' t and ep_at' ep)
             (send_ipc bl call bg cg cgr t ep) (sendIPC bl call bg cg cgr t ep)"
proof -
  show ?thesis
  apply (insert assms)
  apply (unfold send_ipc_def sendIPC_def Let_def)
  apply (case_tac bl)
   apply clarsimp
   apply (rule corres_guard_imp)
     apply (rule corres_split[OF getEndpoint_corres,
              where
              R="\<lambda>rv. einvs and st_tcb_at active t and ep_at ep and
                      valid_ep rv and obj_at (\<lambda>ob. ob = Endpoint rv) ep
                      and ex_nonz_cap_to t"
              and
              R'="\<lambda>rv'. invs' and tcb_at' t and sch_act_not t
                              and ep_at' ep and valid_ep' rv'"])
       apply (case_tac rv)
         apply (simp add: ep_relation_def)
         apply (rule corres_guard_imp)
           apply (rule corres_split[OF setThreadState_corres])
              apply simp
             apply (rule setEndpoint_corres)
             apply (simp add: ep_relation_def)
            apply wp+
          apply (clarsimp simp: st_tcb_at_tcb_at valid_tcb_state_def invs_distinct)
         apply clarsimp
         \<comment> \<open>concludes IdleEP if bl branch\<close>
        apply (simp add: ep_relation_def)
        apply (rule corres_guard_imp)
          apply (rule corres_split[OF setThreadState_corres])
             apply simp
            apply (rule setEndpoint_corres)
            apply (simp add: ep_relation_def)
           apply wp+
         apply (clarsimp simp: st_tcb_at_tcb_at valid_tcb_state_def invs_distinct)
        apply clarsimp
        \<comment> \<open>concludes SendEP if bl branch\<close>
       apply (simp add: ep_relation_def)
       apply (rename_tac list)
       apply (rule_tac F="list \<noteq> []" in corres_req)
        apply (simp add: valid_ep_def)
       apply (case_tac list)
        apply simp
       apply (clarsimp split del: if_split)
       apply (rule corres_guard_imp)
         apply (rule corres_split[OF setEndpoint_corres])
            apply (simp add: ep_relation_def split: list.split)
           apply (simp add: isReceive_def split del:if_split)
           apply (rule corres_split[OF getThreadState_corres])
             apply (rule_tac
                    F="\<exists>data. recv_state = Structures_A.BlockedOnReceive ep data"
                    in corres_gen_asm)
             apply (clarsimp simp: case_bool_If  case_option_If if3_fold
                         simp del: dc_simp split del: if_split cong: if_cong)
             apply (rule corres_split[OF doIPCTransfer_corres])
               apply (rule corres_split[OF setThreadState_corres])
                  apply simp
                 apply (rule corres_split[OF possibleSwitchTo_corres])
                   apply (fold when_def)[1]
                   apply (rule_tac P="call" and P'="call"
                            in corres_symmetric_bool_cases, blast)
                    apply (simp add: when_def dc_def[symmetric] split del: if_split)
                    apply (rule corres_if2, simp)
                     apply (rule setupCallerCap_corres)
                    apply (rule setThreadState_corres, simp)
                   apply (rule corres_trivial)
                   apply (simp add: when_def dc_def[symmetric] split del: if_split)
                  apply (simp split del: if_split add: if_apply_def2)
                  apply (wp hoare_drop_imps)[1]
                 apply (simp split del: if_split add: if_apply_def2)
                 apply (wp hoare_drop_imps)[1]
                apply (wp | simp)+
                apply (wp sts_cur_tcb set_thread_state_runnable_weak_valid_sched_action sts_st_tcb_at_cases)
               apply (wp sts_weak_sch_act_wf sts_valid_objs'
                         sts_cur_tcb' setThreadState_tcb' sts_st_tcb_at'_cases)[1]
              apply (simp add: valid_tcb_state_def pred_conj_def)
              apply (strengthen reply_cap_doesnt_exist_strg disjI2_strg
                                valid_queues_in_correct_ready_q valid_queues_ready_qs_distinct
                                valid_sched_valid_queues)+
              apply ((wp hoare_drop_imps do_ipc_transfer_tcb_caps weak_valid_sched_action_lift
                         do_ipc_transfer_valid_arch
                   | clarsimp simp: is_cap_simps)+)[1]
             apply (simp add: pred_conj_def)
             apply (strengthen sch_act_wf_weak)
             apply (simp add: valid_tcb_state'_def)
             apply (wp weak_sch_act_wf_lift_linear tcb_in_cur_domain'_lift hoare_drop_imps)[1]
            apply (wp gts_st_tcb_at)+
          apply (simp add: pred_conj_def cong: conj_cong)
          apply (wp hoare_TrueI)
         apply (simp)
         apply (wp weak_sch_act_wf_lift_linear set_ep_valid_objs' setEndpoint_valid_mdb')+
        apply (clarsimp simp add: invs_def valid_state_def valid_pspace_def ep_redux_simps
                        ep_redux_simps' st_tcb_at_tcb_at valid_ep_def
                        cong: list.case_cong)
        apply (drule(1) sym_refs_obj_atD[where P="\<lambda>ob. ob = e" for e])
        apply (clarsimp simp: st_tcb_at_refs_of_rev st_tcb_at_reply_cap_valid
                              st_tcb_def2 valid_sched_def valid_sched_action_def)
        apply (force simp: st_tcb_def2 dest!: st_tcb_at_caller_cap_null[simplified,rotated])
       subgoal by (auto simp: valid_ep'_def invs'_def valid_state'_def split: list.split)
      apply wp+
    apply (clarsimp simp: ep_at_def2)+
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getEndpoint_corres,
             where
             R="\<lambda>rv. einvs and st_tcb_at active t and ep_at ep and
                     valid_ep rv and obj_at (\<lambda>k. k = Endpoint rv) ep"
             and
             R'="\<lambda>rv'. invs' and tcb_at' t and sch_act_not t
                             and ep_at' ep and valid_ep' rv'"])
      apply (rename_tac rv rv')
      apply (case_tac rv)
        apply (simp add: ep_relation_def)
        \<comment> \<open>concludes IdleEP branch if not bl and no ft\<close>
       apply (simp add: ep_relation_def)
       \<comment> \<open>concludes SendEP branch if not bl and no ft\<close>
      apply (simp add: ep_relation_def)
      apply (rename_tac list)
      apply (rule_tac F="list \<noteq> []" in corres_req)
       apply (simp add: valid_ep_def)
      apply (case_tac list)
       apply simp
      apply (rule_tac F="a \<noteq> t" in corres_req)
       apply (clarsimp simp: invs_def valid_state_def
                             valid_pspace_def)
       apply (drule(1) sym_refs_obj_atD[where P="\<lambda>ob. ob = e" for e])
       apply (clarsimp simp: st_tcb_at_def obj_at_def tcb_bound_refs_def2)
       apply fastforce
      apply (clarsimp split del: if_split)
      apply (rule corres_guard_imp)
        apply (rule corres_split[OF setEndpoint_corres])
           apply (simp add: ep_relation_def split: list.split)
          apply (rule corres_split[OF getThreadState_corres])
            apply (rule_tac
               F="\<exists>data. recv_state = Structures_A.BlockedOnReceive ep data"
                   in corres_gen_asm)
            apply (clarsimp simp: isReceive_def case_bool_If
                       split del: if_split cong: if_cong)
            apply (rule corres_split[OF doIPCTransfer_corres])
              apply (rule corres_split[OF setThreadState_corres])
                 apply simp
                apply (rule possibleSwitchTo_corres)
               apply (simp add: if_apply_def2)
               apply ((wp sts_cur_tcb set_thread_state_runnable_weak_valid_sched_action sts_st_tcb_at_cases |
                          simp add: if_apply_def2 split del: if_split)+)[1]
              apply (wp sts_weak_sch_act_wf sts_valid_objs'
                        sts_cur_tcb' setThreadState_tcb' sts_st_tcb_at'_cases)
             apply (simp add: valid_tcb_state_def pred_conj_def)
             apply ((wp hoare_drop_imps do_ipc_transfer_tcb_caps  weak_valid_sched_action_lift
                     | clarsimp simp: is_cap_simps
                     | strengthen valid_queues_in_correct_ready_q valid_queues_ready_qs_distinct
                                  valid_sched_valid_queues )+)[1]
            apply (simp add: valid_tcb_state'_def pred_conj_def)
            apply (strengthen sch_act_wf_weak)
            apply (wp weak_sch_act_wf_lift_linear hoare_drop_imps)
           apply (wp gts_st_tcb_at)+
         apply (simp add: pred_conj_def cong: conj_cong)
         apply (wp hoare_TrueI)
        apply simp
        apply (wp weak_sch_act_wf_lift_linear set_ep_valid_objs' setEndpoint_valid_mdb')
       apply (clarsimp simp add: invs_def valid_state_def
                                 valid_pspace_def ep_redux_simps ep_redux_simps'
                                 st_tcb_at_tcb_at
                           cong: list.case_cong)
       apply (clarsimp simp: valid_ep_def)
       apply (drule(1) sym_refs_obj_atD[where P="\<lambda>ob. ob = e" for e])
       apply (clarsimp simp: st_tcb_at_refs_of_rev st_tcb_at_reply_cap_valid
                             st_tcb_at_caller_cap_null)
       apply (fastforce simp: st_tcb_def2 valid_sched_def valid_sched_action_def)
      subgoal by (auto simp: valid_ep'_def
                      split: list.split;
                  clarsimp simp: invs'_def valid_state'_def)
     apply wp+
   apply (clarsimp simp: ep_at_def2)+
  done
qed

lemmas setMessageInfo_typ_ats[wp] = typ_at_lifts [OF setMessageInfo_typ_at']

(* Annotation added by Simon Winwood (Thu Jul  1 20:54:41 2010) using taint-mode *)
declare tl_drop_1[simp]

crunch cancel_ipc
  for cur[wp]: "cur_tcb"
  (wp: crunch_wps simp: crunch_simps)

lemma valid_sched_weak_strg:
  "valid_sched s \<longrightarrow> weak_valid_sched_action s"
  by (simp add: valid_sched_def valid_sched_action_def)

lemma sendSignal_corres:
  "corres dc (einvs and ntfn_at ep) (invs' and ntfn_at' ep)
             (send_signal ep bg) (sendSignal ep bg)"
  apply (simp add: send_signal_def sendSignal_def Let_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getNotification_corres,
                where
                R  = "\<lambda>rv. einvs and ntfn_at ep and valid_ntfn rv and
                           ko_at (Structures_A.Notification rv) ep" and
                R' = "\<lambda>rv'. invs' and ntfn_at' ep and
                            valid_ntfn' rv' and ko_at' rv' ep"])
      defer
      apply (wp get_simple_ko_ko_at get_ntfn_ko')+
    apply (simp add: invs_valid_objs)+
  apply (case_tac "ntfn_obj ntfn")
    \<comment> \<open>IdleNtfn\<close>
    apply (clarsimp simp add: ntfn_relation_def)
    apply (case_tac "ntfnBoundTCB nTFN")
     apply clarsimp
     apply (rule corres_guard_imp[OF setNotification_corres])
       apply (clarsimp simp add: ntfn_relation_def)+
    apply (rule corres_guard_imp)
      apply (rule corres_split[OF getThreadState_corres])
        apply (rule corres_if)
          apply (fastforce simp: receive_blocked_def receiveBlocked_def
                                 thread_state_relation_def
                          split: Structures_A.thread_state.splits
                                 Structures_H.thread_state.splits)
         apply (rule corres_split[OF cancel_ipc_corres])
           apply (rule corres_split[OF setThreadState_corres])
              apply (clarsimp simp: thread_state_relation_def)
             apply (simp add: badgeRegister_def badge_register_def)
             apply (rule corres_split[OF asUser_setRegister_corres])
               apply (rule possibleSwitchTo_corres)
              apply wp
             apply (wp set_thread_state_runnable_weak_valid_sched_action sts_st_tcb_at'
                       sts_st_tcb' sts_valid_objs' hoare_disjI2
                       cancel_ipc_cte_wp_at_not_reply_state
                  | strengthen invs_vobjs_strgs invs_psp_aligned_strg valid_sched_weak_strg
                               valid_queues_in_correct_ready_q valid_queues_ready_qs_distinct
                               valid_sched_valid_queues
                  | simp add: valid_tcb_state_def)+
         apply (rule_tac Q'="\<lambda>rv. invs' and tcb_at' a" in hoare_strengthen_post)
          apply wp
         apply (fastforce simp: invs'_def valid_state'_def sch_act_wf_weak valid_tcb_state'_def)
        apply (rule setNotification_corres)
        apply (clarsimp simp add: ntfn_relation_def)
       apply (wp gts_wp gts_wp' | clarsimp)+
     apply (auto simp: valid_ntfn_def receive_blocked_def valid_sched_def invs_cur
                 elim: pred_tcb_weakenE
                intro: st_tcb_at_reply_cap_valid
                split: Structures_A.thread_state.splits)[1]
    apply (clarsimp simp: valid_ntfn'_def invs'_def valid_state'_def valid_pspace'_def sch_act_wf_weak)
   \<comment> \<open>WaitingNtfn\<close>
   apply (clarsimp simp add: ntfn_relation_def Let_def)
   apply (simp add: update_waiting_ntfn_def)
   apply (rename_tac list)
   apply (case_tac "tl list = []")
    \<comment> \<open>tl list = []\<close>
    apply (rule corres_guard_imp)
      apply (rule_tac F="list \<noteq> []" in corres_gen_asm)
      apply (simp add: list_case_helper split del: if_split)
      apply (rule corres_split[OF setNotification_corres])
         apply (simp add: ntfn_relation_def)
        apply (rule corres_split[OF setThreadState_corres])
           apply simp
          apply (simp add: badgeRegister_def badge_register_def)
          apply (rule corres_split[OF asUser_setRegister_corres])
            apply (rule possibleSwitchTo_corres)
           apply ((wp | simp)+)[1]
          apply (rule_tac Q'="\<lambda>_. (\<lambda>s. sch_act_wf (ksSchedulerAction s) s) and
                                 cur_tcb' and
                                 st_tcb_at' runnable' (hd list) and valid_objs' and
                                 sym_heap_sched_pointers and valid_sched_pointers and
                                 pspace_aligned' and pspace_distinct'"
                   in hoare_post_imp, clarsimp simp: pred_tcb_at' elim!: sch_act_wf_weak)
          apply (wp | simp)+
         apply (wp sts_st_tcb_at' set_thread_state_runnable_weak_valid_sched_action
              | simp)+
        apply (wp sts_st_tcb_at'_cases sts_valid_objs' setThreadState_st_tcb
             | simp)+
      apply (wp set_simple_ko_valid_objs set_ntfn_aligned' set_ntfn_valid_objs'
                hoare_vcg_disj_lift weak_sch_act_wf_lift_linear
           | simp add: valid_tcb_state_def valid_tcb_state'_def)+
     apply (fastforce simp: invs_def valid_state_def valid_ntfn_def
                            valid_pspace_def ntfn_queued_st_tcb_at valid_sched_def
                            valid_sched_action_def)
    apply (auto simp: valid_ntfn'_def )[1]
    apply (clarsimp simp: invs'_def valid_state'_def)

   \<comment> \<open>tl list \<noteq> []\<close>
   apply (rule corres_guard_imp)
     apply (rule_tac F="list \<noteq> []" in corres_gen_asm)
     apply (simp add: list_case_helper)
     apply (rule corres_split[OF setNotification_corres])
        apply (simp add: ntfn_relation_def split:list.splits)
       apply (rule corres_split[OF setThreadState_corres])
          apply simp
         apply (simp add: badgeRegister_def badge_register_def)
         apply (rule corres_split[OF asUser_setRegister_corres])
           apply (rule possibleSwitchTo_corres)
          apply (wp cur_tcb_lift | simp)+
        apply (wp sts_st_tcb_at' set_thread_state_runnable_weak_valid_sched_action
             | simp)+
       apply (wpsimp wp: sts_st_tcb_at'_cases sts_valid_objs' setThreadState_st_tcb)
     apply (wp set_ntfn_aligned' set_simple_ko_valid_objs set_ntfn_valid_objs'
               hoare_vcg_disj_lift weak_sch_act_wf_lift_linear
          | simp add: valid_tcb_state_def valid_tcb_state'_def)+
    apply (fastforce simp: invs_def valid_state_def valid_ntfn_def
                           valid_pspace_def neq_Nil_conv
                           ntfn_queued_st_tcb_at valid_sched_def valid_sched_action_def
                    split: option.splits)
   apply (auto simp: valid_ntfn'_def neq_Nil_conv invs'_def valid_state'_def
                     weak_sch_act_wf_def
              split: option.splits)[1]
  \<comment> \<open>ActiveNtfn\<close>
  apply (clarsimp simp add: ntfn_relation_def)
  apply (rule corres_guard_imp)
    apply (rule setNotification_corres)
    apply (simp add: ntfn_relation_def combine_ntfn_badges_def
                     combine_ntfn_msgs_def)
   apply (simp add: invs_def valid_state_def valid_ntfn_def)
  apply (simp add: invs'_def valid_state'_def valid_ntfn'_def)
  done

lemma valid_Running'[simp]:
  "valid_tcb_state' Running = \<top>"
  by (rule ext, simp add: valid_tcb_state'_def)

crunch setMRs
  for typ'[wp]: "\<lambda>s. P (typ_at' T p s)"
   (wp: crunch_wps simp: zipWithM_x_mapM)

lemma possibleSwitchTo_sch_act[wp]:
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s \<and> st_tcb_at' runnable' t s\<rbrace>
     possibleSwitchTo t
   \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp add: possibleSwitchTo_def curDomain_def bitmap_fun_defs)
  apply (wp hoare_weak_lift_imp threadSet_sch_act setQueue_sch_act threadGet_wp
       | simp add: unless_def | wpc)+
  apply (auto simp: obj_at'_def projectKOs tcb_in_cur_domain'_def)
  done

crunch possibleSwitchTo
  for st_refs_of'[wp]: "\<lambda>s. P (state_refs_of' s)"
  (wp: crunch_wps)

crunch possibleSwitchTo
  for cap_to'[wp]: "ex_nonz_cap_to' p"
  (wp: crunch_wps)
crunch possibleSwitchTo
  for objs'[wp]: valid_objs'
  (wp: crunch_wps)
crunch possibleSwitchTo
  for ct[wp]: cur_tcb'
  (wp: cur_tcb_lift crunch_wps)

lemma possibleSwitchTo_iflive[wp]:
  "\<lbrace>if_live_then_nonz_cap' and ex_nonz_cap_to' t and (\<lambda>s. sch_act_wf (ksSchedulerAction s) s)
    and pspace_aligned' and pspace_distinct'\<rbrace>
   possibleSwitchTo t
   \<lbrace>\<lambda>_. if_live_then_nonz_cap'\<rbrace>"
  apply (simp add: possibleSwitchTo_def curDomain_def)
  apply (wp | wpc | simp)+
      apply (simp only: imp_conv_disj, wp hoare_vcg_all_lift hoare_vcg_disj_lift)
    apply (wp threadGet_wp)+
  apply (auto simp: obj_at'_def)
  done

crunch possibleSwitchTo
  for ifunsafe[wp]: if_unsafe_then_cap'
  (wp: crunch_wps)
crunch possibleSwitchTo
  for idle'[wp]: valid_idle'
  (wp: crunch_wps)
crunch possibleSwitchTo
  for global_refs'[wp]: valid_global_refs'
  (wp: crunch_wps)
crunch possibleSwitchTo
  for arch_state'[wp]: valid_arch_state'
  (wp: crunch_wps)
crunch possibleSwitchTo
  for irq_node'[wp]: "\<lambda>s. P (irq_node' s)"
  (wp: crunch_wps)
crunch possibleSwitchTo
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps)
crunch possibleSwitchTo
  for irq_handlers'[wp]: valid_irq_handlers'
  (simp: unless_def tcb_cte_cases_def cteSizeBits_def wp: crunch_wps)
crunch possibleSwitchTo
  for irq_states'[wp]: valid_irq_states'
  (wp: crunch_wps)
crunch sendSignal
  for ct'[wp]: "\<lambda>s. P (ksCurThread s)"
  (wp: crunch_wps simp: crunch_simps o_def)
crunch sendSignal
  for it'[wp]: "\<lambda>s. P (ksIdleThread s)"
  (wp: crunch_wps simp: crunch_simps)

crunch setBoundNotification
  for irqs_masked'[wp]: "irqs_masked'"
  (wp: irqs_masked_lift)

crunch sendSignal
  for irqs_masked'[wp]: "irqs_masked'"
  (wp: crunch_wps getObject_inv loadObject_default_inv
   simp: crunch_simps unless_def o_def
   rule: irqs_masked_lift)

lemma ct_in_state_activatable_imp_simple'[simp]:
  "ct_in_state' activatable' s \<Longrightarrow> ct_in_state' simple' s"
  apply (simp add: ct_in_state'_def)
  apply (erule pred_tcb'_weakenE)
  apply (case_tac st; simp)
  done

lemma setThreadState_nonqueued_state_update:
  "\<lbrace>\<lambda>s. invs' s \<and> st_tcb_at' simple' t s
               \<and> st \<in> {Inactive, Running, Restart, IdleThreadState}
               \<and> (st \<noteq> Inactive \<longrightarrow> ex_nonz_cap_to' t s)
               \<and> (t = ksIdleThread s \<longrightarrow> idle' st)
               \<and> (\<not> runnable' st \<longrightarrow> sch_act_simple s)\<rbrace>
   setThreadState st t
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def)
  apply (rule hoare_pre, wp valid_irq_node_lift setThreadState_ct_not_inQ)
  apply (clarsimp simp: pred_tcb_at')
  apply (rule conjI, fastforce simp: valid_tcb_state'_def)
  apply (drule simple_st_tcb_at_state_refs_ofD')
  apply (drule bound_tcb_at_state_refs_ofD')
  apply (rule conjI)
   apply clarsimp
   apply (erule delta_sym_refs)
    apply (fastforce split: if_split_asm)
   apply (fastforce simp: symreftype_inverse' tcb_bound_refs'_def split: if_split_asm)
  apply fastforce
  done

lemma cteDeleteOne_reply_cap_to'[wp]:
  "\<lbrace>ex_nonz_cap_to' p and
    cte_wp_at' (\<lambda>c. isReplyCap (cteCap c)) slot\<rbrace>
   cteDeleteOne slot
   \<lbrace>\<lambda>rv. ex_nonz_cap_to' p\<rbrace>"
  apply (simp add: cteDeleteOne_def ex_nonz_cap_to'_def unless_def)
  apply (rule bind_wp [OF _ getCTE_sp])
  apply (rule hoare_assume_pre)
  apply (subgoal_tac "isReplyCap (cteCap cte)")
   apply (wp hoare_vcg_ex_lift emptySlot_cte_wp_cap_other isFinalCapability_inv
        | clarsimp simp: finaliseCap_def isCap_simps
        | wp (once) hoare_drop_imps)+
   apply (fastforce simp: cte_wp_at_ctes_of)
  apply (clarsimp simp: cte_wp_at_ctes_of isCap_simps)
  done

crunch setupCallerCap, possibleSwitchTo, asUser, doIPCTransfer
  for vms'[wp]: "valid_machine_state'"
  (wp: crunch_wps simp: zipWithM_x_mapM_x)

crunch cancelSignal
  for nonz_cap_to'[wp]: "ex_nonz_cap_to' p"
  (wp: crunch_wps simp: crunch_simps)

lemma cancelIPC_nonz_cap_to'[wp]:
  "\<lbrace>ex_nonz_cap_to' p\<rbrace> cancelIPC t \<lbrace>\<lambda>rv. ex_nonz_cap_to' p\<rbrace>"
  apply (simp add: cancelIPC_def getThreadReplySlot_def Let_def
                   capHasProperty_def)
  apply (wp threadSet_cap_to'
       | wpc
       | simp
       | clarsimp elim!: cte_wp_at_weakenE'
       | rule hoare_post_imp[where Q'="\<lambda>rv. ex_nonz_cap_to' p"])+
  done


crunch activateIdleThread, getThreadReplySlot, isFinalCapability
  for nosch[wp]: "\<lambda>s. P (ksSchedulerAction s)"
  (simp: Let_def)

crunch setupCallerCap, asUser, setMRs, doIPCTransfer, possibleSwitchTo
  for pspace_domain_valid[wp]: "pspace_domain_valid"
  (wp: crunch_wps simp: zipWithM_x_mapM_x)

crunch setupCallerCap, doIPCTransfer, possibleSwitchTo
  for ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"
  (wp: crunch_wps simp: zipWithM_x_mapM)

lemma setThreadState_not_rct[wp]:
  "\<lbrace>\<lambda>s. ksSchedulerAction s \<noteq> ResumeCurrentThread \<rbrace>
   setThreadState st t
   \<lbrace>\<lambda>_ s. ksSchedulerAction s \<noteq> ResumeCurrentThread \<rbrace>"
  apply (simp add: setThreadState_def)
  apply (wp)
       apply (rule hoare_post_imp [OF _ rescheduleRequired_notresume], simp)
      apply (simp)
      apply (wp)+
  apply simp
  done

lemma cancelAllIPC_not_rct[wp]:
  "\<lbrace>\<lambda>s. ksSchedulerAction s \<noteq> ResumeCurrentThread \<rbrace>
   cancelAllIPC epptr
   \<lbrace>\<lambda>_ s. ksSchedulerAction s \<noteq> ResumeCurrentThread \<rbrace>"
  apply (simp add: cancelAllIPC_def)
  apply (wp | wpc)+
         apply (rule hoare_post_imp [OF _ rescheduleRequired_notresume], simp)
        apply simp
        apply (rule mapM_x_wp_inv)
        apply (wp)+
       apply (rule hoare_post_imp [OF _ rescheduleRequired_notresume], simp)
      apply simp
      apply (rule mapM_x_wp_inv)
      apply (wpsimp wp: hoare_vcg_all_lift hoare_drop_imp)+
  done

lemma cancelAllSignals_not_rct[wp]:
  "\<lbrace>\<lambda>s. ksSchedulerAction s \<noteq> ResumeCurrentThread \<rbrace>
   cancelAllSignals epptr
   \<lbrace>\<lambda>_ s. ksSchedulerAction s \<noteq> ResumeCurrentThread \<rbrace>"
  apply (simp add: cancelAllSignals_def)
  apply (wp | wpc)+
       apply (rule hoare_post_imp [OF _ rescheduleRequired_notresume], simp)
      apply simp
      apply (rule mapM_x_wp_inv)
      apply (wpsimp wp: hoare_vcg_all_lift hoare_drop_imp)+
  done

crunch finaliseCapTrue_standin
  for not_rct[wp]: "\<lambda>s. ksSchedulerAction s \<noteq> ResumeCurrentThread"
(simp: Let_def)

declare setEndpoint_ct' [wp]

lemma cancelIPC_ResumeCurrentThread_imp_notct[wp]:
  "\<lbrace>\<lambda>s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t'\<rbrace>
   cancelIPC t
   \<lbrace>\<lambda>_ s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t'\<rbrace>"
  (is "\<lbrace>?PRE t'\<rbrace> _ \<lbrace>_\<rbrace>")
proof -
  have aipc: "\<And>t t' ntfn.
    \<lbrace>\<lambda>s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t'\<rbrace>
    cancelSignal t ntfn
    \<lbrace>\<lambda>_ s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t'\<rbrace>"
    apply (simp add: cancelSignal_def)
    apply (wp)[1]
        apply (wp hoare_convert_imp)+
        apply (rule_tac P="\<lambda>s. ksSchedulerAction s \<noteq> ResumeCurrentThread"
                 in hoare_weaken_pre)
          apply (wpc)
           apply (wp | simp)+
       apply (wpc, wp+)
     apply (rule_tac Q'="\<lambda>_. ?PRE t'" in hoare_post_imp, clarsimp)
     apply (wp)
    apply simp
    done
  have cdo: "\<And>t t' slot.
    \<lbrace>\<lambda>s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t'\<rbrace>
    cteDeleteOne slot
    \<lbrace>\<lambda>_ s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t'\<rbrace>"
    apply (simp add: cteDeleteOne_def unless_def split_def)
    apply (wp)
        apply (wp hoare_convert_imp)[1]
       apply (wp)
      apply (rule_tac Q'="\<lambda>_. ?PRE t'" in hoare_post_imp, clarsimp)
      apply (wp hoare_convert_imp | simp)+
     done
  show ?thesis
  apply (simp add: cancelIPC_def Let_def)
  apply (wp, wpc)
          prefer 4 \<comment> \<open>state = Running\<close>
          apply wp
         prefer 7 \<comment> \<open>state = Restart\<close>
         apply wp
        apply (wp)+
           apply (wp hoare_convert_imp)[1]
          apply (wpc, wp+)
        apply (rule_tac Q'="\<lambda>_. ?PRE t'" in hoare_post_imp, clarsimp)
        apply (wp cdo)+
         apply (rule_tac Q'="\<lambda>_. ?PRE t'" in hoare_post_imp, clarsimp)
         apply ((wp aipc hoare_convert_imp)+)[6]
    apply (wp)
       apply (wp hoare_convert_imp)[1]
      apply (wpc, wp+)
    apply (rule_tac Q'="\<lambda>_. ?PRE t'" in hoare_post_imp, clarsimp)
    apply (wp)
   apply (rule_tac Q'="\<lambda>_. ?PRE t'" in hoare_post_imp, clarsimp)
   apply (wp)
  apply simp
  done
qed

crunch setMRs
  for nosch[wp]: "\<lambda>s. P (ksSchedulerAction s)"

lemma sai_invs'[wp]:
  "\<lbrace>invs' and ex_nonz_cap_to' ntfnptr\<rbrace>
     sendSignal ntfnptr badge \<lbrace>\<lambda>y. invs'\<rbrace>"
  unfolding sendSignal_def
  apply (rule bind_wp[OF _ get_ntfn_sp'])
  apply (case_tac "ntfnObj nTFN", simp_all)
    prefer 3
    apply (rename_tac list)
    apply (case_tac list,
           simp_all split del: if_split
                          add: setMessageInfo_def)[1]
    apply (wp hoare_convert_imp [OF asUser_nosch]
              hoare_convert_imp [OF setMRs_sch_act])+
     apply (clarsimp simp:conj_comms)
     apply (simp add: invs'_def valid_state'_def)
     apply (wp valid_irq_node_lift sts_valid_objs' setThreadState_ct_not_inQ
               set_ntfn_valid_objs' cur_tcb_lift sts_st_tcb'
               hoare_convert_imp [OF setNotification_nosch]
           | simp split del: if_split)+

    apply (intro conjI[rotated];
      (solves \<open>clarsimp simp: invs'_def valid_state'_def valid_pspace'_def\<close>)?)
           apply (clarsimp simp: invs'_def valid_state'_def split del: if_split)
           apply (drule(1) ct_not_in_ntfnQueue, simp+)
          apply clarsimp
          apply (frule ko_at_valid_objs', clarsimp)
           apply (simp add: projectKOs)
          apply (clarsimp simp: valid_obj'_def valid_ntfn'_def
                         split: list.splits)
         apply (clarsimp simp: invs'_def valid_state'_def)
         apply (clarsimp simp: st_tcb_at_refs_of_rev' valid_idle'_def pred_tcb_at'_def idle_tcb'_def
                        dest!: sym_refs_ko_atD' sym_refs_st_tcb_atD' sym_refs_obj_atD'
                        split: list.splits)
        apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def)
        apply (frule(1) ko_at_valid_objs')
         apply (simp add: projectKOs)
        apply (clarsimp simp: valid_obj'_def valid_ntfn'_def
                    split: list.splits option.splits)
       apply (clarsimp elim!: if_live_then_nonz_capE' simp:invs'_def valid_state'_def)
       apply (drule(1) sym_refs_ko_atD')
       apply (clarsimp elim!: ko_wp_at'_weakenE
                   intro!: refs_of_live')
      apply (clarsimp split del: if_split)+
      apply (frule ko_at_valid_objs', clarsimp)
       apply (simp add: projectKOs)
      apply (clarsimp simp: valid_obj'_def valid_ntfn'_def split del: if_split)
      apply (frule invs_sym')
      apply (drule(1) sym_refs_obj_atD')
      apply (clarsimp split del: if_split cong: if_cong
                         simp: st_tcb_at_refs_of_rev' ep_redux_simps' ntfn_bound_refs'_def)
      apply (frule st_tcb_at_state_refs_ofD')
      apply (erule delta_sym_refs)
       apply (fastforce simp: split: if_split_asm)
      apply (fastforce simp: tcb_bound_refs'_def set_eq_subset symreftype_inverse'
                      split: if_split_asm)
     apply (clarsimp simp:invs'_def)
     apply (frule ko_at_valid_objs')
       apply (clarsimp simp: valid_pspace'_def valid_state'_def)
      apply (simp add: projectKOs)
     apply (clarsimp simp: valid_obj'_def valid_ntfn'_def split del: if_split)
    apply (clarsimp simp:invs'_def valid_state'_def valid_pspace'_def)
    apply (frule(1) ko_at_valid_objs')
     apply (simp add: projectKOs)
    apply (clarsimp simp: valid_obj'_def valid_ntfn'_def
                  split: list.splits option.splits)
   apply (case_tac "ntfnBoundTCB nTFN", simp_all)
    apply (wp set_ntfn_minor_invs')
    apply (fastforce simp: valid_ntfn'_def invs'_def valid_state'_def
                    elim!: obj_at'_weakenE
                    dest!: global'_no_ex_cap)
   apply (wp add: hoare_convert_imp [OF asUser_nosch]
             hoare_convert_imp [OF setMRs_sch_act]
             setThreadState_nonqueued_state_update sts_st_tcb'
             del: cancelIPC_simple)
     apply (clarsimp | wp cancelIPC_ct')+
    apply (wp set_ntfn_minor_invs' gts_wp' | clarsimp)+
   apply (frule pred_tcb_at')
   by (wp set_ntfn_minor_invs'
        | rule conjI
        | clarsimp elim!: st_tcb_ex_cap''
        | fastforce simp: receiveBlocked_def projectKOs pred_tcb_at'_def obj_at'_def
                   dest!: invs_rct_ct_activatable'
                   split: thread_state.splits
        | fastforce simp: invs'_def valid_state'_def receiveBlocked_def projectKOs
                          valid_obj'_def valid_ntfn'_def
                   split: thread_state.splits
                   dest!: global'_no_ex_cap st_tcb_ex_cap'' ko_at_valid_objs')+

lemma replyFromKernel_corres:
  "corres dc (tcb_at t and invs) (invs')
             (reply_from_kernel t r) (replyFromKernel t r)"
  apply (case_tac r)
  apply (clarsimp simp: replyFromKernel_def reply_from_kernel_def
                        badge_register_def badgeRegister_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqr[OF lookupIPCBuffer_corres])
      apply (rule corres_split[OF asUser_setRegister_corres])
        apply (rule corres_split_eqr[OF setMRs_corres])
           apply clarsimp
          apply (rule setMessageInfo_corres)
          apply (wp hoare_case_option_wp hoare_valid_ipc_buffer_ptr_typ_at'
                 | clarsimp simp: invs_distinct invs_psp_aligned)+
  apply fastforce
  done

lemma rfk_invs':
  "\<lbrace>invs' and tcb_at' t\<rbrace> replyFromKernel t r \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: replyFromKernel_def)
  apply (cases r)
   apply (wp | clarsimp)+
  done

crunch replyFromKernel
  for nosch[wp]: "\<lambda>s. P (ksSchedulerAction s)"

lemma completeSignal_corres:
  "corres dc (ntfn_at ntfnptr and tcb_at tcb and pspace_aligned and valid_objs and pspace_distinct)
             (ntfn_at' ntfnptr and tcb_at' tcb and valid_pspace' and obj_at' isActive ntfnptr)
             (complete_signal ntfnptr tcb) (completeSignal ntfnptr tcb)"
  apply (simp add: complete_signal_def completeSignal_def)
  apply (rule corres_guard_imp)
    apply (rule_tac R'="\<lambda>ntfn. ntfn_at' ntfnptr and tcb_at' tcb and valid_pspace'
                         and valid_ntfn' ntfn and (\<lambda>_. isActive ntfn)"
                                in corres_split[OF getNotification_corres])
      apply (rule corres_gen_asm2)
      apply (case_tac "ntfn_obj rv")
        apply (clarsimp simp: ntfn_relation_def isActive_def
                       split: ntfn.splits Structures_H.notification.splits)+
      apply (rule corres_guard2_imp)
       apply (simp add: badgeRegister_def badge_register_def)
       apply (rule corres_split[OF asUser_setRegister_corres setNotification_corres])
         apply (clarsimp simp: ntfn_relation_def)
        apply (wp set_simple_ko_valid_objs get_simple_ko_wp getNotification_wp | clarsimp simp: valid_ntfn'_def)+
  apply (clarsimp simp: valid_pspace'_def)
  apply (frule_tac P="(\<lambda>k. k = ntfn)" in obj_at_valid_objs', assumption)
  apply (clarsimp simp: valid_obj'_def valid_ntfn'_def obj_at'_def)
  done


lemma doNBRecvFailedTransfer_corres:
  "corres dc (tcb_at thread and pspace_aligned and pspace_distinct) \<top>
             (do_nbrecv_failed_transfer thread)
             (doNBRecvFailedTransfer thread)"
  unfolding do_nbrecv_failed_transfer_def doNBRecvFailedTransfer_def
  by (simp add: badgeRegister_def badge_register_def, rule asUser_setRegister_corres)

lemma receiveIPC_corres:
  assumes "is_ep_cap cap" and "cap_relation cap cap'"
  shows "
   corres dc (einvs and valid_sched and tcb_at thread and valid_cap cap and ex_nonz_cap_to thread
              and cte_wp_at (\<lambda>c. c = cap.NullCap) (thread, tcb_cnode_index 3))
             (invs' and tcb_at' thread and valid_cap' cap')
             (receive_ipc thread cap isBlocking) (receiveIPC thread cap' isBlocking)"
  apply (insert assms)
  apply (simp add: receive_ipc_def receiveIPC_def
              split del: if_split)
  apply (case_tac cap, simp_all add: isEndpointCap_def)
  apply (rename_tac word1 word2 right)
  apply clarsimp
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getEndpoint_corres])
      apply (rule corres_guard_imp)
        apply (rule corres_split[OF getBoundNotification_corres])
          apply (rule_tac r'="ntfn_relation" in corres_split)
             apply (rule corres_option_split[rotated 2])
               apply (rule getNotification_corres)
              apply clarsimp
             apply (rule corres_trivial, simp add: ntfn_relation_def default_notification_def
                                                   default_ntfn_def)
            apply (rule corres_if)
              apply (clarsimp simp: ntfn_relation_def Ipc_A.isActive_def Endpoint_H.isActive_def
                             split: Structures_A.ntfn.splits Structures_H.notification.splits)
             apply clarsimp
             apply (rule completeSignal_corres)
            apply (rule_tac P="einvs and valid_sched and tcb_at thread and
                                      ep_at word1 and valid_ep ep and
                                      obj_at (\<lambda>k. k = Endpoint ep) word1
                                      and cte_wp_at (\<lambda>c. c = cap.NullCap) (thread, tcb_cnode_index 3)
                                      and ex_nonz_cap_to thread" and
                                P'="invs' and tcb_at' thread and ep_at' word1 and
                                          valid_ep' epa"
                                in corres_inst)
            apply (case_tac ep)
              \<comment> \<open>IdleEP\<close>
              apply (simp add: ep_relation_def)
              apply (rule corres_guard_imp)
                apply (case_tac isBlocking; simp)
                 apply (rule corres_split[OF setThreadState_corres])
                    apply simp
                   apply (rule setEndpoint_corres)
                   apply (simp add: ep_relation_def)
                  apply wp+
                apply (rule corres_guard_imp, rule doNBRecvFailedTransfer_corres, simp)
                apply simp
               apply (clarsimp simp add: invs_def valid_state_def valid_pspace_def
              valid_tcb_state_def st_tcb_at_tcb_at)
              apply auto[1]
             \<comment> \<open>SendEP\<close>
             apply (simp add: ep_relation_def)
             apply (rename_tac list)
             apply (rule_tac F="list \<noteq> []" in corres_req)
              apply (clarsimp simp: valid_ep_def)
             apply (case_tac list, simp_all split del: if_split)[1]
             apply (rule corres_guard_imp)
               apply (rule corres_split[OF setEndpoint_corres])
                  apply (case_tac lista, simp_all add: ep_relation_def)[1]
                 apply (rule corres_split[OF getThreadState_corres])
                   apply (rule_tac
                            F="\<exists>data.
                                sender_state =
                                Structures_A.thread_state.BlockedOnSend word1 data"
                            in corres_gen_asm)
                   apply (clarsimp simp: isSend_def case_bool_If
                                         case_option_If if3_fold
                              split del: if_split cong: if_cong)
                   apply (rule corres_split[OF doIPCTransfer_corres])
                     apply (simp split del: if_split cong: if_cong)
                     apply (fold dc_def)[1]
                     apply (rule_tac P="valid_objs and valid_mdb and valid_list and valid_arch_state
                                             and valid_sched
                                             and cur_tcb
                                             and valid_reply_caps
                                             and pspace_aligned and pspace_distinct
                                             and st_tcb_at (Not \<circ> awaiting_reply) a
                                             and st_tcb_at (Not \<circ> halted) a
                                             and tcb_at thread and valid_reply_masters
                                             and cte_wp_at (\<lambda>c. c = cap.NullCap)
                                                           (thread, tcb_cnode_index 3)"
                                 and P'="tcb_at' a and tcb_at' thread and cur_tcb'
                                                   and valid_pspace'
                                                   and valid_objs'
                                             and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s)
                                             and sym_heap_sched_pointers and valid_sched_pointers
                                             and pspace_aligned' and pspace_distinct'"
                                  in corres_guard_imp [OF corres_if])
                         apply (simp add: fault_rel_optionation_def)
                        apply (rule corres_if2 [OF _ setupCallerCap_corres setThreadState_corres])
                         apply simp
                        apply simp
                       apply (rule corres_split[OF setThreadState_corres])
                          apply simp
                         apply (rule possibleSwitchTo_corres)
                        apply (wpsimp wp: sts_st_tcb_at' set_thread_state_runnable_weak_valid_sched_action)+
                       apply (wp sts_st_tcb_at'_cases sts_valid_objs' setThreadState_st_tcb
                            | simp)+
                      apply (fastforce simp: st_tcb_at_tcb_at st_tcb_def2 valid_sched_def
                                             valid_sched_action_def)
                     apply (clarsimp split: if_split_asm)
                    apply (clarsimp | wp do_ipc_transfer_tcb_caps do_ipc_transfer_valid_arch)+
                   apply (rule_tac Q'="\<lambda>_ s. sch_act_wf (ksSchedulerAction s) s
                                            \<and> sym_heap_sched_pointers s \<and> valid_sched_pointers s
                                            \<and> pspace_aligned' s \<and> pspace_distinct' s"
                                in hoare_post_imp)
                    apply (fastforce elim: sch_act_wf_weak)
                   apply (wp sts_st_tcb' gts_st_tcb_at | simp)+
                apply (simp cong: list.case_cong)
                apply wp
               apply simp
               apply (wp weak_sch_act_wf_lift_linear setEndpoint_valid_mdb' set_ep_valid_objs')
              apply (clarsimp split: list.split)
              apply (clarsimp simp add: invs_def valid_state_def st_tcb_at_tcb_at)
              apply (clarsimp simp add: valid_ep_def valid_pspace_def)
              apply (drule(1) sym_refs_obj_atD[where P="\<lambda>ko. ko = Endpoint e" for e])
              apply (fastforce simp: st_tcb_at_refs_of_rev elim: st_tcb_weakenE)
             apply (auto simp: valid_ep'_def invs'_def valid_state'_def split: list.split)[1]
            \<comment> \<open>RecvEP\<close>
            apply (simp add: ep_relation_def)
            apply (rule_tac corres_guard_imp)
              apply (case_tac isBlocking; simp)
               apply (rule corres_split[OF setThreadState_corres])
                  apply simp
                 apply (rule setEndpoint_corres)
                 apply (simp add: ep_relation_def)
                apply wp+
              apply (rule corres_guard_imp, rule doNBRecvFailedTransfer_corres, simp)
              apply simp
             apply (clarsimp simp: valid_tcb_state_def invs_distinct)
            apply (clarsimp simp add: valid_tcb_state'_def)
           apply (wp get_simple_ko_wp[where f=Notification] getNotification_wp gbn_wp gbn_wp'
                      hoare_vcg_all_lift hoare_vcg_imp_lift hoare_vcg_if_lift
                    | wpc | simp add: ep_at_def2[symmetric, simplified] | clarsimp)+
   apply (clarsimp simp: valid_cap_def invs_psp_aligned invs_valid_objs pred_tcb_at_def
                         valid_obj_def valid_tcb_def valid_bound_ntfn_def invs_distinct
                  dest!: invs_valid_objs
                  elim!: obj_at_valid_objsE
                  split: option.splits)
  apply clarsimp
  apply (auto simp: valid_cap'_def invs_valid_pspace' valid_obj'_def valid_tcb'_def
                    valid_bound_ntfn'_def obj_at'_def pred_tcb_at'_def
             dest!: invs_valid_objs' obj_at_valid_objs'
             split: option.splits)[1]
  done

lemma receiveSignal_corres:
  "\<lbrakk> is_ntfn_cap cap; cap_relation cap cap' \<rbrakk> \<Longrightarrow>
  corres dc (invs and st_tcb_at active thread and valid_cap cap and ex_nonz_cap_to thread)
            (invs' and tcb_at' thread and valid_cap' cap')
            (receive_signal thread cap isBlocking) (receiveSignal thread cap' isBlocking)"
  apply (simp add: receive_signal_def receiveSignal_def)
  apply (case_tac cap, simp_all add: isEndpointCap_def)
  apply (rename_tac word1 word2 rights)
  apply (rule corres_guard_imp)
    apply (rule_tac R="\<lambda>rv. invs and tcb_at thread and st_tcb_at active thread and
                            ntfn_at word1 and ex_nonz_cap_to thread and
                            valid_ntfn rv and
                            obj_at (\<lambda>k. k = Notification rv) word1" and
                            R'="\<lambda>rv'. invs' and tcb_at' thread and ntfn_at' word1 and
                            valid_ntfn' rv'"
                         in corres_split[OF getNotification_corres])
      apply clarsimp
      apply (case_tac "ntfn_obj rv")
        \<comment> \<open>IdleNtfn\<close>
        apply (simp add: ntfn_relation_def)
        apply (rule corres_guard_imp)
          apply (case_tac isBlocking; simp)
           apply (rule corres_split[OF setThreadState_corres])
              apply simp
             apply (rule setNotification_corres)
             apply (simp add: ntfn_relation_def)
            apply wp+
          apply (rule corres_guard_imp, rule doNBRecvFailedTransfer_corres; simp)
         apply (clarsimp simp: invs_distinct)
        apply simp
       \<comment> \<open>WaitingNtfn\<close>
       apply (simp add: ntfn_relation_def)
       apply (rule corres_guard_imp)
         apply (case_tac isBlocking; simp)
          apply (rule corres_split[OF setThreadState_corres])
             apply simp
            apply (rule setNotification_corres)
            apply (simp add: ntfn_relation_def)
           apply wp+
         apply (rule corres_guard_imp)
           apply (rule doNBRecvFailedTransfer_corres; simp)
          apply (clarsimp simp: invs_distinct)+
       \<comment> \<open>ActiveNtfn\<close>
      apply (simp add: ntfn_relation_def)
      apply (rule corres_guard_imp)
        apply (simp add: badgeRegister_def badge_register_def)
        apply (rule corres_split[OF asUser_setRegister_corres])
          apply (rule setNotification_corres)
          apply (simp add: ntfn_relation_def)
         apply wp+
       apply (fastforce simp: invs_def valid_state_def valid_pspace_def
                       elim!: st_tcb_weakenE)
      apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def)
     apply wp+
   apply (clarsimp simp add: ntfn_at_def2 valid_cap_def st_tcb_at_tcb_at)
  apply (clarsimp simp add: valid_cap'_def)
  done

lemma tg_sp':
  "\<lbrace>P\<rbrace> threadGet f p \<lbrace>\<lambda>t. obj_at' (\<lambda>t'. f t' = t) p and P\<rbrace>"
  including no_pre
  apply (simp add: threadGet_def)
  apply wp
  apply (rule hoare_strengthen_post)
   apply (rule getObject_tcb_sp)
  apply clarsimp
  apply (erule obj_at'_weakenE)
  apply simp
  done

declare lookup_cap_valid' [wp]

lemma sendFaultIPC_corres:
  "valid_fault f \<Longrightarrow> fr f f' \<Longrightarrow>
  corres (fr \<oplus> dc)
         (einvs and st_tcb_at active thread and ex_nonz_cap_to thread)
         (invs' and sch_act_not thread and tcb_at' thread)
         (send_fault_ipc thread f) (sendFaultIPC thread f')"
  apply (simp add: send_fault_ipc_def sendFaultIPC_def
                   liftE_bindE Let_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[where r'="\<lambda>fh fh'. fh = to_bl fh'"])
       apply (rule threadGet_corres)
       apply (simp add: tcb_relation_def)
      apply simp
      apply (rule corres_splitEE)
         apply (rule corres_cap_fault)
         apply (rule lookup_cap_corres, rule refl)
        apply (rule_tac P="einvs and st_tcb_at active thread
                                and valid_cap handler_cap and ex_nonz_cap_to thread"
                    and P'="invs' and tcb_at' thread and sch_act_not thread
                                  and valid_cap' handlerCap"
                    in corres_inst)
        apply (case_tac handler_cap,
               simp_all add: isCap_defs lookup_failure_map_def
                             case_bool_If If_rearrage
                  split del: if_split cong: if_cong)[1]
         apply (rule corres_guard_imp)
           apply (rule corres_if2 [OF refl])
            apply (simp add: dc_def[symmetric])
            apply (rule corres_split[OF threadset_corres sendIPC_corres], simp_all)[1]
               apply (simp add: tcb_relation_def fault_rel_optionation_def inQ_def)+
             apply (wp thread_set_invs_trivial thread_set_no_change_tcb_state
                       thread_set_typ_at ep_at_typ_at ex_nonz_cap_to_pres
                       thread_set_cte_wp_at_trivial thread_set_not_state_valid_sched
                  | simp add: tcb_cap_cases_def)+
            apply ((wp threadSet_invs_trivial threadSet_tcb'
                  | simp add: tcb_cte_cases_def
                  | wp (once) sch_act_sane_lift)+)[1]
           apply (rule corres_trivial, simp add: lookup_failure_map_def)
          apply (clarsimp simp: st_tcb_at_tcb_at split: if_split)
          apply (clarsimp simp: valid_cap_def invs_distinct)
         apply (clarsimp simp: valid_cap'_def inQ_def)
        apply auto[1]
        apply (clarsimp simp: lookup_failure_map_def)
       apply wp+
   apply (fastforce elim: st_tcb_at_tcb_at)
  apply fastforce
  done

lemma gets_the_noop_corres:
  assumes P: "\<And>s. P s \<Longrightarrow> f s \<noteq> None"
  shows "corres dc P P' (gets_the f) (return x)"
  apply (clarsimp simp: corres_underlying_def gets_the_def
                        return_def gets_def bind_def get_def)
  apply (clarsimp simp: assert_opt_def return_def dest!: P)
  done

lemma handleDoubleFault_corres:
  "corres dc (tcb_at thread and pspace_aligned and pspace_distinct)
             \<top>
             (handle_double_fault thread f ft)
             (handleDoubleFault thread f' ft')"
  apply (rule corres_cross_over_guard[where Q="tcb_at' thread"])
   apply (fastforce intro!: tcb_at_cross)
  apply (simp add: handle_double_fault_def handleDoubleFault_def)
  apply (rule corres_guard_imp)
    apply (subst bind_return [symmetric],
           rule corres_split[OF setThreadState_corres])
       apply simp
      apply (rule corres_noop2)
         apply (simp add: exs_valid_def return_def)
        apply (rule hoare_eq_P)
        apply wp
        apply (rule asUser_inv)
        apply (rule getRestartPC_inv)
       apply (wp no_fail_getRestartPC)+
   apply (wp|simp)+
  done

crunch sendFaultIPC
  for tcb'[wp]: "tcb_at' t" (wp: crunch_wps)

crunch receiveIPC
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps)

lemmas receiveIPC_typ_ats[wp] = typ_at_lifts [OF receiveIPC_typ_at']

crunch receiveSignal
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps)

lemmas receiveAIPC_typ_ats[wp] = typ_at_lifts [OF receiveSignal_typ_at']

crunch setupCallerCap
  for aligned'[wp]: "pspace_aligned'"
  (wp: crunch_wps)
crunch setupCallerCap
  for distinct'[wp]: "pspace_distinct'"
  (wp: crunch_wps)
crunch setupCallerCap
  for cur_tcb[wp]: "cur_tcb'"
  (wp: crunch_wps)

lemma setupCallerCap_state_refs_of[wp]:
  "\<lbrace>\<lambda>s. P ((state_refs_of' s) (sender := {r \<in> state_refs_of' s sender. snd r = TCBBound}))\<rbrace>
     setupCallerCap sender rcvr grant
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  apply (simp add: setupCallerCap_def getThreadCallerSlot_def
                   getThreadReplySlot_def)
  apply (wp hoare_drop_imps)
  apply (simp add: fun_upd_def cong: if_cong)
  done

lemma is_derived_ReplyCap' [simp]:
  "\<And>m p g. is_derived' m p (capability.ReplyCap t False g) =
            (\<lambda>c. \<exists> g. c = capability.ReplyCap t True g)"
  apply (subst fun_eq_iff)
  apply clarsimp
  apply (case_tac x, simp_all add: is_derived'_def isCap_simps
                                   badge_derived'_def
                                   vs_cap_ref'_def)
  done

lemma unique_master_reply_cap':
  "\<And>c t. isReplyCap c \<and> capReplyMaster c \<and> capTCBPtr c = t \<longleftrightarrow>
          (\<exists>g . c = capability.ReplyCap t True g)"
  by (fastforce simp: isCap_simps conj_comms)

lemma getSlotCap_cte_wp_at:
  "\<lbrace>\<top>\<rbrace> getSlotCap sl \<lbrace>\<lambda>rv. cte_wp_at' (\<lambda>c. cteCap c = rv) sl\<rbrace>"
  apply (simp add: getSlotCap_def)
  apply (wp getCTE_wp)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  done

crunch setThreadState
  for no_0_obj'[wp]: no_0_obj'

lemma setupCallerCap_vp[wp]:
  "\<lbrace>valid_pspace' and tcb_at' sender and tcb_at' rcvr\<rbrace>
   setupCallerCap sender rcvr grant \<lbrace>\<lambda>rv. valid_pspace'\<rbrace>"
  apply (simp add: valid_pspace'_def setupCallerCap_def getThreadCallerSlot_def
                   getThreadReplySlot_def locateSlot_conv getSlotCap_def)
  apply (wp getCTE_wp)
  apply (rule_tac Q'="\<lambda>_. valid_pspace' and
                         tcb_at' sender and tcb_at' rcvr"
                  in hoare_post_imp)
   apply (clarsimp simp: valid_cap'_def o_def cte_wp_at_ctes_of isCap_simps
                         valid_pspace'_def)
   apply (frule(1) ctes_of_valid', simp add: valid_cap'_def capAligned_def)
   apply clarsimp
  apply (wp | simp add: valid_pspace'_def valid_tcb_state'_def)+
  done

lemma setupCallerCap_iflive[wp]:
  "\<lbrace>if_live_then_nonz_cap' and ex_nonz_cap_to' sender and pspace_aligned' and pspace_distinct'\<rbrace>
   setupCallerCap sender rcvr grant
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  unfolding setupCallerCap_def getThreadCallerSlot_def
            getThreadReplySlot_def locateSlot_conv
  by (wp getSlotCap_cte_wp_at
          | simp add: unique_master_reply_cap'
          | strengthen eq_imp_strg
          | wp (once) hoare_drop_imp[where f="getCTE rs" for rs])+

lemma setupCallerCap_ifunsafe[wp]:
  "\<lbrace>if_unsafe_then_cap' and valid_objs' and
    ex_nonz_cap_to' rcvr and tcb_at' rcvr and pspace_aligned' and pspace_distinct'\<rbrace>
   setupCallerCap sender rcvr grant
   \<lbrace>\<lambda>rv. if_unsafe_then_cap'\<rbrace>"
  unfolding setupCallerCap_def getThreadCallerSlot_def
            getThreadReplySlot_def locateSlot_conv
  supply raw_tcb_cte_cases_simps[simp] (* FIXME arch-split: legacy, try use tcb_cte_cases_neqs *)
  apply (wp getSlotCap_cte_wp_at
       | simp add: unique_master_reply_cap' | strengthen eq_imp_strg
       | wp (once) hoare_drop_imp[where f="getCTE rs" for rs])+
   apply (rule_tac Q'="\<lambda>rv. valid_objs' and tcb_at' rcvr and ex_nonz_cap_to' rcvr"
                in hoare_post_imp)
    apply (clarsimp simp: ex_nonz_tcb_cte_caps' tcbCallerSlot_def
                          objBits_def objBitsKO_def dom_def cte_level_bits_def)
   apply (wp sts_valid_objs' | simp)+
     apply (clarsimp simp: valid_tcb_state'_def)+
  done

lemma setupCallerCap_global_refs'[wp]:
  "\<lbrace>valid_global_refs'\<rbrace>
     setupCallerCap sender rcvr grant
   \<lbrace>\<lambda>rv. valid_global_refs'\<rbrace>"
  unfolding setupCallerCap_def getThreadCallerSlot_def
            getThreadReplySlot_def locateSlot_conv
  by (wp
      | simp add: o_def unique_master_reply_cap'
      | strengthen eq_imp_strg
      | wp (once) getCTE_wp
      | wp (once) hoare_vcg_imp_lift' hoare_vcg_ex_lift | clarsimp simp: cte_wp_at_ctes_of)+

crunch setupCallerCap
  for valid_arch'[wp]: "valid_arch_state'"
  (wp: hoare_drop_imps)

crunch setupCallerCap
  for irq_node'[wp]: "\<lambda>s. P (irq_node' s)"
  (wp: hoare_drop_imps)

lemma setupCallerCap_irq_handlers'[wp]:
  "\<lbrace>valid_irq_handlers'\<rbrace>
   setupCallerCap sender rcvr grant
   \<lbrace>\<lambda>rv. valid_irq_handlers'\<rbrace>"
  unfolding setupCallerCap_def getThreadCallerSlot_def
            getThreadReplySlot_def locateSlot_conv
  by (wp hoare_drop_imps | simp)+

lemma cteInsert_cap_to':
  "\<lbrace>ex_nonz_cap_to' p and cte_wp_at' (\<lambda>c. cteCap c = NullCap) dest\<rbrace>
     cteInsert cap src dest
   \<lbrace>\<lambda>rv. ex_nonz_cap_to' p\<rbrace>"
  apply (simp add: cteInsert_def ex_nonz_cap_to'_def updateCap_def setUntypedCapAsFull_def)
  apply (wpsimp wp: updateMDB_weak_cte_wp_at setCTE_weak_cte_wp_at hoare_vcg_ex_lift
         | rule hoare_drop_imps
         | wp getCTE_wp)+ (* getCTE_wp is separate to apply it only to the last one *)
  apply (rule_tac x=cref in exI)
  apply (fastforce simp: cte_wp_at_ctes_of)
  done

crunch setExtraBadge
  for cap_to'[wp]: "ex_nonz_cap_to' p"

crunch doIPCTransfer
  for cap_to'[wp]: "ex_nonz_cap_to' p"
  (ignore: transferCapsToSlots
       wp: crunch_wps transferCapsToSlots_pres2 cteInsert_cap_to' hoare_vcg_const_Ball_lift
     simp: zipWithM_x_mapM ball_conj_distrib)

lemma st_tcb_idle':
  "\<lbrakk>valid_idle' s; st_tcb_at' P t s\<rbrakk> \<Longrightarrow>
   (t = ksIdleThread s) \<longrightarrow> P IdleThreadState"
  by (clarsimp simp: valid_idle'_def pred_tcb_at'_def obj_at'_def idle_tcb'_def)

crunch getThreadCallerSlot
  for idle'[wp]: "valid_idle'"
crunch getThreadReplySlot
  for idle'[wp]: "valid_idle'"

crunch setupCallerCap
  for it[wp]: "\<lambda>s. P (ksIdleThread s)"
  (simp: updateObject_cte_inv wp: crunch_wps)

lemma setupCallerCap_idle'[wp]:
  "\<lbrace>valid_idle' and valid_pspace' and
    (\<lambda>s. st \<noteq> ksIdleThread s \<and> rt \<noteq> ksIdleThread s)\<rbrace>
   setupCallerCap st rt gr
   \<lbrace>\<lambda>_. valid_idle'\<rbrace>"
  by (simp add: setupCallerCap_def capRange_def | wp hoare_drop_imps)+

crunch setExtraBadge
  for it[wp]: "\<lambda>s. P (ksIdleThread s)"
crunch receiveIPC
  for it[wp]: "\<lambda>s. P (ksIdleThread s)"
  (ignore: transferCapsToSlots
       wp: transferCapsToSlots_pres2 crunch_wps hoare_vcg_const_Ball_lift
     simp: crunch_simps ball_conj_distrib)

crunch setupCallerCap
  for irq_states'[wp]: valid_irq_states'
  (wp: crunch_wps)

crunch receiveIPC
  for irqs_masked'[wp]: "irqs_masked'"
  (wp: crunch_wps rule: irqs_masked_lift)

crunch getThreadCallerSlot
  for ct_not_inQ[wp]: "ct_not_inQ"
crunch getThreadReplySlot
  for ct_not_inQ[wp]: "ct_not_inQ"

lemma setupCallerCap_ct_not_inQ[wp]:
  "\<lbrace>ct_not_inQ\<rbrace> setupCallerCap sender receiver grant \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  apply (simp add: setupCallerCap_def)
  apply (wp hoare_drop_imp setThreadState_ct_not_inQ)
  done

crunch copyMRs
  for ksQ'[wp]: "\<lambda>s. P (ksReadyQueues s)"
  (wp: mapM_wp' hoare_drop_imps simp: crunch_simps)

crunch doIPCTransfer
  for ksQ[wp]: "\<lambda>s. P (ksReadyQueues s)"
  (wp: hoare_drop_imps hoare_vcg_split_case_option
       mapM_wp'
   simp: split_def zipWithM_x_mapM)

crunch doIPCTransfer
  for ct'[wp]: "\<lambda>s. P (ksCurThread s)"
  (wp: hoare_drop_imps hoare_vcg_split_case_option
       mapM_wp'
   simp: split_def zipWithM_x_mapM)

lemma asUser_ct_not_inQ[wp]:
  "\<lbrace>ct_not_inQ\<rbrace> asUser t m \<lbrace>\<lambda>rv. ct_not_inQ\<rbrace>"
  apply (simp add: asUser_def split_def)
  apply (wp hoare_drop_imps threadSet_not_inQ | simp)+
  done

crunch copyMRs
  for ct_not_inQ[wp]: "ct_not_inQ"
  (wp: mapM_wp' hoare_drop_imps simp: crunch_simps)

crunch doIPCTransfer
  for ct_not_inQ[wp]: "ct_not_inQ"
  (ignore: transferCapsToSlots
   wp: hoare_drop_imps hoare_vcg_split_case_option
       mapM_wp'
   simp: split_def zipWithM_x_mapM)

lemma ntfn_q_refs_no_bound_refs': "rf : ntfn_q_refs_of' (ntfnObj ob) \<Longrightarrow> rf ~: ntfn_bound_refs' (ntfnBoundTCB ob')"
  by (auto simp add: ntfn_q_refs_of'_def ntfn_bound_refs'_def
           split: Structures_H.ntfn.splits)

lemma completeSignal_invs:
  "\<lbrace>invs' and tcb_at' tcb\<rbrace>
     completeSignal ntfnptr tcb
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: completeSignal_def)
  apply (rule bind_wp[OF _ get_ntfn_sp'])
  apply (rule hoare_pre)
   apply (wp set_ntfn_minor_invs' | wpc | simp)+
    apply (rule_tac Q'="\<lambda>_ s. (state_refs_of' s ntfnptr = ntfn_bound_refs' (ntfnBoundTCB ntfn))
                           \<and> ntfn_at' ntfnptr s
                           \<and> valid_ntfn' (ntfnObj_update (\<lambda>_. Structures_H.ntfn.IdleNtfn) ntfn) s
                           \<and> ((\<exists>y. ntfnBoundTCB ntfn = Some y) \<longrightarrow> ex_nonz_cap_to' ntfnptr s)
                           \<and> ntfnptr \<noteq> ksIdleThread s"
                          in hoare_strengthen_post)
     apply ((wp hoare_vcg_ex_lift hoare_weak_lift_imp | wpc | simp add: valid_ntfn'_def)+)[1]
    apply (clarsimp simp: obj_at'_def state_refs_of'_def typ_at'_def ko_wp_at'_def live'_def
                    split: option.splits)
    apply (blast dest: ntfn_q_refs_no_bound_refs')
   apply wp
  apply (subgoal_tac "valid_ntfn' ntfn s")
   apply (subgoal_tac "ntfnptr \<noteq> ksIdleThread s")
    apply (fastforce simp: valid_ntfn'_def valid_bound_tcb'_def ko_at_state_refs_ofD' live'_def
                     elim: obj_at'_weakenE
                           if_live_then_nonz_capD'[OF invs_iflive'
                                                      obj_at'_real_def[THEN meta_eq_to_obj_eq,
                                                                       THEN iffD1]])
   apply (fastforce simp: valid_idle'_def pred_tcb_at'_def obj_at'_def
                   dest!: invs_valid_idle')
  apply (fastforce dest: invs_valid_objs' ko_at_valid_objs'
                   simp: valid_obj'_def)[1]
  done

lemma setupCallerCap_urz[wp]:
  "\<lbrace>untyped_ranges_zero' and valid_pspace' and tcb_at' sender\<rbrace>
    setupCallerCap sender t g \<lbrace>\<lambda>rv. untyped_ranges_zero'\<rbrace>"
  apply (simp add: setupCallerCap_def getSlotCap_def
                   getThreadCallerSlot_def getThreadReplySlot_def
                   locateSlot_conv)
  apply (wp getCTE_wp')
  apply (rule_tac Q'="\<lambda>_. untyped_ranges_zero' and valid_mdb' and valid_objs'" in hoare_post_imp)
   apply (clarsimp simp: cte_wp_at_ctes_of cteCaps_of_def untyped_derived_eq_def
                         isCap_simps)
  apply (wp sts_valid_pspace_hangers)
  apply (clarsimp simp: valid_tcb_state'_def)
  done

lemmas threadSet_urz = untyped_ranges_zero_lift[where f="cteCaps_of", OF _ threadSet_cteCaps_of]

crunch doIPCTransfer
  for urz[wp]: "untyped_ranges_zero'"
  (ignore: threadSet wp: threadSet_urz crunch_wps simp: zipWithM_x_mapM)

crunch receiveIPC
  for gsUntypedZeroRanges[wp]: "\<lambda>s. P (gsUntypedZeroRanges s)"
  (wp: crunch_wps transferCapsToSlots_pres1 simp: zipWithM_x_mapM ignore: constOnFailure)

crunch possibleSwitchTo
  for ctes_of[wp]: "\<lambda>s. P (ctes_of s)"
  (wp: crunch_wps ignore: constOnFailure)

lemmas possibleSwitchToTo_cteCaps_of[wp]
    = cteCaps_of_ctes_of_lift[OF possibleSwitchTo_ctes_of]

crunch possibleSwitchTo
  for ksArch[wp]: "\<lambda>s. P (ksArchState s)"
  (wp: possibleSwitchTo_ctes_of crunch_wps ignore: constOnFailure)

crunch asUser
  for valid_bitmaps[wp]: valid_bitmaps
  (rule: valid_bitmaps_lift wp: crunch_wps)

crunch setupCallerCap, possibleSwitchTo, doIPCTransfer
  for sym_heap_sched_pointers[wp]: sym_heap_sched_pointers
  and valid_sched_pointers[wp]: valid_sched_pointers
  and valid_bitmaps[wp]: valid_bitmaps
  (rule: sym_heap_sched_pointers_lift wp: crunch_wps simp: crunch_simps)

(* t = ksCurThread s *)
lemma ri_invs' [wp]:
  "\<lbrace>invs' and sch_act_not t
          and ct_in_state' simple'
          and st_tcb_at' simple' t
          and ex_nonz_cap_to' t
          and (\<lambda>s. \<forall>r \<in> zobj_refs' cap. ex_nonz_cap_to' r s)\<rbrace>
  receiveIPC t cap isBlocking
  \<lbrace>\<lambda>_. invs'\<rbrace>" (is "\<lbrace>?pre\<rbrace> _ \<lbrace>_\<rbrace>")
  apply (clarsimp simp: receiveIPC_def)
  apply (rule bind_wp [OF _ get_ep_sp'])
  apply (rule bind_wp [OF _ gbn_sp'])
  apply (rule bind_wp)
  (* set up precondition for old proof *)
   apply (rule_tac P''="ko_at' ep (capEPPtr cap) and ?pre" in hoare_vcg_if_split)
    apply (wp completeSignal_invs)
   apply (case_tac ep)
     \<comment> \<open>endpoint = RecvEP\<close>
     apply (simp add: invs'_def valid_state'_def)
     apply (rule hoare_pre, wpc, wp valid_irq_node_lift)
      apply (simp add: valid_ep'_def)
      apply (wp sts_sch_act' hoare_vcg_const_Ball_lift valid_irq_node_lift
                setThreadState_ct_not_inQ
                asUser_urz
           | simp add: doNBRecvFailedTransfer_def cteCaps_of_def)+
     apply (clarsimp simp: valid_tcb_state'_def pred_tcb_at' o_def)
     apply (rule conjI, clarsimp elim!: obj_at'_weakenE)
     apply (frule obj_at_valid_objs')
      apply (clarsimp simp: valid_pspace'_def)
     apply (drule(1) sym_refs_ko_atD')
     apply (drule simple_st_tcb_at_state_refs_ofD')
     apply (drule bound_tcb_at_state_refs_ofD')
     apply (clarsimp simp: st_tcb_at_refs_of_rev' valid_ep'_def
                           valid_obj'_def tcb_bound_refs'_def
                    dest!: isCapDs)
     apply (rule conjI, clarsimp)
      apply (drule (1) bspec)
      apply (clarsimp dest!: st_tcb_at_state_refs_ofD')
      apply (clarsimp simp: set_eq_subset)
     apply (rule conjI, erule delta_sym_refs)
       apply (clarsimp split: if_split_asm)
        apply ((case_tac tp; fastforce elim: nonempty_cross_distinct_singleton_elim)+)[2]
      apply (clarsimp split: if_split_asm)
     apply (fastforce simp: valid_pspace'_def global'_no_ex_cap idle'_not_queued)
   \<comment> \<open>endpoint = IdleEP\<close>
    apply (simp add: invs'_def valid_state'_def)
    apply (rule hoare_pre, wpc, wp valid_irq_node_lift)
     apply (simp add: valid_ep'_def)
     apply (wp sts_sch_act' valid_irq_node_lift
               setThreadState_ct_not_inQ
               asUser_urz
          | simp add: doNBRecvFailedTransfer_def cteCaps_of_def)+
    apply (clarsimp simp: pred_tcb_at' valid_tcb_state'_def o_def)
    apply (rule conjI, clarsimp elim!: obj_at'_weakenE)
    apply (subgoal_tac "t \<noteq> capEPPtr cap")
     apply (drule simple_st_tcb_at_state_refs_ofD')
     apply (drule ko_at_state_refs_ofD')
     apply (drule bound_tcb_at_state_refs_ofD')
     apply (clarsimp dest!: isCapDs)
     apply (rule conjI, erule delta_sym_refs)
       apply (clarsimp split: if_split_asm)
      apply (clarsimp simp: tcb_bound_refs'_def
                      dest: symreftype_inverse'
                     split: if_split_asm)
     apply (fastforce simp: global'_no_ex_cap)
    apply (clarsimp simp: obj_at'_def pred_tcb_at'_def)
   \<comment> \<open>endpoint = SendEP\<close>
   apply (simp add: invs'_def valid_state'_def)
   apply (rename_tac list)
   apply (case_tac list, simp_all split del: if_split)
   apply (rename_tac sender queue)
   apply (rule hoare_pre)
    apply (wp valid_irq_node_lift hoare_drop_imps setEndpoint_valid_mdb'
              set_ep_valid_objs' sts_st_tcb' sts_sch_act'
              setThreadState_ct_not_inQ
              possibleSwitchTo_ct_not_inQ hoare_vcg_all_lift
              setEndpoint_ksQ setEndpoint_ct'
         | simp add: valid_tcb_state'_def case_bool_If
                     case_option_If
              split del: if_split cong: if_cong
        | wp (once) sch_act_sane_lift hoare_vcg_conj_lift hoare_vcg_all_lift
                  untyped_ranges_zero_lift)+
   apply (clarsimp split del: if_split simp: pred_tcb_at')
   apply (frule obj_at_valid_objs')
    apply (clarsimp simp: valid_pspace'_def)
   apply (frule(1) ct_not_in_epQueue, clarsimp, clarsimp)
   apply (drule(1) sym_refs_ko_atD')
   apply (drule simple_st_tcb_at_state_refs_ofD')
   apply (clarsimp simp: projectKOs valid_obj'_def valid_ep'_def
                         st_tcb_at_refs_of_rev' conj_ac
              split del: if_split
                   cong: if_cong)
   apply (subgoal_tac "sch_act_not sender s")
    prefer 2
    apply (clarsimp simp: pred_tcb_at'_def obj_at'_def)
   apply (drule st_tcb_at_state_refs_ofD')
   apply (simp only: conj_ac(1, 2)[where Q="sym_refs R" for R])
   apply (subgoal_tac "distinct (ksIdleThread s # capEPPtr cap # t # sender # queue)")
    apply (rule conjI)
     apply (clarsimp simp: ep_redux_simps' cong: if_cong)
     apply (erule delta_sym_refs)
      apply (clarsimp split: if_split_asm)
     apply (fastforce simp: tcb_bound_refs'_def
                      dest: symreftype_inverse'
                     split: if_split_asm)
    apply (clarsimp simp: singleton_tuple_cartesian split: list.split
            | rule conjI | drule(1) bspec
            | drule st_tcb_at_state_refs_ofD' bound_tcb_at_state_refs_ofD'
            | clarsimp elim!: if_live_state_refsE)+
    apply (case_tac cap, simp_all add: isEndpointCap_def)
    apply (clarsimp simp: global'_no_ex_cap)
   apply (rule conjI
           | clarsimp simp: singleton_tuple_cartesian split: list.split
           | clarsimp elim!: if_live_state_refsE
           | clarsimp simp: global'_no_ex_cap idle'_not_queued' idle'_no_refs tcb_bound_refs'_def
           | drule(1) bspec | drule st_tcb_at_state_refs_ofD'
           | clarsimp simp: set_eq_subset dest!: bound_tcb_at_state_refs_ofD' )+
  apply (rule hoare_pre)
   apply (wp getNotification_wp | wpc | clarsimp)+
  done

(* t = ksCurThread s *)
lemma rai_invs'[wp]:
  "\<lbrace>invs' and sch_act_not t
          and st_tcb_at' simple' t
          and ex_nonz_cap_to' t
          and (\<lambda>s. \<forall>r \<in> zobj_refs' cap. ex_nonz_cap_to' r s)
          and (\<lambda>s. \<exists>ntfnptr. isNotificationCap cap
                 \<and> capNtfnPtr cap = ntfnptr
                 \<and> obj_at' (\<lambda>ko. ntfnBoundTCB ko = None \<or> ntfnBoundTCB ko = Some t)
                           ntfnptr s)\<rbrace>
    receiveSignal t cap isBlocking
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: receiveSignal_def)
  apply (rule bind_wp [OF _ get_ntfn_sp'])
  apply (rename_tac ep)
  apply (case_tac "ntfnObj ep")
    \<comment> \<open>ep = IdleNtfn\<close>
    apply (simp add: invs'_def valid_state'_def)
    apply (rule hoare_pre)
     apply (wp valid_irq_node_lift sts_sch_act' typ_at_lifts
               setThreadState_ct_not_inQ
               asUser_urz
            | simp add: valid_ntfn'_def doNBRecvFailedTransfer_def live'_def | wpc)+
    apply (clarsimp simp: pred_tcb_at' valid_tcb_state'_def)
    apply (rule conjI, clarsimp elim!: obj_at'_weakenE)
    apply (subgoal_tac "capNtfnPtr cap \<noteq> t")
     apply (frule valid_pspace_valid_objs')
     apply (frule (1) ko_at_valid_objs')
      apply (clarsimp simp: projectKOs)
     apply (clarsimp simp: valid_obj'_def valid_ntfn'_def)
     apply (rule conjI, clarsimp simp: obj_at'_def split: option.split)
     apply (drule simple_st_tcb_at_state_refs_ofD'
                  ko_at_state_refs_ofD' bound_tcb_at_state_refs_ofD')+
     apply (clarsimp dest!: isCapDs)
     apply (rule conjI, erule delta_sym_refs)
       apply (clarsimp split: if_split_asm)
      apply (fastforce simp: tcb_bound_refs'_def symreftype_inverse'
                      split: if_split_asm)
     apply (fastforce dest!: global'_no_ex_cap)
    apply (clarsimp simp: pred_tcb_at'_def obj_at'_def projectKOs)
   \<comment> \<open>ep = ActiveNtfn\<close>
   apply (simp add: invs'_def valid_state'_def)
   apply (rule hoare_pre)
    apply (wp valid_irq_node_lift sts_valid_objs' typ_at_lifts hoare_weak_lift_imp
              asUser_urz
         | simp add: valid_ntfn'_def)+
   apply (clarsimp simp: pred_tcb_at' valid_pspace'_def)
   apply (frule (1) ko_at_valid_objs')
    apply (clarsimp simp: projectKOs)
   apply (clarsimp simp: valid_obj'_def valid_ntfn'_def isCap_simps)
   apply (drule simple_st_tcb_at_state_refs_ofD'
                 ko_at_state_refs_ofD')+
   apply (erule delta_sym_refs)
    apply (clarsimp split: if_split_asm simp: global'_no_ex_cap)+
  \<comment> \<open>ep = WaitingNtfn\<close>
  apply (simp add: invs'_def valid_state'_def)
  apply (rule hoare_pre)
   apply (wp hoare_vcg_const_Ball_lift valid_irq_node_lift sts_sch_act'
             setThreadState_ct_not_inQ typ_at_lifts
             asUser_urz
        | simp add: valid_ntfn'_def doNBRecvFailedTransfer_def live'_def | wpc)+
  apply (clarsimp simp: valid_tcb_state'_def)
  apply (frule_tac t=t in not_in_ntfnQueue)
     apply (simp)
    apply (simp)
   apply (erule pred_tcb'_weakenE, clarsimp)
  apply (frule ko_at_valid_objs')
    apply (clarsimp simp: valid_pspace'_def)
   apply (simp add: projectKOs)
  apply (clarsimp simp: valid_obj'_def)
  apply (clarsimp simp: valid_ntfn'_def pred_tcb_at')
  apply (rule conjI, clarsimp elim!: obj_at'_weakenE)
  apply (rule conjI, clarsimp simp: obj_at'_def split: option.split)
  apply (drule(1) sym_refs_ko_atD')
  apply (drule simple_st_tcb_at_state_refs_ofD')
  apply (drule bound_tcb_at_state_refs_ofD')
  apply (clarsimp simp: st_tcb_at_refs_of_rev'
                 dest!: isCapDs)
  apply (rule conjI, erule delta_sym_refs)
    apply (clarsimp split: if_split_asm)
    apply (rename_tac list one two three four five six seven eight nine)
    apply (subgoal_tac "set list \<times> {NTFNSignal} \<noteq> {}")
     apply safe[1]
        apply (auto simp: symreftype_inverse' ntfn_bound_refs'_def tcb_bound_refs'_def)[5]
   apply (fastforce simp: tcb_bound_refs'_def
                   split: if_split_asm)
  apply (fastforce dest!: global'_no_ex_cap)
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

crunch setVMRoot
  for valid_objs'[wp]: valid_objs'
  (wp: crunch_wps simp: crunch_simps)

lemma arch_stt_objs' [wp]:
  "\<lbrace>valid_objs'\<rbrace> Arch.switchToThread t \<lbrace>\<lambda>rv. valid_objs'\<rbrace>"
  apply (simp add: RISCV64_H.switchToThread_def)
  apply wp
  done

declare zipWithM_x_mapM [simp]

lemma cteInsert_invs_bits[wp]:
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>
      cteInsert a b c
   \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  "\<lbrace>cur_tcb'\<rbrace> cteInsert a b c \<lbrace>\<lambda>rv. cur_tcb'\<rbrace>"
  "\<lbrace>\<lambda>s. P (state_refs_of' s)\<rbrace>
      cteInsert a b c
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
apply (wp sch_act_wf_lift valid_queues_lift
          cur_tcb_lift tcb_in_cur_domain'_lift)+
done

lemma possibleSwitchTo_sch_act_not:
  "\<lbrace>sch_act_not t' and K (t \<noteq> t')\<rbrace> possibleSwitchTo t \<lbrace>\<lambda>rv. sch_act_not t'\<rbrace>"
  apply (simp add: possibleSwitchTo_def setSchedulerAction_def curDomain_def)
  apply (wp hoare_drop_imps | wpc | simp)+
  done

crunch possibleSwitchTo
  for urz[wp]: "untyped_ranges_zero'"
  (simp: crunch_simps unless_def wp: crunch_wps)

crunch possibleSwitchTo
  for pspace_aligned'[wp]: pspace_aligned'
  and pspace_distinct'[wp]: pspace_distinct'

lemma si_invs'[wp]:
  "\<lbrace>invs' and st_tcb_at' simple' t
          and sch_act_not t
          and ex_nonz_cap_to' ep and ex_nonz_cap_to' t\<rbrace>
  sendIPC bl call ba cg cgr t ep
  \<lbrace>\<lambda>rv. invs'\<rbrace>"
  supply if_split[split del]
  apply (simp add: sendIPC_def)
  apply (rule bind_wp [OF _ get_ep_sp'])
  apply (case_tac epa)
    \<comment> \<open>epa = RecvEP\<close>
    apply simp
    apply (rename_tac list)
    apply (case_tac list)
     apply simp
    apply (simp add: invs'_def valid_state'_def)
    apply (rule hoare_pre)
     apply (rule_tac P="a\<noteq>t" in hoare_gen_asm)
     apply (wp valid_irq_node_lift
               sts_valid_objs' set_ep_valid_objs' setEndpoint_valid_mdb' sts_st_tcb' sts_sch_act'
               possibleSwitchTo_sch_act_not setThreadState_ct_not_inQ
               possibleSwitchTo_ct_not_inQ hoare_vcg_all_lift
               hoare_convert_imp [OF doIPCTransfer_sch_act doIPCTransfer_ct']
               hoare_convert_imp [OF setEndpoint_nosch setEndpoint_ct']
               hoare_drop_imp [where f="threadGet tcbFault t"]
             | rule_tac f="getThreadState a" in hoare_drop_imp
             | wp (once) hoare_drop_imp[where Q'="\<lambda>_ _. call"]
               hoare_drop_imp[where Q'="\<lambda>_ _. \<not> call"]
               hoare_drop_imp[where Q'="\<lambda>_ _. cg"]
             | simp    add: valid_tcb_state'_def case_bool_If
                            case_option_If
                      cong: if_cong
             | wp (once) sch_act_sane_lift tcb_in_cur_domain'_lift hoare_vcg_const_imp_lift)+
    apply (clarsimp simp: pred_tcb_at' cong: conj_cong imp_cong)
    apply (frule obj_at_valid_objs', clarsimp)
    apply (frule(1) sym_refs_ko_atD')
    apply (clarsimp simp: projectKOs valid_obj'_def valid_ep'_def
                          st_tcb_at_refs_of_rev' pred_tcb_at'
                          conj_comms fun_upd_def[symmetric]
               split del: if_split)
    apply (frule pred_tcb_at')
    apply (drule simple_st_tcb_at_state_refs_ofD' st_tcb_at_state_refs_ofD')+
    apply (clarsimp simp: valid_pspace'_splits)
    apply (subst fun_upd_idem[where x=t])
     apply (clarsimp split: if_split)
     apply (rule conjI, clarsimp simp: obj_at'_def)
     apply (drule bound_tcb_at_state_refs_ofD')
     apply (fastforce simp: tcb_bound_refs'_def)
    apply (subgoal_tac "ex_nonz_cap_to' a s")
     prefer 2
     apply (clarsimp elim!: if_live_state_refsE)
    apply clarsimp
    apply (rule conjI)
     apply (drule bound_tcb_at_state_refs_ofD')
     apply (fastforce simp: tcb_bound_refs'_def set_eq_subset)
    apply (clarsimp simp: conj_ac)
    apply (rule conjI, clarsimp simp: idle'_no_refs)
    apply (rule conjI, clarsimp simp: global'_no_ex_cap)
    apply (rule conjI)
     apply (rule impI)
     apply (frule(1) ct_not_in_epQueue, clarsimp, clarsimp)
     apply (clarsimp)
    apply (simp add: ep_redux_simps')
    apply (rule conjI, clarsimp split: if_split)
     apply (rule conjI, fastforce simp: tcb_bound_refs'_def set_eq_subset)
     apply (clarsimp, erule delta_sym_refs;
            solves\<open>auto simp: symreftype_inverse' tcb_bound_refs'_def split: if_split_asm\<close>)
    apply (solves\<open>clarsimp split: list.splits\<close>)
   \<comment> \<open>epa = IdleEP\<close>
   apply (cases bl)
    apply (simp add: invs'_def valid_state'_def)
    apply (rule hoare_pre, wp valid_irq_node_lift)
     apply (simp add: valid_ep'_def)
     apply (wp valid_irq_node_lift sts_sch_act' setThreadState_ct_not_inQ)
    apply (clarsimp simp: valid_tcb_state'_def pred_tcb_at')
    apply (rule conjI, clarsimp elim!: obj_at'_weakenE)
    apply (subgoal_tac "ep \<noteq> t")
     apply (drule simple_st_tcb_at_state_refs_ofD' ko_at_state_refs_ofD'
                  bound_tcb_at_state_refs_ofD')+
     apply (rule conjI, erule delta_sym_refs)
       apply (auto simp: tcb_bound_refs'_def symreftype_inverse'
                  split: if_split_asm)[2]
     apply (fastforce simp: global'_no_ex_cap)
    apply (clarsimp simp: pred_tcb_at'_def obj_at'_def projectKOs)
   apply simp
   apply wp
   apply simp
  \<comment> \<open>epa = SendEP\<close>
  apply (cases bl)
   apply (simp add: invs'_def valid_state'_def)
   apply (rule hoare_pre, wp valid_irq_node_lift)
    apply (simp add: valid_ep'_def)
    apply (wp hoare_vcg_const_Ball_lift valid_irq_node_lift sts_sch_act' setThreadState_ct_not_inQ)
   apply (clarsimp simp: valid_tcb_state'_def pred_tcb_at')
   apply (rule conjI, clarsimp elim!: obj_at'_weakenE)
   apply (frule obj_at_valid_objs', clarsimp)
   apply (frule(1) sym_refs_ko_atD')
   apply (frule pred_tcb_at')
   apply (drule simple_st_tcb_at_state_refs_ofD')
   apply (drule bound_tcb_at_state_refs_ofD')
   apply (clarsimp simp: valid_obj'_def valid_ep'_def st_tcb_at_refs_of_rev')
   apply (rule conjI, clarsimp)
    apply (drule (1) bspec)
    apply (clarsimp dest!: st_tcb_at_state_refs_ofD' bound_tcb_at_state_refs_ofD'
                     simp: tcb_bound_refs'_def)
    apply (clarsimp simp: set_eq_subset)
   apply (rule conjI, erule delta_sym_refs)
     subgoal by (fastforce simp: obj_at'_def symreftype_inverse'
                     split: if_split_asm)
    apply (fastforce simp: tcb_bound_refs'_def symreftype_inverse'
                    split: if_split_asm)
   apply (fastforce simp: global'_no_ex_cap idle'_not_queued)
  apply (simp | wp)+
  done

lemma sfi_invs_plus':
  "\<lbrace>invs' and st_tcb_at' simple' t
          and sch_act_not t
          and ex_nonz_cap_to' t\<rbrace>
   sendFaultIPC t f
   \<lbrace>\<lambda>_. invs'\<rbrace>, \<lbrace>\<lambda>_. invs' and st_tcb_at' simple' t and sch_act_not t and (\<lambda>s. ksIdleThread s \<noteq> t)\<rbrace>"
  apply (simp add: sendFaultIPC_def)
  apply (wp threadSet_invs_trivial threadSet_pred_tcb_no_state
            threadSet_cap_to'
           | wpc | simp)+
   apply (rule_tac Q'="\<lambda>rv s. invs' s \<and> sch_act_not t s
                             \<and> st_tcb_at' simple' t s
                             \<and> ex_nonz_cap_to' t s
                             \<and> t \<noteq> ksIdleThread s
                             \<and> (\<forall>r\<in>zobj_refs' rv. ex_nonz_cap_to' r s)"
                 in hoare_strengthen_postE_R)
    apply wp
   apply (clarsimp simp: inQ_def pred_tcb_at')
  apply (wp | simp)+
  apply (clarsimp simp: eq_commute)
  apply (subst(asm) global'_no_ex_cap, auto)
  done

crunch send_fault_ipc
  for pspace_aligned[wp]: "pspace_aligned :: det_ext state \<Rightarrow> _"
  and pspace_distinct[wp]: "pspace_distinct :: det_ext state \<Rightarrow> _"
  (simp: crunch_simps wp: crunch_wps)

lemma handleFault_corres:
  "fr f f' \<Longrightarrow>
   corres dc (einvs and st_tcb_at active thread and ex_nonz_cap_to thread
                   and (\<lambda>_. valid_fault f))
             (invs' and sch_act_not thread
                    and st_tcb_at' simple' thread and ex_nonz_cap_to' thread)
             (handle_fault thread f) (handleFault thread f')"
  apply (simp add: handle_fault_def handleFault_def)
  apply (rule corres_guard_imp)
    apply (subst return_bind [symmetric],
               rule corres_split[where P="tcb_at thread",
                                 OF gets_the_noop_corres [where x="()"]])
       apply (simp add: tcb_at_def)
      apply (rule corres_split_catch)
         apply (rule_tac F="valid_fault f" in corres_gen_asm)
         apply (rule sendFaultIPC_corres, assumption)
         apply simp
        apply (rule handleDoubleFault_corres)
       apply wpsimp+
   apply (clarsimp simp: st_tcb_at_tcb_at st_tcb_def2 invs_def valid_state_def valid_idle_def)
   apply auto
  done

lemma sts_invs_minor'':
  "\<lbrace>st_tcb_at' (\<lambda>st'. tcb_st_refs_of' st' = tcb_st_refs_of' st
                   \<and> (st \<noteq> Inactive \<and> \<not> idle' st \<longrightarrow>
                      st' \<noteq> Inactive \<and> \<not> idle' st')) t
      and (\<lambda>s. t = ksIdleThread s \<longrightarrow> idle' st)
      and (\<lambda>s. \<not> runnable' st \<longrightarrow> sch_act_not t s)
      and invs'\<rbrace>
     setThreadState st t
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def)
  apply (rule hoare_pre)
   apply (wp valid_irq_node_lift sts_sch_act' setThreadState_ct_not_inQ)
  apply clarsimp
  apply (rule conjI)
   apply fastforce
  apply (rule conjI)
   apply (clarsimp simp: pred_tcb_at'_def)
   apply (drule obj_at_valid_objs')
    apply (clarsimp simp: valid_pspace'_def)
   apply (clarsimp simp: valid_obj'_def valid_tcb'_def)
   subgoal by (cases st, auto simp: valid_tcb_state'_def
                        split: Structures_H.thread_state.splits)[1]
  apply (rule conjI)
   apply (clarsimp dest!: st_tcb_at_state_refs_ofD'
                   elim!: rsubst[where P=sym_refs]
                  intro!: ext)
  apply (fastforce elim!: st_tcb_ex_cap'')
  done

lemma hf_invs' [wp]:
  "\<lbrace>invs' and sch_act_not t
          and st_tcb_at' simple' t
          and ex_nonz_cap_to' t and (\<lambda>s. t \<noteq> ksIdleThread s)\<rbrace>
   handleFault t f \<lbrace>\<lambda>r. invs'\<rbrace>"
  apply (simp add: handleFault_def)
  apply wp
   apply (simp add: handleDoubleFault_def)
   apply (wp sts_invs_minor'' dmo_invs')+
  apply (rule hoare_strengthen_postE, rule sfi_invs_plus',
         simp_all)
  apply (strengthen no_refs_simple_strg')
  apply clarsimp
  done

declare zipWithM_x_mapM [simp del]

lemma gts_st_tcb':
  "\<lbrace>\<top>\<rbrace> getThreadState t \<lbrace>\<lambda>r. st_tcb_at' (\<lambda>st. st = r) t\<rbrace>"
  apply (rule hoare_strengthen_post)
  apply (rule gts_sp')
  apply simp
  done

declare setEndpoint_ct' [wp]

lemma setupCallerCap_pred_tcb_unchanged:
  "\<lbrace>pred_tcb_at' proj P t and K (t \<noteq> t')\<rbrace>
     setupCallerCap t' t'' g
   \<lbrace>\<lambda>rv. pred_tcb_at' proj P t\<rbrace>"
  apply (simp add: setupCallerCap_def getThreadCallerSlot_def
                   getThreadReplySlot_def)
  apply (wp sts_pred_tcb_neq' hoare_drop_imps)
  apply clarsimp
  done

lemma si_blk_makes_simple':
  "\<lbrace>st_tcb_at' simple' t and K (t \<noteq> t')\<rbrace>
     sendIPC True call bdg x x' t' ep
   \<lbrace>\<lambda>rv. st_tcb_at' simple' t\<rbrace>"
  apply (simp add: sendIPC_def)
  apply (rule bind_wp [OF _ get_ep_inv'])
  apply (case_tac rv, simp_all)
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
  done

lemma si_blk_makes_runnable':
  "\<lbrace>st_tcb_at' runnable' t and K (t \<noteq> t')\<rbrace>
     sendIPC True call bdg x x' t' ep
   \<lbrace>\<lambda>rv. st_tcb_at' runnable' t\<rbrace>"
  apply (simp add: sendIPC_def)
  apply (rule bind_wp [OF _ get_ep_inv'])
  apply (case_tac rv, simp_all)
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
  done

lemma sfi_makes_simple':
  "\<lbrace>st_tcb_at' simple' t and K (t \<noteq> t')\<rbrace>
     sendFaultIPC t' ft
   \<lbrace>\<lambda>rv. st_tcb_at' simple' t\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: sendFaultIPC_def
             cong: if_cong capability.case_cong bool.case_cong)
  apply (wpsimp wp: si_blk_makes_simple' threadSet_pred_tcb_no_state hoare_drop_imps
                    hoare_vcg_all_liftE_R)
  done

lemma sfi_makes_runnable':
  "\<lbrace>st_tcb_at' runnable' t and K (t \<noteq> t')\<rbrace>
     sendFaultIPC t' ft
   \<lbrace>\<lambda>rv. st_tcb_at' runnable' t\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: sendFaultIPC_def
             cong: if_cong capability.case_cong bool.case_cong)
  apply (wpsimp wp: si_blk_makes_runnable' threadSet_pred_tcb_no_state hoare_drop_imps
                    hoare_vcg_all_liftE_R)
  done

lemma hf_makes_runnable_simple':
  "\<lbrace>st_tcb_at' P t' and K (t \<noteq> t') and K (P = runnable' \<or> P = simple')\<rbrace>
     handleFault t ft
   \<lbrace>\<lambda>rv. st_tcb_at' P t'\<rbrace>"
  apply (safe intro!: hoare_gen_asm)
  apply (simp_all add: handleFault_def handleDoubleFault_def)
   apply (wp sfi_makes_runnable' sfi_makes_simple' sts_st_tcb_at'_cases
           | simp add: handleDoubleFault_def)+
  done

crunch possibleSwitchTo, completeSignal
  for pred_tcb_at'[wp]: "pred_tcb_at' proj P t"

lemma ri_makes_runnable_simple':
  "\<lbrace>st_tcb_at' P t' and K (t \<noteq> t') and K (P = runnable' \<or> P = simple')\<rbrace>
     receiveIPC t cap isBlocking
   \<lbrace>\<lambda>rv. st_tcb_at' P t'\<rbrace>"
  including no_pre
  apply (rule hoare_gen_asm)+
  apply (simp add: receiveIPC_def)
  apply (case_tac cap, simp_all add: isEndpointCap_def)
  apply (rule bind_wp [OF _ get_ep_inv'])
  apply (rule bind_wp [OF _ gbn_sp'])
  apply wp
   apply (rename_tac ep q r)
   apply (case_tac ep, simp_all)
     apply (wp sts_st_tcb_at'_cases | wpc | simp add: doNBRecvFailedTransfer_def)+
   apply (rename_tac list)
   apply (case_tac list, simp_all add: case_bool_If case_option_If
                            split del: if_split cong: if_cong)
   apply (rule hoare_pre)
    apply (wp sts_st_tcb_at'_cases setupCallerCap_pred_tcb_unchanged
              hoare_vcg_const_imp_lift)+
     apply (simp, simp only: imp_conv_disj)
     apply (wp hoare_vcg_disj_lift)+
   apply (clarsimp simp: pred_tcb_at'_def obj_at'_def projectKOs)
   apply (fastforce simp: pred_tcb_at'_def obj_at'_def isSend_def
                  split: Structures_H.thread_state.split_asm)
  apply (rule hoare_pre)
   apply wpsimp+
  done

lemma rai_makes_runnable_simple':
  "\<lbrace>st_tcb_at' P t' and K (t \<noteq> t') and K (P = runnable' \<or> P = simple')\<rbrace>
     receiveSignal t cap isBlocking
   \<lbrace>\<lambda>rv. st_tcb_at' P t'\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: receiveSignal_def)
  apply (rule hoare_pre)
   by (wp sts_st_tcb_at'_cases getNotification_wp | wpc | simp add: doNBRecvFailedTransfer_def)+

lemma sendSignal_st_tcb'_Running:
  "\<lbrace>st_tcb_at' (\<lambda>st. st = Running \<or> P st) t\<rbrace>
     sendSignal ntfnptr bdg
   \<lbrace>\<lambda>_. st_tcb_at' (\<lambda>st. st = Running \<or> P st) t\<rbrace>"
  apply (simp add: sendSignal_def)
  apply (wp sts_st_tcb_at'_cases cancelIPC_st_tcb_at' gts_wp' getNotification_wp hoare_weak_lift_imp
       | wpc | clarsimp simp: pred_tcb_at')+
  done

lemma sai_st_tcb':
  "\<lbrace>st_tcb_at' P t and K (P Running)\<rbrace>
     sendSignal ntfn bdg
   \<lbrace>\<lambda>rv. st_tcb_at' P t\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (subgoal_tac "\<exists>Q. P = (\<lambda>st. st = Running \<or> Q st)")
   apply (clarsimp intro!: sendSignal_st_tcb'_Running)
  apply (fastforce intro!: exI[where x=P])
  done

end

end
