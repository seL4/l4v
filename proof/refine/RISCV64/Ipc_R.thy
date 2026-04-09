(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Ipc_R
imports Finalise_R Reply_R
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

end

crunch setExtraBadge
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n n p s)"
  and valid_pspace'[wp]: valid_pspace'
  and cte_wp_at'[wp]: "cte_wp_at' P p"
  and ipc_buffer'[wp]: "valid_ipc_buffer_ptr' buffer"

global_interpretation setExtraBadge: typ_at_all_props' "setExtraBadge buffer badge n"
  by typ_at_props'

crunch getExtraCPtr
  for inv'[wp]: P (wp: dmo_inv' loadWord_inv)

lemmas unifyFailure_discard2
    = corres_injection[OF id_injection unifyFailure_injection, simplified]

lemma deriveCap_not_null:
  "\<lbrace>\<top>\<rbrace> deriveCap slot cap \<lbrace>\<lambda>rv. K (rv \<noteq> NullCap \<longrightarrow> cap \<noteq> NullCap)\<rbrace>,-"
  apply (simp add: deriveCap_def split del: if_split)
  by (case_tac cap; wpsimp simp: gen_isCap_simps)

context begin interpretation Arch . (*FIXME: arch-split*)

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
   apply (clarsimp simp: is_derived'_def gen_isCap_simps)
   apply (drule valid_mdb_untyped_incD')
   apply (case_tac cte, case_tac cteb, clarsimp)
   apply (drule untyped_incD', (simp add: gen_isCap_simps)+)
   apply (frule(1) ctes_of_valid'[where p = p])
   apply (clarsimp simp:valid_cap'_def capAligned_def split:if_splits)
    apply (drule_tac y ="of_nat fb"  in word_plus_mono_right[OF _  is_aligned_no_overflow',rotated])
      apply simp+
     apply (rule word_of_nat_less)
     apply simp
    apply (simp add:p_assoc_help mask_def)
   apply (simp add: max_free_index_def)
  apply (clarsimp simp: maskedAsFull_def is_derived'_def badge_derived'_def
                        gen_isCap_simps capMasterCap_def cte_wp_at_ctes_of
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
  by (case_tac x, auto simp:maskedAsFull_def gen_isCap_simps)

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
      apply (rule corres_if3)
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

crunch transferCapsToSlots
  for reply_projs[wp]: "\<lambda>s. P (replyNexts_of s) (replyPrevs_of s) (replyTCBs_of s) (replySCs_of s)"
  and pred_tcb_at'[wp]: "pred_tcb_at' proj P p"
  and valid_replies' [wp]: valid_replies'
  and pspace_bounded'[wp]: pspace_bounded'

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

crunch setExtraBadge, doIPCTransfer
  for sch_act [wp]: "\<lambda>s. P (ksSchedulerAction s)"
  (wp: crunch_wps mapME_wp' simp: zipWithM_x_mapM)

crunch setExtraBadge
  for ksCurThread[wp]: "\<lambda>s. P (ksCurThread s)"
  and ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  and obj_at' [wp]: "\<lambda>s. P' (obj_at' P p s)"
  and queues [wp]: "\<lambda>s. P (ksReadyQueues s)"
  and queuesL1 [wp]: "\<lambda>s. P (ksReadyQueuesL1Bitmap s)"
  and queuesL2 [wp]: "\<lambda>s. P (ksReadyQueuesL2Bitmap s)"
  and tcbSchedNexts_of[wp]: "\<lambda>s. P (tcbSchedNexts_of s)"
  and tcbSchedPrevs_of[wp]: "\<lambda>s. P (tcbSchedPrevs_of s)"
  and inQ_tcbs_of'[wp]: "\<lambda>s. P (inQ d p |< tcbs_of' s)"

crunch setExtraBadge
  for state_refs_of'[wp]: "\<lambda>s. P (state_refs_of' s)"

lemma tcts_state_refs_of'[wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of' s)\<rbrace>
     transferCapsToSlots ep buffer n caps slots mi
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  by (wp transferCapsToSlots_pres1)

crunch setExtraBadge
  for if_unsafe'[wp]: if_unsafe_then_cap'

lemma tcts_ifunsafe[wp]:
  "\<lbrace>\<lambda>s. if_unsafe_then_cap' s \<and> distinct slots \<and>
         (\<forall>x\<in>set slots.  cte_wp_at' (\<lambda>cte. cteCap cte = capability.NullCap) x s \<and>
             ex_cte_cap_to' x s)\<rbrace> transferCapsToSlots ep buffer n caps slots mi
   \<lbrace>\<lambda>rv. if_unsafe_then_cap'\<rbrace>"
  by (wp transferCapsToSlots_pres2 | simp)+

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

crunch setExtraBadge, transferCapsToSlots
  for ksDomSchedule[wp]: "\<lambda>s. P (ksDomSchedule s)"
  and ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"
  and ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  and replies_of'[wp]: "\<lambda>s. P (replies_of' s)"
  and tcbSchedPrevs_of[wp]: "\<lambda>s. P (tcbSchedPrevs_of s)"
  and tcbSchedNexts_of[wp]: "\<lambda>s. P (tcbSchedNexts_of s)"
  and sym_heap_sched_pointers[wp]: sym_heap_sched_pointers
  and valid_sched_pointers[wp]: valid_sched_pointers
  and ksReadyQueues[wp]: "\<lambda>s. P (ksReadyQueues s)"
  and ksReadyQueuesL1Bitmap[wp]: "\<lambda>s. P (ksReadyQueuesL1Bitmap s)"
  and ksReadyQueuesL2Bitmap[wp]: "\<lambda>s. P (ksReadyQueuesL2Bitmap s)"
  (rule: sym_heap_sched_pointers_lift)

lemma transferCapsToSlots_invs[wp]:
  "\<lbrace>\<lambda>s. invs' s \<and> distinct slots
        \<and> (\<forall>x \<in> set slots. cte_wp_at' (\<lambda>cte. cteCap cte = NullCap) x s)
        \<and> (\<forall>x \<in> set slots. ex_cte_cap_to' x s)
        \<and> (\<forall>x \<in> set slots. real_cte_at' x s)
        \<and> length slots \<le> 1
        \<and> transferCaps_srcs caps s\<rbrace>
   transferCapsToSlots ep buffer n caps slots mi
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: invs'_def valid_dom_schedule'_def)
  apply (wp valid_irq_node_lift valid_bitmaps_lift)
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
   (tcb_at' receiver and valid_objs' and valid_replies' and
    pspace_aligned' and pspace_distinct' and pspace_bounded' and pspace_canonical'
    and pspace_in_kernel_mappings' and no_0_obj' and valid_mdb'
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

end

crunch transferCaps
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n n p s)"

global_interpretation transferCaps: typ_at_all_props' "transferCaps info caps endpoint receiver receiveBuffer"
  by typ_at_props'

context begin interpretation Arch . (*FIXME: arch-split*)

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
  "isArchCap isFrameCap (RetypeDecls_H.maskCapRights R c) = isArchCap isFrameCap c"
  apply (case_tac c; simp add: isCap_simps isArchCap_def maskCapRights_def)
  apply (rename_tac arch_capability)
  apply (case_tac arch_capability; simp add: isCap_simps RISCV64_H.maskCapRights_def)
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
                                  capBadge_def RISCV64_H.updateCapData_def
                           split: if_split_asm)
   apply fastforce+
  done

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

end

crunch copyMRs
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n n p s)"
  (wp: crunch_wps)

global_interpretation copyMRs: typ_at_all_props' "copyMRs s sb r rb n"
  by typ_at_props'

context begin interpretation Arch . (*FIXME: arch-split*)

lemma copy_mrs_invs'[wp]:
  "copyMRs s sb r rb n \<lbrace>invs'\<rbrace>"
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
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>
     setMRs t buf mrs \<lbrace>\<lambda>rv s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  "\<lbrace>\<lambda>s. P (state_refs_of' s)\<rbrace>
     setMRs t buf mrs
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  "\<lbrace>if_unsafe_then_cap'\<rbrace> setMRs t buf mrs \<lbrace>\<lambda>rv. if_unsafe_then_cap'\<rbrace>"
  by (simp add: setMRs_def zipWithM_x_mapM split_def storeWordUser_def | wp crunch_wps)+

crunch setMRs
  for no_0_obj'[wp]: no_0_obj'
  (wp: crunch_wps simp: crunch_simps)

lemma copyMRs_invs_bits[wp]:
  "\<lbrace>valid_pspace'\<rbrace> copyMRs s sb r rb n \<lbrace>\<lambda>rv. valid_pspace'\<rbrace>"
  "\<lbrace>\<lambda>s. P (state_refs_of' s)\<rbrace>
      copyMRs s sb r rb n
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
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
  and reply_projs[wp]: "\<lambda>s. P (replyNexts_of s) (replyPrevs_of s) (replyTCBs_of s) (replySCs_of s)"
  and valid_replies' [wp]: valid_replies'
  and pspace_bounded'[wp]: pspace_bounded'
  (wp: threadSet_ctes_of crunch_wps)

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
  (tcb_at' sender and tcb_at' receiver and valid_objs' and valid_replies'
   and pspace_aligned' and pspace_distinct' and pspace_bounded' and pspace_canonical'
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

end

crunch doNormalTransfer
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n n p s)"
  (wp: crunch_wps)

global_interpretation doNormalTransfer: typ_at_all_props' "doNormalTransfer s sb e b g r rb"
  by typ_at_props'

lemma doNormal_invs'[wp]:
  "doNormalTransfer sender send_buf ep badge can_grant receiver recv_buf \<lbrace>invs'\<rbrace>"
  unfolding doNormalTransfer_def
  by (wpsimp wp: hoare_vcg_const_Ball_lift)

crunch doNormalTransfer
  for pspace_aligned'[wp]: pspace_aligned'
  and pspace_distinct'[wp]: pspace_distinct'
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

context begin interpretation Arch . (*FIXME: arch-split*)

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
  "corres (=) (tcb_at t and valid_objs and pspace_aligned and pspace_distinct) \<top>
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
   apply (clarsimp simp: threadGet_getObject)
   apply (rule corres_guard_imp)
     apply (rule corres_split[OF getObject_TCB_corres])
       apply (rename_tac tcb tcb')
       apply (rule_tac P="\<lambda>s. (bound (tcb_sched_context tcb) \<longrightarrow> sc_at (the (tcb_sched_context tcb)) s)
                              \<and> pspace_aligned s \<and> pspace_distinct s"
                    in corres_inst)
       apply (case_tac "tcb_sched_context tcb"; case_tac "tcbSchedContext tcb'";
              clarsimp simp: tcb_relation_def)
       apply (rule corres_underlying_split)
          apply (rule_tac Q'="sc_at' (the (tcbSchedContext tcb'))" and P'=\<top> in corres_cross_add_guard)
           apply (fastforce dest!: state_relationD intro!: sc_at_cross simp: obj_at'_def)[1]
          apply (rule corres_guard_imp)
            apply (rule schedContextUpdateConsumed_corres)
           apply (wpsimp simp: sched_context_update_consumed_def)+
    apply (fastforce dest!: valid_tcb_objs simp: valid_tcb_def valid_bound_obj_def obj_at_def)
   apply clarsimp
  apply (corresKsimp corres: makeArchFaultMessage_corres)
  done

crunch makeFaultMessage
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n n p s)"

end

global_interpretation makeFaultMessage: typ_at_all_props' "makeFaultMessage x t"
  by typ_at_props'

lemmas threadget_fault_corres =
          threadGet_corres [where r = fault_rel_optionation
                              and f = tcb_fault and f' = tcbFault,
                            simplified tcb_relation_def, simplified]

context begin interpretation Arch . (*FIXME: arch-split RT*)

crunch make_fault_msg
  for in_user_Frame[wp]: "in_user_frame buffer"

lemma makeFaultMessage_valid_ipc_buffer_ptr'[wp]:
  "makeFaultMessage x thread \<lbrace>valid_ipc_buffer_ptr' p\<rbrace>"
  unfolding valid_ipc_buffer_ptr'_def2
  apply (wpsimp wp: hoare_vcg_all_lift)
  done

lemma doFaultTransfer_corres:
  "corres dc
    (valid_objs and pspace_distinct and pspace_aligned
     and obj_at (\<lambda>ko. \<exists>tcb ft. ko = TCB tcb \<and> tcb_fault tcb = Some ft) sender
     and tcb_at receiver and case_option \<top> in_user_frame recv_buf
     and pspace_aligned and pspace_distinct)
    (case_option \<top> valid_ipc_buffer_ptr' recv_buf)
    (do_fault_transfer badge sender receiver recv_buf)
    (doFaultTransfer badge sender receiver recv_buf)"
  apply (clarsimp simp: do_fault_transfer_def doFaultTransfer_def split_def
                        RISCV64_H.badgeRegister_def badge_register_def)
  apply (rule_tac Q="\<lambda>fault. valid_objs and pspace_distinct and pspace_aligned and
                             K (\<exists>f. fault = Some f) and
                             tcb_at sender and tcb_at receiver and
                             case_option \<top> in_user_frame recv_buf"
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

crunch makeFaultMessage
  for invs'[wp]: invs'

lemma doFaultTransfer_invs'[wp]:
  "doFaultTransfer badge sender receiver recv_buf \<lbrace>invs'\<rbrace>"
  by (wpsimp simp: doFaultTransfer_def split_def split: option.split)

lemma doIPCTransfer_corres:
  "corres dc
     (tcb_at s and tcb_at r and valid_objs and pspace_aligned
        and valid_list and valid_arch_state
        and pspace_distinct and valid_mdb and cur_tcb
        and (\<lambda>s. case ep of Some x \<Rightarrow> ep_at x s | _ \<Rightarrow> True))
     (tcb_at' s and tcb_at' r and valid_pspace'
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
     apply (rule stronger_corres_guard_imp)
       apply (rule lookupIPCBuffer_corres')
      apply auto[2]
    apply (rule corres_underlying_split [OF _ _ thread_get_sp threadGet_inv])
     apply (rule corres_guard_imp)
       apply (rule threadget_fault_corres)
      apply simp
     defer
     apply (rule corres_guard_imp)
       apply (subst case_option_If)+
       apply (rule corres_if3)
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
  and state_refs_of[wp]: "\<lambda>s. P (state_refs_of' s)"
  and typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n n p s)"
  and irq_node'[wp]: "\<lambda>s. P (irq_node' s)"
  and valid_arch_state'[wp]: "valid_arch_state'"
  (wp: crunch_wps
   simp: zipWithM_x_mapM ball_conj_distrib)

end

global_interpretation doIPCTransfer: typ_at_all_props' "doIPCTransfer s e b g r"
  by typ_at_props'

context begin interpretation Arch . (*FIXME: arch-split*)

lemmas dit_irq_node'[wp] = valid_irq_node_lift [OF doIPCTransfer_irq_node' doIPCTransfer_typ_at']

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

declare asUser_irq_handlers'[wp]

crunch doIPCTransfer
  for objs'[wp]: "valid_objs'"
  and global_refs'[wp]: "valid_global_refs'"
  and irq_handlers'[wp]: "valid_irq_handlers'"
  and irq_states'[wp]: "valid_irq_states'"
  and irqs_masked'[wp]: "irqs_masked'"
  and invs'[wp]: invs'
  (wp: crunch_wps hoare_vcg_const_Ball_lift
   simp: zipWithM_x_mapM ball_conj_distrib
   rule: irqs_masked_lift)

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
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n n p s)"
  and ct'[wp]: "\<lambda>s. P (ksCurThread s)"
  and nosch[wp]: "\<lambda>s. P (ksSchedulerAction s)"

end

global_interpretation handleFaultReply: typ_at_all_props' "handleFaultReply x t l m"
  by typ_at_props'

lemma doIPCTransfer_sch_act_simple [wp]:
  "\<lbrace>sch_act_simple\<rbrace> doIPCTransfer sender endpoint badge grant receiver \<lbrace>\<lambda>_. sch_act_simple\<rbrace>"
  by (simp add: sch_act_simple_def, wp)

crunch finaliseCapTrue_standin
  for ct'[wp]: "\<lambda>s. P (ksCurThread s)"
  (wp: crunch_wps simp: crunch_simps)

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

crunch unbindMaybeNotification, schedContextMaybeUnbindNtfn, isFinalCapability,
         cleanReply
  for sch_act_not[wp]: "sch_act_not t"
  (wp: crunch_wps simp: crunch_simps)

context begin interpretation Arch . (*FIXME: arch-split*)

crunch handleFaultReply
  for pred_tcb_at'[wp]: "pred_tcb_at' proj P t"

crunch handleFaultReply
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
   \<lbrace> \<lambda>_. invs \<rbrace>"
  unfolding bind_sc_reply_def
  supply if_weak_cong[cong del] if_split[split del]
  apply (rule bind_wp[OF _ gscrpls_sp])
  apply (rename_tac sc_replies')
  apply (case_tac sc_replies'; simp)
   apply (wpsimp wp: sched_context_donate_invs)
     apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                     wp: valid_irq_node_typ set_reply_sc_valid_replies_already_BlockedOnReply)
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
                         valid_sc_typ_list_all_reply)
    apply (wpsimp wp: set_sc_replies_valid_replies update_sched_context_valid_idle)
   apply (wpsimp simp: get_simple_ko_def get_object_def
                   wp: valid_sc_typ_list_all_reply)
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

lemma update_sk_obj_ref_in_correct_ready_q[wp]:
  "update_sk_obj_ref C f ref new \<lbrace>in_correct_ready_q\<rbrace>"
  by (wpsimp wp: in_correct_ready_q_lift)

crunch update_sk_obj_ref
  for ready_qs_distinct[wp]: ready_qs_distinct
  (rule: ready_qs_distinct_lift)

crunch update_sched_context
  for in_correct_ready_q[wp]: in_correct_ready_q
  (wp: in_correct_ready_q_lift)

crunch bind_sc_reply
  for release_queue[wp]: "\<lambda>s. P (release_queue s)"
  and in_correct_ready_q[wp]: in_correct_ready_q
  and ready_queues[wp]: "\<lambda>s. P (ready_queues s)"
  and ready_qs_distinct[wp]: ready_qs_distinct
  and ready_queues_runnable [wp]: ready_queues_runnable
  and release_q_runnable[wp]: release_q_runnable
  and ep_queues_blocked[wp]: ep_queues_blocked
  and ntfn_queues_blocked[wp]: ntfn_queues_blocked
  (wp: crunch_wps ready_qs_distinct_lift ready_queues_runnable_lift release_q_runnable_lift
       ep_queues_blocked_lift ntfn_queues_blocked_lift
   ignore: update_sk_obj_ref)

crunch test_reschedule
  for in_correct_ready_q[wp]: in_correct_ready_q
  and ready_qs_distinct[wp]: ready_qs_distinct

lemma sched_context_donate_in_correct_ready_q[wp]:
  "sched_context_donate sc_ptr tcb_ptr \<lbrace>in_correct_ready_q\<rbrace>"
  apply (clarsimp simp: sched_context_donate_def set_tcb_obj_ref_thread_set)
  apply (wpsimp wp: thread_set_in_correct_ready_q)
  done

crunch thread_set, update_sched_context
  for ready_qs_distinct[wp]: ready_qs_distinct
  (wp: ready_qs_distinct_lift)

lemma sched_context_donate_ready_qs_distinct[wp]:
  "sched_context_donate sc_ptr tcb_ptr \<lbrace>ready_qs_distinct\<rbrace>"
  apply (clarsimp simp: sched_context_donate_def set_tcb_obj_ref_thread_set)
  apply (wpsimp wp: thread_set_in_correct_ready_q)
  done

crunch reply_push
  for in_correct_ready_q[wp]: in_correct_ready_q
  and ready_qs_distinct[wp]: ready_qs_distinct
  (wp: crunch_wps)

crunch bindScReply
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and tcbSchedNexts_of[wp]: "\<lambda>s. P (tcbSchedNexts_of s)"
  and tcbSchedPrevs_of[wp]: "\<lambda>s. P (tcbSchedPrevs_of s)"
  and sym_heap_sched_pointers[wp]: sym_heap_sched_pointers
  and valid_sched_pointers[wp]: valid_sched_pointers
  (simp: crunch_simps)

lemma set_thread_state_release_q_runnable_not_in_release_q:
  "\<lbrace>release_q_runnable and not_in_release_q t\<rbrace> set_thread_state t st \<lbrace>\<lambda>_. release_q_runnable\<rbrace>"
  unfolding release_q_runnable_def
  apply (rule hoare_weaken_pre)
   apply (rule_tac Q="\<lambda>x s. \<forall>t'\<in>set x. st_tcb_at runnable t' s \<and> t \<notin> set x"
                in hoare_lift_Pf_pre_conj[where g=release_queue])
    apply (wpsimp wp: hoare_vcg_ball_lift sts_st_tcb_at_other)
   apply wpsimp
  apply (fastforce simp: not_in_release_q_def)
  done

crunch set_reply_obj_ref
  for ready_queues_runnable[wp]: ready_queues_runnable
  and release_q_runnable[wp]: release_q_runnable
  and ntfn_queued[wp]: "\<lambda>s. P (ntfn_queued ntfn_ptr s)"
  (wp: ready_queues_runnable_lift release_q_runnable_lift ntfn_queued_lift)

lemma not_ep_blocked_not_ep_queued:
  "\<lbrakk>st_tcb_at (\<lambda>ts. ep_blocked ts = None) tcbPtr s; ep_queues_blocked s\<rbrakk> \<Longrightarrow> \<not> ep_queued tcbPtr s"
  apply (clarsimp simp: ep_queues_blocked_def opt_map_def ep_blocked_def eps_of_kh_def ep_queued_def
                        in_ep_queue_at_def st_tcb_at_def obj_at_def
                 split: option.splits)
  apply (rename_tac p ep)
  apply (drule_tac x=p in spec)
  apply clarsimp
  apply (fastforce split: Structures_A.thread_state.splits)
  done

lemma runnable_not_ep_queued:
  "\<lbrakk>st_tcb_at runnable tcbPtr s; ep_queues_blocked s\<rbrakk> \<Longrightarrow> \<not> ep_queued tcbPtr s"
  apply (rule not_ep_blocked_not_ep_queued)
   apply (force simp: pred_tcb_at_def obj_at_def ep_blocked_def
               split: Structures_A.thread_state.splits)
  apply fastforce
  done

lemma not_ntfn_blocked_not_ntfn_queued:
  "\<lbrakk>st_tcb_at (\<lambda>ts. ntfn_blocked ts = None) tcbPtr s; ntfn_queues_blocked s\<rbrakk>
   \<Longrightarrow> \<not> ntfn_queued tcbPtr s"
  apply (clarsimp simp: ntfn_queues_blocked_def opt_map_def ntfn_blocked_def ntfn_queued_def
                        in_ntfn_queue_at_def st_tcb_at_def obj_at_def
                 split: option.splits)
  apply (rename_tac p ntfn)
  apply (drule_tac x=p in spec)
  apply clarsimp
  apply (fastforce split: Structures_A.thread_state.splits)
  done

lemma runnable_not_ntfn_queued:
  "\<lbrakk>st_tcb_at runnable tcbPtr s; ntfn_queues_blocked s\<rbrakk> \<Longrightarrow> \<not> ntfn_queued tcbPtr s"
  apply (rule not_ntfn_blocked_not_ntfn_queued)
   apply (force simp: pred_tcb_at_def obj_at_def ntfn_blocked_def
               split: Structures_A.thread_state.splits)
  apply fastforce
  done

defs not_sched_linked_asrt_def:
  "not_sched_linked_asrt t \<equiv> \<lambda>s. \<not> is_sched_linked t s"

declare not_sched_linked_asrt_def[simp]

defs reply_object_asrt_def:
  "reply_object_asrt t \<equiv> \<lambda>s. st_tcb_at' (\<lambda>st. is_replyState st \<longrightarrow> replyObject st = None) t s"

declare reply_object_asrt_def[simp]

lemma replyPush_corres:
  "can_donate = can_donate' \<Longrightarrow>
   corres dc (valid_replies and pspace_aligned and pspace_distinct and valid_objs
              and K (caller \<noteq> idle_thread_ptr) and tcb_at callee and active_scs_valid
              and (\<lambda>s. distinct (release_queue s)) and in_correct_ready_q and ready_qs_distinct
              and ready_queues_runnable and release_q_runnable
              and ready_or_release
              and ep_queues_blocked and ntfn_queues_blocked
              and st_tcb_at (\<lambda>st. reply_object st = None) caller and ex_nonz_cap_to reply_ptr
              and reply_sc_reply_at (\<lambda>tptr. tptr = None) reply_ptr
              and reply_tcb_reply_at (\<lambda>tptr. tptr = None) reply_ptr
              and weak_valid_sched_action and scheduler_act_not caller
              and not_queued caller and not_in_release_q caller
              and not ep_queued caller and not ntfn_queued caller
              and (\<lambda>s. reply_ptr \<notin> fst ` replies_with_sc s)
              and (\<lambda>s. sym_refs (\<lambda>p. if p = caller
                                     then tcb_non_st_state_refs_of s caller
                                     else state_refs_of s p))
              and valid_idle)
   (sym_heap_sched_pointers and valid_sched_pointers and valid_objs'
    and pspace_aligned' and pspace_distinct' and pspace_bounded'
    and valid_replies'_sc_asrt reply_ptr
    and (\<lambda>s. \<not> is_sched_linked caller s))
   (reply_push caller callee reply_ptr can_donate)
   (replyPush caller callee reply_ptr can_donate')"
  apply add_valid_idle'
  unfolding reply_push_def replyPush_def
  apply clarsimp
  apply (rule corres_stateAssert_implied[where P'=\<top>, simplified, rotated])
   apply (clarsimp simp: valid_reply'_def obj_at'_def)
  apply (rule corres_stateAssert_implied[where P'=\<top>, simplified, rotated],clarsimp)
  apply (rule corres_stateAssert_ignore, simp)
  apply (rule corres_stateAssert_ignore, simp)
  apply (rule corres_symb_exec_r_conj_ex_abs_forwards[OF _ get_reply_sp', rotated]; (solves wpsimp)?)
   apply wpsimp
   apply (clarsimp simp: ex_abs_def)
   apply (force intro!: reply_at_cross
                  simp: reply_at_ppred_def obj_at_def is_reply_def)
  apply (rule corres_assert_gen_asm_cross_forwards)
   apply (clarsimp simp: obj_at'_def)
   apply (frule state_relation_pspace_relation)
   apply (clarsimp simp: pspace_relation_heap_pspace_relation)
   apply (force dest!: replies_relation_reply_relation_conc
                 simp: reply_at_ppred_def obj_at_def reply_relation_def)
  apply (rule corres_stateAssert_ignore)
   apply clarsimp
   apply (frule (3) st_tcb_at_coerce_concrete)
   apply (clarsimp simp: st_tcb_at'_def obj_at'_def st_tcb_at_def pred_tcb_at_def obj_at_def
                         thread_state_relation_def)
   apply (rename_tac st', case_tac "st'"; clarsimp simp: isReply_def)
  apply (rule stronger_corres_guard_imp)
    apply (simp add: get_tcb_obj_ref_def)
    apply (rule corres_split_eqr[OF threadGet_corres])
       apply (clarsimp simp: tcb_relation_def)
      apply (rule corres_split_eqr[OF threadGet_corres])
         apply (clarsimp simp: tcb_relation_def)
        apply (rule corres_split [OF replyTCB_update_corres])
          apply (rule corres_split [OF setThreadState_corres])
             apply simp
            apply (rule corres_when2, clarsimp)
            apply (rule corres_split [OF bindScReply_corres schedContextDonate_corres])
             apply (wpsimp wp: sc_at_typ_at)
            apply (wpsimp wp: sym_heap_sched_pointers_lift)
           apply simp
           apply (wpsimp wp: sts_valid_replies hoare_vcg_imp_lift'
                             hoare_vcg_all_lift sts_in_replies_blocked
                             set_thread_state_weak_valid_sched_action
                             set_thread_state_ready_queues_runnable_not_queued
                             set_thread_state_release_q_runnable_not_in_release_q
                             set_thread_state_ep_queues_blocked_not_queued
                             set_thread_state_ntfn_queues_blocked_not_queued)
          apply (wpsimp wp: hoare_vcg_imp_lift' sts_invs_minor'
                            setThreadState_sched_pointers_valid_sched_pointers)
         apply clarsimp
         apply (wpsimp wp: hoare_vcg_imp_lift' hoare_vcg_all_lift)
        apply (clarsimp simp: cong: conj_cong)
        apply (wpsimp wp: hoare_vcg_imp_lift' hoare_vcg_all_lift updateReply_valid_objs')
       apply (wpsimp wp: thread_get_wp)
      apply (wpsimp wp: threadGet_wp)
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
       by (erule delta_sym_refs; clarsimp split: if_splits;
           fastforce dest: reply_tcb_reply_at_ReplyTCB_in_state_refs_of
                           st_tcb_at_TCBReply_in_state_refs_of)
    apply (fastforce dest: runnable_not_ep_queued)
   apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb is_reply)
  apply (clarsimp simp: valid_reply'_def obj_at'_def)
  done

crunch handle_fault_reply
  for pspace_aligned[wp]: pspace_aligned
  and pspace_distinct[wp]: pspace_distinct

lemma refillReady_sp:
  "\<lbrace>P\<rbrace>
   refillReady scp
   \<lbrace>\<lambda>rv s. P s \<and> (\<exists>sc. scs_of' s scp = Some sc \<and> rv = (rTime (refillHd sc) \<le> ksCurTime s))\<rbrace>"
  by (wpsimp wp: refillReady_wp)

lemma refillSufficient_sp:
  "\<lbrace>P\<rbrace>
   getRefillSufficient scp usage
   \<lbrace>\<lambda>rv s. P s \<and> (\<exists>sc. scs_of' s scp = Some sc \<and> rv = (refillSufficient usage (refillHd sc)))\<rbrace>"
  by wpsimp

lemma cap_in_tcbFaultHandlerSlot:
  "\<lbrakk>ko_at' (tcb :: tcb) t s; valid_tcbs' s\<rbrakk>
   \<Longrightarrow> \<exists>cap. cte_wp_at' (\<lambda>c. cteCap c = cap) (t + 2 ^ cte_level_bits * tcbFaultHandlerSlot) s
             \<and> valid_cap' cap s
             \<and> (\<exists>n\<in>dom tcb_cte_cases. cte_wp_at' (\<lambda>cte. cteCap cte = cap) (t + n) s)"
  supply raw_tcb_cte_cases_simps[simp] (* FIXME arch-split RT: legacy, try use tcb_cte_cases_neqs *)
  apply (rule_tac x="cteCap (tcbFaultHandler tcb)" in exI)
  apply (rule conjI)
   apply (simp add: cte_wp_at_cases')
   apply (rule disjI2)
   apply (rule_tac x="2 ^ cte_level_bits * tcbFaultHandlerSlot" in exI)
   apply (fastforce simp: tcbFaultHandlerSlot_def obj_at'_def objBits_simps' cte_level_bits_def)
  apply (frule (1) ko_at'_valid_tcbs'_valid_tcb')
  apply (rule conjI)
   apply (clarsimp simp: valid_tcb'_def tcb_cte_cases_def cteSizeBits_def)
  apply (rule_tac x="tcbFaultHandlerSlot << cteSizeBits" in bexI)
   apply (fastforce elim: cte_wp_at_tcbI'
                    simp: tcbFaultHandlerSlot_def obj_at'_def objBitsKO_def cteSizeBits_def)
  apply (fastforce simp: tcbFaultHandlerSlot_def cteSizeBits_def)
  done

lemma cap_in_tcbTimeoutHandlerSlot:
  "\<lbrakk>ko_at' (tcb :: tcb) t s; valid_tcbs' s\<rbrakk>
   \<Longrightarrow> \<exists>cap. cte_wp_at' (\<lambda>c. cteCap c = cap) (t + 2 ^ cte_level_bits * tcbTimeoutHandlerSlot) s
             \<and> valid_cap' cap s
             \<and> (\<exists>n\<in>dom tcb_cte_cases. cte_wp_at' (\<lambda>cte. cteCap cte = cap) (t + n) s)"
  supply raw_tcb_cte_cases_simps[simp] (* FIXME arch-split RT: legacy, try use tcb_cte_cases_neqs *)
  apply (rule_tac x="cteCap (tcbTimeoutHandler tcb)" in exI)
  apply (rule conjI)
   apply (simp add: cte_wp_at_cases')
   apply (rule disjI2)
   apply (rule_tac x="2 ^ cte_level_bits * tcbTimeoutHandlerSlot" in exI)
   apply (fastforce simp: tcbTimeoutHandlerSlot_def obj_at'_def objBits_simps' cte_level_bits_def)
  apply (frule (1) ko_at'_valid_tcbs'_valid_tcb')
  apply (rule conjI)
   apply (clarsimp simp: valid_tcb'_def tcb_cte_cases_def cteSizeBits_def)
  apply (rule_tac x="tcbTimeoutHandlerSlot << cteSizeBits" in bexI)
   apply (fastforce elim: cte_wp_at_tcbI'
                    simp: tcbTimeoutHandlerSlot_def obj_at'_def objBitsKO_def cteSizeBits_def)
  apply (fastforce simp: tcbTimeoutHandlerSlot_def cteSizeBits_def)
  done

lemma ko_at_cte_tcbTimeoutHandler:
  "ko_at' tcb p s
   \<Longrightarrow> cte_wp_at' (\<lambda>x. x = tcbTimeoutHandler tcb) (p + 2 ^ cte_level_bits * tcbTimeoutHandlerSlot) s"
  apply (clarsimp simp: obj_at'_def objBits_simps)
  apply (erule (2) cte_wp_at_tcbI')
   apply (fastforce simp add: tcb_cte_cases_def tcbTimeoutHandlerSlot_def cte_level_bits_def cteSizeBits_def)
  apply simp
  done

lemma isValidTimeoutHandler_sp:
  "\<lbrace>P\<rbrace>
   isValidTimeoutHandler x
   \<lbrace>\<lambda>rv s. P s \<and> (\<exists>ko. ko_at' ko x s \<and> (rv = is_EndpointCap (cteCap (tcbTimeoutHandler ko))))\<rbrace>"
  unfolding isValidTimeoutHandler_def getThreadTimeoutHandlerSlot_def
  apply (wpsimp wp: getTCB_wp getSlotCap_wp simp: locateSlot_conv)
  apply (clarsimp simp: is_EndpointCap_def )
  apply normalise_obj_at'
  apply (frule ko_at_cte_tcbTimeoutHandler)
  apply (fastforce simp: cte_wp_at'_def)
  done

declare no_fail_getSlotCap [wp]

crunch doIPCTransfer, possibleSwitchTo
  for pred_tcb_at'[wp]: "pred_tcb_at' proj P t"
  (wp: mapM_wp' crunch_wps simp: zipWithM_x_mapM)

crunch doIPCTransfer, possibleSwitchTo
  for ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  and ksDomSchedule[wp]: "\<lambda>s. P (ksDomSchedule s)"
  (wp: crunch_wps simp: zipWithM_x_mapM)

crunch doIPCTransfer
  for tcbDomain_obj_at'[wp]: "obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t"
  (wp: crunch_wps constOnFailure_wp simp: crunch_simps)

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
  apply (rule bind_wp[OF _ thread_get_sp])
  apply (rule bind_wp[OF _ thread_get_sp])
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

lemma det_wp_ordered_insert[wp]:
  "det_wp (\<lambda>s. (\<forall>t \<in> set ts. \<exists>v. f t s = Some v) \<and> (\<exists>v. f t s = Some v)) (ordered_insert t ts f R)"
  apply (clarsimp simp: ordered_insert_def)
  apply wpsimp
  done

lemmas no_fail_ordered_insert[wp] = det_wp_no_fail[OF det_wp_ordered_insert]

lemma det_wp_tcb_append[wp]:
  "det_wp (\<lambda>s. (\<forall>t \<in> set qs. tcb_at t s) \<and> tcb_at tptr s) (tcb_append tptr qs)"
  unfolding tcb_append_def
  apply wpsimp
  apply (fastforce intro: no_ofailD[OF thread_read_no_ofail])
  done

lemmas no_fail_tcb_append[wp] = det_wp_no_fail[OF det_wp_tcb_append]

lemma det_wp_tcb_append_set_endpoint[wp]:
  "det_wp
     (\<lambda>s. (\<forall>t \<in> set qs. tcb_at t s) \<and> tcb_at tptr s \<and> ep_at epPtr s)
     (do q' \<leftarrow> tcb_append tptr qs; set_endpoint epPtr (update_ep_queue ep q' isRecv) od)"
  by wpsimp

lemmas no_fail_tcb_append_set_endpoint = det_wp_no_fail[OF det_wp_tcb_append_set_endpoint]

lemma tcb_append_set_endpoint_empty_fail:
  "empty_fail (do q' \<leftarrow> tcb_append tptr qs; set_endpoint epPtr (update_ep_queue ep q' isRecv) od)"
  by wpsimp

lemmas tcb_append_rules =
  det_wp_tcb_append no_fail_tcb_append
  det_wp_tcb_append_set_endpoint no_fail_tcb_append_set_endpoint
  tcb_append_empty_fail tcb_append_set_endpoint_empty_fail

crunch orderedInsert
  for valid_objs'[wp]: valid_objs'
  and obj_at'_endpoint[wp]: "\<lambda>s. Q (obj_at' (\<lambda>ep. (P :: endpoint \<Rightarrow> bool) ep) epPtr s)"
  and obj_at'_notification[wp]: "\<lambda>s. Q (obj_at' (\<lambda>ep. (P :: notification \<Rightarrow> bool) ep) epPtr s)"
  (wp: crunch_wps)

method ipc_append =
  (rule det_wp_pre no_fail_pre, rule tcb_append_rules, fastforce)[1] | wpsimp

lemma threadGet_rcorres:
  "(\<And>tcb tcb'. tcb_relation tcb tcb' \<Longrightarrow> rrel (f tcb) (f' tcb'))
   \<Longrightarrow>rcorres
        (\<lambda>s s'. tcbs_relation s s' \<and> tcb_at t s)
        (gets_the (thread_read f t)) (gets_the (threadRead f' t))
        (\<lambda>rv rv' _ _. rrel rv rv')"
  apply (rule rcorres_gets_the_fwd)
   apply (clarsimp simp: thread_read_Some_tcbs_of obj_at_def is_tcb_def)
   apply (rename_tac ko, case_tac ko; clarsimp)
   apply (frule threadRead_SomeD)
   apply (fastforce simp: map_relation_def tcbs_of_kh_def opt_map_def obj_at'_def
                   split: option.splits)
  apply wpsimp
  done

lemma tcbAppend_rcorres:
  "rcorres
     (\<lambda>s s'. (sorted_wrt (img_ord (prios_of s) (opt_ord_rel (\<lambda>x y. y \<le> x))) ts)
             \<and> list_queue_relation ts q (tcbSchedNexts_of s') (tcbSchedPrevs_of s')
             \<and> heap_pspace_relation s s' \<and> sym_heap_sched_pointers s'
             \<and> pspace_aligned s \<and> pspace_distinct s
             \<and> \<not> is_sched_linked t s' \<and> t \<notin> set ts \<and> (\<forall>t \<in> set ts. tcb_at t s) \<and> tcb_at t s)
     (tcb_append t ts) (tcbAppend t q)
     (\<lambda>ts' q' s s'. list_queue_relation ts' q' (tcbSchedNexts_of s') (tcbSchedPrevs_of s'))"
  apply (clarsimp simp: tcb_append_def tcbAppend_def)
  apply (rule rcorres_stateAssert_r_fwd)
  apply (rcorres rcorres: orderedInsert_rcorres threadGet_rcorres
                    simp: tcb_relation_def)
  apply (fastforce intro!: tcb_at_cross
                     simp: thread_read_Some_tcbs_of pspace_relation_heap_pspace_relation)
  done

lemma tcbAppend_rcorres_other:
  "rcorres
     (\<lambda>s s'. list_queue_relation ts q (tcbSchedNexts_of s') (tcbSchedPrevs_of s')
             \<and> list_queue_relation ts' q' (tcbSchedNexts_of s') (tcbSchedPrevs_of s')
             \<and> heap_pspace_relation s s' \<and> sym_heap_sched_pointers s'
             \<and> pspace_aligned s \<and> pspace_distinct s
             \<and> t \<notin> set ts \<and> set ts \<inter> set ts' = {} \<and> tcb_at t s \<and> (\<forall>t \<in> set ts'. tcb_at t s))
     (tcb_append t ts') (tcbAppend t q')
     (\<lambda>_ _ s s'. list_queue_relation ts q (tcbSchedNexts_of s') (tcbSchedPrevs_of s'))"
  apply (clarsimp simp: tcb_append_def tcbAppend_def)
  apply (rule rcorres_stateAssert_r_fwd)
  apply (rcorres rcorres: orderedInsert_rcorres_other threadGet_rcorres
                    simp: tcb_relation_def)
  apply (fastforce intro!: tcb_at_cross simp: pspace_relation_heap_pspace_relation)
  done

lemma tcbEPAppend_corres:
  "\<lbrakk>tcb_ptr = tcbPtr; ep_ptr = epPtr\<rbrakk> \<Longrightarrow>
   corres dc
     (not ep_queued tcbPtr and not ntfn_queued tcbPtr
      and not_queued tcbPtr and not_in_release_q tcbPtr and ep_at ep_ptr and tcb_at tcb_ptr
      and ep_queues_blocked and ntfn_queues_blocked and ready_queues_runnable and release_q_runnable
      and valid_objs and sorted_ipc_queues and in_correct_ready_q and ready_qs_distinct
      and ready_or_release and pspace_aligned and pspace_distinct
      and K (state = (if is_recv then ReceiveEPState else SendEPState)))
     (\<lambda>s. sym_heap_sched_pointers s \<and> valid_objs' s \<and> \<not> is_sched_linked tcbPtr s
          \<and> obj_at' (\<lambda>ep. epState ep \<noteq> IdleEPState \<longrightarrow> epState ep = state) epPtr s)
     (tcb_ep_append tcb_ptr ep_ptr is_recv) (tcbEPAppend tcbPtr epPtr state)"
  supply if_split[split del] tcb_append_rv_wf'[wp del] tcb_append_rv_wf''[wp del]
         ghost_relation_wrapper_def[simp del] (*FIXME arch-split RT: not necessary after arch-split*)
         heap_ghost_relation_wrapper_def[simp del] (*FIXME arch-split RT: not necessary after arch-split*)
  apply (rule corres_gen_asm')
  apply (rule_tac Q'="tcb_at' tcb_ptr" in corres_cross_add_guard, fastforce intro!: tcb_at_cross)
  apply (rule_tac Q'=pspace_aligned' in corres_cross_add_guard)
   apply (fastforce dest!: pspace_aligned_cross)
  apply (rule_tac Q'=pspace_distinct' in corres_cross_add_guard)
   apply (fastforce dest!: pspace_distinct_cross)
  apply (rule_tac Q'="ep_at' epPtr" in corres_cross_add_guard, fastforce intro!: ep_at_cross)
  apply (clarsimp simp: tcb_ep_append_def tcbEPAppend_def)
  apply (rule corres_stateAssert_ignore, simp)
  apply (rule corres_split_forwards'[OF _ get_simple_ko_sp get_ep_sp'])
   apply (corres corres: getEndpoint_corres)
  apply (rename_tac ep ep')
  apply (rule_tac Q="\<lambda>s. ep_queues_of s ep_ptr = Some (ep_queue ep)
                         \<and> valid_ep ep s
                         \<and> (\<forall>t \<in> set (ep_queue ep). tcb_at t s)
                         \<and> sorted_wrt (img_ord (prios_of s) (opt_ord_rel (\<ge>))) (ep_queue ep)"
               in corres_cross_add_abs_guard)
   apply (intro context_conjI)
      apply (fastforce  simp: eps_of_kh_def obj_at_def opt_map_red)
     apply (fastforce intro: valid_objs_valid_ep simp: obj_at_def)
    apply (case_tac ep; clarsimp simp: valid_ep_def)
   apply (fastforce intro!: sorted_ipc_queues_endpoint_priority_ordered)
  apply (rule_tac Q'="\<lambda>s'. tcb_ptr \<notin> set (ep_queue ep)
                           \<and> (\<forall>t \<in> set (ep_queue ep). tcb_at' t s' \<and> sched_flag_set s' t)
                           \<and> list_queue_relation
                               (ep_queue ep) (epQueue ep')
                               (tcbSchedNexts_of s') (tcbSchedPrevs_of s')
                           \<and> (ep_queue ep = [] \<longleftrightarrow> epQueue ep' = emptyQueue)
                           \<and> sorted_wrt (img_ord (\<lambda>t. threadRead tcbPriority t s')
                                         (opt_ord_rel (\<ge>))) (ep_queue ep)"
               in corres_cross_add_guard)
   apply clarsimp
   apply (frule (3) in_ep_queue_sched_flag_set[where p=ep_ptr])
    apply fastforce
   apply (intro context_conjI)
       apply (clarsimp simp: in_ep_queue_at_def ep_queued_def)
      apply (fastforce intro!: tcb_at_cross)
     apply (fastforce intro!: ep_queues_relationD simp: opt_map_red obj_at'_def)
    apply (fastforce dest: list_queue_relation_Nil_iff_emptyHeadEndPtrs)
   apply clarsimp
   apply (frule (1) sorted_ipc_queues_endpoint_priority_ordered)
   apply (erule sorted_wrt_img_ord_eq_lift[THEN iffD1, rotated])
   apply (rename_tac t)
   apply (simp flip: thread_read_Some_tcbs_of)
   apply (rule_tac f="thread_read tcb_priority t" and g="threadRead tcbPriority t"
                in rcorres_rrel_eq)
      apply (rule threadGet_rcorres[where rrel="(=)"])
      apply (clarsimp simp: tcb_relation_def)
     apply (frule state_relation_pspace_relation)
     apply (clarsimp simp: pspace_relation_heap_pspace_relation)
    apply (fastforce intro!: no_ofailD[OF thread_read_no_ofail])
   apply (fastforce intro!: no_ofailD[OF no_ofail_threadRead_tcb_at'])
  apply (rule corres_stateAssert_ignore)
   apply (fastforce dest!: list_queue_relation_tcb_queue_head_end_valid)
  apply (rule corres_underlying_from_rcorres)
   apply (clarsimp simp: tcbAppend_def)
   apply (rule_tac R="\<lambda>_. ep_at' epPtr" in no_fail_bind[where P=P and Q=P for P, simplified])
     apply (wpsimp wp: no_fail_stateAssert hoare_vcg_if_lift2 hoare_drop_imps)
    apply wpsimp
   apply (wpsimp wp: no_fail_orderedInsert no_fail_stateAssert)
   apply (fast intro: no_ofailD[OF no_ofail_threadRead])
  apply (clarsimp simp: state_relation_def ghost_relation_heap_ghost_relation
                        pspace_relation_heap_pspace_relation heap_pspace_relation_def)
  apply (rule_tac Q="\<lambda>s s'. (s, s') \<in> state_relation" in rcorres_add_to_pre)
   apply (clarsimp simp: state_relation_def pspace_relation_heap_pspace_relation
                         heap_pspace_relation_def ghost_relation_heap_ghost_relation)
  apply (rcorres_conj_lift \<open>fastforce\<close> rule: det_wp_tcb_append_set_endpoint simp: tcbAppend_def)+
  apply (rule rcorres_conj_lift_fwd; (solves ipc_append)?)
    \<comment> \<open>eps_relation\<close>
   apply (clarsimp simp: tcbAppend_def bind_assoc)
   apply (rule rcorres_stateAssert_r_fwd)
   apply (rule_tac Q="\<lambda>ls q s s'. eps_relation s s'
                                  \<and> list_queue_relation
                                      ls q (tcbSchedNexts_of s') (tcbSchedPrevs_of s')
                                  \<and> ko_at (kernel_object.Endpoint ep) epPtr s
                                  \<and> (epState ep' \<noteq> IdleEPState \<longrightarrow> epState ep' = state)"
                in rcorres_split[rotated])
    apply (rcorres rcorres: orderedInsert_rcorres threadGet_rcorres
                      simp: tcb_append_def tcbAppend_def tcb_relation_def)
    apply (clarsimp simp: thread_read_Some_tcbs_of)
    apply (force simp: obj_at'_def split: if_splits)
   apply (rule rcorres_from_valid_det)
    apply wpsimp
    apply (clarsimp simp: obj_at_def is_ep_def)
   apply (drule in_set_endpoint)
   apply (wpsimp wp: updateEndpoint_wp)
   apply (clarsimp simp: eps_of_kh_def projectKO_opts_defs map_relation_def ep_relation_def
                         obj_at_def is_ep_def obj_at'_def valid_ep_def
                  split: if_splits Structures_A.endpoint.splits)
  apply (rcorres_conj_lift \<open>fastforce\<close> rule: det_wp_tcb_append_set_endpoint simp: tcbAppend_def)+
  apply (rule rcorres_conj_lift_fwd; (solves ipc_append)?)
   \<comment> \<open>ep_queues_relation\<close>
   apply (simp only: ep_queues_relation_def)
   apply (rule rcorres_allI_fwd; (solves wpsimp)?)
   apply (rename_tac p)
   apply (case_tac "p \<noteq> epPtr")
    apply (rcorres rcorres: tcbAppend_rcorres_other rcorres_allI rcorres_imp_lift
                        wp: set_endpoint_ep_queues_of_other updateEndpoint_epQueues_of_other)
    apply (clarsimp simp: in_ep_queue_at_def ep_queued_def heap_pspace_relation_def)
    apply (blast dest: ep_queues_disjoint)
   \<comment> \<open>p = epPtr\<close>
   apply (rule_tac Q="\<lambda>ls q s s'. ep_at epPtr s
                                  \<and> list_queue_relation
                                      ls q (tcbSchedNexts_of s') (tcbSchedPrevs_of s')"
                in rcorres_split[rotated])
    apply (rcorres rcorres: tcbAppend_rcorres)
    apply (clarsimp simp: heap_pspace_relation_def thread_read_Some_tcbs_of)
   apply (rule rcorres_from_valid_det; (solves wpsimp)?)
   apply (wpsimp wp: updateEndpoint_wp)
   apply (drule in_set_endpoint)
   apply (clarsimp simp: obj_at'_def projectKO_opts_defs)
   subgoal
     by (fastforce simp: projectKO_opts_defs opt_map_def eps_of_kh_def split: kernel_object.splits)
  apply (rule rcorres_conj_lift_fwd; (solves ipc_append)?)
    \<comment> \<open>ntfn_queues\<close>
   apply (simp only: ntfn_queues_relation_def)
   apply (rcorres rcorres: tcbAppend_rcorres_other
             rcorres_lift: rcorres_allI rcorres_imp_lift)
   apply (clarsimp simp: heap_pspace_relation_def in_ntfn_queue_at_def ntfn_queued_def)
   apply (blast dest: ep_queues_ntfn_queues_disjoint)
  apply (rule rcorres_conj_lift_fwd; (solves ipc_append)?)
   \<comment> \<open>ready_queues_relation\<close>
   apply (simp only: ready_queues_relation_def ready_queue_relation_def Let_def)
   apply (intro rcorres_allI_fwd; (solves ipc_append)?)
   apply (rename_tac d p)
   apply (rule_tac p="\<lambda>s. ready_queues s d p" in rcorres_lift_abs)
    apply (rule_tac p="\<lambda>s'. ksReadyQueues s' (d, p)" in rcorres_lift_conc)
     apply (rcorres rcorres: tcbAppend_rcorres_other
               rcorres_lift: rcorres_allI rcorres_imp_lift)
     apply (clarsimp simp: heap_pspace_relation_def not_queued_def)
     apply (blast dest!: ep_queues_ready_queues_disjoint)
    apply wpsimp
   apply wpsimp
  apply (rule rcorres_conj_lift_fwd; (solves ipc_append)?)
   \<comment> \<open>release_queue_relation\<close>
   apply (simp only: release_queue_relation_def)
   apply (rule_tac p=release_queue in rcorres_lift_abs)
    apply (rule_tac p=ksReleaseQueue in rcorres_lift_conc)
     apply (rcorres rcorres: tcbAppend_rcorres_other
               rcorres_lift: rcorres_allI rcorres_imp_lift)
     apply (clarsimp simp: heap_pspace_relation_def not_in_release_q_def)
     apply (blast dest!: ep_queues_release_queue_disjoint)
    apply wpsimp
   apply wpsimp
  by (rcorres_conj_lift \<open>fastforce\<close> rule: det_wp_tcb_append_set_endpoint simp: tcbAppend_def)+

crunch bindScReply
  for valid_tcbs'[wp]: valid_tcbs'
  (simp: crunch_simps)

crunch replyPush
  for pspace_aligned'[wp]: pspace_aligned'
  and pspace_distinct'[wp]: pspace_distinct'
  and pspace_bounded'[wp]: pspace_bounded'
  and pspace_canonical'[wp]: pspace_canonical'
  and if_unsafe_then_cap'[wp]: if_unsafe_then_cap'
  and valid_global_refs'[wp]: valid_global_refs'
  and valid_arch_state'[wp]: valid_arch_state'
  and valid_irq_node'[wp]: "\<lambda>s. valid_irq_node' (irq_node' s) s"
  and valid_irq_handlers'[wp]: valid_irq_handlers'
  and valid_irq_states'[wp]: valid_irq_states'
  and valid_machine_state'[wp]: valid_machine_state'
  and pspace_domain_valid[wp]: pspace_domain_valid
  and ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  and ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"
  and ksDomSchedule[wp]: "\<lambda>s. P (ksDomSchedule s)"
  and valid_dom_schedule'[wp]: valid_dom_schedule'
  and no_0_obj'[wp]: no_0_obj'
  and valid_mdb'[wp]: valid_mdb'
  and tcb_at'[wp]: "tcb_at' t"
  and cte_wp_at'[wp]: "cte_wp_at' P p"
  and ctes_of[wp]: "\<lambda>s. P (ctes_of s)"
  and pspace_in_kernel_mapping'[wp]: pspace_in_kernel_mappings'
  (wp: crunch_wps hoare_vcg_all_lift valid_irq_node_lift valid_dom_schedule'_lift
   simp: crunch_simps valid_mdb'_def)

lemma replyPush_valid_objs'[wp]:
  "replyPush callerPtr calleePtr replyPtr canDonate \<lbrace>valid_objs'\<rbrace>"
  unfolding replyPush_def updateReply_def
  apply (wpsimp wp: setThreadState_sched_pointers_valid_sched_pointers
                    hoare_vcg_if_lift2 threadGet_wp hoare_vcg_imp_lift')
  apply (force dest: reply_ko_at_valid_objs_valid_reply'
               simp: valid_reply'_def)
  done

lemma replyPush_valid_replies'[wp]:
  "\<lbrace>valid_replies' and pspace_distinct' and pspace_aligned' and pspace_bounded'\<rbrace>
   replyPush callerPtr calleePtr replyPtr canDonate
   \<lbrace>\<lambda>_. valid_replies'\<rbrace>"
  apply (clarsimp simp: replyPush_def)
  by (wpsimp wp: hoare_vcg_if_lift hoare_vcg_imp_lift' hoare_vcg_ex_lift
                 sts'_valid_replies'_except_Blocked updateReply_valid_replies'_except
                 sts_st_tcb' threadGet_wp gts_wp')

crunch reply_unlink_tcb
  for sc_replies_sc_at[wp]: "\<lambda>s. Q (sc_replies_sc_at P scp s)"
  (wp: crunch_wps simp: crunch_simps ignore: refill_unblock_check)

crunch if_cond_refill_unblock_check
  for valid_sched_action[wp]: valid_sched_action
  (wp: crunch_wps simp: crunch_simps)

crunch do_ipc_transfer
  for in_correct_ready_q[wp]: in_correct_ready_q
  and ready_qs_distinct[wp]: ready_qs_distinct
  and ready_queues_runnable [wp]: ready_queues_runnable
  and ep_queued[wp]: "\<lambda>s. P (ep_queued t s)"
  and ntfn_queued[wp]: "\<lambda>s. P (ntfn_queued t s)"
  and ep_queues_blocked[wp]: ep_queues_blocked
  and ntfn_queues_blocked[wp]: ntfn_queues_blocked
  (rule: in_correct_ready_q_lift ready_qs_distinct_lift ready_queues_runnable_lift ep_queued_lift
         ntfn_queued_lift ep_queues_blocked_lift ntfn_queues_blocked_lift)

crunch doIPCTransfer
  for reply_projs[wp]: "\<lambda>s. P (replyNexts_of s) (replyPrevs_of s) (replyTCBs_of s) (replySCs_of s)"
  and tcbSchedNexts_of[wp]: "\<lambda>s. P (tcbSchedNexts_of s)"
  and tcbSchedPrevs_of[wp]: "\<lambda>s. P (tcbSchedPrevs_of s)"
  and sym_heap_sched_pointers[wp]: sym_heap_sched_pointers
  and valid_sched_pointers[wp]: valid_sched_pointers
  and pspace_aligned'[wp]: pspace_aligned'
  and pspace_distinct'[wp]: pspace_distinct'
  and pspace_bounded'[wp]: pspace_bounded'
  (wp: crunch_wps simp: crunch_simps rule: sym_heap_sched_pointers_lift)

crunch set_simple_ko
  for ready_qs_distinct[wp]: ready_qs_distinct
  (rule: ready_qs_distinct_lift)

crunch set_thread_state
  for ntfn_queued[wp]: "\<lambda>s. P (ntfn_queued t s)"
  (wp: ntfn_queued_lift)

lemma send_ipc_blocked_corres:
  "corres dc
     (all_invs_but_fault_tcbs
      and st_tcb_at runnable t and ep_at ep_ptr and not_queued t and not_in_release_q t
      and in_correct_ready_q and ready_qs_distinct and ready_queues_runnable and release_q_runnable
      and ready_or_release and sorted_ipc_queues)
     (invs' and obj_at' (\<lambda>ep. epState ep \<noteq> IdleEPState \<longrightarrow> epState ep = SendEPState) ep_ptr)
     (send_ipc_blocked t ep_ptr bg cg cgr call)
     (do setThreadState (BlockedOnSend ep_ptr bg cg cgr call) t;
         tcbEPAppend t ep_ptr SendEPState
      od)"
  apply (rule_tac Q'="st_tcb_at' runnable' t" in corres_cross_add_guard)
   apply (fastforce intro!: st_tcb_at_runnable_cross)
  apply (rule_tac Q'="\<lambda>s'. \<not> (tcbQueued |< tcbs_of' s') t" in corres_cross_add_guard)
   apply (frule state_relation_ready_queues_relation)
   apply (frule in_ready_q_tcbQueued_eq[where t=t])
   apply (clarsimp simp: not_queued_def in_ready_q_def)
  apply (rule_tac Q'="\<lambda>s'. \<not> (tcbInReleaseQueue |< tcbs_of' s') t" in corres_cross_add_guard)
   apply (frule state_relation_release_queue_relation)
   apply (frule in_release_q_tcbInReleaseQueue_eq[where t=t])
   apply (clarsimp simp: in_release_q_def)
  apply (clarsimp simp: send_ipc_blocked_def)
  apply (rule stronger_corres_guard_imp)
    apply (rule corres_split[OF setThreadState_corres])
       apply (clarsimp simp: thread_state_relation_def)
      apply (rule tcbEPAppend_corres, simp, simp, simp)
     apply (wpsimp wp: set_thread_state_ep_queues_blocked_not_queued
                       set_thread_state_ntfn_queues_blocked_not_queued
                       set_thread_state_ready_queues_runnable_not_queued
                       set_thread_state_release_q_runnable_not_in_release_q)
    apply (wpsimp wp: setThreadState_not_queued_valid_sched_pointers)
   apply (clarsimp simp: valid_tcb_state_def)
   apply (frule st_tcb_at_tcb_at[where t=t])
   apply (clarsimp cong: conj_cong)
   apply (intro conjI impI allI; clarsimp?)
    apply (fastforce dest!: runnable_not_ep_queued)
   apply (fastforce dest!: runnable_not_ntfn_queued)
  apply clarsimp
  apply (frule runnable'_not_inIPCQueueThreadState)
  apply (frule invs_valid_sched_pointers)
  apply (fastforce dest!: valid_sched_pointersD)
  done

crunch if_cond_refill_unblock_check
  for ready_queues_runnable[wp]: ready_queues_runnable

lemma set_thread_state_ready_queues_runnable_runnable:
  "\<lbrace>ready_queues_runnable and K (runnable st)\<rbrace> set_thread_state t st \<lbrace>\<lambda>_. ready_queues_runnable\<rbrace>"
  apply (rule hoare_gen_asm)
  unfolding ready_queues_runnable_def
  apply (wpsimp wp: sts_st_tcb_at_cases hoare_vcg_all_lift hoare_vcg_ball_lift2)
  done

lemma sched_context_donate_ready_queues_runnable[wp]:
  "sched_context_donate y callee \<lbrace>ready_queues_runnable\<rbrace>"
  unfolding sched_context_donate_def test_reschedule_def set_tcb_obj_ref_thread_set
  by (wpsimp wp: thread_set_ready_queues_runnable)

lemma reply_push_ready_queues_runnable[wp]:
  "\<lbrace>ready_queues_runnable and not_queued caller\<rbrace>
   reply_push caller callee reply_ptr can_donate
   \<lbrace>\<lambda>_. ready_queues_runnable\<rbrace>"
  unfolding reply_push_def
  by (wpsimp wp: set_thread_state_ready_queues_runnable_not_queued)

lemma reply_push_ep_queues_blocked_not_queued:
  "\<lbrace>ep_queues_blocked and not ep_queued caller\<rbrace>
   reply_push caller callee reply_ptr can_donate
   \<lbrace>\<lambda>_. ep_queues_blocked\<rbrace>"
  unfolding reply_push_def
  by (wpsimp wp: set_thread_state_ep_queues_blocked_not_queued)

lemma reply_push_ntfn_queues_blocked_not_queued:
  "\<lbrace>ntfn_queues_blocked and not ntfn_queued caller\<rbrace>
   reply_push caller callee reply_ptr can_donate
   \<lbrace>\<lambda>_. ntfn_queues_blocked\<rbrace>"
  unfolding reply_push_def
  by (wpsimp wp: set_thread_state_ntfn_queues_blocked_not_queued)

crunch reply_push, sched_context_donate
  for ep_queued[wp]: "\<lambda>s. P (ep_queued ep_ptr s)"
  and ntfn_queued[wp]: "\<lambda>s. P (ntfn_queued ep_ptr s)"
  (wp: ep_queued_lift ntfn_queued_lift)

lemma setThreadState_not_queued_valid_sched_pointers':
  "\<lbrace>valid_sched_pointers and st_tcb_at' (not inIPCQueueThreadState) t\<rbrace>
   setThreadState st t
   \<lbrace>\<lambda>_. valid_sched_pointers\<rbrace>"
  apply (rule hoare_weaken_pre[OF setThreadState_valid_sched_pointers])
  apply (clarsimp simp: st_tcb_at'_def obj_at'_def opt_pred_def opt_map_def split: option.splits)
  done

lemma replyPush_sym_heap_sched_pointers:
  "\<lbrace>\<lambda>s. sym_heap_sched_pointers s \<and> valid_sched_pointers s\<rbrace>
   replyPush callerPtr calleePtr replyPtr canDonate
   \<lbrace>\<lambda>_. sym_heap_sched_pointers\<rbrace>"
  apply (clarsimp simp: replyPush_def)
  apply (intro bind_wp[OF _ stateAssert_sp])
  by (wpsimp wp: setThreadState_sched_pointers_valid_sched_pointers hoare_vcg_if_lift2
                 hoare_drop_imp)

lemma replyPush_valid_sched_pointers:
  "replyPush callerPtr calleePtr replyPtr canDonate \<lbrace>valid_sched_pointers\<rbrace>"
  unfolding replyPush_def
  by (wpsimp wp: setThreadState_sched_pointers_valid_sched_pointers)

crunch bindScReply
  for st_tcb_at[wp]: "\<lambda>s. Q (st_tcb_at' P t s)"
  and bound_sc_tcb_at'[wp]: "\<lambda>s. Q (bound_sc_tcb_at' P t s)"
  and tcbs_of'[wp]: "\<lambda>s. P (tcbs_of' s)"
  and sch_act_not[wp]: "sch_act_not t"
  (simp: crunch_simps)

lemma replyPush_st_tcb_at'_other:
  "\<lbrace>st_tcb_at' P t and K (callerPtr \<noteq> t)\<rbrace>
   replyPush callerPtr calleePtr replyPtr canDonate
   \<lbrace>\<lambda>_ s. st_tcb_at' P t s\<rbrace>"
  unfolding replyPush_def
  by (wpsimp wp: sts_st_tcb_at'_cases)

lemma valid_objs_valid_tcb:
  "\<lbrakk>kheap s t = Some (kernel_object.TCB tcb); valid_objs s\<rbrakk> \<Longrightarrow> valid_tcb t tcb s"
  by (fastforce simp: valid_objs_def valid_obj_def valid_ep_def)

lemma tcbSchedPrev_update_tcbSchedPrevs_of_other:
  "\<lbrace>\<lambda>s. P (tcbSchedPrevs_of s t) \<and> t' \<noteq> t\<rbrace>
   threadSet (tcbSchedPrev_update f) t'
   \<lbrace>\<lambda>_ s. P (tcbSchedPrevs_of s t)\<rbrace>"
  by (wpsimp wp: threadSet_wp)

lemma tcbQueuePrepend_tcbSchedPrevs_of_other:
  "\<lbrace>\<lambda>s. P (tcbSchedPrevs_of s t) \<and> (\<forall>head. tcbQueueHead q = Some head \<longrightarrow> t \<noteq> head)\<rbrace>
   tcbQueuePrepend q t'
   \<lbrace>\<lambda>_ s. P (tcbSchedPrevs_of s t)\<rbrace>"
  unfolding tcbQueuePrepend_def
  apply (wpsimp wp: tcbSchedPrev_update_tcbSchedPrevs_of_other threadSet_field_inv)+
  apply (clarsimp simp: tcbQueueEmpty_def)
  done

lemma tcbSchedEnqueue_tcbSchedPrevs_of_other:
  "\<lbrace>\<lambda>s. P (tcbSchedPrevs_of s t) \<and> t' \<noteq> t \<and> \<not> (tcbQueued |< tcbs_of' s) t\<rbrace>
   tcbSchedEnqueue t'
   \<lbrace>\<lambda>_ s. P (tcbSchedPrevs_of s t)\<rbrace>"
  unfolding tcbSchedEnqueue_def
  apply (wpsimp wp: tcbQueuePrepend_tcbSchedPrevs_of_other threadGet_wp threadSet_field_inv)+
  apply (clarsimp simp: ksReadyQueues_asrt_def ready_queue_relation_def)
  apply normalise_obj_at'
  apply (drule_tac x="tcbDomain tcb" in spec)
  apply (drule_tac x="tcbPriority tcb" in spec)
  apply (clarsimp simp: list_queue_relation_def)
  apply (frule heap_path_head)
   apply fastforce
  apply (fastforce intro: hd_in_set)
  done

lemma rescheduleRequired_tcbSchedPrevs_of_other:
  "\<lbrace>\<lambda>s. P (tcbSchedPrevs_of s t) \<and> sch_act_not t s \<and> \<not> (tcbQueued |< tcbs_of' s) t\<rbrace>
   rescheduleRequired
   \<lbrace>\<lambda>_ s. P (tcbSchedPrevs_of s t)\<rbrace>"
  unfolding rescheduleRequired_def
  by (wpsimp wp: tcbSchedEnqueue_tcbSchedPrevs_of_other getSchedulable_wp)

lemma tcbSchedNext_update_tcbSchedPrevs_of[wp]:
  "threadSet (tcbSchedNext_update f) t' \<lbrace>\<lambda>s. P (tcbSchedPrevs_of s t)\<rbrace>"
  apply (wpsimp wp: threadSet_wp)
  by (clarsimp simp: opt_map_def obj_at'_def)

lemma tcbQueueRemove_tcbSchedPrevs_of_not_in_list:
  "\<lbrace>\<lambda>s. P (tcbSchedPrevs_of s t)
        \<and> (\<exists>ls. list_queue_relation ls q (tcbSchedNexts_of s) (tcbSchedPrevs_of s) \<and> t \<notin> set ls)\<rbrace>
   tcbQueueRemove q t'
   \<lbrace>\<lambda>_ s. P (tcbSchedPrevs_of s t)\<rbrace>"
  apply (clarsimp simp: tcbQueueRemove_def)
  apply (wpsimp wp: tcbSchedPrev_update_tcbSchedPrevs_of_other getTCB_wp)
  apply (clarsimp simp: list_queue_relation_def)
  apply (drule (1) heap_ls_unique)
  apply (force dest!: heap_ls_next_in_list simp: opt_map_def obj_at'_def)
  done

lemma tcbQueueRemove_tcbSchedNexts_of_not_in_list:
  "\<lbrace>\<lambda>s. P (tcbSchedNexts_of s t)
        \<and> (\<exists>ls. list_queue_relation ls q (tcbSchedNexts_of s) (tcbSchedPrevs_of s) \<and> t \<notin> set ls)\<rbrace>
   tcbQueueRemove q t'
   \<lbrace>\<lambda>_ s. P (tcbSchedNexts_of s t)\<rbrace>"
  apply (clarsimp simp: tcbQueueRemove_def)
  apply (wpsimp wp: tcbSchedNext_update_tcbSchedNexts_of_other getTCB_wp)
  apply (clarsimp simp: list_queue_relation_def)
  apply (drule (1) heap_ls_unique)
  by (fastforce intro: sym_heapD2 dest!: heap_ls_prev_cases simp: opt_map_def obj_at'_def)

lemma tcbReleaseRemove_tcbSchedPrevs_of_not_in_list:
  "\<lbrace>\<lambda>s. P (tcbSchedPrevs_of s t) \<and> \<not> (tcbInReleaseQueue |< tcbs_of' s) t\<rbrace>
   tcbReleaseRemove t'
   \<lbrace>\<lambda>_ s. P (tcbSchedPrevs_of s t)\<rbrace>"
  unfolding tcbReleaseRemove_def
  apply (wpsimp wp: tcbQueueRemove_tcbSchedPrevs_of_not_in_list hoare_vcg_ex_lift inReleaseQueue_wp
                    threadSet_field_inv threadSet_sched_pointers)
  by (fastforce simp: ksReleaseQueue_asrt_def)

lemma tcbReleaseRemove_tcbSchedNexts_of_not_in_list:
  "\<lbrace>\<lambda>s. P (tcbSchedNexts_of s t)  \<and> \<not> (tcbInReleaseQueue |< tcbs_of' s) t\<rbrace>
   tcbReleaseRemove t'
   \<lbrace>\<lambda>_ s. P (tcbSchedNexts_of s t)\<rbrace>"
  unfolding tcbReleaseRemove_def
  apply (wpsimp wp: tcbQueueRemove_tcbSchedNexts_of_not_in_list hoare_vcg_ex_lift inReleaseQueue_wp
                    threadSet_field_inv threadSet_sched_pointers)
  by (fastforce simp: ksReleaseQueue_asrt_def)

lemma tcbSchedDequeue_tcbSchedPrevs_of:
  "\<lbrace>\<lambda>s. P (tcbSchedPrevs_of s t) \<and> \<not> (tcbQueued |< tcbs_of' s) t\<rbrace>
   tcbSchedDequeue t'
   \<lbrace>\<lambda>_ s. P (tcbSchedPrevs_of s t)\<rbrace>"
  unfolding tcbSchedDequeue_def
  apply (wpsimp wp: tcbQueueRemove_tcbSchedPrevs_of_not_in_list hoare_vcg_ex_lift inReleaseQueue_wp
                    threadGet_wp threadSet_field_inv threadSet_sched_pointers)
  by (force simp: ksReadyQueues_asrt_def ready_queue_relation_def)

lemma tcbSchedDequeue_tcbSchedNexts_of:
  "\<lbrace>\<lambda>s. P (tcbSchedNexts_of s t) \<and> \<not> (tcbQueued |< tcbs_of' s) t\<rbrace>
   tcbSchedDequeue t'
   \<lbrace>\<lambda>_ s. P (tcbSchedNexts_of s t)\<rbrace>"
  unfolding tcbSchedDequeue_def
  apply (wpsimp wp: tcbQueueRemove_tcbSchedNexts_of_not_in_list hoare_vcg_ex_lift inReleaseQueue_wp
                    threadGet_wp threadSet_field_inv threadSet_sched_pointers)
  by (force simp: ksReadyQueues_asrt_def ready_queue_relation_def)

crunch tcbReleaseRemove
  for tcbQueued_opt_pred[wp]: "\<lambda>s. P (tcbQueued |< tcbs_of' s)"
  (wp: threadSet_field_opt_pred)

lemma tcbSchedDequeue_tcbQueued_other:
  "\<lbrace>\<lambda>s. P ((tcbQueued |< tcbs_of' s) t) \<and> t' \<noteq> t\<rbrace>
   tcbSchedDequeue t'
   \<lbrace>\<lambda>_ s. P ((tcbQueued |< tcbs_of' s) t)\<rbrace>"
  unfolding tcbSchedDequeue_def
  by (wpsimp wp: threadSet_opt_pred_other threadGet_wp)

lemma schedContextDonate_tcbSchedPrevs_of_None:
  "\<lbrace>\<lambda>s. tcbSchedPrevs_of s tcbPtr = None \<and> sch_act_not tcbPtr s
        \<and> sym_heap_tcbSCs s \<and> bound_sc_tcb_at' ((=) None) tcbPtr s
        \<and> \<not> (tcbQueued |< tcbs_of' s) tcbPtr \<and> \<not> (tcbInReleaseQueue |< tcbs_of' s) tcbPtr\<rbrace>
   schedContextDonate scPtr tcbPtr
   \<lbrace>\<lambda>_ s. tcbSchedPrevs_of s tcbPtr = None\<rbrace>"
  unfolding schedContextDonate_def
  apply (wpsimp wp: threadSet_field_inv threadSet_field_opt_pred
                    rescheduleRequired_tcbSchedPrevs_of_other
                    tcbReleaseRemove_tcbSchedPrevs_of_not_in_list
                    tcbSchedDequeue_tcbSchedPrevs_of tcbSchedDequeue_tcbSchedNexts_of
                    tcbSchedDequeue_tcbQueued_other hoare_drop_imp )+
  by (force dest!: sym_heapD2[where p'=scPtr] simp: obj_at'_def opt_map_def pred_tcb_at'_def)

lemma schedContextDonate_tcbSchedNexts_of_None:
  "\<lbrace>\<lambda>s. tcbSchedNexts_of s tcbPtr = None \<and> sch_act_not tcbPtr s
        \<and> sym_heap_tcbSCs s \<and> bound_sc_tcb_at' ((=) None) tcbPtr s
        \<and> \<not> (tcbQueued |< tcbs_of' s) tcbPtr \<and> \<not> (tcbInReleaseQueue |< tcbs_of' s) tcbPtr\<rbrace>
   schedContextDonate scPtr tcbPtr
   \<lbrace>\<lambda>_ s. tcbSchedNexts_of s tcbPtr = None\<rbrace>"
  unfolding schedContextDonate_def
  apply (wpsimp wp: threadSet_field_inv rescheduleRequired_tcbSchedNexts_of_other
                    tcbReleaseRemove_tcbSchedNexts_of_not_in_list
                    tcbSchedDequeue_tcbSchedPrevs_of tcbSchedDequeue_tcbSchedNexts_of
                    tcbSchedDequeue_tcbQueued_other hoare_drop_imps)
  by (force dest!: sym_heapD2[where p'=scPtr] simp: obj_at'_def opt_map_def pred_tcb_at'_def)

crunch setThreadState, replyUnlink, doIPCTransfer, tcbEPDequeue
  for tcbQueued_opt_pred[wp]: "\<lambda>s. P (tcbQueued |< tcbs_of' s)"
  and tcbInReleaseQueue_opt_pred[wp]: "\<lambda>s. P (tcbInReleaseQueue |< tcbs_of' s)"
  and replySCs_of[wp]: "\<lambda>s. P (replySCs_of s)"
  (wp: crunch_wps threadSet_field_opt_pred threadSet_field_inv simp: crunch_simps)

lemma updateSchedContext_field_inv:
  "(\<And>sc. f (F sc) = f sc) \<Longrightarrow> updateSchedContext scPtr F \<lbrace>\<lambda>s. P (scs_of' s |> f)\<rbrace>"
  apply (wpsimp wp: updateSchedContext_wp)
  by (fastforce elim!: rsubst[where P=P] simp: opt_map_def obj_at'_def)

crunch updateReply, scheduleTCB, setThreadState, doIPCTransfer
  for scTCBs_of[wp]: "\<lambda>s. P (scTCBs_of s)"
  and tcbSchedContexts_of[wp]: "\<lambda>s. P (tcbSchedContexts_of s)"
  (wp: threadSet_field_inv updateSchedContext_field_inv crunch_wps simp: crunch_simps
   ignore: updateSchedContext threadSet)

lemma sym_heap_tcbSCs_lift:
  "\<lbrakk>\<And>P. f \<lbrace>\<lambda>s. P (scTCBs_of s)\<rbrace>; \<And>P. f \<lbrace>\<lambda>s. P (tcbSCs_of s)\<rbrace>\<rbrakk> \<Longrightarrow> f \<lbrace>sym_heap_tcbSCs\<rbrace>"
  by (rule_tac f=tcbSCs_of in hoare_lift_Pf2; wpsimp)

crunch bindScReply, scheduleTCB, setThreadState, replyUnlink, doIPCTransfer, tcbEPDequeue
  for sym_heap_tcbSCs[wp]: sym_heap_tcbSCs
  (wp: sym_heap_tcbSCs_lift updateSchedContext_field_inv crunch_wps
   simp: crunch_simps ignore: updateSchedContext)

lemma replyPush_tcbSchedNexts_of_None[wp]:
  "\<lbrace>\<lambda>s. tcbSchedNexts_of s calleePtr = None \<and> sch_act_not calleePtr s \<and> sym_heap_tcbSCs s
        \<and> \<not> (tcbQueued |< tcbs_of' s) calleePtr \<and> \<not> (tcbInReleaseQueue |< tcbs_of' s) calleePtr\<rbrace>
   replyPush callerPtr calleePtr replyPtr canDonate
   \<lbrace>\<lambda>_ s. tcbSchedNexts_of s calleePtr = None\<rbrace>"
  unfolding replyPush_def
  apply (wpsimp wp: hoare_vcg_if_lift2 hoare_vcg_imp_lift' schedContextDonate_tcbSchedNexts_of_None
                    threadGet_wp)
  by normalise_obj_at'

lemma replyPush_tcbSchedPrevs_of_None[wp]:
  "\<lbrace>\<lambda>s. tcbSchedPrevs_of s calleePtr = None \<and> sch_act_not calleePtr s \<and> sym_heap_tcbSCs s
        \<and> \<not> (tcbQueued |< tcbs_of' s) calleePtr \<and> \<not> (tcbInReleaseQueue |< tcbs_of' s) calleePtr\<rbrace>
   replyPush callerPtr calleePtr replyPtr canDonate
   \<lbrace>\<lambda>_ s. tcbSchedPrevs_of s calleePtr = None\<rbrace>"
  unfolding replyPush_def
  apply (wpsimp wp: hoare_vcg_if_lift2 hoare_vcg_imp_lift' schedContextDonate_tcbSchedPrevs_of_None
                    threadGet_wp)
  by normalise_obj_at'

crunch tcb_ep_dequeue
  for ep_at[wp]: "ep_at ep_ptr"
  (wp: crunch_wps)

lemma ready_queues_runnable_not_queued:
  "\<lbrakk>ready_queues_runnable s; st_tcb_at (Not \<circ> runnable) t s\<rbrakk> \<Longrightarrow> not_queued t s"
  apply (clarsimp simp: ready_queues_runnable_def st_tcb_at_def obj_at_def not_queued_def)
  apply fastforce
  done

lemma sendIPC_corres_sym_refs_helper:
  "\<lbrakk>ko_at (kernel_object.Endpoint (RecvEP (dest # ls))) ep_ptr s;
    valid_objs s; sym_refs (state_refs_of s); valid_ep (RecvEP (dest # ls)) s;
    st_tcb_at (\<lambda>x. x = Structures_A.thread_state.BlockedOnReceive ep_ptr data pl) dest s;
    ko_at (kernel_object.Endpoint obj) ep_ptr s\<rbrakk>
   \<Longrightarrow> sym_refs
         (\<lambda>x. if x = dest
              then {r \<in> state_refs_of s dest. snd r = TCBBound \<or> snd r = TCBSchedContext
                                              \<or> snd r = TCBYieldTo \<or> snd r = TCBReply}
              else if x = ep_ptr
                   then ep_q_refs_of (case removeAll dest (ep_queue obj) of
                            [] \<Rightarrow> IdleEP
                          | a # list \<Rightarrow> update_ep_queue obj (removeAll dest (ep_queue obj)) True)
                   else state_refs_of s x)"
  unfolding removeAll_filter_not_eq
  apply (prop_tac "filter ((\<noteq>) dest) ls = ls", fastforce simp: valid_ep_def filter_id_conv)
  apply (rule delta_sym_refs, assumption)
   apply (fastforce simp: obj_at_def state_refs_of_def split: list.splits if_splits)
  apply clarsimp
  apply (intro conjI)
   apply (fastforce simp: valid_obj_def valid_ep_def is_tcb obj_at_def split: list.splits if_splits)
  apply (clarsimp, intro conjI)
   apply (clarsimp simp: obj_at_def split: if_splits)
   apply (fastforce simp: state_refs_of_def)
  apply (clarsimp simp: obj_at_def split: if_splits)
   apply (clarsimp simp: st_tcb_at_def obj_at_def state_refs_of_def get_refs_def2 split: if_splits)
  apply (clarsimp simp: sym_refs_ko_atD obj_at_def split: list.splits)
  done

crunch getSchedulerAction
  for (no_fail) no_fail[wp]

lemma bound_sc_tcb_at_cross':
  "\<lbrakk>bound_sc_tcb_at P t s; (s, s') \<in> state_relation; pspace_aligned s; pspace_distinct s\<rbrakk>
   \<Longrightarrow> bound_sc_tcb_at' P t s'"
  by (fastforce dest!: bound_sc_tcb_at_cross simp: pred_tcb_at'_def obj_at'_def opt_map_red)

lemma sendIPC_corres:
(* call is only true if called in handleSyscall SysCall, which is always blocking. *)
  assumes "call \<longrightarrow> bl"
  shows
  "corres dc
     (all_invs_but_fault_tcbs and fault_tcbs_valid_states_except_set {t} and valid_list
      and active_scs_valid and valid_release_q
      and current_time_bounded
      and st_tcb_at runnable t and not_queued t and not_in_release_q t
      and in_correct_ready_q and ready_qs_distinct and ready_queues_runnable and release_q_runnable
      and ready_or_release and sorted_ipc_queues
      and valid_sched_action and ep_at ep_ptr
      and scheduler_act_not t and (\<lambda>s. cd \<longrightarrow> bound_sc_tcb_at (\<lambda>a. \<exists>y. a = Some y) t s))
     invs'
     (send_ipc bl call bg cg cgr cd t ep_ptr) (sendIPC bl call bg cg cgr cd t ep_ptr)"
  apply (insert assms)
  apply add_sym_refs
  apply add_valid_idle'
  apply (clarsimp simp: send_ipc_def sendIPC_def Let_def split del: if_split)
  apply (rule corres_stateAssert_add_assertion[rotated], simp)
  apply (rule corres_stateAssert_add_assertion[rotated], simp)
  apply (rule corres_stateAssert_add_assertion[rotated], simp)
  apply (rule_tac Q'="ep_at' ep_ptr" in corres_cross_add_guard, fastforce intro!: ep_at_cross)
  apply (rule_tac Q'="st_tcb_at' runnable' t" in corres_cross_add_guard)
   apply (fastforce intro!: st_tcb_at_runnable_cross)
  apply (rule corres_stateAssert_add_assertion[rotated], simp add: runnable_eq_active')
  apply (rule_tac Q'="\<lambda>s'. \<not> (tcbQueued |< tcbs_of' s') t" in corres_cross_add_guard)
   apply (frule state_relation_ready_queues_relation)
   apply (frule in_ready_q_tcbQueued_eq[where t=t])
   apply (clarsimp simp: not_queued_def in_ready_q_def)
  apply (rule_tac Q'="\<lambda>s'. \<not> (tcbInReleaseQueue |< tcbs_of' s') t" in corres_cross_add_guard)
   apply (frule state_relation_release_queue_relation)
   apply (frule in_release_q_tcbInReleaseQueue_eq[where t=t])
   apply (clarsimp simp: in_release_q_def)
  apply (rule corres_split_forwards'[OF _ get_simple_ko_sp get_ep_sp'])
   apply (corres corres: getEndpoint_corres)
  apply (rename_tac ep ep')
  apply (rule_tac Q="\<lambda>s. ep_queues_of s ep_ptr = Some (ep_queue ep)" in corres_cross_add_abs_guard)
   apply (case_tac ep; clarsimp simp: eps_of_kh_def obj_at_def opt_map_def)
  apply (rule_tac Q="valid_ep ep" in corres_cross_add_abs_guard)
   apply (fastforce dest: valid_objs_valid_ep simp: obj_at_def)
  apply (case_tac ep; clarsimp simp: ep_relation_def)
    apply (subst bind_dummy_ret_val)
    apply (corres corres: send_ipc_blocked_corres)
    apply (clarsimp simp: obj_at'_def)
   apply (subst bind_dummy_ret_val)
   apply (corres corres: send_ipc_blocked_corres)
   apply (clarsimp simp: obj_at'_def)
  apply (rename_tac ep' ls)
  apply (rule_tac F="ls \<noteq> []" in corres_req)
   apply (clarsimp simp: valid_ep_def)
  apply (case_tac ls; clarsimp)
  apply (rename_tac dest tail)
  apply (rule_tac Q'="\<lambda>s'. list_queue_relation
                             (dest # tail) (epQueue ep') (tcbSchedNexts_of s') (tcbSchedPrevs_of s')"
               in corres_cross_add_guard)
   apply (fastforce elim!: ep_queues_relationD
                     simp: obj_at_def opt_map_def obj_at'_def split: option.splits)
  apply (rule corres_stateAssert_ignore)
   apply (rule_tac ts="dest # tail" in list_queue_relation_tcb_queue_head_end_valid)
    apply fastforce
   apply (clarsimp simp: valid_ep_def)
   apply (fastforce intro!: tcb_at_cross)
  apply (rule corres_assert_gen_asm_cross_forwards)
   apply (fastforce dest: list_queue_relation_Nil)
  apply (clarsimp simp: tcbQueueEmpty_def)
  apply (rename_tac head)
  apply (rule_tac F="head = dest" in corres_req)
   apply (clarsimp simp: list_queue_relation_def)
  apply clarsimp
  apply (rule_tac Q="st_tcb_at (Not \<circ> runnable) dest" in corres_cross_add_abs_guard)
   apply (clarsimp simp: obj_at_def)
   apply (frule_tac t=dest in in_receive_ep_queue_st_tcb_at)
     apply force
    apply fastforce
   apply (erule st_tcb_weakenE)
   subgoal for \<dots> st by (case_tac st; clarsimp)
  apply (rule corres_assert_gen_asm_cross_forwards; (solves wpsimp)?)
   apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  apply (rule corres_stateAssert_add_assertion[rotated])
   apply simp
   apply (rule in_ready_q_tcbQueued_eq[THEN arg_cong_Not, THEN iffD1])
    apply fastforce
   apply (clarsimp elim!: ready_queues_runnable_not_queued)
  apply (rule corres_stateAssert_add_assertion[rotated])
   apply simp
   apply (rule in_release_q_tcbInReleaseQueue_eq[THEN arg_cong_Not, THEN iffD1])
    apply fastforce
   apply (fastforce dest!: valid_release_q_not_in_release_q_not_runnable)
  apply (rule corres_symb_exec_r[OF _ getSchedulerAction_sp]; (solves wpsimp)?)
  apply (rule corres_assert_gen_asm_cross_forwards; (solves wpsimp)?)
   apply (frule cross_relF[OF _ sch_act_not_cross_rel])
    apply (rule weak_valid_sched_action_scheduler_action_not)
     apply (fastforce intro: valid_sched_action_weak_valid_sched_action)
    apply fastforce
   apply clarsimp
  apply (rule stronger_corres_guard_imp)
    apply (rule corres_split[OF tcbEPDequeue_corres], simp, simp)
      apply clarsimp
      apply (rule corres_split[OF getThreadState_corres])
        apply (rule stronger_corres_guard_imp)
          apply (rule_tac F="\<exists>reply_opt pl. recv_state = Structures_A.BlockedOnReceive ep_ptr reply_opt pl"
                       in corres_gen_asm)
          apply (clarsimp simp: case_bool_If case_option_If if3_fold
                      simp del: dc_simp split del: if_split cong: if_cong)
          apply (clarsimp simp: isReceive_def split del: if_split)
          apply (rule corres_split [OF doIPCTransfer_corres])
            apply (rule corres_stateAssert_r)
            apply (rule corres_split[where r'=dc])
               apply (clarsimp simp: maybeM_def)
               apply (rule corres_option_split[OF refl corres_return_trivial])
               apply clarsimp
               apply (rule replyUnlinkTcb_corres)
              apply (simp only: get_tcb_obj_ref_def)
              apply (rule corres_split [OF threadGet_corres[where r="(=)"]])
                 apply (clarsimp simp: tcb_relation_def)
                apply (rule corres_split [OF threadGet_corres[where r=fault_rel_optionation]])
                   apply (clarsimp simp: tcb_relation_def)
                  apply (rule corres_split [OF corres_if[where r=dc], where r=dc])
                       apply (clarsimp simp: fault_rel_optionation_def)
                      apply (rule corres_if, clarsimp)
                       apply (rule replyPush_corres, simp)
                      apply (rule setThreadState_corres, simp)
                     apply (rule corres_when, simp)
                     apply (rule corres_split [OF threadGet_corres[where r="(=)"]])
                        apply (clarsimp simp: tcb_relation_def)
                       apply (rule corres_assert_assume_r)
                       apply (simp, rule schedContextDonate_corres)
                      apply (wpsimp wp: thread_get_wp)
                     apply (wpsimp wp: threadGet_wp)
                    apply (rule corres_split[OF setThreadState_corres])
                       apply simp
                      apply (rule corres_split_eqr[OF threadGet_corres])
                         apply (clarsimp simp: tcb_relation_def)
                        apply (rule corres_split [OF ifCondRefillUnblockCheck_corres])
                          apply (rule possibleSwitchTo_corres, simp)
                         apply wpsimp
                        apply wpsimp
                       apply clarsimp
                       apply (rule_tac Q'="\<lambda>r. bound_sc_tcb_at ((=) r) dest
                                               and active_scs_valid and valid_sched_action
                                               and pspace_aligned and pspace_distinct
                                               and valid_objs and ready_or_release
                                               and in_correct_ready_q and ready_qs_distinct
                                               and ready_queues_runnable and st_tcb_at runnable dest
                                               and not_in_release_q dest and current_time_bounded
                                               and ep_queues_blocked and ntfn_queues_blocked"
                                    in hoare_post_imp)
                        apply clarsimp
                        apply (case_tac rv; clarsimp)
                        apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb option.case_eq_if)
                        apply (frule (1) valid_objs_valid_tcb)
                        subgoal
                          by (fastforce simp: valid_obj_def valid_tcb_def obj_at_def
                                              valid_bound_obj_def is_sc_obj opt_map_red opt_pred_def
                                       split: option.splits)
                       apply (wpsimp wp: thread_get_wp')
                      apply (wpsimp wp: threadGet_wp)
                     apply (rule_tac Q'="\<lambda>r. active_scs_valid and valid_sched_action
                                             and pspace_aligned and pspace_distinct and valid_objs
                                             and ready_or_release and in_correct_ready_q
                                             and ready_qs_distinct and ready_queues_runnable
                                             and st_tcb_at runnable dest and not_in_release_q dest
                                             and current_time_bounded
                                             and ep_queues_blocked and ntfn_queues_blocked"
                                  in hoare_post_imp)
                      apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb_def)
                     apply (wpsimp wp: set_thread_state_valid_sched_action
                                       set_thread_state_ready_queues_runnable_runnable
                                       set_thread_state_ep_queues_blocked_not_queued
                                       set_thread_state_ntfn_queues_blocked_not_queued)
                    apply (rule_tac Q'="\<lambda>_. tcb_at' dest and valid_objs'
                                            and sym_heap_sched_pointers and valid_sched_pointers
                                            and pspace_aligned' and pspace_distinct'
                                            and pspace_bounded'"
                                 in hoare_post_imp)
                     apply (clarsimp simp: obj_at'_def valid_objs'_valid_tcbs' split: option.split)
                    apply (wpsimp wp: setThreadState_sched_pointers_valid_sched_pointers)
                   apply (rule_tac Q'="\<lambda>_. valid_objs and pspace_aligned and pspace_distinct
                                           and tcb_at dest and active_scs_valid
                                           and valid_sched_action and ready_or_release
                                           and in_correct_ready_q and ready_qs_distinct
                                           and not_in_release_q dest and current_time_bounded
                                           and ready_queues_runnable
                                           and ep_queues_blocked and ntfn_queues_blocked
                                           and not ep_queued dest and not ntfn_queued dest"
                                in hoare_post_imp)
                    apply fastforce
                   apply (wpsimp wp: set_thread_state_valid_sched_action
                                     sched_context_donate_valid_sched_action
                                     thread_get_wp' reply_push_valid_objs
                                     reply_push_ep_queues_blocked_not_queued
                                     reply_push_ntfn_queues_blocked_not_queued
                                     set_thread_state_valid_sched_action
                                     set_thread_state_ready_queues_runnable_not_queued
                                     set_thread_state_ep_queues_blocked_not_queued
                                     set_thread_state_ntfn_queues_blocked_not_queued)
                  apply ((wpsimp wp: replyPush_valid_objs'
                                     replyPush_sym_heap_sched_pointers
                                     replyPush_valid_sched_pointers
                                     replyPush_st_tcb_at'_other
                                     setThreadState_sched_pointers_valid_sched_pointers
                                     sts_st_tcb_at'_cases schedContextDonate_valid_objs'
                                     schedContextDonate_tcbSchedNexts_of_None
                                     schedContextDonate_tcbSchedPrevs_of_None
                          | strengthen valid_objs'_valid_tcbs')+)[1]
                  apply (wpsimp wp: threadGet_wp)
                 apply (wpsimp wp: thread_get_wp')
                apply (wpsimp wp: threadGet_wp)
               apply (wpsimp wp: thread_get_wp')
              apply (wpsimp wp: threadGet_wp)
             apply (rule_tac
                      Q'="\<lambda>_. valid_objs and pspace_aligned and pspace_distinct
                              and valid_replies and scheduler_act_not t
                              and K (t \<noteq> idle_thread_ptr) and valid_idle
                              and tcb_at dest and active_scs_valid
                              and valid_sched_action and ready_or_release
                              and in_correct_ready_q and ready_qs_distinct
                              and ready_queues_runnable and valid_release_q
                              and not_queued t and not_in_release_q t
                              and not ep_queued t and not ntfn_queued t
                              and st_tcb_at runnable t and st_tcb_at active t
                              and ep_queues_blocked and ntfn_queues_blocked
                              and not_in_release_q dest and current_time_bounded
                              and ep_queues_blocked and ntfn_queues_blocked
                              and not ep_queued dest and not ntfn_queued dest
                              and (\<lambda>s. cd \<longrightarrow> bound_sc_tcb_at (\<lambda>a. \<exists>y. a = Some y) t s)
                              and (\<lambda>s. reply_opt \<noteq> None
                                       \<longrightarrow> reply_at (the reply_opt) s
                                           \<and> ex_nonz_cap_to (the reply_opt) s
                                           \<and> reply_tcb_reply_at (\<lambda>tptr. tptr = None) (the reply_opt) s
                                           \<and> reply_sc_reply_at (\<lambda>tptr. tptr = None) (the reply_opt) s
                                           \<and> the reply_opt \<notin> fst ` replies_with_sc s
                                           \<and> sym_refs (state_refs_of s))"
                   in hoare_post_imp)
              apply (prop_tac "reply_opt \<noteq> None
                               \<longrightarrow> sym_refs
                                     (\<lambda>p. if p = t
                                          then tcb_non_st_state_refs_of s t
                                          else state_refs_of s p)")
               subgoal
                 apply clarsimp
                 apply (erule delta_sym_refs)
                 by (auto simp: state_refs_of_def get_refs_def2 pred_tcb_at_def obj_at_def
                         split: if_split_asm option.splits)
              apply (prop_tac "st_tcb_at (\<lambda>st. reply_object st = None) t s")
               apply (fastforce elim!: pred_tcb_weakenE)
              apply (clarsimp simp: st_tcb_at_tcb_at cong: conj_cong)
              apply (frule valid_sched_action_weak_valid_sched_action, simp)
              apply (frule valid_objs_valid_tcbs, simp)
              apply (subgoal_tac "cd \<longrightarrow> bound_sc_tcb_at (\<lambda>sc_ptr_opt. sc_at (the sc_ptr_opt) s) t s")
               apply (clarsimp simp: obj_at_def is_tcb pred_tcb_at_def)
               apply (frule valid_release_q_distinct)
               apply (frule valid_release_q_release_q_runnable)
               apply clarsimp
              apply (drule pred_tcb_at_ko_atD, clarsimp)
              apply (frule (1) valid_objs_ko_at)
              apply (clarsimp simp: pred_tcb_at_def obj_at_def valid_obj_def valid_tcb_def)
             apply (wpsimp wp: reply_unlink_tcb_valid_sched_action
                               reply_unlink_tcb_valid_replies_BlockedOnReceive
                               reply_unlink_tcb_sym_refs_BlockedOnReceive
                               reply_unlink_tcb_reply_tcb_reply_at[where P=id, simplified]
                               reply_unlink_tcb_st_tcb_at' replies_with_sc_lift)
            apply (rule_tac
                     Q'="\<lambda>_ s. tcb_at' t s \<and> tcb_at' dest s \<and> valid_objs' s
                               \<and> sym_heap_sched_pointers s \<and> valid_sched_pointers s
                               \<and> pspace_aligned' s \<and> pspace_distinct' s \<and> pspace_bounded' s
                               \<and> \<not> is_sched_linked t s
                               \<and> \<not> is_sched_linked dest s
                               \<and> \<not> (tcbQueued |< tcbs_of' s) dest
                               \<and> \<not> (tcbInReleaseQueue |< tcbs_of' s) dest
                               \<and> t \<noteq> dest
                               \<and> (reply_opt \<noteq> None
                                  \<longrightarrow> reply_at' (the reply_opt) s
                                      \<and> replySCs_of s (the reply_opt) = None)
                               \<and> sym_heap_tcbSCs s \<and> sch_act_not dest s
                               \<and> (cd \<longrightarrow> bound_sc_tcb_at' (\<lambda>scOpt. scOpt \<noteq> None) t s)"
                  in hoare_post_imp)
             apply (clarsimp cong: conj_cong)
             apply (frule valid_objs'_valid_tcbs')
             apply (drule obj_at_ko_at')+
             apply (prop_tac "reply_opt \<noteq> None \<longrightarrow> valid_replies'_sc_asrt (the reply_opt) s")
              apply (blast dest: no_replySC_valid_replies'_sc_asrt)
             apply normalise_obj_at'
            apply (wpsimp wp: replyUnlink_valid_sched_pointers replyUnlink_st_tcb_at'
                              hoare_vcg_const_imp_lift)
           apply (wpfix add: reply_object.simps(1))
           apply (rule_tac
                    Q'="\<lambda>_. valid_objs and pspace_aligned and pspace_distinct
                            and valid_replies and active_scs_valid and valid_release_q
                            and scheduler_act_not t and valid_sched_action
                            and ready_queues_runnable and not_queued t and not_in_release_q t
                            and not ep_queued t and not ntfn_queued t
                            and st_tcb_at runnable t and valid_idle
                            and ep_queues_blocked and ntfn_queues_blocked
                            and not ep_queued dest and not ntfn_queued dest and not_queued dest
                            and in_correct_ready_q and ready_qs_distinct and ready_or_release
                            and not_in_release_q dest and st_tcb_at active t and tcb_at dest
                            and if_live_then_nonz_cap and scheduler_act_not dest
                            and K (t \<noteq> idle_thread_ptr) and current_time_bounded
                            and (\<lambda>s. cd \<longrightarrow> bound_sc_tcb_at (\<lambda>a. \<exists>y. a = Some y) t s)
                            and (\<lambda>s. reply_opt \<noteq> None
                                     \<longrightarrow> st_tcb_at
                                           ((=) (Structures_A.thread_state.BlockedOnReceive
                                                   ep_ptr reply_opt pl)) dest s
                                         \<and> ex_nonz_cap_to (the reply_opt) s
                                         \<and> reply_tcb_reply_at ((=) (Some dest)) (the reply_opt) s
                                         \<and> reply_sc_reply_at (\<lambda>a. a = None) (the reply_opt) s
                                         \<and> the reply_opt \<notin> fst ` replies_with_sc s)
                            and (\<lambda>s. sym_refs
                                       (\<lambda>x. if x = dest
                                            then {r \<in> state_refs_of s x.
                                                    snd r = TCBBound \<or> snd r = TCBSchedContext
                                                    \<or> snd r = TCBYieldTo \<or> snd r = TCBReply}
                                            else state_refs_of s x))"
                 in hoare_post_imp)
            apply (clarsimp split: option.splits cong: conj_cong)
            apply (intro conjI)
                apply (erule valid_objs_valid_tcbs)
               apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb, fastforce)
              apply fastforce
             apply (fastforce simp: reply_tcb_reply_at_def obj_at_def st_tcb_at_def)
            apply (clarsimp simp: sk_obj_at_pred_def obj_at_def is_reply)
           apply (wpsimp wp: hoare_vcg_imp_lift hoare_vcg_all_lift simp: iff_conv_conj_imp)
          apply (wpfix add: Structures_H.thread_state.sel)
          apply (rule_tac Q'="\<lambda>_ s. tcb_at' t s \<and> tcb_at' dest s \<and> valid_objs' s
                                    \<and> sym_heap_sched_pointers s \<and> valid_sched_pointers s
                                    \<and> pspace_aligned' s \<and> pspace_distinct' s \<and> pspace_bounded' s
                                    \<and> (reply_opt \<noteq> None
                                       \<longrightarrow> reply_at' (the reply_opt) s
                                           \<and> replySCs_of s (the reply_opt) = None)
                                    \<and> \<not> is_sched_linked t s
                                    \<and> \<not> is_sched_linked dest s
                                    \<and> \<not> (tcbQueued |< tcbs_of' s) dest
                                    \<and> \<not> (tcbInReleaseQueue |< tcbs_of' s) dest
                                    \<and> t \<noteq> dest \<and> sym_heap_tcbSCs s \<and> sch_act_not dest s
                                    \<and> (cd \<longrightarrow> bound_sc_tcb_at' (\<lambda>scOpt. scOpt \<noteq> None) t s)"
                       in hoare_post_imp)
           apply (clarsimp split: option.splits)
          apply (wpsimp wp: hoare_vcg_imp_lift)
         apply assumption
        apply (prop_tac "tcb_at' t s' \<and> tcb_at' dest s' \<and> ep_at' ep_ptr s' \<and> valid_pspace' s'
                         \<and> sym_heap_sched_pointers s' \<and> valid_sched_pointers s'
                         \<and> valid_objs' s' \<and> valid_mdb' s'
                         \<and> pspace_aligned' s' \<and> pspace_distinct' s' \<and> pspace_bounded' s'
                         \<and> \<not> is_sched_linked t s'
                         \<and> \<not> is_sched_linked dest s'
                         \<and> \<not> (tcbQueued |< tcbs_of' s') dest
                         \<and> \<not> (tcbInReleaseQueue |< tcbs_of' s') dest
                         \<and> t \<noteq> dest \<and> sym_heap_tcbSCs s' \<and> sch_act_not dest s'
                         \<and> (cd \<longrightarrow> bound_sc_tcb_at' (\<lambda>scOpt. scOpt \<noteq> None) t s')", assumption)
        apply clarsimp
        apply (case_tac reply_opt; clarsimp)
        apply (rename_tac reply_ptr, subgoal_tac "reply_at' reply_ptr s'", simp)
         apply (frule (1) replySCs_of_cross, simp)
        apply (erule cross_relF[OF _ reply_at'_cross_rel])
        apply (clarsimp simp: obj_at_def reply_sc_reply_at_def is_reply)
       apply (wpsimp wp: gts_wp)
      apply (rule_tac Q'="\<lambda>_ s'. tcb_at' t s' \<and> tcb_at' dest s' \<and> ep_at' ep_ptr s' \<and> valid_pspace' s'
                                 \<and> sym_heap_sched_pointers s' \<and> valid_sched_pointers s'
                                 \<and> valid_objs' s' \<and> valid_mdb' s'
                                 \<and> pspace_aligned' s' \<and> pspace_distinct' s' \<and> pspace_bounded' s'
                                 \<and> st_tcb_at' runnable' t s'
                                 \<and> \<not> (tcbQueued |< tcbs_of' s') t
                                 \<and> \<not> (tcbInReleaseQueue |< tcbs_of' s') t
                                 \<and> \<not> is_sched_linked dest s'
                                 \<and> \<not> (tcbQueued |< tcbs_of' s') dest
                                 \<and> \<not> (tcbInReleaseQueue |< tcbs_of' s') dest
                                 \<and> t \<noteq> dest \<and> sym_heap_tcbSCs s' \<and> sch_act_not dest s'
                                 \<and> (cd \<longrightarrow> bound_sc_tcb_at' (\<lambda>scOpt. scOpt \<noteq> None) t s')"
                   in hoare_post_imp)
       apply clarsimp
       apply (frule (1) runnable'_Not_tcbInReleaseQueue_not_sched_linked[rotated])
        apply (clarsimp simp: st_tcb_at'_def obj_at'_def opt_pred_def opt_map_red)
       apply simp
      apply (wpsimp wp: gts_wp')
     apply ((wpsimp wp: tcb_ep_dequeue_ep_queued_other[where t=t]
                        tcb_ep_dequeue_not_ep_queued hoare_vcg_all_lift hoare_vcg_imp_lift'
             | wpsimp simp: tcb_ep_dequeue_def
                        wp: get_simple_ko_wp hoare_vcg_all_lift hoare_vcg_imp_lift'
                            hoare_vcg_disj_lift)+)[1]
    apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' hoare_vcg_disj_lift
                simp: valid_pspace'_def)
   apply clarsimp
   apply (frule sym_refs_ep_queues_blocked)
   apply (frule sym_refs_ntfn_queues_blocked)
   apply (prop_tac "(dest, EPRecv) \<in> state_refs_of s ep_ptr")
    apply (clarsimp simp: state_refs_of_def obj_at_def)
   apply (frule (1) sym_refsD, simp)
   apply (frule TCBBlockedRecv_in_state_refs_of)
   apply (clarsimp simp: invs_def pred_tcb_at_eq_commute st_tcb_at_tcb_at cong: conj_cong)
   apply (intro conjI impI allI)
                 apply (clarsimp simp: in_ep_queue_at_def obj_at_def)
                apply (fastforce elim!: runnable_not_ep_queued)
               apply (fastforce elim!: runnable_not_ntfn_queued)
              apply (rule not_ntfn_blocked_not_ntfn_queued)
               apply (clarsimp simp: pred_tcb_at_def obj_at_def opt_map_def split: option.splits)
               subgoal for \<dots> tcb' by (case_tac "tcb_state tcb'"; clarsimp simp: ntfn_blocked_def)
              apply fastforce
             apply (fastforce elim!: ready_queues_runnable_not_queued)
            apply (force elim!: valid_release_q_not_in_release_q_not_runnable)
           apply (simp add: runnable_eq_active)
          apply (erule (1) if_live_then_nonz_capD)
          apply (clarsimp simp: obj_at_def live_def)
         apply (frule valid_sched_action_weak_valid_sched_action)
         apply (force elim!: weak_valid_sched_action_scheduler_action_not)
        apply (frule (1) not_idle_thread[simplified runnable_eq_active[symmetric]])
        apply (clarsimp simp: valid_idle_def)
       apply (rename_tac st)
       apply (case_tac "reply_object st"; simp)
       apply (rename_tac reply_ptr)
       apply (subgoal_tac "data = Some reply_ptr", simp)
        apply (subgoal_tac "reply_tcb_reply_at ((=) (Some dest)) reply_ptr s", simp)
         apply (subgoal_tac "reply_sc_reply_at (\<lambda>a. a = None) reply_ptr s", simp)
          apply (intro conjI)
           apply (clarsimp simp: sk_obj_at_pred_def obj_at_def)
           apply (erule (1) if_live_then_nonz_capD2)
           apply (clarsimp simp: live_def live_reply_def)
          apply clarsimp
          apply (frule (1) valid_repliesD1_simp, clarsimp simp: replies_blocked_def)
          apply (subst (asm) identity_eq[
                               where x="Structures_A.thread_state.BlockedOnReply ptr" for ptr,
                                        symmetric])+
          apply (frule (1) st_tcb_reply_state_refs)
          apply (clarsimp simp: pred_tcb_at_def obj_at_def reply_tcb_reply_at_def)
         apply (subst identity_eq)
         apply (erule (1) valid_replies_ReceiveD[rotated])
          apply (subst identity_eq, assumption, simp)
        apply (subst identity_eq)
        apply (erule st_tcb_recv_reply_state_refs[rotated])
        apply (subst identity_eq, assumption)
       apply (clarsimp simp: pred_tcb_at_def obj_at_def)
      apply clarsimp
     apply force
    apply (fastforce intro!: sendIPC_corres_sym_refs_helper)
   apply (clarsimp simp: obj_at_def pred_tcb_at_def)
  apply (clarsimp simp: invs'_def valid_pspace'_def)
  apply (intro conjI impI allI)
      apply (fastforce intro: tcb_at_cross)
     apply (fastforce intro: tcb_at_cross)
    apply (clarsimp simp: pred_tcb_at_def obj_at_def)
   apply (fastforce intro!: sym_refs_tcbSCs)
  apply (fastforce dest!: bound_sc_tcb_at_cross')
  done

end

crunch maybeReturnSc
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p' s)"
  and sc_at'_n[wp]: "\<lambda>s. Q (sc_at'_n n p s)"
  (wp: crunch_wps)

global_interpretation maybeReturnSc: typ_at_all_props' "maybeReturnSc ntfnPtr tcbPtr"
  by typ_at_props'

global_interpretation setMessageInfo: typ_at_all_props' "setMessageInfo t info"
  by typ_at_props'

context begin interpretation Arch . (*FIXME: arch-split*)

crunch cancel_ipc
  for cur[wp]: "cur_tcb"
  and ntfn_at[wp]: "ntfn_at t"
  (wp: crunch_wps simp: crunch_simps ignore: set_object)

lemma valid_sched_weak_strg:
  "valid_sched s \<longrightarrow> weak_valid_sched_action s"
  by (simp add: valid_sched_def valid_sched_action_def)

lemma idle_tsr:
  "thread_state_relation ts ts' \<Longrightarrow> idle' ts' = idle ts"
  by (case_tac ts, auto)

lemma oblivious_getObject_ksPSpace_default:
  "\<lbrakk> \<forall>s. ksPSpace (f s) = ksPSpace s;
     \<And>a b c ko. (loadObject a b c ko :: 'a kernel_r) \<equiv> loadObject_default a b c ko \<rbrakk>
   \<Longrightarrow> oblivious f (getObject p :: 'a :: pspace_storable kernel)"
  apply (simp add: getObject_def2 split_def loadObject_default_def
                   projectKO_def alignCheck_assert magnitudeCheck_assert)
  apply (intro oblivious_bind; simp)
  by (auto simp: oblivious_def gets_the_def assert_opt_def bind_def gets_def return_def
                 oassert_opt_def read_magnitudeCheck_def get_def fail_def
          split: option.splits)

lemmas oblivious_getObject_ksPSpace_tcb[simp]
    = oblivious_getObject_ksPSpace_default[OF _ loadObject_tcb]

lemma oblivious_setObject_ksPSpace_tcb[simp]:
  "\<lbrakk> \<forall>s. ksPSpace (f s) = ksPSpace s;
     \<forall>s g. ksPSpace_update g (f s) = f (ksPSpace_update g s) \<rbrakk> \<Longrightarrow>
   oblivious f (setObject p (v :: tcb))"
  apply (simp add: setObject_def split_def updateObject_default_def
                   projectKO_def alignCheck_assert magnitudeCheck_assert)
  apply (intro oblivious_bind; simp)
  by (auto simp: oblivious_def assert_opt_def bind_def gets_def return_def
                 oassert_opt_def get_def fail_def
          split: option.splits)

lemma oblivious_getObject_ksPSpace_cte[simp]:
  "\<lbrakk> \<forall>s. ksPSpace (f s) = ksPSpace s \<rbrakk> \<Longrightarrow>
   oblivious f (getObject p :: cte kernel)"
  apply (simp add: getObject_def2 split_def loadObject_cte
                   projectKO_def alignCheck_assert magnitudeCheck_assert
                   typeError_def unless_when
             cong: Structures_H.kernel_object.case_cong)
  apply (intro oblivious_bind;
         simp split: Structures_H.kernel_object.split if_split)
  by (intro conjI impI allI;
      auto simp: oblivious_def assert_opt_def bind_def gets_def return_def
                 get_def fail_def gets_the_def in_omonad omonad_defs
                 read_typeError_def read_alignCheck_def read_magnitudeCheck_def read_alignError_def
          split: option.splits)

lemma gets_the_readReadyTime_corres:
  "rcorres
     (\<lambda>s s'. pspace_aligned s \<and> pspace_distinct s \<and> valid_objs s \<and> is_active_sc scPtr s
             \<and> sc_at sc_ptr s \<and> active_scs_valid s \<and> valid_objs' s' \<and> scs_relation s s'
             \<and> sc_ptr = scPtr)
     (gets_the (read_ready_time sc_ptr)) (gets_the (readReadyTime scPtr))
     (\<lambda>rv rv' _ _. rv = rv')"
  apply (rule_tac F="sc_ptr = scPtr" in rcorres_req, simp)
  apply (rule_tac Q="\<lambda>s s'. sc_refills_sc_at (\<lambda>refills. refills \<noteq> []) scPtr s"
               in rcorres_add_to_pre)
   apply (fastforce intro: valid_refills_nonempty_refills elim: active_scs_validE)
  apply (clarsimp simp: read_ready_time_def readReadyTime_def)
  apply (rule rcorres_split_gets_the_fwd)
    apply (simp flip: get_refill_head_def getRefillHead_def)
    apply (rcorres rcorres: getRefillHead_rcorres)
    apply clarsimp
   apply wpsimp
  apply (fastforce intro: rcorres_return simp: refill_map_def)
  done

lemma active_sc_tcb_at_cross':
  "\<lbrakk>active_sc_tcb_at tcbPtr s; tcbs_relation s s'; scs_relation s s';
    pspace_aligned s; pspace_distinct s; valid_objs s\<rbrakk>
   \<Longrightarrow> active_sc_tcb_at' tcbPtr s'"
  apply (clarsimp simp: vs_all_heap_simps)
  apply (rename_tac sc_ptr tcb sc n)
  apply (frule (1) tcbs_relation_tcb_relation_abs)
  apply (frule (1) scs_relation_sc_relation_abs)
  apply (clarsimp simp: active_sc_tcb_at'_def tcb_relation_def sc_relation_def active_sc_def
                        in_omonad)
  apply metis
  done

lemma readTCBReadyTime_rcorres:
  "rcorres
     (\<lambda>s s'. pspace_aligned s \<and> pspace_distinct s \<and> valid_objs s \<and> active_scs_valid s
             \<and> active_sc_tcb_at tcbPtr s \<and> valid_objs' s'
             \<and> tcbs_relation s s' \<and> scs_relation s s')
     (gets_the (read_tcb_ready_time tcbPtr)) (gets_the (readTCBReadyTime tcbPtr))
     (\<lambda>rv rv' _ _. rv = rv')"
  apply (clarsimp simp: read_tcb_ready_time_def readTCBReadyTime_def
             simp flip: scActive_def)
  apply (rule rcorres_split_gets_the_fwd[where rrel="(=)"])
    apply (rcorres rcorres: threadGet_rcorres)
     apply (clarsimp simp: tcb_relation_def)
    apply (clarsimp simp: vs_all_heap_simps obj_at_def is_tcb_def)
   apply wpsimp
   apply (clarsimp simp: vs_all_heap_simps obj_at_def is_tcb_def)
  apply (rule rcorres_assert_l_fwd)
   apply (clarsimp simp: vs_all_heap_simps obj_at_def thread_read_def oliftM_def get_tcb_def)
  apply (clarsimp simp: gets_the_ohaskell_assert)
  apply (rule rcorres_assert_r_fwd)
  apply (rule rcorres_symb_exec_r[OF scActive_sp])
  apply (rule rcorres_assert_r_fwd)
  apply (rcorres rcorres: gets_the_readReadyTime_corres)
  apply (fastforce dest: thread_read_SomeD
                   simp: vs_all_heap_simps obj_at_def is_sc_obj_def
                  intro: valid_objs_valid_sched_context_size)
  done

lemma no_ofail_readReadyTime[wp]:
  "no_ofail (valid_objs' and active_sc_at' scPtr) (readReadyTime scPtr)"
  unfolding readReadyTime_def
  by wpsimp

lemma no_ofail_readTCBReadyTime:
  "no_ofail
     (\<lambda>s'. \<exists>s. pspace_aligned s \<and> pspace_distinct s \<and> valid_objs s \<and> active_scs_valid s
               \<and> active_sc_tcb_at tcbPtr s \<and> valid_objs' s'
               \<and> heap_pspace_relation s s')
     (readTCBReadyTime tcbPtr)"
  unfolding readTCBReadyTime_def
  apply (wpsimp wp: ovalid_threadRead)
  apply (rename_tac s' s)
  apply (frule pspace_aligned_cross)
   apply (simp flip: pspace_relation_heap_pspace_relation)
  apply (frule pspace_distinct_cross)
    apply fastforce
   apply (simp flip: pspace_relation_heap_pspace_relation)
  apply (prop_tac "pspace_bounded' s'")
   apply (rule pspace_relation_pspace_bounded')
   apply (simp flip: pspace_relation_heap_pspace_relation)
  apply (frule active_sc_tcb_at_tcb_at)
  apply (intro context_conjI impI allI)
   apply (fastforce intro!: tcb_at_cross_tcbs_relation)
  apply normalise_obj_at'
  apply (frule active_sc_tcb_at_tcb_at)
  apply (clarsimp simp: obj_at_def is_tcb_def)
  apply (rename_tac ko')
  apply (case_tac ko'; clarsimp)
  apply (frule tcbs_relation_tcb_relation_abs)
   apply fastforce
  apply (clarsimp simp: heap_pspace_relation_def)
  apply (frule (5) active_sc_tcb_at_cross')
  apply (intro context_conjI impI allI)
     apply (clarsimp simp: active_sc_tcb_at'_def obj_at'_def opt_pred_def opt_map_def
                    split: option.splits)
    apply (fastforce intro!: sc_at_cross_scs_relation valid_objs_valid_sched_context_size
                       simp: vs_all_heap_simps obj_at_kh_kheap_simps tcb_relation_def
                             is_sc_obj_def obj_at'_def)
   apply (fastforce simp: active_sc_tcb_at'_def obj_at'_def opt_pred_def opt_map_def)
  apply (fastforce simp: active_sc_at'_def obj_at'_def opt_pred_def opt_map_def)
  done

crunch setReprogramTimer
  for (no_fail) no_fail[wp]

lemma set_gets_release_queue_simp:
  "do _ \<leftarrow> set_release_queue q; f q od = do set_release_queue q; q' \<leftarrow> gets release_queue; f q' od"
  by (simp add: simpler_gets_def bind_def modify_def get_def put_def)

crunch orderedInsert
  for tcbQueued[wp]: "\<lambda>s. P (tcbQueued |< tcbs_of' s)"
  (wp: crunch_wps)

lemma valid_release_queue_sorted_wrt':
  "valid_release_q s \<Longrightarrow> sorted_wrt (img_ord (\<lambda>t. read_tcb_ready_time t s) opt_ord) (release_queue s)"
  by (simp add: valid_release_q_def sorted_release_q_def
                tcb_ready_times_of_tcb_refill_ready_times_of
                read_tcb_ready_time_read_tcb_ready_times_of)

lemma det_wp_ready_times_append:
  "det_wp (\<lambda>s. qs = release_queue s \<and> active_scs_valid s \<and> valid_release_q s \<and> active_sc_tcb_at t s)
          (ready_times_append t qs)"
  unfolding ready_times_append_def
  apply wpsimp
  by (fastforce intro: valid_release_q_active_sc no_ofailD[OF read_tcb_ready_time_no_ofail])

lemmas no_fail_ready_times_append = det_wp_no_fail[OF det_wp_ready_times_append]

lemma det_wp_ready_times_append_set_release_queue:
  "det_wp (\<lambda>s. ls = release_queue s \<and> active_scs_valid s \<and> valid_release_q s \<and> active_sc_tcb_at t s)
          (ready_times_append t ls >>= set_release_queue)"
  by (wpsimp wp: det_wp_ready_times_append)

lemmas no_fail_ready_times_append_set_release_queue =
  det_wp_no_fail[OF det_wp_ready_times_append_set_release_queue]

lemma ready_times_append_set_release_queue_empty_fail:
  "empty_fail (ready_times_append t ls >>= set_release_queue)"
  by wpsimp

lemmas ready_times_append_rules =
  no_fail_ready_times_append det_wp_ready_times_append no_fail_ready_times_append_set_release_queue
  det_wp_ready_times_append_set_release_queue ready_times_append_set_release_queue_empty_fail
  ready_times_append_empty_fail

method rlq_append =
  (rule det_wp_pre no_fail_pre, rule ready_times_append_rules, fastforce)[1] | wpsimp

lemma orderedInsert_readTCBReadyTime_rcorres:
  "rcorres
     (\<lambda>s s'. valid_release_q s \<and> ts = release_queue s
             \<and> release_queue_relation s s' \<and> q = ksReleaseQueue s'
             \<and> heap_pspace_relation s s' \<and> sym_heap_sched_pointers s'
             \<and> pspace_aligned s \<and> pspace_distinct s
             \<and> \<not> is_sched_linked t s' \<and> not_in_release_q t s \<and> active_sc_tcb_at t s
             \<and> active_scs_valid s \<and> valid_objs s \<and> valid_objs' s')
     (ready_times_append t ts) (orderedInsert t q readTCBReadyTime (\<le>))
     (\<lambda>ts' q' s s'. list_queue_relation ts' q' (tcbSchedNexts_of s') (tcbSchedPrevs_of s'))"
  apply (rcorres rcorres: orderedInsert_rcorres readTCBReadyTime_rcorres
                      wp: read_tcb_ready_time_no_ofail no_ofail_readTCBReadyTime
                    simp: ready_times_append_def)
  apply clarsimp
  apply (frule pspace_aligned_cross)
   apply (simp flip: pspace_relation_heap_pspace_relation)
  apply (frule (1) pspace_distinct_cross)
   apply (simp flip: pspace_relation_heap_pspace_relation)
  apply (frule valid_release_queue_sorted_wrt')
  apply (clarsimp simp: valid_release_q_def)
  apply (fastforce intro!: tcb_at_cross_tcbs_relation active_sc_tcb_at_tcb_at
                     simp: heap_pspace_relation_def release_queue_relation_def not_in_release_q_def)
  done

lemma orderedInsert_readTCBReadyTime_rcorres_other:
  "rcorres
     (\<lambda>s s'. valid_release_q s \<and> ts' = release_queue s \<and> q' = ksReleaseQueue s'
             \<and> release_queue_relation s s'
             \<and> list_queue_relation ts q (tcbSchedNexts_of s') (tcbSchedPrevs_of s')
             \<and> heap_pspace_relation s s' \<and> sym_heap_sched_pointers s'
             \<and> pspace_aligned s \<and> pspace_distinct s
             \<and> t' \<notin> set ts \<and> set ts \<inter> set (release_queue s) = {}
             \<and> active_sc_tcb_at t' s \<and> active_scs_valid s \<and> valid_objs s \<and> valid_objs' s')
     (ready_times_append t' ts') (orderedInsert t' q' readTCBReadyTime (\<le>))
     (\<lambda>_ _ s s'. list_queue_relation ts q (tcbSchedNexts_of s') (tcbSchedPrevs_of s'))"
  apply (clarsimp simp: ready_times_append_def)
  apply (rcorres rcorres: orderedInsert_rcorres_other readTCBReadyTime_rcorres
                      wp: read_tcb_ready_time_no_ofail no_ofail_readTCBReadyTime)
  apply (clarsimp simp: valid_release_q_def)
  apply (frule pspace_aligned_cross)
   apply (simp flip: pspace_relation_heap_pspace_relation)
  apply (frule (1) pspace_distinct_cross)
   apply (simp flip: pspace_relation_heap_pspace_relation)
  by (fastforce intro!: tcb_at_cross_tcbs_relation active_sc_tcb_at_tcb_at
                  simp: heap_pspace_relation_def release_queue_relation_def)

lemma tcbReleaseEnqueue_corres:
  "corres dc
     (valid_objs and pspace_aligned and pspace_distinct and valid_release_q
      and active_scs_valid and active_sc_tcb_at t and not_in_release_q t and not_queued t
      and ready_or_release and st_tcb_at runnable t and ep_queues_blocked and ntfn_queues_blocked)
     (valid_objs' and sym_heap_sched_pointers and valid_sched_pointers)
     (tcb_release_enqueue t) (tcbReleaseEnqueue t)"
  supply if_split[split del]
         heap_path_append[simp del] heap_path.simps[simp del]
         ghost_relation_wrapper_def[simp del] (*FIXME arch-split RT: not necessary after arch-split*)
         heap_ghost_relation_wrapper_def[simp del] (*FIXME arch-split RT: not necessary after arch-split*)
  apply (rule_tac Q'="tcb_at' t" in corres_cross_add_guard)
   apply (fastforce intro!: tcb_at_cross)
  apply (rule_tac Q'="\<lambda>s'. \<not> (tcbInReleaseQueue |< tcbs_of' s') t" in corres_cross_add_guard)
   apply (frule state_relation_release_queue_relation)
   apply (frule in_release_q_tcbInReleaseQueue_eq[where t=t])
   apply (clarsimp simp: in_release_q_def)
  apply (clarsimp simp: tcb_release_enqueue_def tcbReleaseEnqueue_def)
  apply (rule corres_stateAssert_ignore)
   apply (fastforce dest!: release_queue_active_sc_tcb_at_cross)
  apply (rule corres_stateAssert_add_assertion[rotated])
   apply (fastforce intro: ready_or_release_cross)
  apply (rule corres_stateAssert_add_assertion[rotated])
   apply (fastforce dest!: state_relation_ready_queues_relation in_ready_q_tcbQueued_eq
                     simp: vs_all_heap_simps opt_map_def obj_at'_def)
  apply (rule corres_stateAssert_ignore, fastforce intro: ksReadyQueues_asrt_cross)
  apply (rule corres_stateAssert_ignore, fastforce intro: ksReleaseQueue_asrt_cross)
  apply (rule corres_stateAssert_ignore, simp)
  apply (rule corres_symb_exec_r[rotated, OF isRunnable_sp]; wpsimp?)
  apply (rule corres_symb_exec_r_conj_ex_abs_forwards[rotated, OF assert_sp]; wpsimp)
   apply (fastforce dest: st_tcb_at_runnable_cross simp: ex_abs_def)
  apply (rule corres_symb_exec_r[rotated, OF get_tcb_sp']; wpsimp?)
  apply (rule corres_symb_exec_r_conj_ex_abs_forwards[rotated, OF assert_sp]; wpsimp?)
   apply (fastforce dest: state_relation_release_queue_relation
                    simp: ex_abs_def release_queue_relation_def
                          opt_pred_def opt_map_def obj_at'_def not_in_release_q_def)
  apply (rule corres_split_forwards'[OF _ gets_sp getReleaseQueue_sp])
   apply (corres corres: getReleaseQueue_corres)
  apply (rename_tac ls q)
  apply (rule monadic_rewrite_corres_l[where P=P and Q=P for P, simplified])
   apply (rule monadic_rewrite_bind_tail)
    apply (rule monadic_rewrite_from_simple[where P=True, simplified])
    apply (rule set_gets_release_queue_simp)
   apply wpsimp
  \<comment> \<open>split off the reprogramming of the timer\<close>
  apply (subst bind_assoc[symmetric])
  apply (subst bind_assoc_group3)
  apply (rule corres_split_forwards'[where Q="\<lambda>_ s. release_queue s \<noteq> []" and r'=dc, rotated];
         (solves wpsimp)?)
    apply (clarsimp simp: ready_times_append_def)
    apply wpsimp
   apply clarsimp
   apply (rule corres_split_forwards'[OF _ gets_sp getReleaseQueue_sp])
    apply (corres corres: getReleaseQueue_corres)
   apply (clarsimp simp: when_def)
   apply (rule corres_if_strong')
     apply (fastforce simp: tcbQueueEmpty_def)
    apply (corres corres: setReprogramTimer_corres)
   apply fastforce
  \<comment> \<open>set the release queue\<close>
  apply (rule corres_underlying_from_rcorres)
   apply (wpsimp wp: no_fail_orderedInsert)
   apply (rename_tac s' s)
   apply (prop_tac "heap_pspace_relation s s'")
    apply (simp flip: pspace_relation_heap_pspace_relation)
    apply fastforce
   apply (frule state_relation_release_queue_relation)
   apply (clarsimp simp: release_queue_relation_def)
   subgoal
     by (fastforce intro!: no_ofailD[OF no_ofail_readTCBReadyTime]
                           tcb_at_cross active_sc_tcb_at_tcb_at
                     simp: valid_release_q_def)
  apply (rule_tac Q="\<lambda>s s'. (\<forall>t\<in>set (release_queue s). active_sc_tcb_at t s)
                            \<and> t \<notin> set (release_queue s)
                            \<and> list_queue_relation (release_queue s) (ksReleaseQueue s')
                                                  (tcbSchedNexts_of s') (tcbSchedPrevs_of s')
                            \<and> (\<forall>t\<in>set (release_queue s). tcb_at' t s')"
               in rcorres_add_to_pre)
  apply (intro context_conjI ballI)
      apply (fastforce intro!: valid_release_q_active_sc)
     apply (clarsimp simp: not_in_release_q_def)
    apply (fastforce dest!: state_relation_release_queue_relation simp: release_queue_relation_def)
   apply (force intro!: tcb_at_cross valid_release_q_active_sc dest: active_sc_tcb_at_tcb_at)
  apply (clarsimp simp: state_relation_def pspace_relation_heap_pspace_relation
                        heap_pspace_relation_def ghost_relation_heap_ghost_relation)
  apply (rcorres_conj_lift \<open>fastforce\<close>
                           rule: ready_times_append_rules
                             wp: threadSet_field_inv
                           simp: ready_times_append_def)+
  apply (rule rcorres_conj_lift_fwd; (solves rlq_append)?)
    \<comment> \<open>ep_queues_relation\<close>
   apply (rule rcorres_add_return_l)
   apply (simp only: ep_queues_relation_def bind_assoc)
   apply (rcorres rcorres: rcorres_threadSet_list_queue_relation
                           orderedInsert_readTCBReadyTime_rcorres_other readTCBReadyTime_rcorres
                           rcorres_op_lifts
                       wp: det_wp_ready_times_append no_fail_ready_times_append)
   apply (clarsimp simp: heap_pspace_relation_def)
   apply (intro conjI)
    apply (erule (2) runnable_not_in_ep_queue)
   apply (frule valid_release_q_release_q_runnable)
   apply (blast dest: ep_queues_release_queue_disjoint)
  apply (rule rcorres_conj_lift_fwd; (solves rlq_append)?)
    \<comment> \<open>ntfn_queues_relation\<close>
   apply (rule rcorres_add_return_l)
   apply (simp only: ntfn_queues_relation_def bind_assoc)
   apply (rcorres rcorres: rcorres_threadSet_list_queue_relation
                           orderedInsert_readTCBReadyTime_rcorres_other readTCBReadyTime_rcorres
                           rcorres_op_lifts
                       wp: det_wp_ready_times_append no_fail_ready_times_append)
   apply (clarsimp simp: heap_pspace_relation_def)
   apply (intro conjI)
    apply (erule (2) runnable_not_in_ntfn_queue)
   apply (frule valid_release_q_release_q_runnable)
   apply (blast dest: ntfn_queues_release_queue_disjoint)
  apply (rule rcorres_conj_lift_fwd; (solves rlq_append)?)
    \<comment> \<open>ready_queues_relation\<close>
   apply (clarsimp simp: ready_queues_relation_def ready_queue_relation_def Let_def)
   apply (intro rcorres_allI_fwd; (solves rlq_append)?)
   apply (rename_tac d p)
   apply (rule rcorres_conj_lift_fwd; (solves rlq_append)?)
    apply (rule_tac p="\<lambda>s. ready_queues s d p" in rcorres_lift_abs)
     apply (rule_tac p="\<lambda>s'. ksReadyQueues s' (d, p)" in rcorres_lift_conc)
      apply (rule rcorres_add_return_l)
      apply (simp only: bind_assoc)
      apply (rcorres rcorres: rcorres_threadSet_list_queue_relation
                              rcorres_setReleaseQueue_list_queue_relation_other
                              orderedInsert_readTCBReadyTime_rcorres_other readTCBReadyTime_rcorres
                          wp: det_wp_ready_times_append no_fail_ready_times_append)
      apply (clarsimp simp: heap_pspace_relation_def not_queued_def)
      apply (blast dest: ready_or_release_disjoint)
     apply wpsimp
    apply wpsimp
   apply (rule rcorres_conj_lift_fwd; (solves rlq_append)?)
    apply (intro rcorres_allI_fwd; (solves rlq_append)?)
    apply (rename_tac t')
    apply (rule_tac p="\<lambda>s. t' \<in> set (ready_queues s d p)" in rcorres_lift_abs)
     apply (rule rcorres_lift_conc_only_fwd; (solves rlq_append)?)
     apply (wpsimp wp: threadSet_inQ)
    apply wpsimp
   apply (rule rcorres_from_valid_det; rlq_append)
  apply (rule rcorres_conj_lift_fwd; (solves rlq_append)?)
   \<comment> \<open>release_queue_relation\<close>
   apply (clarsimp simp: release_queue_relation_def)
   apply (rule rcorres_conj_lift_fwd; (solves rlq_append)?)
    apply (rule rcorres_add_return_l)
    apply (simp only: bind_assoc)
    apply (rcorres rcorres: orderedInsert_readTCBReadyTime_rcorres
                            rcorres_threadSet_release_queue_list_queue_relation)
    apply (elim conjE)
    apply (frule (2) valid_sched_pointersD[where t=t])
     apply (fastforce intro!: runnable'_not_inIPCQueueThreadState)
    apply (clarsimp simp: heap_pspace_relation_def release_queue_relation_def)
   apply (intro rcorres_allI_fwd; (solves rlq_append)?)
   apply (rename_tac t')
   apply (rule rcorres_from_valid_det; (solves rlq_append)?)
   apply (clarsimp simp: ready_times_append_def in_monad)
   apply (frule use_valid[OF _ ordered_insert_set], simp)
   apply (case_tac "t' = t")
    apply (wpsimp wp: threadSet_wp hoare_vcg_all_lift hoare_drop_imps)
   apply (wpsimp wp: threadSet_opt_pred_other)
  by (rcorres_conj_lift \<open>fastforce\<close> rule: ready_times_append_rules)+

lemma tcbSchedDequeue_not_sched_linked:
  "tcbSchedDequeue t \<lbrace>\<lambda>s. \<not> is_sched_linked t s\<rbrace>"
  unfolding tcbSchedDequeue_def
  by (wpsimp wp: threadGet_wp threadSet_field_inv tcbQueueRemove_not_sched_linked[simplified])

lemma postpone_corres:
  "corres dc
     (\<lambda>s. valid_objs s \<and> pspace_aligned s \<and> pspace_distinct s
          \<and> sym_refs (state_refs_of s)
          \<and> valid_release_q s \<and> in_correct_ready_q s \<and> ready_qs_distinct s \<and> ready_or_release s
          \<and> active_scs_valid s \<and> is_active_sc ptr s \<and> ready_queues_runnable s
          \<and> sc_tcb_sc_at (\<lambda>sc. \<exists>t. sc = Some t \<and> not_queued t s \<and> not_in_release_q t s
                                   \<and> pred_map runnable (tcb_sts_of s) t) ptr s)
     (pspace_aligned' and pspace_distinct' and pspace_bounded'
      and valid_objs' and sym_heap_sched_pointers and valid_sched_pointers)
     (SchedContext_A.postpone ptr) (postpone ptr)"
  apply (clarsimp simp: SchedContext_A.postpone_def postpone_def get_sc_obj_ref_def)
  apply (rule corres_stateAssert_ignore, simp)
  apply (rule_tac Q="sc_at ptr" in corres_cross_add_abs_guard)
   apply (fastforce intro: valid_objs_valid_sched_context_size
                     simp: vs_all_heap_simps obj_at_def is_obj_defs)
  apply (rule corres_split_forwards'[OF _ get_sched_context_sp get_sc_sp'])
   apply (corres corres: get_sc_corres)
  apply (rule corres_assert_opt_assume_lhs[rotated])
   apply (clarsimp simp: obj_at_def  sc_at_ppred_def)
  apply (rule corres_assert_gen_asm_cross_forwards)
   apply (clarsimp simp: sc_relation_def)
  apply (clarsimp simp: sc_relation_def)
  apply (rule stronger_corres_guard_imp)
    apply (rule corres_split[OF tcbSchedDequeue_corres], simp)
      apply (rule corres_split[OF tcbReleaseEnqueue_corres])
        apply (rule setReprogramTimer_corres)
       apply wpsimp
      apply wpsimp
     apply (wpsimp wp: tcb_sched_dequeue_not_queued_inv)
    apply (wpsimp wp: tcbSchedDequeue_not_sched_linked)
   apply (force dest!: sym_ref_sc_tcb
                 simp: vs_all_heap_simps valid_obj_def obj_at_def is_obj_defs sc_at_ppred_def
                       obj_at_kh_kheap_simps)
  apply fastforce
  done

lemma schedContextResume_corres:
  "corres dc
     (valid_objs and pspace_aligned and pspace_distinct and valid_ready_qs and valid_release_q
      and active_scs_valid and sc_tcb_sc_at (\<lambda>sc. sc \<noteq> None) ptr and ready_or_release
      and (\<lambda>s. sym_refs (state_refs_of s)))
     (pspace_aligned' and pspace_distinct' and pspace_bounded' and valid_objs'
      and sym_heap_sched_pointers and valid_sched_pointers)
     (sched_context_resume ptr) (schedContextResume ptr)"
  apply (rule_tac Q="sc_at ptr" in corres_cross_add_abs_guard)
   apply (fastforce intro: sc_at_pred_n_sc_at)
  apply (clarsimp simp: sched_context_resume_def schedContextResume_def)
  apply (rule corres_stateAssert_ignore, simp)
  apply (rule corres_split_forwards'[OF _ get_sched_context_sp get_sc_sp'])
   apply (corres corres: get_sc_corres)
  apply (rule corres_assert_opt_assume_lhs[rotated])
   apply (clarsimp simp: sc_at_ppred_def obj_at_def)
  apply (rule corres_assert_gen_asm_cross_forwards)
   apply (clarsimp simp: sc_relation_def)
  apply clarsimp
  apply (rename_tac sctcb n scTcb)
  apply (rule_tac F="scTcb = sctcb" in corres_req, clarsimp simp: sc_relation_def)
  apply clarsimp
  apply (rule_tac Q="tcb_at sctcb" in corres_cross_add_abs_guard)
   apply (force dest: valid_objs_valid_sched_context
                simp: valid_sched_context_def obj_at_def)
  apply (rule corres_split_forwards'[where r'="(=)", OF _ gets_sp getSchedulable_sp])
   apply (corres corres: getSchedulable_corres)
  apply (clarsimp simp: when_def)
  apply (rule corres_symb_exec_l[OF _ _ thread_get_sp, rotated]; (solves wpsimp)?)
  apply (rename_tac ts)
  apply (rule_tac F="runnable ts" in corres_req)
   apply (clarsimp simp: schedulable_def2 pred_tcb_at_def obj_at_def)
  apply clarsimp
  apply (rule_tac Q="\<lambda>s. is_active_sc ptr s \<and> valid_refills ptr s
                         \<and> sc_refills_sc_at (\<lambda>refills. refills \<noteq> []) ptr s"
               in corres_cross_add_abs_guard)
   apply (intro context_conjI)
     apply (clarsimp simp: is_active_sc_rewrite schedulable_def)
     apply (prop_tac "(tcb_scs_of s) sctcb = Some ptr")
      apply (fastforce dest!: sym_ref_sc_tcb
                        simp: opt_map_def tcbs_of_kh_def obj_at_def)
     apply (clarsimp simp: is_active_sc2_def opt_pred_def opt_map_red active_sc_def
                           vs_all_heap_simps
                    split: option.splits)
    apply (fastforce elim: active_scs_validE)
   apply (fastforce elim: valid_refills_nonempty_refills)
  apply (rule corres_split_forwards'[OF _ get_sc_refill_ready_sp refillReady_sp])
   apply (corres corres: refillReady_corres)
   apply (fastforce intro!: is_active_sc'2_cross valid_objs'_valid_refills')
  apply (rule corres_split_forwards'[OF _ get_sc_refill_sufficient_sp refillSufficient_sp])
   apply (corres corres: getRefillSufficient_corres)
  apply (rule corres_if_strong')
    apply (clarsimp simp: active_sc_def vs_all_heap_simps sc_at_ppred_def obj_at_def)
   apply (rule corres_symb_exec_l[OF _ _ thread_get_sp, rotated]; (solves wpsimp)?)
   apply (rule corres_symb_exec_l[OF _ _ thread_get_sp, rotated]; (solves wpsimp)?)
   apply (clarsimp simp: get_tcb_queue_def)
   apply (rule corres_symb_exec_l[OF _ _ gets_sp, rotated]; (solves wpsimp)?)
   apply (rule corres_assert_assume_l_forward)
    apply (clarsimp simp: obj_at_def)
    apply (frule valid_refills_refill_sufficient)
    apply (fastforce dest: sym_ref_sc_tcb
                     simp: valid_ready_qs_def released_sc_tcb_at_def vs_all_heap_simps
                           sc_at_ppred_def obj_at_def)
   apply (corres corres: postpone_corres)
    apply (intro context_conjI impI allI; clarsimp?)
    apply (clarsimp simp: vs_all_heap_simps sc_at_ppred_def obj_at_def schedulable_def
                          not_in_release_q_def in_ready_q_def)
    apply (frule (2) in_correct_ready_qD)
    apply clarsimp
   apply clarsimp
  apply clarsimp
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

lemma maybeDonateSc_corres:
  "corres dc
     (tcb_at tcb_ptr and ntfn_at ntfn_ptr and weak_valid_sched_action
      and valid_ready_qs and active_scs_valid and valid_release_q and ready_or_release
      and valid_objs and pspace_aligned and pspace_distinct and (\<lambda>s. sym_refs (state_refs_of s)))
     (valid_objs' and sym_heap_sched_pointers and valid_sched_pointers)
     (maybe_donate_sc tcb_ptr ntfn_ptr)
     (maybeDonateSc tcb_ptr ntfn_ptr)"
  apply (rule_tac Q'="tcb_at' tcb_ptr" in corres_cross_add_guard)
   apply (fastforce intro!: tcb_at_cross)
  apply (rule_tac Q'=pspace_aligned' in corres_cross_add_guard)
   apply (fastforce dest!: pspace_aligned_cross)
  apply (rule_tac Q'=pspace_distinct' in corres_cross_add_guard)
   apply (fastforce dest!: pspace_distinct_cross)
  apply (rule_tac Q'=pspace_bounded' in corres_cross_add_guard)
   apply (fastforce intro!: pspace_relation_pspace_bounded')
  unfolding maybeDonateSc_def maybe_donate_sc_def
  apply (simp add: get_tcb_obj_ref_def get_sk_obj_ref_def liftM_def maybeM_def get_sc_obj_ref_def)
  apply add_sym_refs
  apply (rule corres_stateAssert_assume)
   apply (rule stronger_corres_guard_imp)
     apply (rule corres_split[OF threadGet_corres, where r'="(=)"])
        apply (clarsimp simp: tcb_relation_def)
       apply (rule corres_when, simp)
       apply (rule corres_split[OF getNotification_corres])
         apply (rule corres_option_split)
           apply (clarsimp simp: ntfn_relation_def)
          apply (rule corres_return_trivial)
         apply (simp add: get_tcb_obj_ref_def liftM_def maybeM_def)
         apply (rule corres_split[OF get_sc_corres])
           apply (rule corres_when)
            apply (clarsimp simp: sc_relation_def)
           apply (rule corres_split[OF schedContextDonate_corres])
             apply (rule schedContextResume_corres, simp)
            apply clarsimp
            apply wpsimp
            apply (rule_tac Q'="\<lambda>_. valid_objs and valid_ready_qs and
                      pspace_aligned and pspace_distinct and (\<lambda>s. sym_refs (state_refs_of s)) and
                      active_scs_valid and valid_release_q and
                      sc_not_in_release_q xa and sc_tcb_sc_at ((=) (Some tcb_ptr)) xa and
                      ready_or_release"
                   in hoare_strengthen_post[rotated])
             apply (fastforce simp: sc_at_pred_n_def obj_at_def)
            apply (wpsimp wp: sched_context_donate_sym_refs
                              sched_context_donate_sc_not_in_release_q
                              sched_context_donate_sc_tcb_sc_at)
           apply (wpsimp wp: schedContextDonate_valid_objs')
          apply (wpsimp wp: get_simple_ko_wp getNotification_wp)+
      apply (wpsimp wp: thread_get_wp' threadGet_wp)+
    apply (clarsimp simp: tcb_at_kh_simps pred_map_eq_normalise invs_def valid_state_def valid_pspace_def
                   split: option.splits cong: conj_cong)
    apply (rename_tac sc_ptr)
    apply (subgoal_tac "sc_at sc_ptr s", clarsimp)
     apply (subgoal_tac "pred_map_eq None (tcb_scps_of s) tcb_ptr", clarsimp)
      apply (intro conjI)
               apply fastforce+
        apply (erule (1) weak_valid_sched_action_no_sc_sched_act_not)
       apply (erule (1) valid_release_q_no_sc_not_in_release_q)
      apply clarsimp
      apply (drule heap_refs_retractD[OF sym_refs_retract_tcb_scps, rotated], simp)
      apply (clarsimp simp: vs_all_heap_simps obj_at_def)
     apply (clarsimp simp: vs_all_heap_simps obj_at_def)
    apply (frule valid_objs_ko_at[where ptr=ntfn_ptr, rotated], clarsimp)
    apply (clarsimp simp: valid_obj_def valid_ntfn_def)
   apply (clarsimp simp: tcb_at'_ex_eq_all split: option.splits)
  apply fastforce
  done

lemma tcbReleaseEnqueue_valid_objs'[wp]:
  "tcbReleaseEnqueue tcbPtr \<lbrace>valid_objs'\<rbrace>"
  unfolding tcbReleaseEnqueue_def
  by (wpsimp wp: getTCB_wp)

lemma orderedInsert_sym_heap_sched_pointers[wp]:
  "\<lbrace>\<lambda>s. \<not> is_sched_linked t s\<rbrace>
   orderedInsert t q f R
   \<lbrace>\<lambda>_. sym_heap_sched_pointers\<rbrace>"
  unfolding orderedInsert_def
  by (wpsimp wp: tcbQueuePrepend_sym_heap_sched_pointers
                 tcbQueueAppend_sym_heap_sched_pointers
                 tcbQueueInsert_sym_heap_sched_pointers hoare_drop_imps)

lemma tcbReleaseEnqueue_sym_heap_sched_pointers[wp]:
  "\<lbrace>valid_sched_pointers\<rbrace>
   tcbReleaseEnqueue tcbPtr
   \<lbrace>\<lambda>_. sym_heap_sched_pointers\<rbrace>"
  unfolding tcbReleaseEnqueue_def
  apply (wpsimp wp: getTCB_wp)
  apply (erule (1) valid_sched_pointersD[simplified])
   apply (force simp: opt_pred_def obj_at'_def opt_map_red)
  apply (fastforce intro!: runnable'_not_inIPCQueueThreadState)
  done

crunch postpone, schedContextResume, maybeDonateSc
  for sym_heap_sched_pointers[wp]: sym_heap_sched_pointers
  and valid_objs'[wp]: valid_objs'
  (simp: crunch_simps wp: crunch_wps)

crunch refillUnblockCheck
  for bound_tcb_sc_at[wp]: "obj_at' (\<lambda>a. \<exists>y. scTCB a = Some y) t"
  (wp: crunch_wps simp: crunch_simps)

lemma in_correct_ready_q_reprogram_timer[simp]:
  "in_correct_ready_q (release_queue_update f s) = in_correct_ready_q s"
  by (clarsimp simp: in_correct_ready_q_def)

lemma in_correct_ready_q_ready_qs_distinct[simp]:
  "ready_qs_distinct (release_queue_update f s) = ready_qs_distinct s"
  by (clarsimp simp: ready_qs_distinct_def)

crunch maybe_donate_sc
  for in_correct_ready_q[wp]: in_correct_ready_q
  and ready_qs_distinct[wp]: ready_qs_distinct
  (ignore: tcb_sched_action wp: crunch_wps simp: crunch_simps)

lemma tcbInReleaseQueue_True_valid_sched_pointers[wp]:
  "\<lbrace>valid_sched_pointers_except tcbPtr\<rbrace>
   threadSet (tcbInReleaseQueue_update \<top>) tcbPtr
   \<lbrace>\<lambda>_. valid_sched_pointers\<rbrace>"
  apply (wpsimp wp: threadSet_wp)
  apply (clarsimp simp: valid_sched_pointers_def opt_pred_def)
  done

lemma orderedInsert_valid_sched_pointers_except:
  "\<lbrace>\<lambda>s. valid_sched_pointers s\<rbrace>
   orderedInsert t q f R
   \<lbrace>\<lambda>_. valid_sched_pointers_except t\<rbrace>"
  unfolding orderedInsert_def
  by (wpsimp wp: tcbQueuePrepend_valid_sched_pointers_except
                 tcbQueueAppend_valid_sched_pointers_except
                 tcbQueueInsert_valid_sched_pointers_except hoare_drop_imps)

lemma tcbReleaseEnqueue_valid_sched_pointers[wp]:
  "\<lbrace>valid_sched_pointers and sym_heap_sched_pointers\<rbrace>
   tcbReleaseEnqueue tcbPtr
   \<lbrace>\<lambda>_. valid_sched_pointers\<rbrace>"
  unfolding tcbReleaseEnqueue_def
  by (wpsimp wp: orderedInsert_valid_sched_pointers_except getTCB_wp)

crunch maybeDonateSc
  for pspace_aligned'[wp]: pspace_aligned'
  and pspace_distinct'[wp]: pspace_distinct'
  and pspace_bounded'[wp]: pspace_bounded'
  and valid_sched_pointers[wp]: valid_sched_pointers
  (simp: crunch_simps wp: crunch_wps)

lemma ntfnSetActive_corres:
  "msg = msg' \<Longrightarrow>
   corres dc
     (obj_at (\<lambda>ko. ko = kernel_object.Notification ntfn \<and> (ntfn_queue_of ntfn) = []) ntfn_ptr
      and pspace_aligned and pspace_distinct) \<top>
     (set_notification ntfn_ptr (ntfn_set_obj ntfn (ActiveNtfn msg)))
     (ntfnSetActive ntfn_ptr msg')"
  apply (rule_tac Q="ntfn_at ntfn_ptr" in corres_cross_add_abs_guard)
   apply (fastforce simp: obj_at_def is_ntfn_def)
  apply (rule_tac Q'="ntfn_at' ntfn_ptr" in corres_cross_add_guard)
   apply (fastforce intro: ntfn_at_cross)
  apply (clarsimp simp: ntfnSetActive_def)
  apply (clarsimp simp: updateNotification_def)
  apply (rule corres_symb_exec_r[OF _ get_ntfn_sp'], rename_tac ntfn')
    apply (rule_tac F="ntfn_relation ntfn ntfn'" in corres_req)
     apply (fastforce dest: state_relation_pspace_relation  ntfns_relation_ntfn_relation_abs
                      simp: pspace_relation_heap_pspace_relation obj_at_def obj_at'_def)
    apply (corres corres: setNotification_no_queue_update_corres)
      apply (clarsimp simp: ntfn_relation_def)
     apply (clarsimp simp: obj_at_def)
    apply (clarsimp simp: obj_at'_def)
   apply wpsimp
  apply wpsimp
  done

crunch maybe_donate_sc
  for ep_queues_blocked[wp]: ep_queues_blocked
  and ntfn_queues_blocked[wp]: ntfn_queues_blocked
  (wp: ep_queues_blocked_lift ntfn_queues_blocked_lift crunch_wps)

lemma cancelIPC_receiveBlocked_not_sched_linked:
  "\<lbrace>st_tcb_at' receiveBlocked t\<rbrace> cancelIPC t \<lbrace>\<lambda>_ s. \<not> is_sched_linked t s\<rbrace>"
  apply (clarsimp simp: cancelIPC_def)
  apply (intro bind_wp[OF _ stateAssert_inv] bind_wp[OF _ gts_sp'])
  apply (case_tac state; clarsimp simp: receiveBlocked_def)
         apply (clarsimp simp: blockedCancelIPC_def)
         apply wpsimp
        apply (wpsimp wp: hoare_pre_cont,
               clarsimp simp: st_tcb_at'_def obj_at'_def receiveBlocked_def)+
  done

lemmas cancelIPC_receiveBlocked_tcbSchedNexts_of =
  cancelIPC_receiveBlocked_not_sched_linked[simplified, THEN hoare_conjD1[simplified pred_conj_def]]

lemmas cancelIPC_receiveBlocked_tcbSchedPrevs_of =
  cancelIPC_receiveBlocked_not_sched_linked[simplified, THEN hoare_conjD2[simplified pred_conj_def]]

crunch tcbNTFNDequeue
  for tcbStates_of'[wp]: "\<lambda>s. P (tcbStates_of' s)"
  and gsUntypedZeroRanges[wp]: "\<lambda>s. P (gsUntypedZeroRanges s)"
  (wp: crunch_wps)

lemma tcbNTFNDequeue_invs'[wp]:
  "tcbNTFNDequeue t ntfnPtr \<lbrace>invs'\<rbrace>"
  apply (simp add: invs'_def valid_pspace'_def valid_dom_schedule'_def)
  apply (wpsimp wp: valid_irq_node_lift)
  done

lemma sendSignal_corres:
  "corres dc
     (einvs and ntfn_at ntfn_ptr and current_time_bounded) invs'
     (send_signal ntfn_ptr bg) (sendSignal ntfn_ptr bg)"
  apply add_sym_refs
  apply add_valid_idle'
  apply (rule_tac Q'="ntfn_at' ntfn_ptr" in corres_cross_add_guard)
   apply (fastforce intro!: ntfn_at_cross)
  apply (simp add: send_signal_def sendSignal_def Let_def)
  apply (rule corres_stateAssert_assume[rotated], simp)
  apply (rule corres_split_forwards'[OF _ get_simple_ko_sp get_ntfn_sp'])
   apply (corres corres: getNotification_corres)
    apply fastforce
   apply fastforce
  apply (rename_tac ntfn nTFN)
  apply (rule_tac Q="valid_ntfn ntfn" in corres_cross_add_abs_guard)
   apply (fastforce dest: invs_valid_objs simp: valid_obj_def obj_at_def)
  apply (rule_tac Q'="valid_ntfn' nTFN" in corres_cross_add_guard)
   apply (fastforce elim!: ntfn_ko_at_valid_objs_valid_ntfn')
  apply (case_tac "ntfn_obj ntfn"; clarsimp)
    \<comment> \<open>IdleNtfn\<close>
    apply (clarsimp simp: ntfn_relation_def)
    apply (case_tac "ntfnBoundTCB nTFN"; clarsimp)
     \<comment> \<open>IdleNtfn and no bound TCB\<close>
     apply (corres corres: ntfnSetActive_corres)
      apply (fastforce simp: obj_at_def)
     apply fastforce
    \<comment> \<open>IdleNtfn with a bound TCB\<close>
    apply (rename_tac t)
    apply (rule corres_guard_imp)
      apply (rule corres_split[OF getThreadState_corres])
        apply (rule corres_if)
          apply (fastforce simp: receive_blocked_def receiveBlocked_def thread_state_relation_def
                          split: Structures_A.thread_state.splits thread_state.splits)
         apply (rule corres_split[OF cancel_ipc_corres])
           apply (rule corres_split[OF setThreadState_corres], simp)
             apply (simp add: badgeRegister_def badge_register_def)
             apply (rule corres_split[OF asUser_setRegister_corres])
               apply (rule corres_split[OF maybeDonateSc_corres])
                 apply (rule corres_split[OF getSchedulable_corres])
                   apply (rule corres_split[OF corres_when], simp)
                      apply (rule possibleSwitchTo_corres; (solves simp)?)
                     apply (rule corres_split_eqr[OF get_tcb_obj_ref_corres])
                        apply (clarsimp simp: tcb_relation_def)
                       apply (rule ifCondRefillUnblockCheck_corres)
                      apply (wpsimp wp: get_tcb_obj_ref_wp)
                     apply (wpsimp wp: threadGet_wp)
                    apply (rule_tac Q'="\<lambda>_. tcb_at t and active_scs_valid and pspace_aligned
                                            and pspace_distinct and valid_objs"
                                 in hoare_strengthen_post[rotated])
                     apply (clarsimp, frule (1) valid_objs_ko_at)
                     apply (fastforce simp: valid_obj_def valid_tcb_def valid_bound_obj_def
                                            obj_at_def is_sc_obj opt_map_def opt_pred_def
                                     split: option.split)
                    apply wpsimp
                   apply (rule_tac Q'="\<lambda>_. valid_objs' and pspace_bounded'" in hoare_post_imp)
                    apply (clarsimp simp: obj_at'_def split: option.split)
                   apply wpsimp
                  apply wpsimp
                 apply (wpsimp wp: getSchedulable_wp)
                apply (rule_tac Q'="\<lambda>_. valid_objs and pspace_aligned and pspace_distinct and tcb_at t
                                        and valid_sched_action and active_scs_valid
                                        and in_correct_ready_q and ready_qs_distinct
                                        and ready_queues_runnable
                                        and ready_or_release
                                        and ep_queues_blocked and ntfn_queues_blocked"
                             in hoare_post_imp)
                 apply (fastforce simp: schedulable_def2)
                apply ((wpsimp wp: hoare_drop_imps maybe_donate_sc_valid_sched_action
                                   maybe_donate_sc_valid_ready_qs abs_typ_at_lifts
                        | strengthen valid_objs_valid_tcbs valid_ready_qs_ready_queues_runnable)+)[1]
               apply(wpsimp wp: hoare_drop_imp | strengthen valid_objs'_valid_tcbs')+
            apply (strengthen valid_sched_action_weak_valid_sched_action)
            apply ((wpsimp wp: sts_cancel_ipc_Running_invs set_thread_state_valid_sched_action
                               set_thread_state_valid_ready_qs
                               set_thread_state_valid_release_q
                    | strengthen sym_refs_ep_queues_blocked sym_refs_ntfn_queues_blocked)+)[1]
           apply ((wpsimp wp: sts_invs' | strengthen invs'_implies)+)[1]
          apply (rename_tac ntfn ntfn' tptr st st')
          apply (rule_tac Q'="\<lambda>_. invs and tcb_at tptr and ntfn_at ntfn_ptr
                                  and st_tcb_at
                                        ((=) Structures_A.thread_state.Running
                                         or (=) Structures_A.thread_state.Inactive
                                         or (=) Structures_A.thread_state.Restart
                                         or (=) Structures_A.thread_state.IdleThreadState) tptr
                                  and ex_nonz_cap_to tptr and fault_tcb_at ((=) None) tptr
                                  and valid_sched and scheduler_act_not tptr and active_scs_valid
                                  and current_time_bounded"
                       in hoare_strengthen_post[rotated])
           apply (clarsimp simp: invs_def valid_state_def valid_pspace_def valid_sched_def
                                 pred_disj_def)
           apply (rule conjI, fastforce)
           apply (prop_tac "tcb_non_st_state_refs_of s tptr = state_refs_of s tptr")
            apply (drule (1) sym_refs_st_tcb_atD)
            apply clarsimp
            apply (prop_tac "tcb_st_refs_of ts = {}")
             apply (fastforce simp: tcb_st_refs_of_def)
            apply simp
            subgoal by (clarsimp simp: get_refs_def2 split: option.splits; fastforce?)
           apply (fold fun_upd_def, fastforce)
          apply (wpsimp wp: cancel_ipc_simple_except_awaiting_reply cancel_ipc_ex_nonz_cap_to_tcb)
         apply (clarsimp cong: conj_cong simp: pred_conj_def pred_tcb_at'_eq_commute)
         apply (rule_tac Q'="\<lambda>_ s. invs' s \<and> st_tcb_at' simple' t s \<and> \<not> is_sched_linked t s"
                      in hoare_strengthen_post[rotated])
          apply (fastforce simp: invs'_def valid_pspace'_def pred_tcb_at'_def obj_at'_def)
         apply (wpsimp wp: cancelIPC_invs' cancelIPC_receiveBlocked_not_sched_linked)
        apply (rule ntfnSetActive_corres, clarsimp simp: ntfn_relation_def)
       apply (wpsimp wp: gts_wp gts_wp')+
     apply (frule invs_psp_aligned, frule invs_distinct)
     apply (clarsimp simp: valid_ntfn_def receive_blocked_equiv is_blocked_on_receive_def)
     apply (rule conjI, intro impI)
      apply (frule (1) valid_sched_scheduler_act_not)
       apply (frule st_tcb_ex_cap; clarsimp)
      apply (clarsimp simp: invs_def valid_sched_def valid_state_def valid_pspace_def)
      subgoal by (force dest!: st_tcb_ex_cap)
     apply (clarsimp simp: obj_at_def)
    apply (fastforce simp: pred_tcb_at'_def obj_at'_def ko_wp_at'_def receiveBlocked_equiv
                           is_BlockedOnReceive_def)
   \<comment> \<open>WaitingNtfn\<close>
   apply (clarsimp simp: ntfn_relation_def Let_def update_waiting_ntfn_def)
   apply (rename_tac list)
   apply (rule corres_assert_assume_l_forward)
    apply (clarsimp simp: valid_ntfn_def)
   apply (rule_tac Q'="\<lambda>s'. list_queue_relation
                              list (ntfnQueue nTFN) (tcbSchedNexts_of s') (tcbSchedPrevs_of s')"
                in corres_cross_add_guard)
   apply (frule state_relation_ntfn_queues_relation)
   apply (frule_tac s=s and s'=s' in ntfn_queues_relationD[rotated 2])
      apply (fastforce simp: obj_at_def opt_map_def obj_at'_def split: option.splits)
     apply (fastforce simp: obj_at_def opt_map_def obj_at'_def split: option.splits)
    apply fastforce
   apply (rule corres_assert_gen_asm_cross_forwards)
    apply (fastforce dest: list_queue_relation_Nil)
   apply (clarsimp simp: tcbQueueEmpty_def)
   apply (rename_tac head)
   apply (rule_tac F="hd list = head" in corres_req)
    apply (fastforce dest!: heap_path_head simp: list_queue_relation_def)
   apply clarsimp
   apply (rule_tac Q="st_tcb_at
                        (\<lambda>st. st = Structures_A.thread_state.BlockedOnNotification ntfn_ptr)
                        (hd list)"
                in corres_cross_add_abs_guard)
    apply (fastforce dest: st_in_waitingntfn simp: obj_at_def)
   apply (rule corres_symb_exec_r_conj_ex_abs_forwards[OF _ gts_sp', rotated]; (solves wpsimp)?)
    apply wpsimp
    apply (fastforce intro: tcb_at_cross simp: ex_abs_def)
   apply (rule corres_assert_gen_asm_cross_forwards)
    apply (fastforce dest!: st_tcb_at_coerce_concrete
                      simp: thread_state_relation_def st_tcb_at'_def obj_at'_def isNtfn_def)
   apply (rule stronger_corres_guard_imp)
     apply (rule corres_split[OF tcbNTFNDequeue_corres], simp, simp)
        apply (clarsimp simp: ntfn_relation_def split: list.splits)
       apply (rule corres_split[OF setThreadState_corres], simp)
         apply (simp add: badgeRegister_def badge_register_def)
         apply (rule corres_split[OF asUser_setRegister_corres])
           apply (rule corres_split[OF maybeDonateSc_corres])
             apply (rule corres_split[OF getSchedulable_corres])
               apply (rule corres_split[OF corres_when], simp)
                  apply (rule possibleSwitchTo_corres; (solves simp)?)
                 apply (rule corres_split_eqr[OF get_tcb_obj_ref_corres])
                    apply (clarsimp simp: tcb_relation_def)
                   apply (rule ifCondRefillUnblockCheck_corres[simplified dc_def])
                  apply (wpsimp wp: get_tcb_obj_ref_wp)
                 apply (wpsimp wp: threadGet_wp)
                apply (rule_tac Q'="\<lambda>_. tcb_at (hd list) and active_scs_valid and pspace_aligned
                                        and pspace_distinct and valid_objs"
                             in hoare_post_imp)
                 apply (clarsimp, frule (1) valid_objs_ko_at)
                 apply (fastforce simp: valid_tcb_def obj_at_def is_sc_obj opt_map_def opt_pred_def
                                        valid_obj_def
                                 split: option.split)
                apply wpsimp
               apply (rule_tac Q'="\<lambda>_. valid_objs' and pspace_bounded'" in hoare_post_imp)
                apply (clarsimp simp: obj_at'_def split: option.split)
               apply wpsimp
              apply wpsimp
             apply (wpsimp wp: getSchedulable_wp)
            apply (rule_tac Q'="\<lambda>_. valid_objs and pspace_aligned and pspace_distinct
                                    and tcb_at (hd list) and valid_sched_action and active_scs_valid
                                    and in_correct_ready_q and ready_qs_distinct and ready_or_release
                                    and ep_queues_blocked and ntfn_queues_blocked and valid_ready_qs"
                         in hoare_post_imp)
             apply (fastforce simp: schedulable_def2)
            apply ((wpsimp wp: hoare_drop_imp maybe_donate_sc_valid_sched_action
                               maybe_donate_sc_valid_ready_qs abs_typ_at_lifts
                    | strengthen valid_objs_valid_tcbs)+)[1]
           apply(wpsimp wp: hoare_drop_imp | strengthen valid_objs'_valid_tcbs')+
        apply (strengthen valid_sched_action_weak_valid_sched_action)
        apply ((wpsimp simp: invs_def valid_state_def valid_pspace_def
                         wp: sts_valid_replies sts_only_idle sts_fault_tcbs_valid_states
                             set_thread_state_valid_sched_action
                             set_thread_state_valid_ready_qs set_thread_state_valid_release_q
                | strengthen sym_refs_ep_queues_blocked sym_refs_ntfn_queues_blocked)+)[1]
       apply ((wpsimp wp: sts_invs' | strengthen invs'_implies)+)[1]
      apply (clarsimp simp: tcb_ntfn_dequeue_def
                      cong: conj_cong,
             wpsimp wp: get_simple_ko_wp)
     apply (clarsimp cong: conj_cong)
     apply ((wpsimp wp: tcbNTFNDequeue_not_sched_linked[simplified] hoare_vcg_all_lift
                        hoare_vcg_imp_lift hoare_vcg_disj_lift
             | strengthen valid_objs'_valid_tcbs')+)[1]
    apply (clarsimp cong: conj_cong)
    apply (prop_tac "hd list \<noteq> ntfn_ptr")
     apply (fastforce dest: hd_in_set simp: valid_ntfn_def obj_at_def is_tcb_def)
    apply (clarsimp simp: valid_sched_def cong: conj_cong)
    apply (frule invs_sym_refs)
    apply (frule sym_refs_ep_queues_blocked)
    apply (frule sym_refs_ntfn_queues_blocked)
    apply clarsimp
    apply (intro conjI impI allI; fastforce?)
       apply (clarsimp simp: in_ntfn_queue_at_def obj_at_def opt_map_def)
      apply (clarsimp simp: valid_ntfn_def obj_at_def
                     split: list.splits)
      apply (prop_tac "set (filter ((\<noteq>) (hd list)) list) \<subseteq> set list")
       apply (rule filter_is_subset)
      apply (frule_tac P="(\<noteq>) (hd list)" in distinct_filter)
      subgoal by (auto simp: removeAll_filter_not_eq split: option.splits)
     apply (clarsimp simp: removeAll_filter_not_eq pred_tcb_at_def obj_at_def)
     apply (prop_tac "filter ((\<noteq>) (hd list)) list = tl list")
      apply (fastforce intro: filter_hd_equals_tl simp: valid_ntfn_def)
     apply (erule delta_sym_refs_remove_only[where tp=TCBSignal], clarsimp)
      apply (rule subset_antisym, clarsimp)
      apply (clarsimp simp: state_refs_of_def is_tcb get_refs_def tcb_st_refs_of_def pred_tcb_at_def
                            obj_at_def)
      apply (force split: option.splits)
     apply (rule subset_antisym)
      apply (clarsimp simp: subset_remove ntfn_q_refs_of_def get_refs_def)
      apply (clarsimp split: option.splits)
      apply (case_tac list)
       apply fastforce
      apply (force simp: state_refs_of_def split: list.splits)
     apply (clarsimp split: list.splits)
     apply (case_tac list; fastforce simp: state_refs_of_def)
    apply (rule valid_sched_scheduler_act_not_better)
     subgoal by (clarsimp simp: valid_sched_def)
    apply (clarsimp simp: st_tcb_at_def obj_at_def valid_ntfn_def)
   apply clarsimp
   apply (frule invs_psp_aligned)
   apply (frule invs_distinct)
   apply (frule (3) st_tcb_at_coerce_concrete)
   apply (clarsimp cong: conj_cong)
   apply (intro conjI impI allI; clarsimp?)
    apply (clarsimp simp: pred_tcb_at'_def obj_at'_def)
   apply (clarsimp simp: pred_tcb_at'_def obj_at'_def)
  apply (clarsimp simp: ntfn_relation_def updateNotification_def)
  apply (rule corres_symb_exec_r[OF _ get_ntfn_sp']; (solves wpsimp)?)
  apply (rename_tac nTFN', rule_tac F="nTFN' = nTFN" in corres_req, normalise_obj_at')
  apply (corres corres: setNotification_no_queue_update_corres)
    apply (clarsimp simp: ntfn_relation_def combine_ntfn_badges_def)
   apply (fastforce simp: obj_at_def)
  apply (fastforce simp: obj_at'_def)
  done

lemma replyRemoveTCB_irqs_masked'[wp]:
  "replyRemoveTCB t \<lbrace> irqs_masked' \<rbrace>"
  unfolding replyRemoveTCB_def
  by (wpsimp wp: hoare_drop_imps gts_wp'|rule conjI)+

crunch sendSignal, refillUnblockCheck
  for ct'[wp]: "\<lambda>s. P (ksCurThread s)"
  and it'[wp]: "\<lambda>s. P (ksIdleThread s)"
  and irqs_masked'[wp]: "irqs_masked'"
  (wp: crunch_wps simp: crunch_simps o_def)

crunch setBoundNotification
  for irqs_masked'[wp]: "irqs_masked'"
  (wp: irqs_masked_lift)

lemma ct_in_state_activatable_imp_simple'[simp]:
  "ct_in_state' activatable' s \<Longrightarrow> ct_in_state' simple' s"
  apply (simp add: ct_in_state'_def)
  apply (erule pred_tcb'_weakenE)
  apply (case_tac st; simp)
  done

lemma setThreadState_nonqueued_state_update:
  "\<lbrace>\<lambda>s. invs' s \<and> st_tcb_at' simple' t s\<rbrace>
   setThreadState st t
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: invs'_def valid_dom_schedule'_def)
  apply (rule hoare_pre, wp valid_irq_node_lift setThreadState_not_queued_valid_sched_pointers')
  apply (clarsimp simp: valid_pspace'_def)
  apply (clarsimp simp: pred_tcb_at' pred_tcb_at'_eq_commute)
  apply (intro conjI impI allI)
   subgoal by (fastforce simp: list_refs_of_replies'_def o_def pred_tcb_at'_def obj_at'_def)
  apply (erule pred_tcb'_weakenE)
  apply (rename_tac state, case_tac state; clarsimp)
  done

crunch possibleSwitchTo, asUser, doIPCTransfer
  for vms'[wp]: "valid_machine_state'"
  (wp: crunch_wps simp: zipWithM_x_mapM_x)

crunch activateIdleThread, isFinalCapability
  for nosch[wp]:  "\<lambda>s. P (ksSchedulerAction s)"
  (ignore: setNextPC simp: Let_def)

crunch asUser, setMRs, doIPCTransfer, possibleSwitchTo
  for pspace_domain_valid[wp]: "pspace_domain_valid"
  (wp: crunch_wps simp: zipWithM_x_mapM_x)

crunch doIPCTransfer, possibleSwitchTo
  for ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"
  (wp: crunch_wps simp: zipWithM_x_mapM)

crunch doIPCTransfer
  for urz[wp]: "untyped_ranges_zero'"
  (ignore: threadSet wp: threadSet_urz crunch_wps simp: zipWithM_x_mapM)

crunch receiveIPC
  for gsUntypedZeroRanges[wp]: "\<lambda>s. P (gsUntypedZeroRanges s)"
  (wp: crunch_wps transferCapsToSlots_pres1 hoare_vcg_all_lift
   simp: crunch_simps zipWithM_x_mapM ignore: constOnFailure)

lemmas possibleSwitchToTo_cteCaps_of[wp]
    = cteCaps_of_ctes_of_lift[OF possibleSwitchTo_ctes_of]

lemma setThreadState_Running_invs':
  "\<lbrace>\<lambda>s. invs' s \<and> st_tcb_at' (Not \<circ> is_BlockedOnReply) t s \<and> \<not> is_sched_linked t s\<rbrace>
   setThreadState Running t
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (wpsimp wp: sts_invs')
  apply (simp add: invs'_def valid_dom_schedule'_def pred_tcb_at'_eq_commute)
  apply (fastforce dest: global'_no_ex_cap
                   simp: o_def pred_tcb_at'_def obj_at'_def)
  done

lemma setThreadState_BlockedOnReceive_invs':
  "\<lbrace>\<lambda>s. invs' s
        \<and> st_tcb_at' (Not \<circ> is_BlockedOnReply) t s \<and> st_tcb_at' (not inIPCQueueThreadState) t s\<rbrace>
   setThreadState (BlockedOnReceive eptr cg rptr) t
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: invs'_def valid_dom_schedule'_def)
  apply (wpsimp wp: setThreadState_not_queued_valid_sched_pointers' valid_irq_node_lift
              simp: pred_tcb_at'_eq_commute)
  apply (fastforce dest: global'_no_ex_cap
                   simp: comp_def pred_tcb_at'_def obj_at'_def)
  done

lemma tcbReleaseEnqueue_valid_mdb'[wp]:
  "tcbReleaseEnqueue tcbPtr \<lbrace>valid_mdb'\<rbrace>"
  unfolding tcbReleaseEnqueue_def
  by (wpsimp wp: getTCB_wp)

crunch tcbReleaseEnqueue
  for valid_bitmaps[wp]: valid_bitmaps
  (wp: crunch_wps)

lemma tcbReleaseEnqueue_invs'[wp]:
  "tcbReleaseEnqueue tcbPtr \<lbrace>invs'\<rbrace>"
  apply (simp add: invs'_def valid_pspace'_def)
  apply (wpsimp wp: valid_irq_node_lift  untyped_ranges_zero_lift valid_replies'_lift
              simp: cteCaps_of_def o_def)
  done

crunch postpone, schedContextResume
  for invs'[wp]: invs'
  (wp: crunch_wps simp: crunch_simps)

lemma maybeDonateSc_invs'[wp]:
  "maybeDonateSc tptr nptr \<lbrace>invs'\<rbrace>"
  unfolding maybeDonateSc_def
  by (wpsimp wp: schedContextDonate_invs' getNotification_wp threadGet_wp)

lemma simple'_not_is_BlockedOnReply:
  "simple' st \<Longrightarrow> \<not> is_BlockedOnReply st"
  by (clarsimp simp: is_BlockedOnReply_def)

lemma ntfnSetActive_invs':
  "\<lbrace>invs' and obj_at' (\<lambda>ntfn. ntfnState ntfn = IdleNtfnState) ntfnptr\<rbrace>
   ntfnSetActive ntfnptr badge
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (clarsimp simp: ntfnSetActive_def updateNotification_def)
  apply (wpsimp wp: setNotification_invs' getNotification_wp hoare_vcg_all_lift)
  apply (frule (1) ntfn_ko_at_valid_objs_valid_ntfn'[OF _ invs_valid_objs'])
  apply (clarsimp simp: valid_ntfn'_def)
  done

lemma sai_invs'[wp]:
  "sendSignal ntfnptr badge \<lbrace>invs'\<rbrace>"
  apply (simp add: sendSignal_def)
  apply (rule bind_wp[OF _ stateAssert_sp])
  apply (rule bind_wp[OF _ get_ntfn_sp'])
  apply (rule_tac P'="invs' and ko_at' nTFN ntfnptr and valid_ntfn' nTFN and sym_refs_asrt
                      and (\<lambda>s. sym_refs (state_refs_of' s))" in hoare_weaken_pre)
   apply (case_tac "ntfnState nTFN"; clarsimp)
     \<comment> \<open>IdleNtfn\<close>
     apply (case_tac "ntfnBoundTCB nTFN"; clarsimp)
      apply (wpsimp wp: ntfnSetActive_invs')
      apply (clarsimp simp: obj_at'_def)
     apply (wp getSchedulable_wp)
           apply (rule_tac Q'="\<lambda>_. invs'" in hoare_strengthen_post[rotated])
            apply (clarsimp simp: schedulable'_def)
           apply (wpsimp wp: setThreadState_Running_invs'
                             setNotification_invs' getNotification_wp gts_wp' cancelIPC_simple
                             ntfnSetActive_invs'
                             cancelIPC_receiveBlocked_tcbSchedNexts_of
                             cancelIPC_receiveBlocked_tcbSchedPrevs_of
                       simp: o_def
                  | strengthen pred_tcb'_weakenE[mk_strg I _ O],
                    rule simple'_not_is_BlockedOnReply, assumption)+
     apply (clarsimp simp: valid_ntfn'_def st_tcb_at'_def obj_at'_def cong: conj_cong)
    \<comment> \<open>ActiveNtfn\<close>
    apply (wpsimp wp: setNotification_invs' getNotification_wp
                simp: updateNotification_def valid_ntfn'_def)
    apply (clarsimp simp: valid_ntfn'_def st_tcb_at'_def obj_at'_def)
   \<comment> \<open>WaitingNtfn\<close>
   apply (rename_tac list)
   apply (case_tac list; clarsimp)
   apply (wp getSchedulable_wp)
           apply (rule_tac Q'="\<lambda>_. invs'" in hoare_strengthen_post[rotated])
            apply (clarsimp simp: schedulable'_def)
           apply (wp setThreadState_Running_invs' setNotification_invs' gts_wp')+
   apply (fastforce simp: ko_wp_at'_def st_tcb_at'_def obj_at'_def isNtfn_def
                   split: thread_state.splits)
  apply (fastforce dest: ntfn_ko_at_valid_objs_valid_ntfn')
  done

lemma replyFromKernel_corres:
  "corres dc (tcb_at t and invs) invs' (reply_from_kernel t r) (replyFromKernel t r)"
  apply (case_tac r)
  apply (clarsimp simp: replyFromKernel_def reply_from_kernel_def
                        badge_register_def badgeRegister_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqr[OF lookupIPCBuffer_corres])
      apply (rule corres_split[OF asUser_setRegister_corres])
        apply (rule corres_split_eqr[OF setMRs_corres], simp)
          apply (rule setMessageInfo_corres)
          apply (wp hoare_case_option_wp hoare_valid_ipc_buffer_ptr_typ_at'
                 | fastforce)+
  done

crunch maybe_donate_sc
  for ntfn_at[wp]: "ntfn_at ntfnp"
  and ntfns_of[wp]: "\<lambda>s. P (ntfns_of s)"
  (simp: crunch_simps wp: crunch_wps set_object_wp ignore: set_tcb_obj_ref)

crunch maybeDonateSc
  for ntfn_at'[wp]: "ntfn_at' ntfnp"
  and tcb_at'[wp]: "\<lambda>s. P (tcb_at' tp s)"
  (simp: crunch_simps wp: crunch_wps)

crunch asUser
  for obj_at'_notification[wp]: "\<lambda>s. Q (obj_at' (P :: notification \<Rightarrow> bool) p s)"
  (wp: crunch_wps threadSet_obj_at'_ntfn)

lemma completeSignal_corres:
  "corres dc
      (ntfn_at ntfnptr and tcb_at tcbptr and valid_objs and pspace_aligned and pspace_distinct
       and (\<lambda>s. sym_refs (state_refs_of s)) and (\<lambda>s. (Ipc_A.isActive |< ntfns_of s) ntfnptr)
       and valid_sched and current_time_bounded)
      invs'
      (complete_signal ntfnptr tcbptr) (completeSignal ntfnptr tcbptr)"
  supply opt_mapE[elim!]
  apply add_sym_refs
  apply (rule_tac Q'="tcb_at' tcbptr" in corres_cross_add_guard)
   apply (fastforce intro!: tcb_at_cross)
  apply (simp add: complete_signal_def completeSignal_def)
  apply (rule corres_split_forwards'[OF _ get_simple_ko_sp get_ntfn_sp'])
   apply (corres corres: getNotification_corres)
  apply (rename_tac ntfn ntfn')
  apply (case_tac "ntfn_obj ntfn"; clarsimp simp: ntfn_relation_def)
    apply (corres corres: corres_underlying_fail_fail)
     apply (clarsimp simp: opt_pred_def isActive_def  obj_at_def split: option.splits ntfn.splits)
    apply fastforce
   apply (corres corres: corres_underlying_fail_fail)
    apply (clarsimp simp: opt_pred_def isActive_def  obj_at_def split: option.splits ntfn.splits)
   apply fastforce
  apply (rule stronger_corres_guard_imp)
    apply (simp add: badgeRegister_def badge_register_def)
    apply (rule corres_split[OF asUser_setRegister_corres])
      apply (clarsimp simp: updateNotification_def bind_assoc)
      apply (rule corres_symb_exec_r'[where Q'="ntfn_at' ntfnptr"])
         apply (rename_tac ntfn'')
         apply (rule_tac F="ntfn'' = ntfn'" in corres_gen_asm2)
         apply (rule corres_split[OF setNotification_no_queue_update_corres], simp)
            apply (clarsimp simp: ntfn_relation_def)
           apply (rule corres_split[OF maybeDonateSc_corres])
             apply (rule corres_split_eqr[OF get_tcb_obj_ref_corres])
                apply (clarsimp simp: tcb_relation_def)
               apply (rename_tac sc_opt)
               apply (rule_tac P="bound_sc_tcb_at ((=) sc_opt) tcbptr and ntfn_at ntfnptr and valid_objs
                                  and pspace_aligned and pspace_distinct
                                  and active_scs_valid"
                           and P'="bound_sc_tcb_at' ((=) sc_opt) tcbptr and ntfn_at' ntfnptr and valid_objs'
                                   and pspace_aligned' and pspace_distinct' and pspace_bounded'"
                            in corres_inst)
               apply (rename_tac sc_opt; case_tac sc_opt;
                      simp add: maybeM_def liftM_def get_sk_obj_ref_def)
               apply (rule corres_guard_imp)
                 apply (rule corres_split[OF get_sc_corres])
                   apply (rename_tac scp sc sc')
                   apply (rule_tac P="sc_at scp and (\<lambda>s. scs_of2 s scp = Some sc) and ntfn_at ntfnptr
                                      and valid_objs and active_scs_valid
                                      and pspace_aligned and pspace_distinct"
                               and P'="ko_at' sc' scp and ntfn_at' ntfnptr and valid_objs'
                                       and pspace_aligned' and pspace_distinct' and pspace_bounded'"
                                in corres_inst)
                   apply (rule stronger_corres_guard_imp)
                    apply (fold dc_def)
                     apply (rule corres_when2)
                      apply (clarsimp simp: sc_relation_def active_sc_def)
                     apply (rule corres_split[OF getNotification_corres])
                       apply (rule corres_split[OF getCurSc_corres])
                         apply (rule corres_when2)
                          apply (clarsimp simp: ntfn_relation_def)
                         apply (rule refillUnblockCheck_corres)
                        apply wpsimp
                       apply wpsimp
                      apply (wpsimp wp: get_simple_ko_wp)
                     apply (wpsimp wp: getNotification_wp)
                    apply (clarsimp simp: conj_commute)
                    apply (rule context_conjI)
                     apply (frule_tac sc_ptr=scp in sporadic_implies_active)
                      apply (clarsimp simp: projection_rewrites opt_pred_def opt_map_def)
                     apply (clarsimp simp: opt_pred_def opt_map_def vs_all_heap_simps
                                    split: option.splits)
                    apply (fastforce dest: active_scs_validE[rotated]
                                     simp: vs_all_heap_simps opt_map_red opt_pred_def
                                           valid_refills_def rr_valid_refills_def)
                   apply (fastforce intro!: valid_objs'_valid_refills'
                                            sporadic_implies_active_cross)
                  apply wpsimp
                 apply wpsimp
                apply (clarsimp simp: pred_tcb_at_def obj_at_def valid_obj_def valid_tcb_def
                               dest!: sym[of "Some _"])
                apply (erule (1) valid_objsE[where x=tcbptr])
                apply (clarsimp simp: obj_at_def valid_obj_def valid_tcb_def is_sc_obj opt_map_red)
               apply clarsimp
              apply (clarsimp simp: obj_at'_def pred_tcb_at'_def dest!: sym[of "Some _"])
              apply (wpsimp wp: get_tcb_obj_ref_wp threadGet_wp)
             apply (wpsimp wp: get_tcb_obj_ref_wp threadGet_wp)
            apply (rule_tac Q'="\<lambda>_. tcb_at tcbptr and ntfn_at ntfnptr and valid_objs
                                    and pspace_distinct and pspace_aligned and active_scs_valid"
                         in hoare_strengthen_post[rotated])
             apply (clarsimp simp: pred_tcb_at_def obj_at_def opt_map_red)
            apply (wpsimp wp: abs_typ_at_lifts)
           apply (rule_tac Q'="\<lambda>_. tcb_at' tcbptr and ntfn_at' ntfnptr and valid_objs'
                                   and pspace_aligned' and pspace_distinct' and pspace_bounded'"
                        in hoare_strengthen_post[rotated])
            apply (clarsimp simp: pred_tcb_at'_def obj_at'_def)
           apply (wpsimp wp: getNotification_wp)+
     apply (wpsimp wp: as_user.tcb_agnostic_obj_at
                 simp: tcb_agnostic_pred_def is_tcb_def is_ntfn_def)
    apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift')
   apply (clarsimp simp: valid_sched_def valid_sched_action_def invs_def)
   apply (drule (1) valid_objs_ko_at)
   apply (clarsimp simp: valid_obj_def valid_ntfn_def fun_upd_def[symmetric]
                         state_refs_of_def obj_at_def fun_upd_idem)
  apply (clarsimp simp: valid_pspace'_def invs'_def)
  apply (frule (1) ntfn_ko_at_valid_objs_valid_ntfn')
  apply (clarsimp simp: obj_at'_def valid_ntfn'_def)
  done

lemma ntfn_relation_par_inj:
  "ntfn_relation ntfn ntfn' \<Longrightarrow> ntfn_sc ntfn = ntfnSc ntfn'"
  by (simp add: ntfn_relation_def)

lemma thread_set_weak_valid_sched_action2:
  "\<lbrace>weak_valid_sched_action and scheduler_act_not tptr\<rbrace> thread_set f tptr \<lbrace>\<lambda>rv. weak_valid_sched_action\<rbrace>"
  apply (wpsimp wp: thread_set_wp simp: obj_at_kh_kheap_simps vs_all_heap_simps fun_upd_def
                    weak_valid_sched_action_def)
  apply (clarsimp simp: weak_valid_sched_action_def scheduler_act_not_def)
  apply (rule_tac x=ref' in exI; clarsimp)
  done

lemma valid_tcb'_SchedContext_update_empty[elim!]:
  "valid_tcb' tcb s' \<Longrightarrow> valid_tcb' (tcbSchedContext_update Map.empty tcb) s'"
  by (auto simp: valid_tcb'_def valid_cap'_def tcb_cte_cases_def cteSizeBits_def)

lemma maybeReturnSc_corres:
  "corres dc
   (ntfn_at ntfnPtr and tcb_at thread and valid_tcbs and pspace_aligned
      and scheduler_act_not thread and active_scs_valid
      and pspace_distinct and weak_valid_sched_action
      and not_queued thread and not_in_release_q thread
      and in_correct_ready_q and ready_qs_distinct and ready_queues_runnable and ready_or_release
      and (\<lambda>s. sym_refs (state_refs_of s)))
   (valid_tcbs' and sym_heap_sched_pointers and valid_sched_pointers
    and pspace_aligned' and pspace_distinct' and pspace_bounded')
   (maybe_return_sc ntfnPtr thread)
   (maybeReturnSc ntfnPtr thread)"
  unfolding maybe_return_sc_def maybeReturnSc_def
  apply add_sym_refs
  apply (rule corres_stateAssert_assume)
   apply (clarsimp simp: liftM_def get_sk_obj_ref_def get_tcb_obj_ref_def
                         set_tcb_obj_ref_thread_set)
   apply (rule stronger_corres_guard_imp)
     apply (rule corres_split[OF getNotification_corres])
       apply (frule ntfn_relation_par_inj[symmetric], simp)
       apply (rule corres_split[OF threadGet_corres[where r="(=)"]])
          apply (clarsimp simp: tcb_relation_def)
         apply (rule corres_when2, simp)
         apply (rule corres_assert_opt_assume_l)
         apply (rule corres_split[OF threadset_corresT]; (simp add: inQ_def)?)
              apply (clarsimp simp: tcb_relation_def)
             apply (rule ball_tcb_cap_casesI; simp)
            apply (clarsimp simp: tcb_cte_cases_def cteSizeBits_def)
              apply (rule corres_split)
                 apply (rule updateSchedContext_no_stack_update_corres)
                    apply ((clarsimp simp: sc_relation_def refillSize_def objBits_def
                                           objBitsKO_def)+)[4]
                apply (rule corres_split[OF getCurThread_corres])
                  apply (rule corres_when [OF _ rescheduleRequired_corres], simp)
                 apply (wpsimp wp: hoare_vcg_imp_lift')+
          apply (wpsimp wp: thread_set_in_correct_ready_q thread_set_weak_valid_sched_action2
                            thread_set_ep_queues_blocked thread_set_ntfn_queues_blocked
                            thread_set_ready_queues_runnable)
         apply (wpsimp wp: hoare_drop_imp threadSet_valid_tcbs' threadSet_sched_pointers
                           threadSet_valid_sched_pointers)
        apply (wpsimp wp: thread_get_wp)
       apply (rename_tac sc sc')
       apply (case_tac sc', clarsimp)
       apply (wpsimp wp: threadGet_wp)
      apply (wpsimp wp: get_simple_ko_wp getNotification_wp)+
    apply (rule valid_tcbs_valid_tcbE, simp, simp)
    apply (fastforce simp: valid_tcb_def valid_bound_obj_def split: option.splits)
   apply (rule cross_rel_srE [OF ntfn_at'_cross_rel [where t=ntfnPtr]], simp)
   apply clarsimp
  apply (fastforce dest: ko_at'_valid_tcbs'_valid_tcb'
                   simp: valid_tcb'_def valid_bound_obj'_def split: option.splits)
  done

lemma doNBRecvFailedTransfer_corres:
  "corres dc (pspace_aligned and pspace_distinct and tcb_at thread) \<top>
             (do_nbrecv_failed_transfer thread) (doNBRecvFailedTransfer thread)"
  apply (rule corres_cross[where Q' = "tcb_at' thread", OF tcb_at'_cross_rel], simp)
  apply (clarsimp simp: do_nbrecv_failed_transfer_def doNBRecvFailedTransfer_def)
  apply (rule corres_guard_imp)
    apply (clarsimp simp: badge_register_def badgeRegister_def)
    apply (rule asUser_setRegister_corres)
   apply clarsimp+
  done

crunch maybe_return_sc
  for tcb_at[wp]: "tcb_at thread"
  (wp: crunch_wps simp: crunch_simps)

lemma maybeReturnSc_valid_objs'[wp]:
  "maybeReturnSc ntfnPtr tcbPtr \<lbrace>valid_objs'\<rbrace>"
  apply (clarsimp simp: maybeReturnSc_def updateSchedContext_def)
  apply (wpsimp wp: threadSet_valid_objs' threadGet_wp getNotification_wp
                    hoare_vcg_all_lift hoare_vcg_imp_lift' hoare_vcg_disj_lift)
  apply normalise_obj_at'
  apply (frule (1) tcb_ko_at_valid_objs_valid_tcb')
  apply (fastforce dest!: sc_ko_at_valid_objs_valid_sc'
                    simp: valid_sched_context'_def valid_sched_context_size'_def objBits_simps
                          refillSize_def)
  done

lemma maybeReturnSc_valid_tcbs'[wp]:
  "maybeReturnSc ntfnPtr tcbPtr \<lbrace>valid_tcbs'\<rbrace>"
  unfolding maybeReturnSc_def
  by (wpsimp wp: threadGet_wp getNotification_wp)

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
  "maybeReturnSc nptr tptr \<lbrace>invs'\<rbrace>"
  apply (wpsimp wp: setSchedContext_invs' simp: maybeReturnSc_def updateSchedContext_def)
      apply (clarsimp simp add: invs'_def split del: if_split)
      apply (wp threadSet_valid_pspace'T threadSet_ctes_of threadSet_ifunsafe'T
                valid_irq_node_lift valid_irq_handlers_lift''
                untyped_ranges_zero_lift threadGet_wp' getNotification_wp
                threadSet_sched_pointers threadSet_valid_sched_pointers
                hoare_vcg_imp_lift' hoare_vcg_all_lift valid_dom_schedule'_lift
             | clarsimp simp: tcb_cte_cases_def cteSizeBits_def cteCaps_of_def)+
  apply (clarsimp simp: obj_at'_def)
  apply (rename_tac ntfn tcb)
  apply (rule_tac x=tcb in exI)
  apply (clarsimp simp: invs'_def inQ_def comp_def eq_commute[where a="Some _"])
  apply (intro conjI impI allI; clarsimp?)
    apply (clarsimp simp: untyped_ranges_zero_inv_def cteCaps_of_def comp_def)
   apply (fastforce simp: valid_obj'_def valid_sched_context'_def refillSize_def)
  apply (fastforce simp: valid_obj'_def valid_sched_context_size'_def objBits_def objBitsKO_def)
  done

crunch doIPCTransfer
  for no_0_obj'[wp]: no_0_obj'
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

crunch maybe_return_sc
  for ep_at[wp]: "ep_at epptr"
  (wp: crunch_wps simp: crunch_simps)

lemma thread_set_cap_to_fault_helper:
  "(a, b, c) \<in> ran tcb_cap_cases \<Longrightarrow> a (tcb_fault_update h tcb) = a tcb"
  by (clarsimp simp: tcb_cap_cases_def, fastforce)

crunch cancel_ipc
  for ep_at[wp]: "ep_at epptr"
  and reply_at[wp]: "reply_at rptr"
  and ex_nonz_cap_to[wp]: "ex_nonz_cap_to t"
  (simp: crunch_simps thread_set_cap_to_fault_helper
     wp: crunch_wps thread_set_cap_to)

crunch receive_ipc_preamble
  for ep_at[wp]: "ep_at epptr"
  and valid_list[wp]: valid_list
  and tcb_at[wp]: "tcb_at t"
  and ex_nonz_cap_to[wp]: "ex_nonz_cap_to epptr"
  and idle_thread[wp]: "\<lambda>s. P (idle_thread s)"
  and cte_wp_at[wp]: "cte_wp_at P x"
  and scheduler_act_sane[wp]: scheduler_act_sane

crunch receiveIPC_preamble
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
  shows
  "corres (=)
     (invs and valid_ready_qs and valid_release_q and ready_or_release  and valid_cap reply_cap)
     invs'
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


crunch ifCondRefillUnblockCheck
  for reply_projs[wp]: "\<lambda>s. P (replyNexts_of s) (replyPrevs_of s) (replyTCBs_of s) (replySCs_of s)"
  (wp: crunch_wps simp: crunch_simps)

crunch updateReply
  for obj_at'_endpoint[wp]: "\<lambda>s. Q (obj_at' (P :: endpoint \<Rightarrow> bool) epPtr s)"

lemma receiveIPCBlocked_corres:
  "corres dc
     (einvs and st_tcb_at runnable thread and not_queued thread and not_in_release_q thread
      and not ep_queued thread and not ntfn_queued thread
      and ep_at epptr and receive_ipc_preamble_rv reply_cap replyOpt)
     (invs' and valid_bound_reply' replyOpt
      and obj_at' (\<lambda>ep. epState ep \<noteq> IdleEPState \<longrightarrow> epState ep = ReceiveEPState) epptr)
     (receive_ipc_blocked isBlocking thread epptr replyOpt)
     (receiveIPCBlocked isBlocking thread epptr replyOpt)"
  supply if_split[split del]
  apply (rule_tac Q'="st_tcb_at' runnable' thread" in corres_cross_add_guard)
   apply (fastforce intro: st_tcb_at_runnable_cross)
  apply (rule_tac Q'="ep_at' epptr" in corres_cross_add_guard, fastforce intro!: ep_at_cross)
  apply (rule_tac Q'="\<lambda>s'. \<not> (tcbQueued |< tcbs_of' s') thread" in corres_cross_add_guard)
   apply (frule state_relation_ready_queues_relation)
   apply (frule in_ready_q_tcbQueued_eq[where t=thread])
   apply (clarsimp simp: not_queued_def in_ready_q_def)
  apply (rule_tac Q'="\<lambda>s'. \<not> (tcbInReleaseQueue |< tcbs_of' s') thread" in corres_cross_add_guard)
   apply (frule state_relation_release_queue_relation)
   apply (frule in_release_q_tcbInReleaseQueue_eq[where t=thread])
   apply (clarsimp simp: in_release_q_def)
  apply (clarsimp simp: receive_ipc_blocked_def receiveIPCBlocked_def maybeM_def bool.case_eq_if)
  apply (cases isBlocking; clarsimp)
   apply (rule corres_guard_imp)
     apply (rule corres_split[OF setThreadState_corres])
        apply (clarsimp simp: thread_state_relation_def)
       apply (rule corres_split)
          apply (clarsimp simp: when_def option.case_eq_if)
          apply (subst if_swap)
          apply (rule corres_if_strong[where R=\<top> and R'=\<top>])
            apply fastforce
           apply (rule replyTCB_update_corres)
          apply (rule corres_return_trivial)
         apply (rule tcbEPAppend_corres, simp, simp)
         apply simp
        apply (wpsimp wp: when_wp)
       apply (wpsimp wp: when_wp updateReply_valid_objs')
      apply (wpsimp wp: set_thread_state_ep_queues_blocked_not_queued
                        set_thread_state_ntfn_queues_blocked_not_queued
                        set_thread_state_ready_queues_runnable_not_queued
                        set_thread_state_release_q_runnable_not_in_release_q
                        hoare_vcg_if_lift2 hoare_vcg_imp_lift')
     apply (wpsimp wp: hoare_vcg_if_lift2 hoare_vcg_imp_lift')
      apply (rule_tac Q'="\<lambda>_ s. tcb_at' thread s \<and> \<not> is_sched_linked thread s
                                \<and> obj_at' (\<lambda>ep. epState ep \<noteq> IdleEPState
                                                \<longrightarrow> epState ep = ReceiveEPState)
                                          epptr s"
                   in hoare_post_imp)
       apply (clarsimp simp: valid_reply'_def)
      apply wpsimp
     apply (wpsimp wp: hoare_vcg_imp_lift')
    apply (clarsimp cong: conj_cong)
    apply (frule invs_sym_refs)
    apply (frule valid_sched_valid_ready_qs)
    apply (frule valid_sched_valid_release_q)
    apply (cases replyOpt; fastforce simp: reply_at_ppred_def obj_at_def is_reply_def)
   apply (fastforce dest!: runnable'_Not_tcbInReleaseQueue_not_sched_linked[rotated]
                     simp: st_tcb_at'_def obj_at'_def opt_pred_def opt_map_red)
  apply (corres corres: doNBRecvFailedTransfer_corres)
   apply fastforce
  apply fastforce
  done

crunch refill_unblock_check
  for ntfn_queued[wp]: "\<lambda>s. P (ntfn_queued tcb_ptr s)"
  and ep_queued[wp]: "\<lambda>s. P (ep_queued tcb_ptr s)"
  (wp: ntfn_queued_lift ep_queued_lift)

crunch maybeReturnSc
  for obj_at'_endpoint[wp]: "\<lambda>s. Q (obj_at' (P :: endpoint \<Rightarrow> bool) p s)"
  (wp: crunch_wps threadSet_obj_at'_ntfn)

lemma receiveIPC_corres_sym_refs_helper:
  "\<lbrakk>sym_refs (state_refs_of s); ko_at (kernel_object.Endpoint (SendEP (sender # queue))) epptr s;
    valid_ep (SendEP (sender # queue)) s;
    st_tcb_at (\<lambda>st. \<exists>data. st = Structures_A.thread_state.BlockedOnSend epptr data) sender s\<rbrakk>
   \<Longrightarrow> sym_refs
         (\<lambda>p. if p = sender then tcb_non_st_state_refs_of s sender
              else if p = epptr
                   then ep_q_refs_of
                          (case queue of
                             [] \<Rightarrow> IdleEP
                           | a # list \<Rightarrow> update_ep_queue
                                           (SendEP (sender # queue))
                                           (removeAll sender (ep_queue (SendEP (sender # queue)))) True)
                   else state_refs_of s p)"
  apply (erule delta_sym_refs)
   by (auto simp: ko_at_state_refs_ofD get_refs_def2 pred_tcb_at_def obj_at_def valid_ep_def
           split: list.splits if_splits)

lemma receiveIPC_corres:
  assumes "is_ep_cap cap" and "cap_relation cap cap'"
  assumes "cap_relation reply_cap replyCap"
  assumes "is_reply_cap reply_cap \<or> (reply_cap = cap.NullCap)"
  shows
    "corres dc
       (einvs and valid_cap cap and current_time_bounded and valid_cap reply_cap
        and st_tcb_at active thread and ex_nonz_cap_to thread
        and not_queued thread and not_in_release_q thread
        and scheduler_act_not thread and scheduler_act_sane
        and (\<lambda>s. \<forall>r\<in>zobj_refs reply_cap. ex_nonz_cap_to r s))
       (invs' and valid_cap' cap' and valid_cap' replyCap)
       (receive_ipc thread cap isBlocking reply_cap)
       (receiveIPC thread cap' isBlocking replyCap)"
     (is "corres _ (_ and _ and _ and ?rrefs) _ _ _")
  apply add_sch_act_wf
  apply add_valid_idle'
  apply add_sym_refs
  supply if_split [split del]
  apply (insert assms)
  apply (rule corres_cross_add_abs_guard[where Q="K (thread \<noteq> idle_thread_ptr)"])
   apply (clarsimp simp: invs_def valid_state_def valid_pspace_def)
   apply (frule (1) idle_no_ex_cap)
   apply (clarsimp simp: valid_idle_def)
  apply (simp add: receive_ipc_def receiveIPC_def)
  apply (case_tac cap, simp_all add: isEndpointCap_def)
  apply (rename_tac epptr badge right)
  apply (rule corres_stateAssert_assume[rotated], simp)+
  apply (rule corres_assert_gen_asm_cross_forwards)
   apply (cases reply_cap; clarsimp simp: is_reply_cap_def isCap_simps)
  apply (rule stronger_corres_guard_imp)
    apply (subst receiveIPC_corres_helper)
    apply (clarsimp simp: receive_ipc_preamble_def[symmetric] receiveIPC_preamble_def[symmetric])
    apply (rule corres_split[OF receiveIPC_preamble_corres], simp, simp)
      apply (rule corres_stateAssert_r)
      apply (rule corres_split[OF getEndpoint_corres])
        apply (rename_tac ep ep')
        apply (rule corres_split[OF getBoundNotification_corres])
          apply (rule_tac r'="ntfn_relation" in corres_split)
            apply (rule corres_option_split[OF _ corres_returnTT getNotification_corres]; clarsimp)
             apply (clarsimp simp: ntfn_relation_def default_notification_def default_ntfn_def)
            apply (rule corres_if)
              apply (clarsimp simp: ntfn_relation_def Ipc_A.isActive_def
                             split: Structures_A.ntfn.splits Structures_H.notification.splits)
             apply (simp only: )
             apply (rule completeSignal_corres)
            apply (rule corres_split[where r'=dc])
             apply (rule corres_when; simp)
               apply (rule maybeReturnSc_corres)
              apply (rule_tac P="einvs and st_tcb_at runnable thread
                                 and not_queued thread and not_in_release_q thread
                                 and not ep_queued thread and not ntfn_queued thread
                                 and ex_nonz_cap_to thread and ep_at epptr
                                 and valid_ep ep and ko_at (kernel_object.Endpoint ep) epptr
                                 and current_time_bounded
                                 and receive_ipc_preamble_rv reply_cap replyOpt and ?rrefs"
                          and P'="invs' and tcb_at' thread and ko_at' ep' epptr
                                  and valid_bound_reply' replyOpt"
                           in corres_inst)
              apply (rule_tac P'="valid_bound_obj' valid_replies'_sc_asrt replyOpt"
                           in corres_add_guard[where P=\<top>])
               apply (case_tac replyOpt; simp)
               apply (erule valid_replies_sc_cross; clarsimp elim!: reply_at_ppred_reply_at)
              apply (case_tac ep)
                \<comment> \<open>IdleEP\<close>
                apply (simp add: ep_relation_def)
                apply (fold dc_def)[1]
                apply (corres corres: receiveIPCBlocked_corres)
                 apply fastforce
                apply (clarsimp simp: obj_at'_def)
                \<comment> \<open>SendEP\<close>
               apply (simp add: ep_relation_def get_tcb_obj_ref_def)
               apply (rename_tac list)
               apply (rule_tac F="list \<noteq> []" in corres_req)
                apply (clarsimp simp: valid_ep_def)
               apply (case_tac list, simp_all)[1]
               apply (rename_tac sender queue)
               apply (rule_tac Q'="\<lambda>s'. list_queue_relation
                                          (sender # queue) (epQueue ep')
                                          (tcbSchedNexts_of s') (tcbSchedPrevs_of s')"
                            in corres_cross_add_guard)
                apply (rule_tac p=epptr and s=s in ep_queues_relationD)
                  apply (clarsimp simp: eps_of_kh_def opt_map_red obj_at_def)
                 apply (clarsimp simp: opt_map_red obj_at'_def)
                apply fastforce
               apply (rule corres_stateAssert_ignore)
                apply (rule list_queue_relation_tcb_queue_head_end_valid)
                 apply fastforce
                apply (clarsimp simp: valid_ep_def)
                apply (fastforce intro!: tcb_at_cross)
               apply (rule corres_assert_gen_asm_cross_forwards)
                apply (fastforce dest: list_queue_relation_Nil)
               apply (clarsimp simp: tcbQueueEmpty_def)
               apply (rename_tac head)
               apply (rule_tac F="head = sender" in corres_req)
                apply clarsimp
                apply (frule state_relation_ep_queues_relation)
                apply (frule_tac p=epptr and ls="sender # queue" and q="epQueue ep'"
                              in ep_queues_relationD[rotated 2])
                  apply (clarsimp simp: eps_of_kh_def obj_at_def opt_map_red)
                 apply (clarsimp simp: opt_map_def obj_at'_def split: option.splits)
                apply (clarsimp simp: list_queue_relation_def)
               apply (rule corres_guard_imp)
                 apply (rule corres_split[OF tcbEPDequeue_corres], simp, simp)
                   apply (clarsimp simp: ep_relation_def split: list.splits)
                   apply (rule corres_split[OF getThreadState_corres])
                     apply (rule_tac
                               F="\<exists>data. sender_state
                                         = Structures_A.thread_state.BlockedOnSend epptr data"
                            in corres_gen_asm)
                     apply (clarsimp simp: isSend_def case_bool_If case_option_If if3_fold
                                     cong: if_cong)
                     apply (rule corres_split[OF doIPCTransfer_corres])
                       apply (rule corres_split_eqr[OF threadGet_corres])
                        apply (clarsimp simp: tcb_relation_def)
                       apply (rule corres_split[OF ifCondRefillUnblockCheck_corres])
                           apply (rule corres_split[OF threadget_fault_corres])
                           apply (simp cong: if_cong)
                             apply (fold dc_def)[1]
                             apply (rule_tac P="valid_objs and valid_mdb and valid_list
                                                and valid_sched and valid_replies and valid_idle
                                                and cur_tcb and current_time_bounded
                                                and ep_queues_blocked and ntfn_queues_blocked
                                                and pspace_aligned and pspace_distinct
                                                and st_tcb_at is_blocked_on_send sender
                                                and tcb_at thread and not_queued sender
                                                and not ep_queued sender and not ntfn_queued sender
                                                and receive_ipc_preamble_rv reply_cap replyOpt
                                                and valid_bound_obj
                                                      (\<lambda>r s. r \<notin> fst ` replies_with_sc s) replyOpt
                                                and (\<lambda>s. sym_refs
                                                           (\<lambda>p. if p = sender
                                                                then tcb_non_st_state_refs_of s sender
                                                                else state_refs_of s p))
                                                and ?rrefs"
                                         and P'="tcb_at' sender and tcb_at' thread
                                                 and (\<lambda>s. \<not> is_sched_linked sender s)
                                                 and sym_heap_sched_pointers
                                                 and valid_sched_pointers
                                                 and valid_objs'
                                                 and valid_bound_obj' valid_replies'_sc_asrt replyOpt
                                                 and pspace_aligned' and pspace_distinct'
                                                 and pspace_bounded'"
                                          in corres_guard_imp[OF corres_if])
                                 apply (simp add: fault_rel_optionation_def)
                                apply (rule corres_if2)
                                  apply simp
                                 apply (rule corres_split_eqr[OF threadGet_corres replyPush_corres])
                                    apply (clarsimp simp: tcb_relation_def)
                                   apply (clarsimp simp: fault_rel_optionation_def split: option.splits)
                                  prefer 3 \<comment> \<open> defer wp until corres complete \<close>
                                  apply (rule setThreadState_corres, simp)
                                 prefer 3 \<comment> \<open> defer wp until corres complete \<close>
                                 apply (rule corres_split[OF setThreadState_corres], simp)
                                   apply (rule possibleSwitchTo_corres, simp)
                                  apply (wpsimp wp: set_thread_state_valid_sched_action
                                                    set_thread_state_ep_queues_blocked_not_queued
                                                    set_thread_state_ntfn_queues_blocked_not_queued
                                                    set_thread_state_ready_queues_runnable_not_queued)
                                 apply (wpsimp wp: setThreadState_sched_pointers_valid_sched_pointers)
                                apply wpsimp
                               apply wpsimp
                              apply clarsimp
                              apply (frule valid_objs_valid_tcbs)
                              apply (frule pred_tcb_at_tcb_at)
                              apply (frule (1) valid_sched_scheduler_act_not_better[OF _ st_tcb_weakenE])
                               apply (clarsimp simp: is_blocked_on_send_def)
                              apply (frule (1) not_idle_thread',
                                     clarsimp simp: is_blocked_on_send_def)
                              apply (clarsimp simp: valid_sched_def valid_idle_def
                                             split: if_splits cong: conj_cong)
                              apply (prop_tac "not_in_release_q sender s")
                               apply (erule valid_release_q_not_in_release_q_not_runnable)
                               apply (fastforce simp: st_tcb_at_def obj_at_def runnable_eq_active)
                              apply (subgoal_tac "replyOpt \<noteq> None
                                                  \<longrightarrow> the replyOpt \<notin> fst ` replies_with_sc s")
                               apply (prop_tac "st_tcb_at (\<lambda>st. reply_object st = None) sender s")
                                apply (fastforce elim!: pred_tcb_weakenE
                                                  simp: is_blocked_on_send_def)
                               apply (frule valid_sched_action_weak_valid_sched_action)
                               apply (clarsimp simp: valid_sched_def
                                              split: if_splits cong: conj_cong)
                               subgoal by fastforce
                              apply (fastforce simp: image_def)
                             apply (clarsimp, frule valid_objs'_valid_tcbs')
                             apply (clarsimp simp: valid_sched_def split: if_splits
                                             cong: conj_cong)
                             apply (case_tac replyOpt; simp)
                            apply wpsimp
                           apply wpsimp
                          apply (wpsimp simp: if_cond_refill_unblock_check_def
                                          wp: refill_unblock_check_valid_sched
                                              valid_bound_obj_lift hoare_vcg_ball_lift)
                         apply (wpsimp wp: valid_bound_obj'_lift valid_replies'_sc_asrt_lift)
                        apply (rule_tac Q'="\<lambda>rv. all_invs_but_sym_refs and valid_sched
                                                 and ep_queues_blocked and ntfn_queues_blocked
                                                 and not_queued sender
                                                 and not ep_queued sender and not ntfn_queued sender
                                                 and current_time_bounded and tcb_at sender
                                                 and tcb_at thread
                                                 and st_tcb_at is_blocked_on_send sender
                                                 and (\<lambda>s. \<forall>r\<in>zobj_refs reply_cap. ex_nonz_cap_to r s)
                                                 and valid_list and bound_sc_tcb_at ((=) rv) sender
                                                 and (\<lambda>s. sym_refs
                                                            (\<lambda>p. if p = sender
                                                                 then tcb_non_st_state_refs_of s sender
                                                                 else state_refs_of s p))
                                                 and valid_bound_obj
                                                       (\<lambda>r s. r \<notin> fst ` replies_with_sc s) replyOpt
                                                 and receive_ipc_preamble_rv reply_cap replyOpt"
                                     in hoare_post_imp)
                         apply (clarsimp simp: valid_sched_active_scs_valid)
                         apply (rule conjI)
                          apply (rename_tac rv s; case_tac rv; simp)
                          apply (rule context_conjI)
                           apply (clarsimp simp: obj_at_def is_tcb pred_tcb_at_def)
                           apply (drule sym[of "Some _"])
                           apply (erule_tac x=sender in valid_objsE, simp)
                           apply (clarsimp simp: obj_at_def is_sc_obj valid_tcb_def valid_obj_def)
                          apply (clarsimp simp: valid_sched_active_scs_valid
                                                opt_map_red opt_pred_def obj_at_def is_sc_obj)
                         apply (clarsimp simp: obj_at_def is_tcb pred_tcb_at_def sc_tcb_sc_at_def
                                        split: if_split)
                         apply (drule send_signal_WN_sym_refs_helper)
                         apply (prop_tac "heap_ref_eq x sender (tcb_scps_of s)")
                          apply (clarsimp simp: vs_all_heap_simps)
                         apply (drule_tac p=t and p'=sender in heap_refs_retract_inj_eq; simp)
                         apply (clarsimp simp: vs_all_heap_simps)
                         apply (drule_tac t=t in valid_release_q_not_in_release_q_not_runnable[
                                                   OF valid_sched_valid_release_q])
                          apply (clarsimp simp: is_blocked_on_send_def pred_tcb_at_def obj_at_def)
                         apply clarsimp
                        apply (wpsimp wp: thread_get_wp')
                       apply (wpsimp wp: threadGet_wp)
                      apply (rule_tac Q'="\<lambda>_. all_invs_but_sym_refs and valid_sched and valid_list
                                              and ep_queues_blocked and ntfn_queues_blocked
                                              and not_queued sender
                                              and not ep_queued sender and not ntfn_queued sender
                                              and current_time_bounded and tcb_at sender
                                              and tcb_at thread and st_tcb_at is_blocked_on_send sender
                                              and (\<lambda>s. \<forall>r\<in>zobj_refs reply_cap. ex_nonz_cap_to r s)
                                              and (\<lambda>s. sym_refs
                                                         (\<lambda>p. if p = sender
                                                              then tcb_non_st_state_refs_of s sender
                                                              else state_refs_of s p))
                                              and valid_bound_obj
                                                    (\<lambda>r s. r \<notin> fst ` replies_with_sc s) replyOpt
                                              and receive_ipc_preamble_rv reply_cap replyOpt"
                                   in hoare_post_imp)
                       apply (clarsimp simp: valid_sched_active_scs_valid)
                       apply (rename_tac opt; case_tac opt;
                              clarsimp simp: obj_at_def is_tcb pred_tcb_at_def)
                      apply (wpsimp wp: do_ipc_transfer_tcb_caps hoare_vcg_ball_lift
                                        valid_bound_obj_lift)
                     apply (rule_tac Q'="\<lambda>_ s. tcb_at' sender s \<and> \<not> is_sched_linked sender s
                                               \<and> tcb_at' thread s
                                               \<and> sym_heap_sched_pointers s \<and> valid_sched_pointers s
                                               \<and> valid_objs' s
                                               \<and> pspace_aligned' s \<and> pspace_distinct' s
                                               \<and> pspace_bounded' s
                                               \<and> valid_bound_obj' valid_replies'_sc_asrt replyOpt s"
                                  in hoare_post_imp)
                      apply (clarsimp simp: obj_at'_def split: option.split)
                     apply (wpsimp wp: valid_replies'_sc_asrt_lift valid_bound_obj'_lift)
                    apply (wpsimp wp: gts_st_tcb_at)
                   apply wpsimp
                  apply (wpsimp wp: tcb_ep_dequeue_not_ep_queued)
                  apply (wpsimp simp: tcb_ep_dequeue_def
                                  wp: get_simple_ko_wp hoare_vcg_all_lift hoare_vcg_imp_lift'
                                      hoare_vcg_ball_lift valid_bound_obj_lift)
                 apply (clarsimp simp: valid_pspace'_def pred_conj_def cong: conj_cong)
                 apply (wpsimp wp: valid_replies'_sc_asrt_lift valid_bound_obj'_lift hoare_drop_imps)
                apply (clarsimp simp: invs_def valid_state_def st_tcb_at_tcb_at
                                      valid_pspace_def live_def)
                apply (prop_tac "sender \<noteq> epptr")
                 apply (fastforce simp: valid_ep_def obj_at_def is_obj_defs)
                apply (prop_tac "st_tcb_at (\<lambda>st. \<exists>data. st = Structures_A.BlockedOnSend epptr data)
                                           sender s")
                 apply (force intro!: in_send_ep_queue_st_tcb_at simp: obj_at_def)
                apply (prop_tac "ex_nonz_cap_to epptr s")
                 apply (fastforce simp: live_def obj_at_def is_ep elim!: if_live_then_nonz_capD2)
                apply (frule valid_sched_valid_ready_qs)
                apply (frule valid_sched_valid_release_q)
                apply (clarsimp cong: conj_cong)
                apply (intro conjI impI allI; (solves clarsimp)?)
                     apply (clarsimp simp: in_ep_queue_at_def obj_at_def eps_of_kh_def opt_map_red)
                    apply (erule valid_ready_qs_not_queued_not_runnable)
                    apply (force elim!: st_tcb_weakenE)
                   apply (rule not_ntfn_blocked_not_ntfn_queued)
                    apply (force elim: st_tcb_weakenE
                                 simp: ntfn_blocked_def split: thread_state.splits)
                   apply fastforce
                  apply (force elim: st_tcb_weakenE split: thread_state.splits)
                 apply (drule (1) ko_at_obj_congD)
                 apply clarsimp
                 apply (prop_tac "filter ((\<noteq>) sender) queue = queue")
                  apply (fastforce simp: valid_ep_def filter_id_conv)
                 apply (force simp: removeAll_filter_not_eq intro!: receiveIPC_corres_sym_refs_helper)
                apply (frule (2) ri_preamble_not_in_sc)
                apply (frule_tac y=sender in valid_sched_scheduler_act_not_better)
                 apply (fastforce simp: st_tcb_at_refs_of_rev elim: st_tcb_weakenE)
                apply (clarsimp simp: list_case_If split: if_splits)
               apply (fastforce simp: invs'_def split: list.split)
              \<comment> \<open>RecvEP\<close>
              apply (simp add: ep_relation_def)
              apply (fold dc_def)[1]
              apply (corres corres: receiveIPCBlocked_corres)
               apply fastforce
              apply (clarsimp simp: obj_at'_def)
             \<comment> \<open> end of ep cases \<close>
             apply (rule_tac Q'="\<lambda>_. einvs and st_tcb_at runnable thread
                                     and not_queued thread and not_in_release_q thread
                                     and ko_at (kernel_object.Endpoint ep) epptr
                                     and current_time_bounded
                                     and receive_ipc_preamble_rv reply_cap replyOpt and ?rrefs"
                          in hoare_post_imp)
              apply clarsimp
              apply (frule invs_sym_refs)
              apply (intro conjI)
                  apply (rule not_ep_blocked_not_ep_queued)
                   apply (erule st_tcb_weakenE)
                   apply (case_tac st; clarsimp simp: ep_blocked_def)
                  apply fastforce
                 apply (rule not_ntfn_blocked_not_ntfn_queued)
                  apply (erule st_tcb_weakenE)
                  apply (case_tac st; clarsimp simp: ntfn_blocked_def)
                 apply fastforce
                apply (fastforce elim: runnable_nonz_cap_to)
               apply (clarsimp simp: obj_at_def is_ep)
              apply (frule (1) valid_objs_ko_at[OF invs_valid_objs])
              apply (clarsimp simp: valid_obj_def)
             apply (wpsimp wp: hoare_vcg_ball_lift)
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
     apply (rule_tac Q'="\<lambda>r. invs and ep_at epptr and valid_list and current_time_bounded
                             and scheduler_act_not thread and scheduler_act_sane
                             and (\<lambda>s. thread \<noteq> idle_thread s)
                             and valid_sched and st_tcb_at runnable thread
                             and receive_ipc_preamble_rv reply_cap r
                             and not_queued thread and not_in_release_q thread and ?rrefs"
                  in hoare_post_imp)
      apply clarsimp
      apply (intro conjI impI allI; clarsimp?)
       apply (fastforce dest!: valid_objs_valid_tcb
                         simp: obj_at_def valid_tcb_def valid_bound_obj_def split: option.splits)
      apply (rename_tac bound_ntfn ntfn)
      apply (prop_tac "ntfn_at bound_ntfn s")
       apply (clarsimp simp: obj_at_def is_ntfn_def)
      apply (clarsimp split: if_splits)
      apply (frule valid_sched_valid_ready_qs)
      apply (fastforce simp: in_opt_pred opt_map_red obj_at_def)
     apply (wpsimp wp: receive_ipc_preamble_invs receive_ipc_preamble_valid_sched
                       receive_ipc_preamble_st_tcb_at receive_ipc_preamble_rv hoare_vcg_ball_lift)
    apply (rule_tac Q'="\<lambda>replyOpt s. ep_at' epptr s \<and> tcb_at' thread s \<and> invs' s
                                     \<and> thread \<noteq> idle_thread_ptr \<and> valid_bound_reply' replyOpt s"
                 in hoare_post_imp)
     apply (fastforce split: if_split option.splits)
    apply wpsimp
   apply clarsimp
   apply (frule valid_sched_valid_ready_qs)
   apply (frule valid_sched_valid_release_q)
   apply (frule valid_sched_ready_or_release)
   apply (clarsimp simp: valid_cap_def valid_idle_def invs_def valid_state_def)
   apply (erule st_tcb_weakenE)
   apply (metis runnable_eq_active)
  apply (fastforce intro!: tcb_at_cross simp: valid_cap'_def)
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

lemma det_wp_tcb_append_set_notification[wp]:
  "det_wp (\<lambda>s. (\<forall>t \<in> set (ntfn_queue_of ntfn). tcb_at t s)
               \<and> tcb_at tptr s \<and> ntfn_at ntfnPtr s)
     (do qs' \<leftarrow> tcb_append tptr (ntfn_queue_of ntfn);
         set_notification ntfnPtr (ntfn_set_obj ntfn (WaitingNtfn qs'))
      od)"
  by wpsimp

lemmas no_fail_tcb_append_set_notification = det_wp_no_fail[OF det_wp_tcb_append_set_notification]

lemma tcb_append_set_notification_empty_fail:
  "empty_fail
     (do q' \<leftarrow> tcb_append tptr qs;
         set_notification ntfn_ptr (ntfn_set_obj notification (WaitingNtfn qs'))
      od)"
  by wpsimp

lemmas tcb_append_ntfn_rules =
  det_wp_tcb_append no_fail_tcb_append
  det_wp_tcb_append_set_notification no_fail_tcb_append_set_notification
  tcb_append_empty_fail tcb_append_set_notification_empty_fail

method ipc_ntfn_append =
  (rule det_wp_pre no_fail_pre, rule tcb_append_ntfn_rules, fastforce)[1] | wpsimp

lemma tcbNTFNAppend_corres:
  "\<lbrakk>tcb_ptr = tcbPtr; ntfn_ptr = ntfnPtr\<rbrakk> \<Longrightarrow>
   corres dc
     (not ep_queued tcbPtr and not ntfn_queued tcbPtr
      and not_queued tcbPtr and not_in_release_q tcbPtr and ntfn_at ntfn_ptr and tcb_at tcb_ptr
      and ep_queues_blocked and ntfn_queues_blocked and ready_queues_runnable and release_q_runnable
      and valid_objs and sorted_ipc_queues and in_correct_ready_q and ready_qs_distinct
      and ready_or_release and pspace_aligned and pspace_distinct)
     (\<lambda>s. sym_heap_sched_pointers s \<and> valid_objs' s \<and> \<not> is_sched_linked tcbPtr s)
     (tcb_ntfn_append tcb_ptr ntfn_ptr) (tcbNTFNAppend tcbPtr ntfnPtr)"
  supply if_split[split del] tcb_append_rv_wf'[wp del] tcb_append_rv_wf''[wp del]
         ghost_relation_wrapper_def[simp del] (*FIXME arch-split RT: not necessary after arch-split*)
         heap_ghost_relation_wrapper_def[simp del] (*FIXME arch-split RT: not necessary after arch-split*)
  apply (rule_tac Q'="tcb_at' tcb_ptr" in corres_cross_add_guard, fastforce intro!: tcb_at_cross)
  apply (rule_tac Q'=pspace_aligned' in corres_cross_add_guard)
   apply (fastforce dest!: pspace_aligned_cross)
  apply (rule_tac Q'=pspace_distinct' in corres_cross_add_guard)
   apply (fastforce dest!: pspace_distinct_cross)
  apply (rule_tac Q'="ntfn_at' ntfnPtr" in corres_cross_add_guard, fastforce intro!: ntfn_at_cross)
  apply (clarsimp simp: tcb_ntfn_append_def tcbNTFNAppend_def)
  apply (rule corres_split_forwards'[OF _ get_simple_ko_sp get_ntfn_sp'])
   apply (corres corres: getNotification_corres)
  apply (rename_tac ntfn ntfn')
  apply (rule_tac Q="\<lambda>s. ntfn_queues_of s ntfn_ptr = Some (ntfn_queue (ntfn_obj ntfn))
                         \<and> valid_ntfn ntfn s
                         \<and> (\<forall>t \<in> set (ntfn_queue (ntfn_obj ntfn)). tcb_at t s)
                         \<and> sorted_wrt (img_ord (prios_of s) (opt_ord_rel (\<ge>))) (ntfn_queue (ntfn_obj ntfn))"
               in corres_cross_add_abs_guard)
   apply (intro context_conjI)
      apply (fastforce simp: obj_at_def opt_map_red)
     apply (fastforce intro: valid_objs_valid_ntfn simp: obj_at_def)
    apply (case_tac "ntfn_obj ntfn"; clarsimp simp: valid_ntfn_def)
   apply (fastforce intro!: sorted_ipc_queues_notification_priority_ordered)
  apply (rule_tac Q'="\<lambda>s'. tcb_ptr \<notin> set (ntfn_queue (ntfn_obj ntfn))
                           \<and> (\<forall>t \<in> set (ntfn_queue (ntfn_obj ntfn)). tcb_at' t s'
                                                                     \<and> sched_flag_set s' t)
                           \<and> valid_ntfn' ntfn' s'
                           \<and> list_queue_relation
                               (ntfn_queue (ntfn_obj ntfn)) (ntfnQueue ntfn')
                               (tcbSchedNexts_of s') (tcbSchedPrevs_of s')
                           \<and> (ntfn_queue (ntfn_obj ntfn) = [] \<longleftrightarrow> ntfnQueue ntfn' = emptyQueue)
                           \<and> sorted_wrt (img_ord (\<lambda>t. threadRead tcbPriority t s')
                                         (opt_ord_rel (\<ge>))) (ntfn_queue (ntfn_obj ntfn))"
               in corres_cross_add_guard)
   apply clarsimp
   apply (frule (3) in_ntfn_queue_sched_flag_set[where p=ntfn_ptr])
    apply force
   apply (intro context_conjI)
       apply (clarsimp simp: in_ntfn_queue_at_def ntfn_queued_def)
      apply (fastforce dest: ntfn_ko_at_valid_objs_valid_ntfn')
     apply (fastforce dest: ntfn_ko_at_valid_objs_valid_ntfn')
    apply (fastforce intro!: ntfn_queues_relationD simp: opt_map_red obj_at'_def)
   apply (fastforce dest: list_queue_relation_Nil_iff_emptyHeadEndPtrs)
   apply clarsimp
   apply (frule (1) sorted_ipc_queues_notification_priority_ordered)
   apply (erule sorted_wrt_img_ord_eq_lift[THEN iffD1, rotated])
   apply (rename_tac t)
   apply (simp flip: thread_read_Some_tcbs_of)
   apply (rule_tac f="thread_read tcb_priority t" and g="threadRead tcbPriority t"
                in rcorres_rrel_eq)
      apply (rule threadGet_rcorres[where rrel="(=)"])
      apply (clarsimp simp: tcb_relation_def)
     apply (frule state_relation_pspace_relation)
     apply (clarsimp simp: pspace_relation_heap_pspace_relation)
    apply (fastforce intro!: no_ofailD[OF thread_read_no_ofail])
   apply (fastforce intro!: no_ofailD[OF no_ofail_threadRead_tcb_at'])
  apply (rule corres_stateAssert_ignore)
   apply (fastforce dest!: list_queue_relation_tcb_queue_head_end_valid)
  apply (rule corres_underlying_from_rcorres)
   apply (clarsimp simp: tcbAppend_def)
   apply (rule_tac R="\<lambda>_. ntfn_at' ntfnPtr" in no_fail_bind[where P=P and Q=P for P, simplified])
     apply (wpsimp wp: hoare_vcg_if_lift2 hoare_drop_imps)
    apply wpsimp
   apply (wpsimp wp: no_fail_orderedInsert no_fail_stateAssert)
   apply (meson no_ofailD[OF no_ofail_threadRead])
  apply (clarsimp simp: state_relation_def pspace_relation_heap_pspace_relation
                        heap_pspace_relation_def ghost_relation_heap_ghost_relation)
  apply (rule_tac Q="\<lambda>s s'. (\<forall>t \<in> set (ntfn_queue (ntfn_obj ntfn)). tcb_at t s)
                            \<and> (\<forall>t \<in> set (ntfn_queue (ntfn_obj ntfn)). tcb_at' t s')
                            \<and> (s, s') \<in> state_relation"
               in rcorres_add_to_pre)
   apply (intro context_conjI)
     apply (case_tac "ntfn_obj ntfn"; clarsimp simp: valid_ntfn_def)
    apply (fastforce intro: tcb_at_cross_tcbs_relation)
   apply (clarsimp simp: state_relation_def pspace_relation_heap_pspace_relation
                         heap_pspace_relation_def ghost_relation_heap_ghost_relation)
  apply (rcorres_conj_lift \<open>fastforce\<close>
                           rule: det_wp_tcb_append_set_notification simp: tcbAppend_def)+
  apply (rule rcorres_conj_lift_fwd; (solves ipc_ntfn_append)?)
    \<comment> \<open>ntfns_relation\<close>
   apply (clarsimp simp: tcbAppend_def bind_assoc)
   apply (rule rcorres_stateAssert_r_fwd)
   apply (rule_tac Q="\<lambda>ls q s s'. ntfns_relation s s'
                                  \<and> list_queue_relation
                                      ls q (tcbSchedNexts_of s') (tcbSchedPrevs_of s')
                                  \<and> ko_at (kernel_object.Notification ntfn) ntfnPtr s
                                  \<and> ko_at' ntfn' ntfnPtr s'"
                in rcorres_split)
    apply (rule rcorres_from_valid_det)
     apply wpsimp
     apply (clarsimp simp: obj_at_def is_ntfn_def)
    apply (drule in_set_notification)
    apply (wpsimp wp: updateNotification_wp)
    apply (clarsimp simp: projectKO_opts_defs map_relation_def ntfn_relation_def
                          obj_at_def is_ntfn_def obj_at'_def valid_ntfn'_def
                   split: if_splits ntfn.splits Structures_A.kernel_object.splits)
   apply (rcorres rcorres: orderedInsert_rcorres threadGet_rcorres
                     simp: tcb_append_def tcbAppend_def tcb_relation_def)
   apply (clarsimp simp: thread_read_Some_tcbs_of)
  apply (rcorres_conj_lift \<open>fastforce\<close>
                           rule: det_wp_tcb_append_set_notification simp: tcbAppend_def)+
  apply (rule rcorres_conj_lift_fwd; (solves ipc_ntfn_append)?)
   \<comment> \<open>ep_queues_relation\<close>
   apply (simp only: ep_queues_relation_def)
   apply (rcorres rcorres: tcbAppend_rcorres_other rcorres_op_lifts)
   apply (clarsimp simp: heap_pspace_relation_def in_ep_queue_at_def ep_queued_def)
   apply (blast dest: ep_queues_ntfn_queues_disjoint)
  apply (rule rcorres_conj_lift_fwd; (solves ipc_ntfn_append)?)
  \<comment> \<open>ntfn_queues_relation\<close>
   apply (clarsimp simp: bind_assoc)
   apply (simp only: ntfn_queues_relation_def)
   apply (rule rcorres_allI_fwd; (solves wpsimp)?)
   apply (rename_tac p)
   apply (case_tac "p \<noteq> ntfnPtr")
    apply (rule_tac Q="\<lambda>_ _ s s'. ntfn_at ntfnPtr s
                                  \<and> (\<forall>ls q. ntfn_queues_of s p = Some ls
                                            \<longrightarrow> ntfnQueues_of s' p = Some q
                                            \<longrightarrow> list_queue_relation
                                                  ls q (tcbSchedNexts_of s') (tcbSchedPrevs_of s'))"
                 in rcorres_split)
     apply (rcorres rcorres: rcorres_op_lifts
                         wp: set_notification_ntfn_queues_of_other
                             updateNotification_ntfnQueues_of_other)
     apply fastforce
    apply (rcorres rcorres: tcbAppend_rcorres_other rcorres_allI rcorres_imp_lift)
    apply (clarsimp simp: in_ntfn_queue_at_def ntfn_queued_def heap_pspace_relation_def)
    apply (blast dest: ntfn_queues_disjoint)
   \<comment> \<open>p = ntfnPtr\<close>
   apply (rule_tac Q="\<lambda>ls q s s'. ntfn_at ntfnPtr s
                                  \<and> list_queue_relation
                                      ls q (tcbSchedNexts_of s') (tcbSchedPrevs_of s')"
                in rcorres_split)
    apply (rule rcorres_from_valid_det; (solves wpsimp)?)
    apply (wpsimp wp: updateNotification_wp)
    apply (drule in_set_notification)
    apply (clarsimp simp: obj_at'_def projectKO_opts_defs)
    subgoal
      by (fastforce simp: projectKO_opts_defs opt_map_def split: kernel_object.splits)
   apply (rcorres rcorres: tcbAppend_rcorres)
   apply (clarsimp simp: heap_pspace_relation_def thread_read_Some_tcbs_of)
  apply (rule rcorres_conj_lift_fwd; (solves ipc_ntfn_append)?)
    \<comment> \<open>ready_queues\<close>
   apply (simp only: ready_queues_relation_def ready_queue_relation_def Let_def)
   apply (intro rcorres_allI_fwd; (solves ipc_ntfn_append)?)
   apply (rename_tac d p)
   apply (rule_tac p="\<lambda>s. ready_queues s d p" in rcorres_lift_abs)
    apply (rule_tac p="\<lambda>s'. ksReadyQueues s' (d, p)" in rcorres_lift_conc)
     apply (rcorres rcorres: tcbAppend_rcorres_other rcorres_op_lifts)
     apply (clarsimp simp: heap_pspace_relation_def not_queued_def)
     apply (blast dest!: ntfn_queues_ready_queues_disjoint)
    apply wpsimp
   apply wpsimp
  apply (rule rcorres_conj_lift_fwd; (solves ipc_ntfn_append)?)
   \<comment> \<open>release_queue_relation\<close>
   apply (simp only: release_queue_relation_def)
   apply (rule_tac p=release_queue in rcorres_lift_abs)
    apply (rule_tac p=ksReleaseQueue in rcorres_lift_conc)
     apply (rcorres rcorres: tcbAppend_rcorres_other rcorres_op_lifts)
     apply (clarsimp simp: heap_pspace_relation_def not_in_release_q_def)
     apply (blast dest!: ntfn_queues_release_queue_disjoint)
    apply wpsimp
   apply wpsimp
  by (rcorres_conj_lift \<open>fastforce\<close>
                        rule: det_wp_tcb_append_set_notification simp: tcbAppend_def)+

crunch tcb_ntfn_append, tcb_ep_append
  for valid_tcbs[wp]: valid_tcbs
  and pspace_aligned[wp]: pspace_aligned
  and pspace_distinct[wp]: pspace_distinct
  and weak_valid_sched_action[wp]: weak_valid_sched_action
  and in_correct_ready_q[wp]: in_correct_ready_q
  and ready_qs_distinct[wp]: ready_qs_distinct
  and ready_queues_runnable[wp]: ready_queues_runnable
  (wp: crunch_wps ready_queues_runnable_lift ignore: set_simple_ko)

lemma tcbNTFNAppend_valid_objs'[wp]:
  "\<lbrace>valid_objs' and tcb_at' tcbPtr\<rbrace> tcbNTFNAppend tcbPtr ntfnPtr \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  unfolding tcbNTFNAppend_def updateNotification_def
  apply (wpsimp wp: getNotification_wp hoare_vcg_all_lift hoare_vcg_imp_lift
              simp: tcbAppend_def valid_ntfn'_def)
  apply normalise_obj_at'
  apply (frule (1) ntfn_ko_at_valid_objs_valid_ntfn')
  apply (clarsimp simp: valid_ntfn'_def valid_bound_obj'_def split: option.splits)
  done

crunch tcbEPAppend
  for valid_objs'[wp]: valid_objs'
  (wp: crunch_wps)

lemma tcbAppend_sym_heap_sched_pointers[wp]:
  "\<lbrace>\<lambda>s. \<not> is_sched_linked tcbPtr s\<rbrace> tcbAppend tcbPtr q \<lbrace>\<lambda>_. sym_heap_sched_pointers\<rbrace>"
  unfolding tcbAppend_def
  by (wpsimp wp: getNotification_wp)

lemma tcbNTFNAppend_sym_heap_sched_pointers[wp]:
  "\<lbrace>\<lambda>s. \<not> is_sched_linked tcbPtr s\<rbrace> tcbNTFNAppend tcbPtr ntfnPtr \<lbrace>\<lambda>_. sym_heap_sched_pointers\<rbrace>"
  unfolding tcbNTFNAppend_def
  by (wpsimp wp: getNotification_wp)

lemma tcbEPAppend_sym_heap_sched_pointers[wp]:
  "tcbEPAppend tcbPtr epPtr isRecv \<lbrace>sym_heap_sched_pointers\<rbrace>"
  unfolding tcbEPAppend_def
  by (wpsimp wp: getEndpoint_wp)

crunch tcbNTFNAppend, tcbEPAppend
  for valid_sched_pointers[wp]: valid_sched_pointers
  (wp: crunch_wps)

lemma setThreadState_inIPCQueueThreadState_valid_sched_pointers:
  "\<lbrace>valid_sched_pointers_except tcbPtr and K (inIPCQueueThreadState st)\<rbrace>
   setThreadState st tcbPtr
   \<lbrace>\<lambda>_. valid_sched_pointers\<rbrace>"
  unfolding setThreadState_def
  apply (wpsimp wp: threadSet_wp)
  apply (clarsimp simp: valid_sched_pointers_def opt_pred_def)
  done

lemma inIPCQueueThreadState_sched_flag_set:
  "\<lbrace>K (inIPCQueueThreadState st)\<rbrace> setThreadState st tcbPtr \<lbrace>\<lambda>_ s. sched_flag_set s tcbPtr\<rbrace>"
  unfolding setThreadState_def scheduleTCB_def
  by (wpsimp wp: threadSet_wp getSchedulable_wp)

lemma receiveSignalBlocked_sym_refs_helper:
  "\<lbrakk>sym_refs (state_refs_of s); ntfn_obj ntfn = IdleNtfn \<or> (\<exists>q. ntfn_obj ntfn = WaitingNtfn q);
    ko_at (kernel_object.Notification ntfn) ntfn_ptr s; st_tcb_at runnable thread s\<rbrakk>
   \<Longrightarrow> sym_refs
         (\<lambda>a. if a = ntfn_ptr
              then insert (thread, NTFNSignal)
                          (set (ntfn_queue (ntfn_obj ntfn)) \<times> {NTFNSignal}
                           \<union> get_refs NTFNBound (ntfn_bound_tcb ntfn)
                           \<union> get_refs NTFNSchedContext (ntfn_sc ntfn))
              else if a = thread
                   then insert (ntfn_ptr, TCBSignal) (tcb_non_st_state_refs_of s thread)
                   else state_refs_of s a)"
  by (elim disjE; erule delta_sym_refs; clarsimp split: if_split_asm;
      fastforce simp: state_refs_of_def get_refs_def2 tcb_st_refs_of_def pred_tcb_at_def obj_at_def
                      runnable_eq_active
               split: if_split_asm option.splits)

lemma receiveSignalBlocked_corres:
  "ntfn_obj ntfn = IdleNtfn \<or> ntfn_obj ntfn = WaitingNtfn queue \<Longrightarrow>
   corres dc
     (ko_at (kernel_object.Notification ntfn) ntfn_ptr
      and invs and weak_valid_sched_action and scheduler_act_not thread
      and valid_ready_qs and valid_release_q and sorted_ipc_queues and ready_or_release
      and active_scs_valid
      and st_tcb_at runnable thread and not_queued thread and not_in_release_q thread)
     invs'
     (receive_signal_blocked thread ntfn_ptr isBlocking)
     (receiveSignalBlocked thread ntfn_ptr isBlocking)"
  apply (rule_tac Q'="st_tcb_at' runnable' thread" in corres_cross_add_guard)
   apply (fastforce intro: st_tcb_at_runnable_cross)
  apply (rule_tac Q'="\<lambda>s'. \<not> (tcbQueued |< tcbs_of' s') thread" in corres_cross_add_guard)
   apply (frule state_relation_ready_queues_relation)
   apply (frule in_ready_q_tcbQueued_eq[where t=thread])
   apply (clarsimp simp: not_queued_def in_ready_q_def)
  apply (rule_tac Q'="\<lambda>s'. \<not> (tcbInReleaseQueue |< tcbs_of' s') thread" in corres_cross_add_guard)
   apply (frule state_relation_release_queue_relation)
   apply (frule in_release_q_tcbInReleaseQueue_eq[where t=thread])
   apply (clarsimp simp: in_release_q_def)
  apply (clarsimp simp: receive_signal_blocked_def receiveSignalBlocked_def)
  apply (cases isBlocking; simp)
   apply (rule stronger_corres_guard_imp)
     apply (rule corres_split[OF setThreadState_corres])
        apply (clarsimp simp: thread_state_relation_def)
       apply (rule corres_split[OF tcbNTFNAppend_corres], simp, simp)
         apply (rule maybeReturnSc_corres)
        apply (wpsimp wp: abs_typ_at_lifts get_simple_ko_wp
                    simp: tcb_ntfn_append_def)
       apply ((wpsimp | strengthen valid_objs'_valid_tcbs')+)[1]
      apply (wpsimp wp: set_thread_state_ep_queues_blocked_not_queued
                        set_thread_state_ntfn_queues_blocked_not_queued
                        set_thread_state_ready_queues_runnable_not_queued
                        set_thread_state_release_q_runnable_not_in_release_q
                        set_thread_state_weak_valid_sched_action
                        hoare_vcg_all_lift hoare_vcg_imp_lift')
     apply (wpsimp wp: setThreadState_inIPCQueueThreadState_valid_sched_pointers
                       inIPCQueueThreadState_sched_flag_set)
    apply clarsimp
    apply (frule invs_sym_refs)
    apply (clarsimp cong: conj_cong)
    apply (intro conjI impI allI; fastforce?)
        apply (clarsimp simp: valid_tcb_state_def obj_at_def is_ntfn_def)
       apply (rule runnable_not_ep_queued; fastforce)
      apply (rule runnable_not_ntfn_queued; fastforce)
     apply (clarsimp simp: obj_at_def is_ntfn_def)
    apply (drule (1) ko_at_obj_congD)+
    apply (force intro!: receiveSignalBlocked_sym_refs_helper)
   apply (clarsimp cong: conj_cong)
   apply (frule invs_valid_sched_pointers)
   apply (frule (1) runnable'_Not_tcbInReleaseQueue_not_sched_linked[rotated])
    apply (fastforce simp: st_tcb_at'_def obj_at'_def opt_pred_def opt_map_red)
   apply (fastforce simp: valid_sched_pointers_except_def)
  apply (corres corres: doNBRecvFailedTransfer_corres)
   apply fastforce
  apply fastforce
  done

lemma receiveSignal_corres:
 "\<lbrakk>is_ntfn_cap cap; cap_relation cap cap'\<rbrakk> \<Longrightarrow>
  corres dc
    (invs and weak_valid_sched_action and scheduler_act_not thread and valid_ready_qs
     and st_tcb_at runnable thread and active_scs_valid and valid_release_q
     and sorted_ipc_queues and current_time_bounded
     and not_queued thread and not_in_release_q thread and ready_or_release
     and ex_nonz_cap_to thread and valid_cap cap)
    invs'
    (receive_signal thread cap isBlocking) (receiveSignal thread cap' isBlocking)"
  apply (rule_tac Q'="tcb_at' thread" in corres_cross_add_guard, fastforce intro!: tcb_at_cross)
  apply (rule_tac Q'="\<lambda>s'. \<not> (tcbQueued |< tcbs_of' s') thread" in corres_cross_add_guard)
   apply (frule state_relation_ready_queues_relation)
   apply (frule in_ready_q_tcbQueued_eq[where t=thread])
   apply (clarsimp simp: not_queued_def in_ready_q_def)
  apply (rule_tac Q'="\<lambda>s'. \<not> (tcbInReleaseQueue |< tcbs_of' s') thread" in corres_cross_add_guard)
   apply (frule state_relation_release_queue_relation)
   apply (frule in_release_q_tcbInReleaseQueue_eq[where t=thread])
   apply (clarsimp simp: in_release_q_def)
  apply (simp add: receive_signal_def receiveSignal_def)
  apply add_sym_refs
  apply add_valid_idle'
  apply (rule corres_stateAssert_assume[rotated], solves simp)+
  apply (rule corres_symb_exec_r[OF _ isRunnable_sp]; (solves wpsimp)?)
  apply (rule corres_assert_gen_asm_cross_forwards)
   apply (fastforce intro: st_tcb_at_runnable_cross)
  apply (rule corres_stateAssert_ignore)
   apply clarsimp
   apply (frule invs_valid_sched_pointers)
   apply (erule (2) valid_sched_pointersD[simplified])
   apply (fastforce dest: runnable'_not_inIPCQueueThreadState)
  apply (case_tac cap, simp_all add: isEndpointCap_def)
  apply (rename_tac cap_ntfn_ptr badge rights)
  apply (rule corres_split_forwards'[OF _ get_simple_ko_sp get_ntfn_sp'])
   apply (corres corres: getNotification_corres)
    apply (fastforce simp: valid_cap_def)
   apply fastforce
  apply (rename_tac ntfn ntfn')
  apply (case_tac "ntfn_obj ntfn"; clarsimp simp: ntfn_relation_def)
    apply (corres corres: receiveSignalBlocked_corres)
      apply fastforce
     apply fastforce
    apply fastforce
   apply (corres corres: receiveSignalBlocked_corres)
     apply fastforce
    apply fastforce
   apply fastforce
  \<comment> \<open>ActiveNtfn\<close>
  apply (rule corres_guard_imp)
    apply (clarsimp simp: badge_register_def badgeRegister_def)
    apply (rule corres_split[OF asUser_setRegister_corres])
      apply (clarsimp simp: updateNotification_def bind_assoc)
      apply (rule_tac Q'="ntfn_at' cap_ntfn_ptr" in corres_symb_exec_r')
         apply (rename_tac ntfn'')
         apply (rule_tac F="ntfn'' = ntfn'" in corres_gen_asm2)
         apply (rule corres_split[OF setNotification_no_queue_update_corres], simp)
            apply (clarsimp simp: ntfn_relation_def)
           apply (rule corres_split[OF maybeDonateSc_corres])
             apply (rule corres_split_eqr[OF get_tcb_obj_ref_corres])
                apply (clarsimp simp: tcb_relation_def)
               apply (rule ifCondRefillUnblockCheck_corres[unfolded dc_def])
              apply (wpsimp wp: get_tcb_obj_ref_wp)
             apply (wpsimp wp: threadGet_wp)
            apply (rule_tac Q'="\<lambda>_. tcb_at thread and active_scs_valid and pspace_distinct
                                    and pspace_aligned and valid_objs"
                         in hoare_post_imp)
             apply (clarsimp simp: obj_at_def is_tcb)
             apply (clarsimp split: option.splits)
             apply (erule (1) valid_objsE)
             apply (fastforce simp: valid_obj_def valid_tcb_def obj_at_def opt_map_def opt_pred_def
                                    is_sc_obj)
            apply (wpsimp wp: abs_typ_at_lifts)
           apply (rule_tac Q'="\<lambda>_. tcb_at' thread and valid_objs' and pspace_bounded'"
                        in hoare_post_imp)
            apply (clarsimp simp: obj_at'_def split: option.split)
           apply wpsimp
          apply (wpsimp wp: set_ntfn_minor_invs)
         apply (wpsimp wp: set_ntfn_minor_invs')
        apply (wpsimp wp: getNotification_wp)
       apply wpsimp
      apply wpsimp
     apply (wpsimp wp: as_user.tcb_agnostic_obj_at simp: valid_ntfn_def)
      apply (clarsimp simp: tcb_agnostic_pred_def)
     apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift')
    apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift')
   apply (clarsimp cong: conj_cong)
   apply (intro conjI impI allI; fastforce?)
      apply (clarsimp simp: obj_at_def)
     apply (clarsimp simp: valid_cap_def)
    apply (frule invs_valid_objs)
    apply (fastforce simp: valid_cap_def valid_objs_def valid_obj_def obj_at_def valid_ntfn_def)
   apply (frule invs_sym_refs)
   apply (frule_tac p=cap_ntfn_ptr in sym_refs_ko_atD[rotated])
    apply (fastforce simp: obj_at_def)
   apply clarsimp
   apply (fold fun_upd_def)
   apply (drule sym[of "state_refs_of _ _"])
   apply simp
  apply (clarsimp cong: conj_cong)
  apply (intro conjI impI allI; fastforce?)
    apply (clarsimp simp: obj_at'_def)
   apply (frule (1) ntfn_ko_at_valid_objs_valid_ntfn'[OF _ invs_valid_objs'])
   apply (clarsimp simp: valid_ntfn'_def obj_at'_def)
  apply (fastforce simp: obj_at'_def)
  done

declare lookup_cap_valid' [wp]

lemma thread_set_fault_valid_sched_except_blocked_except_released_ipc_qs[wp]:
  "thread_set (tcb_fault_update f) t \<lbrace>valid_sched_except_blocked_except_released_ipc_qs\<rbrace>"
  by (wpsimp wp: thread_set_fault_valid_sched_pred simp: valid_sched_2_def)

lemma sendFaultIPC_corres:
  assumes "fr f f'"
  assumes "cap_relation cap cap'"
  shows
  "corres (=)
     (invs and valid_list and valid_sched_action and active_scs_valid
      and valid_release_q and valid_ready_qs and ready_or_release and sorted_ipc_queues
      and st_tcb_at runnable thread and scheduler_act_not thread
      and not_queued thread and not_in_release_q thread
      and current_time_bounded
      and (\<lambda>s. can_donate \<longrightarrow> bound_sc_tcb_at (\<lambda>sc. sc \<noteq> None) thread s)
      and valid_cap cap and K (valid_fault_handler cap) and K (valid_fault f))
     (invs' and valid_cap' cap')
     (send_fault_ipc thread cap f can_donate) (sendFaultIPC thread cap' f' can_donate)"
  using assms
  apply (clarsimp simp: send_fault_ipc_def sendFaultIPC_def)
  apply (rule corres_gen_asm)
  apply (rule corres_gen_asm)
  apply (rule corres_stateAssert_ignore, clarsimp)
  apply (cases cap; simp add: valid_fault_handler_def tcb_relation_def)
  apply (rule stronger_corres_guard_imp)
    apply (rule corres_split)
       apply (rule threadset_corres;
              clarsimp simp: tcb_relation_def fault_rel_optionation_def inQ_def)
      apply (rule corres_split)
         apply (rule sendIPC_corres, clarsimp)
        apply (rule corres_trivial, clarsimp)
       apply (wpsimp wp: threadSet_invs_trivial thread_set_invs_but_fault_tcbs
                         thread_set_no_change_tcb_state thread_set_no_change_tcb_sched_context
                         thread_set_cte_wp_at_trivial ex_nonz_cap_to_pres hoare_weak_lift_imp
                         thread_set_in_correct_ready_q thread_set_ready_queues_runnable
                         thread_set_release_q_runnable
                   simp: ran_tcb_cap_cases valid_cap_def)+
   apply fastforce
  apply (frule cross_relF[OF _ tcb_at'_cross_rel[where t=thread]], fastforce)
  apply (fastforce simp: invs'_def valid_tcb_def valid_cap'_def obj_at'_def inQ_def)
  done

lemma gets_the_noop_corres:
  assumes P: "\<And>s. P s \<Longrightarrow> f s \<noteq> None"
  shows "corres dc P P' (gets_the f) (return x)"
  apply (clarsimp simp: corres_underlying_def gets_the_def
                        return_def gets_def bind_def get_def)
  apply (clarsimp simp: assert_opt_def return_def dest!: P)
  done

end

crunch sendFaultIPC, receiveIPC, receiveSignal
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n n p s)"
  (wp: crunch_wps hoare_vcg_all_lift simp: crunch_simps)

global_interpretation sendFaultIPC: typ_at_all_props' "sendFaultIPC t cap f d"
  by typ_at_props'
global_interpretation receiveIPC: typ_at_all_props' "receiveIPC t cap b r"
  by typ_at_props'
global_interpretation receiveSignal: typ_at_all_props' "receiveSignal t cap b"
  by typ_at_props'

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
  apply (simp add: cteInsert_def ex_nonz_cap_to'_def updateCap_def setUntypedCapAsFull_def)
  apply (wpsimp wp: updateMDB_weak_cte_wp_at setCTE_weak_cte_wp_at hoare_vcg_ex_lift
         | rule hoare_drop_imps
         | wp getCTE_wp)+ (* getCTE_wp is separate to apply it only to the last one *)
  apply (rule_tac x=cref in exI)
  apply (fastforce simp: cte_wp_at_ctes_of)
  done

context begin interpretation Arch . (*FIXME: arch-split*)

crunch setExtraBadge, doIPCTransfer
  for cap_to'[wp]: "ex_nonz_cap_to' p"
  (ignore: transferCapsToSlots
       wp: crunch_wps transferCapsToSlots_pres2 cteInsert_cap_to' hoare_vcg_const_Ball_lift
     simp: zipWithM_x_mapM ball_conj_distrib)

lemma st_tcb_idle':
  "\<lbrakk>valid_idle' s; st_tcb_at' P t s\<rbrakk> \<Longrightarrow>
   (t = ksIdleThread s) \<longrightarrow> P IdleThreadState"
  by (clarsimp simp: valid_idle'_def pred_tcb_at'_def obj_at'_def idle_tcb'_def)

crunch setExtraBadge, receiveIPC
  for it[wp]: "\<lambda>s. P (ksIdleThread s)"
  and irqs_masked' [wp]: "irqs_masked'"
  (ignore: transferCapsToSlots
       wp: transferCapsToSlots_pres2 crunch_wps hoare_vcg_all_lift
     simp: crunch_simps ball_conj_distrib)

crunch copyMRs, doIPCTransfer
  for ksQ'[wp]: "\<lambda>s. P (ksReadyQueues s)"
  and ct'[wp]: "\<lambda>s. P (ksCurThread s)"
  (wp: mapM_wp' hoare_drop_imps simp: crunch_simps)

lemma completeSignal_invs':
  "completeSignal ntfnptr tcb \<lbrace>invs'\<rbrace>"
  apply (simp add: completeSignal_def)
  apply (rule bind_wp[OF _ get_ntfn_sp'])
  apply (wpsimp wp: refillUnblockCheck_invs' threadGet_wp)
       apply (rule hoare_strengthen_post[where Q'="\<lambda>_. invs'"])
        apply wpsimp
       apply (clarsimp simp: obj_at'_def)
      apply (wpsimp wp: set_ntfn_minor_invs' getNotification_wp simp: updateNotification_def)
     apply (wpsimp wp: hoare_vcg_ex_lift hoare_weak_lift_imp hoare_vcg_all_lift
                       hoare_vcg_imp_lift')
    apply wpsimp
   apply wpsimp
  apply normalise_obj_at'
  apply (frule (1) ntfn_ko_at_valid_objs_valid_ntfn'[OF _ invs_valid_objs'])
  apply (fastforce simp: valid_ntfn'_def)
  done

lemma maybeReturnSc_st_tcb_at'[wp]:
  "maybeReturnSc nptr tptr \<lbrace>\<lambda>s. P (st_tcb_at' Q t s)\<rbrace>"
  by (wpsimp wp: hoare_drop_imps threadSet_cap_to' threadSet_pred_tcb_no_state
           simp: maybeReturnSc_def tcb_cte_cases_def cteCaps_of_def)

crunch scheduleTCB
  for invs'[wp]: invs'

crunch doNBRecvFailedTransfer
  for invs'[wp]: invs'

crunch tcbNTFNAppend
  for gsUntypedZeroRanges[wp]: "\<lambda>s. P (gsUntypedZeroRanges s)"
  (wp: crunch_wps)

lemma tcbNTFNAppend_invs':
  "\<lbrace>\<lambda>s. invs' s \<and> tcb_at' tcbPtr s \<and> sched_flag_set s tcbPtr \<and> \<not> is_sched_linked tcbPtr s\<rbrace>
   tcbNTFNAppend tcbPtr ntfnPtr
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: invs'_def valid_pspace'_def valid_dom_schedule'_def)
  by (wpsimp wp: valid_irq_node_lift valid_irq_handlers_lift'' irqs_masked_lift
           simp: cteCaps_of_def o_def)

lemma tcbEPAppend_invs':
  "\<lbrace>\<lambda>s. invs' s \<and> tcb_at' tcbPtr s \<and> sched_flag_set s tcbPtr\<rbrace>
   tcbEPAppend tcbPtr ntfnPtr isRecv
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: invs'_def valid_pspace'_def valid_dom_schedule'_def)
  by (wpsimp wp: valid_irq_node_lift valid_irq_handlers_lift'' irqs_masked_lift
           simp: cteCaps_of_def o_def)

(* t = ksCurThread s *)
lemma receiveSignal_invs'[wp]:
  "receiveSignal t cap isBlocking \<lbrace>invs'\<rbrace>"
  apply (simp add: receiveSignal_def doNBRecvFailedTransfer_def)
  apply (intro bind_wp[OF _ stateAssert_sp])
  apply (intro bind_wp[OF _ isRunnable_sp])
  apply (intro bind_wp[OF _ assert_sp])
  apply (intro bind_wp[OF _ stateAssert_sp])
  apply (rule bind_wp [OF _ get_ntfn_sp'], rename_tac ntfn)
  apply (case_tac "ntfnState ntfn"; clarsimp)
    \<comment> \<open>IdleNtfn\<close>
    apply (clarsimp simp: receiveSignalBlocked_def)
    apply (wpsimp wp: inIPCQueueThreadState_sched_flag_set
                      setThreadState_nonqueued_state_update maybeReturnSc_invs' tcbNTFNAppend_invs')
    apply (rule conjI)
     apply (erule pred_tcb'_weakenE)
     apply (rename_tac st, case_tac st; clarsimp)
    apply fastforce
   \<comment> \<open>ActiveNtfn\<close>
   apply (wpsimp wp: setNotification_invs' getNotification_wp hoare_vcg_imp_lift' hoare_vcg_all_lift
               simp: updateNotification_def)
   apply (fastforce simp: valid_obj'_def valid_ntfn'_def obj_at'_def
                    dest: invs_valid_objs')
  \<comment> \<open>WaitingNtfn\<close>
  apply (clarsimp simp: receiveSignalBlocked_def)
  apply (wpsimp wp: inIPCQueueThreadState_sched_flag_set
                    setThreadState_nonqueued_state_update maybeReturnSc_invs' tcbNTFNAppend_invs')
  apply (rule conjI)
   apply (erule pred_tcb'_weakenE)
   apply (rename_tac st, case_tac st; clarsimp)
  apply fastforce
  done

lemma updateReply_reply_at'_wp:
  "\<lbrace>\<lambda>s. P (if p = rptr then True else reply_at' p s)\<rbrace>
   updateReply rptr f
   \<lbrace>\<lambda>rv s. P (reply_at' p s)\<rbrace>"
  apply (rule hoare_weaken_pre, rule updateReply_obj_at')
  apply (clarsimp simp: obj_at'_real_def split: if_splits)
  done

crunch setThreadState
  for tcbSCs_of[wp]: "\<lambda>s. P (tcbSCs_of s)"
  (ignore: threadSet wp: threadSet_tcbSCs_of_inv simp: crunch_simps)

crunch replyUnlink
  for tcbSCs_of[wp]: "\<lambda>s. P (tcbSCs_of s)"
  and scs_of'[wp]: "\<lambda>s. P (scs_of' s)"
  (simp: crunch_simps)

lemma replyUnlink_misc_heaps[wp]:
  "replyUnlink rPtr tPtr \<lbrace>\<lambda>s. P (tcbSCs_of s) (scTCBs_of s) (scReplies_of s) (replySCs_of s)\<rbrace>"
  by (rule hoare_weaken_pre, wps, wp, simp)

lemma schedContextUpdateConsumed_scReplies_of[wp]:
  "schedContextUpdateConsumed scPtr \<lbrace>\<lambda>s. P (scReplies_of s) \<rbrace>"
  unfolding schedContextUpdateConsumed_def updateSchedContext_def
  apply (wpsimp simp: setSchedContext_def)
  apply (clarsimp simp: opt_map_def if_distrib)
  apply (erule subst[where P=P, rotated], rule ext)
  apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def split: option.splits)
  done

lemma schedContextUpdateConsumed_sc_tcbs_of[wp]:
  "schedContextUpdateConsumed scPtr \<lbrace>\<lambda>s. P (scTCBs_of s)\<rbrace>"
  unfolding schedContextUpdateConsumed_def updateSchedContext_def
  apply (wpsimp simp: setSchedContext_def)
  apply (clarsimp simp: opt_map_def if_distrib)
  apply (erule subst[where P=P, rotated], rule ext)
  apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def split: option.splits)
  done

crunch schedContextUpdateConsumed
  for tcbSCs_of[wp]: "\<lambda>s. P (tcbSCs_of s)"

lemma schedContextUpdateConsumed_misc_heaps[wp]:
  "schedContextUpdateConsumed scPtr
   \<lbrace>\<lambda>s. P (scReplies_of s) (replySCs_of s) (tcbSCs_of s) (scTCBs_of s)\<rbrace>"
  by (rule hoare_weaken_pre, wps, wp, simp)

crunch doIPCTransfer
  for scs_replies_of[wp]: "\<lambda>s. P (scReplies_of s) (replySCs_of s)"
  (wp: crunch_wps ignore: setSchedContext simp: zipWithM_x_mapM)

crunch doIPCTransfer
  for scs_tcbs_of[wp]: "\<lambda>s. P (tcbSCs_of s) (scTCBs_of s)"
  (wp: crunch_wps threadSet_tcbSCs_of_inv ignore: threadSet simp: zipWithM_x_mapM)

crunch setEndpoint
  for misc_heaps[wp]: "\<lambda>s. P (scReplies_of s) (replySCs_of s) (tcbSCs_of s) (scTCBs_of s)"
  (wp: crunch_wps)

lemma replyPush_sym_refs_list_refs_of_replies':
  "\<lbrace>(\<lambda>s. sym_refs (list_refs_of_replies' s)) and valid_replies' and valid_objs'
    and sym_heap_scReplies\<rbrace>
   replyPush callerPtr calleePtr replyPtr canDonate
   \<lbrace>\<lambda>_ s. sym_refs (list_refs_of_replies' s)\<rbrace>"
  supply if_split [split del]
  unfolding replyPush_def
  apply wpsimp
        apply (wpsimp wp: bindsym_heap_scReplies_list_refs_of_replies'
                          hoare_vcg_if_lift2 hoare_vcg_imp_lift' hoare_vcg_all_lift)
       apply (rule_tac Q'="(\<lambda>_ s. sym_refs (list_refs_of_replies' s) \<and>
        (\<forall>rptr scp. (scReplies_of s) scp = Some rptr
                     \<longrightarrow> replySCs_of s rptr = Some scp) \<and>
        \<not> is_reply_linked replyPtr s \<and> replySCs_of s replyPtr = None)"
      in hoare_strengthen_post[rotated])
        apply (fastforce split: if_splits simp del: comp_apply)
       apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift'
                         updateReply_list_refs_of_replies'_inv threadGet_wp)+
  apply (prop_tac "replyTCBs_of s replyPtr = None")
   apply (clarsimp simp: obj_at'_def opt_map_red)
  apply (frule valid_replies'_no_tcb_not_linked; clarsimp)
  apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def sym_heap_def pred_map_eq)
  done

lemma replyPush_untyped_ranges_zero'[wp]:
  "replyPush callerPtr calleePtr replyPtr canDonate \<lbrace>untyped_ranges_zero'\<rbrace>"
  apply (clarsimp simp: untyped_ranges_zero_inv_null_filter_cteCaps_of)
  apply (rule hoare_lift_Pf[where f="ctes_of"])
   apply wp+
  done

crunch replyPush
  for valid_bitmaps[wp]: valid_bitmaps
  (simp: crunch_simps wp: crunch_wps)

lemma replyPush_invs':
  "\<lbrace>invs' and sym_heap_scReplies\<rbrace>
   replyPush callerPtr calleePtr replyPtr canDonate
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  unfolding invs'_def valid_pspace'_def
  by (wpsimp wp: replyPush_sym_heap_sched_pointers replyPush_valid_sched_pointers
                 replyPush_sym_refs_list_refs_of_replies'
           simp: valid_pspace'_def)

lemma setEndpoint_invs':
  "setEndpoint eptr ep \<lbrace>invs'\<rbrace>"
  by (wpsimp simp: invs'_def valid_dom_schedule'_def comp_def)

crunch maybeReturnSc, cancelIPC
  for sch_act_not[wp]: "sch_act_not t"
  and sch_act_simple[wp]: "sch_act_simple"
  (wp: crunch_wps hoare_drop_imps simp: crunch_simps)

crunch maybeReturnSc, doIPCTransfer
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
  apply (rule bind_wp[OF _ stateAssert_sp])
  apply (rule bind_wp[OF _ stateAssert_sp])
  apply (rule bind_wp[OF _ gts_sp'])
  apply (case_tac state; clarsimp)
         \<comment> \<open>BlockedOnReceive\<close>
         apply (wpsimp wp: getEndpoint_wp
                           hoare_vcg_all_lift hoare_vcg_imp_lift')
         apply (clarsimp simp: pred_tcb_at'_def obj_at'_def)
         apply (drule_tac ko="ko :: reply" for ko in sym_refs_ko_atD'[rotated])
          apply (fastforce simp: obj_at'_def)
         apply (clarsimp simp: tcb_st_refs_of'_def tcb_bound_refs'_def
                               refs_of_rev' get_refs_def ko_wp_at'_def opt_map_def
                        split: option.splits if_splits)
        \<comment> \<open>BlockedOnReply\<close>
        apply (wp stateAssert_inv gts_wp' updateReply_obj_at'_inv
                  hoare_vcg_all_lift hoare_vcg_const_imp_lift hoare_vcg_imp_lift'
               | rule threadSet_pred_tcb_no_state
               | simp add: replyRemoveTCB_def cleanReply_def if_fun_split)+
        apply (clarsimp simp: pred_tcb_at'_def obj_at'_def)
        apply (drule_tac p=rptr and ko="ko :: reply" for ko in sym_refs_ko_atD'[rotated])
         apply (fastforce simp: obj_at'_def)
        apply (clarsimp simp: tcb_st_refs_of'_def tcb_bound_refs'_def
                              refs_of_rev' get_refs_def ko_wp_at'_def opt_map_def
                       split: option.splits)
       \<comment> \<open>Other thread states\<close>
       apply (all \<open>wpsimp simp: cancelSignal_def sym_refs_asrt_def wp: hoare_drop_imps\<close>)
       apply (all \<open>clarsimp simp: pred_tcb_at'_def obj_at'_def\<close>)
       apply (all \<open>drule_tac p=rptr and ko="ko :: reply" for ko in sym_refs_ko_atD'[rotated]\<close>)
             apply (fastforce simp: tcb_bound_refs'_def tcb_st_refs_of'_def refs_of_rev'
                                    get_refs_def ko_wp_at'_def obj_at'_def
                             split: option.splits
                             elim!: opt_mapE)+
  done

crunch cancelSignal, replyRemoveTCB, replyUnlink
  for ep_obj_at'[wp]: "obj_at' (P :: endpoint \<Rightarrow> bool) eptr"
  (wp: crunch_wps simp: crunch_simps)

crunch rescheduleRequired
  for scs_tcbs_of[wp]: "\<lambda>s. P (tcbSCs_of s) (scTCBs_of s)"
  (wp: crunch_wps threadSet_tcbSCs_of_inv ignore: threadSet)

lemma maybeReturnSc_sym_heap_tcbSCs[wp]:
  "\<lbrace>sym_heap_tcbSCs and valid_objs'\<rbrace>
   maybeReturnSc y t
   \<lbrace>\<lambda>_. sym_heap_tcbSCs\<rbrace>"
  unfolding maybeReturnSc_def updateSchedContext_def
  apply (simp add: liftM_def)
  apply (rule bind_wp[OF _ stateAssert_sp])
  apply (rule bind_wp[OF _ get_ntfn_sp'])
  apply (wpsimp wp: setSchedContext_scTCBs_of threadSet_tcbSCs_of | wps)+
   apply (wpsimp wp: threadGet_wp)
  apply (clarsimp simp: tcb_at'_ex_eq_all)
  apply (drule sym, simp)
  apply (subgoal_tac "(tcbSCs_of s) t = Some (the (tcbSchedContext tcb))")
   apply (clarsimp simp: sym_heap_def)
   apply (subst (asm) sym_heap_symmetric[simplified sym_heap_def], simp)
  apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def opt_map_def)
  done

lemma maybeReturnSc_sym_heap_scReplies[wp]:
  "maybeReturnSc y t \<lbrace>sym_heap_scReplies\<rbrace>"
  unfolding maybeReturnSc_def updateSchedContext_def
  apply (wpsimp wp: setSchedContext_scReplies_of threadGet_wp getNotification_wp | wps)+
  apply (erule back_subst)
  apply (rule arg_cong2[where f=sym_heap, OF _ refl], rule ext)
  apply (clarsimp simp: pred_map_eq_def pred_map_def obj_at'_real_def ko_wp_at'_def opt_map_def)
  done

crunch cleanReply
  for scTCBs_of[wp]: "\<lambda>s. P (scTCBs_of s)"
  and tcbSCs_of[wp]: "\<lambda>s. P (tcbSCs_of s)"

lemma replyRemoveTCB_scTCBs_of[wp]:
  "replyRemoveTCB tptr \<lbrace>\<lambda>s. P (scTCBs_of s)\<rbrace>"
  unfolding replyRemoveTCB_def updateSchedContext_def
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

crunch cancelIPC
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
        apply (rule_tac Q'="\<lambda>_ s. (replySCs_of s) (the (replyPrev reply)) = None \<and>
                 sym_heap (scReplies_of s) (\<lambda>a. if a = rptr then None else replySCs_of s a)"
               in hoare_strengthen_post[rotated], clarsimp)
        apply wpsimp
       apply (rule_tac Q'="\<lambda>_ s. (replyPrev reply \<noteq> None \<longrightarrow>
                reply_at' (the (replyPrev reply)) s \<longrightarrow>
                (replySCs_of s) (the (replyPrev reply)) = None) \<and>
                sym_heap (scReplies_of s) (\<lambda>a. if a = rptr then None else replySCs_of s a)"
              in hoare_strengthen_post[rotated])
        apply (clarsimp split: if_splits simp: obj_at'_def)
       apply (clarsimp simp: updateSchedContext_def)
       apply (wp hoare_vcg_if_lift2 hoare_vcg_imp_lift' hoare_vcg_all_lift)
         apply wps
         apply (wpsimp wp: setSchedContext_scReplies_of)
        apply wpsimp
       apply wp
        apply wps
        apply wpsimp
       apply wpsimp
      apply wpsimp
     apply (rule_tac Q'="\<lambda>replya s. sym_heap_scReplies s \<and> sym_refs (list_refs_of_replies' s)"
            in hoare_strengthen_post[rotated])
      apply (rename_tac rv s)
      apply (clarsimp split: if_splits)
      apply (intro conjI; intro allI impI)
       apply clarsimp
       apply (intro conjI; intro allI impI)
         apply (clarsimp simp: isHead_to_head)
         apply (intro conjI; intro allI impI)
          apply clarsimp
          apply (rename_tac replyPtr scPtr sc)
          apply (subgoal_tac "replyPrevs_of s rv = Some replyPtr")
           apply (rule replyNexts_Some_replySCs_None)
           apply (simp add: sym_refs_replyNext_replyPrev_sym[symmetric])
          apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def opt_map_def)
         apply (intro conjI; intro allI impI)
          apply clarsimp
          apply (drule ko_at'_inj, assumption, simp)
          apply (clarsimp simp: isHead_to_head)
          apply (rename_tac rPtr)
          apply (subgoal_tac "replyPrevs_of s rv = Some rPtr")
           apply (insert replyNexts_Some_replySCs_None)
           apply (simp add: sym_refs_replyNext_replyPrev_sym[symmetric])
           apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def opt_map_def)
          apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def opt_map_def)
         apply clarsimp
         apply (rename_tac replyPtr reply rPtr reply')
         apply (subgoal_tac "replyPrevs_of s rv = Some replyPtr")
          apply (rule replyNexts_Some_replySCs_None)
          apply (simp add: sym_refs_replyNext_replyPrev_sym[symmetric])
         apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def opt_map_def)
        apply (clarsimp simp: isHead_to_head)
        apply (erule sym_heap_remove_only[simplified fun_upd_def])
        apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def opt_map_def pred_map_eq)
       apply (clarsimp simp: isHead_to_head)
       apply (erule rsubst2[where P=sym_heap, OF _ refl])
       apply (rule ext, clarsimp split: if_split)
       apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def opt_map_def)
      apply (intro conjI, intro allI impI)
       apply clarsimp
       apply (rename_tac replyPtr)
       apply (subgoal_tac "replyPrevs_of s rv = Some replyPtr")
        apply (rule replyNexts_Some_replySCs_None)
        apply (simp add: sym_refs_replyNext_replyPrev_sym[symmetric])
       apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def opt_map_def)
      apply (erule rsubst2[where P=sym_heap, OF _ refl])
      apply (rule ext, clarsimp split: if_split)
      apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def opt_map_def)
     apply (wpsimp wp: hoare_drop_imp)+
  done

crunch blockedCancelIPC, cancelSignal
  for sym_heap_scReplies[wp]: sym_heap_scReplies
  (wp: crunch_wps  ignore: setSchedContext setReply updateReply)

lemma cancelIPC_sym_heap_scReplies [wp]:
  "\<lbrace>sym_heap_scReplies and (\<lambda>s. sym_refs (list_refs_of_replies' s))\<rbrace>
   cancelIPC t
   \<lbrace>\<lambda>_. sym_heap_scReplies\<rbrace>"
  unfolding cancelIPC_def
  by (wpsimp wp: gts_wp')

lemma replyTCB_is_not_ksIdleThread:
  "\<lbrakk>ko_at' reply replyPtr s; the (replyTCB reply) = ksIdleThread s; replyTCB reply = Some tcb;
    valid_idle' s; sym_refs (state_refs_of' s)\<rbrakk>
   \<Longrightarrow> False"
  apply (frule sym_ref_replyTCB_Receive_or_Reply)
    apply blast
   apply fastforce
  apply (clarsimp simp: st_tcb_at'_def obj_at_simps valid_idle'_def idle_tcb'_def)
  done

lemma refillPopHead_sym_heap_tcbSCs[wp]:
  "refillPopHead scp \<lbrace>sym_heap_tcbSCs\<rbrace>"
  unfolding refillPopHead_def
  apply (wpsimp wp: updateSchedContext_wp getRefillNext_wp)
  apply (fastforce simp: sym_heap_def obj_at'_def opt_map_def split: option.splits)
  done

lemma updateRefillHd_scTCBs_of[wp]:
  "updateRefillHd scPtr f \<lbrace>\<lambda>s. P (scTCBs_of s)\<rbrace>"
  unfolding updateRefillHd_def updateSchedContext_def
  apply (wpsimp wp: setSchedContext_scTCBs_of)
  apply (fastforce elim: back_subst[where P=P] simp: opt_map_def obj_at'_real_def ko_wp_at'_def)
  done

lemma updateRefillHd_sym_heap_tcbSCs[wp]:
  "updateRefillHd scPtr f \<lbrace>sym_heap_tcbSCs\<rbrace>"
  by (rule hoare_weaken_pre, wps, wpsimp)

crunch refillUnblockCheck
  for sym_heap_tcbSCs[wp]: sym_heap_tcbSCs
  (wp: crunch_wps)

lemma refillPopHead_sym_heap_scReplies[wp]:
  "refillPopHead scp \<lbrace>sym_heap_scReplies\<rbrace>"
  unfolding refillPopHead_def
  apply (wpsimp wp: updateSchedContext_wp getRefillNext_wp)
  apply (clarsimp simp: sym_heap_def obj_at'_def opt_map_def split: option.splits)
  done

lemma updateRefillHd_sym_heap_scReplies[wp]:
  "updateRefillHd scPtr f \<lbrace>sym_heap_scReplies\<rbrace>"
  unfolding updateRefillHd_def
  apply (wpsimp wp: updateSchedContext_wp)
  apply (clarsimp simp: sym_heap_def obj_at'_def opt_map_def split: option.splits)
  done

crunch refillUnblockCheck
  for sym_heap_scReplies[wp]: sym_heap_scReplies
  (wp: crunch_wps)

crunch ifCondRefillUnblockCheck
  for sym_heap_tcbSCs[wp]: sym_heap_tcbSCs
  and sym_heap_scReplies[wp]: sym_heap_scReplies
  and obj_at'_tcb[wp]: "\<lambda>s. Q (obj_at' (P :: tcb \<Rightarrow> bool) tcbPtr s)"
  (simp: crunch_simps wp: crunch_wps)

lemma tcbEPDequeue_invs'[wp]:
  "tcbEPDequeue t epPtr \<lbrace>invs'\<rbrace>"
  apply (simp add: invs'_def valid_pspace'_def valid_dom_schedule'_def)
  apply (wpsimp wp: valid_irq_node_lift )
  done

lemma getBoundNotification_tcb_at'[wp]:
  "getBoundNotification t \<lbrace>\<lambda>s. P (tcb_at' tcbPtr s)\<rbrace>"
  by wpsimp

(* t = ksCurThread s *)
lemma ri_invs' [wp]:
  "\<lbrace>invs' and st_tcb_at' active' t\<rbrace>
   receiveIPC t cap isBlocking replyCap
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (clarsimp simp: receiveIPC_def
                 split: if_split)
  apply (intro bind_wp[OF _ stateAssert_sp] bind_wp[OF _ assert_sp])
  apply (rule bind_wp)
   apply (rule bind_wp)
    apply (rule bind_wp)
    \<comment> \<open>After getEndpoint, the following holds regardless of the type of ep\<close>
    apply (rule_tac Q'="\<lambda>ep s. invs' s  \<and> sym_heap_tcbSCs s \<and> sym_heap_scReplies s
                               \<and> st_tcb_at' simple' t s
                               \<and> (\<forall>ptr. replyOpt = Some ptr
                                         \<longrightarrow> reply_at' ptr s \<and> replyTCBs_of s ptr = None)
                               \<and> ko_at' ep (capEPPtr cap) s"
                 in bind_wp)
     apply (rule_tac P'1="\<lambda>s. \<forall>rptr. replyOpt = Some rptr \<longrightarrow> \<not> is_reply_linked rptr s"
                  in hoare_pre_add[THEN iffD2])
      apply clarsimp
      apply (frule valid_replies'_no_tcb; clarsimp)
     apply (rename_tac ep)
     apply (case_tac "epState ep"; clarsimp)
       apply (find_goal \<open>match premises in "epState _ = IdleEPState" \<Rightarrow> -\<close>)
       apply (clarsimp simp: receiveIPCBlocked_def)
       apply (wpsimp wp: completeSignal_invs' tcbEPAppend_invs'
                         setThreadState_BlockedOnReceive_invs' maybeReturnSc_invs'
                         updateReply_replyTCB_invs' inIPCQueueThreadState_sched_flag_set
                         getNotification_wp gbn_wp' hoare_vcg_all_lift hoare_vcg_const_imp_lift
                   simp: receiveIPCBlocked_def if_fun_split
              | wp (once) hoare_false_imp)+
       apply (fastforce simp: valid_obj'_def pred_tcb_at'_def obj_at'_def)
      apply (find_goal \<open>match premises in "epState _ = ReceiveEPState" \<Rightarrow> -\<close>)
      apply (clarsimp simp: receiveIPCBlocked_def)
      apply (wpsimp wp: completeSignal_invs' tcbEPAppend_invs' setThreadState_BlockedOnReceive_invs'
                        maybeReturnSc_invs' updateReply_replyTCB_invs'
                        inIPCQueueThreadState_sched_flag_set getNotification_wp gbn_wp'
                        hoare_vcg_all_lift hoare_vcg_const_imp_lift
                  simp: receiveIPCBlocked_def if_fun_split
             | wp (once) hoare_false_imp)+
      apply (fastforce simp: valid_obj'_def pred_tcb_at'_def obj_at'_def)
     \<comment> \<open>SendEP\<close>
     apply (rule bind_wp[OF _ gbn_sp'])
     apply (wpsimp wp: replyPush_invs' completeSignal_invs' sts_invs' setThreadState_st_tcb
                       threadGet_wp)
               apply (rename_tac scOpt)
               apply (rule_tac Q'="\<lambda>_. invs' and tcb_at' t
                                       and st_tcb_at' (Not \<circ> is_replyState)
                                                      (the (tcbQueueHead (epQueue ep)))
                                       and (\<lambda>s. \<not> is_sched_linked
                                                    (the (tcbQueueHead (epQueue ep))) s)
                                       and sym_heap_tcbSCs and sym_heap_scReplies
                                       and (\<lambda>s. \<forall>ptr. replyOpt = Some ptr
                                                      \<longrightarrow> reply_at' ptr s \<and> replyTCBs_of s ptr = None)"
                            in hoare_post_imp)
                apply (clarsimp simp: pred_tcb_at'_eq_commute)
                apply (fastforce simp: pred_tcb_at'_def obj_at'_real_def ko_wp_at'_def
                                       is_BlockedOnReply_def is_BlockedOnReceive_def)
               apply (wpsimp wp: ifCondRefillUnblockCheck_invs' hoare_vcg_all_lift
                                 hoare_vcg_imp_lift')
              apply (rule_tac Q'="\<lambda>_. invs' and tcb_at' t
                                      and st_tcb_at' (Not \<circ> is_replyState)
                                                     (the (tcbQueueHead (epQueue ep)))
                                      and (\<lambda>s. \<not> is_sched_linked
                                                   (the (tcbQueueHead (epQueue ep))) s)
                                      and sym_heap_tcbSCs and sym_heap_scReplies
                                      and (\<lambda>s. \<forall>ptr. replyOpt = Some ptr
                                                     \<longrightarrow> reply_at' ptr s \<and> replyTCBs_of s ptr = None)"
                           in hoare_post_imp)
               apply (clarsimp simp: o_def invs_valid_objs')
              apply (wpsimp wp: hoare_vcg_imp_lift' maybeReturnSc_invs'
                                hoare_vcg_all_lift getNotification_wp gbn_wp'
                                stateAssert_inv
                     | drule Some_to_the)+
     apply (clarsimp simp: st_tcb_at'_def obj_at'_def)
     subgoal
       by (intro conjI impI allI;
           force simp: is_BlockedOnReply_def is_BlockedOnReceive_def isSend_def
                split: thread_state.splits)
    \<comment> \<open>Resolve common precondition\<close>
    apply (simp (no_asm_use) cong: conj_cong
           | wpsimp wp: cancelIPC_st_tcb_at'_different_thread
                        cancelIPC_replyTCBs_of_None hoare_vcg_all_lift getEndpoint_wp
                        hoare_drop_imp[where Q'="\<lambda>_ s. \<exists>ko. ko_at' ko _ s"] hoare_vcg_imp_lift')+
  apply (rename_tac s)
  apply (clarsimp simp: comp_def invs'_def valid_pspace'_def if_distribR
                  cong: conj_cong imp_cong)
  apply (frule (3) sym_refs_tcbSCs)
  apply (frule (3) sym_refs_scReplies)
  apply (prop_tac "\<forall>r g. replyCap = ReplyCap r g \<longrightarrow> \<not>obj_at' (\<lambda>a. replyTCB a = Some t) r s")
   apply (clarsimp simp: pred_tcb_at'_def obj_at'_def)
   apply (drule_tac ko="ko :: reply" for ko in sym_refs_ko_atD'[rotated])
    apply (fastforce simp: obj_at'_def)
   apply (fastforce simp: refs_of_rev' ko_wp_at'_def tcb_bound_refs'_def get_refs_def
                   split: option.splits)
  apply (prop_tac "st_tcb_at' simple' t s ")
   apply (fastforce simp: pred_tcb_at'_def obj_at'_def)
  apply (fastforce simp: opt_map_def obj_at'_def)
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
  "\<lbrace>\<lambda>s. invs' s \<and> (replyTCBs_of s replyPtr = Some tcbPtr \<longrightarrow> \<not> is_reply_linked replyPtr s)
        \<and> \<not> is_sched_linked tcbPtr s\<rbrace>
   replyUnlink replyPtr tcbPtr
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  unfolding invs'_def valid_dom_schedule'_def
  by (wpsimp wp: replyUnlink_valid_sched_pointers)

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

crunch doIPCTransfer
  for pred_tcb_at''[wp]: "\<lambda>s. P (pred_tcb_at' proj test t s)"
  (wp: setCTE_pred_tcb_at' getCTE_wp mapM_wp' simp: cte_wp_at'_def zipWithM_x_mapM)

lemma si_invs'_helper:
  "\<lbrace>\<lambda>s. invs' s \<and> st_tcb_at' runnable' t s
        \<and> st_tcb_at' (Not \<circ> is_BlockedOnReply) d s
        \<and> \<not> (tcbQueued |< tcbs_of' s) d \<and> \<not> (tcbInReleaseQueue |< tcbs_of' s) d
        \<and> \<not> is_sched_linked d s \<and> sch_act_not d s
        \<and> sym_heap_tcbSCs s \<and> sym_heap_scReplies s
        \<and> (cd \<and> scOptDest = Nothing
           \<longrightarrow> bound_sc_tcb_at' ((=) None) d s
               \<and> (\<exists>scptr. bound_sc_tcb_at' (\<lambda>scp. scp = (Some scptr)) t s))
        \<and> t \<noteq> d\<rbrace>
   if call \<or> (\<exists>y. fault = Some y)
   then if (cg \<or> cgr) \<and> (\<exists>y. replyObject recvState = Some y)
        then replyPush t d (the (replyObject recvState)) cd
        else setThreadState Structures_H.thread_state.Inactive t
   else when (cd \<and> scOptDest = None) (do
          scOptSrc \<leftarrow> threadGet tcbSchedContext t;
          y \<leftarrow> assert (\<exists>y. scOptSrc = Some y);
          schedContextDonate (the scOptSrc) d
        od)
  \<lbrace>\<lambda>_ s. invs' s
         \<and> st_tcb_at' (Not \<circ> is_BlockedOnReply) d s
         \<and> \<not> is_sched_linked d s\<rbrace>"
  apply (wpsimp wp: schedContextDonate_invs' replyPush_invs' sts_invs_minor'
                    replyPush_st_tcb_at'_not_caller sts_st_tcb'
                    schedContextDonate_tcbSchedPrevs_of_None
                    schedContextDonate_tcbSchedNexts_of_None threadGet_wp)
  apply (frule_tac P'="(\<lambda>st'. \<forall>rptr. st' \<noteq> BlockedOnReply rptr)" in pred_tcb'_weakenE)
   apply (clarsimp simp: is_BlockedOnReply_def)
  apply (frule pred_tcb_at')
  apply (frule_tac t=d in pred_tcb_at')
  apply (frule_tac P'="Not \<circ> is_replyState" in pred_tcb'_weakenE)
   apply (fastforce simp: is_BlockedOnReply_def is_BlockedOnReceive_def)
  apply (frule invs_valid_objs')
  apply (clarsimp simp: tcb_at'_ex_eq_all o_def)
  apply normalise_obj_at'
  apply (clarsimp simp: pred_tcb_at'_def obj_at'_real_def ko_wp_at'_def)
  apply (rename_tac tcb tcb', case_tac "tcbState tcb"; clarsimp)
  done

lemma replyUnlink_obj_at_tcb_none:
  "\<lbrace>K (rptr' = rptr)\<rbrace>
   replyUnlink rptr tptr
   \<lbrace>\<lambda>_. obj_at' (\<lambda>reply. replyTCB reply = None) rptr'\<rbrace>"
  apply (simp add: replyUnlink_def)
  apply (wpsimp wp: updateReply_wp_all gts_wp')
  by (auto simp: obj_at'_def objBitsKO_def)

lemma si_invs'[wp]:
  "\<lbrace>invs' and st_tcb_at' runnable' t and (\<lambda>s. cd \<longrightarrow> bound_sc_tcb_at' (\<lambda>a. a \<noteq> None) t s)\<rbrace>
   sendIPC bl call ba cg cgr cd t ep
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  supply if_split[split del]
  apply (simp add: sendIPC_def)
  apply (intro bind_wp[OF _ stateAssert_sp])
  apply (rule bind_wp [OF _ get_ep_sp'])
  apply (rename_tac ep')
  apply (case_tac "epState ep'"; clarsimp)
    apply (find_goal \<open>match premises in "epState _ = IdleEPState" \<Rightarrow> -\<close>)
    apply (wpsimp wp: tcbEPAppend_invs' setThreadState_nonqueued_state_update
                      inIPCQueueThreadState_sched_flag_set)
    apply (rule conjI)
     apply (erule pred_tcb'_weakenE)
     apply (rename_tac st, case_tac st; clarsimp)
    apply fastforce
   apply (find_goal \<open>match premises in "epState _ = SendEPState" \<Rightarrow> -\<close>)
   apply (wpsimp wp: tcbEPAppend_invs' setThreadState_nonqueued_state_update
                     inIPCQueueThreadState_sched_flag_set)
   apply (rule conjI)
    apply (erule pred_tcb'_weakenE)
    apply (rename_tac st, case_tac st; clarsimp)
   apply fastforce
  \<comment> \<open>ep' = RecvEP\<close>
  apply (rule bind_wp[OF _ stateAssert_sp])
  apply (rule bind_wp[OF _ assert_sp])
  apply (rule hoare_gen_asm_conj)
  apply (clarsimp simp: tcbQueueEmpty_def)
  apply (rename_tac q dest)
  apply (wpsimp wp: setThreadState_Running_invs' replyPush_invs' replyPush_st_tcb_at'_not_caller
                    setThreadState_nonqueued_state_update[where t=t] sts_st_tcb'
                    schedContextDonate_invs' schedContextDonate_tcbSchedPrevs_of_None
                    schedContextDonate_tcbSchedNexts_of_None threadGet_wp)
               apply (rule hoare_drop_imp)
               apply (wpsimp wp: setThreadState_Running_invs')
              apply (wpsimp wp: si_invs'_helper)
             apply wpsimp
            apply (wpsimp wp: threadGet_wp)
           apply (rule_tac Q'="\<lambda>_ s. invs' s \<and> st_tcb_at' runnable' t s
                                     \<and> st_tcb_at' (Not \<circ> is_BlockedOnReply) dest s
                                     \<and> \<not> (tcbQueued |< tcbs_of' s) dest
                                     \<and> \<not> (tcbInReleaseQueue |< tcbs_of' s) dest
                                     \<and> \<not> is_sched_linked dest s \<and> sch_act_not dest s
                                     \<and> sym_heap_tcbSCs s \<and> sym_heap_scReplies s
                                     \<and> (cd \<longrightarrow> (\<exists>scptr. bound_sc_tcb_at' (\<lambda>scp. scp = Some scptr) t s))
                                     \<and> t \<noteq> dest"
                        in hoare_post_imp)
            apply (fastforce simp: obj_at'_def pred_tcb_at'_def)
           apply (wpsimp wp: replyUnlink_invs' replyUnlink_st_tcb_at' replyUnlink_obj_at_tcb_none
                             hoare_vcg_ex_lift hoare_vcg_imp_lift')
          apply (rule_tac Q'="\<lambda>_ s. invs' s \<and> st_tcb_at' runnable' t s
                                    \<and> st_tcb_at' is_BlockedOnReceive dest s
                                    \<and> dest \<noteq> t
                                    \<and> \<not> (tcbQueued |< tcbs_of' s) dest
                                    \<and> \<not> (tcbInReleaseQueue |< tcbs_of' s) dest
                                    \<and> \<not> is_sched_linked dest s \<and> sch_act_not dest s
                                    \<and> sym_heap_tcbSCs s \<and> sym_heap_scReplies s
                                    \<and> (\<forall>ptr. replyObject recvState = Some ptr
                                             \<longrightarrow> (replyTCBs_of s ptr = Some dest
                                                  \<longrightarrow> \<not> is_reply_linked ptr s))
                                    \<and> (cd \<longrightarrow> (\<exists>scptr. bound_sc_tcb_at' (\<lambda>scp. scp = Some scptr) t s))"
                       in hoare_post_imp)
           apply (force simp: obj_at'_def pred_tcb_at'_def invs'_def
                              is_BlockedOnReceive_def is_BlockedOnReply_def)
          apply (wpsimp simp: invs'_def valid_dom_schedule'_def valid_pspace'_def
                          wp: hoare_vcg_all_lift hoare_vcg_ex_lift hoare_vcg_imp_lift' gts_wp')+
  apply (intro conjI; (solves clarsimp)?)
      apply (erule pred_tcb'_weakenE)
      apply (rename_tac st, case_tac st; clarsimp simp: is_BlockedOnReceive_def isReceive_def)
     apply (erule (3) sym_refs_tcbSCs)
    apply (erule (3) sym_refs_scReplies)
   apply clarsimp
   apply (drule (1) valid_replies'_other_state; clarsimp simp: isReceive_def)
  apply (clarsimp simp: pred_tcb_at'_def obj_at'_def)
  done

lemma sendFaultIPC_invs':
  "\<lbrace>invs' and st_tcb_at' runnable' t and (\<lambda>s. canDonate \<longrightarrow> bound_sc_tcb_at' (\<lambda>a. a \<noteq> None) t s)\<rbrace>
   sendFaultIPC t cap f canDonate
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  unfolding sendFaultIPC_def
  by (wpsimp wp: threadSet_invs_trivial threadSet_pred_tcb_no_state threadSet_cap_to')

lemma handleFault_corres:
  "fr f f' \<Longrightarrow>
   corres dc
     (invs and valid_list and valid_sched_action and active_scs_valid
      and valid_release_q and valid_ready_qs and ready_or_release
      and sorted_ipc_queues and scheduler_act_not t
      and st_tcb_at runnable t and not_queued t and not_in_release_q t and current_time_bounded
      and ex_nonz_cap_to t and K (valid_fault f))
     invs'
     (handle_fault t f) (handleFault t f')"
  apply (rule_tac Q'="st_tcb_at' runnable' t" in corres_cross_add_guard)
   apply (fastforce intro: st_tcb_at_runnable_cross)
  apply add_valid_idle'
  apply (simp add: handle_fault_def handleFault_def)
  apply (rule corres_stateAssert_add_assertion[rotated], simp)
  apply (rule corres_gen_asm)
  apply (rule corres_guard_imp)
    apply (simp add: getThreadFaultHandlerSlot_def locateSlot_conv)
    apply (rule corres_split[OF getSlotCap_corres])
       apply (simp add: cte_map_def tcb_cnode_index_def cte_level_bits_def
                        get_tcb_fault_handler_ptr_def tcbFaultHandlerSlot_def)
      apply (rule corres_split[OF threadGet_corres, where r'="(=)"])
         apply (clarsimp simp: tcb_relation_def)
        apply clarsimp
        apply (rule corres_split[OF sendFaultIPC_corres])
            apply (fastforce simp: tcb_relation_def)+
          apply (clarsimp simp: handle_no_fault_def handleNoFaultHandler_def unless_def when_def)
          apply (rule setThreadState_corres, simp)
         apply (rule_tac Q'="\<lambda>_ s. invs s \<and> tcb_at t s" in hoare_strengthen_post[rotated])
          apply (clarsimp simp: invs_def valid_state_def valid_pspace_def)
         apply wp
        apply ((wpsimp wp: sendFaultIPC_invs'
                | strengthen invs'_implies valid_objs'_valid_tcbs')+)[1]
       apply (wp gbn_inv get_tcb_obj_ref_wp thread_get_wp)
      apply (wp hoare_vcg_imp_lift' threadGet_wp)
     apply (wp get_cap_wp)
    apply (wp getObject_tcb_wp hoare_vcg_all_lift hoare_drop_imps hoare_vcg_bex_lift
              hoare_vcg_ex_lift getSlotCap_wp)+
   apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb_def get_tcb_def
                         get_tcb_fault_handler_ptr_def cong: conj_cong)
   apply (intro conjI; fastforce?)
    apply (fastforce dest!: get_tcb_SomeD
                      simp: is_timeout_fault_def valid_fault_def cte_wp_at_cases
                            get_tcb_timeout_handler_ptr_def)
   apply clarsimp
   apply (intro conjI impI allI; fastforce?)
      apply (fastforce elim: cte_wp_valid_cap)
     apply (fastforce dest: tcb_ep_slot_cte_wp_ats[where t=t]
                      simp: tcb_at_def get_tcb_def cte_wp_at_cases)
    apply (fastforce simp: runnable_eq_active)
   apply (fastforce simp: caps_of_state_Some_simp)
  apply clarsimp
  apply (intro conjI impI allI; fastforce?)
  apply (clarsimp simp: pred_tcb_at'_def)
  apply normalise_obj_at'
  apply (fastforce dest: cap_in_tcbFaultHandlerSlot)
  done

lemma isValidTimeoutHandler_corres:
  "corres (=) (tcb_at t and pspace_aligned and pspace_distinct) valid_tcbs'
     (is_valid_timeout_handler t) (isValidTimeoutHandler t)"
  apply (rule corres_cross_add_guard[where Q'="tcb_at' t"])
   apply (fastforce intro: tcb_at_cross)
  apply (rule_tac Q'="pspace_aligned'" in corres_cross_add_guard)
   apply (fastforce dest!: pspace_aligned_cross)
  apply (rule_tac Q'="pspace_distinct'" in corres_cross_add_guard)
   apply (fastforce dest!: pspace_distinct_cross)
  apply (clarsimp simp: is_valid_timeout_handler_def get_tcb_timeout_handler_ptr_def
                        isValidTimeoutHandler_def)
  apply (rule corres_stateAssert_add_assertion[rotated])
   apply fastforce
  apply (simp add: getThreadTimeoutHandlerSlot_def locateSlot_conv)
  apply (rule stronger_corres_guard_imp)
    apply (rule corres_split[OF getSlotCap_corres, where R="\<top>\<top>" and R'="\<top>\<top>"])
       apply (simp add: cte_map_def tcb_cnode_index_def cte_level_bits_def tcbTimeoutHandlerSlot_def)
      apply (case_tac rv; case_tac rv'; clarsimp)
     apply (wpsimp wp: get_cap_wp)
    apply (wpsimp wp: getSlotCap_wp)
   apply (fastforce intro: tcb_at_cte_at_4)
  apply normalise_obj_at'
  apply (fastforce dest: cap_in_tcbTimeoutHandlerSlot)
  done

lemma handleTimeout_corres:
  "fr f f' \<Longrightarrow>
   corres dc
     (invs and valid_list and valid_sched_action and active_scs_valid
      and valid_release_q and valid_ready_qs and ready_or_release
      and sorted_ipc_queues and scheduler_act_not t
      and st_tcb_at runnable t and not_queued t and not_in_release_q t and current_time_bounded
      and cte_wp_at is_ep_cap (t,tcb_cnode_index 4) and K (valid_fault f))
     invs'
     (handle_timeout t f) (handleTimeout t f')"
  apply add_valid_idle'
  apply (rule corres_cross_add_guard[where Q'="tcb_at' t"])
   apply (fastforce intro: tcb_at_cross)
  apply (clarsimp simp: handle_timeout_def handleTimeout_def getThreadTimeoutHandlerSlot_def)
  apply (rule corres_stateAssert_add_assertion[rotated], simp)
  apply (rule corres_stateAssert_add_assertion[rotated])
   apply (fastforce intro!: st_tcb_at_runnable_cross
                 simp flip: runnable_eq_active' simp: runnable_eq_active)
  apply (rule corres_stateAssert_add_assertion[rotated], clarsimp)
  apply (rule corres_gen_asm)
  apply (rule stronger_corres_guard_imp)
    apply (rule corres_split[OF isValidTimeoutHandler_corres])
      apply (rule corres_split[OF corres_assert])
        apply (simp add: getThreadTimeoutHandlerSlot_def locateSlot_conv)
        apply (rule corres_split[OF getSlotCap_corres])
           apply (simp add: cte_map_def tcb_cnode_index_def cte_level_bits_def
                            get_tcb_timeout_handler_ptr_def tcbTimeoutHandlerSlot_def)
          apply (rule corres_split[OF sendFaultIPC_corres])
              apply fastforce
             apply (fastforce simp: tcb_relation_def)
            apply (rule corres_trivial, clarsimp)
           apply (wp getTCB_wp)+
         apply (wpsimp wp: get_cap_wp getSlotCap_wp
                     simp: is_valid_timeout_handler_def isValidTimeoutHandler_def
                           getThreadTimeoutHandlerSlot_def locateSlot_conv)+
   apply (fastforce dest: tcb_ep_slot_cte_wp_ats[where t=t]
                    simp: cte_wp_at_cases get_tcb_timeout_handler_ptr_def)
  apply normalise_obj_at'
  apply (frule cap_in_tcbTimeoutHandlerSlot)
  apply fastforce
  apply (frule cte_wp_at_norm)
  apply (frule state_relation_pspace_relation)
  apply (fastforce dest!: pspace_relation_cte_wp_at
                    simp: cte_wp_at'_def cap_relation_def is_cap_simps cte_map_def
                          tcb_cnode_index_def shiftl_t2n tcbTimeoutHandlerSlot_def)
  done

lemma hf_invs'[wp]:
  "\<lbrace>invs' and st_tcb_at' runnable' t\<rbrace>
   handleFault t f
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: handleFault_def handleNoFaultHandler_def sendFaultIPC_def)
  apply (rule bind_wp[OF _ stateAssert_sp])
  apply (wpsimp wp: sts_invs_minor' threadSet_invs_trivialT threadSet_pred_tcb_no_state getTCB_wp
                    threadGet_wp hoare_vcg_all_lift hoare_vcg_imp_lift' getSlotCap_wp
              simp: getThreadFaultHandlerSlot_def locateSlot_conv
         | fastforce simp: tcb_cte_cases_def cteSizeBits_def)+
   apply (clarsimp simp: pred_tcb_at'_def)
  apply normalise_obj_at'
  apply (frule cap_in_tcbFaultHandlerSlot)
   apply fastforce
  apply (clarsimp cong: conj_cong)
  apply (rename_tac cap n get set)
  apply (intro conjI impI allI; clarsimp?)
   apply fastforce
  apply (rename_tac tcb cap n get set)
  apply (case_tac "tcbState tcb"; clarsimp)
  done

lemma gts_st_tcb':
  "\<lbrace>\<top>\<rbrace> getThreadState t \<lbrace>\<lambda>r. st_tcb_at' (\<lambda>st. st = r) t\<rbrace>"
  apply (rule hoare_strengthen_post)
  apply (rule gts_sp')
  apply simp
  done

crunch replyRemove
  for ksSchedulerAction[wp]: "\<lambda>s. P (ksSchedulerAction s)"
  (simp: crunch_simps wp: crunch_wps wp_comb: hoare_weaken_pre)

crunch getSanitiseRegisterInfo
 for inv[wp]: P

lemma handleFaultReply_invs[wp]:
  "\<lbrace>invs' and tcb_at' t\<rbrace> handleFaultReply x t label msg \<lbrace>\<lambda>rv. invs'\<rbrace>"
  unfolding handleFaultReply_def
  by (cases x; wpsimp simp: handleArchFaultReply_def split: arch_fault.split)

lemma doReplyTransfer_corres:
  "corres dc
     (einvs and reply_at reply and tcb_at sender and current_time_bounded)
     invs'
     (do_reply_transfer sender reply grant)
     (doReplyTransfer sender reply grant)"
  apply add_cur_tcb'
  apply add_sym_refs
  supply if_split [split del] subst_all[simp del] opt_mapE[elim!]
  apply (simp add: do_reply_transfer_def doReplyTransfer_def cong: option.case_cong)
  apply (rule corres_stateAssert_ignore, solves clarsimp)+
  apply (rule corres_stateAssert_ignore)
   apply (fastforce intro: weak_sch_act_wf_cross)
  apply (rule stronger_corres_guard_imp)
    apply (rule corres_split [OF getReply_TCB_corres])
      apply (simp add: maybeM_def)
      apply (rule corres_option_split [OF refl corres_return_trivial])
      apply (rename_tac recv_opt receiverOpt recvr)
      apply (rule_tac Q="\<lambda>s. einvs s \<and> tcb_at sender s \<and> tcb_at recvr s \<and> current_time_bounded s \<and>
                             reply_tcb_reply_at (\<lambda>xa. xa = Some recvr) reply s" and
                      Q'=invs'
             in corres_split [OF _ _ gts_sp gts_sp' ])
       apply (rule getThreadState_corres, simp, rename_tac ts ts')
      apply (case_tac ts; simp add: isReply_def)
      apply (rule stronger_corres_guard_imp)
        apply (rule corres_assert_assume_l)
        apply (rule corres_split [OF replyRemove_corres], (rule refl)+)
          apply (rule corres_split_eqr[OF get_tcb_obj_ref_corres])
             apply (clarsimp simp: tcb_relation_def)
            apply (rule corres_split [OF ifCondRefillUnblockCheck_corres])
              apply (rule corres_split [OF threadget_fault_corres])
                apply (rule corres_split)
                   apply (rule_tac P="tcb_at sender and tcb_at recvr and valid_objs and pspace_aligned and
                                      valid_list and pspace_distinct and valid_mdb and cur_tcb
                                      and current_time_bounded and valid_arch_state" and
                                   P'="tcb_at' sender and tcb_at' recvr and valid_pspace' and
                                       sym_heap_sched_pointers"
                          in corres_guard_imp)
                     apply (simp add: fault_rel_optionation_def)
                     apply (rule corres_option_split; simp)
                      apply (rule corres_split [OF doIPCTransfer_corres setThreadState_corres])
                        apply (clarsimp simp: thread_state_relation_def)
                       prefer 3
                       apply (rule corres_split_mapr[OF getMessageInfo_corres])
                         apply (rule corres_split_eqr[OF lookupIPCBuffer_corres'])
                           apply (rule corres_split_eqr[OF getMRs_corres], simp)
                             apply (simp (no_asm) del: dc_simp)
                             apply (rule corres_split_eqr[OF handleFaultReply_corres])
                                apply simp
                               apply (rule corres_split [OF threadset_corresT setThreadState_corres])
                                        apply (clarsimp simp: tcb_relation_def fault_rel_optionation_def)
                                       apply (clarsimp simp: tcb_cap_cases_def)
                                      apply (clarsimp simp: tcb_cte_cases_def cteSizeBits_def)
                                     apply fastforce
                                    apply fastforce
                                   apply (fastforce simp: inQ_def)
                                  apply fastforce
                                 apply (clarsimp simp: thread_state_relation_def split: if_split)
                                (* solving hoare_triples *)
                                apply (clarsimp simp: valid_tcb_state_def)
                                apply (rule_tac Q'="\<lambda>_. valid_objs and pspace_aligned and
                                                       pspace_distinct and tcb_at recvr
                                                       and current_time_bounded" in
                                        hoare_strengthen_post[rotated])
                                 apply (clarsimp simp: valid_objs_valid_tcbs)
                                apply (wpsimp wp: thread_set_fault_valid_objs)
                               apply (wpsimp wp: threadSet_valid_tcbs')
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
                  apply (clarsimp simp: isRunnable_def readRunnable_def get_tcb_obj_ref_def
                             simp flip: getThreadState_def threadGet_def)
                  (* solve remaining corres goals *)
                  apply (rule corres_split [OF threadGet_corres[where r="(=)"]])
                     apply (simp add: tcb_relation_def)
                    apply (rule corres_split [OF getThreadState_corres])
                      apply (rename_tac scopt scopt' state state')
                      apply (rule corres_when)
                       apply (case_tac state; simp add: thread_state_relation_def)
                      apply (rule corres_assert_opt_assume_l)
                      apply (rule_tac Q="valid_sched_action and tcb_at recvr
                                         and sc_tcb_sc_at (\<lambda>a. a \<noteq> None) (the scopt) and
                                         active_sc_at (the scopt) and valid_refills (the scopt) and
                                         valid_release_q and active_scs_valid and sorted_ipc_queues and
                                         (\<lambda>s. sc_tcb_sc_at (\<lambda>tcb_ptr_opt.
                                                             tcb_ptr_opt = Some recvr
                                                             \<and> not_queued recvr s
                                                             \<and> not_in_release_q recvr s
                                                             \<and> pred_map runnable (tcb_sts_of s) recvr)
                                                           (the scopt) s) and
                                         invs and valid_list and scheduler_act_not recvr
                                         and current_time_bounded and st_tcb_at active recvr
                                         and valid_ready_qs and ready_or_release"
                                  and Q'="invs' and tcb_at' recvr and active_sc_at' (the scopt')"
                                  and P'="invs' and tcb_at' recvr"
                                  and P="valid_sched_action and tcb_at recvr and current_time_bounded and
                                         sc_tcb_sc_at (\<lambda>a. a \<noteq> None) (the scopt) and
                                         active_sc_at (the scopt) and valid_refills (the scopt) and
                                         valid_release_q and active_scs_valid and sorted_ipc_queues and
                                         (\<lambda>s. sc_tcb_sc_at (\<lambda>tcb_ptr_opt.
                                                             tcb_ptr_opt = Some recvr
                                                             \<and> not_queued recvr s
                                                             \<and> not_in_release_q recvr s
                                                             \<and> pred_map runnable (tcb_sts_of s) recvr)
                                                           (the scopt) s) and
                                         invs and valid_list and scheduler_act_not recvr and st_tcb_at active recvr
                                         and valid_ready_qs and ready_or_release"
                             in stronger_corres_guard_imp)

                        (* this next section by somewhat complicated symbolic executions *)
                        apply (rule corres_symb_exec_l [OF _ _ get_sched_context_sp], rename_tac sc)
                          apply (rule corres_symb_exec_l [OF _ _ gets_sp], rename_tac ct)
                            apply (rule corres_symb_exec_r [OF _ refillReady_sp], rename_tac ready)
                              apply (rule corres_symb_exec_r [OF _ refillSufficient_sp], rename_tac suff)
                                apply (rule_tac Q'="\<lambda>_. ready = refill_ready ct (refill_hd sc)
                                                        \<and> suff = refill_sufficient 0 (refill_hd sc)"
                                             in corres_cross_add_guard[rotated])
                                 apply (rule_tac corres_gen_asm2)
                                 apply (rule stronger_corres_guard_imp)
                                   apply (rule corres_if, simp)
                                    apply (rule possibleSwitchTo_corres; (solves simp)?)
                                   apply (rule corres_symb_exec_r[OF _ get_sc_sp'], rename_tac sc')
                                     apply (rule_tac Q'="\<lambda>_. sc_badge sc = scBadge sc'" in corres_cross_add_guard[rotated])
                                      apply (rule_tac corres_gen_asm2)
                                      apply (rule_tac Q="\<lambda>s. active_scs_valid s \<and>
                                               is_active_sc (the scopt') s \<and> current_time_bounded s \<and>
                                               (\<lambda>s. sc_tcb_sc_at (\<lambda>tcb_ptr_opt.
                                                             tcb_ptr_opt = Some recvr
                                                             \<and> not_queued recvr s
                                                             \<and> not_in_release_q recvr s
                                                             \<and> pred_map runnable (tcb_sts_of s) recvr)
                                                           (the scopt) s) s \<and>
                                               invs s \<and> valid_release_q s \<and> tcb_at recvr s \<and>
                                               valid_list s \<and> valid_sched_action s \<and> sorted_ipc_queues s \<and>
                                               scheduler_act_not recvr s \<and> st_tcb_at active recvr s \<and>
                                               valid_ready_qs s \<and> ready_or_release s"
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
                                                apply (clarsimp simp: invs'_def valid_pspace'_def)
                                                apply (auto simp: is_timeout_fault_def fault_map_def split: ExceptionTypes_A.fault.splits)[1]

                                               (* solve final hoare triple goals *)
                                               apply wpsimp
                                              apply wpsimp
                                             apply (wpsimp wp: hoare_drop_imp
                                                         simp: isValidTimeoutHandler_def
                                                               getThreadTimeoutHandlerSlot_def)
                                            apply (wpsimp simp: isValidTimeoutHandler_def
                                                                getThreadTimeoutHandlerSlot_def
                                                                locateSlot_conv
                                                            wp: no_fail_stateAssert)
                                            apply normalise_obj_at'
                                            apply (fastforce dest: cap_in_tcbTimeoutHandlerSlot
                                                            elim!: cte_wp_at_weakenE')
                                           apply (clarsimp split: if_split simp: valid_fault_def invs_def valid_state_def valid_pspace_def)
                                           apply (frule valid_ready_qs_in_correct_ready_q)
                                           apply (frule valid_ready_qs_ready_qs_distinct)
                                           apply (fastforce simp: tcb_cnode_map_def obj_at_def TCB_cte_wp_at_obj_at sc_at_pred_n_def pred_tcb_at_def)
                                          apply (clarsimp simp: obj_at_def)
                                          apply (frule (1) pspace_relation_absD[OF _ state_relation_pspace_relation])
                                          apply (clarsimp simp: tcb_relation_cut_def obj_at'_def
                                                                tcb_relation_def)
                                          apply (case_tac "cteCap (tcbTimeoutHandler ko)";
                                                 case_tac "tcb_timeout_handler tcb"; simp)
                                         apply (wpsimp simp: tcb_at_def)
                                        apply (wpsimp simp: tcb_at_def)
                                       apply (assumption)
                                      apply clarsimp
                                      apply (subgoal_tac "invs' s \<and> tcb_at' recvr s
                                                          \<and> obj_at' (\<lambda>sc'. sc_badge sc = scBadge sc') (the scopt') s")
                                       apply (clarsimp simp: obj_at'_def)
                                      apply (assumption)
                                     apply (clarsimp simp: obj_at'_def)
                                    apply wpsimp
                                   apply wpsimp

                                  apply (clarsimp simp: invs_def valid_state_def valid_pspace_def active_sc_at_equiv
                                                 split: if_split)
                                  apply (frule valid_objs_valid_tcbs)
                                  apply (frule valid_ready_qs_in_correct_ready_q)
                                  apply (frule valid_ready_qs_ready_queues_runnable)
                                  apply (fastforce simp: obj_at_def sc_at_pred_n_def
                                                         obj_at_kh_kheap_simps)
                                 apply (clarsimp simp: invs_def valid_state_def valid_pspace_def invs'_def
                                                       valid_pspace'_def
                                                split: if_split)
                                 apply (frule (1) valid_objs_ko_at, clarsimp simp: valid_obj_def)
                                 apply (clarsimp simp: obj_at_def)
                                 apply (frule (1) pspace_relation_absD[OF _ state_relation_pspace_relation])
                                 apply (prop_tac "sc_at' (the scopt') s'")
                                  apply (fastforce intro!: sc_at_cross intro: sc_at_pred_n_sc_at)
                                 apply (clarsimp simp: obj_at'_def sc_relation_def)
                                apply (clarsimp simp: invs_def valid_state_def valid_pspace_def invs'_def valid_pspace'_def)
                                apply (frule (1) valid_objs_ko_at, clarsimp simp: valid_obj_def)
                                apply (rename_tac sc' n)
                                apply (prop_tac "sc_relation sc n sc'")
                                 apply (clarsimp simp: obj_at_def)
                                 apply (frule (1) pspace_relation_absD[OF _ state_relation_pspace_relation])
                                 apply (clarsimp simp: obj_at'_def split: if_splits)
                                apply (frule (1) ksPSpace_valid_sched_context')
                                apply (subgoal_tac "0 < scRefillMax sc'")
                                 apply (subgoal_tac "sc_valid_refills sc")
                                  apply (subgoal_tac "sc_valid_refills' sc'")
                                   apply (simp add: refill_ready_relation refill_sufficient_relation
                                                    state_relation_def active_sc_at_equiv)
                                  apply (metis valid_sched_context'_def)
                                 apply (subst (asm) active_sc_at_equiv)
                                 apply (frule (1) active_scs_validE)
                                 apply (clarsimp simp: valid_refills_def2 obj_at_def)
                                apply (fastforce simp: obj_at_def vs_all_heap_simps active_sc_def
                                                       sc_relation_def)
                               apply wpsimp
                              apply wpsimp
                             apply (wpsimp wp: refillReady_wp)
                            apply (simp add: refillReady_def, rule no_ofail_gets_the)
                            apply wpsimp
                           apply wpsimp
                          apply (clarsimp simp: obj_at_def sc_at_pred_n_def get_sched_context_exs_valid)
                         apply (rule get_sched_context_exs_valid)
                         apply (clarsimp simp: sc_at_pred_n_def obj_at_def)
                        apply ((wpsimp simp: obj_at_def is_sc_obj_def
                               | clarsimp split: Structures_A.kernel_object.splits)+)[1]
                       apply simp
                      apply clarsimp
                      apply (erule active_sc_at'_cross)
                         apply fastforce
                        apply fastforce
                       apply (fastforce simp: obj_at_kh_kheap_simps)
                      apply (fastforce simp: vs_all_heap_simps obj_at_kh_kheap_simps is_sc_obj_def
                                     intro!: valid_sched_context_size_objsI)
                     apply (wpsimp wp: gts_wp)
                    apply (wpsimp wp: gts_wp')
                   apply (wpsimp wp: thread_get_wp')
                  apply (wpsimp wp: threadGet_wp)
                 apply (rule_tac Q'="\<lambda>_. tcb_at recvr and valid_sched_action and invs and valid_list
                                        and valid_release_q and valid_ready_qs and scheduler_act_not recvr
                                        and active_scs_valid and current_time_bounded
                                        and active_if_bound_sc_tcb_at recvr and ready_or_release
                                        and sorted_ipc_queues
                                        and not_queued recvr and not_in_release_q recvr"
                        in hoare_strengthen_post[rotated])
                  apply (clarsimp simp del: comp_apply)
                  apply (frule invs_psp_aligned, frule invs_distinct)
                  apply (clarsimp simp: obj_at_def is_tcb)
                  apply (subgoal_tac "pred_map (\<lambda>a. a = Some y) (tcb_scps_of s) recvr")
                   apply (subgoal_tac "pred_map (\<lambda>a. a = Some recvr) (sc_tcbs_of s) y")
                    apply (intro conjI)
                        apply (clarsimp simp: vs_all_heap_simps sc_at_kh_simps)
                       apply (clarsimp simp: vs_all_heap_simps)
                      apply (erule active_scs_validE[rotated], clarsimp simp: vs_all_heap_simps)
                     apply (clarsimp simp: pred_tcb_at_def obj_at_def vs_all_heap_simps sc_at_kh_simps)
                    apply (clarsimp simp: vs_all_heap_simps pred_tcb_at_def obj_at_def runnable_eq)
                   apply (simp add: sc_at_kh_simps pred_map_eq_normalise heap_refs_inv_def2)
                   apply (erule heap_refs_retractD[rotated], clarsimp)
                  apply (clarsimp simp: vs_all_heap_simps)
                 apply (wpsimp wp: set_thread_state_valid_sched_action
                                   set_thread_state_valid_release_q
                                   set_thread_state_valid_ready_qs sts_invs_minor2)
                     apply (rule_tac Q'="\<lambda>_ s.
                               st_tcb_at inactive recvr s \<and>
                               invs s \<and> valid_list s \<and> scheduler_act_not recvr s \<and>
                               ex_nonz_cap_to recvr s \<and> current_time_bounded s \<and>
                               recvr \<noteq> idle_thread s \<and>
                               fault_tcb_at ((=) None) recvr s \<and>
                               valid_release_q s \<and> valid_ready_qs s \<and> ready_or_release s \<and>
                               active_scs_valid s \<and> sorted_ipc_queues s \<and>
                               heap_refs_inv (sc_tcbs_of s) (tcb_scps_of s) \<and>
                               (pred_map_eq None (tcb_scps_of s) recvr \<or> active_sc_tcb_at recvr s) \<and>
                               not_queued recvr s \<and> not_in_release_q recvr s"
                            in hoare_strengthen_post[rotated])
                      apply (clarsimp split: if_split simp: pred_tcb_at_def obj_at_def)
                     apply (wpsimp wp: thread_set_no_change_tcb_state thread_set_cap_to
                                       thread_set_no_change_tcb_state
                                       thread_set_pred_tcb_at_sets_true simp: ran_tcb_cap_cases)
                    apply (simp del: comp_apply)
                    apply (wpsimp wp: hoare_drop_imp)
                   apply wpsimp
                  apply wpsimp
                 apply wpsimp
                apply (rule_tac Q'="\<lambda>_. tcb_at' recvr and invs'" in hoare_strengthen_post[rotated])
                 apply (clarsimp simp: tcb_at'_ex_eq_all invs'_def valid_pspace'_def)
                apply (wpsimp wp: sts_invs')
                 apply (rule_tac Q'="\<lambda>_. invs' and (st_tcb_at' (\<lambda>st. st = Inactive) recvr)"
                              in hoare_strengthen_post[rotated])
                  apply (clarsimp simp: pred_tcb_at'_def obj_at'_def opt_pred_def
                                 split: option.splits)
                 apply wpsimp
                apply (wpsimp wp: sts_invs')
                    apply (rule_tac Q'="\<lambda>_. invs' and sch_act_not recvr
                                            and (st_tcb_at' (\<lambda>st. st = Inactive) recvr)"
                                 in hoare_post_imp)
                     apply (clarsimp simp: pred_tcb_at'_def obj_at'_def opt_pred_def
                                    split: option.splits)
                    apply (wpsimp wp: threadSet_fault_invs' threadSet_pred_tcb_no_state threadSet_cur)
                   apply wpsimp+
               apply (wpsimp wp: thread_get_wp')
              apply (wpsimp wp: threadGet_wp)
             apply (rule_tac Q'="\<lambda>_. tcb_at sender and tcb_at recvr and invs and valid_list and
                       valid_sched and scheduler_act_not recvr and not_in_release_q recvr and
                       active_if_bound_sc_tcb_at recvr and st_tcb_at inactive recvr and
                       ex_nonz_cap_to recvr and not_queued recvr and not_in_release_q recvr and
                       current_time_bounded"
                    in hoare_strengthen_post[rotated])
              apply (clarsimp simp: valid_sched_def invs_def valid_state_def valid_pspace_def
                                    pred_tcb_at_def obj_at_def
                             dest!: idle_no_ex_cap)
             apply (wpsimp wp: refill_unblock_check_valid_sched
                         simp: if_cond_refill_unblock_check_def)
            apply (rule_tac Q'="\<lambda>_. invs' and tcb_at' sender and sch_act_not recvr
                                    and st_tcb_at' ((=) Inactive) recvr"
                         in hoare_post_imp)
             apply (clarsimp simp: op_equal invs'_def obj_at'_def)
            apply wpsimp
           apply (wpsimp wp: get_tcb_obj_ref_wp)
          apply (wpsimp wp: threadGet_wp)
         apply (rule_tac Q'="\<lambda>_. tcb_at sender and tcb_at recvr and invs and valid_list and
                   valid_sched and scheduler_act_not recvr and not_in_release_q recvr and
                   active_if_bound_sc_tcb_at recvr and st_tcb_at inactive recvr and
                   ex_nonz_cap_to recvr and not_queued recvr and not_in_release_q recvr and
                   current_time_bounded"
                in hoare_strengthen_post[rotated])
          apply (clarsimp simp: valid_sched_def invs_def valid_state_def valid_pspace_def
                         dest!: idle_no_ex_cap)
          apply (erule disjE;
                 clarsimp simp: vs_all_heap_simps obj_at_def is_sc_obj opt_map_red opt_pred_def)
          apply (rule conjI)
           apply (erule (1) valid_sched_context_size_objsI)
          apply (clarsimp split: if_split)
          apply (drule sym_refs_inv_tcb_scps, rename_tac scp sc n t tcb')
          apply (prop_tac "heap_ref_eq scp t (tcb_scps_of s) \<and> heap_ref_eq scp recvr (tcb_scps_of s)")
           apply (clarsimp simp: vs_all_heap_simps)
          apply (clarsimp simp: heap_refs_inv_def2 vs_all_heap_simps)
         apply (wpsimp wp: reply_remove_valid_sched reply_remove_active_if_bound_sc_tcb_at reply_remove_invs)
        apply (rule_tac Q'="\<lambda>_. tcb_at' sender and invs' and sch_act_not recvr
                                and st_tcb_at' (\<lambda>a. a = Structures_H.thread_state.Inactive) recvr"
                     in hoare_post_imp)
         apply (clarsimp simp: obj_at'_def invs'_def valid_pspace'_def op_equal split: option.split)
        apply (wpsimp simp: valid_pspace'_def wp: replyRemove_invs')
       apply (clarsimp simp: invs_def valid_state_def valid_pspace_def valid_sched_def
                             valid_sched_action_weak_valid_sched_action
                       cong: conj_cong)
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
      apply (clarsimp simp: invs'_def valid_pspace'_def cong: conj_cong)
      apply (intro conjI)
        apply (erule cross_relF[OF _ tcb_at'_cross_rel[where t=sender]], fastforce)
       apply (clarsimp simp: pred_tcb_at'_def obj_at'_def)
      apply (prop_tac "sch_act_wf (ksSchedulerAction s') s'")
       apply (fastforce dest: sch_act_wf_cross)
      apply (clarsimp simp: pred_tcb_at'_def obj_at'_def)
     apply (wpsimp wp: get_simple_ko_wp)+
   apply (clarsimp split: option.split simp: invs_def valid_state_def valid_pspace_def)
   apply (frule (1) valid_objs_ko_at)
   apply (clarsimp simp: valid_obj_def valid_reply_def obj_at_def reply_tcb_reply_at_def)
  apply (clarsimp split: option.split
                   simp: invs_def valid_state_def valid_pspace_def invs'_def
                         valid_pspace'_def)
  apply (frule cross_relF[OF _ reply_at'_cross_rel[where t=reply]]; clarsimp)
  done

end

end
