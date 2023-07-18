(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Arch_DP
imports Retype_DP
begin


lemma cdl_get_pde_result_pt:
  "\<lbrace> < (pd, unat (ptr >> 20)) \<mapsto>c PageTableCap p b None \<and>* sep_true> \<rbrace>
    cdl_get_pde (cdl_lookup_pd_slot pd ptr)
  \<lbrace>\<lambda>r s. \<exists>asid. r = PageTableCap p b asid\<rbrace>"
  apply (clarsimp simp:cdl_get_pde_def cdl_lookup_pd_slot_def)
  apply wp
  apply (clarsimp dest!:opt_cap_sep_imp)
  apply (clarsimp simp:reset_cap_asid_def split:cdl_cap.splits)
  done

lemma cdl_lookup_pt_slot_rv:
  "\<lbrace> K (R (p, unat ((ptr >> 12) && 0xFF))) and <(pd, unat (ptr >> 20)) \<mapsto>c PageTableCap p Fake None \<and>* (\<lambda>s. True)>\<rbrace>
  cdl_lookup_pt_slot pd ptr \<lbrace>\<lambda>r s. R r\<rbrace>,-"
  apply (rule validE_validE_R)
  apply (clarsimp simp : cdl_lookup_pt_slot_def)
  apply (clarsimp simp: validE_def valid_def bindE_def
    bind_def bind_assoc Nondet_Monad.lift_def)
  apply (case_tac a)
   apply (clarsimp simp:liftE_def bindE_def bind_def return_def)
  apply (clarsimp simp:liftE_def bindE_def bind_def return_def)
  apply (drule use_valid[OF _  cdl_get_pde_result_pt])
   apply simp
  apply (clarsimp split:option.splits)
   apply (clarsimp simp: returnOk_def return_def)
  apply (clarsimp simp:throwError_def return_def)
  done

lemma decode_invocation_invER[wp]:
  "\<lbrace>P and Q\<rbrace> decode_invocation a b c d\<lbrace>\<lambda>_. P\<rbrace>, \<lbrace>\<lambda>_. Q\<rbrace>"
  apply (simp add:decode_invocation_def)
  apply (case_tac a,simp_all)
  apply (rule hoare_pre, (wp | simp add:throw_opt_def | wpc | intro conjI impI)+)+
  done

definition
  "cap_mapped cap = (case cap of PageTableCap _ _ asid \<Rightarrow> asid
  | FrameCap _ _ _ _ _ asid \<Rightarrow> asid)"

definition
  "cap_asid cap = (case cap of PageDirectoryCap pd_ptr real' asid' \<Rightarrow> asid')"

definition
  "get_mapped_asid \<equiv> \<lambda>asid vaddr. option_map (\<lambda>x. (x,vaddr)) asid"



lemma decode_page_map_intent_rv_20_24:
  "\<lbrakk>n = 20 \<or> n = 24 \<rbrakk>
  \<Longrightarrow> \<lbrace>\<lambda>s. R (InvokePage (PageMap (FrameCap dev frame_ptr rights n Real (get_mapped_asid asid' vaddr))
         (FrameCap False frame_ptr (validate_vm_rights (rights \<inter> perms)) n Fake None) ref [cdl_lookup_pd_slot ptr vaddr])) \<rbrace>
  decode_invocation (FrameCap dev frame_ptr rights n real_type asid) ref
  [(PageDirectoryCap ptr real' asid',pdref)]
  (PageIntent (PageMapIntent vaddr perms vmattr))
  \<lbrace>\<lambda>r s. R r\<rbrace>, -"
  apply (simp add: decode_invocation_def get_index_def get_page_intent_def throw_opt_def
                   cap_rights_def decode_page_invocation_def throw_on_none_def get_mapped_asid_def)
  apply (wp alternativeE_wp select_wp | wpc)+
     apply (rule validE_validE_R)
     apply (wp alternativeE_wp)
     apply (simp add:cdl_page_mapping_entries_def split del:if_split | wp | wpc)+
  apply auto
  done

lemma decode_page_map_intent_rv_16_12:
  "\<lbrakk>n = 12 \<or> n = 16 \<rbrakk>
  \<Longrightarrow> \<lbrace>\<lambda>s. R (InvokePage (PageMap (FrameCap dev frame_ptr rights n Real (get_mapped_asid asid' vaddr))
         (FrameCap False frame_ptr (validate_vm_rights (rights \<inter> perms)) n Fake None) ref
         [(p, unat ((vaddr >> 12) && 0xFF))]))
  \<and> <(ptr, unat (vaddr >> 20)) \<mapsto>c PageTableCap p Fake None \<and>* (\<lambda>s. True)> s\<rbrace>
  decode_invocation (FrameCap dev frame_ptr rights n real_type asid) ref
  [(PageDirectoryCap ptr real' asid',pdref)]
  (PageIntent (PageMapIntent vaddr perms vmattr))
  \<lbrace>\<lambda>r s. R r\<rbrace>, -"
  apply (simp add:decode_invocation_def get_index_def
    get_page_intent_def throw_opt_def cap_rights_def
    decode_page_invocation_def throw_on_none_def
    get_mapped_asid_def)
  apply (wp alternativeE_wp select_wp)
  apply (rule validE_validE_R)
   apply (wp alternativeE_wp)
    apply (simp add:cdl_page_mapping_entries_def)
    apply (wp cdl_lookup_pt_slot_rv | wpc | simp)+
   apply auto
  done

abbreviation(input)
  invoke_page_map_slots :: "cdl_invocation \<Rightarrow> cdl_cap_ref list"
  where "invoke_page_map_slots ivk \<equiv>
  case ivk of (InvokePage (PageMap cap cap' ref xs)) \<Rightarrow> xs"

lemma invoke_page_wp:
  "pinv = PageMap (FrameCap dev frame_ptr rights n fake asid)
  (FrameCap False frame_ptr rights' n fake' asid') ref x
  \<Longrightarrow>\<lbrace><ref \<mapsto>c - \<and>* \<And>* map sep_any_map_c (invoke_page_map_slots (InvokePage pinv))
    \<and>* P (invoke_page_map_slots (InvokePage pinv)) >\<rbrace>
    invoke_page pinv
   \<lbrace>\<lambda>r. <\<And>* map (\<lambda>ptr. ptr\<mapsto>c (FrameCap False frame_ptr rights' n fake' asid'))
          (invoke_page_map_slots (InvokePage pinv))
       \<and>* ref \<mapsto>c (FrameCap dev frame_ptr rights n fake asid) \<and>* P (invoke_page_map_slots (InvokePage pinv))>\<rbrace>"
  apply (simp add:invoke_page_def)
  apply wp
  apply (rule sep_lifted.mapM_x_sep_inv
    [where lft = sep_state_projection and I' = \<top>,simplified])
   apply (simp add:swp_def)
   apply (rule hoare_pre)
    apply (rule set_cap_wp)
   apply simp
  apply (wp sep_wp: set_cap_wp, sep_solve)
done


lemma invoke_page_table_wp:
  "pinv = PageTableMap real_pt_cap pt_cap pt_cap_ref pt_target_slot \<Longrightarrow>
  \<lbrace> < pt_cap_ref \<mapsto>c - \<and>* pt_target_slot \<mapsto>c - \<and>* P> \<rbrace>
  invoke_page_table pinv
  \<lbrace>\<lambda>_.  <pt_cap_ref \<mapsto>c real_pt_cap \<and>* pt_target_slot \<mapsto>c pt_cap \<and>* P>\<rbrace>"
  apply (clarsimp simp:invoke_page_table_def)
  apply (wp sep_wp: insert_cap_orphan_wp set_cap_wp, sep_solve)
done

crunch cdl_cur_thread[wp]: invoke_page "\<lambda>s. P (cdl_current_thread s)"
(wp: crunch_wps select_wp alternative_wp simp : swp_def )

crunch cdl_cur_thread[wp]: invoke_page_table "\<lambda>s. P (cdl_current_thread s)"
(wp: crunch_wps select_wp alternative_wp simp : swp_def )

crunch cdl_cur_domain[wp]: invoke_page_table, invoke_page "\<lambda>s. P (cdl_current_domain s)"
(wp: crunch_wps select_wp alternative_wp simp : swp_def unless_def)

lemmas cap_asid_simps[simp] = cap_asid_def[split_simps cdl_cap.split]
lemmas cap_mapped_simps[simp] = cap_mapped_def[split_simps cdl_cap.split]

lemma decode_page_table_rv:
  "\<lbrace>Q (InvokePageTable
               (PageTableMap (PageTableCap ptr Real (get_mapped_asid (cap_asid (fst pd_cap_slot)) (vaddr && ~~ mask 20)))
                 (PageTableCap ptr Fake None) ref
                 (cdl_lookup_pd_slot (cap_object (fst pd_cap_slot)) vaddr))) \<rbrace>
  decode_invocation (PageTableCap ptr b asid) ref  [pd_cap_slot]
  (PageTableIntent (PageTableMapIntent vaddr vmattribs))
  \<lbrace>Q\<rbrace>, -"
  apply (case_tac pd_cap_slot)
  apply (simp add:decode_invocation_def get_page_table_intent_def
    throw_opt_def decode_page_table_invocation_def)
  apply (rule hoare_pre)
   apply (wp alternativeE_wp  throw_on_none_wp | wpc | simp)+
  apply (clarsimp split:option.splits simp:get_index_def cap_object_def
    cap_has_object_def get_mapped_asid_def)
  done

lemma seL4_Page_Table_Map:
  notes split_paired_Ex[simp del]
  assumes misc:
  "cap_object cnode_cap = cnode_id"
  "is_cnode_cap cnode_cap"
  "offset page_table root_size = pt_offset"
  "offset page_directory root_size = pd_offset"
  and sz: "one_lvl_lookup cnode_cap word_bits root_size"
          "guard_equal cnode_cap page_directory word_bits"
          "guard_equal cnode_cap page_table word_bits"
  shows "\<lbrace>
  \<guillemotleft> (root_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap
  \<and>* (cdl_lookup_pd_slot pd_ptr vaddr) \<mapsto>c -
  \<and>* (cnode_id, pt_offset) \<mapsto>c (PageTableCap ptr Real None)
  \<and>* (cnode_id, pd_offset) \<mapsto>c (PageDirectoryCap pd_ptr real_type None)
  \<and>* (root_tcb_id, tcb_cspace_slot) \<mapsto>c cnode_cap
  \<and>* root_tcb_id \<mapsto>f (Tcb tcb)
  \<and>* cnode_id \<mapsto>f CNode (empty_cnode root_size)
  \<and>*R \<guillemotright>\<rbrace>
  seL4_PageTable_Map page_table page_directory vaddr vmattribs
  \<lbrace>\<lambda>r s.
  \<guillemotleft> (root_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap
  \<and>* cdl_lookup_pd_slot pd_ptr vaddr \<mapsto>c (PageTableCap ptr Fake None)
  \<and>* (cnode_id, pt_offset) \<mapsto>c (PageTableCap ptr Real None)
  \<and>* (cnode_id, pd_offset) \<mapsto>c (PageDirectoryCap pd_ptr real_type None)
  \<and>* (root_tcb_id, tcb_cspace_slot) \<mapsto>c cnode_cap
  \<and>* root_tcb_id \<mapsto>f (Tcb tcb)
  \<and>* cnode_id \<mapsto>f CNode (empty_cnode root_size)
  \<and>*R \<guillemotright> s \<rbrace>"
  apply (simp add:seL4_PageTable_Map_def sep_state_projection2_def)
  apply (rule hoare_name_pre_state)
  apply (rule hoare_pre)
   apply (rule do_kernel_op_pull_back)
   apply (rule call_kernel_with_intent_allow_error_helper
     [where check = True and Perror = \<top>,simplified])
                apply fastforce
               apply (rule set_cap_wp)
              apply (wp+)[4]
          apply (rule_tac P = "\<exists>asid'. iv = InvokePageTable (PageTableMap
            (PageTableCap ptr Real asid') (PageTableCap ptr Fake None)
            (cnode_id,pt_offset) (cdl_lookup_pd_slot pd_ptr vaddr))"
            in hoare_gen_asmEx)
         apply clarsimp
         apply wp
         apply (rule_tac P1 = "P1 \<and>* P2" for P1 P2 in hoare_strengthen_post
           [OF invoke_page_table_wp])
          apply fastforce
         apply (rule conjI)
         apply (sep_solve)
           apply (subst sep_map_c_asid_reset [where ptr = "(cnode_id,pt_offset)"])
            prefer 2
            apply (sep_solve)
           apply (simp add:reset_cap_asid_def)
          apply (wp hoare_vcg_conj_lift)
          apply (wp hoare_strengthen_post[OF set_cap_wp])
          apply (sep_solve )
         apply wp
        apply (rule_tac P = "\<exists>asid asid'. (c = (PageTableCap ptr Real asid)
         \<and> cs = [(PageDirectoryCap pd_ptr real_type asid',(cnode_id,pd_offset))]
         \<and> ref = (cnode_id,pt_offset))"
         in hoare_gen_asmEx)
        apply (elim conjE exE)
        apply simp
        apply (rule_tac Q = "\<lambda>iv s. cdl_current_thread s = Some root_tcb_id \<and>
                                    cdl_current_domain s = minBound \<and>
          <(root_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap
          \<and>* (root_tcb_id, tcb_cspace_slot) \<mapsto>c cnode_cap
          \<and>* (cdl_lookup_pd_slot pd_ptr vaddr) \<mapsto>c -
          \<and>* (cnode_id, pt_offset) \<mapsto>c PageTableCap ptr Real None
          \<and>* (cnode_id, pd_offset) \<mapsto>c PageDirectoryCap pd_ptr real_type None
          \<and>* root_tcb_id \<mapsto>f Tcb tcb
          \<and>* cnode_id \<mapsto>f CNode (empty_cnode root_size) \<and>*  R> s \<and>
         iv = InvokePageTable (PageTableMap (PageTableCap ptr Real (get_mapped_asid asid' (vaddr && ~~ mask 20))) (PageTableCap ptr Fake None)
          (cnode_id,pt_offset) (cdl_lookup_pd_slot pd_ptr vaddr))"
         in hoare_post_impErr[rotated -1])
           apply assumption
          apply clarsimp
         apply (rule hoare_vcg_E_elim)
          apply wp
         apply wp
         apply (rule validE_validE_R)
         apply (rule hoare_weaken_preE[where P = \<top>])
         apply (wp decode_page_table_rv)[1]
          apply (simp add:cap_object_def)
         apply (simp add:cap_has_object_def)
        apply clarsimp
        apply (sep_solve)
       apply (simp add:lookup_extra_caps_def conj_comms mapME_singleton)
       apply (rule wp_no_exception_seq)
        apply wp
       apply (rule lookup_cap_and_slot_rvu[where r = root_size
       and cap' = "PageDirectoryCap pd_ptr real_type None"])
      apply (rule hoare_pre)
       apply (wp lookup_cap_and_slot_rvu[where r = root_size
        and cap' = "PageTableCap ptr Real None"])[1]
      apply (erule_tac Q="cdl_current_domain sa = minBound" in conjE, assumption)
      apply (wp lookup_cap_and_slot_rvu[where r = root_size
       and cap' = "PageTableCap ptr Real None"])[1]
     apply clarsimp
    apply (wp update_thread_intent_update hoare_vcg_all_lift
      hoare_vcg_imp_lift)
   apply clarsimp
   defer
   apply clarsimp
   using misc sz
   apply (intro conjI impI allI, simp_all add: reset_cap_asid_simps2)
        apply (sep_solve)
       apply simp
       apply sep_solve
      apply (clarsimp simp:user_pointer_at_def Let_def word_bits_def sep_conj_assoc)
      apply sep_solve
     apply (clarsimp dest!:reset_cap_asid_simps2 simp: ep_related_cap_def)
    apply (clarsimp simp:user_pointer_at_def Let_def word_bits_def sep_conj_assoc)
    apply (sep_solve)
   apply (clarsimp dest!:reset_cap_asid_simps2 simp: ep_related_cap_def)
   apply (clarsimp simp:user_pointer_at_def Let_def word_bits_def sep_conj_assoc)
   apply (sep_solve)
  apply (drule_tac x = "PageTableCap ptr Real None"  in spec)
  apply clarsimp
  apply (erule impE)
   apply (rule_tac x = "PageDirectoryCap pd_ptr real_type None" in exI)
   apply simp
  apply clarsimp
  apply (sep_solve)
  done

lemma seL4_Section_Map_wp:
  notes split_paired_Ex[simp del]
  assumes misc:
  "cap_object cnode_cap = cnode_id" "is_cnode_cap cnode_cap"
  "offset sel_page root_size = frame_offset"
  "offset sel4_page_directory root_size = pd_offset"
  and sz: "one_lvl_lookup cnode_cap word_bits root_size"
          "guard_equal cnode_cap sel4_page_directory word_bits"
          "guard_equal cnode_cap sel_page word_bits"
  shows "\<lbrakk>n = 20 \<or> n = 24
  \<rbrakk> \<Longrightarrow> \<lbrace>
  \<guillemotleft> (root_tcb_id,tcb_pending_op_slot) \<mapsto>c RunningCap
  \<and>* root_tcb_id \<mapsto>f Tcb tcb
  \<and>* (root_tcb_id,tcb_cspace_slot) \<mapsto>c cnode_cap
  \<and>* cnode_id \<mapsto>f CNode (empty_cnode root_size)
  \<and>* (cdl_lookup_pd_slot pd_ptr vaddr) \<mapsto>c -
  \<and>* (cnode_id, pd_offset) \<mapsto>c (PageDirectoryCap pd_ptr real_type None)
  \<and>* (cnode_id, frame_offset) \<mapsto>c FrameCap dev frame_ptr rights n Real None \<and>* R \<guillemotright> \<rbrace>
  seL4_Page_Map sel_page sel4_page_directory vaddr perms vmattr
  \<lbrace>\<lambda>r s. \<guillemotleft> (root_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap
    \<and>* (root_tcb_id, tcb_cspace_slot) \<mapsto>c cnode_cap
    \<and>* cdl_lookup_pd_slot pd_ptr vaddr \<mapsto>c
       FrameCap False frame_ptr (validate_vm_rights (rights \<inter> perms)) n Fake None
    \<and>* (cnode_id, frame_offset) \<mapsto>c FrameCap dev frame_ptr rights n Real None
    \<and>* root_tcb_id \<mapsto>f (Tcb tcb)
    \<and>* (cnode_id, pd_offset) \<mapsto>c (PageDirectoryCap pd_ptr real_type None)
    \<and>* cnode_id \<mapsto>f CNode (empty_cnode root_size)
    \<and>* R \<guillemotright> s \<rbrace>"
  apply (simp add:seL4_Page_Map_def sep_state_projection2_def)
  apply (rule hoare_name_pre_state)
  apply (rule hoare_pre)
   apply (rule do_kernel_op_pull_back)
   apply (rule call_kernel_with_intent_allow_error_helper
     [where check = True and Perror = \<top>,simplified])
                 apply fastforce
                apply (rule set_cap_wp)
               apply (wp+)[4]
           apply (rule_tac P = "\<exists>asid'. iv = InvokePage
             (PageMap (FrameCap dev frame_ptr rights n Real asid')
             (FrameCap False frame_ptr (validate_vm_rights (rights \<inter> perms)) n Fake None) (cnode_id,frame_offset)
             [cdl_lookup_pd_slot pd_ptr vaddr])"
             in hoare_gen_asmEx)
           apply clarsimp
           apply wp
           apply (rule_tac P1 = "\<lambda>iv. P1 \<and>* P2" for P1 P2 in hoare_strengthen_post
            [OF invoke_page_wp[where fake = Real
              and fake' = Fake and x = "[cdl_lookup_pd_slot pd_ptr vaddr]" ]])
            apply (rule refl)
           apply simp
           apply (rule conjI)
           apply (sep_solve)
           apply (subst sep_map_c_asid_reset [where ptr = "(cnode_id,frame_offset)"])
            prefer 2
             apply (sep_erule_concl refl_imp)+
             apply (sep_solve)
           apply (simp add:reset_cap_asid_def)
          apply (wp hoare_vcg_conj_lift)
          apply (wp hoare_strengthen_post[OF set_cap_wp])
          apply (sep_solve)
         apply wp
        apply (rule_tac P = "\<exists>asid asid'. (c = (FrameCap dev frame_ptr rights n Real asid)
         \<and> cs = [(PageDirectoryCap pd_ptr real_type asid',(cnode_id,pd_offset))]
         \<and> ref = (cnode_id,frame_offset))"
         in hoare_gen_asmEx)
        apply (elim exE)+
        apply simp
        apply (rule_tac Q = "\<lambda>iv s. cdl_current_thread s = Some root_tcb_id \<and>
                                    cdl_current_domain s = minBound \<and>
          <(root_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap
          \<and>* (root_tcb_id, tcb_cspace_slot) \<mapsto>c cnode_cap
          \<and>* (cdl_lookup_pd_slot pd_ptr vaddr) \<mapsto>c -
          \<and>* (cnode_id, frame_offset) \<mapsto>c -
          \<and>* root_tcb_id \<mapsto>f Tcb tcb \<and>* (cnode_id, pd_offset) \<mapsto>c PageDirectoryCap pd_ptr real_type None
          \<and>* cnode_id \<mapsto>f CNode (empty_cnode root_size) \<and>*  R> s \<and>
         iv = InvokePage
         (PageMap (FrameCap dev frame_ptr rights n Real (get_mapped_asid asid' vaddr))
         (FrameCap False frame_ptr (validate_vm_rights (rights \<inter> perms)) n Fake None) (cnode_id,frame_offset)
          [cdl_lookup_pd_slot pd_ptr vaddr])"
         in hoare_post_impErr[rotated -1])
          apply assumption
         apply (rule hoare_vcg_E_elim)
          apply wp
         apply wp
         apply (rule validE_validE_R)
         apply (rule hoare_weaken_preE[where P = \<top>])
         apply (wp decode_page_map_intent_rv_20_24)[1]
          apply simp
         apply simp
        apply clarsimp
        apply sep_solve
       apply (simp add:lookup_extra_caps_def conj_comms mapME_singleton)
       apply (rule wp_no_exception_seq)
        apply wp[1]
       apply (rule lookup_cap_and_slot_rvu[where r = root_size
       and cap' = "PageDirectoryCap pd_ptr real_type None"])
      apply (rule hoare_pre)
       apply (wp lookup_cap_and_slot_rvu[where r = root_size
        and cap' = "FrameCap dev frame_ptr rights n Real None"])[1]
      apply (erule_tac Q="cdl_current_domain sa = minBound" in conjE, assumption)
      apply (wp lookup_cap_and_slot_rvu[where r = root_size
       and cap' = "FrameCap dev frame_ptr rights n Real None"])[1]
     apply clarsimp
    apply (wp update_thread_intent_update hoare_vcg_all_lift
      hoare_vcg_imp_lift)
   apply clarsimp
   defer
  apply clarsimp
  using misc sz
  apply (intro conjI impI allI, simp_all add: reset_cap_asid_simps2)
        apply (sep_solve)
       apply simp
       apply sep_solve
      apply (clarsimp simp:user_pointer_at_def Let_def
        word_bits_def sep_conj_assoc)
      apply sep_solve
     apply (clarsimp dest!:reset_cap_asid_simps2
       simp:ep_related_cap_def)
    apply (clarsimp simp:user_pointer_at_def Let_def
          word_bits_def sep_conj_assoc)
    apply (sep_solve)
  apply clarsimp
  apply (sep_solve)
  apply (clarsimp dest!:reset_cap_asid_simps2
       simp:ep_related_cap_def)
    apply (clarsimp simp:user_pointer_at_def Let_def
          word_bits_def sep_conj_assoc)
  apply (drule_tac x = "FrameCap dev frame_ptr rights n Real None"  in spec)
   apply clarsimp
  apply (erule impE)
   apply (rule_tac x = "PageDirectoryCap pd_ptr real_type None" in exI)
   apply simp
  apply clarsimp
 apply (sep_solve)
done


lemma seL4_Page_Map_wp:
  notes split_paired_Ex[simp del]
  assumes misc:
  "cap_object cnode_cap = cnode_id" "is_cnode_cap cnode_cap"
  "offset sel_page root_size = frame_offset"
  "offset sel4_page_directory root_size = pd_offset"
  and sz: "one_lvl_lookup cnode_cap word_bits root_size"
          "guard_equal cnode_cap sel4_page_directory word_bits"
          "guard_equal cnode_cap sel_page word_bits"
  shows "\<lbrakk>n = 12 \<or> n = 16
  \<rbrakk> \<Longrightarrow> \<lbrace>
  \<guillemotleft> (root_tcb_id,tcb_pending_op_slot) \<mapsto>c RunningCap
  \<and>* root_tcb_id \<mapsto>f Tcb tcb
  \<and>* (root_tcb_id,tcb_cspace_slot) \<mapsto>c cnode_cap
  \<and>* cnode_id \<mapsto>f CNode (empty_cnode root_size)
  \<and>* (cdl_lookup_pd_slot pd_ptr vaddr) \<mapsto>c PageTableCap pt_ptr Fake None
  \<and>* (cnode_id, pd_offset) \<mapsto>c (PageDirectoryCap pd_ptr real_type None)
  \<and>* (cnode_id, frame_offset) \<mapsto>c FrameCap dev frame_ptr rights n Real None
  \<and>* (pt_ptr, unat ((vaddr >> 12) && 0xFF)) \<mapsto>c -
  \<and>* R \<guillemotright> \<rbrace>
  seL4_Page_Map sel_page sel4_page_directory vaddr perms vmattr
  \<lbrace>\<lambda>r s. \<guillemotleft> (root_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap
    \<and>* (root_tcb_id, tcb_cspace_slot) \<mapsto>c cnode_cap
    \<and>* (pt_ptr, unat ((vaddr >> 12) && 0xFF)) \<mapsto>c
       FrameCap False frame_ptr (validate_vm_rights (rights \<inter> perms)) n Fake None
    \<and>* (cnode_id, frame_offset) \<mapsto>c FrameCap dev frame_ptr rights n Real None
    \<and>* root_tcb_id \<mapsto>f (Tcb tcb)
    \<and>* (cnode_id, pd_offset) \<mapsto>c (PageDirectoryCap pd_ptr real_type None)
    \<and>* cnode_id \<mapsto>f CNode (empty_cnode root_size)
    \<and>* cdl_lookup_pd_slot pd_ptr vaddr \<mapsto>c PageTableCap pt_ptr Fake None
    \<and>* R \<guillemotright> s \<rbrace>"
  apply (simp add:seL4_Page_Map_def sep_state_projection2_def)
  apply (rule hoare_name_pre_state)
  apply (rule hoare_pre)
   apply (rule do_kernel_op_pull_back)
   apply (rule call_kernel_with_intent_allow_error_helper
     [where check = True and Perror = \<top>,simplified])
                 apply fastforce
                apply (rule set_cap_wp)
               apply (wp+)[4]
           apply (rule_tac P = "\<exists>asid'. iv = InvokePage
             (PageMap (FrameCap dev frame_ptr rights n Real asid')
             (FrameCap False frame_ptr (validate_vm_rights (rights \<inter> perms)) n Fake None) (cnode_id,frame_offset)
             [(pt_ptr, unat ((vaddr >> 12) && 0xFF))])"
             in hoare_gen_asmEx)
           apply clarsimp
           apply wp
           apply (rule_tac P1 = "\<lambda>iv. P1 \<and>* P2" for P1 P2 in hoare_strengthen_post
            [OF invoke_page_wp[where fake = Real
              and fake' = Fake
              and x = "[(pt_ptr, unat ((vaddr >> 12) && 0xFF))]" ]])
            apply (rule refl)
           apply simp
           apply (rule conjI)
           apply (sep_solve)
           apply (subst sep_map_c_asid_reset [where ptr = "(cnode_id,frame_offset)"])
            prefer 2
            apply (sep_schem)
           apply (simp add:reset_cap_asid_def)
          apply (wp hoare_vcg_conj_lift)
          apply (wp hoare_strengthen_post[OF set_cap_wp])
          apply (sep_solve)
         apply wp
        apply (rule_tac P = "\<exists>asid asid'. (c = (FrameCap dev frame_ptr rights n Real asid)
         \<and> cs = [(PageDirectoryCap pd_ptr real_type asid',(cnode_id,pd_offset))]
         \<and> ref = (cnode_id,frame_offset))"
         in hoare_gen_asmEx)
        apply (elim exE)+
        apply simp
        apply (rule_tac Q = "\<lambda>iv s. cdl_current_thread s = Some root_tcb_id \<and>
                                    cdl_current_domain s = minBound \<and>
          <(root_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap
          \<and>* (root_tcb_id, tcb_cspace_slot) \<mapsto>c cnode_cap
          \<and>* (pt_ptr, unat ((vaddr >> 12) && 0xFF)) \<mapsto>c -
          \<and>* (cnode_id, frame_offset) \<mapsto>c -
          \<and>* root_tcb_id \<mapsto>f Tcb tcb
          \<and>* (cnode_id, pd_offset) \<mapsto>c PageDirectoryCap pd_ptr real_type None
          \<and>* cdl_lookup_pd_slot pd_ptr vaddr \<mapsto>c PageTableCap pt_ptr Fake None
          \<and>* cnode_id \<mapsto>f CNode (empty_cnode root_size) \<and>*  R> s \<and>
         iv = InvokePage
         (PageMap (FrameCap dev frame_ptr rights n Real (get_mapped_asid asid' vaddr))
         (FrameCap False frame_ptr (validate_vm_rights (rights \<inter> perms)) n Fake None)
             (cnode_id,frame_offset) [ (pt_ptr, unat ((vaddr >> 12) && 0xFF))] )"
         in hoare_post_impErr[rotated -1])
          apply assumption
         apply (rule hoare_vcg_E_elim)
          apply wp
         apply wp
         apply (rule validE_validE_R)
         apply (rule_tac P = "<P>" for P in hoare_weaken_preE)
         apply (wp decode_page_map_intent_rv_16_12[where p = pt_ptr])[1]
          apply simp
         apply simp
        apply clarsimp
        apply sep_solve
       apply (simp add:lookup_extra_caps_def conj_comms mapME_singleton)
       apply (rule wp_no_exception_seq)
        apply wp[1]
       apply (rule lookup_cap_and_slot_rvu[where r = root_size
       and cap' = "PageDirectoryCap pd_ptr real_type None"])
      apply (rule hoare_pre)
       apply (wp lookup_cap_and_slot_rvu[where r = root_size
        and cap' = "FrameCap dev frame_ptr rights n Real None"])[1]
      apply (erule_tac Q="cdl_current_domain sa = minBound" in conjE, assumption)
    apply (wp update_thread_intent_update hoare_vcg_all_lift
      hoare_vcg_imp_lift)
   apply clarsimp
   defer
   apply clarsimp
   using misc sz
   apply (intro conjI impI allI, simp_all add: reset_cap_asid_simps2)
         apply (sep_solve)
        apply (simp add:cdl_lookup_pd_slot_def)
        apply sep_solve
       apply simp
       apply sep_solve
      apply (clarsimp simp:user_pointer_at_def Let_def word_bits_def sep_conj_assoc)
      apply sep_solve
     apply (clarsimp dest!:reset_cap_asid_simps2 simp: ep_related_cap_def)
    apply (clarsimp simp:user_pointer_at_def Let_def
          word_bits_def sep_conj_assoc)
    apply (sep_solve)
   apply sep_solve
  apply clarsimp
  apply (drule_tac x = "FrameCap dev frame_ptr rights n Real None"  in spec)
  apply clarsimp
  apply (erule impE)
   apply (rule_tac x = "PageDirectoryCap pd_ptr real_type None" in exI)
   apply simp
  apply clarsimp
  apply (sep_solve)
  done

lemma decode_invocation_asid_pool_assign:
  "\<lbrace> \<lambda>s. (c = AsidPoolCap p base) \<rbrace>
  decode_invocation c ref [(PageDirectoryCap pd is_real sz,pd_ref)]
  (AsidPoolIntent AsidPoolAssignIntent)
  \<lbrace>\<lambda>iv s. \<exists>x. x < 2 ^ asid_low_bits \<and> iv = InvokeAsidPool (Assign (base, x) pd_ref (p, x)) \<rbrace>, -"
  apply (rule hoare_pre)
   apply (rule hoare_gen_asmE[where P =" c = AsidPoolCap p base"])
   apply (simp add:decode_invocation_def get_asid_pool_intent_def
     decode_asid_pool_invocation_def get_index_def
     throw_opt_def throw_on_none_def)
   apply (rule validE_validE_R)
   apply (wp alternativeE_wp select_wp)
  apply (clarsimp simp:cap_object_def cap_has_object_def)
  done

crunch cdl_cur_thread[wp]: invoke_asid_pool "\<lambda>s. P (cdl_current_thread s)"

crunch cdl_cur_domain[wp]: invoke_asid_pool "\<lambda>s. P (cdl_current_domain s)"

lemma set_split_single:
  "a \<in>A \<Longrightarrow> A = A - {a} \<union> {a}"
  by blast


lemma invoke_asid_pool_wp:
  "off < 2 ^ asid_low_bits \<Longrightarrow>
  \<lbrace> <(cur_thread, tcb_pending_op_slot) \<mapsto>c RestartCap
    \<and>* (\<And>* off\<in>{off. off < 2 ^ asid_low_bits}. (p, off) \<mapsto>c -)
    \<and>* pd_ref \<mapsto>c (PageDirectoryCap pd Real asid')
    \<and>* R > \<rbrace>
  invoke_asid_pool (Assign asid pd_ref (p,off))
  \<lbrace>\<lambda>rv s. <(cur_thread, tcb_pending_op_slot) \<mapsto>c RestartCap
    \<and>* pd_ref \<mapsto>c  (PageDirectoryCap pd Real (Some asid))
    \<and>* (\<And>* off\<in>{off. off < 2 ^ asid_low_bits}. (p, off) \<mapsto>c -)
    \<and>* R > s\<rbrace>"
  apply (clarsimp simp:invoke_asid_pool_def | wp| wpc)+
          apply (rename_tac word cdl_frame_cap_type option)
          apply (rule_tac P = "word = pd" in hoare_gen_asm)
          apply simp
          apply (rule hoare_strengthen_post[OF set_cap_wp])
          apply (subst set_split_single[where A = "(Collect (\<lambda>off. off < 2 ^ asid_low_bits))"])
           apply simp
          apply (subst sep.prod.union_disjoint)
             apply simp+
          apply (clarsimp simp: sep_conj_assoc)
          apply (sep_erule_concl sep_any_imp, sep_solve)
         apply (rename_tac word cdl_frame_cap_type option)
         apply (wp hoare_vcg_conj_lift)
         apply (rule_tac P = "word = pd" in hoare_gen_asm)
         apply simp
         apply (rule hoare_strengthen_post[OF set_cap_wp])
         apply (sep_solve)
        apply wp+
  apply clarsimp
  apply (safe; fastforce?)
   apply (subst (asm) set_split_single[where A = "(Collect (\<lambda>off. off < 2 ^ asid_low_bits))"])
    apply simp
   apply (subst (asm) sep.prod.union_disjoint)
     apply simp+
   apply (simp add:sep_conj_assoc)
   apply sep_solve
  apply (sep_select_asm 3)
  apply (drule opt_cap_sep_imp)
  apply clarsimp
  done

lemma sep_map_c_asid_simp:
  "(slot \<mapsto>c FrameCap dev ptr rights sz real_type option) = (slot \<mapsto>c FrameCap dev ptr rights sz real_type None)"
  "(slot \<mapsto>c PageTableCap ptr real_type option) = (slot \<mapsto>c PageTableCap ptr real_type None)"
  "(slot \<mapsto>c PageDirectoryCap ptr real_type option') = (slot \<mapsto>c PageDirectoryCap ptr real_type None)"
  by (simp_all add:sep_map_c_asid_reset)


lemma seL4_ASIDPool_Assign_wp:
  assumes misc:
  "cap_object cnode_cap = cnode_id" "is_cnode_cap cnode_cap"
  "offset sel4_page_directory root_size = pd_offset"
  "offset sel4_asid root_size = asid_offset"
  and sz: "one_lvl_lookup cnode_cap word_bits root_size"
          "guard_equal cnode_cap sel4_page_directory word_bits"
          "guard_equal cnode_cap sel4_asid word_bits"
  shows
  "\<lbrace>
  \<guillemotleft> (root_tcb_id,tcb_pending_op_slot) \<mapsto>c RunningCap
  \<and>* root_tcb_id \<mapsto>f Tcb tcb
  \<and>* (cnode_id,asid_offset) \<mapsto>c AsidPoolCap p base
  \<and>* (cnode_id,pd_offset) \<mapsto>c PageDirectoryCap pd Real None
  \<and>*  (\<And>* off\<in>{off. off < 2 ^ asid_low_bits}. (p, off) \<mapsto>c -)
  \<and>* cnode_id \<mapsto>f CNode (empty_cnode root_size)
  \<and>* (root_tcb_id, tcb_cspace_slot) \<mapsto>c cnode_cap
  \<and>* R \<guillemotright>\<rbrace>
  seL4_ASIDPool_Assign sel4_asid sel4_page_directory
  \<lbrace>\<lambda>_. \<guillemotleft> (root_tcb_id,tcb_pending_op_slot) \<mapsto>c RunningCap
  \<and>* root_tcb_id \<mapsto>f Tcb tcb
  \<and>* (cnode_id,asid_offset) \<mapsto>c AsidPoolCap p base
  \<and>* (cnode_id,pd_offset) \<mapsto>c PageDirectoryCap pd Real None
  \<and>* (\<And>* off\<in>{off. off < 2 ^ asid_low_bits}. (p, off) \<mapsto>c -)
  \<and>* cnode_id \<mapsto>f CNode (empty_cnode root_size)
  \<and>* (root_tcb_id, tcb_cspace_slot) \<mapsto>c cnode_cap
  \<and>* R\<guillemotright> \<rbrace>"
  apply (simp add:seL4_ASIDPool_Assign_def sep_state_projection2_def
    | wp do_kernel_op_wp)+
   apply (rule call_kernel_with_intent_allow_error_helper[where check = True and Perror = \<top>,simplified])
                apply fastforce
               apply (rule set_cap_wp)
             apply (wp+)[4]
            apply (rule_tac P = "\<exists>x. x < 2 ^ asid_low_bits
              \<and> iv =  (InvokeAsidPool (Assign (base, x) (cnode_id,pd_offset) (p, x)))"
              in hoare_gen_asmEx)
            apply clarsimp
           apply wp
          apply (rule hoare_strengthen_post[OF invoke_asid_pool_wp[where pd = pd
              and cur_thread = root_tcb_id
              and R="(cnode_id, asid_offset) \<mapsto>c AsidPoolCap p base \<and>*
                      root_tcb_id \<mapsto>f Tcb tcb \<and>*
                      cnode_id \<mapsto>f CNode (empty_cnode root_size) \<and>*
                      (root_tcb_id, tcb_cspace_slot) \<mapsto>c cnode_cap \<and>* R"]])
           apply simp
          apply (rule conjI,sep_solve)
          apply (subst (asm) sep_map_c_asid_simp)
          apply sep_solve
         apply (wp hoare_vcg_conj_lift)
          apply (rule hoare_strengthen_post[OF set_cap_wp])
           apply assumption
          apply wp
          apply (subst sep_map_c_asid_simp)
          apply (wp hoare_vcg_conj_lift)
          apply simp
          apply (rule_tac P = "\<exists>asid. cs = [(PageDirectoryCap pd Real asid,(cnode_id,pd_offset))]" in hoare_gen_asmE)
          apply clarsimp
          apply (rule decode_invocation_asid_pool_assign)
         apply (clarsimp simp:conj_comms lookup_extra_caps_def mapME_singleton)
         apply (rule wp_no_exception_seq)
          apply wp
         apply (rule lookup_cap_and_slot_rvu[where r = root_size
           and cap' = "PageDirectoryCap pd Real None"])
        apply (rule hoare_pre)
         apply (rule lookup_cap_and_slot_rvu[where r = root_size
           and cap' = "AsidPoolCap p base"])
        apply (erule_tac Q="cdl_current_domain s = minBound" in conjE, assumption)
    apply clarsimp
    apply (wp update_thread_intent_update hoare_vcg_all_lift
      hoare_vcg_imp_lift)
   apply clarsimp defer
   apply clarsimp
   using misc sz
   apply (intro conjI impI allI, simp_all add: reset_cap_asid_simps2)
        apply sep_solve
       apply sep_solve
      apply (clarsimp simp:user_pointer_at_def Let_def word_bits_def sep_conj_assoc)
      apply (sep_solve)
     apply (clarsimp dest!:reset_cap_asid_simps2 simp: ep_related_cap_def)
    apply (clarsimp simp:user_pointer_at_def Let_def word_bits_def sep_conj_assoc)
    apply (sep_solve)
   apply (sep_solve)
  apply clarsimp
  apply (drule_tac x = "AsidPoolCap p base" in spec)
  apply clarsimp
  apply (erule impE)
   apply (rule_tac x = "PageDirectoryCap pd Real None" in exI)
   apply simp
  apply clarsimp
  apply (drule  use_sep_true_for_sep_map_c)
   apply simp
  apply sep_solve
  done

end

