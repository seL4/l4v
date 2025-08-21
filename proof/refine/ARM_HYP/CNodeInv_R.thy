(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
  Results about CNode Invocations, particularly the
  recursive revoke and delete operations.
*)

theory CNodeInv_R
imports Ipc_R Invocations_R
begin

unbundle l4v_word_context

context begin interpretation Arch . (*FIXME: arch-split*)

primrec
  valid_cnode_inv' :: "Invocations_H.cnode_invocation \<Rightarrow> kernel_state \<Rightarrow> bool"
where
  "valid_cnode_inv' (Insert cap ptr ptr') =
   (valid_cap' cap and
    (\<lambda>s. cte_wp_at' (is_derived' (ctes_of s) ptr cap \<circ> cteCap) ptr s) and
    cte_wp_at' (untyped_derived_eq cap \<circ> cteCap) ptr and
    cte_wp_at' (\<lambda>c. cteCap c = NullCap) ptr' and (\<lambda>s. ptr \<noteq> ptr') and
    ex_cte_cap_to' ptr')"
| "valid_cnode_inv' (Move cap ptr ptr') =
   (cte_wp_at' (\<lambda>c. weak_derived' cap (cteCap c)) ptr and
    cte_wp_at' (\<lambda>c. isUntypedCap (cteCap c) \<longrightarrow> (cteCap c) = cap) ptr and
    cte_wp_at' (\<lambda>c. cteCap c \<noteq> NullCap) ptr and valid_cap' cap and
    cte_wp_at' (\<lambda>c. cteCap c = NullCap) ptr' and ex_cte_cap_to' ptr')"
| "valid_cnode_inv' (Revoke ptr) = cte_at' ptr"
| "valid_cnode_inv' (Delete ptr) = cte_at' ptr"
| "valid_cnode_inv' (Rotate s_cap p_cap src pivot dest) =
   (valid_cap' s_cap and valid_cap' p_cap and
    cte_wp_at' (\<lambda>c. weak_derived' s_cap (cteCap c)) src and
    cte_wp_at' (\<lambda>c. isUntypedCap (cteCap c) \<longrightarrow> (cteCap c) = s_cap) src and
    cte_wp_at' (\<lambda>c. weak_derived' p_cap (cteCap c)) pivot and
    cte_wp_at' (\<lambda>c. isUntypedCap (cteCap c) \<longrightarrow> (cteCap c) = p_cap) pivot and
    K (src \<noteq> pivot \<and> pivot \<noteq> dest \<and> s_cap \<noteq> capability.NullCap \<and>
       p_cap \<noteq> capability.NullCap) and
    (\<lambda>s. src \<noteq> dest \<longrightarrow> cte_wp_at' (\<lambda>c. cteCap c = NullCap) dest s) and
    (\<lambda>s. ex_cte_cap_to' pivot s \<and> ex_cte_cap_to' dest s))"
| "valid_cnode_inv' (SaveCaller slot) =
   (ex_cte_cap_to' slot and cte_wp_at' (\<lambda>c. cteCap c = NullCap) slot)"
| "valid_cnode_inv' (CancelBadgedSends cap) =
   (valid_cap' cap and K (hasCancelSendRights cap))"

lemma rightsFromWord_correspondence:
  "rightsFromWord w = rights_mask_map (data_to_rights w)"
  by (simp add: rightsFromWord_def rights_mask_map_def data_to_rights_def Let_def)

primrec
  cnodeinv_relation :: "Invocations_A.cnode_invocation \<Rightarrow> Invocations_H.cnode_invocation \<Rightarrow> bool"
where
  "cnodeinv_relation (InsertCall c cp1 cp2) x = (
   \<exists>c'. cap_relation c c' \<and> (x =
    Insert c' (cte_map cp1) (cte_map cp2)))"
| "cnodeinv_relation (MoveCall c cp1 cp2) x = (
   \<exists>c'. cap_relation c c' \<and> (x =
    Move c' (cte_map cp1) (cte_map cp2)))"
| "cnodeinv_relation (RevokeCall cp) x = (x =
   Revoke (cte_map cp))"
| "cnodeinv_relation (DeleteCall cp) x = (x =
   Delete (cte_map cp))"
| "cnodeinv_relation (RotateCall sc pc src pvt dst) x = (\<exists>sc' pc'.
   cap_relation sc sc' \<and> cap_relation pc pc' \<and>
   x = Rotate sc' pc' (cte_map src) (cte_map pvt) (cte_map dst))"
| "cnodeinv_relation (SaveCall p) x = (x = SaveCaller (cte_map p))"
| "cnodeinv_relation (CancelBadgedSendsCall c) x = (\<exists>c'. cap_relation c c' \<and> x = CancelBadgedSends c')"


lemma cap_relation_NullCap:
  "cap_relation cap cap' \<Longrightarrow>
   (update_cap_data P x cap = cap.NullCap) = (RetypeDecls_H.updateCapData P x cap' = capability.NullCap)"
  apply (cases cap)
            apply (simp_all add: Let_def mask_cap_def cap_rights_update_def update_cap_data_closedform
                                 arch_update_cap_data_def word_bits_def updateCapData_def isCap_simps
                      split del: if_split)
     apply simp
    apply simp
   apply (clarsimp simp: word_size word_size_def cteRightsBits_def cteGuardBits_def)
  apply (clarsimp simp: ARM_HYP_H.updateCapData_def isCap_simps split del: if_split)
  done

(* Sometimes I need something about the state. This is neater (IMHO) and req *)
lemma whenE_throwError_corres':
  assumes P: "frel f f'"
  assumes Q: "\<And>s s'. \<lbrakk>(s, s') \<in> state_relation; R s; R' s'\<rbrakk> \<Longrightarrow> P = P'"
  assumes R: "\<not> P \<Longrightarrow> corres (frel \<oplus> rvr) Q Q' m m'"
  shows      "corres (frel \<oplus> rvr) (R and Q) (R' and Q')
                     (whenE P  (throwError f ) >>=E (\<lambda>_. m ))
                     (whenE P' (throwError f') >>=E (\<lambda>_. m'))"
  unfolding whenE_def
  apply (rule corres_req)
   apply (erule Q)
    apply simp
   apply simp
  apply (cases P)
   apply (simp add: P)
  apply simp
  apply (erule corres_guard_imp [OF R])
   apply simp
  apply simp
  done

(* FIXME: move *)
lemma corres_split_liftM2:
  assumes    corr: "corres (\<lambda>x y. r' x (f y)) P P' a c"
  and r1: "\<And>rv rv'. r' rv rv' \<Longrightarrow> corres r (R rv) (R' rv') (b rv) (d rv')"
  and h1: "\<lbrace>Q\<rbrace> a \<lbrace>R\<rbrace>" and h2: "\<lbrace>Q'\<rbrace> c \<lbrace>\<lambda>x. R' (f x)\<rbrace>"
  shows "corres r (P and Q) (P' and Q') (a >>= b) (liftM f c >>= d)"
  apply (rule corres_guard_imp)
  apply (rule corres_split[OF _ _ h1])
       apply (simp add: o_def)
       apply (rule corr)
      apply (erule r1)
     apply wp
    apply (simp add: o_def)
    apply (rule h2)
   apply simp
  apply simp
  done

lemma cap_relation_NullCapI:
  "cap_relation c c' \<Longrightarrow> (c = cap.NullCap) = (c' = NullCap)"
  by (cases c, auto)

lemma isCNodeCap_CNodeCap:
  "isCNodeCap (CNodeCap a b c d)"
  by (simp add: isCap_simps)

lemma get_cap_corres':
  "cte_ptr' = cte_map cte_ptr \<Longrightarrow>
   corres (\<lambda>x y. cap_relation x (cteCap y)) (cte_at cte_ptr)
    (pspace_aligned' and pspace_distinct') (get_cap cte_ptr)
    (getCTE cte_ptr')"
  by (simp add: get_cap_corres)

lemma cnode_invok_case_cleanup:
  "i \<notin> {CNodeRevoke, CNodeDelete, CNodeCancelBadgedSends, CNodeRotate, CNodeSaveCaller}
        \<Longrightarrow> (case i of CNodeRevoke \<Rightarrow> P | CNodeDelete \<Rightarrow> Q | CNodeCancelBadgedSends \<Rightarrow> R
                 | CNodeRotate \<Rightarrow> S | CNodeSaveCaller \<Rightarrow> T
                 | _ \<Rightarrow> U) = U"
  by (simp split: gen_invocation_labels.split)

lemma cancelSendRightsEq:
  "cap_relation cap cap' \<Longrightarrow> hasCancelSendRights cap' = has_cancel_send_rights cap"
  by (auto simp: hasCancelSendRights_def has_cancel_send_rights_def all_rights_def
                 vmrights_map_def
                  split: cap.splits bool.splits if_splits |
         case_tac x)+

lemma decodeCNodeInvocation_corres:
  "\<lbrakk> cap_relation (cap.CNodeCap w n list) cap'; list_all2 cap_relation cs cs';
     length list \<le> 32 \<rbrakk> \<Longrightarrow>
  corres
  (ser \<oplus> cnodeinv_relation)
  (invs and cap_table_at n w and K (n \<noteq> 0) and (\<lambda>s. \<forall>x \<in> set cs. s \<turnstile> x)) (invs' and valid_cap' cap' and (\<lambda>s. \<forall>x \<in> set cs'. s \<turnstile>' x))
  (decode_cnode_invocation (mi_label mi) args
    (cap.CNodeCap w n list) cs)
  (decodeCNodeInvocation (mi_label mi) args
    cap' cs')"
  apply (rule decode_cnode_cases2[where args=args and exs=cs and label="mi_label mi"])
        \<comment> \<open>Move / Insert\<close>
        apply (clarsimp simp: list_all2_Cons1 decode_cnode_invocation_def
                              decodeCNodeInvocation_def split_def Let_def
                              unlessE_whenE isCNodeCap_CNodeCap
                              cnode_invok_case_cleanup
                   split del: if_split
                        cong: if_cong list.case_cong)
        apply (rule corres_guard_imp)
          apply (rule corres_splitEE)
             apply (rule lookupSlotForCNodeOp_corres; simp)
            apply (rule corres_splitEE)
               apply (rule ensureEmptySlot_corres; simp)
              apply (rule corres_splitEE)
                 apply (rule lookupSlotForCNodeOp_corres; simp)
                apply (simp(no_asm) add: liftE_bindE del: de_Morgan_conj split del: if_split)
                apply (rule corres_split[OF get_cap_corres'])
                   apply (simp add: split_def)
                  apply (rule whenE_throwError_corres)
                    apply (simp add: lookup_failure_map_def)
                   apply auto[1]
                  apply (rule_tac r'="\<lambda>a b. fst b = rights_mask_map (fst a)
                                          \<and> snd b = fst (snd a)
                                          \<and> snd (snd a) = (gen_invocation_type (mi_label mi)
                                                \<in> {CNodeMove, CNodeMutate})"
                             in corres_splitEE)
                     apply (rule corres_trivial)
                     subgoal by (auto split: list.split gen_invocation_labels.split,
                                 auto simp: returnOk_def all_rights_def
                                            rightsFromWord_correspondence)
                    apply (rule_tac r'=cap_relation in corres_splitEE)
                       apply (simp add: returnOk_def del: imp_disjL)
                       apply (rule conjI[rotated], rule impI)
                        apply (rule deriveCap_corres)
                         apply (clarsimp simp: cap_relation_mask
                                               cap_map_update_data
                                        split: option.split)
                        apply clarsimp
                       apply (clarsimp simp: cap_map_update_data
                                      split: option.split)
                      apply (rule corres_trivial)
                      subgoal by (auto simp add: whenE_def, auto simp add: returnOk_def)
                     apply (wp | wpc | simp(no_asm))+
                 apply (wp hoare_vcg_const_imp_liftE_R hoare_vcg_const_imp_lift
                           hoare_vcg_all_liftE_R hoare_vcg_all_lift lsfco_cte_at' hoare_drop_imps
                                | clarsimp)+
         subgoal by (auto elim!: valid_cnode_capI)
        apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def)
       \<comment> \<open>Revoke\<close>
       apply (simp add: decode_cnode_invocation_def decodeCNodeInvocation_def
                        isCap_simps Let_def unlessE_whenE del: ser_def split del: if_split)
       apply (rule corres_guard_imp, rule corres_splitEE)
            apply (rule lookupSlotForCNodeOp_corres; simp)
           apply (simp add: split_beta)
           apply (rule corres_returnOkTT)
           apply simp
          apply wp+
        apply (auto elim!: valid_cnode_capI)[1]
       apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def)
      \<comment> \<open>Delete\<close>
      apply (simp add: decode_cnode_invocation_def decodeCNodeInvocation_def
                       isCap_simps Let_def unlessE_whenE del: ser_def split del: if_split)
      apply (rule corres_guard_imp)
        apply (rule corres_splitEE)
           apply (rule lookupSlotForCNodeOp_corres; simp)
          apply (simp add: split_beta)
          apply (rule corres_returnOkTT)
          apply simp
         apply wp+
       apply (auto elim!: valid_cnode_capI)[1]
      apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def)
     \<comment> \<open>SaveCall\<close>
     apply (simp add: decode_cnode_invocation_def decodeCNodeInvocation_def
                      isCap_simps Let_def unlessE_whenE del: ser_def split del: if_split)
     apply (rule corres_guard_imp)
       apply (rule corres_splitEE)
          apply (rule lookupSlotForCNodeOp_corres; simp)
         apply (simp add: split_beta)
         apply (rule corres_split_norE)
            apply (rule ensureEmptySlot_corres)
            apply simp
           apply (rule corres_returnOkTT)
           apply simp
          apply (wp hoare_drop_imps)+
      apply (auto elim!: valid_cnode_capI)[1]
     apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def)
    \<comment> \<open>CancelBadgedSends\<close>
    apply (simp add: decode_cnode_invocation_def decodeCNodeInvocation_def
                     isCap_simps Let_def unlessE_whenE del: ser_def split del: if_split)
    apply (rule corres_guard_imp)
      apply (rule corres_splitEE)
         apply (rule lookupSlotForCNodeOp_corres; simp)
        apply (simp(no_asm) add: split_beta liftE_bindE)
        apply (rule corres_split[OF get_cap_corres'], simp)
          apply (rule corres_split_norE)
             apply (simp add: cancelSendRightsEq)
             apply (rule corres_trivial, auto simp add: whenE_def returnOk_def)[1]
            apply (rule corres_trivial)
            apply (clarsimp simp add: returnOk_def)
           apply (wp get_cap_wp getCTE_wp | simp only: whenE_def | clarsimp)+
      apply (rule hoare_trivE_R[where P="\<top>"])
      apply (wpsimp simp: cte_wp_at_ctes_of pred_conj_def)
     apply (fastforce elim!: valid_cnode_capI simp: invs_def valid_state_def valid_pspace_def)
    apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def)
   \<comment> \<open>Rotate\<close>
   apply (frule list_all2_lengthD)
   apply (clarsimp simp: list_all2_Cons1)
   apply (simp add: le_diff_conv2 split_def decode_cnode_invocation_def decodeCNodeInvocation_def
                    isCap_simps Let_def unlessE_whenE whenE_whenE_body
               del: disj_not1 ser_def split del: if_split)
   apply (rule corres_guard_imp, rule corres_splitEE)
        apply (rule lookupSlotForCNodeOp_corres; simp)
       apply (rename_tac dest_slot destSlot)
       apply (rule corres_splitEE, (rule lookupSlotForCNodeOp_corres; simp))+
           apply (rule_tac R = "\<lambda>s. cte_at pivot_slot s \<and> cte_at dest_slot s
                                  \<and> cte_at src_slot s \<and> invs s" in
             whenE_throwError_corres' [where R' = \<top>])
             apply simp
            apply (elim conjE)
            apply rule
             apply fastforce
            apply (erule disjE)
             apply (clarsimp simp add: split_def)
             apply (drule (2) cte_map_inj_eq, clarsimp+)[1]
            apply (clarsimp simp add: split_def)
            apply (drule (2) cte_map_inj_eq, clarsimp+)[1]
           apply (rule corres_split_norE)
              apply (rule_tac F = "(src_slot \<noteq> dest_slot) = (srcSlot \<noteq> destSlot)"
                and P = "\<lambda>s. cte_at src_slot s \<and> cte_at dest_slot s \<and> invs s" and P' = invs' in corres_req)
               apply simp
               apply rule
                apply clarsimp
               apply clarsimp
               apply (drule (2) cte_map_inj_eq, clarsimp+)[1]
              apply (rule corres_guard_imp)
                apply (erule corres_whenE)
                 apply (rule ensureEmptySlot_corres)
                 apply clarsimp
                apply simp
               apply clarsimp
              apply clarsimp
             apply (simp add: liftE_bindE del: de_Morgan_conj disj_not1 split del: if_split)
             apply (rule corres_split_liftM2, simp only: split_beta, rule get_cap_corres)
               apply (rule whenE_throwError_corres)
                 apply (simp add: lookup_failure_map_def)
                apply (erule cap_relation_NullCapI)
               apply (rule corres_split_liftM2, simp only: split_beta, rule get_cap_corres)
                 apply (rule whenE_throwError_corres)
                   apply (simp add: lookup_failure_map_def)
                  apply (erule cap_relation_NullCapI)
                 apply (rule whenE_throwError_corres)
                   apply simp
                  apply (simp add: cap_relation_NullCap)
                 apply (rule corres_returnOkTT)
                 apply simp
                 apply (intro conjI)
                  apply (erule cap_map_update_data)+
                apply (wp hoare_drop_imps)+
          apply simp
          apply (wp lsfco_cte_at' lookup_cap_valid lookup_cap_valid')
         apply (simp add: if_apply_def2)
         apply (wp hoare_drop_imps)
        apply wp
       apply simp
       apply (wp lsfco_cte_at' lookup_cap_valid lookup_cap_valid' hoare_drop_imps
                 | simp add: if_apply_def2 del: de_Morgan_conj split del: if_split)+
    apply (auto elim!: valid_cnode_capI)[1]
   apply (clarsimp dest!: list_all2_lengthD simp: invs'_def valid_state'_def valid_pspace'_def)
  \<comment> \<open>Errors\<close>
  apply (elim disjE)
     apply (simp add: decode_cnode_invocation_def decodeCNodeInvocation_def
                      isCNodeCap_CNodeCap unlessE_whenE
               split: list.split)
    apply (clarsimp simp: decode_cnode_invocation_def decodeCNodeInvocation_def
                          isCNodeCap_CNodeCap unlessE_whenE)
   apply (clarsimp simp: decode_cnode_invocation_def decodeCNodeInvocation_def
                         isCNodeCap_CNodeCap unlessE_whenE)
  apply clarsimp
  apply (elim disjE)
   apply (clarsimp simp: decode_cnode_invocation_def decodeCNodeInvocation_def
                         isCNodeCap_CNodeCap split_def unlessE_whenE
                         cnode_invok_case_cleanup
              split del: if_split cong: if_cong)
   apply (rule corres_guard_imp)
     apply (rule corres_splitEE)
        apply (rule lookupSlotForCNodeOp_corres; simp)
       apply (rule corres_trivial, clarsimp split: list.split_asm)
      apply wp+
    apply (auto elim!: valid_cnode_capI)[1]
   apply fastforce
  apply (clarsimp simp: decode_cnode_invocation_def decodeCNodeInvocation_def
                        isCNodeCap_CNodeCap split_def unlessE_whenE
             split del: if_split cong: if_cong)
  apply (rule corres_guard_imp)
    apply (rule corres_splitEE[OF lookupSlotForCNodeOp_corres _ wp_post_tautE wp_post_tautE])
      apply simp
     apply simp
    apply (clarsimp simp: list_all2_Cons1 list_all2_Nil
                   split: list.split_asm split del: if_split)
   apply (auto elim!: valid_cnode_capI)[1]
  apply fastforce
  done

lemma capBadge_updateCapData_True:
  "updateCapData True x c \<noteq> NullCap \<Longrightarrow> capBadge (updateCapData True x c) = capBadge c"
  apply (simp add: updateCapData_def isCap_simps Let_def
            split: if_split_asm split del: if_split)
  apply (simp add: ARM_HYP_H.updateCapData_def)
  done

lemma badge_derived_updateCapData:
  "\<lbrakk> updateCapData False x cap \<noteq> NullCap; badge_derived' cap cap' \<rbrakk>
         \<Longrightarrow> badge_derived' (updateCapData False x cap) cap'"
  by (simp add: badge_derived'_def updateCapData_Master
                updateCapData_ordering)

lemma deriveCap_Null_helper:
  assumes "\<lbrace>P\<rbrace> deriveCap x cap \<lbrace>\<lambda>rv s. rv \<noteq> NullCap \<longrightarrow> Q rv s\<rbrace>,-"
  shows   "\<lbrace>\<lambda>s. cap \<noteq> NullCap \<longrightarrow> P s\<rbrace> deriveCap x cap \<lbrace>\<lambda>rv s. rv \<noteq> NullCap \<longrightarrow> Q rv s\<rbrace>,-"
  apply (cases "cap = NullCap")
   apply (simp add: deriveCap_def isCap_simps)
   apply (wp | simp)+
  apply (rule hoare_strengthen_postE_R, rule assms)
  apply simp
  done

lemma hasCancelSendRights_not_Null:
  "hasCancelSendRights cap \<Longrightarrow> isEndpointCap cap"
  by (clarsimp simp: hasCancelSendRights_def isCap_simps split: capability.splits)

declare if_split [split del]

lemma untyped_derived_eq_maskCapRights:
  "untyped_derived_eq (RetypeDecls_H.maskCapRights m cap) cap'
    = untyped_derived_eq cap cap'"
  apply (simp add: untyped_derived_eq_def)
  apply (rule imp_cong)
   apply (rule capMaster_isUntyped, simp)
  apply (clarsimp simp: isCap_simps)
  done

lemma untyped_derived_eq_updateCapData:
  "RetypeDecls_H.updateCapData x y cap \<noteq> NullCap
    \<Longrightarrow> untyped_derived_eq (RetypeDecls_H.updateCapData x y cap) cap'
        = untyped_derived_eq cap cap'"
  apply (simp add: untyped_derived_eq_def)
  apply (rule imp_cong)
   apply (rule capMaster_isUntyped)
   apply (erule updateCapData_Master)
  apply (clarsimp simp: isCap_simps)
  apply (clarsimp simp: updateCapData_def isCap_simps)
  done

lemma untyped_derived_eq_refl:
  "untyped_derived_eq c c"
  by (simp add: untyped_derived_eq_def)

lemma decodeCNodeInv_wf[wp]:
  "\<lbrace>invs' and valid_cap' (CNodeCap w n w2 n2)
          and (\<lambda>s. \<forall>r\<in>cte_refs' (CNodeCap w n w2 n2) (irq_node' s).
                     ex_cte_cap_to' r s)
          and (\<lambda>s. \<forall>cap \<in> set cs. s \<turnstile>' cap)
          and (\<lambda>s. \<forall>cap \<in> set cs. \<forall>r\<in>cte_refs' cap (irq_node' s). ex_cte_cap_to' r s)\<rbrace>
     decodeCNodeInvocation label args
     (CNodeCap w n w2 n2) cs
   \<lbrace>valid_cnode_inv'\<rbrace>, -"
  apply (rule decode_cnode_cases2[where label=label and args=args and exs=cs])
        \<comment> \<open>Move/Insert\<close>
        apply (simp add: decodeCNodeInvocation_def isCNodeCap_CNodeCap
                         split_def cnode_invok_case_cleanup unlessE_whenE
                   cong: if_cong bool.case_cong list.case_cong)
        apply (rule hoare_pre)
         apply (wp whenE_throwError_wp)
               apply (rule deriveCap_Null_helper)
               apply (simp add: imp_conjR)
               apply ((wp deriveCap_derived deriveCap_untyped_derived
                 | wp (once) hoare_drop_imps)+)[1]
              apply (wp whenE_throwError_wp getCTE_wp | wpc | simp(no_asm))+
           apply (rule_tac Q'="\<lambda>rv. invs' and cte_wp_at' (\<lambda>cte. cteCap cte = NullCap) destSlot
                                          and ex_cte_cap_to' destSlot"
                                   in hoare_strengthen_postE_R, wp)
           apply (clarsimp simp: cte_wp_at_ctes_of)
           apply (frule invs_valid_objs')
           apply (simp add: ctes_of_valid' valid_updateCapDataI
                            weak_derived_updateCapData capBadge_updateCapData_True
                            badge_derived_updateCapData
                            badge_derived_mask untyped_derived_eq_maskCapRights
                            untyped_derived_eq_updateCapData
                            untyped_derived_eq_refl)
           apply (auto simp:isCap_simps updateCapData_def)[1]
          apply (wp ensureEmptySlot_stronger | simp | wp (once) hoare_drop_imps)+
       \<comment> \<open>Revoke\<close>
       apply (simp add: decodeCNodeInvocation_def isCNodeCap_CNodeCap split_def
                        unlessE_whenE
                  cong: if_cong bool.case_cong list.case_cong)
       apply (rule hoare_pre)
        apply (wp lsfco_cte_at' | simp)+
       apply clarsimp
      \<comment> \<open>Delete\<close>
      apply (simp add: decodeCNodeInvocation_def isCNodeCap_CNodeCap split_def
                       unlessE_whenE
                 cong: if_cong bool.case_cong list.case_cong)
      apply (rule hoare_pre)
       apply (wp lsfco_cte_at' | simp)+
      apply clarsimp
     \<comment> \<open>SaveCaller\<close>
     apply (simp add: decodeCNodeInvocation_def isCNodeCap_CNodeCap split_def
                      unlessE_whenE)
     apply (rule hoare_pre)
      apply (wp lsfco_cte_at' | simp | wp (once) hoare_drop_imps)+
    \<comment> \<open>CancelBadgedSends\<close>
    apply (simp add: decodeCNodeInvocation_def isCNodeCap_CNodeCap split_def
                     unlessE_whenE)
    apply (rule hoare_pre)
     apply (wp whenE_throwError_wp getCTE_wp | simp)+
     apply (rule_tac Q'="\<lambda>rv s. invs' s \<and> cte_wp_at' (\<lambda>_. True) rv s" in hoare_strengthen_postE_R)
      apply (wp lsfco_cte_at')
     apply (simp add: cte_wp_at_ctes_of imp_ex hasCancelSendRights_not_Null)
     apply (clarsimp simp: ctes_of_valid' invs_valid_objs')
    apply (simp add: invs_valid_objs')
   \<comment> \<open>Rotate\<close>
   apply (simp add: decodeCNodeInvocation_def isCNodeCap_CNodeCap split_def
                    unlessE_def)
   apply (rule hoare_pre)
    apply (wp whenE_throwError_wp getCTE_wp ensureEmptySlot_stronger
                   | simp add: o_def)+
      apply (rule_tac Q'="\<lambda>rv s. cte_at' rv s \<and> cte_at' destSlot s
                              \<and> cte_at' srcSlot s \<and> ex_cte_cap_to' rv s
                              \<and> ex_cte_cap_to' destSlot s
                              \<and> invs' s" in hoare_strengthen_postE_R)
       apply (wp lsfco_cte_at')
      apply (clarsimp simp: cte_wp_at_ctes_of)
      apply (frule invs_valid_objs')
      apply (simp add: weak_derived_updateCapData capBadge_updateCapData_True
                       valid_updateCapDataI ctes_of_valid')
      apply (fastforce simp:isCap_simps updateCapData_def)
     apply (wp lsfco_cte_at')+
   apply clarsimp
  \<comment> \<open>Errors\<close>
  apply (elim disjE exE conjE,
         simp_all add: decodeCNodeInvocation_def isCNodeCap_CNodeCap
                       unlessE_whenE cnode_invok_case_cleanup
                split: list.split_asm list.split)
  by (auto simp: valid_def validE_def validE_R_def in_monad)

lemma decodeCNodeInvocation_inv[wp]:
  "\<lbrace>P\<rbrace>  decodeCNodeInvocation label args cap cs  \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (cases "\<not>isCNodeCap cap")
   apply (simp only: decodeCNodeInvocation_def Let_def split_def
                     fst_conv snd_conv, simp)
  apply (rule decode_cnode_cases2[where label=label and args=args and exs=cs])
        apply (simp_all add: decodeCNodeInvocation_def isCNodeCap_CNodeCap split_def
                             Let_def whenE_def unlessE_def cnode_invok_case_cleanup
                  split del: if_split cong del: if_cong)[6]
        apply (fold_subgoals (prefix))[6]
        subgoal premises prems
        by (safe intro!: hoare_pre[where P=P],
                (wp hoare_drop_imps | simp | wpcw)+)
  apply (elim disjE exE conjE,
         simp_all add: decodeCNodeInvocation_def isCNodeCap_CNodeCap
                       cnode_invok_case_cleanup unlessE_whenE
                split: list.split_asm split del: if_split)
  apply (simp_all split: list.split add: unlessE_whenE)
  apply safe
  apply (wp | simp)+
  done

text \<open>Various proofs about the two recursive deletion operations.
        These call out to various functions in Tcb and Ipc, and are
        thus better proved here than in CSpace_R.\<close>

text \<open>Proving the termination of rec_del\<close>

crunch cancel_ipc
  for typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  (wp: crunch_wps hoare_vcg_if_splitE simp: crunch_simps)

declare if_split [split]

text \<open>Proving desired properties about rec_del/cap_delete\<close>

declare of_nat_power [simp del]

(* FIXME: pull up *)
declare word_unat_power [symmetric, simp del]

text \<open>Proving desired properties about recursiveDelete/cteDelete\<close>

text \<open>Proving the termination of finaliseSlot\<close>

definition
  not_recursive_ctes :: "kernel_state \<Rightarrow> word32 set"
where
 "not_recursive_ctes s \<equiv> {ptr. \<exists>cap. cteCaps_of s ptr = Some cap
                             \<and> \<not> (isZombie cap \<and> capZombiePtr cap = ptr)}"

lemma not_recursive_ctes_wu [simp]:
  "not_recursive_ctes (ksWorkUnitsCompleted_update f s) = not_recursive_ctes s"
  by (simp add: not_recursive_ctes_def)

lemma not_recursive_ctes_irq_state_independent[simp, intro!]:
  "not_recursive_ctes (s \<lparr> ksMachineState := ksMachineState s \<lparr> irq_state := x \<rparr>\<rparr>) = not_recursive_ctes s"
  by (simp add: not_recursive_ctes_def)

lemma capSwap_not_recursive:
  "\<lbrace>\<lambda>s. card (not_recursive_ctes s) \<le> n
     \<and> cte_wp_at' (\<lambda>cte. \<not> (isZombie (cteCap cte) \<and> capZombiePtr (cteCap cte) = p1)) p1 s
     \<and> cte_wp_at' (\<lambda>cte. isZombie (cteCap cte) \<and> capZombiePtr (cteCap cte) = p1) p2 s
     \<and> p1 \<noteq> p2\<rbrace>
     capSwapForDelete p1 p2
   \<lbrace>\<lambda>rv s. card (not_recursive_ctes s) < n\<rbrace>"
  apply (simp add: not_recursive_ctes_def cteSwap_def capSwapForDelete_def)
  apply (wp | simp add: o_def | rule getCTE_cteCap_wp)+
  apply (simp add: cte_wp_at_ctes_of modify_map_def cteCaps_of_def
             cong: option.case_cong)
  apply (elim conjE exE)
  apply (simp cong: conj_cong)
  apply (erule order_less_le_trans[rotated])
  apply (rule psubset_card_mono)
   apply simp
  apply (rule psubsetI)
   apply clarsimp
  apply (rule_tac f="\<lambda>S. p1 \<in> S" in distinct_lemma)
  apply simp
  done

lemma updateCap_not_recursive:
  "\<lbrace>\<lambda>s. card (not_recursive_ctes s) \<le> n
         \<and> cte_wp_at' (\<lambda>cte. isZombie (cteCap cte) \<and> capZombiePtr (cteCap cte) = ptr
                                \<longrightarrow> isZombie cap \<and> capZombiePtr cap = ptr)
               ptr s\<rbrace>
     updateCap ptr cap
   \<lbrace>\<lambda>rv s. card (not_recursive_ctes s) \<le> n\<rbrace>"
  apply (simp add: not_recursive_ctes_def)
  apply wp
  apply clarsimp
  apply (erule order_trans[rotated])
  apply (rule card_mono, simp)
  apply clarsimp
  apply (simp add: modify_map_def split: if_split_asm)
  apply (clarsimp simp: cteCaps_of_def cte_wp_at_ctes_of)
  done

lemma suspend_ctes_of_thread:
  "\<lbrace>\<lambda>s. \<exists>node. ctes_of s x = Some (CTE (ThreadCap t) node)\<rbrace>
     suspend t
   \<lbrace>\<lambda>rv s. \<exists>node. ctes_of s x = Some (CTE (ThreadCap t) node)\<rbrace>"
  apply (rule hoare_chain)
  apply (rule suspend_cte_wp_at'[where P="(=) (ThreadCap t)" and p=x])
    apply (clarsimp simp add: finaliseCap_def Let_def isCap_simps)
   apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (case_tac cte, simp)
  done

lemma unbindNotification_ctes_of_thread:
  "\<lbrace>\<lambda>s. \<exists>node. ctes_of s x = Some (CTE (ThreadCap t) node)\<rbrace>
     unbindNotification t
   \<lbrace>\<lambda>rv s. \<exists>node. ctes_of s x = Some (CTE (ThreadCap t) node)\<rbrace>"
  by wp

lemma prepareThreadDelete_ctes_of[wp]:
  "prepareThreadDelete t \<lbrace>\<lambda>s. P (ctes_of s)\<rbrace>"
  by (wpsimp simp: prepareThreadDelete_def)

lemma prepareThreadDelete_ctes_of_thread:
  "\<lbrace>\<lambda>s. \<exists>node. ctes_of s x = Some (CTE (ThreadCap t) node)\<rbrace>
     prepareThreadDelete t
   \<lbrace>\<lambda>rv s. \<exists>node. ctes_of s x = Some (CTE (ThreadCap t) node)\<rbrace>"
  by wp

lemma suspend_not_recursive_ctes:
  "\<lbrace>\<lambda>s. P (not_recursive_ctes s)\<rbrace>
     suspend t
   \<lbrace>\<lambda>rv s. P (not_recursive_ctes s)\<rbrace>"
  apply (simp only: suspend_def not_recursive_ctes_def cteCaps_of_def)
  unfolding updateRestartPC_def
  apply (wp threadSet_ctes_of | simp add: unless_def del: o_apply)+
  apply (fold cteCaps_of_def)
  apply (wp cancelIPC_cteCaps_of)
  apply (clarsimp elim!: rsubst[where P=P] intro!: set_eqI)
  apply (clarsimp simp: cte_wp_at_ctes_of cteCaps_of_def)
  apply (auto simp: isCap_simps finaliseCap_def Let_def)
  done

lemma unbindNotification_not_recursive_ctes:
  "\<lbrace>\<lambda>s. P (not_recursive_ctes s)\<rbrace>
     unbindNotification t
   \<lbrace>\<lambda>rv s. P (not_recursive_ctes s)\<rbrace>"
  apply (simp only: not_recursive_ctes_def cteCaps_of_def)
  apply wp
  done

lemma prepareThreadDelete_not_recursive_ctes:
  "\<lbrace>\<lambda>s. P (not_recursive_ctes s)\<rbrace>
     prepareThreadDelete t
   \<lbrace>\<lambda>rv s. P (not_recursive_ctes s)\<rbrace>"
  by (wpsimp simp: not_recursive_ctes_def cteCaps_of_def)

definition
  finaliseSlot_recset :: "((word32 \<times> bool \<times> kernel_state) \<times> (word32 \<times> bool \<times> kernel_state)) set"
where
 "finaliseSlot_recset \<equiv>
    wf_sum (\<lambda>(slot, exposed, state). exposed)
      (inv_image (less_than <*lex*> less_than)
         (\<lambda>(x, exp, s). case ctes_of s x of
                      Some (CTE NullCap node) \<Rightarrow> (0, 0)
                    | Some (CTE (Zombie p zb n) node) \<Rightarrow>
                           (if p = x then 1 else 2, n)
                    | _ \<Rightarrow> (3, 0)))
      (measure (\<lambda>(x, exp, s). card (not_recursive_ctes s)))"

lemma finaliseSlot_recset_wf: "wf finaliseSlot_recset"
  unfolding finaliseSlot_recset_def
  by (intro wf_sum_wf wf_rdcall_finalise_ord_lift wf_measure
            wf_inv_image wf_lex_prod wf_less_than)

lemma in_preempt':
  "(Inr rv, s') \<in> fst (preemptionPoint s) \<Longrightarrow>
   \<exists>f g. s' = ksWorkUnitsCompleted_update f
      (s \<lparr> ksMachineState := ksMachineState s \<lparr> irq_state := g (irq_state (ksMachineState s)) \<rparr>\<rparr>)"
  apply (simp add: preemptionPoint_def alternative_def in_monad eq_commute
                   getActiveIRQ_def doMachineOp_def split_def
                   select_f_def select_def getWorkUnits_def setWorkUnits_def
                   modifyWorkUnits_def return_def returnOk_def
              split: option.splits if_splits)
   apply (erule disjE)
     apply (cases "workUnitsLimit \<le> ksWorkUnitsCompleted s + 1", drule (1) mp,
            rule exI[where x="\<lambda>x. 0"], rule exI[where x=Suc], force,
            rule exI[where x="\<lambda>x. x + 1"], rule exI[where x=id], force)+
  apply (rule exI[where x="\<lambda>x. x + 1"], rule exI[where x=id], force)
  done

lemma updateCap_implies_cte_at:
  "(rv, s') \<in> fst (updateCap ptr cap s)
      \<Longrightarrow> cte_at' ptr s"
  apply (clarsimp simp: updateCap_def in_monad)
  apply (frule in_inv_by_hoareD [OF getCTE_inv])
  apply (drule use_valid [OF _ getCTE_cte_wp_at], simp)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  done

lemma case_Zombie_assert_fold:
  "(case cap of Zombie ptr zb n \<Rightarrow> haskell_assertE (P ptr) str | _ \<Rightarrow> returnOk ())
       = assertE (isZombie cap \<longrightarrow> P (capZombiePtr cap))"
  by (cases cap, simp_all add: isCap_simps assertE_def)

termination finaliseSlot'
  apply (rule finaliseSlot'.termination,
         rule finaliseSlot_recset_wf)
   apply (simp add: finaliseSlot_recset_def wf_sum_def)
  apply (clarsimp simp: in_monad dest!: in_preempt')
  apply (drule in_inv_by_hoareD [OF isFinalCapability_inv])
  apply (frule use_valid [OF _ getCTE_cte_wp_at, OF _ TrueI])
  apply (drule in_inv_by_hoareD [OF getCTE_inv])
  apply (clarsimp simp: in_monad split: if_split_asm)
   apply (clarsimp simp: Let_def in_monad finaliseSlot_recset_def
                         wf_sum_def liftM_def
                         case_Zombie_assert_fold)
   apply (frule use_valid [OF _ getCTE_cte_wp_at, OF _ TrueI])
   apply (drule in_inv_by_hoareD [OF getCTE_inv])
   apply clarsimp
   apply (erule use_valid [OF _ capSwap_not_recursive])
   apply (simp add: cte_wp_at_ctes_of)
   apply (frule updateCap_implies_cte_at)
   apply (erule use_valid [OF _ hoare_vcg_conj_lift,
                           OF _ updateCap_not_recursive updateCap_ctes_of_wp])
   apply (clarsimp simp: cte_wp_at_ctes_of modify_map_def)
   apply (frule use_valid [OF _ finaliseCap_cases], simp)
   apply (case_tac rv, simp)
   apply (simp add: isCap_simps, elim conjE disjE exE)
      apply simp
     apply (clarsimp simp: finaliseCap_def Let_def isCap_simps in_monad
                           getThreadCSpaceRoot_def locateSlot_conv)
     apply (frule(1) use_valid [OF _ unbindNotification_ctes_of_thread, OF _ exI])
     apply (frule(1) use_valid [OF _ suspend_ctes_of_thread])
     apply (frule(1) use_valid [OF _ prepareThreadDelete_ctes_of_thread])
     apply clarsimp
     apply (erule use_valid [OF _ prepareThreadDelete_not_recursive_ctes])
     apply (erule use_valid [OF _ suspend_not_recursive_ctes])
     apply (erule use_valid [OF _ unbindNotification_not_recursive_ctes])
     apply simp
    apply (clarsimp simp: finaliseCap_def Let_def isCap_simps in_monad)
   apply (clarsimp simp: finaliseCap_def Let_def isCap_simps in_monad)
  apply (clarsimp simp: in_monad Let_def locateSlot_conv
                        finaliseSlot_recset_def wf_sum_def
                        cte_wp_at_ctes_of cong: if_cong)
  apply (clarsimp split: if_split_asm
                   simp: in_monad
                  dest!: in_getCTE)
    apply (erule use_valid [OF _ updateCap_ctes_of_wp])+
    apply (clarsimp simp: cte_wp_at_ctes_of modify_map_def)
    apply (case_tac ourCTE)
    apply (rename_tac cap node)
    apply (case_tac rv, simp)
    apply (rename_tac cap' node')
    apply (case_tac cap'; simp)
   apply (erule use_valid [OF _ updateCap_ctes_of_wp])+
   apply (clarsimp simp: cte_wp_at_ctes_of modify_map_def)
   apply (frule use_valid [OF _ finaliseCap_cases], simp)
   apply (case_tac ourCTE, case_tac rv,
          clarsimp simp: isCap_simps)
   apply (elim disjE conjE exE, simp_all)[1]
   apply (clarsimp simp: finaliseCap_def Let_def isCap_simps in_monad)
  apply (frule use_valid [OF _ finaliseCap_cases], simp)
  apply (case_tac rv, case_tac ourCTE)
  apply (clarsimp simp: isCap_simps cte_wp_at_ctes_of)
  apply (elim disjE conjE exE, simp_all)[1]
  done

lemmas finaliseSlot'_simps_ext =
    finaliseSlot'.simps [THEN ext [where f="finaliseSlot' slot exp" for slot exp]]

lemmas finalise_spec_induct = finaliseSlot'.induct[where P=
    "\<lambda>sl exp s. s \<turnstile> \<lbrace>P sl exp\<rbrace> finaliseSlot' sl exp \<lbrace>Q sl exp\<rbrace>,\<lbrace>E sl exp\<rbrace>" for P Q E]

lemma finaliseSlot'_preservation:
  assumes wp:
    "\<And>cap final. \<lbrace>P\<rbrace> finaliseCap cap final False \<lbrace>\<lambda>rv. P\<rbrace>"
    "\<And>sl opt. \<lbrace>P\<rbrace> emptySlot sl opt \<lbrace>\<lambda>rv. P\<rbrace>"
    "\<And>sl1 sl2. \<lbrace>P\<rbrace> capSwapForDelete sl1 sl2 \<lbrace>\<lambda>rv. P\<rbrace>"
    "\<And>sl cap. \<lbrace>P\<rbrace> updateCap sl cap \<lbrace>\<lambda>rv. P\<rbrace>"
    "\<And>f s. P (ksWorkUnitsCompleted_update f s) = P s"
  assumes irq: "irq_state_independent_H P"
  shows
    "st \<turnstile> \<lbrace>P\<rbrace> finaliseSlot' slot exposed \<lbrace>\<lambda>rv. P\<rbrace>, \<lbrace>\<lambda>rv. P\<rbrace>"
proof (induct rule: finalise_spec_induct)
  case (1 sl exp s)
  show ?case
    apply (rule hoare_pre_spec_validE)
     apply (subst finaliseSlot'_simps_ext)
     apply (simp only: split_def)
     apply wp
         apply (simp, wp wp)
        apply (wp "1.hyps")
          apply (unfold Let_def split_def fst_conv snd_conv
                        case_Zombie_assert_fold haskell_fail_def)
          apply (wp wp preemptionPoint_inv| simp add: o_def irq)+
           apply (wp hoare_drop_imps)
          apply (wp wp | simp)+
               apply (wp hoare_drop_imps | simp(no_asm))+
            apply (wp wp)[1]
           apply (simp(no_asm))
           apply (rule "1.hyps", (assumption | rule refl)+)
          apply (wp wp hoare_drop_imps isFinalCapability_inv
                    | simp add: locateSlot_conv)+
    done
qed

lemmas finaliseSlot_preservation
    = validE_valid [OF use_spec(2) [OF finaliseSlot'_preservation],
                    folded finaliseSlot_def]

lemma cteDelete_preservation:
  assumes wp:
    "\<And>cap final. \<lbrace>P\<rbrace> finaliseCap cap final False \<lbrace>\<lambda>rv. P\<rbrace>"
    "\<And>sl opt. \<lbrace>P\<rbrace> emptySlot sl opt \<lbrace>\<lambda>rv. P\<rbrace>"
    "\<And>sl1 sl2. \<lbrace>P\<rbrace> capSwapForDelete sl1 sl2 \<lbrace>\<lambda>rv. P\<rbrace>"
    "\<And>sl cap. \<lbrace>P\<rbrace> updateCap sl cap \<lbrace>\<lambda>rv. P\<rbrace>"
    "\<And>f s. P (ksWorkUnitsCompleted_update f s) = P s"
  assumes irq: "irq_state_independent_H P"
  shows
    "\<lbrace>P\<rbrace> cteDelete p e \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp add: cteDelete_def whenE_def split_def)
  apply (wp wp)
  apply (simp only: simp_thms cases_simp)
  apply (wp finaliseSlot_preservation wp | simp add: irq)+
  done

crunch capSwapForDelete
  for aligned'[wp]: pspace_aligned'
crunch capSwapForDelete
  for distinct'[wp]: pspace_distinct'

lemma cte_wp_at_ctes_ofI:
  "\<lbrakk> cte_wp_at' ((=) cte) ptr s \<rbrakk> \<Longrightarrow> ctes_of s ptr = Some cte"
  by (rule ctes_of_eq_cte_wp_at')

declare modify_map_dom[simp]

(* subsumes  update_prev_next_trancl *)
lemma modify_map_next_trancl:
  assumes nxt: "m \<turnstile> x \<leadsto>\<^sup>+ y"
  and     inv: "\<And>cte. mdbNext (cteMDBNode (f cte)) = mdbNext (cteMDBNode cte)"
  shows "(modify_map m ptr f) \<turnstile> x \<leadsto>\<^sup>+ y"
proof (cases "m ptr")
  case None
  thus ?thesis using nxt
    by (simp add: modify_map_def)
next
  case (Some cte)
  let ?m = "m(ptr \<mapsto> f cte)"

  from nxt have "?m \<turnstile> x \<leadsto>\<^sup>+ y"
  proof induct
    case (base y)
    thus ?case using Some inv r_into_trancl next_unfold'
      by fastforce
  next
    case (step q r)
    show ?case
    proof (rule trancl_into_trancl)
      show "?m \<turnstile> q \<leadsto> r" using step(2) Some inv
        by (simp only: mdb_next_update, clarsimp simp: next_unfold')
    qed fact+
  qed
  thus ?thesis using Some
    by (simp add: modify_map_def)
qed


(* subsumes update_prev_next_trancl2 *)
lemma modify_map_next_trancl2:
  assumes nxt: "(modify_map m ptr f) \<turnstile> x \<leadsto>\<^sup>+ y"
  and     inv: "\<And>cte. mdbNext (cteMDBNode (f cte)) = mdbNext (cteMDBNode cte)"
  shows   "m \<turnstile> x \<leadsto>\<^sup>+ y"
proof (cases "m ptr")
  case None
  thus ?thesis using nxt
    by (simp add: modify_map_def)
next
  case (Some cte)
  let ?m = "m(ptr \<mapsto> f cte)"

  from nxt have "m \<turnstile> x \<leadsto>\<^sup>+ y"
  proof induct
    case (base y)
    thus ?case using Some inv
      by (auto intro!: r_into_trancl
        simp: modify_map_def mdb_next_update next_unfold' split: if_split_asm)
  next
    case (step q r)
    show ?case
    proof
      show "m \<turnstile> q \<leadsto> r" using step(2) Some inv
      by (auto simp: modify_map_def mdb_next_update next_unfold' split: if_split_asm)
    qed fact+
  qed
  thus ?thesis using Some
    by (simp add: modify_map_def)
qed

lemma modify_map_next_trancl_iff:
  assumes inv: "\<And>cte. mdbNext (cteMDBNode (f cte)) = mdbNext (cteMDBNode cte)"
  shows  "(modify_map m ptr f) \<turnstile> x \<leadsto>\<^sup>+ y = m \<turnstile> x \<leadsto>\<^sup>+ y"
  using inv
  by (auto intro: modify_map_next_trancl  modify_map_next_trancl2)

lemma mdb_chain_0_cap_update:
  "mdb_chain_0 (modify_map ctemap ptr (cteCap_update f)) =
  mdb_chain_0 ctemap"
  unfolding mdb_chain_0_def
  by (auto simp: modify_map_next_trancl_iff)

lemma modify_map_dlist:
  assumes nxt: "valid_dlist m"
  and     inv: "\<And>cte. cteMDBNode (f cte) = cteMDBNode cte"
  shows "valid_dlist (modify_map m ptr f)"
proof (cases "m ptr")
  case None
  thus ?thesis using nxt
    by (simp add: modify_map_def)
next
  case (Some ptrcte)
  let ?m = "m(ptr \<mapsto> f ptrcte)"

  have "valid_dlist ?m"
  proof
    fix p cte
    assume cp: "?m p = Some cte" and n0: "mdbPrev (cteMDBNode cte) \<noteq> 0"
    let ?thesis =
      "\<exists>cte'.(m(ptr \<mapsto> f ptrcte)) (mdbPrev (cteMDBNode cte)) = Some cte' \<and>
      mdbNext (cteMDBNode cte') = p"

    {
      assume peq: "p = ptr"

      hence mdb: "cteMDBNode cte = cteMDBNode ptrcte" using cp Some
        by (clarsimp simp: inv)

      hence "\<exists>cte'. m (mdbPrev (cteMDBNode cte)) = Some cte' \<and> mdbNext (cteMDBNode cte') = p"
        using nxt Some n0 peq
        by (auto elim: valid_dlistEp)
      hence ?thesis using peq mdb cp Some
        by (cases "ptr = mdbPrev (cteMDBNode cte)") simp_all
    } moreover
    {
      assume pne: "p \<noteq> ptr"
      hence ?thesis using cp Some nxt n0
        by (cases "(mdbPrev (cteMDBNode cte)) = ptr") (auto elim: valid_dlistEp simp: inv)
    }
    ultimately show ?thesis by (cases "p = ptr") auto
  next
    fix p cte
    assume cp: "?m p = Some cte" and n0: "mdbNext (cteMDBNode cte) \<noteq> 0"
    let ?thesis =
      "\<exists>cte'.(m(ptr \<mapsto> f ptrcte)) (mdbNext (cteMDBNode cte)) = Some cte' \<and>
      mdbPrev (cteMDBNode cte') = p"

    {
      assume peq: "p = ptr"

      hence mdb: "cteMDBNode cte = cteMDBNode ptrcte" using cp Some
        by (clarsimp simp: inv)

      hence "\<exists>cte'. m (mdbNext (cteMDBNode cte)) = Some cte' \<and> mdbPrev (cteMDBNode cte') = p"
        using nxt Some n0 peq
        by (auto elim: valid_dlistEn)
      hence ?thesis using peq mdb cp Some
        by (cases "ptr = mdbNext (cteMDBNode cte)") simp_all
    } moreover
    {
      assume pne: "p \<noteq> ptr"
      hence ?thesis using cp Some nxt n0
        by (cases "(mdbNext (cteMDBNode cte)) = ptr") (auto elim: valid_dlistEn simp: inv)
    }
    ultimately show ?thesis by (cases "p = ptr") auto
  qed
  thus ?thesis using Some
    by (simp add: modify_map_def)
qed

lemma modify_map_dlist2:
  assumes nxt: "valid_dlist (modify_map m ptr f)"
  and     inv: "\<And>cte. cteMDBNode (f cte) = cteMDBNode cte"
  shows  "valid_dlist m"
proof (cases "m ptr")
  case None
  thus ?thesis using nxt
    by (simp add: modify_map_def)
next
  case (Some ptrcte)
  let ?m = "modify_map m ptr f"

  have "valid_dlist m"
  proof
    fix p cte
    assume cp: "m p = Some cte" and n0: "mdbPrev (cteMDBNode cte) \<noteq> 0"
    let ?thesis =
      "\<exists>cte'. m (mdbPrev (cteMDBNode cte)) = Some cte' \<and> mdbNext (cteMDBNode cte') = p"

    {
      assume peq: "p = ptr"

      hence mdb: "cteMDBNode cte = cteMDBNode ptrcte" using cp Some
        by (clarsimp simp: inv)

      hence "\<exists>cte'. ?m (mdbPrev (cteMDBNode cte)) = Some cte' \<and> mdbNext (cteMDBNode cte') = p"
        using nxt Some n0 peq
        by (auto elim: valid_dlistEp [where p = ptr] simp: modify_map_same inv)
      hence ?thesis using peq cp Some
        by (cases "ptr = mdbPrev (cteMDBNode cte)") (clarsimp simp: inv modify_map_same modify_map_other)+
    } moreover
    {
      assume pne: "p \<noteq> ptr"
      hence ?thesis using cp Some nxt n0
        by (cases "(mdbPrev (cteMDBNode cte)) = ptr") (auto elim!: valid_dlistEp simp: inv modify_map_apply)
    }
    ultimately show ?thesis by (cases "p = ptr") auto
  next
    fix p cte
    assume cp: "m p = Some cte" and n0: "mdbNext (cteMDBNode cte) \<noteq> 0"
    let ?thesis =
      "\<exists>cte'. m (mdbNext (cteMDBNode cte)) = Some cte' \<and> mdbPrev (cteMDBNode cte') = p"

    {
      assume peq: "p = ptr"

      hence mdb: "cteMDBNode cte = cteMDBNode ptrcte" using cp Some
        by (clarsimp simp: inv)

      hence "\<exists>cte'. ?m (mdbNext (cteMDBNode cte)) = Some cte' \<and> mdbPrev (cteMDBNode cte') = p"
        using nxt Some n0 peq
        by (auto elim: valid_dlistEn [where p = ptr] simp: modify_map_same inv)
      hence ?thesis using peq cp Some
        by (cases "ptr = mdbNext (cteMDBNode cte)") (clarsimp simp: inv modify_map_same modify_map_other)+
    } moreover
    {
      assume pne: "p \<noteq> ptr"
      hence ?thesis using cp Some nxt n0
        by (cases "(mdbNext (cteMDBNode cte)) = ptr") (auto elim!: valid_dlistEn simp: inv modify_map_apply)
    }
    ultimately show ?thesis by (cases "p = ptr") auto
  qed
  thus ?thesis using Some
    by (simp add: modify_map_def)
qed

lemma modify_map_dlist_iff:
  assumes inv: "\<And>cte. cteMDBNode (f cte) = cteMDBNode cte"
  shows  "valid_dlist (modify_map m ptr f) = valid_dlist m"
  using inv
  by (auto intro: modify_map_dlist modify_map_dlist2)

lemma mdb_chain_0_modify_map_inv:
  "\<lbrakk> mdb_chain_0 m; \<And>cte. mdbNext (cteMDBNode (f cte)) = mdbNext (cteMDBNode cte) \<rbrakk> \<Longrightarrow> mdb_chain_0 (modify_map m ptr f)"
  unfolding mdb_chain_0_def
  by (auto simp: modify_map_next_trancl_iff)

lemma mdb_chain_0_modify_map_replace:
  assumes unf: "mdb_chain_0 (modify_map m p (cteMDBNode_update (mdbNext_update (%_. (mdbNext node)))))"
  shows "mdb_chain_0 (modify_map m p (cteMDBNode_update (\<lambda>m. node)))"
proof -
  have "modify_map m p (cteMDBNode_update (\<lambda>m. node)) =
    modify_map (modify_map (modify_map (modify_map m p (cteMDBNode_update (mdbNext_update (%_. (mdbNext node))))) p
          (cteMDBNode_update (mdbPrev_update (%_. (mdbPrev node))))) p
       (cteMDBNode_update (mdbRevocable_update (%_. (mdbRevocable node))))) p
       (cteMDBNode_update (mdbFirstBadged_update (%_. (mdbFirstBadged node))))"
    apply (cases node)
    apply (cases "m p")
     apply (simp add: modify_map_None)
    apply (case_tac a)
    apply (rename_tac mdbnode)
    apply (case_tac mdbnode)
    apply (clarsimp simp add: next_update_is_modify [symmetric])
    done

  thus ?thesis
    apply simp
    apply (rule mdb_chain_0_modify_map_inv)
     apply (rule mdb_chain_0_modify_map_inv)
      apply (rule mdb_chain_0_modify_map_inv [OF unf])
      apply simp_all
   done
qed

lemmas mdb_chain_0_mm_rep_next =
  mdb_chain_0_modify_map_replace [OF mdb_chain_0_modify_map_next]

lemma setCTE_cte_wp_at_other:
 "\<lbrace>cte_wp_at' P p and (\<lambda>s. ptr \<noteq> p)\<rbrace>
  setCTE ptr cte
  \<lbrace>\<lambda>uu s. cte_wp_at' P p s\<rbrace>"
  apply (simp add: cte_wp_at_ctes_of)
  apply wp
  apply (clarsimp simp: cte_wp_at_ctes_of)
  done

lemma updateMDB_cte_wp_at_other:
 "\<lbrace>cte_wp_at' P p and (\<lambda>s. m \<noteq> p)\<rbrace>
  updateMDB m f
  \<lbrace>\<lambda>uu. cte_wp_at' P p\<rbrace>"
  unfolding updateMDB_def
  apply simp
  apply safe
   apply wp
   apply simp
  apply (wp setCTE_cte_wp_at_other)
  done

(* CLAG from _next *)
lemma mdb_chain_0_modify_map_0:
  assumes chain: "mdb_chain_0 m"
  and      no0:  "no_0 m"
  shows
  "mdb_chain_0 (modify_map m ptr (cteMDBNode_update (mdbNext_update (%_. 0))))"
  (is "mdb_chain_0 ?M")
  unfolding mdb_chain_0_def
proof
  fix x
  assume "x \<in> dom ?M"
  hence xd: "x \<in> dom m"
    by (clarsimp simp: modify_map_def dom_def split: if_split_asm)
  hence x0: "m \<turnstile> x \<leadsto>\<^sup>+ 0" using chain unfolding mdb_chain_0_def by simp

  show "?M \<turnstile> x \<leadsto>\<^sup>+ 0"
  proof (cases "m ptr")
    case None
    thus ?thesis
      by (simp add: modify_map_def) (rule x0)
  next
    case (Some cte)
    show ?thesis
    proof (cases "m \<turnstile> x \<leadsto>\<^sup>* ptr")
      case False
      thus ?thesis
        apply (subst next_update_is_modify [symmetric, OF _ refl])
        apply (rule Some)
        apply (erule mdb_trancl_other_update [OF x0])
        done
    next
      case True
      hence "?M \<turnstile> x \<leadsto>\<^sup>* ptr"
        apply (subst next_update_is_modify [symmetric, OF _ refl])
        apply (rule Some)
        apply (erule next_rtrancl_tranclE)
        apply simp
        apply (rule trancl_into_rtrancl)
        apply (erule no_loops_upd_last [OF mdb_chain_0_no_loops [OF chain no0]])
        done
      moreover have "?M \<turnstile> ptr \<leadsto> 0"
        apply (subst next_update_is_modify [symmetric, OF _ refl])
        apply (rule Some)
        apply (simp add: mdb_next_update)
        done
      ultimately show ?thesis by simp
    qed
  qed
qed

lemma no_0_lhs_tranclI: "\<lbrakk> no_0 m; dest \<noteq> 0 \<rbrakk> \<Longrightarrow> \<not> m \<turnstile> 0 \<leadsto>\<^sup>* dest"
  apply rule
  apply (erule next_rtrancl_tranclE)
   apply simp
  apply (drule (1) no_0_lhs_trancl)
   apply simp
   done

lemma no_next_prev_rtrancl:
  assumes  c0: "valid_mdb_ctes m"
  and src: "m src = Some (CTE cap src_node)"
  and "mdbPrev src_node \<noteq> 0"
  shows   "\<not> m \<turnstile> mdbNext src_node \<leadsto>\<^sup>* mdbPrev src_node"
proof
  assume asm: "m \<turnstile> mdbNext src_node \<leadsto>\<^sup>* mdbPrev src_node"

  from c0 have n0: "no_0 m" ..
  from c0 have chain: "mdb_chain_0 m" ..

  have  "m \<turnstile> src \<leadsto>\<^sup>+ mdbPrev src_node"
    using src
    by - (rule rtrancl_into_trancl2 [OF _ asm], clarsimp simp: next_unfold')

  moreover
  from c0 have vd: "valid_dlist m" ..
  have "m \<turnstile> mdbPrev src_node \<leadsto> src" by (rule prev_leadstoI [OF _ _ vd]) fact+
  ultimately have "m \<turnstile> src \<leadsto>\<^sup>+ src" ..
  thus False using mdb_chain_0_no_loops [OF chain n0]
    by (simp add: no_loops_trancl_simp)
qed

lemma ctes_of_strng:
  "(\<exists>cte. ctes_of s ptr = Some cte \<and> P cte)
  \<longrightarrow> (\<exists>cte. cte_wp_at' ((=) cte) ptr s \<and> P cte)"
  by (clarsimp simp: cte_wp_at_ctes_of)

lemma updateCap_valid_cap [wp]:
  "\<lbrace>valid_cap' cap\<rbrace> updateCap ptr cap' \<lbrace>\<lambda>r. valid_cap' cap\<rbrace>"
  unfolding updateCap_def
  by (wp setCTE_valid_cap getCTE_wp) (clarsimp dest!: cte_at_cte_wp_atD)

lemma mdb_chain_0_trancl:
  assumes chain: "mdb_chain_0 m"
  and   n0: "no_0 m"
  and   ab: "m \<turnstile> a \<leadsto>\<^sup>+ b"
  shows "m \<turnstile> b \<leadsto>\<^sup>* 0"
  using ab
proof induct
  case (base y)
  thus ?case using chain
    by (clarsimp simp: next_unfold') (erule (1) mdb_chain_0_nextD)
next
  case (step y z)
  thus ?case using n0
    apply -
    apply (erule next_rtrancl_tranclE)
     apply (simp add: next_unfold')
    apply (drule tranclD [where x = y])
    apply clarsimp
    apply (drule (1) next_single_value)
    apply simp
    done
qed

lemma mdb_chain_0_cases [consumes 3, case_names srcdest destsrc indep]:
  assumes chain: "mdb_chain_0 m"
  and   no: "no_0 m"
  and   ds: "dest \<noteq> src"
  and  srcdest: "\<lbrakk> m \<turnstile> src \<leadsto>\<^sup>+ dest; \<not> m \<turnstile> dest \<leadsto>\<^sup>* src; m \<turnstile> dest \<leadsto>\<^sup>* 0 \<rbrakk> \<Longrightarrow> R"
  and  destsrc: "\<lbrakk> m \<turnstile> dest \<leadsto>\<^sup>+ src; \<not> m \<turnstile> src \<leadsto>\<^sup>* dest; m \<turnstile> src \<leadsto>\<^sup>* 0 \<rbrakk> \<Longrightarrow> R"
  and  neither: "\<lbrakk>  \<not> m \<turnstile> src \<leadsto>\<^sup>+ dest; \<not> m \<turnstile> dest \<leadsto>\<^sup>+ src \<rbrakk> \<Longrightarrow> R"
  shows "R"
proof (cases "m \<turnstile> src \<leadsto>\<^sup>+ dest")
  case True

  thus ?thesis
  proof (rule srcdest)
    show "\<not> m \<turnstile> dest \<leadsto>\<^sup>* src" by (rule no_loops_tranclE [OF mdb_chain_0_no_loops]) fact+

    show "m \<turnstile> dest \<leadsto>\<^sup>* 0"
      by (rule mdb_chain_0_trancl) fact+
  qed
next
  case False

  note F = False

  show ?thesis
  proof (cases "m \<turnstile> dest \<leadsto>\<^sup>+ src")
    case True
    thus ?thesis
    proof (rule destsrc)
      show "\<not> m \<turnstile> src \<leadsto>\<^sup>* dest" using False ds
        by (clarsimp elim!: next_rtrancl_tranclE)
      show "m \<turnstile> src \<leadsto>\<^sup>* 0"
        by (rule mdb_chain_0_trancl) fact+
    qed
  next
    case False
    with F show ?thesis
      by (rule neither)
  qed
qed

lemma next_fold:
  "\<lbrakk> m a = Some cte; mdbNext (cteMDBNode cte) = b\<rbrakk> \<Longrightarrow> m \<turnstile> a \<leadsto> b"
  by (clarsimp simp: next_unfold')


lemma cteMDBNode_update_comp [simp]:
  "(cteMDBNode_update f \<circ> cteMDBNode_update g) = cteMDBNode_update (f \<circ> g)"
  by rule (case_tac x, simp)

lemma modify_map_lhs_trancl:
  "\<lbrakk> m p = Some cte; \<not> m \<turnstile> mdbNext (cteMDBNode (f cte)) \<leadsto>\<^sup>* p \<rbrakk> \<Longrightarrow>
  modify_map m p f \<turnstile> p \<leadsto>\<^sup>+ x = m \<turnstile> mdbNext (cteMDBNode (f cte)) \<leadsto>\<^sup>* x"
  by (clarsimp simp: next_update_is_modify [symmetric] intro!: next_update_lhs_trancl)

lemma modify_map_lhs_rtrancl:
  "\<lbrakk> m p = Some cte; \<not> m \<turnstile> mdbNext (cteMDBNode (f cte)) \<leadsto>\<^sup>* p \<rbrakk> \<Longrightarrow>
  modify_map m p f \<turnstile> p \<leadsto>\<^sup>* x = (x = p \<or> m \<turnstile> mdbNext (cteMDBNode (f cte)) \<leadsto>\<^sup>* x)"
  apply rule
   apply (erule next_rtrancl_tranclE)
    apply simp
  apply (drule (2) iffD1 [OF modify_map_lhs_trancl])
  apply simp
   apply (erule disjE)
    apply simp
  apply (drule (2) iffD2 [OF modify_map_lhs_trancl])
  apply (erule trancl_into_rtrancl)
  done

lemma next_prev:
  assumes cte: "m p = Some cte"
  and      vd: "valid_dlist m"
  and     no0: "no_0 m"
  and     nxt: "m \<turnstile> q \<leadsto> p"
  shows   "q = mdbPrev (cteMDBNode cte)"
proof -
  from no0 have p0: "p \<noteq> 0" using cte unfolding no_0_def
    by - (rule, clarsimp)

  thus ?thesis
    using nxt vd cte
    apply -
    apply (simp add: next_unfold')
    apply (erule exE conjE)+
    apply (erule (1) valid_dlistEn, fastforce)
    apply simp
    done
qed

declare modify_map_ndom[simp]

lemma mdb_trancl_other_update_iff:
  "\<not> m \<turnstile> x \<leadsto>\<^sup>* p \<Longrightarrow> m(p \<mapsto> cte) \<turnstile> x \<leadsto>\<^sup>+ y = m \<turnstile> x \<leadsto>\<^sup>+ y"
  by (auto intro:  mdb_trancl_other_update mdb_trancl_update_other)



lemma modify_map_trancl_other_iff:
  "\<not> m \<turnstile> x \<leadsto>\<^sup>* p \<Longrightarrow> modify_map m p f \<turnstile> x \<leadsto>\<^sup>+ y = m \<turnstile> x \<leadsto>\<^sup>+ y"
  apply -
  apply (cases "m p")
   apply (simp add: modify_map_None)
  apply (subst next_update_is_modify [symmetric])
    apply assumption
   apply simp
  apply (erule  mdb_trancl_other_update_iff)
  done

lemma next_modify_map_trancl_last:
  assumes chain: "mdb_chain_0 m"
  and     no0:   "no_0 m"
  and     nxt: "m \<turnstile> x \<leadsto>\<^sup>+ p"
  shows   "modify_map m p f \<turnstile> x \<leadsto>\<^sup>+ p"
proof -
  note noloop = mdb_chain_0_no_loops [OF chain no0]

  from noloop nxt have xp: "x \<noteq> p"
    by (clarsimp dest!: neg_no_loopsI)

  from nxt show ?thesis using xp
  proof (induct rule: converse_trancl_induct')
    case (base y)
    hence "modify_map m p f \<turnstile> y \<leadsto> p"
      by (clarsimp simp: next_unfold' modify_map_other)

    thus ?case ..
  next
    case (step y z)

    from noloop step have xp: "z \<noteq> p"
      by (clarsimp dest!: neg_no_loopsI)

    hence "modify_map m p f \<turnstile> y \<leadsto> z" using step
      by (clarsimp simp: next_unfold' modify_map_other)
    moreover from xp have "modify_map m p f \<turnstile> z \<leadsto>\<^sup>+ p" using step.hyps by simp
    ultimately show ?case by (rule trancl_into_trancl2)
  qed
qed

lemma next_modify_map_trancl_last2:
  assumes chain: "mdb_chain_0 (modify_map m p f)"
  and     no0:   "no_0 m"
  and     nxt:   "modify_map m p f \<turnstile> x \<leadsto>\<^sup>+ p"
  shows "m \<turnstile> x \<leadsto>\<^sup>+ p"
proof -
  let ?m = "modify_map m p f"
  have no0': "no_0 ?m" using no0 by simp
  note noloop = mdb_chain_0_no_loops [OF chain no0']

  from noloop nxt have xp: "x \<noteq> p"
    by (clarsimp dest!: neg_no_loopsI)

  from nxt show ?thesis using xp
  proof (induct rule: converse_trancl_induct')
    case (base y)
    hence "m \<turnstile> y \<leadsto> p"
      by (clarsimp simp: next_unfold' modify_map_other)

    thus ?case ..
  next
    case (step y z)

    from noloop step have xp: "z \<noteq> p"
      by (clarsimp dest!: neg_no_loopsI)

    hence "m \<turnstile> y \<leadsto> z" using step
      by (clarsimp simp: next_unfold' modify_map_other)
    moreover from xp have "m \<turnstile> z \<leadsto>\<^sup>+ p" using step.hyps by simp
    ultimately show ?case by (rule trancl_into_trancl2)
  qed
qed

lemma next_modify_map_trancl_last_iff:
  assumes c1: "mdb_chain_0 m"
  and   chain: "mdb_chain_0 (modify_map m p f)"
  and     no0:   "no_0 m"
  shows  "modify_map m p f \<turnstile> x \<leadsto>\<^sup>+ p = m \<turnstile> x \<leadsto>\<^sup>+ p"
  using c1 chain no0
  by (auto intro: next_modify_map_trancl_last next_modify_map_trancl_last2)

lemma next_modify_map_last:
  shows "x \<noteq> p \<Longrightarrow> modify_map m p f \<turnstile> x \<leadsto> p = m \<turnstile> x \<leadsto> p"
  by (clarsimp simp: next_unfold' modify_map_other)

lemma next_rtrancl_nx:
  assumes node: "m ptr = Some (CTE cap node)"
  and       nl: "m \<turnstile> ptr \<leadsto>\<^sup>+ ptr'"
  shows "m \<turnstile> mdbNext node \<leadsto>\<^sup>* ptr'"
  using nl node
  by (clarsimp dest!: tranclD elim!: next_rtrancl_tranclE simp: next_unfold')

lemma next_trancl_nx:
  assumes node: "m ptr = Some (CTE cap node)"
  and       nl: "m \<turnstile> ptr \<leadsto>\<^sup>+ ptr'"
  and      neq: "mdbNext node \<noteq> ptr'"
  shows "m \<turnstile> mdbNext node \<leadsto>\<^sup>+ ptr'"
  using nl node neq
  by (clarsimp dest!: tranclD elim!: next_rtrancl_tranclE simp: next_unfold')

lemma next_rtrancl_xp:
  assumes node: "m ptr' = Some (CTE cap node)"
  and      vd: "valid_dlist m"
  and     no0: "no_0 m"
  and       nl: "m \<turnstile> ptr \<leadsto>\<^sup>+ ptr'"
  shows "m \<turnstile> ptr \<leadsto>\<^sup>* mdbPrev node"
  using nl node
  apply -
  apply (drule tranclD2)
  apply clarsimp
  apply (drule (1) next_prev [OF _ vd no0])
  apply simp
  done

lemma next_trancl_xp:
  assumes node: "m ptr' = Some (CTE cap node)"
  and      vd: "valid_dlist m"
  and     no0: "no_0 m"
  and     neq: "mdbPrev node \<noteq> ptr"
  and       nl: "m \<turnstile> ptr \<leadsto>\<^sup>+ ptr'"
  shows "m \<turnstile> ptr \<leadsto>\<^sup>+ mdbPrev node"
  using neq node nl
  apply -
  apply (drule (1) next_rtrancl_xp [OF _ vd no0])
  apply (erule next_rtrancl_tranclE)
   apply simp
  apply simp
  done

lemma next_trancl_np:
  assumes node: "m ptr = Some (CTE cap node)"
  and    node': "m ptr' = Some (CTE cap' node')"
  and      vd: "valid_dlist m"
  and     no0: "no_0 m"
  and     neq: "mdbPrev node' \<noteq> ptr"
  and    neq': "mdbNext node \<noteq> mdbPrev node'"
  and       nl: "m \<turnstile> ptr \<leadsto>\<^sup>+ ptr'"
  shows "m \<turnstile> mdbNext node \<leadsto>\<^sup>+ mdbPrev node'"
  by (rule next_trancl_nx [OF _ next_trancl_xp]) fact+

lemma neg_next_trancl_nx:
  assumes node: "m ptr = Some (CTE cap node)"
  and       nl: "\<not> m \<turnstile> ptr \<leadsto>\<^sup>+ ptr'"
  shows "\<not> m \<turnstile> mdbNext node \<leadsto>\<^sup>+ ptr'"
  using nl
proof (rule contrapos_nn)
  assume "m \<turnstile> mdbNext node \<leadsto>\<^sup>+ ptr'"
  show "m \<turnstile> ptr \<leadsto>\<^sup>+ ptr'"
  proof (rule trancl_into_trancl2)
    show "m \<turnstile> ptr \<leadsto> mdbNext node" using node by (rule next_fold, simp)
  qed fact+
qed

lemma neg_next_rtrancl_nx:
  assumes node: "m ptr = Some (CTE cap node)"
  and       nl: "\<not> m \<turnstile> ptr \<leadsto>\<^sup>+ ptr'"
  shows "\<not> m \<turnstile> mdbNext node \<leadsto>\<^sup>* ptr'"
  using nl
proof (rule contrapos_nn)
  assume "m \<turnstile> mdbNext node \<leadsto>\<^sup>* ptr'"
  show "m \<turnstile> ptr \<leadsto>\<^sup>+ ptr'"
  proof (rule rtrancl_into_trancl2)
    show "m \<turnstile> ptr \<leadsto> mdbNext node" using node by (rule next_fold, simp)
  qed fact+
qed

lemma dom_into_not0 [intro?]:
  "\<lbrakk> no_0 m; p \<in> dom m \<rbrakk> \<Longrightarrow> p \<noteq> 0"
  by (rule, clarsimp)

lemma neg_next_trancl_xp:
  assumes node: "m ptr' = Some (CTE cap node)"
  and      dom: "mdbPrev node \<in> dom m"
  and      no0: "no_0 m"
  and       vd: "valid_dlist m"
  and       nl: "\<not> m \<turnstile> ptr \<leadsto>\<^sup>+ ptr'"
  shows "\<not> m \<turnstile> ptr \<leadsto>\<^sup>+ mdbPrev node"
  using nl
proof (rule contrapos_nn)
  assume "m \<turnstile> ptr \<leadsto>\<^sup>+ mdbPrev node"

  show "m \<turnstile> ptr \<leadsto>\<^sup>+ ptr'"
  proof (rule trancl_into_trancl)
    have "mdbPrev node \<noteq> 0" using assms by auto
    thus "m \<turnstile> mdbPrev node \<leadsto> ptr'" using vd node
      apply -
      apply (erule (1) valid_dlistEp)
      apply simp
      apply (rule next_fold)
      apply simp
      apply simp
      done
  qed fact+
qed

lemma neg_next_trancl_np:
  assumes node: "m ptr = Some (CTE cap node)"
  and    node': "m ptr' = Some (CTE cap' node')"
  and      dom: "mdbPrev node' \<in> dom m"
  and      no0: "no_0 m"
  and       vd: "valid_dlist m"
  and       nl: "\<not> m \<turnstile> ptr \<leadsto>\<^sup>+ ptr'"
  shows "\<not> m \<turnstile> mdbNext node \<leadsto>\<^sup>+ mdbPrev node'"
  by (rule neg_next_trancl_nx [OF _ neg_next_trancl_xp]) fact+

lemma neg_next_rtrancl_np:
  assumes node: "m ptr = Some (CTE cap node)"
  and    node': "m ptr' = Some (CTE cap' node')"
  and      dom: "mdbPrev node' \<in> dom m"
  and      no0: "no_0 m"
  and       vd: "valid_dlist m"
  and       nl: "\<not> m \<turnstile> ptr \<leadsto>\<^sup>+ ptr'"
  shows "\<not> m \<turnstile> mdbNext node \<leadsto>\<^sup>* mdbPrev node'"
  by (rule neg_next_rtrancl_nx [OF _ neg_next_trancl_xp]) fact+

lemma neg_next_trancl_trancl:
  assumes nxt: "m \<turnstile> a \<leadsto>\<^sup>* a'"
  and      ab: "\<not> m \<turnstile> b \<leadsto>\<^sup>* a'"
  and      nl: "\<not> m \<turnstile> a' \<leadsto>\<^sup>* b"
  shows "\<not> m \<turnstile> a \<leadsto>\<^sup>+ b"
  using nl nxt
  apply -
  apply (erule contrapos_nn)
  apply (erule next_rtrancl_tranclE)
   apply simp
  apply (erule (1) next_trancl_split_tt [OF _ _ ab])
  done

declare domE[elim?]

lemma ndom_is_0D:
  "\<lbrakk> mdbNext node \<notin> dom m; mdb_chain_0 m; no_0 m; m ptr = Some (CTE cap node) \<rbrakk>
  \<Longrightarrow> mdbNext node = 0"
  apply -
  apply (frule (1) mdb_chain_0_nextD)
  apply simp
  apply (erule next_rtrancl_tranclE)
   apply simp
  apply (drule tranclD)
  apply (clarsimp simp: next_unfold')
  done

end

(* almost exactly 1000 lines --- yuck.  There is a lot of redundancy here, but I doubt it is worth
   exploiting above the cut'n'paste already here.
 *)

lemma (in mdb_swap) cteSwap_chain:
  "mdb_chain_0 n"
proof -
  have chain: "mdb_chain_0 m" using valid ..

  let ?m = "(modify_map
    (modify_map
         (modify_map
           (modify_map (modify_map m (mdbPrev src_node) (cteMDBNode_update (mdbNext_update (%_. dest))))
             (mdbNext src_node) (cteMDBNode_update (mdbPrev_update (%_. dest))))
           src (cteMDBNode_update (\<lambda>m. dest2_node)))
         dest (cteMDBNode_update (\<lambda>m. src_node)))
       (mdbPrev dest2_node) (cteMDBNode_update (mdbNext_update (%_. src))))"

  let ?n' = "modify_map m src (cteMDBNode_update (mdbNext_update (%_. (mdbNext dest_node))))"

  have [simp]: "src \<in> dom m" by (rule domI, rule src)
  have [simp]: "dest \<in> dom m" by (rule domI, rule dest)

  have dn: "m \<turnstile> dest \<leadsto> mdbNext dest_node" using dest by (rule next_fold, simp)

  have dp: "mdbPrev dest_node \<in> dom m
    \<Longrightarrow> m \<turnstile> mdbPrev dest_node \<leadsto> dest"
  proof -
    assume "mdbPrev dest_node \<in> dom m"
    hence "mdbPrev dest_node \<noteq> 0" using no_0 by - (rule, clarsimp)
    thus ?thesis using dest
      apply -
      apply (clarsimp dest!: dest_prev [where p = "mdbPrev dest_node", simplified])
      apply (erule next_fold)
      apply simp
      done
  qed

  have [simp]: "\<not> m \<turnstile> dest \<leadsto>\<^sup>+ dest"
    using mdb_chain_0_no_loops [OF chain no_0]
    by (simp add: no_loops_trancl_simp)

  have [simp]: "\<not> m \<turnstile> src \<leadsto>\<^sup>+ src"
    using mdb_chain_0_no_loops [OF chain no_0]
    by (simp add: no_loops_trancl_simp)

  have [simp]: "\<not> m \<turnstile> mdbNext src_node \<leadsto>\<^sup>* src"
    by (rule neg_next_rtrancl_nx, rule src, simp)


  have sn: "mdbPrev src_node \<in> dom m
    \<Longrightarrow> m \<turnstile> mdbPrev src_node \<leadsto> src"
  proof -
    assume "mdbPrev src_node \<in> dom m"
    hence "mdbPrev src_node \<noteq> 0" using no_0 by - (rule, clarsimp)
    thus ?thesis using src
      apply -
      apply (clarsimp dest!: src_prev [where p = "mdbPrev src_node", simplified])
      apply (erule next_fold)
      apply simp
      done
  qed

  from chain no_0 neq [symmetric]
  have "mdb_chain_0 ?m"
  proof (cases rule: mdb_chain_0_cases)
    case srcdest

    note [simp] = neg_rtrancl_into_trancl [OF srcdest(2)]
    note [simp] = srcdest(2)

    have dsneq: "dest \<noteq> mdbPrev src_node"
    proof
      assume "dest = mdbPrev src_node"
      hence "m \<turnstile> dest \<leadsto>\<^sup>* src"
        by - (rule r_into_rtrancl, rule next_fold [where m = m, OF dest], simp)

      thus False using srcdest by simp
    qed

    from dest have n1 [simp]:"\<not> m \<turnstile> mdbNext dest_node \<leadsto>\<^sup>* src"
      by (rule neg_next_rtrancl_nx [OF _ neg_rtrancl_into_trancl]) fact+

    have chain_n': "mdb_chain_0 ?n'"
    proof (cases "mdbNext dest_node \<in> dom m")
      case True
      thus ?thesis using n1
        by (rule mdb_chain_0_modify_map_next [OF chain no_0])
    next
      case False
      thus ?thesis using dest chain no_0
        by - (drule (3) ndom_is_0D, simp, erule (1) mdb_chain_0_modify_map_0)
    qed

    from dest src
    have n4: "mdbPrev src_node \<in> dom m \<Longrightarrow> \<not> m \<turnstile> mdbNext dest_node \<leadsto>\<^sup>* mdbPrev src_node"
      using neg_next_rtrancl_np [OF _ _ _ no_0 dlist neg_rtrancl_into_trancl]
      by auto

    hence n2 [simp]: "\<not> ?n' \<turnstile> src \<leadsto>\<^sup>* dest"
      using dn src
      by (auto dest: rtrancl_into_trancl2 simp: modify_map_lhs_rtrancl)

    hence n3: "mdbPrev src_node \<in> dom m
      \<Longrightarrow> \<not> modify_map ?n' dest (cteMDBNode_update (mdbNext_update (%_. src))) \<turnstile> dest \<leadsto>\<^sup>* mdbPrev src_node"
      using dest dsneq src n1
      by (simp add: modify_map_lhs_rtrancl modify_map_app) (rule n4)

    from srcdest(1)
    show ?thesis
    proof (cases rule: tranclE2')
      case base
      hence ds: "dest = mdbNext src_node" by (clarsimp simp: next_unfold' src)
      hence d2: "dest2_node = MDB (mdbNext dest_node) dest (mdbRevocable dest_node) (mdbFirstBadged dest_node)"
        using dsneq
        unfolding dest2_node_def by clarsimp

      let ?m' = "(modify_map
          (modify_map ?n' dest (cteMDBNode_update (mdbNext_update (%_. src))))
           (mdbPrev src_node) (cteMDBNode_update (mdbNext_update (%_. dest))))"

      let ?goal = "mdb_chain_0 ?m'"
      {
        assume d1: "mdbPrev src_node \<in> dom m" and d2: "mdbNext dest_node \<in> dom m"
        hence ?goal
          apply (intro mdb_chain_0_modify_map_next)
          apply (auto simp: no_0 chain n1 n2 n3[OF d1])
          done
      } moreover
      {
        assume d1: "mdbPrev src_node \<notin> dom m" and "mdbNext dest_node \<in> dom m"
        hence ?goal
          by simp ((rule mdb_chain_0_modify_map_next)+, simp_all add: no_0 chain n1 n2)
      } moreover
      {
        assume d1: "mdbPrev src_node \<in> dom m" and "mdbNext dest_node \<notin> dom m"
        hence m0: "mdbNext dest_node = 0"
          by (clarsimp dest!: dest_next [where p = "mdbNext dest_node", simplified])

        have ?goal using chain_n' d1 src dest
          apply -
          apply (rule  mdb_chain_0_modify_map_next)
          apply (rule  mdb_chain_0_modify_map_next [OF chain_n'])
          apply (simp_all add: no_0 chain n1 n2  n3 [OF d1])
          done
      } moreover
      {
        assume d1: "mdbPrev src_node \<notin> dom m" and "mdbNext dest_node \<notin> dom m"
        hence m0: "mdbNext dest_node = 0"
          by (clarsimp dest!: dest_next [where p = "mdbNext dest_node", simplified])

        have ?goal using d1 chain_n'
          apply simp
          apply (rule mdb_chain_0_modify_map_next)
          apply (simp_all add: no_0 chain n1 n2)
          done
      }
      ultimately have ?goal
        apply (cases "mdbPrev src_node \<in> dom m")
        apply (cases "mdbNext dest_node \<in> dom m")
        apply (auto)[2]
        apply (cases "mdbNext dest_node \<in> dom m")
        apply auto
        done

      thus ?thesis using ds [symmetric] d2 neqs dsneq
        apply simp
        apply (subst modify_map_addr_com [OF neqs(2)])
        apply (subst modify_map_comp [symmetric])
        apply (subst modify_map_comp [symmetric])
        apply (simp)
        apply (simp add: o_def)
        apply (rule mdb_chain_0_modify_map_replace)
        apply simp
        apply (subst modify_map_addr_com [where x = src])
        apply simp
        apply (rule mdb_chain_0_modify_map_replace)
        apply simp
        apply (subst modify_map_addr_com [OF dsneq [symmetric]])
        apply (subst modify_map_addr_com [where y = src], simp)+
        apply assumption
        done
    next
      case (trancl c)
      hence dsneq': "dest \<noteq> mdbNext src_node" using src
        apply -
        apply rule
        apply simp
        apply (drule next_fold)
        apply simp
        apply (drule (1) next_single_value)
        apply simp
        done

      hence d2n: "dest2_node = dest_node"
        unfolding dest2_node_def
        by (cases dest_node, simp add: dsneq)

      from trancl obtain d where dnext: "m \<turnstile> d \<leadsto> dest" and ncd: "m \<turnstile> c \<leadsto>\<^sup>* d"
        by (clarsimp dest!: tranclD2)

      have ddest: "d = mdbPrev (cteMDBNode (CTE dest_cap dest_node))"
        using dest dlist no_0 dnext
        by (rule next_prev)

      hence d2: "mdbPrev dest_node \<in> dom m" using dnext
        by (clarsimp simp: next_unfold')

      have dnz: "mdbPrev dest_node \<noteq> 0"
        by (rule dom_into_not0 [OF no_0 d2])

      have n5 [simp]: "\<not> ?n' \<turnstile> src \<leadsto>\<^sup>* mdbPrev dest_node"
      proof -
        have "src \<noteq> mdbPrev dest_node"
          by (simp add: dsneq' [symmetric])
        hence "?n' \<turnstile> mdbPrev dest_node \<leadsto> dest" using dp [OF d2]
          by (clarsimp simp: next_unfold' modify_map_other)
        thus ?thesis using n2
          by - (erule contrapos_nn, erule (1) rtrancl_into_rtrancl)
      qed

      let ?n2 = "modify_map ?n' (mdbPrev dest_node) (cteMDBNode_update (mdbNext_update (%_. src)))"
      have chain_n2: "mdb_chain_0 ?n2"
        by ((rule chain_n' | rule mdb_chain_0_modify_map_next)+, simp_all add: no_0)

      have r [simp]: "\<not> m \<turnstile> mdbNext dest_node \<leadsto>\<^sup>* mdbPrev dest_node"
        by (rule neg_next_rtrancl_np [OF _ _ d2 no_0 dlist], rule dest, rule dest, simp)

      have r3 [simp]: "\<not> m \<turnstile> mdbNext dest_node \<leadsto>\<^sup>* src"
        by (rule neg_next_rtrancl_nx, rule dest, simp)

      have r4 [simp]: "\<not> m \<turnstile> dest \<leadsto>\<^sup>+ mdbPrev dest_node"
        by (rule neg_next_trancl_xp [OF _ d2 no_0 dlist], rule dest, simp)

      let ?m'' =
        "(modify_map (modify_map
          (modify_map ?n' (mdbPrev dest_node) (cteMDBNode_update (mdbNext_update (%_. src))))
           (mdbPrev src_node) (cteMDBNode_update (mdbNext_update (%_. dest))))
          dest (cteMDBNode_update (mdbNext_update (%_. (mdbNext src_node)))))"

      have n2_2 [simp]:
        "?n2 \<turnstile> mdbNext src_node \<leadsto>\<^sup>* mdbPrev dest_node"
        apply (cases "mdbNext src_node = mdbPrev dest_node")
        apply simp
        apply (rule trancl_into_rtrancl)
        apply (rule next_modify_map_trancl_last [OF chain_n'], simp add: no_0)
        apply (subst modify_map_trancl_other_iff)
        apply simp
        apply (rule next_trancl_np [OF _ _ dlist no_0])
        apply (rule src, rule dest)
        apply (simp add: dsneq' [symmetric])
        apply assumption
        apply (rule srcdest(1))
        done

      hence n2_3 [simp]: "\<not> ?n2 \<turnstile> mdbNext src_node \<leadsto>\<^sup>+ dest"
      proof (rule neg_next_trancl_trancl)
        show "\<not> ?n2 \<turnstile> dest \<leadsto>\<^sup>* mdbPrev dest_node"
          apply (rule neg_rtranclI)
          apply simp
          apply (subst next_modify_map_trancl_last_iff [OF chain_n' chain_n2])
          apply (simp add: no_0)
          apply (simp add: modify_map_trancl_other_iff)
          done

        show "\<not> ?n2 \<turnstile> mdbPrev dest_node \<leadsto>\<^sup>* dest" using d2
          by (clarsimp simp: modify_map_lhs_rtrancl modify_map_other dsneq' [symmetric])
      qed

      have r5 [simp]: "mdbPrev src_node \<in> dom m \<Longrightarrow> \<not> m \<turnstile> dest \<leadsto>\<^sup>+ mdbPrev src_node"
        by (rule neg_next_trancl_xp [OF _ _ no_0 dlist], rule src, simp_all)

      have n2_4 [simp]:
        "mdbPrev src_node \<in> dom m \<Longrightarrow> \<not> ?n2 \<turnstile> dest \<leadsto>\<^sup>* mdbPrev src_node"
        apply -
        apply (rule neg_rtranclI [OF dsneq])
        apply (subst modify_map_trancl_other_iff)
        apply (rule neg_rtranclI)
        apply (simp_all add: modify_map_trancl_other_iff)
        done

      let ?goal = "mdb_chain_0 ?m''"
      {
        assume d1: "mdbPrev src_node \<in> dom m" and d3: "mdbNext src_node \<in> dom m"

        have r2 [simp]: "\<not> m \<turnstile> mdbNext dest_node \<leadsto>\<^sup>* mdbPrev src_node"
          using dest src
          by (rule neg_next_rtrancl_np [OF _ _ _ no_0 dlist neg_rtrancl_into_trancl]) fact+

        have ?goal
        proof ((rule chain_n' | rule chain_n2 | rule mdb_chain_0_modify_map_next)+,
            simp_all add: no_0 chain n1 d1)

          have n2_1:
            "\<not> ?n2 \<turnstile> mdbPrev dest_node \<leadsto>\<^sup>* mdbPrev src_node" using d2  dsneq' [symmetric]
            apply -
            apply (erule domE)
            apply (subst modify_map_lhs_rtrancl)
              apply (clarsimp simp: modify_map_other)
              apply simp
             apply simp
            apply (simp add: dom_into_not0 [OF no_0 d2])
            apply (subst modify_map_lhs_rtrancl, rule src)
             apply simp
             apply (simp)
            done

          have "\<not> ?n' \<turnstile> mdbPrev src_node \<leadsto>\<^sup>+ mdbPrev dest_node"
            apply (rule neg_next_rtrancl_trancl [where y = src])
            apply (subst modify_map_lhs_rtrancl)
            apply (rule src)
            apply simp
            apply (simp add: dsneq' [symmetric])
            apply (subst next_modify_map_last)
            apply simp
            apply (rule sn [OF d1])
            done
          hence "mdbPrev src_node \<noteq> 0 \<Longrightarrow> \<not> ?n2 \<turnstile> mdbPrev src_node \<leadsto>\<^sup>* mdbPrev dest_node"
            apply -
            apply (rule neg_rtranclI)
            apply simp
            apply (subst next_modify_map_trancl_last_iff [OF chain_n' chain_n2])
            apply (simp add: no_0)
            apply assumption
            done
          moreover from no_0 have "mdbPrev src_node \<noteq> 0" using d1 by auto
          ultimately show
            "\<not> modify_map ?n2 (mdbPrev src_node) (cteMDBNode_update (mdbNext_update (%_. dest))) \<turnstile> mdbNext src_node \<leadsto>\<^sup>* dest" using n2_1
            apply -
            apply (rule neg_rtranclI)
            apply (simp add: dsneq' [symmetric])
            apply (subst modify_map_trancl_other_iff)
            apply (rule neg_rtranclI)
            apply simp
            apply (rule neg_next_trancl_trancl [OF n2_2])
            apply auto
            done
        qed fact+
      } moreover
      {
        assume d1: "mdbPrev src_node \<notin> dom m" and d3: "mdbNext src_node \<in> dom m"

        have ?goal
        proof (simp add: d1, (rule chain_n' | rule chain_n2 | rule mdb_chain_0_modify_map_next)+,
            simp_all add: no_0 chain n1)
          show "\<not> ?n2 \<turnstile> mdbNext src_node \<leadsto>\<^sup>* dest"
            by (rule neg_rtranclI [OF _ n2_3], simp add: dsneq' [symmetric])
        qed fact+
      } moreover
      {
        assume d1: "mdbPrev src_node \<in> dom m" and d3: "mdbNext src_node \<notin> dom m"
        hence m0: "mdbNext src_node = 0"
          by (clarsimp dest!: src_next [where p = "mdbNext src_node", simplified])

        have ?goal
          by (simp add: m0,
          (rule chain_n' | rule chain_n2 | rule mdb_chain_0_modify_map_0 | rule mdb_chain_0_modify_map_next)+,
            simp_all add: no_0 chain n1 d1)
      } moreover
      {
        assume d1: "mdbPrev src_node \<notin> dom m" and d3: "mdbNext src_node \<notin> dom m"
        hence m0: "mdbNext src_node = 0"
          by (clarsimp dest!: src_next [where p = "mdbNext src_node", simplified])

        have ?goal
          by (simp add: m0 d1,
          (rule chain_n' | rule chain_n2 | rule mdb_chain_0_modify_map_0 | rule mdb_chain_0_modify_map_next)+,
            simp_all add: no_0 chain n1 d1)
      } ultimately have ?goal
        apply (cases "mdbPrev src_node \<in> dom m")
        apply (cases "mdbNext src_node \<in> dom m")
        apply (auto)[2]
        apply (cases "mdbNext src_node \<in> dom m")
        apply auto
        done

      thus ?thesis using no_0 d2n
        apply simp
        apply (subst modify_map_addr_com [where y = "mdbPrev dest_node"])
        apply simp
        apply (rule mdb_chain_0_modify_map_replace)
        apply (subst modify_map_addr_com [where x = src])
        apply (simp add: dsneq' [symmetric])
        apply (subst modify_map_addr_com [where x = src])
        apply simp
        apply (rule mdb_chain_0_modify_map_replace)
        apply simp
        apply (rule mdb_chain_0_modify_map_prev)
        apply (subst modify_map_addr_com [where y = dest], simp add: dsneq [symmetric] dsneq')+
        apply (subst modify_map_addr_com [where y = "mdbPrev src_node"], simp add: dsneq)
        apply (subst modify_map_addr_com [where y = "mdbPrev dest_node"], simp add: dsneq dnz)+
        apply (subst modify_map_addr_com [where y = src], simp add: dsneq dsneq' [symmetric] dnz)+
        apply assumption
        done
    qed
  next
    case destsrc (* Dual of srcdest *)

    let ?n' = "modify_map m dest (cteMDBNode_update (mdbNext_update (%_. (mdbNext src_node))))"

    note [simp] = neg_rtrancl_into_trancl [OF destsrc(2)]
    note [simp] = destsrc(2)

    have dsneq: "src \<noteq> mdbPrev dest_node"
    proof
      assume "src = mdbPrev dest_node"
      hence "m \<turnstile> src \<leadsto>\<^sup>* dest"
        by - (rule r_into_rtrancl, rule next_fold [where m = m, OF src], simp)

      thus False using destsrc by simp
    qed

    from src have n1 [simp]:"\<not> m \<turnstile> mdbNext src_node \<leadsto>\<^sup>* dest"
      by (rule neg_next_rtrancl_nx [OF _ neg_rtrancl_into_trancl]) fact+

    have chain_n': "mdb_chain_0 ?n'"
    proof (cases "mdbNext src_node \<in> dom m")
      case True
      thus ?thesis using n1
        by (rule mdb_chain_0_modify_map_next [OF chain no_0])
    next
      case False
      thus ?thesis using src chain no_0
        by - (drule (3) ndom_is_0D, simp, erule (1) mdb_chain_0_modify_map_0)
    qed

    from src dest
    have n4: "mdbPrev dest_node \<in> dom m \<Longrightarrow> \<not> m \<turnstile> mdbNext src_node \<leadsto>\<^sup>* mdbPrev dest_node"
      using neg_next_rtrancl_np [OF _ _ _ no_0 dlist neg_rtrancl_into_trancl]
      by auto

    hence n2 [simp]: "\<not> ?n' \<turnstile> dest \<leadsto>\<^sup>* src"
      using sn dest
      by (auto dest: rtrancl_into_trancl2 simp: modify_map_lhs_rtrancl)

    hence n3: "mdbPrev dest_node \<in> dom m
      \<Longrightarrow> \<not> modify_map ?n' src (cteMDBNode_update (mdbNext_update (%_. dest))) \<turnstile> src \<leadsto>\<^sup>* mdbPrev dest_node"
      using dest dsneq src n1
      by (simp add: modify_map_lhs_rtrancl modify_map_app) (rule n4)

    from destsrc(1)
    show ?thesis
    proof (cases rule: tranclE2')
      case base
      hence ds: "src = mdbNext dest_node" by (clarsimp simp: next_unfold' dest)
      hence d2: "dest2_node =  MDB dest (mdbPrev dest_node) (mdbRevocable dest_node) (mdbFirstBadged dest_node)"
        using dsneq
        unfolding dest2_node_def by simp

      let ?m' = "(modify_map
          (modify_map ?n' src (cteMDBNode_update (mdbNext_update (%_. dest))))
           (mdbPrev dest_node) (cteMDBNode_update (mdbNext_update (%_. src))))"

      let ?goal = "mdb_chain_0 ?m'"
      {
        assume d1: "mdbPrev dest_node \<in> dom m" and "mdbNext src_node \<in> dom m"
        hence ?goal
          apply (intro mdb_chain_0_modify_map_next)
          apply (auto simp: no_0 chain n1 n2 n3 [OF d1])
          done
      } moreover
      {
        assume d1: "mdbPrev dest_node \<notin> dom m" and "mdbNext src_node \<in> dom m"
        hence ?goal
          by simp ((rule mdb_chain_0_modify_map_next)+, simp_all add: no_0 chain n1 n2)
      } moreover
      {
        assume d1: "mdbPrev dest_node \<in> dom m" and "mdbNext src_node \<notin> dom m"
        hence m0: "mdbNext src_node = 0"
          by (clarsimp dest!: src_next [where p = "mdbNext src_node", simplified])

        have ?goal using chain_n' d1 src dest
          apply -
          apply (rule  mdb_chain_0_modify_map_next)
          apply (rule  mdb_chain_0_modify_map_next [OF chain_n'])
          apply (simp_all add: no_0 chain n1 n2  n3 [OF d1])
          done
      } moreover
      {
        assume d1: "mdbPrev dest_node \<notin> dom m" and "mdbNext src_node \<notin> dom m"
        hence m0: "mdbNext src_node = 0"
          by (clarsimp dest!: src_next [where p = "mdbNext src_node", simplified])

        have ?goal using d1 chain_n'
          apply simp
          apply (rule mdb_chain_0_modify_map_next)
          apply (simp_all add: no_0 chain n1 n2)
          done
      }
      ultimately have ?goal
        apply (cases "mdbPrev dest_node \<in> dom m")
        apply (cases "mdbNext src_node \<in> dom m")
        apply (auto)[2]
        apply (cases "mdbNext src_node \<in> dom m")
        apply auto
        done
      thus ?thesis using ds [symmetric] d2 neqs dsneq
        apply simp
        apply (subst modify_map_addr_com [where x = "mdbNext src_node"], simp)+
        apply (subst modify_map_addr_com [OF neqs(1)])
        apply (subst modify_map_comp [symmetric])
        apply (simp)
        apply (rule mdb_chain_0_modify_map_prev)
        apply (subst modify_map_addr_com [where x = src])
        apply simp
        apply (rule mdb_chain_0_modify_map_replace)
        apply simp
        apply (subst modify_map_addr_com [where x = dest], simp)+
        apply (rule mdb_chain_0_modify_map_replace)
        apply (subst modify_map_addr_com [where y = src], simp)+
        apply (subst modify_map_addr_com [where y = dest], simp)+
        apply assumption
        done
    next
      case (trancl c)
      hence dsneq': "src \<noteq> mdbNext dest_node" using dest
        apply -
        apply rule
        apply simp
        apply (drule next_fold)
        apply simp
        apply (drule (1) next_single_value)
        apply simp
        done

      hence d2n: "dest2_node = dest_node"
        unfolding dest2_node_def using dsneq
        by simp

      from trancl obtain d where dnext: "m \<turnstile> d \<leadsto> src" and ncd: "m \<turnstile> c \<leadsto>\<^sup>* d"
        by (clarsimp dest!: tranclD2)

      have ddest: "d = mdbPrev (cteMDBNode (CTE src_cap src_node))"
        using src dlist no_0 dnext
        by (rule next_prev)

      hence d2: "mdbPrev src_node \<in> dom m" using dnext
        by (clarsimp simp: next_unfold')

      have dnz: "mdbPrev src_node \<noteq> 0"
        by (rule dom_into_not0 [OF no_0 d2])

      have n5 [simp]: "\<not> ?n' \<turnstile> dest \<leadsto>\<^sup>* mdbPrev src_node"
      proof -
        have "dest \<noteq> mdbPrev src_node"
          by (simp add: dsneq' [simplified, symmetric])
        hence "?n' \<turnstile> mdbPrev src_node \<leadsto> src" using sn [OF d2]
          by (clarsimp simp: next_unfold' modify_map_other)
        thus ?thesis using n2
          by - (erule contrapos_nn, erule (1) rtrancl_into_rtrancl)
      qed

      let ?n2 = "modify_map ?n' (mdbPrev src_node) (cteMDBNode_update (mdbNext_update (%_. dest)))"
      have chain_n2: "mdb_chain_0 ?n2"
        by ((rule chain_n' | rule mdb_chain_0_modify_map_next)+, simp_all add: no_0)

      have r [simp]: "\<not> m \<turnstile> mdbNext src_node \<leadsto>\<^sup>* mdbPrev src_node"
        by (rule neg_next_rtrancl_np [OF _ _ d2 no_0 dlist], rule src, rule src, simp)

      have r3 [simp]: "\<not> m \<turnstile> mdbNext src_node \<leadsto>\<^sup>* dest"
        by (rule neg_next_rtrancl_nx, rule src, simp)

      have r5 [simp]: "\<not> m \<turnstile> mdbNext dest_node \<leadsto>\<^sup>* dest"
        by (rule neg_next_rtrancl_nx, rule dest, simp)

      have r4 [simp]: "\<not> m \<turnstile> src \<leadsto>\<^sup>+ mdbPrev src_node"
        by (rule neg_next_trancl_xp [OF _ d2 no_0 dlist], rule src, simp)

      let ?m'' =
        "(modify_map (modify_map
          (modify_map ?n' (mdbPrev src_node) (cteMDBNode_update (mdbNext_update (%_. dest))))
           (mdbPrev dest_node) (cteMDBNode_update (mdbNext_update (%_. src))))
          src (cteMDBNode_update (mdbNext_update (%_. (mdbNext dest_node)))))"

      have n2_2 [simp]:
        "?n2 \<turnstile> mdbNext dest_node \<leadsto>\<^sup>* mdbPrev src_node"
        apply (cases "mdbNext dest_node = mdbPrev src_node")
        apply simp
        apply (rule trancl_into_rtrancl)
        apply (rule next_modify_map_trancl_last [OF chain_n'], simp add: no_0)
        apply (subst modify_map_trancl_other_iff)
        apply simp
        apply (rule next_trancl_np [OF _ _ dlist no_0])
        apply (rule dest, rule src)
        apply (simp add: dsneq' [simplified])
        apply assumption
        apply (rule destsrc(1))
        done

      hence n2_3 [simp]: "\<not> ?n2 \<turnstile> mdbNext dest_node \<leadsto>\<^sup>+ src"
      proof (rule neg_next_trancl_trancl)
        show "\<not> ?n2 \<turnstile> src \<leadsto>\<^sup>* mdbPrev src_node"
          apply (rule neg_rtranclI)
          apply simp
          apply (subst next_modify_map_trancl_last_iff [OF chain_n' chain_n2])
          apply (simp add: no_0)
          apply (simp add: modify_map_trancl_other_iff)
          done

        show "\<not> ?n2 \<turnstile> mdbPrev src_node \<leadsto>\<^sup>* src" using d2
          by (clarsimp simp: modify_map_lhs_rtrancl modify_map_other dsneq' [simplified, symmetric])
      qed

      have r6 [simp]: "mdbPrev dest_node \<in> dom m \<Longrightarrow> \<not> m \<turnstile> src \<leadsto>\<^sup>+ mdbPrev dest_node"
        by (rule neg_next_trancl_xp [OF _ _ no_0 dlist], rule dest, simp_all)

      have n2_4 [simp]:
        "mdbPrev dest_node \<in> dom m \<Longrightarrow> \<not> ?n2 \<turnstile> src \<leadsto>\<^sup>* mdbPrev dest_node"
        apply -
        apply (rule neg_rtranclI [OF dsneq])
        apply (subst modify_map_trancl_other_iff)
        apply (rule neg_rtranclI)
        apply (simp_all add: modify_map_trancl_other_iff)
        done

      let ?goal = "mdb_chain_0 ?m''"
      {
        assume d1: "mdbPrev dest_node \<in> dom m" and d3: "mdbNext dest_node \<in> dom m"

        have r2 [simp]: "\<not> m \<turnstile> mdbNext src_node \<leadsto>\<^sup>* mdbPrev dest_node"
          using src dest
          by (rule neg_next_rtrancl_np [OF _ _ _ no_0 dlist neg_rtrancl_into_trancl]) fact+

        have ?goal
          proof ((rule chain_n' | rule chain_n2 | rule mdb_chain_0_modify_map_next)+,
              simp_all add: no_0 chain n1 d1)

          have n2_1:
            "\<not> ?n2 \<turnstile> mdbPrev src_node \<leadsto>\<^sup>* mdbPrev dest_node" using d2  dsneq' [symmetric]
            apply -
            apply (erule domE)
            apply (subst modify_map_lhs_rtrancl)
              apply (clarsimp simp: modify_map_other)
              apply simp
             apply simp
            apply (simp add: dom_into_not0 [OF no_0 d2])
            apply (subst modify_map_lhs_rtrancl, rule dest)
             apply simp
             apply (simp)
            done
          have "\<not> ?n' \<turnstile> mdbPrev dest_node \<leadsto>\<^sup>+ mdbPrev src_node"
            apply (rule neg_next_rtrancl_trancl [where y = dest])
             apply (subst modify_map_lhs_rtrancl)
               apply (rule dest)
              apply simp
             apply (simp add: dsneq' [simplified])
            apply (subst next_modify_map_last)
             apply simp
            apply (rule dp [OF d1])
            done
          hence "mdbPrev dest_node \<noteq> 0 \<Longrightarrow> \<not> ?n2 \<turnstile> mdbPrev dest_node \<leadsto>\<^sup>* mdbPrev src_node"
            apply -
            apply (rule neg_rtranclI)
             apply simp
            apply (subst next_modify_map_trancl_last_iff [OF chain_n' chain_n2])
             apply (simp add: no_0)
            apply assumption
            done
          moreover from no_0 have "mdbPrev dest_node \<noteq> 0" using d1 by auto
          ultimately show
            "\<not> modify_map ?n2 (mdbPrev dest_node) (cteMDBNode_update (mdbNext_update (%_. src))) \<turnstile> mdbNext dest_node \<leadsto>\<^sup>* src" using n2_1 dsneq' [symmetric]
            apply -
            apply (rule neg_rtranclI)
            apply (simp)
            apply (subst modify_map_trancl_other_iff)
            apply (rule neg_rtranclI)
            apply simp
            apply (rule neg_next_trancl_trancl [OF n2_2])
            apply auto
            done
        qed fact+
      } moreover
      {
        assume d1: "mdbPrev dest_node \<notin> dom m" and d3: "mdbNext dest_node \<in> dom m"

        have ?goal
        proof (simp add: d1, (rule chain_n' | rule chain_n2 | rule mdb_chain_0_modify_map_next)+,
            simp_all add: no_0 chain n1)
          show "\<not> ?n2 \<turnstile> mdbNext dest_node \<leadsto>\<^sup>* src"
            by (rule neg_rtranclI [OF _ n2_3], simp add: dsneq' [simplified])
        qed fact+
      } moreover
      {
        assume d1: "mdbPrev dest_node \<in> dom m" and d3: "mdbNext dest_node \<notin> dom m"
        hence m0: "mdbNext dest_node = 0"
          by (clarsimp dest!: dest_next [where p = "mdbNext dest_node", simplified])

        have ?goal
          by (simp add: m0,
          (rule chain_n' | rule chain_n2 | rule mdb_chain_0_modify_map_0 | rule mdb_chain_0_modify_map_next)+,
            simp_all add: no_0 chain n1 d1)
      } moreover
      {
        assume d1: "mdbPrev dest_node \<notin> dom m" and d3: "mdbNext dest_node \<notin> dom m"
        hence m0: "mdbNext dest_node = 0"
          by (clarsimp dest!: dest_next [where p = "mdbNext dest_node", simplified])

        have ?goal
          by (simp add: m0 d1,
          (rule chain_n' | rule chain_n2 | rule mdb_chain_0_modify_map_0 | rule mdb_chain_0_modify_map_next)+,
            simp_all add: no_0 chain n1 d1)
      } ultimately have ?goal
        apply (cases "mdbPrev dest_node \<in> dom m")
        apply (cases "mdbNext dest_node \<in> dom m")
        apply (auto)[2]
        apply (cases "mdbNext dest_node \<in> dom m")
        apply auto
        done
      thus ?thesis using no_0 d2n dsneq dsneq'
        apply simp
        apply (subst modify_map_addr_com [where y = "mdbPrev dest_node"])
        apply simp
        apply (rule mdb_chain_0_modify_map_replace)
        apply (subst modify_map_addr_com [where x = src], simp)+
        apply (rule mdb_chain_0_modify_map_replace)
        apply simp
        apply (rule mdb_chain_0_modify_map_prev)
        apply (subst modify_map_addr_com [where y = src], simp)+
        apply (subst modify_map_addr_com [where y = "mdbPrev dest_node"], simp add: dnz)+
        apply (subst modify_map_addr_com [where y = "mdbPrev src_node"], simp add: dnz)+
        apply (subst modify_map_addr_com [where y = dest], simp add:  dnz)+
        apply assumption
        done
    qed
  next
    case indep

    have indep_rt1: "\<not> m \<turnstile> src \<leadsto>\<^sup>* dest"
      by (rule neg_rtranclI, simp) fact+

    have indep_rt2: "\<not> m \<turnstile> dest \<leadsto>\<^sup>* src"
      by (rule neg_rtranclI, simp) fact+

    have dsneq: "src \<noteq> mdbPrev dest_node"
    proof
      assume "src = mdbPrev dest_node"
      hence "m \<turnstile> src \<leadsto>\<^sup>+ dest"
        by - (rule r_into_trancl, rule next_fold [where m = m, OF src], simp)

      thus False using indep by simp
    qed

    note [simp] = dsneq [simplified]

    have sdneq: "dest \<noteq> mdbPrev src_node"
    proof
      assume "dest = mdbPrev src_node"
      hence "m \<turnstile> dest \<leadsto>\<^sup>+ src"
        by - (rule r_into_trancl, rule next_fold [where m = m, OF dest], simp)

      thus False using indep by simp
    qed

    note [simp] = sdneq [simplified]

    have dsneq' [simp]: "dest \<noteq> mdbNext src_node"
    proof
      assume "dest = mdbNext src_node"
      hence "m \<turnstile> src \<leadsto>\<^sup>+ dest"
        apply -
        apply (rule r_into_trancl)
        apply (rule next_fold)
        apply (rule src)
        apply simp
        done
      thus False using indep by simp
    qed

    have dsnp: "mdbPrev src_node \<in> dom m \<Longrightarrow> mdbNext dest_node \<noteq> mdbPrev src_node"
    proof
      assume "mdbPrev src_node \<in> dom m" and "mdbNext dest_node = mdbPrev src_node"
      hence "m \<turnstile> mdbNext dest_node \<leadsto>\<^sup>* mdbPrev src_node"
        by simp
      moreover have "m \<turnstile> dest \<leadsto> mdbNext dest_node" using dest by (rule next_fold, simp)
      moreover have "m \<turnstile> mdbPrev src_node \<leadsto> src" by (rule sn) fact+
      ultimately have "m \<turnstile> dest \<leadsto>\<^sup>+ src" by auto
      thus False using indep by simp
    qed

    have d2n: "dest2_node = dest_node"
      unfolding dest2_node_def by (cases dest_node, simp)

    let ?n' = "modify_map m dest (cteMDBNode_update (mdbNext_update (%_. (mdbNext src_node))))"

    let ?n2 = "modify_map ?n' (mdbPrev src_node) (cteMDBNode_update (mdbNext_update (%_. dest)))"

    from src have n1 [simp]:"\<not> m \<turnstile> mdbNext src_node \<leadsto>\<^sup>* dest"
      by (rule neg_next_rtrancl_nx [OF _ neg_rtrancl_into_trancl]) (rule indep_rt1)

    have chain_n': "mdb_chain_0 ?n'"
    proof (cases "mdbNext src_node \<in> dom m")
      case True
      thus ?thesis using n1
        by (rule mdb_chain_0_modify_map_next [OF chain no_0])
    next
      case False
      thus ?thesis using src chain no_0
        by - (drule (3) ndom_is_0D, simp, erule (1) mdb_chain_0_modify_map_0)
    qed

    have chain_n2: "mdb_chain_0 ?n2"
      apply (cases "mdbPrev src_node \<in> dom m")
      apply ((rule chain_n' | rule mdb_chain_0_modify_map_next)+, simp_all add: no_0)
      apply (subst modify_map_lhs_rtrancl)
      apply (rule dest)
      apply simp
      apply (simp add: sdneq [symmetric])
      apply (rule neg_next_rtrancl_np [OF _ _ _ no_0 dlist])
      apply (rule src, rule src)
      apply assumption
      apply simp
      apply (rule chain_n')
      done

    let ?m' = "(modify_map
       (modify_map ?n2
         src (cteMDBNode_update (mdbNext_update (%_. (mdbNext dest_node)))))
       (mdbPrev dest_node) (cteMDBNode_update (mdbNext_update (%_. src))))"

    have r1 [simp]: "mdbPrev src_node \<in> dom m \<Longrightarrow> \<not> m \<turnstile> src \<leadsto>\<^sup>+ mdbPrev src_node"
      apply (rule neg_next_trancl_xp)
      apply (rule src, assumption, rule no_0, rule dlist)
      apply simp
      done

    have r [simp]: "mdbPrev src_node \<in> dom m \<Longrightarrow> \<not> ?n' \<turnstile> src \<leadsto>\<^sup>+ mdbPrev src_node"
      by (simp add: modify_map_trancl_other_iff [OF indep_rt1])

    have r2 [simp]: "mdbPrev dest_node \<in> dom m \<Longrightarrow> \<not> m \<turnstile> mdbNext src_node \<leadsto>\<^sup>* mdbPrev dest_node"
      using src dest indep neg_next_rtrancl_np [OF _ _ _ no_0 dlist]
      by auto

    have n2 [simp]: "\<not> ?n' \<turnstile> dest \<leadsto>\<^sup>* src"
      using sn dest
      by (auto dest: rtrancl_into_trancl2 simp: modify_map_lhs_rtrancl)

    have n5 [simp]: "mdbPrev src_node \<in> dom m \<Longrightarrow> \<not> ?n' \<turnstile> dest \<leadsto>\<^sup>* mdbPrev src_node"
    proof -
      assume d2: "mdbPrev src_node \<in> dom m"
      have "?n' \<turnstile> mdbPrev src_node \<leadsto> src" using sn [OF d2]
        by (clarsimp simp: next_unfold' modify_map_other)
      thus ?thesis using n2
        by - (erule contrapos_nn, erule (1) rtrancl_into_rtrancl)
    qed

    have r4 [simp]: "mdbPrev src_node \<in> dom m \<Longrightarrow> \<not> m \<turnstile> mdbNext dest_node \<leadsto>\<^sup>+ mdbPrev src_node"
      apply (rule neg_next_trancl_np [OF _ _ _ no_0 dlist])
         apply (rule dest)
        apply (rule src)
       apply assumption
      apply (rule indep(2))
      done

    have r5 [simp]: "\<not> m \<turnstile> mdbNext dest_node \<leadsto>\<^sup>* dest"
      by (rule neg_next_rtrancl_nx, rule dest, simp)
    have r6 [simp]: " \<not> m \<turnstile> mdbNext dest_node \<leadsto>\<^sup>+ src"
      by (rule neg_next_trancl_nx, rule dest, rule indep(2))
    have r7 [simp]: " mdbPrev dest_node \<in> dom m \<Longrightarrow> \<not> m \<turnstile> mdbNext dest_node \<leadsto>\<^sup>+ mdbPrev dest_node"
      apply (rule neg_next_trancl_np [OF _ _ _ no_0 dlist])
         apply (rule dest)
        apply (rule dest)
       apply assumption
      apply simp
      done

    have n6 [simp]: "\<not> ?n' \<turnstile> mdbNext dest_node \<leadsto>\<^sup>+ src"
      by (subst modify_map_trancl_other_iff) simp_all

    have n6_r [simp]: "\<not> ?n' \<turnstile> mdbNext dest_node \<leadsto>\<^sup>* src"
      by (rule neg_rtranclI) (simp_all add: sdneq [symmetric])

    have n2_3 [simp]: "mdbPrev src_node \<in> dom m \<Longrightarrow> \<not> ?n2 \<turnstile> mdbNext dest_node \<leadsto>\<^sup>+ src"
      apply (subst modify_map_trancl_other_iff)
      apply (rule neg_rtranclI)
      apply (simp add: dsnp)
      apply (subst modify_map_trancl_other_iff)
      apply (rule neg_next_rtrancl_nx)
      apply (rule dest)
      apply simp_all
      done

    have n7 [simp]: "mdbPrev src_node \<in> dom m \<Longrightarrow>  \<not> ?n' \<turnstile>  mdbNext dest_node \<leadsto>\<^sup>* mdbPrev src_node"
      apply (rule neg_rtranclI)
      apply (erule dsnp)
      apply (subst modify_map_trancl_other_iff)
      apply simp_all
      done

    have n8 [simp]: "mdbPrev dest_node \<in> dom m
      \<Longrightarrow> \<not> ?n' \<turnstile> mdbNext dest_node \<leadsto>\<^sup>+ mdbPrev dest_node"
      by (simp add: modify_map_trancl_other_iff)

    have n2_5 [simp]: "mdbPrev dest_node \<in> dom m \<Longrightarrow> \<not> ?n2 \<turnstile> mdbNext dest_node \<leadsto>\<^sup>+ mdbPrev dest_node"
      by (cases "mdbPrev src_node \<in> dom m", simp_all add: modify_map_trancl_other_iff)

    have n2_4 [simp]: "mdbPrev dest_node \<in> dom m \<Longrightarrow> \<not> ?n2 \<turnstile> mdbNext dest_node \<leadsto>\<^sup>* mdbPrev dest_node"
      apply (frule dom_into_not0 [OF no_0])
      apply (cases "mdbPrev src_node \<in> dom m")
       apply (rule neg_rtranclI)
        apply (drule dom_into_not0 [OF no_0])
        apply simp
       apply simp
      apply simp
      apply (rule neg_rtranclI)
       apply simp
      apply simp
      done

    have n9 [simp]: "mdbPrev dest_node \<in> dom m \<Longrightarrow>
      \<not> modify_map ?n' src (cteMDBNode_update (mdbNext_update (%_. (mdbNext dest_node)))) \<turnstile> src \<leadsto>\<^sup>* mdbPrev dest_node"
        apply (subst modify_map_lhs_rtrancl)
        apply (simp add: src modify_map_other)
        apply simp
        apply simp
        apply (rule neg_rtranclI)
        apply (drule dom_into_not0 [OF no_0])
        apply simp
        apply simp
        done

    have chain_n3: "mdbPrev src_node \<in> dom m \<Longrightarrow> mdb_chain_0
        (modify_map
          (modify_map (modify_map m dest (cteMDBNode_update (mdbNext_update (%_. (mdbNext src_node)))))
            (mdbPrev src_node) (cteMDBNode_update (mdbNext_update (%_. dest))))
          src (cteMDBNode_update (mdbNext_update (%_. (mdbNext dest_node)))))"
      apply -
      apply (cases "mdbNext dest_node \<in> dom m")
       apply (rule mdb_chain_0_modify_map_next [OF chain_n2])
         apply (simp add: no_0)
        apply simp
       apply (rule neg_rtranclI)
        apply (simp add: sdneq [symmetric])
       apply simp
      apply (frule ndom_is_0D [OF _ chain no_0])
       apply (rule dest)
      apply simp
      apply (rule mdb_chain_0_modify_map_0 [OF chain_n2])
      apply (simp_all add: no_0)
      done

    have "mdb_chain_0 ?m'"
    proof (cases rule: cases2 [of "mdbPrev src_node \<in> dom m" "mdbPrev dest_node \<in> dom m"])
      case pos_pos

      thus ?thesis
        apply -
        apply (rule mdb_chain_0_modify_map_next [OF chain_n3])
           apply (simp_all add: no_0)
        apply (subst modify_map_lhs_rtrancl)
          apply (simp add: modify_map_other src)
         apply simp
         apply (rule neg_rtranclI)
          apply (simp add: sdneq [symmetric])
         apply simp
        apply simp
        done
    next
      case pos_neg
      thus ?thesis
        by simp (rule chain_n3)
    next
      case neg_pos
      thus ?thesis using no_0
        apply -
        apply simp
        apply (cases "mdbNext dest_node \<in> dom m")
         apply (rule mdb_chain_0_modify_map_next)
            apply (rule mdb_chain_0_modify_map_next [OF chain_n'])
              apply simp_all
        apply (drule ndom_is_0D [OF _ chain no_0], rule dest)
        apply simp
        apply (rule mdb_chain_0_modify_map_next)
           apply (rule mdb_chain_0_modify_map_0 [OF chain_n'])
           apply simp_all
        apply (subst modify_map_lhs_rtrancl)
          apply (simp add: modify_map_other src)
         apply simp_all
        apply (rule no_0_no_0_lhs_rtrancl)
         apply simp
        apply (erule (1) dom_into_not0)
        done
    next
      case neg_neg
      thus ?thesis using no_0
        apply -
        apply (cases "mdbNext dest_node \<in> dom m")
         apply simp
         apply (rule mdb_chain_0_modify_map_next [OF chain_n'])
           apply simp
          apply simp
         apply simp
        apply (drule ndom_is_0D [OF _ chain no_0], rule dest)
        apply simp
        apply (rule mdb_chain_0_modify_map_0 [OF chain_n'])
        apply simp
        done
    qed

      thus ?thesis using d2n
      apply simp
      apply (subst modify_map_addr_com [where x = dest], simp)+
      apply (rule mdb_chain_0_modify_map_replace)
      apply (subst modify_map_addr_com [where x = src], simp)+
      apply (rule mdb_chain_0_modify_map_replace)
      apply simp
      apply (rule mdb_chain_0_modify_map_prev)
      apply (subst modify_map_addr_com [where y = dest], simp add: sdneq [symmetric])+
      apply (subst modify_map_addr_com [where y = src], simp)
      apply assumption
      done
  qed
  thus ?thesis
    unfolding n_def n'_def
    apply (simp add: const_def)
    apply (rule mdb_chain_0_modify_map_prev)
    apply (subst modify_map_com [where g = "cteCap_update (%_. scap)"], case_tac x, simp)+
    apply (rule mdb_chain_0_modify_map_inv)
    apply (subst modify_map_com [where g = "cteCap_update (%_. dcap)"], case_tac x, simp)+
    apply (rule mdb_chain_0_modify_map_inv)
    apply simp_all
    done
qed

lemma (in mdb_swap) next_m_n2:
  "n \<turnstile> p \<leadsto> p' = m \<turnstile> s_d_swp p \<leadsto> s_d_swp p'"
  by (simp add: next_m_n)

lemma (in mdb_swap) n_src [simp]:
  "n src = Some (CTE dcap dest2_node)"
  unfolding n_def n'_def
  apply (simp)
  apply (subst modify_map_same | subst modify_map_other, simp add: dest2_node_def)+
  apply (simp add: src)
  done

lemma (in mdb_swap) swap_cases [case_names src_dest dest_src other]:
  assumes src_dest:
  "\<lbrakk>mdbNext src_node = dest; mdbPrev dest_node = src; mdbNext dest_node \<noteq> src; mdbPrev src_node \<noteq> dest\<rbrakk> \<Longrightarrow> P"
  and dest_src:
  "\<lbrakk>mdbNext dest_node = src; mdbPrev src_node = dest; mdbNext src_node \<noteq> dest; mdbPrev dest_node \<noteq> src\<rbrakk> \<Longrightarrow> P"
  and other:
  "\<lbrakk>mdbNext src_node \<noteq> dest; mdbPrev dest_node \<noteq> src; mdbNext dest_node \<noteq> src; mdbPrev src_node \<noteq> dest \<rbrakk> \<Longrightarrow> P"
  shows "P"
proof (cases "mdbNext src_node = dest")
  case True
  thus ?thesis
  proof (rule src_dest)
    from True show "mdbPrev dest_node = src"
      by simp
    show "mdbNext dest_node \<noteq> src"
    proof
      assume "mdbNext dest_node = src"
      hence "m \<turnstile> dest \<leadsto> src" using dest
        by - (rule next_fold, simp+)
      moreover have "m \<turnstile> src \<leadsto> dest" using src True
        by - (rule next_fold, simp+)
      finally show False by simp
    qed
    show "mdbPrev src_node \<noteq> dest"
    proof
      assume "mdbPrev src_node = dest"
      hence "mdbNext dest_node = src" using src
        by (clarsimp elim: dlistEp)
      hence "m \<turnstile> dest \<leadsto> src" using dest
        by - (rule next_fold, simp+)
      moreover have "m \<turnstile> src \<leadsto> dest" using src True
        by - (rule next_fold, simp+)
      finally show False by simp
    qed
  qed
next
  case False

  note firstFalse = False

  show ?thesis
  proof (cases "mdbNext dest_node = src")
    case True
    thus ?thesis
    proof (rule dest_src)
      from True show "mdbPrev src_node = dest" by simp
      show "mdbPrev dest_node \<noteq> src"
      proof
        assume "mdbPrev dest_node = src"
        hence "mdbNext src_node = dest" using dest
          by (clarsimp elim: dlistEp)
        hence "m \<turnstile> src \<leadsto> dest" using src
          by - (rule next_fold, simp+)
        moreover have "m \<turnstile> dest \<leadsto> src" using dest True
          by - (rule next_fold, simp+)
        finally show False by simp
      qed
    qed fact+
  next
    case False
    from firstFalse show ?thesis
    proof (rule other)
      show "mdbPrev dest_node \<noteq> src" and "mdbPrev src_node \<noteq> dest" using False firstFalse
        by simp+
    qed fact+
  qed
qed

lemma (in mdb_swap) src_prev_next [intro?]:
  "mdbPrev src_node \<noteq> 0 \<Longrightarrow> m \<turnstile> mdbPrev src_node \<leadsto> src"
  using src
  apply -
  apply (erule dlistEp)
    apply simp
  apply (rule next_fold)
   apply simp
  apply simp
  done

lemma (in mdb_swap) dest_prev_next [intro?]:
  "mdbPrev dest_node \<noteq> 0 \<Longrightarrow> m \<turnstile> mdbPrev dest_node \<leadsto> dest"
  using dest
  apply -
  apply (erule dlistEp)
    apply simp
  apply (rule next_fold)
   apply simp
  apply simp
  done

lemma (in mdb_swap) n_dest:
  "n dest = Some (CTE scap (MDB (if mdbNext src_node = dest then src else mdbNext src_node) (if mdbPrev src_node = dest then src else mdbPrev src_node) (mdbRevocable src_node) (mdbFirstBadged src_node)))"
  unfolding n_def n'_def using dest p_0
  apply (simp only: dest2_next dest2_prev)
  apply (cases "mdbPrev src_node = dest")
   apply (subgoal_tac "dest \<noteq> mdbNext src_node")
    apply (simp add: modify_map_same modify_map_other)
    apply (cases src_node, simp)
   apply clarsimp
  apply (cases "mdbNext src_node = dest")
   apply (simp add: modify_map_same modify_map_other)
   apply (cases src_node, simp)
  apply (simp add: modify_map_same modify_map_other)
  done

lemma (in mdb_swap) n_dest_prev:
  assumes md: "m (mdbPrev dest_node) = Some cte"
  shows "\<exists>cte'. n (mdbPrev dest_node) = Some cte'
  \<and> mdbNext (cteMDBNode cte') = (if dest = mdbNext src_node then mdbNext dest_node else src)
  \<and> mdbPrev (cteMDBNode cte') =
  (if (mdbNext src_node = mdbPrev dest_node \<or> dest = mdbNext src_node) then dest else
  mdbPrev (cteMDBNode cte))"
proof -
  have nz: "(mdbPrev dest_node) \<noteq> 0" using md
    by (rule dom_into_not0 [OF no_0 domI])

  show ?thesis
  proof (cases rule: cases2 [of "dest = mdbNext src_node"  "mdbNext src_node = mdbPrev dest_node"])
    case pos_pos thus ?thesis by simp
  next
    case neg_pos
    thus ?thesis using nz md
      unfolding n_def n'_def
      apply (simp only: dest2_next dest2_prev)
      apply (clarsimp simp add: modify_map_same modify_map_other)
      done
  next
    case pos_neg

    hence "(mdbPrev dest_node) = src" by simp
    thus ?thesis using pos_neg md p_0
      unfolding n_def n'_def
      apply (simp only: dest2_next dest2_prev)
      apply (simp add: modify_map_same modify_map_other del: dest2_parts )
      apply (simp only: next_unfold' dest2_next dest2_prev)
      apply (subst if_not_P)
      apply simp+
      done
  next
    case neg_neg
    thus ?thesis using md nz
      unfolding n_def n'_def
      apply (simp only: dest2_next dest2_prev)
      apply (clarsimp simp add: modify_map_same modify_map_other)
      done
  qed
qed

(* Dual of above *)
lemma (in mdb_swap) n_dest_next:
  assumes md: "m (mdbNext dest_node) = Some cte"
  shows "\<exists>cte'. n (mdbNext dest_node) = Some cte'
  \<and> mdbNext (cteMDBNode cte') = (if (src = mdbNext dest_node \<or> mdbNext dest_node = mdbPrev src_node) then dest else mdbNext (cteMDBNode cte))
  \<and> mdbPrev (cteMDBNode cte') =  (if src = mdbNext dest_node then mdbPrev dest_node else src)"
proof -
  have nz: "(mdbNext dest_node) \<noteq> 0" using md
    by (rule dom_into_not0 [OF no_0 domI])

  show ?thesis
  proof (cases rule: cases2 [of "src = mdbNext dest_node"  "mdbNext dest_node = mdbPrev src_node"])
    case pos_pos thus ?thesis by simp
  next
    case neg_pos
    hence "(mdbPrev src_node) \<noteq> dest"
      by - (rule, simp add: next_dest_prev_src_sym)
    thus ?thesis using nz md neg_pos
      unfolding n_def n'_def
      apply (simp only: dest2_next dest2_prev)
      apply (clarsimp simp add: modify_map_same modify_map_other)
      done
  next
    case pos_neg
    hence pd: "mdbPrev src_node = dest" by simp

    have "mdbNext src_node \<noteq> dest"
    proof
      assume a: "mdbNext src_node = dest"
      from pd have "mdbPrev src_node \<noteq> 0" by simp
      hence "m \<turnstile> mdbPrev src_node \<leadsto> src" ..
      also have "m \<turnstile> src \<leadsto> dest" using src next_fold a
        by auto
      finally show False using pd by simp
    qed
    thus ?thesis using md p_0 pd pos_neg nz
      unfolding n_def n'_def
      apply (simp only: dest2_next dest2_prev)
      apply (simp add: modify_map_same modify_map_other del: dest2_parts )
      apply (simp only: dest2_next dest2_prev)
      apply (subst if_P [OF refl])
      apply simp+
      done
  next
    case neg_neg
    thus ?thesis using md nz
      unfolding n_def n'_def
      apply (simp only: dest2_next dest2_prev)
      apply (clarsimp simp add: modify_map_same modify_map_other)
      done
  qed
qed

lemma (in mdb_swap) n_src_prev:
  assumes md: "m (mdbPrev src_node) = Some cte"
  shows "\<exists>cte'. n (mdbPrev src_node) = Some cte'
  \<and> mdbNext (cteMDBNode cte') = (if src = mdbNext dest_node then mdbNext src_node else dest)
  \<and> mdbPrev (cteMDBNode cte') =
  (if (mdbNext dest_node = mdbPrev src_node \<or> src = mdbNext dest_node) then src else
  mdbPrev (cteMDBNode cte))"
proof -
  have nz: "(mdbPrev src_node) \<noteq> 0" using md
    by (rule dom_into_not0 [OF no_0 domI])

  show ?thesis
  proof (cases rule: cases2 [of "dest = mdbNext src_node"  "mdbNext src_node = mdbPrev dest_node"])
    case pos_pos thus ?thesis by simp
  next
    case neg_pos
    thus ?thesis using nz md
      unfolding n_def n'_def
      apply (simp only: dest2_next dest2_prev)
      apply (clarsimp simp add: modify_map_same modify_map_other)
      done
  next
    case pos_neg

    hence "(mdbPrev dest_node) = src" by simp
    thus ?thesis using pos_neg md p_0
      unfolding n_def n'_def
      apply (simp only: dest2_next dest2_prev)
      apply (clarsimp simp add: modify_map_same modify_map_other del: dest2_parts )
      done
  next
    case neg_neg
    thus ?thesis using md nz
      unfolding n_def n'_def
      apply (simp only: dest2_next dest2_prev)
      by (clarsimp simp add: modify_map_same modify_map_other)
  qed
qed

(* Dual of above *)
lemma (in mdb_swap) n_src_next:
  assumes md: "m (mdbNext src_node) = Some cte"
  shows "\<exists>cte'. n (mdbNext src_node) = Some cte'
  \<and> mdbNext (cteMDBNode cte') = (if (dest = mdbNext src_node \<or> mdbNext src_node = mdbPrev dest_node) then src else mdbNext (cteMDBNode cte))
  \<and> mdbPrev (cteMDBNode cte') =  (if dest = mdbNext src_node then mdbPrev src_node else dest)"
proof -
  have nz: "(mdbNext src_node) \<noteq> 0" using md
    by (rule dom_into_not0 [OF no_0 domI])

  show ?thesis
  proof (cases rule: cases2 [of "src = mdbNext dest_node"  "mdbNext dest_node = mdbPrev src_node"])
    case pos_pos thus ?thesis by simp
  next
    case neg_pos
    hence "(mdbPrev src_node) \<noteq> dest"
      by - (rule, simp add: next_dest_prev_src_sym)
    thus ?thesis using nz md neg_pos
      unfolding n_def n'_def
      apply (simp only: dest2_next dest2_prev)
      by (clarsimp simp add: modify_map_same modify_map_other)
  next
    case pos_neg
    hence pd: "mdbPrev src_node = dest" by simp

    have "mdbNext src_node \<noteq> dest"
    proof
      assume a: "mdbNext src_node = dest"
      from pd have "mdbPrev src_node \<noteq> 0" by simp
      hence "m \<turnstile> mdbPrev src_node \<leadsto> src" ..
      also have "m \<turnstile> src \<leadsto> dest" using src using a next_fold by auto
      finally show False using pd by simp
    qed
    thus ?thesis using md p_0 pd pos_neg nz
      unfolding n_def n'_def
      apply (simp only: dest2_next dest2_prev)
      by (clarsimp simp add: modify_map_same modify_map_other del: dest2_parts )
  next
    case neg_neg
    thus ?thesis using md nz
      unfolding n_def n'_def
      apply (simp only: dest2_next dest2_prev)
      by (clarsimp simp add: modify_map_same modify_map_other)
  qed
qed

lemma (in mdb_swap) dest2_node_next:
  "mdbNext dest2_node = (if dest = mdbPrev src_node then dest else mdbNext dest_node)"
  unfolding dest2_node_def
  by simp

lemma (in mdb_swap) dest2_node_prev:
  "mdbPrev dest2_node = (if dest = mdbNext src_node then dest else mdbPrev dest_node)"
  unfolding dest2_node_def
  by simp

lemma (in mdb_swap) n_other:
  assumes     other: "p \<noteq> mdbPrev src_node" "p \<noteq> src" "p \<noteq> mdbNext src_node"
  "p \<noteq> mdbPrev dest_node" "p \<noteq> dest" "p \<noteq> mdbNext dest_node"
  shows   "n p = m p"
  using other
  unfolding n_def n'_def
  by (simp add: modify_map_other dest2_node_next dest2_node_prev)

lemma (in mdb_swap) dom_n_m:
  "dom n = dom m"
  unfolding n_def n'_def by simp

lemma (in mdb_swap) other_src_next_dest_src:
  fixes cte
  defines "p \<equiv> mdbNext (cteMDBNode cte)"
  assumes dest_src: "mdbNext dest_node = src"
  and     ps: "m (mdbNext src_node) = Some cte"
  and     p0: "p \<noteq> 0"
  shows  "p \<noteq> mdbPrev src_node" "p \<noteq> src" "p \<noteq> mdbNext src_node"
  "p \<noteq> mdbPrev dest_node" "p \<noteq> dest" "p \<noteq> mdbNext dest_node"
proof -
  have sn: "m \<turnstile> src \<leadsto> mdbNext src_node" ..
  also have pn: "m \<turnstile> mdbNext src_node \<leadsto> p" using ps
    by (simp add: next_unfold' p_def)
  finally have sp [intro?]: "m \<turnstile> src \<leadsto>\<^sup>+ p" .

  have "m \<turnstile> dest \<leadsto> mdbNext dest_node" ..
  also have "mdbNext dest_node = src" by fact+
  finally have ds [intro?]: "m \<turnstile> dest \<leadsto> src" .

  show "p \<noteq> mdbPrev src_node"
  proof
    assume a: "p = mdbPrev src_node"
    hence "mdbPrev src_node \<noteq> 0" using p0 by simp
    hence "m \<turnstile> mdbPrev src_node \<leadsto> src" ..
    hence "m \<turnstile> p \<leadsto> src" using a by simp
    thus False using sp by - (drule (1) trancl_into_trancl2, simp)
  qed

  show "p \<noteq> src"
  proof
    assume "p = src"
    also have "m \<turnstile> src \<leadsto> mdbNext src_node" ..
    also have "m \<turnstile> mdbNext src_node \<leadsto> p" by (rule pn)
    finally show False by simp
  qed

  show "p \<noteq> mdbNext src_node" using pn
    by clarsimp

  show "p \<noteq> mdbPrev dest_node"
  proof
    assume a: "p = mdbPrev dest_node"
    hence "mdbPrev dest_node \<noteq> 0" using p0 by simp
    hence "m \<turnstile> mdbPrev dest_node \<leadsto> dest" ..
    also have "m \<turnstile> dest \<leadsto> src" ..
    also have "m \<turnstile> src \<leadsto>\<^sup>+ p" ..
    finally show False using a by simp
  qed

  show "p \<noteq> dest"
  proof
    assume "p = dest"
    also have "m \<turnstile> dest \<leadsto> src" ..
    also have "m \<turnstile> src \<leadsto>\<^sup>+ p" ..
    finally show False by simp
  qed

  show "p \<noteq> mdbNext dest_node"
  proof
    assume "p = mdbNext dest_node"
    also have "mdbNext dest_node = src" by fact+
    also have "m \<turnstile> src \<leadsto>\<^sup>+ p" ..
    finally show False by simp
  qed
qed

lemma (in mdb_swap) other_src_prev_src_dest:
  fixes cte
  defines "p \<equiv> mdbPrev (cteMDBNode cte)"
  assumes src_dest: "mdbNext src_node = dest"
  and     ps: "m (mdbPrev src_node) = Some cte"
  and     p0: "p \<noteq> 0"
  shows  "p \<noteq> mdbPrev src_node" "p \<noteq> src" "p \<noteq> mdbNext src_node"
  "p \<noteq> mdbPrev dest_node" "p \<noteq> dest" "p \<noteq> mdbNext dest_node"
proof -
  note really_annoying_simps [simp del] = word_neq_0_conv

  have pp: "m \<turnstile> p \<leadsto> mdbPrev src_node"
    using p0 ps unfolding p_def
    by (cases cte, simp) (erule (1) prev_leadstoI [OF _ _ dlist])
  also have "mdbPrev src_node \<noteq> 0" using ps no_0
    by (rule no_0_neq)
  hence "m \<turnstile> mdbPrev src_node \<leadsto> src" ..
  finally have ps' [intro?]: "m \<turnstile> p \<leadsto>\<^sup>+ src" .

  from src_dest src have sd [intro?]: "m \<turnstile> src \<leadsto> dest"
    by (simp add: next_unfold')

  from ps' sd have pd [intro?]: "m \<turnstile> p \<leadsto>\<^sup>+ dest" ..

  show "p \<noteq> mdbPrev src_node" using pp
    by clarsimp

  show "p \<noteq> src" using ps' by clarsimp

  show "p \<noteq> mdbNext src_node"
  proof
    assume a: "p = mdbNext src_node"
    also have "m \<turnstile> src \<leadsto> mdbNext src_node" ..
    also have "m \<turnstile> p \<leadsto>\<^sup>+ src" ..
    finally show False by simp
  qed

  from src_dest have "mdbPrev dest_node = src" by simp
  hence "mdbPrev dest_node \<noteq> 0" using mdb_ptr_src.p_0
    by (rule ssubst)
  thus "p \<noteq> mdbPrev dest_node"
    unfolding p_def using ps src_dest
    by (cases cte, auto simp add: p_prev_qe)

  show "p \<noteq> dest"
  proof
    assume "p = dest"
    hence "dest = p" ..
    also have "m \<turnstile> p \<leadsto>\<^sup>+ src" ..
    also have "m \<turnstile> src \<leadsto> dest" ..
    finally show False by simp
  qed

  show "p \<noteq> mdbNext dest_node"
  proof
    assume "p = mdbNext dest_node"
    also have "m \<turnstile> dest \<leadsto> mdbNext dest_node" ..
    also have "m \<turnstile> p \<leadsto>\<^sup>+ src" ..
    also have "m \<turnstile> src \<leadsto> dest" ..
    finally show False by simp
  qed
qed

lemma (in mdb_swap) other_dest_next_src_dest:
  fixes cte
  defines "p \<equiv> mdbNext (cteMDBNode cte)"
  assumes src_dest: "mdbNext src_node = dest"
  and     ps: "m (mdbNext dest_node) = Some cte"
  and     p0: "p \<noteq> 0"
  shows  "p \<noteq> mdbPrev src_node" "p \<noteq> src" "p \<noteq> mdbNext src_node"
  "p \<noteq> mdbPrev dest_node" "p \<noteq> dest" "p \<noteq> mdbNext dest_node"
proof -
  have sn: "m \<turnstile> dest \<leadsto> mdbNext dest_node" ..
  also have pn: "m \<turnstile> mdbNext dest_node \<leadsto> p" using ps
    by (simp add: next_unfold' p_def)
  finally have sp [intro?]: "m \<turnstile> dest \<leadsto>\<^sup>+ p" .

  have "m \<turnstile> src \<leadsto> mdbNext src_node" ..
  also have "mdbNext src_node = dest" by fact+
  finally have ds [intro?]: "m \<turnstile> src \<leadsto> dest" .

  show "p \<noteq> mdbPrev dest_node"
  proof
    assume a: "p = mdbPrev dest_node"
    hence "mdbPrev dest_node \<noteq> 0" using p0 by simp
    hence "m \<turnstile> mdbPrev dest_node \<leadsto> dest" ..
    hence "m \<turnstile> p \<leadsto> dest" using a by simp
    thus False using sp by - (drule (1) trancl_into_trancl2, simp)
  qed

  show "p \<noteq> dest"
  proof
    assume "p = dest"
    also have "m \<turnstile> dest \<leadsto> mdbNext dest_node" ..
    also have "m \<turnstile> mdbNext dest_node \<leadsto> p" by (rule pn)
    finally show False by simp
  qed

  show "p \<noteq> mdbNext dest_node" using pn
    by clarsimp

  show "p \<noteq> mdbPrev src_node"
  proof
    assume a: "p = mdbPrev src_node"
    hence "mdbPrev src_node \<noteq> 0" using p0 by simp
    hence "m \<turnstile> mdbPrev src_node \<leadsto> src" ..
    also have "m \<turnstile> src \<leadsto> dest" ..
    also have "m \<turnstile> dest \<leadsto>\<^sup>+ p" ..
    finally show False using a by simp
  qed

  show "p \<noteq> src"
  proof
    assume "p = src"
    also have "m \<turnstile> src \<leadsto> dest" ..
    also have "m \<turnstile> dest \<leadsto>\<^sup>+ p" ..
    finally show False by simp
  qed

  show "p \<noteq> mdbNext src_node"
  proof
    assume "p = mdbNext src_node"
    also have "mdbNext src_node = dest" by fact+
    also have "m \<turnstile> dest \<leadsto>\<^sup>+ p" ..
    finally show False by simp
  qed
qed

lemma (in mdb_swap) other_dest_prev_dest_src:
  fixes cte
  defines "p \<equiv> mdbPrev (cteMDBNode cte)"
  assumes dest_src: "mdbNext dest_node = src"
  and     ps: "m (mdbPrev dest_node) = Some cte"
  and     p0: "p \<noteq> 0"
  shows  "p \<noteq> mdbPrev src_node" "p \<noteq> src" "p \<noteq> mdbNext src_node"
  "p \<noteq> mdbPrev dest_node" "p \<noteq> dest" "p \<noteq> mdbNext dest_node"
proof -
  note really_annoying_simps [simp del] = word_neq_0_conv

  have pp: "m \<turnstile> p \<leadsto> mdbPrev dest_node"
    using p0 ps unfolding p_def
    by (cases cte, simp) (erule (1) prev_leadstoI [OF _ _ dlist])
  also have "mdbPrev dest_node \<noteq> 0" using ps no_0
    by (rule no_0_neq)
  hence "m \<turnstile> mdbPrev dest_node \<leadsto> dest" ..
  finally have ps' [intro?]: "m \<turnstile> p \<leadsto>\<^sup>+ dest" .

  from dest_src dest have sd [intro?]: "m \<turnstile> dest \<leadsto> src"
    by (simp add: next_unfold')

  from ps' sd have pd [intro?]: "m \<turnstile> p \<leadsto>\<^sup>+ src" ..

  show "p \<noteq> mdbPrev dest_node" using pp
    by clarsimp

  show "p \<noteq> dest" using ps' by clarsimp

  show "p \<noteq> mdbNext dest_node"
  proof
    assume a: "p = mdbNext dest_node"
    also have "m \<turnstile> dest \<leadsto> mdbNext dest_node" ..
    also have "m \<turnstile> p \<leadsto>\<^sup>+ dest" ..
    finally show False by simp
  qed

  from dest_src have "mdbPrev src_node = dest" by simp
  hence s0: "mdbPrev src_node \<noteq> 0" using p_0
    by (rule ssubst)
  have sn: "mdbNext src_node \<noteq> dest" using dest_src
    by (clarsimp simp: s0)
  show "p \<noteq> mdbPrev src_node"
    unfolding p_def using ps dest_src
    by (cases cte) (clarsimp simp: mdb_ptr_src.p_prev_qe sn s0)

  show "p \<noteq> src"
  proof
    assume "p = src"
    hence "src = p" ..
    also have "m \<turnstile> p \<leadsto>\<^sup>+ dest" ..
    also have "m \<turnstile> dest \<leadsto> src" ..
    finally show False by simp
  qed

  show "p \<noteq> mdbNext src_node"
  proof
    assume "p = mdbNext src_node"
    also have "m \<turnstile> src \<leadsto> mdbNext src_node" ..
    also have "m \<turnstile> p \<leadsto>\<^sup>+ dest" ..
    also have "m \<turnstile> dest \<leadsto> src" ..
    finally show False by simp
  qed
qed

lemma (in mdb_swap) swap_ptr_cases [case_names p_src_prev p_src p_src_next p_dest_prev p_dest p_dest_next p_other]:
  "\<lbrakk>p = mdbPrev src_node \<Longrightarrow> P; p = src \<Longrightarrow> P; p = mdbNext src_node \<Longrightarrow> P;
  p = mdbPrev dest_node \<Longrightarrow> P; p = dest \<Longrightarrow> P; p = mdbNext dest_node \<Longrightarrow> P;
  \<lbrakk>p \<noteq> mdbPrev src_node; p \<noteq> src; p \<noteq> mdbNext src_node;
  p \<noteq> mdbPrev dest_node; p \<noteq> dest; p \<noteq> mdbNext dest_node\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by auto

lemma (in mdb_swap) prev_not0_into_dom:
  assumes np: "n p = Some cte"
  and n0: "mdbPrev (cteMDBNode cte) \<noteq> 0"
  shows "mdbPrev (cteMDBNode cte) \<in> dom m"
proof -
  note p_next_qe_src = mdb_ptr_src.p_next_qe

  note annoying_simps [simp del]
    = next_dest_prev_src  next_dest_prev_src_sym prev_dest_next_src prev_dest_next_src_sym

  note really_annoying_simps [simp del] = word_neq_0_conv

  from np have "p \<in> dom n" by (rule domI)
  then obtain ctep where mp: "m p = Some ctep"
    by (clarsimp simp add: dom_n_m)

  show ?thesis
  proof (cases rule: swap_ptr_cases [where p = p])
    case p_src_prev
    thus ?thesis using mp np n0 src dest
      apply simp
      apply (frule n_src_prev)
      apply (auto simp: elim: dlistEp)
      done
  next
    case p_src
    thus ?thesis using mp np n0 src dest
      apply (clarsimp simp add: dest2_node_prev)
      apply safe
       apply simp+
      apply (erule dlistEp, fastforce)
      apply simp
      done
  next
    case p_src_next
    thus ?thesis using mp np n0 src dest
      apply simp
      apply (frule n_src_next)
      apply (auto simp: elim: dlistEp)
      done
  next
    case p_dest_prev
    thus ?thesis using mp np n0 src dest
      apply simp
      apply (frule n_dest_prev)
      apply (auto elim: dlistEp)
      done
  next
    case p_dest
    thus ?thesis using mp np n0 src dest
      apply (clarsimp simp: n_dest)
      apply (erule dlistEp, fastforce)
      apply simp
      done
  next
    case p_dest_next
    thus ?thesis using mp np n0 src dest
      apply simp
      apply (frule n_dest_next)
      apply (auto simp: elim: dlistEp)
      done
  next
    case p_other
    thus ?thesis using mp np n0 src dest
      by (auto simp: n_other elim: dlistEp)
  qed
qed

lemma (in mdb_swap) cteSwap_dlist_helper:
  shows "valid_dlist n"
proof
  fix p cte
  assume np: "n p = Some cte" and n0: "mdbPrev (cteMDBNode cte) \<noteq> 0"
  let ?thesis =
    "\<exists>cte'. n (mdbPrev (cteMDBNode cte)) = Some cte' \<and> mdbNext (cteMDBNode cte') = p"
  let ?mn = "mdbPrev (cteMDBNode cte)"

  note p_prev_qe_src = mdb_ptr_src.p_prev_qe

  note annoying_simps [simp del]
    = next_dest_prev_src  next_dest_prev_src_sym prev_dest_next_src prev_dest_next_src_sym

  note really_annoying_simps [simp del] = word_neq_0_conv

  from np have domn: "p \<in> dom n" by (rule domI)
  then obtain ctep where mp: "m p = Some ctep"
    by (clarsimp simp add: dom_n_m)

  have dd: "mdbPrev (cteMDBNode cte) \<in> dom n"
    by (subst dom_n_m, rule prev_not0_into_dom) fact+
  then obtain cte' where mmn: "m (mdbPrev (cteMDBNode cte)) = Some cte'"
    by (clarsimp simp add: dom_n_m)

  have dest_src_pn: "\<lbrakk>mdbPrev src_node \<noteq> 0; mdbNext src_node = dest \<rbrakk>
    \<Longrightarrow> mdbNext dest_node \<noteq> mdbPrev src_node"
  proof (rule not_sym, rule)
    assume "mdbPrev src_node = mdbNext dest_node" and "mdbPrev src_node \<noteq> 0"
      and msd: "mdbNext src_node = dest"
    hence "m \<turnstile> mdbNext dest_node \<leadsto> src"
      by (auto dest!: src_prev intro: next_fold)
    also have "m \<turnstile> src \<leadsto> dest" using src next_fold msd by auto
    also have "m \<turnstile> dest \<leadsto> mdbNext dest_node" ..
    finally show False by simp
  qed

  have src_dest_pn': "\<lbrakk> mdbPrev dest_node \<noteq> 0; mdbNext dest_node = src \<rbrakk>
    \<Longrightarrow> mdbNext src_node \<noteq> mdbPrev dest_node"
  proof (rule not_sym, rule)
    assume a: "mdbPrev dest_node = mdbNext src_node" and "mdbPrev dest_node \<noteq> 0"
      and msd: "mdbNext dest_node = src"
    hence a': "mdbPrev dest_node \<noteq> 0" by simp
    have "m \<turnstile> src \<leadsto> mdbPrev dest_node" by (rule next_fold, rule src, simp add: a)
    also have "m \<turnstile> mdbPrev dest_node \<leadsto> dest" using a' ..
    also have "m \<turnstile> dest \<leadsto> src" using dest msd
      by - (rule next_fold, simp+)
    finally show False by simp
  qed

  from domn have domm: "p \<in> dom m" by (simp add: dom_n_m)
  with no_0 have p0: "p \<noteq> 0"
    by (rule dom_into_not0)

  show ?thesis
  proof (cases rule: swap_ptr_cases [where p = p])
    case p_src_prev

    hence psrc [intro?]: "m \<turnstile> p \<leadsto> src" using p0
      by (clarsimp intro!: src_prev_next)

    show ?thesis
    proof (cases rule: swap_cases)
      case dest_src
      hence "?mn = src" using p_src_prev dest src np n0
        using [[hypsubst_thin = true]]
        apply clarsimp
        apply (drule n_src_prev)
        apply (clarsimp simp: dest_src )
        done
      thus ?thesis using p_src_prev mmn dest_src
        by (simp add: dest2_node_def)
    next
      case src_dest

      hence "mdbNext dest_node \<noteq> mdbPrev src_node" using p_src_prev p0
        by - (rule dest_src_pn, simp)
      hence "?mn = mdbPrev (cteMDBNode ctep)" using p_src_prev src np mp p0 dest src_dest
        by simp (drule n_src_prev, clarsimp)
      thus ?thesis using p_src_prev src_dest mmn n0 mp
        apply simp
        apply (subst n_other [OF other_src_prev_src_dest])
        apply simp+
        apply (erule dlistEp [OF mp, simplified])
        apply simp
        done
    next
      case other

      show ?thesis
      proof (cases "mdbPrev src_node = mdbNext dest_node")
        case True thus ?thesis using p_src_prev mmn other np mp other
          by simp (drule n_dest_next, simp add: dest2_node_next split: if_split_asm)
      next
        let ?mn' = "mdbPrev (cteMDBNode ctep)"
        case False
        hence mnmn: "?mn = ?mn'" using p_src_prev src np mp p0 dest other
          by simp (drule n_src_prev, clarsimp)

        have mnp: "m \<turnstile> ?mn' \<leadsto> p" using mp mnmn n0 dlist
          by (cases ctep, auto intro!: prev_leadstoI)

        note superFalse = False

        show ?thesis
        proof (cases "?mn' = mdbNext dest_node")
          case True
          thus ?thesis using mmn p_src_prev superFalse n0 mp
            by (simp add: mnmn) (frule n_dest_next, auto elim: dlistEp simp: other [symmetric])
        next
          case False

          have eq: "n ?mn' = m ?mn'"
          proof (rule n_other)

            show "?mn' \<noteq> mdbPrev dest_node" using mp other p_src_prev n0 mnmn
              by (cases ctep, simp add: p_prev_qe)

            show "?mn' \<noteq> dest"
            proof
              assume "?mn' = dest"
              hence "mdbNext dest_node = mdbPrev src_node" using mnp dest p_src_prev
                by (simp add: next_unfold')
              thus False using superFalse by simp
            qed

            show "?mn' \<noteq> mdbNext dest_node" by fact+

            show "?mn' \<noteq> mdbPrev src_node" using mp other p_src_prev n0 mnmn
              by (cases ctep, simp add: p_prev_qe_src)

            show "?mn' \<noteq> src" using src mnp p_src_prev p0
              by (clarsimp simp add: next_unfold')

            show "?mn' \<noteq> mdbNext src_node"
            proof
              assume a: "?mn' = mdbNext src_node"
              have "m \<turnstile> ?mn' \<leadsto> p" using mnp .
              also have "m \<turnstile> p \<leadsto> src" ..
              also have "m \<turnstile> src \<leadsto> mdbNext src_node" ..
              finally show False using a by simp
            qed
          qed
          thus ?thesis using mnmn mmn mp p_src_prev n0
            by - (erule dlistEp [where p = p], simp+)
        qed
      qed
    qed
  next
    case p_src

    show ?thesis
    proof (cases rule: swap_cases)
      case src_dest
      hence "?mn = dest" using p_src src dest np
        by (cases cte, clarsimp simp add: dest2_node_def)
      thus ?thesis using p_src src_dest
        by (simp add: n_dest)
    next
      case dest_src
      hence "?mn = mdbPrev dest_node" using p_src src np
        by (clarsimp simp: dest2_node_def)
      thus ?thesis using p_src mmn dest_src
        apply (simp add: n_dest dest2_node_prev)
        apply (drule n_dest_prev)
        apply clarsimp
        done
    next
      case other
      hence "?mn = mdbPrev dest_node" using p_src src np
        by (clarsimp simp add: dest2_node_def)
      thus ?thesis using p_src mmn other
        by simp (drule n_dest_prev, clarsimp)
    qed
  next
    case p_src_next

    show ?thesis
    proof (cases rule: swap_cases)
      case src_dest
      hence "?mn = mdbPrev src_node" using p_src_next src dest np mp
        by (clarsimp simp: n_dest)
      thus ?thesis using p_src_next mmn src_dest
        by simp (drule n_src_prev, clarsimp)
    next
      case dest_src
      hence "?mn = dest" using p_src_next src np mp
        by simp (drule n_src_next, simp)
      thus ?thesis using p_src_next dest_src
        by (simp add: n_dest)
    next
      case other
      hence "?mn = dest" using p_src_next src np mp
        by simp (drule n_src_next, simp)
      thus ?thesis using p_src_next mmn other
        by (simp add: n_dest)
    qed
  next
    case p_dest_prev

    hence pdest [intro?]: "m \<turnstile> p \<leadsto> dest" using p0
      by (clarsimp intro!: dest_prev_next)

    show ?thesis
    proof (cases rule: swap_cases)
      case src_dest
      hence "?mn = dest" using p_dest_prev src dest np n0
        using [[hypsubst_thin = true]]
        apply clarsimp
        apply (drule n_dest_prev)
        apply (clarsimp simp: src_dest )
        done
      thus ?thesis using p_dest_prev mmn src_dest
        by (simp add: n_dest)
    next
      case dest_src

      hence "mdbNext src_node \<noteq> mdbPrev dest_node" using p_dest_prev p0
        by - (rule src_dest_pn', simp)
      hence "?mn = mdbPrev (cteMDBNode ctep)" using p_dest_prev dest np mp p0 src dest_src
        by simp (drule n_dest_prev, clarsimp)
      thus ?thesis using p_dest_prev dest_src mmn n0 mp
        apply simp
        apply (subst n_other [OF other_dest_prev_dest_src])
        apply simp+
        apply (erule dlistEp [OF mp, simplified])
        apply simp
        done
    next
      case other

      show ?thesis
      proof (cases "mdbNext src_node = mdbPrev dest_node")
        case True thus ?thesis using p_dest_prev mmn other np mp other
          by simp (drule n_dest_prev, simp add: n_dest)
      next
        let ?mn' = "mdbPrev (cteMDBNode ctep)"
        case False
        hence mnmn: "?mn = ?mn'" using p_dest_prev src np mp p0 dest other
          by simp (drule n_dest_prev, clarsimp)

        have mnp: "m \<turnstile> ?mn' \<leadsto> p" using mp mnmn n0 dlist
          by (cases ctep, auto intro!: prev_leadstoI)

        note superFalse = False

        show ?thesis
        proof (cases "?mn' = mdbNext src_node")
          case True
          thus ?thesis using mmn p_dest_prev superFalse n0 mp
            by (simp add: mnmn) (frule n_src_next, auto elim: dlistEp simp: other [symmetric])
        next
          case False

          have eq: "n ?mn' = m ?mn'"
          proof (rule n_other)
            show "?mn' \<noteq> mdbPrev src_node" using mp other p_dest_prev n0 mnmn
              by (cases ctep, simp add: p_prev_qe_src)

            show "?mn' \<noteq> src"
            proof
              assume "?mn' = src"
              hence "mdbNext src_node = mdbPrev dest_node" using mnp src p_dest_prev
                by (simp add: next_unfold')
              thus False using superFalse by simp
            qed

            show "?mn' \<noteq> mdbNext src_node" by fact+

            show "?mn' \<noteq> mdbPrev dest_node" using mp other p_dest_prev n0 mnmn
              by (cases ctep, simp add: p_prev_qe)

            show "?mn' \<noteq> dest" using dest mnp p_dest_prev p0
              by (clarsimp simp add: next_unfold')

            show "?mn' \<noteq> mdbNext dest_node"
            proof
              assume a: "?mn' = mdbNext dest_node"
              have "m \<turnstile> ?mn' \<leadsto> p" using mnp .
              also have "m \<turnstile> p \<leadsto> dest" ..
              also have "m \<turnstile> dest \<leadsto> mdbNext dest_node" ..
              finally show False using a by simp
            qed
          qed
          thus ?thesis using mnmn mmn mp p_dest_prev n0
            by - (erule dlistEp [where p = p], simp+)
        qed
      qed
    qed
  next
    case p_dest

    show ?thesis
    proof (cases rule: swap_cases)
      case dest_src
      hence "?mn = src" using p_dest dest src np
        by (cases cte, clarsimp simp add: n_dest)
      thus ?thesis using p_dest dest_src
        by (simp add: dest2_node_next)
    next
      case src_dest
      hence "?mn = mdbPrev src_node" using p_dest dest np
        by (clarsimp simp: n_dest)
      thus ?thesis using p_dest mmn src_dest
        apply (simp add: n_src n_dest)
        apply (drule n_src_prev)
        apply clarsimp
        done
    next
      case other
      hence "?mn = mdbPrev src_node" using p_dest dest np
        by (clarsimp simp add: n_dest)
      thus ?thesis using p_dest mmn other
        by simp (drule n_src_prev, clarsimp)
    qed
  next
    case p_dest_next

    show ?thesis
    proof (cases rule: swap_cases)
      case dest_src
      hence "?mn = mdbPrev dest_node" using p_dest_next dest src np mp
        by (clarsimp simp: dest2_node_def)
      thus ?thesis using p_dest_next mmn dest_src
        by simp (drule n_dest_prev, clarsimp)
    next
      case src_dest
      hence "?mn = src" using p_dest_next dest np mp
        by simp (drule n_dest_next, simp)
      thus ?thesis using p_dest_next src_dest
        by (simp add: dest2_node_def)
    next
      case other
      hence "?mn = src" using p_dest_next dest np mp
        by simp (drule n_dest_next, simp)
      thus ?thesis using p_dest_next mmn other
        by (simp add: dest2_node_def)
    qed
  next
    case p_other
    hence eq: "n p = m p" by (rule n_other)
    hence eq': "cte = ctep" using mp np by simp

    have mns: "?mn \<noteq> src"
    proof
      assume "?mn = src"
      hence "p = mdbNext src_node" using mp mmn src eq' n0
        by (auto elim: dlistEp)
      thus False using p_other by simp
    qed

    have mnsn: "?mn \<noteq> mdbPrev src_node"
    proof
      assume "?mn = mdbPrev src_node"
      hence "src = p" using mp eq' n0
        by (cases ctep, clarsimp dest!: p_prev_qe_src)
      thus False using p_other by simp
    qed

    have mnd: "?mn \<noteq> dest"
    proof
      assume "?mn = dest"
      hence "p = mdbNext dest_node" using mp mmn dest eq' n0
        by (auto elim: dlistEp)
      thus False using p_other by simp
    qed

    have mndn: "?mn \<noteq> mdbPrev dest_node"
    proof
      assume "?mn = mdbPrev dest_node"
      hence "dest = p" using mp eq' n0
        by (cases ctep, clarsimp dest!: p_prev_qe)
      thus False using p_other by simp
    qed

    from dd obtain cten where nmn: "n ?mn = Some cten" by auto

    have mnext: "mdbNext (cteMDBNode cte') = p" using mp mmn
      by - (erule dlistEp, rule dom_into_not0 [OF no_0], (clarsimp simp: eq')+)

    show ?thesis
    proof (cases rule: cases2 [of "?mn = mdbNext src_node" "?mn = mdbNext dest_node"])
      case pos_pos
      thus ?thesis using n0 by simp
    next
      case pos_neg
      thus ?thesis using  mmn nmn mnd mndn
        by simp (drule n_src_next, simp add: mnext eq' next_dest_prev_src_sym)
    next
      case neg_pos
      thus ?thesis using mmn nmn mns mnsn
        by simp (drule n_dest_next, simp add: mnext eq' annoying_simps)
    next
      case neg_neg
      thus ?thesis using mmn nmn mns mnsn mnd mndn mnext
        by (simp add: n_other)
    qed
  qed
next
  fix p cte
  assume np: "n p = Some cte" and n0: "mdbNext (cteMDBNode cte) \<noteq> 0"
  let ?thesis =
    "\<exists>cte'. n (mdbNext (cteMDBNode cte)) = Some cte' \<and> mdbPrev (cteMDBNode cte') = p"
  let ?mn = "mdbNext (cteMDBNode cte)"

  note p_next_qe_src = mdb_ptr_src.p_next_qe

  note annoying_simps [simp del]
    = next_dest_prev_src  next_dest_prev_src_sym prev_dest_next_src prev_dest_next_src_sym

  from np have domn: "p \<in> dom n" by (rule domI)
  then obtain ctep where mp: "m p = Some ctep"
    by (clarsimp simp add: dom_n_m)

  from n0 have dd: "mdbNext (cteMDBNode cte) \<in> dom n" using np
    apply -
    apply (erule contrapos_pp)
    apply (cases cte)
    apply (drule ndom_is_0D [OF _ cteSwap_chain no_0_n, where ptr = p])
    apply simp+
    done

  then obtain cte' where mmn: "m (mdbNext (cteMDBNode cte)) = Some cte'"
    by (clarsimp simp add: dom_n_m)

  have src_dest_pn: "\<lbrakk>mdbNext dest_node \<noteq> 0; mdbNext src_node = dest \<rbrakk>
    \<Longrightarrow> mdbPrev src_node \<noteq> mdbNext dest_node"
  proof
    assume "mdbPrev src_node = mdbNext dest_node" and "mdbNext dest_node \<noteq> 0"
      and msd: "mdbNext src_node = dest"
    hence "m \<turnstile> mdbNext dest_node \<leadsto> src"
      by (auto dest!: src_prev intro: next_fold)
    also have "m \<turnstile> src \<leadsto> dest" using src using msd next_fold by auto
    also have "m \<turnstile> dest \<leadsto> mdbNext dest_node" ..
    finally show False by simp
  qed

  have src_dest_pn': "\<lbrakk> mdbNext src_node \<noteq> 0; mdbNext dest_node = src \<rbrakk>
    \<Longrightarrow> mdbPrev dest_node \<noteq> mdbNext src_node"
  proof
    assume a: "mdbPrev dest_node = mdbNext src_node" and "mdbNext src_node \<noteq> 0"
      and msd: "mdbNext dest_node = src"
    hence a': "mdbPrev dest_node \<noteq> 0" by simp
    have "m \<turnstile> src \<leadsto> mdbPrev dest_node" by (rule next_fold, rule src, simp add: a)
    also have "m \<turnstile> mdbPrev dest_node \<leadsto> dest" using a' ..
    also have "m \<turnstile> dest \<leadsto> src" using dest msd
      by - (rule next_fold, simp+)
    finally show False by simp
  qed

  from domn have domm: "p \<in> dom m" by (simp add: dom_n_m)
  with no_0 have p0: "p \<noteq> 0"
    by (rule dom_into_not0)

  from np have npp: "n \<turnstile> p \<leadsto> mdbNext (cteMDBNode cte)"
    by (simp add: next_fold)
  hence swp: "m \<turnstile> s_d_swp p \<leadsto> s_d_swp (mdbNext (cteMDBNode cte))"
    by (simp add: next_m_n)

  show ?thesis
  proof (cases rule: swap_ptr_cases [where p = p])
    case p_src_prev

    hence p0': "mdbPrev src_node \<noteq> 0" using p0 by simp
    hence stp: "m \<turnstile> mdbPrev src_node \<leadsto> src" ..

    show ?thesis
    proof (cases rule: swap_cases)
      case src_dest
      hence "?mn = dest" using stp np mp p_src_prev
        by (simp add: next_m_n s_d_swap_def  next_unfold') (drule n_src_prev, clarsimp)
      thus ?thesis using p_src_prev n_dest src_dest
        by auto
    next
      case dest_src
      hence "?mn = mdbNext src_node" using stp np mp p_src_prev
        by (clarsimp simp add: next_m_n s_d_swap_def  next_unfold' n_dest)
      thus ?thesis using p_src_prev mmn dest_src
        by simp (drule n_src_next, clarsimp)
    next
      case other
      hence "?mn = dest" using stp np mp p_src_prev
        by (clarsimp simp add: next_m_n s_d_swap_def next_unfold' annoying_simps
          dest!: n_src_prev)
      thus ?thesis using p_src_prev other
        by (simp add: n_dest)
    qed
  next
    case p_src

    show ?thesis
    proof (cases rule: swap_cases)
      case src_dest
      hence "?mn = mdbNext dest_node" using p_src src np
        by (cases cte, clarsimp simp add: dest2_node_def)
      thus ?thesis using p_src mmn src_dest
        by simp (drule n_dest_next, clarsimp)
    next
      case dest_src
      hence "?mn = dest" using p_src src np
        by (cases cte, clarsimp simp add: dest2_node_def)
      thus ?thesis using p_src mmn dest_src
        by (simp add: n_dest)
    next
      case other
      hence "?mn = mdbNext dest_node" using p_src src np
        by (cases cte, clarsimp simp add: dest2_node_def)
      thus ?thesis using p_src mmn other
        by simp (drule n_dest_next, clarsimp)
    qed
  next
    case p_src_next

    show ?thesis
    proof (cases rule: swap_cases)
      case src_dest
      hence "?mn = src" using p_src_next dest np
        by (cases cte, clarsimp simp: n_dest)
      thus ?thesis using p_src_next mmn src_dest
        by (simp add: dest2_node_def)
    next
      case dest_src

      hence "mdbPrev dest_node \<noteq> mdbNext src_node" using p_src_next p0
        by - (rule src_dest_pn', simp+)
      hence "?mn = mdbNext (cteMDBNode ctep)" using p_src_next src np mp p0 dest dest_src
        by simp (drule n_src_next, clarsimp)
      thus ?thesis using p_src_next dest_src mmn n0 mp
        apply simp
        apply (subst n_other [OF other_src_next_dest_src])
        apply simp+
        apply (erule dlistEn [OF mp, simplified])
        apply simp
        done
    next
      case other

      show ?thesis
      proof (cases "mdbNext src_node = mdbPrev dest_node")
        case True thus ?thesis using p_src_next mmn other np mp other
          by simp (drule n_dest_prev, simp add: dest2_node_prev split: if_split_asm)
      next
        let ?mn' = "mdbNext (cteMDBNode ctep)"
        case False
        hence mnmn: "?mn = ?mn'" using p_src_next src np mp p0 dest other
          by simp (drule n_src_next, clarsimp)

        note superFalse = False

        show ?thesis
        proof (cases "?mn' = mdbPrev dest_node")
          case True
          thus ?thesis using mmn p_src_next superFalse n0 mp
            by (simp add: mnmn) (frule n_dest_prev, auto elim: dlistEn)
        next
          case False

          have eq: "n ?mn' = m ?mn'"
          proof (rule n_other)
            have "m \<turnstile> src \<leadsto> mdbNext src_node" ..
            hence sp [intro?]: "m \<turnstile> src \<leadsto> p" by (simp add: p_src_next)
            also have mmn'[intro?]: "m \<turnstile> p \<leadsto> ?mn'" using mp by (simp add: next_unfold')
            finally have smn [intro?]: "m \<turnstile> src \<leadsto>\<^sup>+ ?mn'" .
              (* Sigh *)

            show "?mn' \<noteq> mdbPrev src_node"
            proof
              assume a: "?mn' = mdbPrev src_node"
              also have "mdbPrev src_node \<noteq> 0" using mmn
                by - (rule dom_into_not0 [OF no_0 domI], simp add: a [symmetric] mnmn)
              hence "m \<turnstile> mdbPrev src_node \<leadsto> src" ..
              also have "m \<turnstile> src \<leadsto>\<^sup>+ ?mn'" ..
              finally show False by simp
            qed

            show "?mn' \<noteq> src" using smn
              by clarsimp

            show "?mn' \<noteq> mdbNext src_node"
            proof
              assume "?mn' = mdbNext src_node"
              also have "mdbNext src_node = p" by (simp add: p_src_next)
              also have "m \<turnstile> p \<leadsto> ?mn'" ..
              finally show False by simp
            qed

            show "?mn' \<noteq> mdbPrev dest_node" by fact+
            show "?mn' \<noteq> dest" using src mp p_src_next mnmn swp
              by (clarsimp simp add: next_unfold' s_d_swap_def split: if_split_asm)
            show "?mn' \<noteq> mdbNext dest_node" using mnmn mp p_src_next swp False superFalse other n0
              by (cases ctep, clarsimp simp add: next_unfold' s_d_swap_def dest!: p_next_eq)
          qed
          thus ?thesis using mnmn mmn mp p_src_next n0
            by - (erule dlistEn [where p = p], simp+)
        qed
      qed
    qed
  next
    case p_dest_prev
    hence p0': "mdbPrev dest_node \<noteq> 0" using p0 by simp
    hence stp: "m \<turnstile> mdbPrev dest_node \<leadsto> dest" ..

    show ?thesis
    proof (cases rule: swap_cases)
      case dest_src
      hence "?mn = src" using stp np mp p_dest_prev
        by (simp add: next_m_n s_d_swap_def  next_unfold') (drule n_dest_prev, clarsimp)
      thus ?thesis using p_dest_prev dest_src
        by (simp add: n_src dest2_node_prev)
    next
      case src_dest
      hence "?mn = mdbNext dest_node" using stp np mp p_dest_prev
        by (simp add: annoying_simps) (drule n_dest_prev, clarsimp)
      thus ?thesis using p_dest_prev mmn src_dest
        by simp (drule n_dest_next, clarsimp)
    next
      case other
      hence "?mn = src" using stp np mp p_dest_prev
        by simp (drule n_dest_prev, simp)
      thus ?thesis using p_dest_prev other
        by (simp add: n_src dest2_node_prev)
    qed
  next
    case p_dest

    show ?thesis
    proof (cases rule: swap_cases)
      case dest_src
      hence "?mn = mdbNext src_node" using p_dest dest src np
        by (cases cte, clarsimp simp add: n_dest)
      thus ?thesis using p_dest mmn dest_src
        by simp (drule n_src_next, clarsimp)
    next
      case src_dest
      hence "?mn = src" using p_dest dest np
        by (cases cte, clarsimp simp add: n_dest)
      thus ?thesis using p_dest mmn src_dest
        by (simp add: n_src dest2_node_prev)
    next
      case other
      hence "?mn = mdbNext src_node" using p_dest dest np
        by (cases cte, clarsimp simp add: n_dest)
      thus ?thesis using p_dest mmn other
        by simp (drule n_src_next, clarsimp)
    qed
  next
    case p_dest_next

    show ?thesis
    proof (cases rule: swap_cases)
      case dest_src
      hence "?mn = dest" using p_dest_next src np
        by (cases cte, clarsimp simp: n_src dest2_node_def)
      thus ?thesis using p_dest_next mmn dest_src
        by (simp add: dest2_node_def n_dest)
    next
      case src_dest

      hence "mdbPrev src_node \<noteq> mdbNext dest_node" using p_dest_next p0
        by - (rule src_dest_pn, simp+)
      hence "?mn = mdbNext (cteMDBNode ctep)" using p_dest_next dest np mp p0 src src_dest
        by simp (drule n_dest_next, clarsimp)
      thus ?thesis using p_dest_next src_dest mmn n0 mp
        apply simp
        apply (subst n_other [OF other_dest_next_src_dest])
        apply simp+
        apply (erule dlistEn [OF mp, simplified])
        apply simp
        done
    next
      case other

      show ?thesis
      proof (cases "mdbNext dest_node = mdbPrev src_node")
        case True thus ?thesis using p_dest_next mmn other np mp other
          by simp (drule n_src_prev, simp add: dest2_node_prev n_dest )
      next
        let ?mn' = "mdbNext (cteMDBNode ctep)"
        case False
        hence mnmn: "?mn = ?mn'" using p_dest_next src np mp p0 dest other
          by simp (drule n_dest_next, clarsimp)

        note superFalse = False

        show ?thesis
        proof (cases "?mn' = mdbPrev src_node")
          case True
          thus ?thesis using mmn p_dest_next superFalse n0 mp
            by (simp add: mnmn) (frule n_src_prev, auto elim: dlistEn)
        next
          case False

          have eq: "n ?mn' = m ?mn'"
          proof (rule n_other)
            have "m \<turnstile> dest \<leadsto> mdbNext dest_node" ..
            hence sp [intro?]: "m \<turnstile> dest \<leadsto> p" by (simp add: p_dest_next)
            also have mmn'[intro?]: "m \<turnstile> p \<leadsto> ?mn'" using mp by (simp add: next_unfold')
            finally have smn [intro?]: "m \<turnstile> dest \<leadsto>\<^sup>+ ?mn'" .
              (* Sigh *)

            show "?mn' \<noteq> mdbPrev dest_node"
            proof
              assume a: "?mn' = mdbPrev dest_node"
              also have "mdbPrev dest_node \<noteq> 0" using mmn
                by - (rule dom_into_not0 [OF no_0 domI], simp add: a [symmetric] mnmn)
              hence "m \<turnstile> mdbPrev dest_node \<leadsto> dest" ..
              also have "m \<turnstile> dest \<leadsto>\<^sup>+ ?mn'" ..
              finally show False by simp
            qed

            show "?mn' \<noteq> dest" using smn
              by clarsimp

            show "?mn' \<noteq> mdbNext dest_node"
            proof
              assume "?mn' = mdbNext dest_node"
              also have "mdbNext dest_node = p" by (simp add: p_dest_next)
              also have "m \<turnstile> p \<leadsto> ?mn'" ..
              finally show False by simp
            qed

            show "?mn' \<noteq> mdbPrev src_node" by fact+
            show "?mn' \<noteq> src" using dest mp p_dest_next mnmn swp
              by (clarsimp simp add: next_unfold' s_d_swap_def split: if_split_asm)
            show "?mn' \<noteq> mdbNext src_node" using mnmn mp p_dest_next swp False superFalse other n0
              by (cases ctep, clarsimp simp add: next_unfold' s_d_swap_def
                dest!: p_next_qe_src)
          qed
          thus ?thesis using mnmn mmn mp p_dest_next n0
            by - (erule dlistEn [where p = p], simp+)
        qed
      qed
    qed
  next
    case p_other
    hence eq: "n p = m p" by (rule n_other)
    hence eq': "cte = ctep" using mp np by simp

    have mns: "?mn \<noteq> src"
    proof
      assume "?mn = src"
      hence "p = mdbPrev src_node" using mp mmn src eq' n0
        by (auto elim: dlistEn)
      thus False using p_other by simp
    qed

    have mnsn: "?mn \<noteq> mdbNext src_node"
    proof
      assume "?mn = mdbNext src_node"
      hence "src = p" using mp eq' n0
        by (cases ctep, clarsimp dest!: p_next_qe_src)
      thus False using p_other by simp
    qed

    have mnd: "?mn \<noteq> dest"
    proof
      assume "?mn = dest"
      hence "p = mdbPrev dest_node" using mp mmn dest eq' n0
        by (auto elim: dlistEn)
      thus False using p_other by simp
    qed

    have mndn: "?mn \<noteq> mdbNext dest_node"
    proof
      assume "?mn = mdbNext dest_node"
      hence "dest = p" using mp eq' n0
        by (cases ctep, clarsimp dest!: p_next_qe)
      thus False using p_other by simp
    qed

    from dd obtain cten where nmn: "n ?mn = Some cten" by auto

    have mprev: "mdbPrev (cteMDBNode cte') = p" using mp mmn
      by - (erule dlistEn, rule dom_into_not0 [OF no_0], (clarsimp simp: eq')+)

    show ?thesis
    proof (cases rule: cases2 [of "?mn = mdbPrev src_node" "?mn = mdbPrev dest_node"])
      case pos_pos
      thus ?thesis using n0 by simp
    next
      case pos_neg
      thus ?thesis using  mmn nmn mnd mndn
        by simp (drule n_src_prev, simp add: mprev eq' next_dest_prev_src_sym)
    next
      case neg_pos
      thus ?thesis using mmn nmn mns mnsn
        by simp (drule n_dest_prev, simp add: mprev eq' annoying_simps)
    next
      case neg_neg
      thus ?thesis using mmn nmn mns mnsn mnd mndn mprev
        by (simp add: n_other)
    qed
  qed
qed

lemma sameRegionAs_eq_child:
  "\<lbrakk> sameRegionAs cap c; weak_derived' c c' \<rbrakk>
  \<Longrightarrow> sameRegionAs cap c'"
  by (clarsimp simp: weak_derived'_def ARM_HYP.sameRegionAs_def2) (* FIXME arch-split *)

lemma sameRegionAs_eq_parent:
  "\<lbrakk> sameRegionAs c cap; weak_derived' c c' \<rbrakk>
  \<Longrightarrow> sameRegionAs c' cap"
  by (clarsimp simp: weak_derived'_def ARM_HYP.sameRegionAs_def2) (* FIXME arch-split *)

context mdb_swap
begin

lemma sameRegionAs_dcap_parent:
  "sameRegionAs dcap cap = sameRegionAs dest_cap cap"
  apply (rule iffI)
   apply (erule sameRegionAs_eq_parent, rule weak_derived_sym', rule dest_derived)
  apply (erule sameRegionAs_eq_parent, rule dest_derived)
  done

lemma sameRegionAs_dcap_child:
  "sameRegionAs cap dcap = sameRegionAs cap dest_cap"
  apply (rule iffI)
   apply (erule sameRegionAs_eq_child, rule weak_derived_sym', rule dest_derived)
  apply (erule sameRegionAs_eq_child, rule dest_derived)
  done

lemma sameRegionAs_scap_parent:
  "sameRegionAs scap cap = sameRegionAs src_cap cap"
  apply (rule iffI)
   apply (erule sameRegionAs_eq_parent, rule weak_derived_sym', rule src_derived)
  apply (erule sameRegionAs_eq_parent, rule src_derived)
  done

lemma sameRegionAs_scap_child:
  "sameRegionAs cap scap = sameRegionAs cap src_cap"
  apply (rule iffI)
   apply (erule sameRegionAs_eq_child, rule weak_derived_sym', rule src_derived)
  apply (erule sameRegionAs_eq_child, rule src_derived)
  done

lemmas region_simps =
  sameRegionAs_scap_child sameRegionAs_scap_parent
  sameRegionAs_dcap_child sameRegionAs_dcap_parent

lemma master_srcI:
  "\<lbrakk> \<And>cap. F (capMasterCap cap) = F cap \<rbrakk>
      \<Longrightarrow> F scap = F src_cap"
  using src_derived
  by (clarsimp simp: weak_derived'_def elim!: master_eqI)

lemma isEPsrc:
  "isEndpointCap scap = isEndpointCap src_cap"
  by (rule master_srcI, rule gen_isCap_Master)

lemma isIRQControl_src:
  "(scap = IRQControlCap) = (src_cap = IRQControlCap)"
  using src_derived
  by (auto simp: gen_isCap_simps weak_derived'_def)

lemma isIRQHandler_src:
  "isIRQHandlerCap scap = isIRQHandlerCap src_cap"
  using src_derived
  by (fastforce simp: gen_isCap_simps weak_derived'_def)

lemma isEPbadge_src:
  "isEndpointCap src_cap \<Longrightarrow> capEPBadge scap = capEPBadge src_cap"
  using src_derived
  by (clarsimp simp: gen_isCap_simps weak_derived'_def)

lemma isNTFNsrc:
  "isNotificationCap scap = isNotificationCap src_cap"
  by (rule master_srcI, rule gen_isCap_Master)

lemma isNTFNbadge_src:
  "isNotificationCap src_cap \<Longrightarrow> capNtfnBadge scap = capNtfnBadge src_cap"
  using src_derived
  by (clarsimp simp: gen_isCap_simps weak_derived'_def)

lemma isEPdest:
  "isEndpointCap dcap = isEndpointCap dest_cap"
  using dest_derived by (fastforce simp: gen_isCap_simps weak_derived'_def)

lemma isIRQHandler_dest:
  "isIRQHandlerCap dcap = isIRQHandlerCap dest_cap"
  using dest_derived by (fastforce simp: gen_isCap_simps weak_derived'_def)

lemma isIRQControl_dest:
  "(dcap = IRQControlCap) = (dest_cap = IRQControlCap)"
  using dest_derived by (auto simp: gen_isCap_simps weak_derived'_def)

lemma isEPbadge_dest:
  "isEndpointCap dest_cap \<Longrightarrow> capEPBadge dcap = capEPBadge dest_cap"
  using dest_derived by (auto simp: weak_derived'_def gen_isCap_simps)

lemma isNTFNdest:
  "isNotificationCap dcap = isNotificationCap dest_cap"
  using dest_derived by (auto simp: weak_derived'_def gen_isCap_simps)

lemma isNTFNbadge_dest:
  "isNotificationCap dest_cap \<Longrightarrow> capNtfnBadge dcap = capNtfnBadge dest_cap"
  using dest_derived by (auto simp: weak_derived'_def gen_isCap_simps)

lemmas ep_simps =
  isEPsrc isEPbadge_src isNTFNsrc isNTFNbadge_src
  isEPdest isEPbadge_dest isNTFNdest isNTFNbadge_dest

(* FIXME arch-split: arch dependent part of mdb_swap proofs, no arch_global_naming because of locale *)
context begin
interpretation Arch .

lemma isSGI_src:
  "isArchSGISignalCap scap = isArchSGISignalCap src_cap"
  using src_derived
  by (fastforce simp: isCap_simps weak_derived'_def)

lemma isSGI_dest:
  "isArchSGISignalCap dcap = isArchSGISignalCap dest_cap"
  using dest_derived by (fastforce simp: isCap_simps weak_derived'_def)

lemma SGI_dcap_neq:
  "isArchSGISignalCap dest_cap \<Longrightarrow> (cap \<noteq> dcap) = (cap \<noteq> dest_cap)"
  using dest_derived
  by (auto simp: weak_derived'_def isCap_simps)

lemma SGI_dcap_neq_cap:
  "isArchSGISignalCap cap \<Longrightarrow> (dcap \<noteq> cap) = (dest_cap \<noteq> cap)"
  using dest_derived
  by (auto simp: weak_derived'_def isCap_simps)

lemma SGI_scap_neq:
  "isArchSGISignalCap src_cap \<Longrightarrow> (cap \<noteq> scap) = (cap \<noteq> src_cap)"
  using src_derived
  by (auto simp: weak_derived'_def isCap_simps)

lemma SGI_scap_neq_cap:
  "isArchSGISignalCap cap \<Longrightarrow> (scap \<noteq> cap) = (src_cap \<noteq> cap)"
  using src_derived
  by (auto simp: weak_derived'_def isCap_simps)


(* export to generic below *)

lemma mdb_chunked_arch_assms_scap[simp]:
  "mdb_chunked_arch_assms scap =  mdb_chunked_arch_assms src_cap"
  by (simp add: mdb_chunked_arch_assms_def isSGI_src)

lemma mdb_chunked_arch_assms_dcap[simp]:
  "mdb_chunked_arch_assms dcap =  mdb_chunked_arch_assms dest_cap"
  by (simp add: mdb_chunked_arch_assms_def isSGI_dest)


lemma valid_arch_badges_src[simp]:
  "valid_arch_badges scap c node = valid_arch_badges src_cap c node"
  by (simp add: valid_arch_badges_def SGI_scap_neq_cap)

lemma valid_arch_badges_dest[simp]:
  "valid_arch_badges c dcap node = valid_arch_badges c dest_cap node"
  by (simp add: valid_arch_badges_def isSGI_dest SGI_dcap_neq)

lemma valid_arch_badges_dest'[simp]:
  "valid_arch_badges dcap c node = valid_arch_badges dest_cap c node"
  by (simp add: valid_arch_badges_def  SGI_dcap_neq_cap)

lemma valid_arch_badges_src'[simp]:
  "valid_arch_badges c scap node = valid_arch_badges c src_cap node"
  by (simp add: valid_arch_badges_def isSGI_src SGI_scap_neq)

end

lemmas cap_simps =
  ep_simps
  isIRQControl_src isSGI_src isIRQHandler_src
  isIRQControl_dest isSGI_dest isIRQHandler_dest
  SGI_dcap_neq SGI_dcap_neq_cap SGI_scap_neq SGI_scap_neq_cap

end

lemma sameRegion_ep:
  "\<lbrakk> sameRegionAs cap cap'; isEndpointCap cap \<rbrakk> \<Longrightarrow> isEndpointCap cap'"
  by (auto simp: ARM_HYP.sameRegionAs_def3 ARM_HYP.isCap_simps)

lemma sameRegion_ntfn:
  "\<lbrakk> sameRegionAs cap cap'; isNotificationCap cap \<rbrakk> \<Longrightarrow> isNotificationCap cap'"
  by (auto simp: ARM_HYP.sameRegionAs_def3 ARM_HYP.isCap_simps)

lemma (in mdb_swap) cteSwap_valid_badges:
  "valid_badges n"
proof -
  from valid
  have "valid_badges m" ..
  thus ?thesis using src dest
    apply (clarsimp simp add: valid_badges_def next_m_n2)
    apply (frule_tac p=p in n_cap)
    apply (frule_tac p=p' in n_cap)
    apply (drule badge_n)+
    apply (clarsimp simp: s_d_swap_def sameRegion_ntfn sameRegion_ep cap_simps region_simps
                    split: if_split_asm;
           blast intro: valid_arch_badges_firstBadged)
    done
qed

lemma (in mdb_swap) m_trancl:
  assumes "m \<turnstile> p \<leadsto>\<^sup>+ p'"
  shows "n \<turnstile> s_d_swp p \<leadsto>\<^sup>+ s_d_swp p'"
  using assms
proof induct
  case (base x)
  thus ?case by (fastforce simp: next_m_n)
next
  case (step x y)
  thus ?case by (fastforce simp: next_m_n elim: trancl_trans)
qed

lemma (in mdb_swap) n_trancl:
  "n \<turnstile> p \<leadsto>\<^sup>+ p' = m \<turnstile> s_d_swp p \<leadsto>\<^sup>+ s_d_swp p'"
proof
  assume "n \<turnstile> p \<leadsto>\<^sup>+ p'"
  thus "m \<turnstile> s_d_swp p \<leadsto>\<^sup>+ s_d_swp p'"
    by induct (auto simp: next_m_n2 elim!: trancl_trans)
next
  assume "m \<turnstile> s_d_swp p \<leadsto>\<^sup>+ s_d_swp p'"
  thus "n \<turnstile> p \<leadsto>\<^sup>+ p'"
    by (fastforce dest: m_trancl)
qed

lemma (in mdb_swap) n_rtrancl:
  "n \<turnstile> p \<leadsto>\<^sup>* p' = m \<turnstile> s_d_swp p \<leadsto>\<^sup>* s_d_swp p'"
  by (simp add: rtrancl_eq_or_trancl n_trancl)

lemma (in mdb_swap) n_cap_eq':
  "(\<exists>n'. n p = Some (CTE cap n')) =
   (if p = src
    then cap = dcap
    else if p = dest
    then cap = scap
    else \<exists>n'. m p = Some (CTE cap n'))"
  using src dest
  apply simp
  apply (rule conjI, clarsimp)
   apply (rule iffI)
    apply (fastforce dest: n_cap)
   subgoal by (simp add: n_def modify_map_if dest2_node_def n'_def, auto)
  apply clarsimp
  apply (rule conjI, fastforce)
  apply clarsimp
  apply (rule iffI)
   apply (fastforce dest: n_cap)
  apply (simp add: n_def modify_map_cases n'_def)
  apply (simp add: dest2_node_def)
  apply auto[1]
     apply (cases "mdbNext dest_node = 0")
      apply (cases "mdbNext src_node = 0")
       apply simp
      apply simp
      apply (cases "mdbPrev dest_node = mdbNext src_node")
       apply simp
      apply simp
     apply simp
     apply (cases "mdbPrev dest_node = mdbNext src_node")
      apply simp
     apply simp
    apply (cases "mdbNext dest_node = p")
     apply simp
     apply fastforce
    apply simp
    apply (cases "mdbPrev dest_node = p")
     apply simp
    apply simp
   apply (cases "mdbNext dest_node = p")
    apply simp
    apply (cases "mdbPrev dest_node = p")
     apply simp
     apply fastforce
    apply simp
    apply (cases "mdbPrev src_node = p", simp)
    apply simp
   apply simp
   apply (cases "mdbPrev dest_node = p", simp)
    apply fastforce
   apply simp
   apply (cases "mdbPrev src_node = p", simp)
   apply simp
  apply (cases "mdbNext dest_node = p")
   apply simp
   apply (cases "mdbPrev dest_node = p")
    apply simp
    apply fastforce
   apply simp
   apply (cases "mdbPrev src_node = p", simp)
   apply simp
  apply simp
  apply (cases "mdbPrev dest_node = p", simp)
   apply fastforce
  apply simp
  apply (cases "mdbPrev src_node = p", simp)
  apply simp
  done

lemma (in mdb_swap) n_cap_eq:
  "(\<exists>n'. n p = Some (CTE cap n')) =
  (\<exists>n'. if p = src then m (s_d_swp p) = Some (CTE dest_cap n') \<and> cap = dcap
        else if p = dest then m (s_d_swp p) = Some (CTE src_cap n') \<and> cap = scap
        else m (s_d_swp p) = Some (CTE cap n'))"
  apply (simp add: s_d_swp_def n_cap_eq' src dest)
  apply (auto simp: s_d_swap_def)
  done

lemma (in mdb_swap) cteSwap_chunked:
  "mdb_chunked n"
proof -
  from valid
  have "mdb_chunked m" ..
  thus ?thesis
    apply (clarsimp simp add: mdb_chunked_def is_chunk_def n_trancl n_rtrancl n_cap_eq)
    apply (case_tac "p = dest")
     apply simp
     apply (case_tac "p' = src")
      apply (clarsimp simp add: region_simps cap_simps)
      apply (erule_tac x=src in allE)
      apply (erule_tac x=dest in allE)
      apply clarsimp
      apply (erule disjE)
       apply clarsimp
       apply (rule conjI)
        apply clarsimp
        apply (erule_tac x="s_d_swap p'' src dest" in allE)
        apply clarsimp
        apply (case_tac "p'' = dest", simp)
        apply simp
        apply (case_tac "p'' = src")
         apply (clarsimp simp: region_simps)
        apply simp
       apply clarsimp
       apply (drule (1) trancl_trans)
       apply simp
      apply simp
      apply (rule conjI)
       apply clarsimp
       apply (drule (1) trancl_trans)
       apply simp
      apply clarsimp
      apply (erule_tac x="s_d_swap p'' src dest" in allE)
      apply clarsimp
      apply (case_tac "p'' = dest")
       apply (clarsimp simp: region_simps)
      apply simp
      apply (case_tac "p'' = src", simp)
      apply simp
     apply (clarsimp simp: region_simps cap_simps)
     apply (erule_tac x=src in allE)
     apply clarsimp
     apply (erule_tac x="s_d_swap p' src dest" in allE)
     apply clarsimp
     apply (erule impE)
      apply (clarsimp simp: s_d_swap_def)
     apply clarsimp
     apply (erule disjE)
      apply clarsimp
      apply (rule conjI)
       apply clarsimp
       apply (case_tac "p''=dest", simp)
       apply clarsimp
       apply (case_tac "p''=src")
        apply (clarsimp simp: dest)
        apply (clarsimp simp: region_simps)
        apply (erule_tac x=dest in allE)
        apply (clarsimp simp: dest)
       apply clarsimp
      apply clarsimp
      apply (drule (1) trancl_trans, simp)
     apply clarsimp
     apply (rule conjI)
      apply clarsimp
      apply (drule (1) trancl_trans, simp)
     apply clarsimp
     apply (case_tac "p''=dest")
      apply (clarsimp simp: region_simps)
      apply (erule_tac x=src in allE)
      apply clarsimp
     apply clarsimp
     apply (case_tac "p''=src")
      apply (simp add: dest region_simps)
      apply (erule_tac x=dest in allE)
      apply (clarsimp simp: dest)
     apply simp
    apply clarsimp
    apply (case_tac "p'=dest")
     apply clarsimp
     apply (case_tac "p=src")
      apply (clarsimp simp: region_simps cap_simps)
      apply (erule_tac x=dest in allE)
      apply (erule_tac x=src in allE)
      apply clarsimp
      apply (erule disjE)
       apply clarsimp
       apply (rule conjI)
        apply clarsimp
        apply (case_tac "p''=dest")
         apply (simp add: region_simps)
        apply simp
        apply (case_tac "p''=src")
         apply (simp add: region_simps)
        apply simp
       apply clarsimp
       apply (drule (1) trancl_trans)
       apply simp
      apply clarsimp
      apply (rule conjI)
       apply clarsimp
       apply (drule (1) trancl_trans)
       apply simp
      apply clarsimp
      apply (case_tac "p''=dest")
       apply (simp add: region_simps)
      apply simp
      apply (case_tac "p''=src")
       apply (simp add: region_simps)
       apply (erule_tac x="dest" in allE)
       apply simp
      apply simp
     apply clarsimp
     apply (erule_tac x="s_d_swap p src dest" in allE)
     apply (erule_tac x="src" in allE)
     apply (clarsimp simp: region_simps)
     apply (rule conjI)
      apply clarsimp
      apply (case_tac "p''=dest")
       apply (simp add: region_simps)
      apply (case_tac "p''=src")
       apply (simp add: region_simps dest)
       apply (erule_tac x=dest in allE)
       apply (clarsimp simp: dest)
      apply simp
     apply clarsimp
     apply (case_tac "p''=dest")
      apply (simp add: region_simps)
     apply (case_tac "p''=src")
      apply (simp add: region_simps dest)
      apply (erule_tac x=dest in allE)
      apply (clarsimp simp: dest)
     apply simp
    apply clarsimp
    apply (case_tac "p'=src")
     apply clarsimp
     apply (erule_tac x="s_d_swap p src dest" in allE)
     apply (erule_tac x=dest in allE)
     apply (clarsimp simp: region_simps)
     apply (erule impE)
      apply (clarsimp simp: s_d_swap_def)
     apply clarsimp
     apply (rule conjI)
      apply clarsimp
      apply (case_tac "p''=src")
       apply (simp add: region_simps)
      apply (case_tac "p''=dest")
       apply (simp add: src region_simps)
       apply (erule_tac x=src in allE)
       apply (simp add: src)
      apply clarsimp
     apply clarsimp
     apply (case_tac "p''=src")
      apply (simp add: region_simps)
     apply (case_tac "p''=dest")
      apply (simp add: src region_simps)
      apply (erule_tac x=src in allE)
      apply (simp add: src)
     apply clarsimp
    apply clarsimp
    apply (case_tac "p=src")
     apply clarsimp
     apply (erule_tac x="dest" in allE)
     apply (erule_tac x="s_d_swap p' src dest" in allE)
     apply (clarsimp simp: region_simps cap_simps)
     apply (erule impE)
      apply (clarsimp simp: s_d_swap_def)
     apply clarsimp
     apply (rule conjI)
      apply clarsimp
      apply (case_tac "p''=dest")
       apply (simp add: src region_simps)
       apply (erule_tac x=src in allE)
       apply (simp add: src)
      apply simp
      apply (case_tac "p''=src")
       apply (simp add: region_simps)
      apply simp
     apply clarsimp
     apply (case_tac "p''=dest")
      apply (simp add: src region_simps)
      apply (erule_tac x=src in allE)
      apply (simp add: src)
     apply simp
     apply (case_tac "p''=src")
      apply (simp add: region_simps)
      apply (erule_tac x=dest in allE)
      apply (simp add: dest)
     apply simp
    apply clarsimp
    apply (erule_tac x="s_d_swap p src dest" in allE)
    apply (erule_tac x="s_d_swap p' src dest" in allE)
    apply clarsimp
    apply (rule conjI)
     apply clarsimp
     apply (case_tac "p''=dest")
      apply (simp add: src region_simps)
      apply (erule_tac x=src in allE)
      apply (simp add: src)
     apply (case_tac "p''=src")
      apply (simp add: region_simps)
      apply (erule_tac x=dest in allE)
      apply (simp add: dest)
     apply simp
    apply clarsimp
    apply (case_tac "p''=dest")
     apply (simp add: src region_simps)
     apply (erule_tac x=src in allE)
     apply (simp add: src)
    apply (case_tac "p''=src")
     apply (simp add: region_simps)
     apply (erule_tac x=dest in allE)
     apply (simp add: dest)
    apply simp
    done
qed

(* FIXME: make this a locale from the start *)
locale weak_der' =
  fixes old new
  assumes derived: "weak_derived' new old"
begin

lemma isUntyped_new:
  "isUntypedCap new = isUntypedCap old"
  using derived by (auto simp: weak_derived'_def gen_isCap_simps)

lemma capRange_new:
  "capRange new = capRange old"
  using derived
  apply (clarsimp simp: weak_derived'_def)
  apply (rule master_eqI, rule capRange_Master)
  apply simp
  done

lemma untypedRange_new:
  "untypedRange new = untypedRange old"
  using derived
  apply (clarsimp simp add: weak_derived'_def)
  apply (rule master_eqI, rule untypedRange_Master)
  apply simp
  done

lemmas range_simps [simp] =
  isUntyped_new capRange_new untypedRange_new

lemma isReplyMaster_eq:
  "(isReplyCap new \<and> capReplyMaster new)
      = (isReplyCap old \<and> capReplyMaster old)"
  using derived
  by (fastforce simp: weak_derived'_def gen_isCap_simps)

end

lemma master_eqE:
  "\<lbrakk> capMasterCap cap = capMasterCap cap';
      \<And>cap. F (capMasterCap cap) = F cap \<rbrakk>
          \<Longrightarrow> F cap = F cap'"
  by (rule master_eqI, assumption, simp)

lemma weak_derived_Null' [simp]:
  "weak_derived' cap NullCap = (cap = NullCap)"
  by (auto simp add: weak_derived'_def)

lemma Null_weak_derived_Null' [simp]:
  "weak_derived' NullCap cap = (cap = NullCap)"
  by (auto simp add: weak_derived'_def)

lemma distinct_zombies_switchE:
  "\<lbrakk> distinct_zombies m; m x = Some old_x; m y = Some old_y;
             capMasterCap (cteCap old_x) = capMasterCap (cteCap new_y);
             capMasterCap (cteCap old_y) = capMasterCap (cteCap new_x) \<rbrakk>
       \<Longrightarrow> distinct_zombies (m(x \<mapsto> new_x, y \<mapsto> new_y))"
  apply (cases "x = y")
   apply clarsimp
   apply (erule(1) distinct_zombies_sameMasterE)
   apply simp
  apply (drule_tac F="\<lambda>cap. (isUntypedCap cap, isZombie cap, isArchPageCap cap,
                             capClass cap, capUntypedPtr cap, capBits cap)"
               in master_eqE,
         simp add: gen_isCap_Master capClass_Master capUntyped_Master capBits_Master
                   isArchFrameCap_capMasterCap)+
  (* FIXME arch-split *)
  apply (simp add: distinct_zombies_def distinct_zombie_caps_def ARM_HYP.arch_isCap_Master
                    split del: if_split)
  apply (intro allI)
  apply (drule_tac x="(id (x := y, y := x)) ptr" in spec)
  apply (drule_tac x="(id (x := y, y := x)) ptr'" in spec)
  apply (clarsimp split del: if_split)
  apply (clarsimp simp: gen_isCap_Master
                        capBits_Master
                        capClass_Master
                        capUntyped_Master
                  split: if_split_asm )
  done

context mdb_swap
begin

lemma weak_der_src:
  "weak_der' src_cap scap"
  apply unfold_locales
  apply (rule weak_derived_sym')
  apply (rule src_derived)
  done

lemma weak_der_dest:
  "weak_der' dest_cap dcap"
  apply unfold_locales
  apply (rule weak_derived_sym')
  apply (rule dest_derived)
  done

lemmas src_range_simps [simp] = weak_der'.range_simps [OF weak_der_src]
lemmas dest_range_simps [simp] = weak_der'.range_simps [OF weak_der_dest]

lemma caps_contained:
  "caps_contained' n"
  using valid
  apply (clarsimp simp: valid_mdb_ctes_def caps_contained'_def)
  apply (drule n_cap)+
  apply (simp split: if_split_asm)
          apply (clarsimp dest!: capRange_untyped)
         apply fastforce
        apply fastforce
       apply fastforce
      apply fastforce
     apply (clarsimp dest!: capRange_untyped)
    apply fastforce
   apply fastforce
  apply fastforce
  done

lemma untyped_mdb_n:
  "untyped_mdb' n"
  using untyped_mdb
  apply (simp add: n_cap_eq untyped_mdb'_def descendants_of'_def parency)
  apply clarsimp
  apply (case_tac "p=dest")
   apply clarsimp
   apply (case_tac "p'=dest", simp)
   apply (case_tac "p'=src", simp)
   apply clarsimp
  apply clarsimp
  apply (case_tac "p'=dest")
   apply clarsimp
   apply (case_tac "p=src", simp)
   apply clarsimp
  apply clarsimp
  apply (case_tac "p=src")
   apply clarsimp
   apply (case_tac "p'=src",simp)
   apply clarsimp
  apply clarsimp
  apply (case_tac "p'=src",simp)
  apply clarsimp
  done


lemma untyped_inc_n:
  assumes untyped_eq: "isUntypedCap src_cap \<Longrightarrow> scap = src_cap"
                      "isUntypedCap dest_cap \<Longrightarrow> dcap = dest_cap"
  shows "untyped_inc' n"
  using untyped_inc
  apply (simp add: n_cap_eq untyped_inc'_def descendants_of'_def parency)
  apply clarsimp
  apply (erule_tac x="s_d_swap p src dest" in allE)
  apply (erule_tac x="s_d_swap p' src dest" in allE)
  apply (case_tac "p=dest")
   apply simp
   apply (case_tac "p'=src", simp)
   apply (clarsimp simp:untyped_eq)
   apply (case_tac "p'=dest", simp)
   apply (clarsimp simp: s_d_swap_def untyped_eq)
  apply clarsimp
  apply (case_tac "p=src")
   apply clarsimp
   apply (case_tac "p'=dest", simp)
   apply (clarsimp simp:untyped_eq)
   apply (case_tac "p'=src", simp)
   apply (clarsimp simp:untyped_eq)
  apply clarsimp
  apply (case_tac "p'=src")
   apply (clarsimp simp:untyped_eq)
  apply simp
  apply (case_tac "p'=dest", clarsimp simp:untyped_eq)
  apply (clarsimp simp:untyped_eq)
  done

lemma n_next:
  "n p = Some cte \<Longrightarrow> \<exists>z. m (s_d_swp p) = Some z \<and> s_d_swp (mdbNext (cteMDBNode cte)) = mdbNext (cteMDBNode z)"
  apply (drule conjI [THEN exI [THEN next_m_n2 [THEN iffD1, unfolded mdb_next_unfold]]])
   apply (rule refl)
  apply assumption
  done

lemma n_prevD:
  notes if_cong [cong] option.case_cong [cong]
  shows "n \<turnstile> p \<leftarrow> p' \<Longrightarrow> m \<turnstile> s_d_swp p \<leftarrow> s_d_swp p'"
  apply (cases "p'=0")
   apply (simp add: mdb_prev_def)
  apply (cases "p=0")
   apply (clarsimp simp: mdb_prev_def s_d_swap_def)
   apply (rule conjI)
    apply clarsimp
    apply (simp add: n_dest)
    apply (case_tac z)
    apply (clarsimp simp: src split: if_split_asm)
   apply clarsimp
   apply (rule conjI)
    apply (clarsimp simp: dest)
    apply (simp add: dest2_node_def split: if_split_asm)
   apply clarsimp
   apply (case_tac z)
   apply clarsimp
   apply (simp add: n_def n'_def modify_map_if dest2_node_def)
   apply (insert src dest)[1]
   apply (clarsimp split: if_split_asm)
  apply (simp add: Invariants_H.valid_dlist_prevD [OF cteSwap_dlist_helper, symmetric])
  apply (simp add: Invariants_H.valid_dlist_prevD [OF dlist, symmetric] next_m_n2)
  done

lemma n_prev:
  "n p = Some cte \<Longrightarrow> \<exists>z. m (s_d_swp p) = Some z \<and> s_d_swp (mdbPrev (cteMDBNode cte)) = mdbPrev (cteMDBNode z)"
  apply (drule conjI [THEN exI [THEN n_prevD [unfolded mdb_prev_def]]])
   apply (rule refl)
  apply assumption
  done

lemma nullcaps_n: "valid_nullcaps n"
proof -
  from valid have "valid_nullcaps m" ..
  thus ?thesis using dest_derived src_derived
    apply (clarsimp simp: valid_nullcaps_def)
    apply (frule n_cap)
    apply (frule revokable)
    apply (frule badge_n)
    apply (frule n_prev)
    apply (drule n_next)
    apply (insert src dest)
    apply (frule_tac x=src in spec)
    apply (frule_tac x=dest in spec)
    apply (erule_tac x=p in allE)
    apply simp
    apply (case_tac n)
    apply (clarsimp simp: s_d_swap_def nullMDBNode_def ARM_HYP_H.nullPointer_def split: if_split_asm)
    done
qed

lemma ut_rev_n: "ut_revocable' n"
proof -
  from valid have "ut_revocable' m" ..
  thus ?thesis using dest_derived src_derived src dest
    apply (clarsimp simp: ut_revocable'_def)

    apply (frule n_cap)
    apply (frule revokable)
    by (auto simp: weak_derived'_def dest2_node_def
            split: if_split_asm)
qed

lemma scap_class[simp]:
  "capClass scap = capClass src_cap"
  using src_derived
  apply (clarsimp simp: weak_derived'_def)
  apply (rule master_eqI, rule capClass_Master)
  apply simp
  done

lemma dcap_class[simp]:
  "capClass dcap = capClass dest_cap"
  using dest_derived
  apply (clarsimp simp: weak_derived'_def)
  apply (rule master_eqI, rule capClass_Master)
  apply simp
  done

lemma class_links_n: "class_links n"
proof -
  from valid have "class_links m"
    by (simp add: valid_mdb_ctes_def)
  thus ?thesis
    apply (clarsimp simp: class_links_def)
    apply (case_tac cte, case_tac cte', clarsimp)
    apply (drule n_cap)+
    apply (simp add: imp_conjL[symmetric])
    apply (subst(asm) conj_commute)
    apply (simp add: imp_conjL)
    apply (simp add: imp_conjL[symmetric])
    apply (subst(asm) conj_commute)
    apply (simp add: imp_conjL next_m_n2)
    apply (elim allE, drule(1) mp)
    apply (auto simp: s_d_swap_def src dest
               split: if_split_asm)
    done
qed

lemma irq_control_n: "irq_control n"
  using src dest dest_derived src_derived
  apply (clarsimp simp: irq_control_def)
  apply (frule revokable)
  apply (drule n_cap)
  apply (clarsimp split: if_split_asm)
    apply (clarsimp simp: weak_derived'_def)
    apply (frule irq_revocable, rule irq_control)
    apply clarsimp
    apply (drule n_cap)
    apply (clarsimp split: if_split_asm)
     apply (drule (1) irq_controlD, rule irq_control)
     apply simp
    apply (drule (1) irq_controlD, rule irq_control)
    apply simp
   apply (clarsimp simp: weak_derived'_def)
   apply (frule irq_revocable, rule irq_control)
   apply clarsimp
   apply (drule n_cap)
   apply (clarsimp split: if_split_asm)
    apply (drule (1) irq_controlD, rule irq_control)
    apply simp
   apply (drule (1) irq_controlD, rule irq_control)
   apply simp
  apply (clarsimp simp: weak_derived'_def)
  apply (frule irq_revocable, rule irq_control)
  apply clarsimp
  apply (drule n_cap)
  apply (clarsimp split: if_split_asm)
    apply (drule (1) irq_controlD, rule irq_control)
    apply simp
   apply (drule (1) irq_controlD, rule irq_control)
   apply clarsimp
  apply (drule (1) irq_controlD, rule irq_control)
  apply clarsimp
  done

lemma distinct_zombies_m:
  "distinct_zombies m"
  using valid by auto

lemma distinct_zombies_n:
  "distinct_zombies n"
  using distinct_zombies_m
  apply (simp add: n_def distinct_zombies_nonCTE_modify_map)
  apply (simp add: n'_def distinct_zombies_nonCTE_modify_map)
  apply (simp add: modify_map_apply src dest)
  apply (erule distinct_zombies_switchE, rule src, rule dest)
   apply (cut_tac weak_der_src)
   apply (clarsimp simp: weak_der'_def weak_derived'_def)
  apply (cut_tac weak_der_dest)
  apply (clarsimp simp: weak_der'_def weak_derived'_def)
  done

lemma reply_masters_rvk_fb_m:
  "reply_masters_rvk_fb m"
  using valid by auto

lemma reply_masters_rvk_fb_n:
  "reply_masters_rvk_fb n"
  using reply_masters_rvk_fb_m
        weak_der'.isReplyMaster_eq[OF weak_der_src]
        weak_der'.isReplyMaster_eq[OF weak_der_dest]
  apply (simp add: reply_masters_rvk_fb_def)
  apply (frule bspec, rule ranI, rule m_p)
  apply (frule bspec, rule ranI, rule mdb_ptr_src.m_p)
  apply (clarsimp simp: ball_ran_eq)
  apply (case_tac cte, clarsimp)
  apply (frule n_cap, frule revokable, frule badge_n)
  apply (simp split: if_split_asm)
  apply clarsimp
  apply (elim allE, drule(1) mp)
  apply simp
  done

lemma cteSwap_valid_mdb_helper:
  assumes untyped_eq: "isUntypedCap src_cap \<Longrightarrow> scap = src_cap"
                      "isUntypedCap dest_cap \<Longrightarrow> dcap = dest_cap"
  shows "valid_mdb_ctes n"
  using cteSwap_chain cteSwap_dlist_helper cteSwap_valid_badges
        cteSwap_chunked caps_contained untyped_mdb_n untyped_inc_n
        nullcaps_n ut_rev_n class_links_n irq_control_n
        distinct_zombies_n reply_masters_rvk_fb_n
  by (auto simp:untyped_eq)

end

lemma cteSwap_ifunsafe'[wp]:
  "\<lbrace>if_unsafe_then_cap' and ex_cte_cap_to' c1 and ex_cte_cap_to' c2
        and cte_wp_at' (\<lambda>cte. cte_refs' (cteCap cte) = cte_refs' c) c1
        and cte_wp_at' (\<lambda>cte. cte_refs' (cteCap cte) = cte_refs' c') c2\<rbrace>
     cteSwap c c1 c' c2
  \<lbrace>\<lambda>rv. if_unsafe_then_cap'\<rbrace>"
  apply (simp add: ifunsafe'_def3 cteSwap_def)
  apply (wp | simp add: o_def | rule getCTE_wp)+
  apply (clarsimp simp: cte_wp_at_ctes_of cteCaps_of_def)
  apply (subgoal_tac "ex_cte_cap_to' cref s")
   apply (clarsimp simp: ex_cte_cap_to'_def cte_wp_at_ctes_of)
   apply (rule_tac x="(id (c1 := c2, c2 := c1)) crefc" in exI)
   apply (clarsimp simp: modify_map_def)
   apply fastforce
  apply (clarsimp dest!: modify_map_K_D
                 split: if_split_asm)
  apply (drule_tac x=cref in spec)
  apply (clarsimp simp: ex_cte_cap_to'_def cte_wp_at_ctes_of)
  apply fastforce
  done

lemma cteSwap_iflive'[wp]:
  "\<lbrace>if_live_then_nonz_cap'
        and cte_wp_at' (\<lambda>cte. zobj_refs' (cteCap cte) = zobj_refs' c) c1
        and cte_wp_at' (\<lambda>cte. zobj_refs' (cteCap cte) = zobj_refs' c') c2\<rbrace>
     cteSwap c c1 c' c2
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  apply (simp add: cteSwap_def)
  apply (wp | simp)+
   apply (rule hoare_post_imp,
          simp only: if_live_then_nonz_cap'_def imp_conv_disj
                     ex_nonz_cap_to'_def)
   apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift
             hoare_vcg_ex_lift updateCap_cte_wp_at_cases hoare_weak_lift_imp)+
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (drule(1) if_live_then_nonz_capE')
  apply (clarsimp simp: ex_nonz_cap_to'_def cte_wp_at_ctes_of)
  apply (rule_tac x="(id (c1 := c2, c2 := c1)) cref" in exI)
  apply auto
  done

lemmas tcbSlots =
  tcbCTableSlot_def tcbVTableSlot_def
  tcbReplySlot_def tcbCallerSlot_def tcbIPCBufferSlot_def

lemma updateMDB_pspace_canonical'[wp]:
  "updateMDB next prev \<lbrace>pspace_canonical'\<rbrace>"
  by (wpsimp simp: ARM_HYP.pspace_canonical'_top)

lemma updateMDB_pspace_in_kernel_mappings'[wp]:
  "updateMDB next prev \<lbrace>pspace_in_kernel_mappings'\<rbrace>"
  by (wpsimp simp: ARM_HYP.pspace_in_kernel_mappings'_def)

lemma updateCap_pspace_canonical'[wp]:
  "updateCap next prev \<lbrace>pspace_canonical'\<rbrace>"
  by (wpsimp simp: ARM_HYP.pspace_canonical'_top)

lemma updateCap_pspace_in_kernel_mappings'[wp]:
  "updateCap next prev \<lbrace>pspace_in_kernel_mappings'\<rbrace>"
  by (wpsimp simp: ARM_HYP.pspace_in_kernel_mappings'_def)

lemma cteSwap_valid_pspace'[wp]:
  "\<lbrace>valid_pspace' and
    cte_wp_at' (weak_derived' c o cteCap) c1 and
    cte_wp_at' (\<lambda>cc. isUntypedCap (cteCap cc) \<longrightarrow> (cteCap cc) = c) c1 and
    cte_wp_at' (weak_derived' c' o cteCap) c2 and
    cte_wp_at' (\<lambda>cc. isUntypedCap (cteCap cc) \<longrightarrow> (cteCap cc) = c') c2 and
    valid_cap' c and valid_cap' c' and
    K (c1 \<noteq> c2)\<rbrace>
  cteSwap c c1 c' c2
  \<lbrace>\<lambda>rv. valid_pspace'\<rbrace>"
  unfolding cteSwap_def
  apply (simp add: pred_conj_def valid_pspace'_def valid_mdb'_def)
  apply (rule hoare_pre)
   apply wp
          apply (wp getCTE_inv getCTE_wp)
         apply (strengthen imp_consequent, strengthen ctes_of_strng)
         apply ((wp sch_act_wf_lift valid_queues_lift
                    cur_tcb_lift updateCap_no_0  updateCap_ctes_of_wp
                    hoare_vcg_ex_lift updateMDB_cte_wp_at_other getCTE_wp
                  | simp add: cte_wp_at_ctes_ofI o_def
                  | rule hoare_drop_imps)+)[6]
  apply (clarsimp simp: valid_pspace_no_0[unfolded valid_pspace'_def valid_mdb'_def]
                        cte_wp_at_ctes_of)
  apply (subgoal_tac "c2 \<in> dom (modify_map
               (modify_map
                 (modify_map
                   (modify_map (ctes_of s) c1 (cteCap_update (%_. c'))) c2
                   (cteCap_update (%_. c)))
                 (mdbPrev (cteMDBNode cte))
                 (cteMDBNode_update (mdbNext_update (%_. c2))))
               (mdbNext (cteMDBNode cte))
               (cteMDBNode_update (mdbPrev_update (%_. c2))))")
   apply (erule domE)
   apply (intro exI)
   apply (rule conjI)
    apply (clarsimp simp: modify_map_def cte_wp_at_ctes_of)
    apply (rule refl)
   apply (case_tac cte)
   apply (case_tac cteb)
   apply (rule_tac dest_node = "cteMDBNode cteb" in
     mdb_swap.cteSwap_valid_mdb_helper [simplified const_def])
   apply (rule mdb_swap.intro)
     apply (rule mdb_ptr.intro)
      apply (erule vmdb.intro)
     apply (rule mdb_ptr_axioms.intro)
     apply simp
    apply (rule mdb_ptr.intro)
     apply (erule vmdb.intro)
    apply (rule mdb_ptr_axioms.intro)
    apply (simp add: cte_wp_at_ctes_of)
   apply (erule mdb_swap_axioms.intro)
     apply clarsimp
     apply (erule weak_derived_sym')
    apply clarsimp
    apply (erule weak_derived_sym')
   apply (simp)
  apply clarsimp+
  done

context begin interpretation Arch . (*FIXME: arch-split*)

crunch cteSwap
  for tcb_at[wp]: "tcb_at' t"
crunch cteSwap
  for sch[wp]: "\<lambda>s. P (ksSchedulerAction s)"
crunch cteSwap
  for inQ[wp]: "obj_at' (inQ d p) tcb"
crunch cteSwap
  for ksQ[wp]: "\<lambda>s. P (ksReadyQueues s)"
crunch cteSwap
  for sym[wp]: "\<lambda>s. sym_refs (state_refs_of' s)"
crunch cteSwap
  for sym_hyp[wp]: "\<lambda>s. sym_refs (state_hyp_refs_of' s)"
crunch cteSwap
  for cur[wp]: "\<lambda>s. P (ksCurThread s)"
crunch cteSwap
  for ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
crunch cteSwap
  for ksDomSchedule[wp]: "\<lambda>s. P (ksDomSchedule s)"
crunch cteSwap
  for it[wp]: "\<lambda>s. P (ksIdleThread s)"
crunch cteSwap
  for tcbDomain_obj_at'[wp]: "obj_at' (\<lambda>tcb. x = tcbDomain tcb) t"

lemma cteSwap_idle'[wp]:
  "\<lbrace>valid_idle'\<rbrace>
     cteSwap c c1 c' c2
   \<lbrace>\<lambda>rv s. valid_idle' s\<rbrace>"
  apply (simp add: cteSwap_def)
  apply (wp updateCap_idle' | simp)+
  done

lemma weak_derived_zobj:
  "weak_derived' c c' \<Longrightarrow> zobj_refs' c' = zobj_refs' c"
  apply (clarsimp simp: weak_derived'_def)
  apply (rule master_eqI, rule zobj_refs_Master)
  apply simp
  done

lemma weak_derived_cte_refs:
  "weak_derived' c c' \<Longrightarrow> cte_refs' c' = cte_refs' c"
  apply (clarsimp simp: weak_derived'_def)
  apply (rule master_eqI, rule cte_refs_Master)
  apply simp
  done

lemma weak_derived_capRange_capBits:
  "weak_derived' c c' \<Longrightarrow> capRange c' = capRange c \<and> capBits c' = capBits c"
  apply (clarsimp simp: weak_derived'_def)
  apply (metis capRange_Master capBits_Master)
  done

lemma cteSwap_refs[wp]:
  "\<lbrace>valid_global_refs' and cte_wp_at' (weak_derived' c \<circ> cteCap) c1
           and cte_wp_at' (weak_derived' c' \<circ> cteCap) c2\<rbrace>
     cteSwap c c1 c' c2
   \<lbrace>\<lambda>rv. valid_global_refs'\<rbrace>"
  apply (simp add: cteSwap_def)
  apply wp
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (drule(1) valid_global_refsD_with_objSize)+
  apply (drule weak_derived_capRange_capBits)+
  apply (clarsimp simp: global_refs'_def Int_Un_distrib2)
  done

crunch cteSwap
  for ksInterrupt[wp]: "\<lambda>s. P (ksInterruptState s)"

crunch cteSwap
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"

lemma cteSwap_valid_irq_handlers[wp]:
  "\<lbrace>valid_irq_handlers' and cte_wp_at' (weak_derived' c \<circ> cteCap) c1
           and cte_wp_at' (weak_derived' c' \<circ> cteCap) c2\<rbrace>
     cteSwap c c1 c' c2
   \<lbrace>\<lambda>rv. valid_irq_handlers'\<rbrace>"
  apply (simp add: valid_irq_handlers'_def irq_issued'_def)
  apply (rule hoare_pre)
   apply (rule hoare_use_eq [where f=ksInterruptState, OF cteSwap_ksInterrupt])
   apply (simp add: cteSwap_def)
   apply wp
  apply (clarsimp simp: cte_wp_at_ctes_of cteCaps_of_def ran_def)
  apply (clarsimp simp add: modify_map_def split: if_split_asm)
     apply (auto simp add: weak_derived'_def isCap_simps)
  done

lemma weak_derived_untypedZeroRange:
  "\<lbrakk> weak_derived' c c'; isUntypedCap c' \<longrightarrow> c' = c \<rbrakk>
    \<Longrightarrow> untypedZeroRange c = untypedZeroRange c'"
  apply (clarsimp simp: untypedZeroRange_def isCap_simps)
  apply (clarsimp simp: weak_derived'_def)
  done

lemma cteSwap_urz[wp]:
  "\<lbrace>untyped_ranges_zero' and valid_pspace'
    and cte_wp_at' (\<lambda>cc. isUntypedCap (cteCap cc) \<longrightarrow> (cteCap cc) = c) c1
    and cte_wp_at' (weak_derived' c' o cteCap) c2
    and cte_wp_at' (\<lambda>cc. isUntypedCap (cteCap cc) \<longrightarrow> (cteCap cc) = c') c2
    and cte_wp_at' (weak_derived' c \<circ> cteCap) c1
    and K (c1 \<noteq> c2)\<rbrace>
  cteSwap c c1 c' c2
  \<lbrace>\<lambda>rv. untyped_ranges_zero'\<rbrace>"
  apply (simp add: cteSwap_def)
  apply (rule hoare_pre)
   apply (rule untyped_ranges_zero_lift)
    apply wp+
  apply clarsimp
  apply (erule untyped_ranges_zero_delta[where xs="[c1, c2]"])
     apply (simp add: modify_map_def)
    apply clarsimp
   apply clarsimp
  apply (clarsimp simp: ran_restrict_map_insert cte_wp_at_ctes_of
                        cteCaps_of_def modify_map_def)
  apply (drule(1) weak_derived_untypedZeroRange)+
  apply auto
  done

crunch cteSwap
  for valid_arch_state'[wp]: "valid_arch_state'"

crunch cteSwap
  for irq_states'[wp]: "valid_irq_states'"

crunch cteSwap
  for pde_mappings'[wp]: "valid_pde_mappings'"

crunch cteSwap
  for ksqsL1[wp]: "\<lambda>s. P (ksReadyQueuesL1Bitmap s)"

crunch cteSwap
  for ksqsL2[wp]: "\<lambda>s. P (ksReadyQueuesL2Bitmap s)"

crunch cteSwap
  for st_tcb_at'[wp]: "st_tcb_at' P t"

crunch cteSwap
  for vms'[wp]: "valid_machine_state'"

crunch cteSwap
  for pspace_domain_valid[wp]: "pspace_domain_valid"

crunch cteSwap
  for ct_not_inQ[wp]: "ct_not_inQ"

crunch cteSwap
  for ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"

crunch cteSwap
  for sym_heap_sched_pointers[wp]: sym_heap_sched_pointers
  and valid_sched_pointers[wp]: valid_sched_pointers
  and valid_bitmaps[wp]: valid_bitmaps
  (rule: valid_bitmaps_lift)

lemma cteSwap_invs'[wp]:
  "\<lbrace>invs' and valid_cap' c and valid_cap' c' and
    ex_cte_cap_to' c1 and ex_cte_cap_to' c2 and
    cte_wp_at' (\<lambda>cc. isUntypedCap (cteCap cc) \<longrightarrow> (cteCap cc) = c) c1 and
    cte_wp_at' (weak_derived' c' o cteCap) c2 and
    cte_wp_at' (\<lambda>cc. isUntypedCap (cteCap cc) \<longrightarrow> (cteCap cc) = c') c2 and
    cte_wp_at' (weak_derived' c \<circ> cteCap) c1 and
    K (c1 \<noteq> c2)\<rbrace>
  cteSwap c c1 c' c2
  \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def pred_conj_def)
  apply (rule hoare_pre)
   apply (wp hoare_vcg_conj_lift sch_act_wf_lift
             valid_queues_lift cur_tcb_lift
             valid_irq_node_lift irqs_masked_lift tcb_in_cur_domain'_lift
             ct_idle_or_in_cur_domain'_lift2)
  apply (clarsimp simp: cte_wp_at_ctes_of weak_derived_zobj weak_derived_cte_refs
                        weak_derived_capRange_capBits)
  done

lemma capSwap_invs'[wp]:
  "\<lbrace>invs' and ex_cte_cap_to' c1 and ex_cte_cap_to' c2\<rbrace>
  capSwapForDelete c1 c2
  \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: capSwapForDelete_def)
  apply (wp getCTE_wp')
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (auto dest!: ctes_of_valid')
  done

lemma Zombie_isZombie[simp]:
  "isZombie (Zombie x y z)"
  by (simp add: isZombie_def)

lemmas sameObject_sameRegion = sameObjectAs_sameRegionAs

lemma mdb_next_cap_upd:
  "m sl = Some (CTE cap' mdbnode) \<Longrightarrow>
  m (sl \<mapsto> CTE cap mdbnode) \<turnstile> p \<leadsto> p' = m \<turnstile> p \<leadsto> p'"
  by (simp add: mdb_next_unfold)

lemma trancl_cap_upd:
  "m sl = Some (CTE cap' mdbnode) \<Longrightarrow>
  m (sl \<mapsto> CTE cap mdbnode) \<turnstile> p \<leadsto>\<^sup>+ p' = m \<turnstile> p \<leadsto>\<^sup>+ p'"
  apply (rule iffI)
   apply (erule trancl_induct)
    apply (fastforce simp: mdb_next_cap_upd simp del: fun_upd_apply)
   apply (fastforce simp: mdb_next_cap_upd simp del: fun_upd_apply elim: trancl_trans)
  apply (erule trancl_induct)
   apply (fastforce simp: mdb_next_cap_upd simp del: fun_upd_apply)
  apply (fastforce simp: mdb_next_cap_upd simp del: fun_upd_apply elim: trancl_trans)
  done

lemma rtrancl_cap_upd:
  "m sl = Some (CTE cap' mdbnode) \<Longrightarrow>
  m (sl \<mapsto> CTE cap mdbnode) \<turnstile> p \<leadsto>\<^sup>* p' = m \<turnstile> p \<leadsto>\<^sup>* p'"
  by (simp add: trancl_cap_upd rtrancl_eq_or_trancl)

lemma no_loops_tranclD:
  "\<lbrakk> m \<turnstile> p \<leadsto>\<^sup>+ p'; no_loops m \<rbrakk> \<Longrightarrow> \<not> m \<turnstile> p' \<leadsto>\<^sup>+ p"
  apply clarsimp
  apply (drule (1) trancl_trans)
  apply (simp add: no_loops_def)
  done

lemmas mdb_chain_0_tranclD = no_loops_tranclD [OF _ mdb_chain_0_no_loops]

lemma caps_contained_subrange:
  "\<lbrakk> caps_contained' m; m sl = Some (CTE cap n'); capRange cap' \<subseteq> capRange cap; \<not>isUntypedCap cap; \<not> isUntypedCap cap' \<rbrakk>
  \<Longrightarrow> caps_contained' (modify_map m sl (cteCap_update (%_. cap')))"
  apply (simp add: caps_contained'_def modify_map_apply notUntypedRange)
  apply clarsimp
  apply (erule_tac x=p in allE)
  apply (erule_tac x=sl in allE)
  apply simp
  apply blast
  done
lemma ex_cte_cap_to'_cteCap:
  "ex_cte_cap_to' p = (\<lambda>s. \<exists>p' c. cteCaps_of s p' = Some c \<and> p \<in> cte_refs' c (irq_node' s))"
  apply (simp add: ex_cte_cap_to'_def cte_wp_at_ctes_of cteCaps_of_def)
  apply (fastforce intro!: ext)
  done

lemma updateCap_ifunsafe':
  "\<lbrace>\<lambda>s. if_unsafe_then_cap' s \<and> valid_objs' s
       \<and> cte_wp_at' (\<lambda>cte. \<forall>r\<in>cte_refs' (cteCap cte) (irq_node' s) - cte_refs' cap (irq_node' s).
                        cte_wp_at' (\<lambda>cte. cteCap cte = NullCap) r s
                             \<and> (r = sl \<longrightarrow> cap = NullCap)) sl s
       \<and> (cap \<noteq> NullCap \<longrightarrow> ex_cte_cap_to' sl s)\<rbrace>
      updateCap sl cap
   \<lbrace>\<lambda>rv. if_unsafe_then_cap'\<rbrace>"
  apply (simp add: ifunsafe'_def3 o_def)
  apply wp
  apply clarsimp
  apply (subgoal_tac "ex_cte_cap_to' cref s")
   apply (clarsimp simp: ex_cte_cap_to'_def cte_wp_at_ctes_of)
   apply (rule_tac x=crefa in exI)
   apply (clarsimp simp: cteCaps_of_def modify_map_def)
   apply (rule ccontr, drule bspec, clarsimp, erule(1) conjI)
   apply (clarsimp split: if_split_asm)
  apply (drule_tac x=cref in spec)
  apply (clarsimp dest!: modify_map_K_D
                   simp: ex_cte_cap_to'_cteCap
                  split: if_split_asm)
  done

lemma valid_vmdb [elim!]:
  "valid_mdb' s \<Longrightarrow> vmdb (ctes_of s)"
  by unfold_locales (simp add: valid_mdb'_def)

lemma class_links_update:
  "\<lbrakk> class_links m; \<exists>cte. m x = Some cte
      \<and> mdbNext (cteMDBNode cte) = mdbNext (cteMDBNode cte')
      \<and> capClass (cteCap cte) = capClass (cteCap cte') \<rbrakk>
        \<Longrightarrow> class_links (m(x \<mapsto> cte'))"
  apply clarsimp
  apply (unfold class_links_def)
  apply (erule allEI, erule allEI)
  apply (clarsimp simp: mdb_next_unfold split del: if_split split: if_split_asm)
  done

lemma sameRegionAs_Zombie[simp]:
  "\<not> sameRegionAs (Zombie p zb n) cap"
  by (simp add: sameRegionAs_def3 isCap_simps)

lemma descendants_of_subset_untyped:
  assumes adj: "\<And>x. ((m x = None) = (m' x = None))
                   \<and> (\<forall>cte cte'. m x = Some cte \<and> m' x = Some cte'
                       \<longrightarrow> (isUntypedCap (cteCap cte) = isUntypedCap (cteCap cte'))
                         \<and> (capRange (cteCap cte) = capRange (cteCap cte'))
                         \<and> (isUntypedCap (cteCap cte) \<longrightarrow> cteCap cte = cteCap cte'))"
  and    desc: "\<And>x. descendants_of' x m \<subseteq> descendants_of' x m'"
  shows        "(untyped_inc' m \<longrightarrow> untyped_inc' m')
                     \<and> (untyped_mdb' m \<longrightarrow> untyped_mdb' m')"
proof
  have P: "\<And>x cte. \<lbrakk> m' x = Some cte; isUntypedCap (cteCap cte) \<rbrakk>
                       \<Longrightarrow> \<exists>node. m x = Some (CTE (cteCap cte) node) \<and> m' x = Some cte"
    apply (cut_tac x=x in adj)
    apply clarsimp
    apply (case_tac y, simp)
    done

  show "untyped_inc' m \<longrightarrow> untyped_inc' m'"
    unfolding untyped_inc'_def
    apply (rule impI, erule allEI, erule allEI)
    apply clarsimp
    apply (drule P | simp)+
    apply clarsimp
    apply (cut_tac x=p in desc)
    apply (cut_tac x=p' in desc)
    apply blast
    done

  have Q: "\<And>x cte. m' x = Some cte
             \<Longrightarrow> \<exists>cap node. m x = Some (CTE cap node)
                    \<and> isUntypedCap cap = isUntypedCap (cteCap cte)
                    \<and> capRange cap = capRange (cteCap cte)"
    apply (cut_tac x=x in adj)
    apply clarsimp
    apply (case_tac y, simp)
    done

  show "untyped_mdb' m \<longrightarrow> untyped_mdb' m'"
    unfolding untyped_mdb'_def
    apply (rule impI, erule allEI, erule allEI)
    apply clarsimp
    apply (drule_tac x=p in P, simp)
    apply (drule_tac x=p' in Q, simp)
    apply clarsimp
    apply (cut_tac x=p in desc)
    apply blast
    done

qed

lemma invalid_Thread_CNode:
  "\<lbrakk> isThreadCap cap; isCNodeCap cap'; s \<turnstile>' cap; s \<turnstile>' cap' \<rbrakk>
        \<Longrightarrow> capUntypedPtr cap \<noteq> capUntypedPtr cap'"
  apply (clarsimp simp: valid_cap'_def isCap_simps)
  apply (drule_tac x=0 in spec)
  apply (clarsimp simp: obj_at'_def projectKOs)
  done

(* FIXME MOVE *)
lemma all_Not_False[simp]:
  "All Not = False"
  by blast

lemma Final_notUntyped_capRange_disjoint:
  "\<lbrakk> isFinal cap sl (cteCaps_of s); cteCaps_of s sl' = Some cap';
      sl \<noteq> sl'; capUntypedPtr cap = capUntypedPtr cap'; capBits cap = capBits cap';
      isThreadCap cap \<or> isCNodeCap cap; s \<turnstile>' cap;
      \<not> isUntypedCap cap'; \<not> isArchPageCap cap'; \<not> isZombie cap';
      capClass cap' = PhysicalClass; valid_objs' s \<rbrakk>
          \<Longrightarrow> P"
  apply (clarsimp simp add: isFinal_def)
  apply (drule_tac x=sl' in spec)
  apply (clarsimp simp: cteCaps_of_def)
  apply (drule(1) ctes_of_valid')
  apply (elim disjE isCapDs[elim_format])
   apply (clarsimp simp: valid_cap'_def valid_arch_cap'_def
                         obj_at'_def projectKOs objBits_simps'
                         typ_at'_def ko_wp_at'_def
                         page_table_at'_def page_directory_at'_def
                         sameObjectAs_def3 isCap_simps
                  split: capability.split_asm zombie_type.split_asm
                         arch_capability.split_asm option.split_asm
                  dest!: spec[where x=0])+
  done

lemma capBits_capUntyped_capRange:
  "\<lbrakk> capBits cap = capBits cap';
     capUntypedPtr cap = capUntypedPtr cap';
     capClass cap = capClass cap' \<rbrakk>
          \<Longrightarrow> capRange cap = capRange cap'"
  by (simp add: capRange_def)

lemma ztc_phys:
  "\<lbrakk> isCNodeCap cap \<or> isThreadCap cap \<or> isZombie cap \<rbrakk>
       \<Longrightarrow> capClass cap = PhysicalClass"
  by (auto simp: isCap_simps)

lemma ztc_sameRegion:
  "\<lbrakk> isCNodeCap cap \<or> isThreadCap cap \<or> isZombie cap \<rbrakk>
       \<Longrightarrow> sameRegionAs cap cap' = sameObjectAs cap cap'"
  apply (subgoal_tac "\<not> isUntypedCap cap \<and> \<not> isArchPageCap cap
                          \<and> \<not> isIRQControlCap cap")
   apply (simp add: sameRegionAs_def3 sameObjectAs_def3)
   apply (auto simp: isCap_simps)
  done

lemma distinct_zombies_seperate_if_zombiedE:
  "\<lbrakk> distinct_zombies m; m x = Some cte;
        isUntypedCap (cteCap cte) \<longrightarrow> isUntypedCap (cteCap cte');
        isArchPageCap (cteCap cte) \<longrightarrow> isArchPageCap (cteCap cte');
        capClass (cteCap cte') = capClass (cteCap cte);
        capBits (cteCap cte') = capBits (cteCap cte);
        capUntypedPtr (cteCap cte') = capUntypedPtr (cteCap cte);
        \<And>y cte''. \<lbrakk> m y = Some cte''; x \<noteq> y;
                    isZombie (cteCap cte'); \<not> isZombie (cteCap cte);
                    \<not> isZombie (cteCap cte'');
                    \<not> isUntypedCap (cteCap cte''); \<not> isArchPageCap (cteCap cte'');
                    capClass (cteCap cte'') = PhysicalClass;
                    capUntypedPtr (cteCap cte'') = capUntypedPtr (cteCap cte);
                    capBits (cteCap cte'') = capBits (cteCap cte)
                        \<rbrakk> \<Longrightarrow> False    \<rbrakk>
          \<Longrightarrow> distinct_zombies (m (x \<mapsto> cte'))"
  apply (cases "isZombie (cteCap cte') \<and> \<not> isZombie (cteCap cte)")
   apply (subgoal_tac "\<forall>y cte''. m y = Some cte'' \<longrightarrow> y \<noteq> x
                            \<longrightarrow> capUntypedPtr (cteCap cte'') = capUntypedPtr (cteCap cte)
                            \<longrightarrow> capBits (cteCap cte'') = capBits (cteCap cte)
                            \<longrightarrow> \<not> isZombie (cteCap cte'')")
    apply (erule distinct_zombies_seperateE)
    apply (drule_tac x=y in spec, clarsimp)
    apply auto[1]
   apply (clarsimp simp add: distinct_zombies_def distinct_zombie_caps_def)
   apply (drule_tac x=y in spec, drule_tac x=x in spec)
   apply (frule isZombie_capClass[where cap="cteCap cte'"])
   apply clarsimp
   apply (auto simp: isCap_simps)[1]
  apply clarsimp
  apply (erule(7) distinct_zombies_unzombieE)
  done

lemma mdb_chunked_update_final:
  assumes chunked: "mdb_chunked m"
         and slot: "m slot = Some (CTE cap node)"
         and Fin1: "\<And>x cte. m x = Some cte \<Longrightarrow> x \<noteq> slot
                        \<Longrightarrow> \<not> sameRegionAs cap (cteCap cte)"
         and Fin2: "\<And>x cte. m x = Some cte \<Longrightarrow> x \<noteq> slot
                        \<Longrightarrow> \<not> sameRegionAs cap' (cteCap cte)"
         and Fin3: "\<And>x cte. m x = Some cte \<Longrightarrow> x \<noteq> slot
                        \<Longrightarrow> sameRegionAs (cteCap cte) cap
                        \<Longrightarrow> isUntypedCap (cteCap cte)"
         and Fin4: "\<And>x cte. m x = Some cte \<Longrightarrow> x \<noteq> slot
                        \<Longrightarrow> sameRegionAs (cteCap cte) cap'
                        \<Longrightarrow> isUntypedCap (cteCap cte)"
         and capR: "capRange cap = capRange cap'"
  shows            "mdb_chunked (m (slot \<mapsto> CTE cap' node))"
           (is "mdb_chunked ?m'")
proof -
  note trancl[simp] = trancl_cap_upd [where m=m, OF slot]
  note rtrancl[simp] = rtrancl_cap_upd [where m=m, OF slot]

  have sameRegionAs:
    "\<And>x cte. \<lbrakk> m x = Some cte; x \<noteq> slot; sameRegionAs (cteCap cte) cap' \<rbrakk>
              \<Longrightarrow> sameRegionAs (cteCap cte) cap"
    apply (frule(2) Fin4)
    apply (clarsimp simp: sameRegionAs_def3 capR)
    apply (clarsimp simp: isCap_simps)
    done

  have is_chunk:
    "\<And>x cap n p p'. \<lbrakk> is_chunk m cap p p'; m x = Some (CTE cap n); x \<noteq> slot \<rbrakk> \<Longrightarrow>
                        is_chunk ?m' cap p p'"
    apply (simp add: is_chunk_def split del: if_split)
    apply (erule allEI)
    apply (clarsimp simp: slot)
    apply (frule(1) Fin3, simp)
    apply (clarsimp simp: sameRegionAs_def3 capR)
    apply (clarsimp simp: isCap_simps)
    done

  have not_chunk: "\<And>p. \<lbrakk> m \<turnstile> slot \<leadsto>\<^sup>+ p; p \<noteq> slot \<rbrakk> \<Longrightarrow> \<not> is_chunk m cap slot p"
    apply (simp add: is_chunk_def)
    apply (rule_tac x=p in exI)
    apply clarsimp
    apply (frule(1) Fin1)
    apply simp
    done

  show ?thesis using chunked
    apply (simp add: mdb_chunked_def split del: if_split)
    apply (erule allEI, erule allEI)
    apply (clarsimp split del: if_split)
    apply (clarsimp simp: slot split: if_split_asm)
      apply (frule(1) Fin2[OF _ not_sym], simp)
     apply (frule(1) sameRegionAs, clarsimp+)
     apply (simp add: not_chunk is_chunk)
    apply (simp add: is_chunk)
    done
qed

lemma distinct_zombiesD:
  "\<lbrakk> m x = Some cte; distinct_zombies m; isZombie (cteCap cte);
       y \<noteq> x; m y = Some cte'; capBits (cteCap cte') = capBits (cteCap cte);
       capUntypedPtr (cteCap cte') = capUntypedPtr (cteCap cte);
       \<not> isUntypedCap (cteCap cte'); \<not> isArchPageCap (cteCap cte');
       capClass (cteCap cte') = PhysicalClass \<rbrakk>
       \<Longrightarrow> False"
  apply (simp add: distinct_zombies_def distinct_zombie_caps_def)
  apply (drule_tac x=x in spec, drule_tac x=y in spec)
  apply clarsimp
  apply auto
  done

lemma ztc_replace_update_final:
  assumes chunk: "mdb_chunked m"
      and  slot: "m x = Some (CTE cap node)"
      and  ztc1: "isCNodeCap cap \<or> isThreadCap cap \<or> isZombie cap"
      and  ztc2: "isCNodeCap cap' \<or> isThreadCap cap' \<or> isZombie cap'"
      and   unt: "capUntypedPtr cap = capUntypedPtr cap'"
      and  bits: "capBits cap = capBits cap'"
      and distz: "distinct_zombies m"
      and   Fin: "isFinal cap x (option_map cteCap \<circ> m)"
      and valid: "s \<turnstile>' cap" "s \<turnstile>' cap'"
      shows      "mdb_chunked (m (x \<mapsto> CTE cap' node))"
proof (rule mdb_chunked_update_final [OF chunk, OF slot])
  have cases: "capMasterCap cap = capMasterCap cap'
                  \<or> isZombie cap \<or> isZombie cap'"
    using bits unt ztc1 ztc2
          invalid_Thread_CNode [OF _ _ valid]
          invalid_Thread_CNode [OF _ _ valid(2) valid(1)]
    by (auto simp: isCap_simps)

  have Fin': "\<And>y cte. \<lbrakk> m y = Some cte; y \<noteq> x \<rbrakk> \<Longrightarrow> \<not> sameObjectAs cap (cteCap cte)"
    using Fin
    apply (clarsimp simp: isFinal_def)
    apply (drule_tac x=y in spec)
    apply (clarsimp simp: sameObjectAs_def3 simp del: isArchFrameCap_capMasterCap)
    done

  show Fin1: "\<And>y cte. \<lbrakk> m y = Some cte; y \<noteq> x \<rbrakk> \<Longrightarrow> \<not> sameRegionAs cap (cteCap cte)"
    by (clarsimp simp: ztc_sameRegion [OF ztc1] Fin')

  show capR: "capRange cap = capRange cap'"
    using unt bits ztc_phys[OF ztc1] ztc_phys[OF ztc2]
    by (simp add: capRange_def)

  have capR_neq: "capRange cap' \<noteq> {}"
    using capAligned_capUntypedPtr [OF valid_capAligned, OF valid(2)]
    by (clarsimp simp add: ztc_phys [OF ztc2])

  have zombie_case_helper:
    "\<And>y cte. \<lbrakk> m y = Some cte; y \<noteq> x; isZombie cap \<rbrakk>
                 \<Longrightarrow> \<not> sameObjectAs cap' (cteCap cte)"
    apply (clarsimp simp: ztc_sameRegion ztc1 ztc2
                   elim!: sameObjectAsE)
    apply (rule distinct_zombiesD [OF slot distz], simp_all)[1]
        apply (drule master_eqE, rule capBits_Master)
        apply (simp add: bits)
       apply (drule arg_cong[where f=capUntypedPtr])
       apply (simp add: capUntyped_Master unt)
      apply (drule arg_cong[where f=isUntypedCap])
      apply (simp add: gen_isCap_Master)
     apply (drule arg_cong[where f=isArchPageCap])
     apply (clarsimp simp add: gen_isCap_Master)
     apply (cut_tac ztc2, clarsimp simp: isCap_simps)
    apply (drule arg_cong[where f=capClass])
    apply (simp add: capClass_Master ztc_phys[OF ztc2])
    done

  show Fin2: "\<And>y cte. \<lbrakk> m y = Some cte; y \<noteq> x \<rbrakk> \<Longrightarrow> \<not> sameRegionAs cap' (cteCap cte)"
    using capR
    apply clarsimp
    apply (frule(1) Fin1)
    apply (rule disjE [OF cases])
     apply (clarsimp simp: ztc_sameRegion ztc1 ztc2 sameObjectAs_def3)
     apply (drule_tac F="\<lambda>cap. (isNullCap cap, isZombie cap, isIRQControlCap cap,
                                isUntypedCap cap, isArchFrameCap cap,
                                capRange cap)" in  master_eqE,
            simp add: gen_isCap_Master capRange_Master del: isNullCap)+
     apply (auto simp: gen_isCap_Master capRange_Master)[1]
    apply (erule disjE)
     apply (drule(2) zombie_case_helper)
     apply (simp add: ztc_sameRegion ztc1 ztc2)
    apply (clarsimp simp: ztc_sameRegion ztc1 ztc2
                   elim!: sameObjectAsE)
    done

  have untyped_helper:
    "\<And>cap cap'. \<lbrakk> isCNodeCap cap' \<or> isThreadCap cap' \<or> isZombie cap';
                  sameRegionAs cap cap' \<rbrakk>
                    \<Longrightarrow> isUntypedCap cap \<or> sameRegionAs cap' cap"
    apply (erule sameRegionAsE)
       apply (clarsimp simp: ztc_sameRegion sameObjectAs_def3)
       apply (drule_tac F="\<lambda>cap. (isNullCap cap, isZombie cap, isIRQControlCap cap,
                                  isUntypedCap cap, isArchFrameCap cap,
                                  capRange cap)" in  master_eqE,
              simp add: gen_isCap_Master capRange_Master del: isNullCap)+
       apply (auto simp: gen_isCap_Master capRange_Master isCap_simps)[1]
      apply simp
     apply (clarsimp simp: isCap_simps)+
    done

  show Fin3: "\<And>y cte. \<lbrakk> m y = Some cte; y \<noteq> x; sameRegionAs (cteCap cte) cap \<rbrakk>
                         \<Longrightarrow> isUntypedCap (cteCap cte)"
    apply (frule(1) Fin1)
    apply (drule untyped_helper[OF ztc1])
    apply simp
    done

  show Fin4: "\<And>y cte. \<lbrakk> m y = Some cte; y \<noteq> x; sameRegionAs (cteCap cte) cap' \<rbrakk>
                         \<Longrightarrow> isUntypedCap (cteCap cte)"
    apply (frule(1) Fin2)
    apply (drule untyped_helper[OF ztc2])
    apply simp
    done

qed

lemma updateCap_untyped_ranges_zero_simple:
  "\<lbrace>cte_wp_at' ((\<lambda>cp. untypedZeroRange cp = untypedZeroRange cap) o cteCap) sl and untyped_ranges_zero'\<rbrace>
    updateCap sl cap
  \<lbrace>\<lambda>_. untyped_ranges_zero'\<rbrace>"
  apply (rule hoare_pre, rule untyped_ranges_zero_lift, wp+)
  apply (clarsimp simp: modify_map_def cteCaps_of_def cte_wp_at_ctes_of)
  apply (simp add: untyped_ranges_zero_inv_def)
  apply (rule arg_cong[where f=ran])
  apply (simp add: fun_eq_iff map_comp_def)
  done

crunch updateCap
  for tcb_in_cur_domain'[wp]: "tcb_in_cur_domain' t"
  (wp: crunch_wps simp: crunch_simps rule: tcb_in_cur_domain'_lift)

crunch updateCap
  for valid_bitmaps[wp]: valid_bitmaps
  (rule: valid_bitmaps_lift)

lemma make_zombie_invs':
  "\<lbrace>\<lambda>s. invs' s \<and> s \<turnstile>' cap \<and>
    cte_wp_at' (\<lambda>cte. isFinal (cteCap cte) sl (cteCaps_of s)) sl s \<and>
    cte_wp_at' (\<lambda>cte. capClass (cteCap cte) = PhysicalClass \<and>
                      capUntypedPtr (cteCap cte) = capUntypedPtr cap \<and>
                      capBits (cteCap cte) = capBits cap \<and>
                      (\<forall>r\<in>cte_refs' (cteCap cte) (irq_node' s) - cte_refs' cap (irq_node' s).
                        cte_wp_at' (\<lambda>cte. cteCap cte = NullCap) r s) \<and>
                      (isZombie cap \<or> isThreadCap cap \<or> isCNodeCap cap) \<and>
                      final_matters' (cteCap cte) \<and>
                      (isThreadCap (cteCap cte) \<or> isCNodeCap (cteCap cte)
                         \<or> isZombie (cteCap cte)) \<and> \<not> isUntypedCap (cteCap cte) \<and>
                      (\<forall>p \<in> threadCapRefs (cteCap cte).
                            st_tcb_at' ((=) Inactive) p s
                             \<and> bound_tcb_at' ((=) None) p s
                             \<and> obj_at' (Not \<circ> tcbQueued) p s
                             \<and> ko_wp_at' (Not \<circ> hyp_live') p s
                             \<and> obj_at' (\<lambda>tcb. tcbSchedNext tcb = None
                                              \<and> tcbSchedPrev tcb = None) p s)) sl s\<rbrace>
    updateCap sl cap
  \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def valid_pspace'_def valid_mdb'_def
                   valid_irq_handlers'_def irq_issued'_def)
  apply (wp updateCap_ctes_of_wp sch_act_wf_lift valid_queues_lift cur_tcb_lift
            updateCap_iflive' updateCap_ifunsafe' updateCap_idle'
            valid_irq_node_lift ct_idle_or_in_cur_domain'_lift2
            updateCap_untyped_ranges_zero_simple
       | simp split del: if_split)+
  apply (intro conjI[rotated])

          apply (clarsimp simp: cte_wp_at_ctes_of)
          apply (auto simp: untypedZeroRange_def isCap_simps)[1]
         apply clarsimp
        apply (clarsimp simp: modify_map_def ran_def split del: if_split
                       split: if_split_asm)
         apply (clarsimp simp: cteCaps_of_def cte_wp_at_ctes_of isCap_simps)
        apply auto[1]
       apply (clarsimp simp: disj_comms cte_wp_at_ctes_of
                      dest!: ztc_phys capBits_capUntyped_capRange)
       apply (frule(1) capBits_capUntyped_capRange, simp)
       apply (clarsimp dest!: valid_global_refsD_with_objSize)
      apply (clarsimp simp: disj_comms cte_wp_at_ctes_of
                     dest!: ztc_phys capBits_capUntyped_capRange)
      apply (frule(1) capBits_capUntyped_capRange, simp)
      apply (clarsimp dest!: valid_global_refsD_with_objSize)
     apply clarsimp
     apply (auto elim: if_unsafe_then_capD' simp: isCap_simps)[1]
    apply safe[1]
     apply (clarsimp simp: cte_wp_at_ctes_of)
     apply (drule bspec[where x=sl], simp)
     apply (clarsimp simp: isCap_simps)
    apply (auto elim: if_unsafe_then_capD' simp: isCap_simps)[1]
   apply (clarsimp simp: cte_wp_at_ctes_of)
   apply (subgoal_tac "st_tcb_at' ((=) Inactive) p' s
                               \<and> obj_at' (Not \<circ> tcbQueued) p' s
                               \<and> bound_tcb_at' ((=) None) p' s
                               \<and> ko_wp_at' (Not \<circ> hyp_live') p' s
                               \<and> obj_at' (\<lambda>tcb. tcbSchedNext tcb = None
                                                \<and> tcbSchedPrev tcb = None) p' s")
    apply (clarsimp simp: pred_tcb_at'_def obj_at'_def ko_wp_at'_def projectKOs live'_def hyp_live'_def)
   subgoal by (auto dest!: isCapDs)[1]
  apply (clarsimp simp: cte_wp_at_ctes_of disj_ac
                 dest!: isCapDs)
  apply (frule ztc_phys[where cap=cap])
  apply (frule(1) capBits_capUntyped_capRange, simp)
  apply (case_tac cte)
  apply clarsimp
  apply (simp add: valid_mdb_ctes_def)
  apply (rule conjI)
   apply (subst modify_map_dlist_iff)
   apply (case_tac cte, simp)
   apply simp
  apply (rule conjI)
   apply (rule mdb_chain_0_modify_map_inv, simp)
   apply simp
  apply (rule conjI)
   apply (clarsimp simp: modify_map_apply)
   apply (simp add: valid_badges_def del: fun_upd_apply)
   apply clarify
   apply (thin_tac "\<not> isUntypedCap cap" for cap)
   apply (rule conjI; clarsimp)
    apply (clarsimp simp: isCap_simps split: if_split_asm)
      subgoal by ((elim disjE | clarsimp simp: isCap_simps)+)
     subgoal by (fastforce simp: isCap_simps sameRegionAs_def3)
    apply (clarsimp simp: mdb_next_unfold)
    apply (erule_tac x=p in allE)
    apply (erule_tac x="mdbNext node" in allE)
   subgoal by simp
   apply (clarsimp simp: isCap_simps valid_arch_badges_def split: if_split_asm)
    apply (erule_tac x=sl in allE)
    apply simp
    apply (erule_tac x=p' in allE)
    apply (solves \<open>clarsimp simp: mdb_next_unfold\<close>)
   apply (erule_tac x=p in allE)
   apply simp
   apply (erule_tac x=p' in allE)
   apply (solves \<open>clarsimp simp: mdb_next_unfold\<close>)
  apply (rule conjI)
   apply clarsimp
   apply (erule (1) caps_contained_subrange, simp)
    subgoal by (clarsimp simp: isCap_simps)
   apply (clarsimp simp add: isCap_simps)
  apply (subgoal_tac "valid_mdb' s")
   prefer 2
   apply (simp add: valid_mdb'_def valid_mdb_ctes_def)
  apply (rule conjI)
   defer
   apply (cut_tac m="ctes_of s"
            and m'="(modify_map (ctes_of s) sl
                       (cteCap_update (\<lambda>_. cap)))"
                in descendants_of_subset_untyped)
     apply (clarsimp simp: modify_map_def)
     apply (rule conjI, clarsimp simp: isCap_simps)
     apply clarsimp
    apply (simp only: modify_map_apply)
    apply (rule use_update_ztc_two [OF descendants_of_update_ztc])
            apply (rule exEI, rule vmdb.isFinal_untypedParent)
                apply (rule vmdb.intro, simp add: valid_mdb'_def)
               apply assumption
              apply (simp add: cteCaps_of_def)
             apply (clarsimp simp: isCap_simps, fastforce) (* needs unfolding before fastforce *)
            apply (clarsimp simp: isCap_simps)
           apply assumption
          apply (simp add: disj_comms)
         apply (simp add: capRange_def)
        apply (simp add: capRange_def)
       apply (rule valid_capAligned)
       apply (erule(1) ctes_of_valid')
      apply (simp add: disj_comms)
     apply clarsimp
     apply (erule(1) mdb_chain_0_no_loops)
    apply (erule (3) isFinal_no_descendants)
   apply (clarsimp simp: modify_map_apply)
   apply (rule conjI, clarsimp simp: valid_nullcaps_def isCap_simps)
   apply (rule conjI, clarsimp simp: ut_revocable'_def isCap_simps)
   apply (rule conjI, clarsimp elim!: class_links_update)
   apply (rule conjI)
    apply (erule(1) distinct_zombies_seperate_if_zombiedE)
         apply (clarsimp simp: isCap_simps)
        apply (clarsimp simp: isCap_simps)
       apply simp
      apply simp
     apply simp
    apply (erule_tac sl'=y in Final_notUntyped_capRange_disjoint,
           simp add: cteCaps_of_def,
           simp_all add: disj_ac)[1]
    apply (erule(1) ctes_of_valid_cap')
   apply (rule conjI)
    apply (subgoal_tac "cap \<noteq> IRQControlCap")
     apply (clarsimp simp: irq_control_def)
    apply (clarsimp simp: isCap_simps)
   apply (simp add: reply_masters_rvk_fb_def, erule ball_ran_fun_updI)
   apply (clarsimp simp: isCap_simps)
  apply (clarsimp simp: modify_map_apply)
  apply (erule(1) ztc_replace_update_final, simp_all)
   apply (simp add: cteCaps_of_def)
  apply (erule(1) ctes_of_valid_cap')
  done


lemma isFinal_Zombie:
  "isFinal (Zombie p' b n) p cs"
  by (simp add: isFinal_def sameObjectAs_def isCap_simps)

lemma shrink_zombie_invs':
  "\<lbrace>invs' and (K (isZombie cap))
    and cte_wp_at' (\<lambda>cte. cteCap cte = Zombie (capZombiePtr cap) (capZombieType cap) (capZombieNumber cap + 1)) sl
    and cte_wp_at' (\<lambda>cte. cteCap cte = NullCap) (capZombiePtr cap + 2^cteSizeBits * (of_nat (capZombieNumber cap)))\<rbrace>
      updateCap sl cap
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (wp make_zombie_invs')
  apply (clarsimp simp: cte_wp_at_ctes_of isFinal_Zombie isCap_simps final_matters'_def)
  apply (rule context_conjI)
   apply (drule ctes_of_valid', clarsimp)
   apply (clarsimp simp: valid_cap'_def capAligned_def)
  apply clarsimp
  apply (rule ccontr, erule notE, rule imageI)
  apply (drule word_le_minus_one_leq)
  apply (rule ccontr, simp add: linorder_not_less mult.commute mult.left_commute shiftl_t2n)
  done

lemma setQueue_cte_wp_at':
  "\<lbrace>cte_wp_at' P p\<rbrace> setQueue d pr q \<lbrace>\<lambda>rv. cte_wp_at' P p\<rbrace>"
  unfolding setQueue_def
  by (wp, clarsimp elim!: cte_wp_at'_pspaceI)

crunch suspend
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps getObject_inv_tcb simp: crunch_simps)

lemma cte_wp_at_cteCap_norm:
  "(cte_wp_at' (\<lambda>c. P (cteCap c)) p s) = (\<exists>cap. cte_wp_at' (\<lambda>c. cteCap c = cap) p s \<and> P cap)"
  by (auto simp add: cte_wp_at'_def)

lemma cte_wp_at_conj_eq':
  "cte_wp_at' (\<lambda>c. P c \<and> Q c) p s = (cte_wp_at' P p s \<and> cte_wp_at' Q p s)"
  by (auto simp add: cte_wp_at'_def)

lemma cte_wp_at_disj_eq':
  "cte_wp_at' (\<lambda>c. P c \<or> Q c) p s = (cte_wp_at' P p s \<or> cte_wp_at' Q p s)"
  by (auto simp add: cte_wp_at'_def)

crunch cancelAllIPC
  for cte_wp_at'[wp]: "cte_wp_at' P p"
  (wp: crunch_wps mapM_x_wp simp: crunch_simps)

crunch cancelAllIPC
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps mapM_x_wp simp: crunch_simps)

crunch cancelAllSignals
  for cte_wp_at'[wp]: "cte_wp_at' P p"
  (wp: crunch_wps mapM_x_wp simp: crunch_simps)

crunch cancelAllSignals
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps mapM_x_wp simp: crunch_simps)

crunch doMachineOp
  for cte_wp_at'[wp]: "cte_wp_at' P p"
  (wp: crunch_wps mapM_x_wp simp: crunch_simps)

crunch doMachineOp
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps mapM_x_wp simp: crunch_simps)

lemma valid_Zombie_cte_at':
  "\<lbrakk> s \<turnstile>' Zombie p zt m; n < zombieCTEs zt \<rbrakk> \<Longrightarrow> cte_at' (p + (of_nat n * 2^cteSizeBits)) s"
  supply raw_tcb_cte_cases_simps[simp] (* FIXME arch-split: legacy, try use tcb_cte_cases_neqs *)
  apply (clarsimp simp: valid_cap'_def split: zombie_type.split_asm)
   apply (clarsimp simp: obj_at'_def projectKOs objBits_simps)
   apply (subgoal_tac "tcb_cte_cases (of_nat n * 2^cteSizeBits) \<noteq> None")
    apply clarsimp
    apply (erule(2) cte_wp_at_tcbI')
     apply fastforce
    apply simp
   apply (thin_tac "a < word_bits" for a)
   apply ((clarsimp | erule less_handy_casesE | fastforce simp: objBits_defs)+)[1]
  apply (drule spec[where x="of_nat n"])
  apply (subst(asm) less_mask_eq)
   apply (rule order_less_le_trans)
    apply (erule of_nat_mono_maybe [rotated])
    apply (rule power_strict_increasing)
     apply (simp add: word_bits_def)
    apply simp
   apply simp
  apply (clarsimp simp: mult.commute mult.left_commute real_cte_at')
  done

lemma cteSwap_cte_wp_cteCap:
  "\<lbrace>\<lambda>s. p \<noteq> sl \<and>
       (p = p' \<longrightarrow> cte_at' p' s \<and> P cap') \<and>
       (p \<noteq> p' \<longrightarrow> cte_wp_at' (\<lambda>c. P (cteCap c)) p s)\<rbrace>
  cteSwap cap p' cap' sl
  \<lbrace>\<lambda>rv. cte_wp_at' (\<lambda>c. P (cteCap c)) p\<rbrace>"
  apply (simp add: cteSwap_def)
  apply (rule hoare_pre)
   apply (wp updateMDB_weak_cte_wp_at updateCap_cte_wp_at_cases getCTE_wp'
             hoare_vcg_all_lift)
       apply simp
       apply (wp hoare_drop_imps)[1]
       apply (wp updateMDB_weak_cte_wp_at updateCap_cte_wp_at_cases
                 getCTE_wp' hoare_vcg_all_lift hoare_weak_lift_imp)+
    apply simp
  apply (clarsimp simp: o_def)
  done

lemma capSwap_cte_wp_cteCap:
  "\<lbrace>\<lambda>s. p \<noteq> sl \<and>
       (p = p' \<longrightarrow> cte_wp_at' (\<lambda>c. P (cteCap c)) sl s) \<and>
       (p \<noteq> p' \<longrightarrow> cte_wp_at' (\<lambda>c. P (cteCap c)) p s)\<rbrace>
  capSwapForDelete p' sl
  \<lbrace>\<lambda>rv. cte_wp_at' (\<lambda>c. P (cteCap c)) p\<rbrace>"
  apply(simp add: capSwapForDelete_def)
  apply(wp)
     apply(rule cteSwap_cte_wp_cteCap)
    apply(wp getCTE_wp getCTE_cte_wp_at hoare_weak_lift_imp)+
  apply(clarsimp)
  apply(rule conjI)
   apply(simp add: cte_at_cte_wp_atD)
   apply(clarsimp simp: cte_wp_at_cteCap_norm)
   apply(unfold cte_at'_def cte_wp_at'_def)
   apply(clarsimp)
  apply(clarsimp)
  done

lemma cteSwap_cteCaps_of [wp]:
  "\<lbrace>\<lambda>s. P ((cteCaps_of s) ( a := Some cap2, b := Some cap1 ))\<rbrace>
     cteSwap cap1 a cap2 b
   \<lbrace>\<lambda>rv s. P (cteCaps_of s)\<rbrace>"
  apply (simp add: cteSwap_def)
  apply (wp getCTE_cteCap_wp | simp)+
  apply (clarsimp split: option.split)
  apply (erule rsubst[where P=P], intro ext)
  apply (clarsimp simp: modify_map_def split: if_split_asm)
  done

lemma capSwap_cteCaps_of [wp]:
  notes if_cong [cong]
  shows
  "\<lbrace>\<lambda>s. P ((cteCaps_of s) \<circ> (id ( a := b, b := a )))\<rbrace>
     capSwapForDelete a b
   \<lbrace>\<lambda>rv s. P (cteCaps_of s)\<rbrace>"
  apply(simp add: capSwapForDelete_def)
  apply(wp getCTE_wp getCTE_cteCap_wp)
  apply(clarsimp)
  apply(rule conjI)
   prefer 2
   apply(clarsimp simp: o_def)
  apply(clarsimp simp: cte_wp_at_ctes_of o_def)
  apply(erule rsubst [where P=P])
  apply(rule ext)
  apply(clarsimp simp: cte_wp_at_ctes_of cteCaps_of_def)
  done

lemma cte_wp_final_cteCaps_of:
  "(cte_wp_at' (\<lambda>c. isFinal (cteCap c) p (cteCaps_of s)) p s) =
   (\<exists>cap. cteCaps_of s p = Some cap \<and> isFinal cap p (cteCaps_of s))"
  by (auto simp add: cteCaps_of_def cte_wp_at_ctes_of)

lemma updateCap_cap_to':
  "\<lbrace>\<lambda>s. ex_cte_cap_to' p s \<and>
        cte_wp_at' (\<lambda>cte. p \<notin> cte_refs' (cteCap cte) (irq_node' s) - cte_refs' cap (irq_node' s)) sl s\<rbrace>
     updateCap sl cap
   \<lbrace>\<lambda>rv. ex_cte_cap_to' p\<rbrace>"
  apply (simp add: ex_cte_cap_to'_cteCap)
  apply wp
  apply clarsimp
  apply (rule_tac x=p' in exI)
  apply (clarsimp simp: modify_map_def cte_wp_at_ctes_of cteCaps_of_def)
  done

lemma cteDeleteOne_cap_to'[wp]:
  "\<lbrace>ex_cte_cap_wp_to' P p\<rbrace> cteDeleteOne slot \<lbrace>\<lambda>rv. ex_cte_cap_wp_to' P p\<rbrace>"
  apply (simp add: ex_cte_cap_wp_to'_def)
  apply (rule hoare_pre)
   apply (rule hoare_use_eq_irq_node'[OF cteDeleteOne_irq_node'])
   apply (wp hoare_vcg_ex_lift cteDeleteOne_cte_wp_at_preserved)
   apply (case_tac cap, simp_all add: finaliseCap_def Let_def isCap_simps)[1]
  apply simp
  done

lemmas setNotification_cap_to'[wp]
    = ex_cte_cap_to'_pres [OF setNotification_cte_wp_at' set_ntfn_ksInterrupt]

lemmas setEndpoint_cap_to'[wp]
    = ex_cte_cap_to'_pres [OF setEndpoint_cte_wp_at' setEndpoint_ksInterruptState]

lemmas setThreadState_cap_to'[wp]
    = ex_cte_cap_to'_pres [OF setThreadState_cte_wp_at' setThreadState_ksInterruptState]

crunch cancelSignal
  for cap_to'[wp]: "ex_cte_cap_wp_to' P p"
  (simp: crunch_simps wp: crunch_wps)

lemma cancelIPC_cap_to'[wp]:
  "\<lbrace>ex_cte_cap_wp_to' P p\<rbrace> cancelIPC t \<lbrace>\<lambda>rv. ex_cte_cap_wp_to' P p\<rbrace>"
  apply (simp add: cancelIPC_def Let_def)
  apply (rule bind_wp [OF _ gts_sp'])
  apply (case_tac state, simp_all add: getThreadReplySlot_def locateSlot_conv)
          apply (wp ex_cte_cap_to'_pres [OF threadSet_cte_wp_at']
               | simp add: o_def if_apply_def2
               | wpcw | wp (once) hoare_drop_imps)+
  done

lemma emptySlot_deletes [wp]:
  "\<lbrace>\<top>\<rbrace> emptySlot p opt \<lbrace>\<lambda>rv s. cte_wp_at' (\<lambda>c. cteCap c = NullCap) p s\<rbrace>"
  apply (simp add: emptySlot_def case_Null_If)
  apply (subst tree_cte_cteCap_eq [unfolded o_def])
  apply (wp getCTE_cteCap_wp opt_return_pres_lift)
  apply (clarsimp split: option.splits simp: modify_map_def)
  done

lemma capCylicZombieD[dest!]:
  "capCyclicZombie cap slot \<Longrightarrow> \<exists>zb n. cap = Zombie slot zb n"
  by (clarsimp simp: capCyclicZombie_def split: capability.split_asm)

lemma finaliseSlot_abort_cases':
  "s \<turnstile> \<lbrace>\<top>\<rbrace>
     finaliseSlot' sl ex
   \<lbrace>\<lambda>rv s. fst rv \<or> (\<not> ex \<and> cte_wp_at' (\<lambda>cte. isZombie (cteCap cte)
                                \<and> capZombiePtr (cteCap cte) = sl) sl s)\<rbrace>,\<lbrace>\<top>\<top>\<rbrace>"
proof (induct rule: finalise_spec_induct)
  case (1 slot exp)
  show ?case
    apply (subst finaliseSlot'_simps_ext)
    apply (simp only: split_def)
    apply (rule hoare_pre_spec_validE)
     apply (wp | simp)+
         apply ((wp "1.hyps" updateCap_cte_wp_at_cases)+,
                 (assumption | rule refl | simp only: split_def fst_conv snd_conv)+)
          apply (wp | simp)+
       apply (rule hoare_strengthen_post)
        apply (rule hoare_vcg_conj_lift[where Q="\<lambda>rv. cte_at' slot"])
         apply (wp typ_at_lifts [OF finaliseCap_typ_at'])[1]
        apply (rule finaliseCap_cases)
       apply (clarsimp simp: cte_wp_at_ctes_of)
      apply (wp getCTE_wp isFinalCapability_inv | simp)+
    apply (clarsimp simp: cte_wp_at_ctes_of)
    done
qed

lemmas finaliseSlot_abort_cases
    = use_spec(2) [OF finaliseSlot_abort_cases',
                      folded validE_R_def finaliseSlot_def]

crunch emptySlot
  for it[wp]: "\<lambda>s. P (ksIdleThread s)"
crunch capSwapForDelete
  for it[wp]: "\<lambda>s. P (ksIdleThread s)"

lemma cteDelete_delete_cases:
  "\<lbrace>\<top>\<rbrace>
     cteDelete slot e
   \<lbrace>\<lambda>rv. cte_wp_at' (\<lambda>c. cteCap c = NullCap
                       \<or> \<not> e \<and> isZombie (cteCap c)
                           \<and> capZombiePtr (cteCap c) = slot) slot\<rbrace>, -"
  apply (simp add: cteDelete_def whenE_def split_def)
  apply wp
    apply (rule hoare_strengthen_post [OF emptySlot_deletes])
    apply (clarsimp simp: cte_wp_at_ctes_of)
   apply wp+
   apply (rule hoare_strengthen_postE_R, rule finaliseSlot_abort_cases)
   apply (clarsimp simp: cte_wp_at_ctes_of)
  apply simp
  done

lemmas cteDelete_deletes = cteDelete_delete_cases[where e=True, simplified]

lemma cteSwap_cap_to'[wp]:
  "\<lbrace>ex_cte_cap_to' p\<rbrace> capSwapForDelete c1 c2 \<lbrace>\<lambda>rv. ex_cte_cap_to' p\<rbrace>"
  apply (simp add: cteSwap_def capSwapForDelete_def ex_cte_cap_to'_cteCap)
  apply (wp getCTE_cteCap_wp | simp add: o_def)+
  apply (clarsimp split: option.splits)
  apply (rule_tac x="(id (c1 := c2, c2 := c1)) p'" in exI)
  apply (clarsimp simp: modify_map_def | rule conjI)+
  done

lemma zombieCTEs_le:
  "zombieCTEs zb \<le> 2 ^ zBits zb"
  by (cases zb, simp_all add: objBits_defs)

lemma valid_cap'_handy_bits:
  "s \<turnstile>' Zombie r zb n \<Longrightarrow> n \<le> 2 ^ (zBits zb)"
  "s \<turnstile>' Zombie r zb n \<Longrightarrow> n < 2 ^ word_bits"
  "\<lbrakk> s \<turnstile>' Zombie r zb n; n \<noteq> 0 \<rbrakk> \<Longrightarrow> of_nat n - 1 < (2 ^ (zBits zb) :: word32)"
  "s \<turnstile>' Zombie r zb n \<Longrightarrow> zBits zb < word_bits"
  apply (insert zombieCTEs_le[where zb=zb],
         simp_all add: valid_cap'_def)
   apply (clarsimp elim!: order_le_less_trans)
  apply (clarsimp simp: word_less_nat_alt)
  apply (subgoal_tac "n \<in> unats (len_of TYPE (32))")
   apply (subst unat_minus_one)
    apply (drule of_nat_mono_maybe[rotated, where 'a=32])
     apply (simp add: unats_def)
    apply simp
   apply (simp add: word_unat.Abs_inverse)
  apply (simp only: unats_def mem_simps)
  apply (erule order_le_less_trans)
  apply (erule order_le_less_trans)
  apply (rule power_strict_increasing)
   apply (simp only: word_bits_len_of)
  apply simp
  done

lemma ex_Zombie_to:
  "\<lbrakk> ctes_of s p = Some cte; cteCap cte = Zombie p' b n;
       n \<noteq> 0; valid_objs' s \<rbrakk>
      \<Longrightarrow> ex_cte_cap_to' p' s"
  apply (simp add: ex_cte_cap_to'_def cte_wp_at_ctes_of)
  apply (intro exI, rule conjI, assumption)
  apply (simp add: image_def)
  apply (rule bexI[where x=0])
   apply simp
  apply simp
  apply (frule(1) ctes_of_valid')
  apply (drule of_nat_mono_maybe[rotated, where 'a=32])
   apply (simp only: word_bits_len_of)
   apply (erule valid_cap'_handy_bits)
  apply simp
  done

lemma ex_Zombie_to2:
  "\<lbrakk> ctes_of s p = Some cte; cteCap cte = Zombie p' b n;
       n \<noteq> 0; valid_objs' s \<rbrakk>
      \<Longrightarrow> ex_cte_cap_to' (p' + (2^cteSizeBits * of_nat n - 2^cteSizeBits)) s"
  apply (simp add: ex_cte_cap_to'_def cte_wp_at_ctes_of)
  apply (intro exI, rule conjI, assumption)
  apply (simp add: image_def)
  apply (rule bexI[where x="of_nat n - 1"])
   apply (fastforce simp: objBits_defs shiftl_t2n)
  apply (subgoal_tac "n \<in> unats (len_of TYPE(32))")
   apply (simp add: word_less_nat_alt)
   apply (subst unat_minus_one)
    apply (simp add: word_neq_0_conv)
    apply (drule of_nat_mono_maybe[rotated, where 'a=32])
     apply (simp add: unats_def)
    apply simp
   apply (simp add: word_unat.Abs_inverse)
  apply (simp only: unats_def mem_simps word_bits_len_of)
  apply (drule(1) ctes_of_valid', simp)
  apply (erule valid_cap'_handy_bits)
  done

declare word_to_1_set[simp]

lemmas finalise_spec_induct2 = finaliseSlot'.induct[where P=
    "\<lambda>sl exp s. P sl (finaliseSlot' sl exp) (\<lambda>P. exp \<or> P) s" for P]

lemma cteSwap_sch_act_simple[wp]:
  "\<lbrace>sch_act_simple\<rbrace> cteSwap cap1 slot1 cap2 slot2 \<lbrace>\<lambda>_. sch_act_simple\<rbrace>"
  by (simp add: cteSwap_def sch_act_simple_def, wp)

crunch capSwapForDelete
  for sch_act_simple[wp]: sch_act_simple

lemma updateCap_sch_act_simple[wp]:
  "\<lbrace>sch_act_simple\<rbrace> updateCap slot newCap \<lbrace>\<lambda>_. sch_act_simple\<rbrace>"
  by (simp add: sch_act_simple_def, wp)

definition
  "no_cte_prop P = (if \<forall>sl cte. \<lbrace>P\<rbrace> setCTE sl cte \<lbrace>\<lambda>_. P\<rbrace> then P else \<top>)"

lemma no_cte_prop_top:
  "no_cte_prop \<top> = \<top>"
  by (simp add: no_cte_prop_def)

definition
  "finalise_prop_stuff P
    = ((\<forall>s f. P (ksWorkUnitsCompleted_update f s) = P s)
    \<and> irq_state_independent_H P
    \<and> (\<forall>s f. P (gsUntypedZeroRanges_update f s) = P s)
    \<and> (\<forall>s f. P (ksInterruptState_update f s) = P s)
    \<and> (\<forall>s f. P (ksMachineState_update (irq_state_update f) s) = P s)
    \<and> (\<forall>s f. P (ksMachineState_update (irq_masks_update f) s) = P s))"

lemma setCTE_no_cte_prop:
  "\<lbrace>no_cte_prop P\<rbrace> setCTE sl cte \<lbrace>\<lambda>_. no_cte_prop P\<rbrace>"
  by (simp add: no_cte_prop_def hoare_vcg_prop)

lemma setInterruptState_no_cte_prop:
  "\<lbrace>no_cte_prop P and K (finalise_prop_stuff P)\<rbrace> setInterruptState st \<lbrace>\<lambda>_. no_cte_prop P\<rbrace>"
  apply (simp add: setInterruptState_def, wp)
  apply (clarsimp simp: finalise_prop_stuff_def no_cte_prop_def)
  done

lemma dmo_maskInterrupt_no_cte_prop:
  "\<lbrace>no_cte_prop P and K (finalise_prop_stuff P)\<rbrace>
    doMachineOp (maskInterrupt m irq) \<lbrace>\<lambda>_. no_cte_prop P\<rbrace>"
  apply (wp dmo_maskInterrupt)
  apply (clarsimp simp: no_cte_prop_def finalise_prop_stuff_def)
  done

lemma updateTrackedFreeIndex_no_cte_prop[wp]:
  "\<lbrace>no_cte_prop P and K (finalise_prop_stuff P)\<rbrace>
    updateTrackedFreeIndex ptr idx \<lbrace>\<lambda>_. no_cte_prop P\<rbrace>"
  apply (simp add: updateTrackedFreeIndex_def getSlotCap_def)
  apply (wp getCTE_wp')
  apply (clarsimp simp: no_cte_prop_def finalise_prop_stuff_def)
  done

crunch emptySlot, capSwapForDelete
  for no_cte_prop[wp]: "no_cte_prop P"
  (ignore: doMachineOp wp: dmo_maskInterrupt_no_cte_prop)

lemma reduceZombie_invs'':
  assumes fin:
  "\<And>s'' rv. \<lbrakk>\<not> (isZombie cap \<and> capZombieNumber cap = 0); \<not> (isZombie cap \<and> \<not> exposed); isZombie cap \<and> exposed;
              (Inr rv, s'')
              \<in> fst ((withoutPreemption $ locateSlotCap cap (fromIntegral (capZombieNumber cap - 1))) st)\<rbrakk>
             \<Longrightarrow> s'' \<turnstile> \<lbrace>\<lambda>s. no_cte_prop Q s \<and> invs' s \<and> sch_act_simple s
                                   \<and> cte_wp_at' (\<lambda>cte. isZombie (cteCap cte)) slot s
                                   \<and> ex_cte_cap_to' rv s\<rbrace>
                         finaliseSlot rv False
                \<lbrace>\<lambda>rva s. no_cte_prop Q s \<and> invs' s \<and> sch_act_simple s
                            \<and> (fst rva \<longrightarrow> cte_wp_at' (\<lambda>cte. removeable' rv s (cteCap cte)) rv s)
                            \<and> (\<forall>sl'. snd rva \<noteq> NullCap \<longrightarrow> sl' \<noteq> rv \<longrightarrow> cteCaps_of s sl' \<noteq> Some (snd rva))\<rbrace>,
                \<lbrace>\<lambda>rv s. no_cte_prop Q s \<and> invs' s \<and> sch_act_simple s\<rbrace>"
  assumes stuff:
    "finalise_prop_stuff Q"
  shows
  "st \<turnstile> \<lbrace>\<lambda>s.
      no_cte_prop Q s \<and> invs' s \<and> sch_act_simple s
              \<and> (exposed \<or> ex_cte_cap_to' slot s)
              \<and> cte_wp_at' (\<lambda>cte. cteCap cte = cap) slot s
              \<and> (exposed \<or> p = slot \<or>
                  cte_wp_at' (\<lambda>cte. (P and isZombie) (cteCap cte)
                                  \<or> (\<exists>zb n cp. cteCap cte = Zombie p zb n
                                       \<and> P cp \<and> (isZombie cp \<longrightarrow> capZombiePtr cp \<noteq> p))) p s)\<rbrace>
       reduceZombie cap slot exposed
   \<lbrace>\<lambda>rv s.
      no_cte_prop Q s \<and> invs' s \<and> sch_act_simple s
              \<and> (exposed \<or> ex_cte_cap_to' slot s)
              \<and> (exposed \<or> p = slot \<or>
                  cte_wp_at' (\<lambda>cte. (P and isZombie) (cteCap cte)
                                  \<or> (\<exists>zb n cp. cteCap cte = Zombie p zb n
                                       \<and> P cp \<and> (isZombie cp \<longrightarrow> capZombiePtr cp \<noteq> p))) p s)\<rbrace>,
   \<lbrace>\<lambda>rv s. no_cte_prop Q s \<and> invs' s \<and> sch_act_simple s\<rbrace>"
  apply (unfold reduceZombie_def cteDelete_def Let_def
                split_def fst_conv snd_conv haskell_fail_def
                case_Zombie_assert_fold)
  apply (rule hoare_pre_spec_validE)
   apply (wp hoare_vcg_disj_lift | simp)+
       apply (wp capSwap_cte_wp_cteCap getCTE_wp' | simp)+
           apply (wp shrink_zombie_invs')[1]
          apply (wp | simp)+
         apply (rule getCTE_wp)
        apply (wp | simp)+
      apply (rule_tac Q'="\<lambda>cte s. rv = capZombiePtr cap +
                                      of_nat (capZombieNumber cap) * 2^cteSizeBits - 2^cteSizeBits
                              \<and> cte_wp_at' (\<lambda>c. c = cte) slot s \<and> invs' s
                              \<and> no_cte_prop Q s \<and> sch_act_simple s"
                  in hoare_post_imp)
       apply (clarsimp simp: cte_wp_at_ctes_of mult.commute mult.left_commute dest!: isCapDs)
       apply (simp add: field_simps)
      apply (wp getCTE_cte_wp_at)+
      apply simp
      apply wp
     apply (rule spec_strengthen_postE)
      apply (rule_tac Q="\<lambda>fc s. rv = capZombiePtr cap +
                                      of_nat (capZombieNumber cap) * 2^cteSizeBits - 2^cteSizeBits"
                 in spec_valid_conj_liftE1)
       apply wp[1]
      apply (rule fin, assumption+)
     apply (clarsimp simp: stuff)
    apply (simp add: locateSlot_conv)
    apply ((wp | simp)+)[2]
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (rule conjI)
   apply (clarsimp dest!: isCapDs)
   apply (rule conjI)
    apply (erule(1) ex_Zombie_to)
     apply clarsimp
    apply clarsimp
   apply clarsimp
  apply (clarsimp dest!: isCapDs)
  apply (fastforce dest!: ex_Zombie_to2 simp: cte_level_bits_def objBits_defs)
  done

lemmas preemptionPoint_invR =
  valid_validE_R [OF preemptionPoint_inv]

lemmas preemptionPoint_invE =
  valid_validE_E [OF preemptionPoint_inv]

lemma finaliseSlot_invs':
  assumes finaliseCap:
    "\<And>cap final sl. \<lbrace>no_cte_prop Pr and invs' and sch_act_simple
        and cte_wp_at' (\<lambda>cte. cteCap cte = cap) sl\<rbrace> finaliseCap cap final False \<lbrace>\<lambda>rv. no_cte_prop Pr\<rbrace>"
  and stuff: "finalise_prop_stuff Pr"
  shows
  "st \<turnstile> \<lbrace>\<lambda>s.
      no_cte_prop Pr s \<and> invs' s \<and> sch_act_simple s
              \<and> (exposed \<or> ex_cte_cap_to' slot s)
              \<and> (exposed \<or> p = slot \<or>
                  cte_wp_at' (\<lambda>cte. (P and isZombie) (cteCap cte)
                                  \<or> (\<exists>zb n cp. cteCap cte = Zombie p zb n
                                       \<and> P cp \<and> (isZombie cp \<longrightarrow> capZombiePtr cp \<noteq> p))) p s)\<rbrace>
       finaliseSlot' slot exposed
   \<lbrace>\<lambda>rv s.
      no_cte_prop Pr s \<and> invs' s \<and> sch_act_simple s
              \<and> (exposed \<or> p = slot \<or>
                  cte_wp_at' (\<lambda>cte. (P and isZombie) (cteCap cte)
                                  \<or> (\<exists>zb n cp. cteCap cte = Zombie p zb n
                                       \<and> P cp \<and> (isZombie cp \<longrightarrow> capZombiePtr cp \<noteq> p))) p s)
              \<and> (fst rv \<longrightarrow> cte_wp_at' (\<lambda>cte. removeable' slot s (cteCap cte)) slot s)
              \<and> (\<forall>sl'. snd rv \<noteq> NullCap \<longrightarrow> sl' \<noteq> slot \<longrightarrow> cteCaps_of s sl' \<noteq> Some (snd rv))\<rbrace>,
   \<lbrace>\<lambda>rv s. no_cte_prop Pr s \<and> invs' s \<and> sch_act_simple s\<rbrace>"
proof (induct arbitrary: P p rule: finalise_spec_induct2)
  case (1 sl exp s Q q)
  let ?P = "\<lambda>cte. (Q and isZombie) (cteCap cte)
                     \<or> (\<exists>zb n cp. cteCap cte = Zombie q zb n
                          \<and> Q cp \<and> (isZombie cp \<longrightarrow> capZombiePtr cp \<noteq> q))"
  note hyps = "1.hyps"[folded reduceZombie_def[unfolded cteDelete_def finaliseSlot_def]]
  have Q: "\<And>x y n. {x :: machine_word} = (\<lambda>x. y + (x << cteSizeBits)) ` {0 ..< n} \<Longrightarrow> n = 1"
    apply (simp only: shiftl_t2n mult_ac)
    apply (drule sym)
    apply (case_tac "1 < n")
     apply (frule_tac x = "y + 0 * 2^cteSizeBits" in eqset_imp_iff)
     apply (frule_tac x = "y + 1 * 2^cteSizeBits" in eqset_imp_iff)
     apply (subst(asm) imageI, simp)
      apply (erule order_less_trans[rotated], simp)
     apply (subst(asm) imageI, simp)
     apply simp
    apply (simp add: linorder_not_less objBits_defs)
    apply (case_tac "n < 1")
     apply simp
    apply simp
    done
  have R: "\<And>n. n \<noteq> 0 \<Longrightarrow> {0 .. n - 1} = {0 ..< n :: word32}"
    apply safe
     apply simp
     apply (erule(1) word_leq_minus_one_le)
    apply simp
    apply (erule word_le_minus_one_leq)
    done
  have final_IRQHandler_no_copy:
    "\<And>irq sl sl' s. \<lbrakk> isFinal (IRQHandlerCap irq) sl (cteCaps_of s); sl \<noteq> sl' \<rbrakk> \<Longrightarrow> cteCaps_of s sl' \<noteq> Some (IRQHandlerCap irq)"
    apply (clarsimp simp: isFinal_def sameObjectAs_def2 isCap_simps)
    apply fastforce
    done
  from stuff have stuff':
    "finalise_prop_stuff (no_cte_prop Pr)"
    by (simp add: no_cte_prop_def finalise_prop_stuff_def)
  note stuff'[unfolded finalise_prop_stuff_def, simp]
  show ?case
    apply (subst finaliseSlot'.simps)
    apply (fold reduceZombie_def[unfolded cteDelete_def finaliseSlot_def])
    apply (unfold split_def)
    apply (rule hoare_pre_spec_validE)
     apply (wp | simp)+
         apply (wp make_zombie_invs' updateCap_cte_wp_at_cases
                   hoare_vcg_disj_lift)[1]
        apply (wp hyps)

          apply ((wp preemptionPoint_invE preemptionPoint_invR
              | clarsimp simp: sch_act_simple_def
              | simp cong: kernel_state.fold_congs machine_state.fold_congs)+)[1]
         apply (rule spec_strengthen_postE [OF reduceZombie_invs''[OF _ stuff]])
          prefer 2
          apply fastforce
         apply (rule hoare_pre_spec_validE,
                rule spec_strengthen_postE)
          apply (unfold finaliseSlot_def)[1]
           apply (rule hyps[where P="\<top>" and p=sl], (assumption | rule refl)+)
          apply clarsimp
         apply (clarsimp simp: cte_wp_at_ctes_of)
        apply (wp, simp)
        apply (wp make_zombie_invs' updateCap_ctes_of_wp updateCap_cap_to'
                  hoare_vcg_disj_lift updateCap_cte_wp_at_cases)+
       apply simp
       apply (rule hoare_strengthen_post)
        apply (rule_tac Q="\<lambda>fin s. invs' s \<and> sch_act_simple s \<and> s \<turnstile>' (fst fin)
                                 \<and> (exp \<or> ex_cte_cap_to' sl s)
                                 \<and> no_cte_prop Pr s
                                 \<and> cte_wp_at' (\<lambda>cte. cteCap cte = cteCap rv) sl s
                                 \<and> (q = sl \<or> exp \<or> cte_wp_at' (?P) q s)"
                   in hoare_vcg_conj_lift)
         apply (wp hoare_vcg_disj_lift finaliseCap finaliseCap_invs[where sl=sl])
         apply (rule finaliseCap_zombie_cap')
        apply (rule hoare_vcg_conj_lift)
         apply (rule finaliseCap_cte_refs)
        apply (rule finaliseCap_replaceable[where slot=sl])
       apply clarsimp
       apply (erule disjE[where P="F \<and> G" for F G])
        apply (clarsimp simp: capRemovable_def cte_wp_at_ctes_of)
        apply (rule conjI, clarsimp)
        apply (case_tac b; case_tac "cteCap rv"; simp add: arch_cap_has_cleanup'_def)
        apply (clarsimp simp: final_IRQHandler_no_copy)
       apply (clarsimp dest!: isCapDs)
       apply (rule conjI)
        apply (clarsimp simp: capRemovable_def)
        apply (rule conjI)
         apply (clarsimp simp: cte_wp_at_ctes_of)
         apply (rule conjI, clarsimp)
         apply (case_tac "cteCap rv",
                simp_all add: isCap_simps removeable'_def
                              fun_eq_iff[where f="cte_refs' cap" for cap]
                              fun_eq_iff[where f=tcb_cte_cases]
                              tcb_cte_cases_def
                              word_neq_0_conv[symmetric])[1]
        apply (clarsimp simp: cte_wp_at_ctes_of)
        apply (rule conjI, clarsimp)
        apply (case_tac "cteCap rv",
               simp_all add: isCap_simps removeable'_def
                             fun_eq_iff[where f="cte_refs' cap" for cap]
                             fun_eq_iff[where f=tcb_cte_cases]
                             tcb_cte_cases_def cteSizeBits_def)[1]
         apply (frule Q[unfolded cteSizeBits_def, simplified])
         apply clarsimp
        apply (simp add: mask_def)
        apply (subst(asm) R)
         apply (drule valid_capAligned [OF ctes_of_valid'])
          apply fastforce
         apply (simp add: capAligned_def word_bits_def)
        apply (frule Q[unfolded cteSizeBits_def, simplified])
        apply clarsimp
       apply (clarsimp simp: cte_wp_at_ctes_of capRemovable_def)
       apply (subgoal_tac "final_matters' (cteCap rv) \<and> \<not> isUntypedCap (cteCap rv)")
        apply clarsimp
        apply (rule conjI)
         apply clarsimp
        apply clarsimp
       apply (case_tac "cteCap rv",
              simp_all add: isCap_simps final_matters'_def)[1]
      apply (wp isFinalCapability_inv hoare_weak_lift_imp | simp | wp (once) isFinal[where x=sl])+
     apply (wp getCTE_wp')
    apply (clarsimp simp: cte_wp_at_ctes_of disj_ac)
    apply (rule conjI, clarsimp simp: removeable'_def)
    apply (clarsimp simp: conj_comms)
    apply (rule conjI, erule ctes_of_valid', clarsimp)
    apply (rule conjI, clarsimp)
    apply fastforce
    done
qed

lemma finaliseSlot_invs'':
  "\<lbrace>\<lambda>s. invs' s \<and> sch_act_simple s \<and> (\<not> exposed \<longrightarrow> ex_cte_cap_to' slot s)\<rbrace>
     finaliseSlot slot exposed
   \<lbrace>\<lambda>rv s. invs' s \<and> sch_act_simple s \<and> (fst rv \<longrightarrow> cte_wp_at' (\<lambda>cte. removeable' slot s (cteCap cte)) slot s)
                 \<and> (\<forall>sl'. snd rv \<noteq> NullCap \<longrightarrow> sl' \<noteq> slot \<longrightarrow> cteCaps_of s sl' \<noteq> Some (snd rv))\<rbrace>,
   \<lbrace>\<lambda>rv s. invs' s \<and> sch_act_simple s\<rbrace>"
  unfolding finaliseSlot_def
  apply (rule hoare_pre, rule hoare_strengthen_postE, rule use_spec)
     apply (rule finaliseSlot_invs'[where P="\<top>" and Pr="\<top>" and p=slot])
      apply (simp_all add: no_cte_prop_top)
    apply wp
   apply (simp add: finalise_prop_stuff_def)
  apply clarsimp
  done

lemma finaliseSlot_invs:
  "\<lbrace>\<lambda>s. invs' s \<and> sch_act_simple s \<and> (\<not> e \<longrightarrow> ex_cte_cap_to' slot s)\<rbrace> finaliseSlot slot e \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (rule validE_valid, rule hoare_strengthen_postE)
    apply (rule finaliseSlot_invs'')
   apply simp+
  done

lemma finaliseSlot_sch_act_simple:
  "\<lbrace>\<lambda>s. invs' s \<and> sch_act_simple s \<and> (\<not> e \<longrightarrow> ex_cte_cap_to' slot s)\<rbrace> finaliseSlot slot e \<lbrace>\<lambda>rv. sch_act_simple\<rbrace>"
  apply (rule validE_valid, rule hoare_strengthen_postE)
    apply (rule finaliseSlot_invs'')
   apply simp+
  done

lemma finaliseSlot_removeable:
  "\<lbrace>\<lambda>s. invs' s \<and> sch_act_simple s \<and> (\<not> e \<longrightarrow> ex_cte_cap_to' slot s)\<rbrace>
     finaliseSlot slot e
   \<lbrace>\<lambda>rv s. fst rv \<longrightarrow> cte_wp_at' (\<lambda>cte. removeable' slot s (cteCap cte)) slot s\<rbrace>,-"
  apply (rule validE_validE_R, rule hoare_strengthen_postE)
    apply (rule finaliseSlot_invs'')
   apply simp+
  done

lemma finaliseSlot_irqs:
  "\<lbrace>\<lambda>s. invs' s \<and> sch_act_simple s \<and> (\<not> e \<longrightarrow> ex_cte_cap_to' slot s)\<rbrace>
     finaliseSlot slot e
   \<lbrace>\<lambda>rv s. \<forall>sl'. snd rv \<noteq> NullCap \<longrightarrow> sl' \<noteq> slot \<longrightarrow> cteCaps_of s sl' \<noteq> Some (snd rv)\<rbrace>,-"
  apply (rule validE_validE_R, rule hoare_strengthen_postE)
    apply (rule finaliseSlot_invs'')
   apply simp+
  done

lemma finaliseSlot_cte_wp_at:
  "\<lbrakk> \<And>cap. P cap \<Longrightarrow> isZombie cap; p \<noteq> slot \<rbrakk> \<Longrightarrow>
   \<lbrace>\<lambda>s. invs' s \<and> sch_act_simple s \<and> ex_cte_cap_to' slot s
         \<and> cte_wp_at' (\<lambda>cte. P (cteCap cte)) p s\<rbrace>
     finaliseSlot slot False
   \<lbrace>\<lambda>rv s. cte_wp_at' (\<lambda>cte. P (cteCap cte) \<or>
                         (\<exists>zb n cp. cteCap cte = Zombie p zb n \<and>
                              P cp \<and> capZombiePtr cp \<noteq> p)) p s\<rbrace>,-"
  unfolding finaliseSlot_def
  apply (rule hoare_pre, unfold validE_R_def)
   apply (rule hoare_strengthen_postE, rule use_spec)
     apply (rule finaliseSlot_invs'[where P=P and Pr=\<top> and p=p])
      apply (simp_all add: no_cte_prop_top finalise_prop_stuff_def)
    apply wp
   apply (clarsimp simp: cte_wp_at_ctes_of)
   apply fastforce
  apply (clarsimp simp: cte_wp_at_ctes_of)
  done

lemmas reduceZombie_invs'
    = reduceZombie_invs''[where Q=\<top>, simplified no_cte_prop_top simp_thms
         finalise_prop_stuff_def irq_state_independent_H_def,
         OF drop_spec_validE TrueI,
         OF hoare_weaken_preE,
         OF finaliseSlot_invs'',
         THEN use_specE']

lemma reduceZombie_invs:
  "\<lbrace>\<lambda>s. invs' s \<and> sch_act_simple s \<and> (\<not> exposed \<longrightarrow> ex_cte_cap_to' slot s)
           \<and> cte_wp_at' (\<lambda>cte. cteCap cte = cap) slot s\<rbrace>
     reduceZombie cap slot exposed
   \<lbrace>\<lambda>rv s. invs' s\<rbrace>"
  apply (rule validE_valid)
  apply (rule hoare_strengthen_postE, rule hoare_pre, rule reduceZombie_invs'[where p=slot])
     apply clarsimp+
  done

lemma reduceZombie_cap_to:
  "\<lbrace>\<lambda>s. invs' s \<and> sch_act_simple s \<and> (\<not> exposed \<longrightarrow> ex_cte_cap_to' slot s)
           \<and> cte_wp_at' (\<lambda>cte. cteCap cte = cap) slot s\<rbrace>
     reduceZombie cap slot exposed
   \<lbrace>\<lambda>rv s. \<not> exposed \<longrightarrow> ex_cte_cap_to' slot s\<rbrace>, -"
  apply (rule validE_validE_R, rule hoare_pre,
         rule hoare_strengthen_postE)
     apply (rule reduceZombie_invs'[where p=slot])
     apply clarsimp+
  done

lemma reduceZombie_sch_act_simple:
  "\<lbrace>\<lambda>s. invs' s \<and> sch_act_simple s \<and> (\<not> exposed \<longrightarrow> ex_cte_cap_to' slot s)
           \<and> cte_wp_at' (\<lambda>cte. cteCap cte = cap) slot s\<rbrace>
     reduceZombie cap slot exposed
   \<lbrace>\<lambda>rv. sch_act_simple\<rbrace>"
  apply (rule validE_valid, rule hoare_pre,
         rule hoare_strengthen_postE)
     apply (rule reduceZombie_invs'[where p=slot])
     apply clarsimp+
  done

lemma cteDelete_invs':
  "\<lbrace>invs' and sch_act_simple and K ex\<rbrace> cteDelete ptr ex \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: cteDelete_def whenE_def split_def)
  apply (rule hoare_pre, wp finaliseSlot_invs)
   apply (rule hoare_strengthen_postE_R)
    apply (unfold validE_R_def)
    apply (rule use_spec)
    apply (rule spec_valid_conj_liftE1)
     apply (rule finaliseSlot_removeable)
    apply (rule spec_valid_conj_liftE1)
     apply (rule finaliseSlot_irqs)
    apply (rule finaliseSlot_abort_cases'[folded finaliseSlot_def])
   apply simp
  apply simp
  done

declare cases_simp_conj[simp]

crunch capSwapForDelete
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps)

lemma cteDelete_typ_at' [wp]:
  "\<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> cteDelete slot exposed \<lbrace>\<lambda>_ s. P (typ_at' T p s)\<rbrace>"
  by (wp cteDelete_preservation | simp | fastforce)+

lemmas cteDelete_typ_at'_lifts [wp] = typ_at_lifts [OF cteDelete_typ_at']

lemma cteDelete_cte_at:
  "\<lbrace>\<top>\<rbrace> cteDelete slot bool \<lbrace>\<lambda>rv. cte_at' slot\<rbrace>"
  apply (rule_tac P'="\<lambda>s. cte_at' slot s \<or> \<not> cte_at' slot s"
               in hoare_weaken_pre)
   apply (rule hoare_strengthen_post)
    apply (rule hoare_vcg_disj_lift)
     apply (rule typ_at_lifts, rule cteDelete_typ_at')
    apply (simp add: cteDelete_def finaliseSlot_def split_def)
    apply (rule validE_valid, rule bindE_wp_fwd)
     apply (subst finaliseSlot'_simps_ext)
     apply (rule bindE_wp_fwd)
      apply simp
      apply (rule getCTE_sp)
     apply (rule hoare_pre, rule hoare_FalseE)
     apply (clarsimp simp: cte_wp_at_ctes_of)
    apply (rule hoare_FalseE)
   apply auto
  done

lemma cteDelete_cte_wp_at_invs:
  "\<lbrakk> \<And>cap. P cap \<Longrightarrow> isZombie cap \<rbrakk> \<Longrightarrow>
   \<lbrace>\<lambda>s. invs' s \<and> sch_act_simple s \<and> ex_cte_cap_to' slot s \<and>
       cte_wp_at' (\<lambda>cte. P (cteCap cte)) p s\<rbrace>
     cteDelete slot False
   \<lbrace>\<lambda>rv. cte_at' slot and invs' and sch_act_simple
        and cte_wp_at' (\<lambda>cte. P (cteCap cte) \<or> cteCap cte = NullCap \<or>
        (\<exists>zb n cp. cteCap cte = capability.Zombie p zb n \<and> P cp
             \<and> (capZombiePtr cp \<noteq> p \<or> p = slot))) p\<rbrace>, -"
  apply (rule hoare_pre)
   apply (wp cteDelete_cte_at)
   prefer 2
   apply (erule_tac Q="invs' s \<and> R" for s R in conjI[rotated])
   apply simp
  apply (simp only: cteDelete_def withoutPreemption_def fun_app_def split_def)
  apply (cases "p = slot")
   apply (cases "\<exists>cp. P cp")
    apply (simp add: whenE_def)
    apply wp
      apply (rule hoare_strengthen_post [OF emptySlot_deletes])
      apply (clarsimp simp: cte_wp_at_ctes_of)
     apply wp
    apply (simp add: imp_conjR conj_comms)
    apply (rule_tac Q'="\<lambda>rv s. invs' s \<and> sch_act_simple s \<and>
                   (fst rv \<longrightarrow>
                       cte_wp_at' (\<lambda>cte. removeable' slot s (cteCap cte)) slot s) \<and>
                   (fst rv \<longrightarrow>
                       (\<forall>sl'. snd rv \<noteq> NullCap \<longrightarrow> sl' \<noteq> slot \<longrightarrow>
                                  cteCaps_of s sl' \<noteq> Some (snd rv))) \<and>
                   (\<not> fst rv \<longrightarrow>
                       cte_wp_at' (\<lambda>cte. P (cteCap cte) \<or>
                                         cteCap cte = NullCap \<or>
                                         (\<exists>zb n. cteCap cte = Zombie slot zb n))
                                  slot s)"
                and E'="\<lambda>rv. \<top>" in hoare_strengthen_postE)
      apply (wp finaliseSlot_invs finaliseSlot_removeable finaliseSlot_sch_act_simple
                hoare_drop_impE_R[OF finaliseSlot_irqs])
       apply (rule hoare_strengthen_postE_R, rule finaliseSlot_abort_cases)
       apply (clarsimp simp: cte_wp_at_ctes_of dest!: isCapDs)
      apply simp
     apply simp
    apply simp
   apply (simp add: cte_wp_at_ctes_of validE_R_def)
  apply (simp add: whenE_def)
  apply (wp emptySlot_cte_wp_cap_other)
   apply (rule_tac Q'="\<lambda>rv s. invs' s \<and> sch_act_simple s \<and>
                  (fst rv \<longrightarrow>
                      cte_wp_at' (\<lambda>cte. removeable' slot s (cteCap cte)) slot s) \<and>
                  (fst rv \<longrightarrow>
                      (\<forall>sl'. snd rv \<noteq> NullCap \<longrightarrow> sl' \<noteq> slot \<longrightarrow>
                                 cteCaps_of s sl' \<noteq> Some (snd rv))) \<and>
                  cte_wp_at' (\<lambda>cte. P (cteCap cte) \<or>
                                    cteCap cte = NullCap \<or>
                                    (\<exists>zb n. cteCap cte = Zombie p zb n) \<and>
                                    (\<exists>cp. P cp \<and> capZombiePtr cp \<noteq> p))
                             p s"
               in hoare_strengthen_postE_R)
    apply (wp finaliseSlot_invs finaliseSlot_removeable finaliseSlot_sch_act_simple
              hoare_drop_impE_R[OF finaliseSlot_irqs])
    apply (rule hoare_strengthen_postE_R [OF finaliseSlot_cte_wp_at[where p=p and P=P]])
      apply simp+
    apply (clarsimp simp: cte_wp_at_ctes_of)
   apply simp
  apply simp
  done


lemma cteDelete_sch_act_simple:
  "\<lbrace>invs' and sch_act_simple and (\<lambda>s. \<not> exposed \<longrightarrow> ex_cte_cap_to' slot s)\<rbrace>
     cteDelete slot exposed \<lbrace>\<lambda>rv. sch_act_simple\<rbrace>"
  apply (simp add: cteDelete_def whenE_def split_def)
  apply (wp hoare_drop_imps | simp)+
  apply (rule_tac hoare_strengthen_postE [where Q'="\<lambda>rv. sch_act_simple"
                                       and E'="\<lambda>rv. sch_act_simple"])
    apply (rule valid_validE)
    apply (wp finaliseSlot_sch_act_simple)
    apply simp+
  done

crunch emptySlot
  for st_tcb_at'[wp]: "st_tcb_at' P t" (simp: case_Null_If)

crunch vcpuSwitch
  for st_tcb_at'[wp]: "st_tcb_at' P t"
  (simp: crunch_simps wp: crunch_wps FalseI)

crunch "Arch.finaliseCap", unbindMaybeNotification, prepareThreadDelete
  for st_tcb_at'[wp]: "st_tcb_at' P t"
  (simp: crunch_simps
   wp: crunch_wps getObject_inv loadObject_default_inv)
end


lemma finaliseCap2_st_tcb_at':
  assumes x[simp]: "\<And>st. simple' st \<Longrightarrow> P st"
  shows "\<lbrace>st_tcb_at' P t\<rbrace>
     finaliseCap cap final flag
   \<lbrace>\<lambda>rv. st_tcb_at' P t\<rbrace>"
  apply (simp add: finaliseCap_def Let_def
                   getThreadCSpaceRoot deletingIRQHandler_def
             cong: if_cong split del: if_split)
  apply (rule hoare_pre)
   apply ((wp cancelAllIPC_st_tcb_at cancelAllSignals_st_tcb_at
              prepareThreadDelete_st_tcb_at'
              suspend_st_tcb_at' cteDeleteOne_st_tcb_at getCTE_wp'
             | simp add: gen_isCap_simps getSlotCap_def getIRQSlot_def
                         locateSlot_conv getInterruptState_def
                  split del: if_split
             | wpc))+
  done

crunch capSwapForDelete
  for st_tcb_at'[wp]: "st_tcb_at' P t"

lemma cteDelete_st_tcb_at':
  assumes x[simp]: "\<And>st. simple' st \<Longrightarrow> P st"
  shows "\<lbrace>st_tcb_at' P t\<rbrace>
     cteDelete slot ex
   \<lbrace>\<lambda>rv. st_tcb_at' P t\<rbrace>"
  apply (rule cteDelete_preservation)
     apply (rule finaliseCap2_st_tcb_at' [OF x])
     apply assumption
    apply wp+
  apply auto
  done

definition
  capToRPO :: "capability \<Rightarrow> word32 option \<times> nat"
where
 "capToRPO cap \<equiv> case cap of
    NullCap \<Rightarrow> (None, 0)
  | Zombie p zt n \<Rightarrow> (Some p, 2)
  | _ \<Rightarrow> (None, 3)"

lemma emptySlot_rvk_prog:
  "\<lbrace>\<lambda>s. revoke_progress_ord m (option_map capToRPO \<circ> cteCaps_of s)\<rbrace>
     emptySlot sl opt
   \<lbrace>\<lambda>rv s. revoke_progress_ord m (option_map capToRPO \<circ> cteCaps_of s)\<rbrace>"
  apply (simp add: emptySlot_def case_Null_If)
  apply (wp getCTE_cteCap_wp opt_return_pres_lift)
  apply (clarsimp simp: o_def split: option.split)
  apply (erule rpo_trans)
  apply (rule rpo_delta[where S="{sl}"], simp_all)
   apply (simp add: modify_map_def)
  apply (simp add: Int_insert_left dom_def modify_map_def)
  apply (clarsimp simp: capToRPO_def split: capability.split)
  done

lemma rvk_prog_modify_map:
  "\<lbrakk> \<And>x. Some x = m p \<Longrightarrow>
          capToRPO (f x) = capToRPO x
       \<or> rpo_measure p (Some (capToRPO (f x)))
           < rpo_measure p (Some (capToRPO x)) \<rbrakk>
    \<Longrightarrow> revoke_progress_ord (option_map capToRPO \<circ> m) (option_map capToRPO \<circ> (modify_map m p f))"
  apply (cases "m p")
   apply (simp add: modify_map_def fun_upd_idem)
   apply (simp add: revoke_progress_ord_def)
  apply simp
  apply (erule disjE)
   apply (simp add: modify_map_def fun_upd_idem)
   apply (simp add: revoke_progress_ord_def)
  apply (rule rpo_delta[where S="{p}"],
         simp_all add: modify_map_def dom_def)
  done

lemma capSwap_rvk_prog:
  "\<lbrace>\<lambda>s. revoke_progress_ord m (option_map capToRPO \<circ> cteCaps_of s)
           \<and> cte_wp_at' (\<lambda>cte. \<exists>n. (capToRPO (cteCap cte)) = (Some p1, Suc n)) p2 s
           \<and> cte_wp_at' (\<lambda>cte. fst (capToRPO (cteCap cte)) \<noteq> Some p1) p1 s\<rbrace>
     capSwapForDelete p1 p2
   \<lbrace>\<lambda>rv s. revoke_progress_ord m (option_map capToRPO \<circ> cteCaps_of s)\<rbrace>"
  apply wp
  apply (clarsimp simp: cte_wp_at_ctes_of cteCaps_of_def)
  apply (cases "p1 = p2")
   apply simp
  apply (erule rpo_trans)
  apply (rule rpo_delta[where S="{p1, p2}"], simp_all)
  apply (simp add: Int_insert_left dom_def)
  apply (case_tac "capToRPO (cteCap ctea)")
  apply simp
  apply arith
  done

lemmas cancelAllIPC_cteCaps_of[wp] = ctes_of_cteCaps_of_lift [OF cancelAllIPC_ctes_of]
lemmas cancelAllSignals_cteCaps_of[wp] = ctes_of_cteCaps_of_lift [OF cancelAllSignals_ctes_of]
lemmas setEndpoint_cteCaps_of[wp] = ctes_of_cteCaps_of_lift [OF set_ep_ctes_of]
lemmas setNotification_cteCaps_of[wp] = ctes_of_cteCaps_of_lift [OF set_ntfn_ctes_of]

lemmas emptySlot_rvk_prog' = emptySlot_rvk_prog[unfolded o_def]
lemmas threadSet_ctesCaps_of = ctes_of_cteCaps_of_lift[OF threadSet_ctes_of]

context begin interpretation Arch . (*FIXME: arch-split*)

lemmas setObject_ASID_cteCaps_of[wp] = ctes_of_cteCaps_of_lift [OF setObject_ASID_ctes_of']
lemmas storePTE_cteCaps_of[wp] = ctes_of_cteCaps_of_lift [OF storePTE_ctes]
lemmas storePDE_cteCaps_of[wp] = ctes_of_cteCaps_of_lift [OF storePDE_ctes]

lemma vcpuSwitch_rvk_prog':
  "vcpuSwitch v \<lbrace>\<lambda>s. revoke_progress_ord m (\<lambda>x. map_option capToRPO (cteCaps_of s x))\<rbrace>"
  by (wpsimp simp: cteCaps_of_def)

crunch vcpuFinalise
  for ctes_of[wp]: "\<lambda>s. P (ctes_of s)"

lemma vcpuFinalise_rvk_prog':
  "vcpuFinalise v \<lbrace>\<lambda>s. revoke_progress_ord m (\<lambda>x. map_option capToRPO (cteCaps_of s x))\<rbrace>"
  by (wpsimp simp: cteCaps_of_def)

context
notes option.case_cong_weak[cong]
begin
crunch finaliseCap
  for rvk_prog': "\<lambda>s. revoke_progress_ord m (\<lambda>x. option_map capToRPO (cteCaps_of s x))"
  (wp: crunch_wps threadSet_ctesCaps_of getObject_inv
       loadObject_default_inv dissociateVCPUTCB_isFinal
   simp: crunch_simps o_def
   ignore: threadSet)
end

lemmas finalise_induct3 = finaliseSlot'.induct[where P=
    "\<lambda>sl exp s. P sl (finaliseSlot' sl exp) s" for P]

lemma finaliseSlot_rvk_prog:
  "s \<turnstile> \<lbrace>\<lambda>s. revoke_progress_ord m (option_map capToRPO \<circ> cteCaps_of s)\<rbrace>
       finaliseSlot' slot e
   \<lbrace>\<lambda>rv s. revoke_progress_ord m (option_map capToRPO \<circ> cteCaps_of s)\<rbrace>,\<lbrace>\<top>\<top>\<rbrace>"
proof (induct rule: finalise_induct3)
  case (1 sl ex st)
  show ?case
    apply (subst finaliseSlot'.simps)
    apply (unfold split_def)
    apply (rule hoare_pre_spec_validE)
     apply wp
         apply ((wp | simp)+)[1]
     apply (wp "1.hyps")
          apply (unfold Let_def split_def fst_conv
                        snd_conv haskell_fail_def
                        case_Zombie_assert_fold)
          apply (wp capSwap_rvk_prog | simp only: withoutPreemption_def)+
        apply (wp preemptionPoint_inv)[1]
        apply force
        apply force
        apply (wp capSwap_rvk_prog | simp only: withoutPreemption_def)+
           apply (wp getCTE_wp | simp)+
            apply (rule hoare_strengthen_post [OF emptySlot_rvk_prog[where m=m]])
            apply (clarsimp simp: cte_wp_at_ctes_of cteCaps_of_def o_def
                           dest!: isCapDs)
            apply (erule rpo_trans)
            apply (rule rvk_prog_modify_map[unfolded o_def])
            apply (clarsimp simp: capToRPO_def)
           apply (rule spec_strengthen_postE,
                  rule "1.hyps", (assumption | rule refl)+)
           apply (clarsimp simp: cte_wp_at_ctes_of)
           apply (erule rpo_trans)
           apply (rule rvk_prog_modify_map[unfolded o_def])
           apply (clarsimp simp: cteCaps_of_def capToRPO_def dest!: isCapDs)
          apply ((wp | simp add: locateSlot_conv)+)[2]
        apply (rule drop_spec_validE)
        apply simp
        apply (rule_tac Q'="\<lambda>rv s. revoke_progress_ord m (option_map capToRPO \<circ> cteCaps_of s)
                                     \<and> cte_wp_at' (\<lambda>cte. cteCap cte = fst rvb) sl s"
                         in hoare_post_imp)
         apply (clarsimp simp: o_def cte_wp_at_ctes_of capToRPO_def
                        dest!: isCapDs)
         apply (simp split: capability.split_asm)
        apply (wp updateCap_cte_wp_at_cases | simp)+
       apply (rule hoare_strengthen_post)
        apply (rule_tac Q="\<lambda>fc s. cte_wp_at' (\<lambda>cte. cteCap cte = cteCap rv) sl s
                               \<and> revoke_progress_ord m (option_map capToRPO \<circ> cteCaps_of s)"
                   in hoare_vcg_conj_lift)
         apply (wp finaliseCap_rvk_prog'[folded o_def])[1]
        apply (rule finaliseCap_cases)
       apply (clarsimp simp: o_def cte_wp_at_ctes_of cteCaps_of_def)
       apply (strengthen imp_consequent, simp)
       apply (erule rpo_trans)
       apply (rule rvk_prog_modify_map[unfolded o_def])
       apply (erule disjE, simp add: capRemovable_def)
       apply (auto dest!: isCapDs simp: capToRPO_def split: if_split if_split_asm)[1]
      apply (wp isFinalCapability_inv getCTE_wp | simp)+
    apply (clarsimp simp: cte_wp_at_ctes_of o_def)
    done
qed

lemma cteDelete_rvk_prog:
  "\<lbrace>\<lambda>s. revoke_progress_ord m (option_map capToRPO \<circ> cteCaps_of s)\<rbrace>
       cteDelete slot e
   \<lbrace>\<lambda>rv s. revoke_progress_ord m (option_map capToRPO \<circ> cteCaps_of s)\<rbrace>,-"
  including no_pre
  apply (simp add: cteDelete_def whenE_def split_def)
  apply (wp emptySlot_rvk_prog)
  apply (simp only: cases_simp)
  apply (simp add: finaliseSlot_def)
  apply (rule use_spec, rule finaliseSlot_rvk_prog)
  done

text \<open>Proving correspondence between the delete functions.\<close>

definition
  "spec_corres s r P P' f f' \<equiv> corres r (P and ((=) s)) P' f f'"

lemma use_spec_corres':
  assumes x: "\<And>s. Q s \<Longrightarrow> spec_corres s r P P' f f'"
  shows      "corres r (P and Q) P' f f'"
  apply (clarsimp simp: corres_underlying_def)
  apply (frule x)
  apply (clarsimp simp: spec_corres_def corres_underlying_def)
  apply (erule(1) my_BallE, simp)+
  done

lemmas use_spec_corres = use_spec_corres'[where Q="\<top>", simplified]

lemma drop_spec_corres:
  "corres r P P' f f' \<Longrightarrow> spec_corres s r P P' f f'"
  unfolding spec_corres_def
  apply (erule corres_guard_imp)
   apply simp
  apply assumption
  done

lemma spec_corres_split:
  assumes x: "spec_corres s r' P P' f f'"
  assumes y: "\<And>rv rv' s'. \<lbrakk> (rv, s') \<in> fst (f s); r' rv rv' \<rbrakk> \<Longrightarrow>
                spec_corres s' r (R rv) (R' rv') (g rv) (g' rv')"
  assumes z: "\<lbrace>Q\<rbrace> f \<lbrace>R\<rbrace>" "\<lbrace>Q'\<rbrace> f' \<lbrace>R'\<rbrace>"
  shows "spec_corres s r (P and Q) (P' and Q') (f >>= g) (f' >>= g')"
proof -
  have w: "\<And>rv rv'. r' rv rv' \<Longrightarrow> corres r (R rv and (\<lambda>s'. (rv, s') \<in> fst (f s))) (R' rv') (g rv) (g' rv')"
    apply (rule use_spec_corres')
    apply (erule(1) y)
    done
  show ?thesis
    unfolding spec_corres_def
    apply (rule corres_guard_imp)
      apply (rule corres_split)
         apply (rule x[unfolded spec_corres_def])
        apply (erule w)
       apply (wp z)
       apply (rule univ_wp)
      apply (rule z)
     apply simp
    apply assumption
    done
qed

lemma spec_corres_splitE:
  assumes x: "spec_corres s (e \<oplus> r') P P' f f'"
  assumes y: "\<And>rv rv' s'. \<lbrakk> (Inr rv, s') \<in> fst (f s); r' rv rv' \<rbrakk> \<Longrightarrow>
                spec_corres s' (e \<oplus> r) (R rv) (R' rv') (g rv) (g' rv')"
  assumes z: "\<lbrace>Q\<rbrace> f \<lbrace>R\<rbrace>,-" "\<lbrace>Q'\<rbrace> f' \<lbrace>R'\<rbrace>,-"
  shows "spec_corres s (e \<oplus> r) (P and Q) (P' and Q') (f >>=E g) (f' >>=E g')"
proof -
  note w = z[unfolded validE_R_def validE_def]
  show ?thesis
    unfolding bindE_def
    apply (rule spec_corres_split [OF x _ w(1) w(2)])
    apply (case_tac rv)
     apply (clarsimp simp: lift_def spec_corres_def)
    apply (clarsimp simp: lift_def)
    apply (erule(1) y)
    done
qed

lemmas spec_corres_split' = spec_corres_split [OF drop_spec_corres]
lemmas spec_corres_splitE' = spec_corres_splitE [OF drop_spec_corres]

lemma spec_corres_guard_imp:
  assumes x: "spec_corres s r Q Q' f f'"
  assumes y: "P s \<Longrightarrow> Q s" "\<And>s'. P' s' \<Longrightarrow> Q' s'"
  shows      "spec_corres s r P P' f f'"
  unfolding spec_corres_def
  apply (rule corres_guard_imp)
    apply (rule x[unfolded spec_corres_def])
   apply (clarsimp elim!: y)
  apply (erule y)
  done

lemma spec_corres_returns[simp]:
  "spec_corres s r  P P' (return x) (return y) = (\<forall>s'. (P s \<and> P' s' \<and> (s, s') \<in> state_relation) \<longrightarrow> r x y)"
  "spec_corres s r' P P' (returnOk x) (returnOk y) = (\<forall>s'. (P s \<and> P' s' \<and> (s, s') \<in> state_relation) \<longrightarrow> r' (Inr x) (Inr y))"
  by (simp add: spec_corres_def returnOk_def)+

lemma cte_map_replicate:
  "cte_map (ptr, replicate bits False) = ptr"
  by (simp add: cte_map_def)

lemma spec_corres_locate_Zombie:
  "\<lbrakk> P s \<Longrightarrow> valid_cap (cap.Zombie ptr bits (Suc n)) s;
      spec_corres s r P P' f (f' (cte_map (ptr, nat_to_cref (zombie_cte_bits bits) n))) \<rbrakk>
    \<Longrightarrow> spec_corres s r P P' f (locateSlotCap (Zombie ptr (zbits_map bits) (Suc n)) (of_nat n) >>= f')"
  unfolding spec_corres_def
  apply (simp add: locateSlot_conv cte_level_bits_def stateAssert_def bind_assoc)
  apply (rule corres_symb_exec_r[OF _ get_sp])
    apply (rule corres_assume_pre, clarsimp)
    apply (frule cte_at_nat_to_cref_zbits, rule lessI)
    apply (subst(asm) cte_map_nat_to_cref)
      apply (drule valid_Zombie_n_less_cte_bits)
      apply simp
     apply (clarsimp simp: valid_cap_def cap_aligned_def word_bits_def
                     split: option.split_asm)
    apply (simp add: mult.commute cte_level_bits_def)
    apply (clarsimp simp: isCap_simps valid_cap_def)
    apply (simp only: assert_def, subst if_P)
     apply (cases bits, simp_all add: zbits_map_def)
     apply (clarsimp simp: cap_table_at_gsCNodes isCap_simps
                           zbits_map_def)
     apply (rule word_of_nat_less)
     apply (simp add: cap_aligned_def)
    apply (erule corres_guard_imp, simp_all)
   apply wp+
  done

lemma spec_corres_req:
  "\<lbrakk> \<And>s'. \<lbrakk> P s; P' s'; (s, s') \<in> state_relation \<rbrakk> \<Longrightarrow> F;
     F \<Longrightarrow> spec_corres s r P P' f f' \<rbrakk>
     \<Longrightarrow> spec_corres s r P P' f f'"
  unfolding spec_corres_def
  apply (rule corres_assume_pre, erule meta_mp)
  apply simp
  done

lemma zombie_alignment_oddity:
  "\<lbrakk> cte_wp_at (\<lambda>c. c = cap.Zombie (cte_map slot) zb n) slot s;
     invs s \<rbrakk> \<Longrightarrow> (cte_map slot, replicate (zombie_cte_bits zb) False) = slot"
  apply (frule cte_wp_at_valid_objs_valid_cap, clarsimp+)
  apply (rule cte_map_inj_eq)
       apply (simp only: cte_map_replicate)
      apply (erule cte_at_replicate_zbits)
     apply (erule cte_wp_at_weakenE, simp)
    apply clarsimp+
  done

primrec
  rec_del_concrete :: "rec_del_call \<Rightarrow> (bool \<times> capability) kernel_p set"
where
  "rec_del_concrete (CTEDeleteCall ptr ex)
     = {liftME (\<lambda>x. (True, NullCap)) (cteDelete (cte_map ptr) ex)}"
| "rec_del_concrete (FinaliseSlotCall ptr ex)
     = {finaliseSlot (cte_map ptr) ex}"
| "rec_del_concrete (ReduceZombieCall cap slot ex)
     = (if red_zombie_will_fail cap then {} else
       (\<lambda>cap. liftME (\<lambda>x. (True, NullCap)) (reduceZombie cap (cte_map slot) ex)) ` {cap'. cap_relation cap cap'})"

lemma rec_del_concrete_empty:
  "red_zombie_will_fail cap \<Longrightarrow> rec_del_concrete (ReduceZombieCall cap slot ex) = {}"
  by simp

lemmas rec_del_concrete_unfold
  = rec_del_concrete.simps red_zombie_will_fail.simps
    if_True if_False ball_simps simp_thms

lemma cap_relation_removables:
  "\<lbrakk> cap_relation cap cap'; isNullCap cap' \<or> isZombie cap';
      s \<turnstile> cap; cte_at slot s; invs s \<rbrakk>
       \<Longrightarrow> cap_removeable cap slot = capRemovable cap' (cte_map slot)
               \<and> cap_cyclic_zombie cap slot = capCyclicZombie cap' (cte_map slot)"
  apply (clarsimp simp: capRemovable_def isCap_simps
                        capCyclicZombie_def cap_cyclic_zombie_def
                 split: cap_relation_split_asm arch_cap.split_asm)
  apply (rule iffD1 [OF conj_commute], rule context_conjI)
   apply (rule iffI)
    apply (clarsimp simp: cte_map_replicate)
   apply clarsimp
   apply (frule(1) cte_map_inj_eq [rotated, OF _ cte_at_replicate_zbits])
       apply clarsimp+
    apply (simp add: cte_map_replicate)
   apply simp
  apply simp
  done

lemma spec_corres_add_asm:
  "spec_corres s r P Q f g \<Longrightarrow> spec_corres s r (P and F) Q f g"
  unfolding spec_corres_def
  apply (erule corres_guard_imp)
   apply simp+
  done

lemma spec_corres_gen_asm2:
  "(F \<Longrightarrow> spec_corres s r Q P' f g) \<Longrightarrow> spec_corres s r Q (P' and (\<lambda>s. F)) f g"
  unfolding spec_corres_def
  by (auto intro: corres_gen_asm2)

crunch reduceZombie
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  (simp: crunch_simps wp: crunch_wps)

lemmas reduceZombie_typ_ats[wp] = typ_at_lifts [OF reduceZombie_typ_at']

lemma spec_corres_if:
  "\<lbrakk> G = G'; G \<Longrightarrow> spec_corres s r P P' a c; \<not> G \<Longrightarrow> spec_corres s r Q Q' b d\<rbrakk>
    \<Longrightarrow> spec_corres s r (\<lambda>x. (G \<longrightarrow> P x) \<and> (\<not> G \<longrightarrow> Q x)) (\<lambda>x. (G' \<longrightarrow> P' x) \<and> (\<not> G' \<longrightarrow> Q' x))
        (if G then a else b) (if G' then c else d)"
  by simp

lemma spec_corres_liftME2:
  "spec_corres s (f \<oplus> r) P P' m (liftME fn m')
      = spec_corres s (f \<oplus> (\<lambda>x. r x \<circ> fn)) P P' m m'"
  by (simp add: spec_corres_def)


lemma rec_del_ReduceZombie_emptyable:
  "\<lbrace>invs
      and (cte_wp_at ((=) cap) slot and is_final_cap' cap
      and (\<lambda>y. is_zombie cap)) and
         (\<lambda>s. \<not> ex \<longrightarrow> ex_cte_cap_wp_to (\<lambda>cp. cap_irqs cp = {}) slot s) and
         emptyable slot and
         (\<lambda>s. \<not> cap_removeable cap slot \<and> (\<forall>t\<in>obj_refs cap. halted_if_tcb t s))\<rbrace>
   rec_del (ReduceZombieCall cap slot ex) \<lbrace>\<lambda>rv. emptyable slot\<rbrace>, -"
  by (rule rec_del_emptyable [where args="ReduceZombieCall cap slot ex", simplified])

crunch cteDelete
  for sch_act_simple[wp]: sch_act_simple

lemmas preemption_point_valid_list = preemption_point_inv'[where P="valid_list", simplified]

lemma finaliseSlot_typ_at'[wp]:
  "\<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> finaliseSlot ptr exposed \<lbrace>\<lambda>_ s. P (typ_at' T p s)\<rbrace>"
  by (rule finaliseSlot_preservation, (wp | simp)+)

lemmas finaliseSlot_typ_ats[wp] = typ_at_lifts[OF finaliseSlot_typ_at']

lemmas rec_del_valid_list_irq_state_independent[wp] =
  rec_del_preservation[OF cap_swap_for_delete_valid_list set_cap_valid_list empty_slot_valid_list finalise_cap_valid_list preemption_point_valid_list]

lemma rec_del_corres:
  "\<forall>C \<in> rec_del_concrete args.
   spec_corres s (dc \<oplus> (case args of
                            FinaliseSlotCall _ _ \<Rightarrow> (\<lambda>r r'. fst r = fst r'
                                                           \<and> cap_relation (snd r) (snd r') )
                          | _ \<Rightarrow> dc))
      (einvs and simple_sched_action
            and valid_rec_del_call args
            and cte_at (slot_rdcall args)
            and emptyable (slot_rdcall args)
            and (\<lambda>s. \<not> exposed_rdcall args \<longrightarrow> ex_cte_cap_wp_to (\<lambda>cp. cap_irqs cp = {}) (slot_rdcall args) s)
            and (\<lambda>s. case args of ReduceZombieCall cap sl ex \<Rightarrow>
                                     \<forall>t\<in>obj_refs cap. halted_if_tcb t s
                                | _ \<Rightarrow> True))
      (invs' and sch_act_simple and cte_at' (cte_map (slot_rdcall args)) and
       (\<lambda>s. \<not> exposed_rdcall args \<longrightarrow> ex_cte_cap_to' (cte_map (slot_rdcall args)) s)
        and (\<lambda>s. case args of ReduceZombieCall cap sl ex \<Rightarrow>
                     \<exists>cp'. cap_relation cap cp'
                            \<and> ((cte_wp_at' (\<lambda>cte. cteCap cte = cp') (cte_map sl))
                                 and (\<lambda>s. \<not> capRemovable cp' (cte_map sl)
                                       \<and> (\<not> ex \<longrightarrow> \<not> capCyclicZombie cp' (cte_map sl)))) s
                  | _ \<Rightarrow> True))
      (rec_del args) C"
proof (induct rule: rec_del.induct,
       simp_all only: rec_del_fails rec_del_concrete_empty
                      red_zombie_will_fail.simps ball_simps(5))
  case (1 slot exposed)
  show ?case
    apply (clarsimp simp: cteDelete_def liftME_def bindE_assoc
                          split_def)
    apply (rule spec_corres_guard_imp)
      apply (rule spec_corres_splitE)
         apply (rule "1.hyps"[simplified rec_del_concrete_unfold dc_def])
        apply (rule drop_spec_corres)
        apply (simp(no_asm) add: dc_def[symmetric] liftME_def[symmetric]
                                 whenE_liftE)
        apply (rule corres_when, simp)
        apply simp
        apply (rule emptySlot_corres)
       apply (wp rec_del_invs rec_del_valid_list rec_del_cte_at finaliseSlot_invs hoare_drop_imps
                 preemption_point_inv'
            | simp)+
    done
next
  case (2 slot exposed)
  have prove_imp:
    "\<And>P Q. \<lbrakk> P \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> (P \<longrightarrow> Q) = True"
    by simp
  show ?case
    apply (simp only: rec_del_concrete_unfold finaliseSlot_def)
    apply (subst rec_del_simps_ext)
    apply (subst finaliseSlot'_simps_ext)
    apply (fold reduceZombie_def[unfolded cteDelete_def finaliseSlot_def])
    apply (unfold fun_app_def unlessE_whenE K_bind_def split_def)
    apply (rule spec_corres_guard_imp)
      apply (rule spec_corres_splitE')
         apply simp
         apply (rule get_cap_corres)
        apply (rule spec_corres_if)
          apply auto[1]
         apply (rule drop_spec_corres, rule corres_trivial,
                simp add: returnOk_def)
        apply (rule spec_corres_splitE')
           apply simp
           apply (rule isFinalCapability_corres[where ptr=slot])
          apply (rule spec_corres_splitE')
             apply simp
             apply (rule finaliseCap_corres[where sl=slot])
               apply simp
              apply simp
             apply simp

            apply (rule_tac F="isZombie (fst rv'b) \<or> isNullCap (fst rv'b)"
                      in spec_corres_gen_asm2)
            apply (rule spec_corres_req[rotated])
             apply (rule_tac F="\<lambda>s. invs s \<and> cte_at slot s \<and> s \<turnstile> fst rvb"
                       in spec_corres_add_asm)
             apply (rule spec_corres_if)
               apply (erule conjunct1)
              apply (rule drop_spec_corres, rule corres_trivial,
                     simp add: returnOk_def)
             apply (rule spec_corres_if)
               apply (erule conjunct2)
              apply (rule drop_spec_corres,
                     simp add: liftME_def[symmetric] o_def dc_def[symmetric])
              apply (rule updateCap_corres)
               apply simp
              apply (simp(no_asm_use) add: cap_cyclic_zombie_def split: cap.split_asm)
              apply (simp add: is_cap_simps)
             apply (rule spec_corres_splitE')
                apply simp
                apply (rule updateCap_corres, erule conjunct1)
                apply (case_tac "fst rvb", auto simp: isCap_simps is_cap_simps)[1]
               apply (rule spec_corres_splitE)
                  apply (rule iffD1 [OF spec_corres_liftME2[where fn="\<lambda>v. (True, NullCap)"]])
                  apply (rule bspec [OF "2.hyps"(1), unfolded fun_app_def], assumption+)
                  apply (case_tac "fst rvb", simp_all add: isCap_simps is_cap_simps)[1]
                   apply (rename_tac nat)
                   apply (case_tac nat, simp_all)[1]
                  apply clarsimp
                 apply (rule spec_corres_splitE'[OF preemptionPoint_corres])
                   apply (rule "2.hyps"(2)[unfolded fun_app_def rec_del_concrete_unfold
                                                    finaliseSlot_def],
                          assumption+)
                  apply (wp preemption_point_inv')[1]
                  apply clarsimp+
                 apply (wp preemptionPoint_invR)
                  apply simp
                 apply clarsimp
                apply simp
                apply (wp rec_del_invs rec_del_cte_at reduce_zombie_cap_somewhere
                          rec_del_ReduceZombie_emptyable
                          reduceZombie_invs reduce_zombie_cap_to | simp)+
               apply (wp reduceZombie_cap_to reduceZombie_sch_act_simple)
              apply simp
              apply ((wp replace_cap_invs final_cap_same_objrefs
                        set_cap_cte_wp_at set_cap_cte_cap_wp_to
                        hoare_vcg_const_Ball_lift hoare_weak_lift_imp
                         | simp add: conj_comms
                         | erule finalise_cap_not_reply_master [simplified])+)
          apply (elim conjE, strengthen exI[mk_strg I],
    strengthen asm_rl[where psi="(cap_relation cap cap')" for cap cap', mk_strg I E])
             apply (wp make_zombie_invs' updateCap_cap_to'
                        updateCap_cte_wp_at_cases
                        hoare_vcg_ex_lift hoare_weak_lift_imp)
            apply clarsimp
            apply (drule_tac cap=a in cap_relation_removables,
                      clarsimp, assumption+)
            apply (clarsimp simp: conj_comms)
           apply (wp | simp)+
           apply (rule hoare_strengthen_post)
            apply (rule_tac Q="\<lambda>fin s. einvs s \<and> simple_sched_action s
                                      \<and> replaceable s slot (fst fin) rv
                                      \<and> cte_wp_at ((=) rv) slot s \<and> s \<turnstile> fst fin
                                      \<and> emptyable slot s
                                      \<and> (\<forall>t\<in>obj_refs (fst fin). halted_if_tcb t s)"
                       in hoare_vcg_conj_lift)
             apply (wp finalise_cap_invs finalise_cap_replaceable
                       finalise_cap_makes_halted
                       hoare_vcg_disj_lift hoare_vcg_ex_lift)[1]
            apply (rule finalise_cap_cases[where slot=slot])
           apply clarsimp
           apply (frule if_unsafe_then_capD, clarsimp, clarsimp)
           apply (clarsimp simp: cte_wp_at_caps_of_state)
           apply (erule disjE[where P="c = cap.NullCap \<and> P" for c P])
            apply clarsimp
           apply (clarsimp simp: conj_comms dest!: is_cap_simps [THEN iffD1])
           apply (frule trans [OF _ appropriate_Zombie, OF sym])
           apply (case_tac rv, simp_all add: fst_cte_ptrs_def is_cap_simps
                                             is_final_cap'_def)[1]
          apply (wp | simp)+
          apply (rule hoare_strengthen_post)
           apply (rule_tac Q="\<lambda>fin s. invs' s \<and> sch_act_simple s \<and> s \<turnstile>' fst fin
                                    \<and> (exposed \<or> ex_cte_cap_to' (cte_map slot) s)
                                    \<and> cte_wp_at' (\<lambda>cte. cteCap cte = cteCap rv') (cte_map slot) s"
                      in hoare_vcg_conj_lift)
            apply (wp hoare_vcg_disj_lift finaliseCap_invs[where sl="cte_map slot"])[1]
           apply (rule hoare_vcg_conj_lift)
            apply (rule finaliseCap_replaceable[where slot="cte_map slot"])
           apply (rule finaliseCap_cte_refs)
          apply clarsimp
          apply (erule disjE[where P="F \<and> G" for F G])
           apply (clarsimp simp: capRemovable_def cte_wp_at_ctes_of)
          apply (clarsimp dest!: isCapDs simp: cte_wp_at_ctes_of)
          apply (case_tac "cteCap rv'",
                 auto simp add: isCap_simps is_cap_simps final_matters'_def)[1]
         apply (wp isFinalCapability_inv hoare_weak_lift_imp
                 | simp add: is_final_cap_def conj_comms cte_wp_at_eq_simp)+
       apply (rule isFinal[where x="cte_map slot"])
      apply (wp get_cap_wp| simp add: conj_comms)+
      apply (wp getCTE_wp')
     apply clarsimp
     apply (frule cte_wp_at_valid_objs_valid_cap[where P="(=) cap" for cap])
      apply fastforce
     apply (fastforce simp: cte_wp_at_caps_of_state)
    apply (clarsimp simp: cte_wp_at_ctes_of)
    apply (frule ctes_of_valid', clarsimp)
    apply ((clarsimp | rule conjI)+)[1]
    done

next
  case (3 ptr bits n slot)
  show ?case
    apply simp
    apply (rule drop_spec_corres)
    apply (simp add: reduceZombie_def case_Zombie_assert_fold)
    apply (rule stronger_corres_guard_imp[rotated])
      apply assumption
     apply (rule conjI)
      apply clarsimp
      apply (drule cte_wp_valid_cap, clarsimp)
      apply (clarsimp simp: cte_wp_at_caps_of_state)
      apply (drule cte_at_replicate_zbits)
      apply (drule cte_at_get_cap_wp, clarsimp)
      apply (rule cte_wp_at_weakenE')
       apply (erule(1) pspace_relation_cte_wp_at[OF state_relation_pspace_relation])
        apply clarsimp+
      apply (rule TrueI)
     apply assumption
    apply (rule_tac F="(ptr, replicate (zombie_cte_bits bits) False) \<noteq> slot" in corres_req)
     apply (clarsimp simp: capCyclicZombie_def cte_map_replicate)
    apply (rule_tac F="ptr \<noteq> cte_map slot" in corres_req)
     apply (elim conjE exE)
     apply (frule cte_wp_valid_cap, clarsimp)
     apply (drule cte_map_inj)
          apply (erule cte_at_replicate_zbits)
         apply (erule cte_wp_at_weakenE, simp)
        apply clarsimp+
     apply (simp add: cte_map_replicate)
    apply (simp add: liftM_def liftME_def[symmetric])
    apply (simp add: liftE_bindE)
    apply (rule corres_symb_exec_r [OF _ getCTE_sp])
      apply (rule_tac F="isZombie (cteCap x) \<longrightarrow> capZombiePtr (cteCap x) \<noteq> ptr"
                   in corres_req)
       apply (clarsimp simp: state_relation_def dest!: isCapDs)
       apply (drule pspace_relation_cte_wp_atI')
         apply (subst(asm) eq_commute, assumption)
        apply clarsimp
       apply clarsimp
       apply (case_tac c, simp_all)[1]
       apply (clarsimp simp: cte_wp_at_def)
       apply (drule(1) zombies_finalD2, clarsimp+)
      apply (fold dc_def)
      apply (rule corres_guard_imp, rule capSwapForDelete_corres)
         apply (simp add: cte_map_replicate)
        apply simp
       apply clarsimp
       apply (rule conjI, clarsimp)+
       apply (rule conjI, rule cte_at_replicate_zbits, erule cte_wp_valid_cap)
        apply clarsimp
       apply (clarsimp simp: cte_wp_at_caps_of_state)
       apply (erule tcb_valid_nonspecial_cap, fastforce)
        apply (clarsimp simp: ran_tcb_cap_cases is_cap_simps is_nondevice_page_cap_simps
                       split: Structures_A.thread_state.split)
       apply (simp add: ran_tcb_cap_cases is_cap_simps is_nondevice_page_cap_simps)
      apply fastforce
     apply wp
    apply (rule no_fail_pre, wp)
    apply (clarsimp simp: cte_map_replicate)
    done
next
  note if_cong [cong] option.case_cong [cong]
  case (4 ptr bits n slot)
  let ?target = "(ptr, nat_to_cref (zombie_cte_bits bits) n)"
  note hyps = "4.hyps"[simplified rec_del_concrete_unfold spec_corres_liftME2]
  show ?case
    apply (simp only: rec_del_concrete_unfold cap_relation.simps)
    apply (simp add: reduceZombie_def Let_def
                     liftE_bindE
                del: inf_apply)
    apply (subst rec_del_simps_ext)
    apply (rule_tac F="ptr + 2 ^ cte_level_bits * of_nat n
                         = cte_map ?target"
              in spec_corres_req)
     apply clarsimp
     apply (drule cte_wp_valid_cap, clarsimp)
     apply (subst cte_map_nat_to_cref)
       apply (drule valid_Zombie_n_less_cte_bits, simp)
      apply (clarsimp simp: valid_cap_def cap_aligned_def word_bits_def
                     split: option.split_asm)
     apply (simp add: cte_level_bits_def)
    apply (simp add: spec_corres_liftME2 pred_conj_assoc)
    apply (rule spec_corres_locate_Zombie)
     apply (auto dest: cte_wp_valid_cap)[1]
    apply (rule_tac F="n < 2 ^ (word_bits - cte_level_bits)" in spec_corres_req)
     apply clarsimp
     apply (drule cte_wp_valid_cap, clarsimp)
     apply (frule valid_Zombie_n_less_cte_bits)
     apply (drule Suc_le_lessD)
     apply (erule order_less_le_trans)
     apply (rule power_increasing)
      apply (clarsimp simp: valid_cap_def cap_aligned_def
                     split: option.split_asm)
       apply (simp add: cte_level_bits_def word_bits_def)
      apply simp
     apply simp
    apply (rule spec_corres_gen_asm2)
    apply (rule spec_corres_guard_imp)
      apply (rule spec_corres_splitE)
         apply (rule hyps)
         apply (simp add: in_monad)
        apply (rule drop_spec_corres)
        apply (simp add: liftE_bindE del: rec_del.simps)
        apply (rule corres_split[OF get_cap_corres])
          apply (rule_tac F="cteCap ourCTE = Zombie ptr (zbits_map bits) (Suc n)
                               \<or> cteCap ourCTE = NullCap
                               \<or> (\<exists>zb n cp. cteCap ourCTE = Zombie (cte_map slot) zb n
                                      \<and> cp = Zombie ptr (zbits_map bits) (Suc n)
                                      \<and> capZombiePtr cp \<noteq> cte_map slot)"
                      in corres_gen_asm2)
          apply (rule_tac P="invs and cte_wp_at (\<lambda>c. c = new_cap) slot
                                and cte_wp_at (\<lambda>c. c = cap.NullCap \<or> \<not> False \<and> is_zombie c
                                                    \<and> ?target \<in> fst_cte_ptrs c) ?target"
                     and  P'="invs' and sch_act_simple
                                    and cte_wp_at' (\<lambda>c. c = ourCTE) (cte_map slot)
                                    and cte_at' (cte_map ?target)"
                     in corres_inst)
          apply (erule disjE)
           apply (case_tac new_cap, simp_all split del: if_split)[1]
           apply (simp add: liftME_def[symmetric])
           apply (rule stronger_corres_guard_imp)
             apply (rule corres_symb_exec_r)
                apply (rule_tac F="cteCap endCTE = capability.NullCap"
                            in corres_gen_asm2, simp)
                apply (rule updateCap_corres)
                 apply simp
                apply (simp add: is_cap_simps)
               apply (rule_tac Q'="\<lambda>rv. cte_at' (cte_map ?target)" in hoare_post_add)
               apply (wp, (wp getCTE_wp)+)
              apply (clarsimp simp: cte_wp_at_ctes_of)
             apply (rule no_fail_pre, wp, simp)
            apply clarsimp
            apply (frule zombies_finalD, clarsimp)
             apply (clarsimp simp: is_cap_simps)
            apply (clarsimp simp: cte_wp_at_caps_of_state is_cap_simps)
           apply (clarsimp simp: cte_wp_at_ctes_of)
           apply (frule cte_wp_valid_cap[unfolded cte_wp_at_eq_simp], clarsimp)
           apply (drule cte_wp_at_norm[where p="?target"], clarsimp)
           apply (erule disjE)
            apply (drule(1) pspace_relation_cte_wp_at
                                [OF state_relation_pspace_relation],
                   clarsimp+)
            apply (clarsimp simp: cte_wp_at_ctes_of)
           apply (clarsimp simp: is_cap_simps fst_cte_ptrs_def
                                 cte_wp_at_ctes_of)
           apply (frule cte_at_cref_len [rotated, OF cte_at_replicate_zbits])
            apply (fastforce simp add: cte_wp_at_caps_of_state)
           apply clarsimp
           apply (drule(1) nat_to_cref_replicate_Zombie)
            apply simp
           apply (clarsimp simp: capRemovable_def cte_wp_at_def)
           apply (drule(1) zombies_finalD2, clarsimp+)
           apply (simp add: is_cap_simps)
          apply (erule disjE)
           apply (case_tac new_cap, simp_all split del: if_split)[1]
           apply (simp add: assertE_def returnOk_def)
          apply (elim exE conjE)
          apply (case_tac new_cap, simp_all)[1]
          apply (clarsimp simp add: is_zombie_def)
          apply (simp add: assertE_def liftME_def[symmetric]
                        split del: if_split)
          apply (rule corres_req[rotated], subst if_P, assumption)
           apply (simp add: returnOk_def)
          apply (clarsimp simp: zombie_alignment_oddity cte_map_replicate)
         apply (wp get_cap_cte_wp_at getCTE_wp' rec_del_cte_at
                   rec_del_invs rec_del_delete_cases)+
      apply (rule hoare_strengthen_postE_R)
       apply (rule_tac P="\<lambda>cp. cp = Zombie ptr (zbits_map bits) (Suc n)"
                    in cteDelete_cte_wp_at_invs[where p="cte_map slot"])
       apply clarsimp
      apply (clarsimp simp: cte_wp_at_ctes_of | rule conjI)+
      apply (clarsimp simp: capRemovable_def shiftl_t2n[symmetric])
      apply (drule arg_cong[where f="\<lambda>x. x >> cte_level_bits"],
             subst(asm) shiftl_shiftr_id)
        apply (clarsimp simp: cte_level_bits_def word_bits_def)
       apply (rule order_less_le_trans)
        apply (erule of_nat_mono_maybe [rotated])
        apply (rule power_strict_increasing)
         apply (simp add: word_bits_def cte_level_bits_def)
        apply simp
       apply (simp add: word_bits_def)
      apply simp
      apply (erule(1) notE [rotated, OF _ of_nat_neq_0])
      apply (erule order_less_le_trans)
      apply (rule power_increasing)
       apply (simp add: word_bits_def cte_level_bits_def)
      apply simp
     apply clarsimp
     apply (frule cte_wp_valid_cap, clarsimp)
     apply (rule conjI, erule cte_at_nat_to_cref_zbits)
      apply simp
     apply (simp add: halted_emptyable)
     apply (erule(1) zombie_is_cap_toE)
      apply simp
     apply simp
    apply (clarsimp simp: cte_wp_at_ctes_of)
    apply (frule ctes_of_valid', clarsimp+)
    apply (frule valid_Zombie_cte_at'[where n=n])
     apply (clarsimp simp: valid_cap'_def)
    apply (intro conjI)
     apply (fastforce simp: cte_wp_at_ctes_of cte_level_bits_def objBits_defs
                            mult.commute mult.left_commute)
    apply (clarsimp simp: ex_cte_cap_to'_def cte_wp_at_ctes_of)
    apply (rule_tac x="cte_map slot" in exI)
    apply (clarsimp simp: image_def)
    apply (rule_tac x="of_nat n" in bexI)
     apply (simp add: cte_level_bits_def shiftl_t2n objBits_defs mult.commute mult.left_commute)
    apply simp
    apply (subst field_simps, rule plus_one_helper2)
     apply simp
    apply (frule of_nat_mono_maybe[rotated, where 'a=32])
     apply (rule power_strict_increasing)
      apply (simp add: word_bits_def cte_level_bits_def)
     apply simp
    apply clarsimp
    apply (drule_tac f="\<lambda>x. x - 1" and y=0 in arg_cong)
    apply (clarsimp simp: word_bits_def cte_level_bits_def)
    done
qed

lemma cteDelete_corres:
  "corres (dc \<oplus> dc)
      (einvs and simple_sched_action and cte_at ptr and emptyable ptr)
      (invs' and sch_act_simple and cte_at' (cte_map ptr))
      (cap_delete ptr) (cteDelete (cte_map ptr) True)"
  unfolding cap_delete_def
  using rec_del_corres[where args="CTEDeleteCall ptr True"]
  apply (simp add: spec_corres_liftME2 liftME_def[symmetric])
  apply (erule use_spec_corres)
  done


text \<open>The revoke functions, and their properties, are
        slightly easier to deal with than the delete
        function. However, their termination arguments
        are complex, requiring that the delete functions
        reduce the number of non-null capabilities.\<close>

definition
  cteRevoke_recset :: "((machine_word \<times> kernel_state) \<times> (machine_word \<times> kernel_state)) set"
where
 "cteRevoke_recset \<equiv> measure (\<lambda>(sl, s). (\<lambda>mp. \<Sum>x \<in> dom mp. rpo_measure x (mp x))
                                   (option_map capToRPO \<circ> cteCaps_of s))"

lemma wf_cteRevoke_recset:
  "wf cteRevoke_recset"
  by (simp add: cteRevoke_recset_def)

termination cteRevoke
  apply (rule cteRevoke.termination)
   apply (rule wf_cteRevoke_recset)
  apply (clarsimp simp add: cteRevoke_recset_def in_monad
                  dest!: in_getCTE in_preempt')
  apply (frule use_validE_R [OF _ cteDelete_rvk_prog])
   apply (rule rpo_sym)
  apply (frule use_validE_R [OF _ cteDelete_deletes])
   apply simp
  apply (simp add: revoke_progress_ord_def)
  apply (erule disjE)
   apply (drule_tac f="\<lambda>f. f (mdbNext (cteMDBNode rv))" in arg_cong)
   apply (clarsimp simp: cte_wp_at_ctes_of cteCaps_of_def capToRPO_def)
   apply (simp split: capability.split_asm)
   apply (case_tac rvb, clarsimp)
  apply assumption
  done

lemma cteRevoke_preservation':
  assumes x: "\<And>ptr. \<lbrace>P\<rbrace> cteDelete ptr True \<lbrace>\<lambda>rv. P\<rbrace>"
  assumes y: "\<And>f s. P (ksWorkUnitsCompleted_update f s) = P s"
  assumes irq: "irq_state_independent_H P"
  shows      "s \<turnstile> \<lbrace>P\<rbrace> cteRevoke ptr \<lbrace>\<lambda>rv. P\<rbrace>,\<lbrace>\<lambda>rv. P\<rbrace>"
proof (induct rule: cteRevoke.induct)
  case (1 p s')
  show ?case
    apply (subst cteRevoke.simps)
    apply (wp "1.hyps")
        apply (wp x y preemptionPoint_inv hoare_drop_imps irq | clarsimp)+
    done
qed

lemmas cteRevoke_preservation =
       validE_valid [OF use_spec(2) [OF cteRevoke_preservation']]

lemma cteRevoke_typ_at':
  "\<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> cteRevoke ptr \<lbrace>\<lambda>rv s. P (typ_at' T p s)\<rbrace>"
  by (wp cteRevoke_preservation | clarsimp)+

lemma cteRevoke_invs':
  "\<lbrace>invs' and sch_act_simple\<rbrace> cteRevoke ptr \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (rule_tac Q'="\<lambda>rv. invs' and sch_act_simple" in hoare_strengthen_post)
  apply (wp cteRevoke_preservation cteDelete_invs' cteDelete_sch_act_simple)+
    apply simp_all
  done

declare cteRevoke.simps[simp del]

lemma spec_corres_symb_exec_l_Ex:
  assumes x: "\<And>rv. (rv, s) \<in> fst (f s) \<Longrightarrow> spec_corres s r (Q rv) P' (g rv) h"
  shows      "spec_corres s r (\<lambda>s. \<exists>rv. Q rv s \<and> (rv, s) \<in> fst (f s)) P'
                              (do rv \<leftarrow> f; g rv od) h"
proof -
  have y: "\<And>rv. corres r (\<lambda>s'. s' = s \<and> Q rv s \<and> (rv, s) \<in> fst (f s)) P' (g rv) h"
    apply (rule corres_req)
     defer
     apply (rule corres_guard_imp,
            erule x[unfolded spec_corres_def])
      apply simp+
    done
  show ?thesis
    unfolding spec_corres_def
    apply (rule corres_guard_imp,
           rule corres_symb_exec_l_Ex,
           rule y)
     apply simp+
    done
qed

lemma spec_corres_symb_exec_l_Ex2:
  assumes y: "P s \<Longrightarrow> \<exists>rv. (rv, s) \<in> fst (f s)"
  assumes x: "\<And>rv. (rv, s) \<in> fst (f s) \<Longrightarrow>
                   spec_corres s r (\<lambda>s. \<exists>s'. (rv, s) \<in> fst (f s') \<and> P s') P' (g rv) h"
  shows      "spec_corres s r P P' (do rv \<leftarrow> f; g rv od) h"
  apply (rule spec_corres_guard_imp)
    apply (rule spec_corres_symb_exec_l_Ex)
    apply (erule x)
   apply (frule y)
   apply fastforce
  apply assumption
  done

lemma spec_corres_symb_exec_r_All:
  assumes nf: "\<And>rv. no_fail (Q' rv) g"
  assumes x: "\<And>rv. spec_corres s r P (Q' rv) f (h rv)"
  shows      "spec_corres s r P (\<lambda>s. (\<forall>p \<in> fst (g s). snd p = s \<and> Q' (fst p) s) \<and> (\<exists>rv. Q' rv s))
                              f (do rv \<leftarrow> g; h rv od)"
  unfolding spec_corres_def
  apply (rule corres_guard_imp,
         rule corres_symb_exec_r_All,
         rule nf,
         rule x[unfolded spec_corres_def])
   apply simp+
  done

lemma spec_corres_symb_exec_r_Ex:
  assumes y: "\<And>s. P' s \<Longrightarrow> \<forall>p \<in> fst (g s). snd p = s"
  assumes z: "\<And>s. P' s \<Longrightarrow> \<exists>p \<in> fst (g s). snd p = s"
  assumes nf: "no_fail P' g"
  assumes x: "\<And>rv. spec_corres s r P (\<lambda>s. \<exists>s'. (rv, s) \<in> fst (g s') \<and> P' s') f (h rv)"
  shows      "spec_corres s r P P' f (do rv \<leftarrow> g; h rv od)"
  apply (rule spec_corres_guard_imp)
    apply (rule spec_corres_symb_exec_r_All)
     prefer 2
     apply (rule x)
    apply (insert nf)[1]
    apply (clarsimp simp: no_fail_def)
    apply (frule y)
    apply (drule(1) bspec)
    apply fastforce
   apply assumption
  apply (frule y)
  apply (rule conjI)
   apply clarsimp
   apply (drule(1) bspec)
   apply fastforce
  apply (frule z)
  apply fastforce
  done

lemma in_getCTE_cte_wp_at':
  "(rv, s') \<in> fst (getCTE p s) = (s = s' \<and> cte_wp_at' ((=) rv) p s)"
  apply (rule iffI)
   apply (clarsimp dest!: in_getCTE simp: cte_wp_at'_def)
  apply (clarsimp simp: cte_wp_at'_def getCTE_def)
  done

lemma state_relation_cap_relation:
  "\<lbrakk> (s, s') \<in> state_relation; cte_wp_at ((=) cap) p s;
     cte_wp_at' ((=) cte) (cte_map p) s';
     valid_objs s; pspace_distinct' s'; pspace_aligned' s' \<rbrakk>
     \<Longrightarrow> cap_relation cap (cteCap cte)"
  apply (cases p, clarsimp simp: state_relation_def)
  apply (drule(3) pspace_relation_cte_wp_at)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  done

lemma descendants_of_empty_state_relation:
  "\<lbrakk> (s, s') \<in> state_relation; cte_at p s \<rbrakk> \<Longrightarrow>
    (descendants_of p (cdt s) = {}) = (descendants_of' (cte_map p) (ctes_of s') = {})"
  apply (clarsimp simp only: state_relation_def cdt_relation_def swp_def)
  apply (drule spec, drule(1) mp)
  apply (fastforce)
  done

lemma subtree_first_step:
  "\<lbrakk> ctes_of s p = Some cte; ctes_of s \<turnstile> p \<rightarrow> p' \<rbrakk>
     \<Longrightarrow> mdbNext (cteMDBNode cte) \<noteq> nullPointer \<and>
         (\<exists>cte'. ctes_of s (mdbNext (cteMDBNode cte)) = Some cte'
                 \<and> isMDBParentOf cte cte')"
  apply (erule subtree.induct)
   apply (clarsimp simp: mdb_next_unfold nullPointer_def parentOf_def)
  apply clarsimp
  done

lemma cap_revoke_mdb_stuff1:
  "\<lbrakk> (s, s') \<in> state_relation; cte_wp_at ((=) cap) p s;
     cte_wp_at' ((=) cte) (cte_map p) s'; invs s; invs' s';
     cap \<noteq> cap.NullCap; cteCap cte \<noteq> NullCap \<rbrakk>
     \<Longrightarrow> (descendants_of p (cdt s) = {})
          = (\<not> (mdbNext (cteMDBNode cte) \<noteq> nullPointer
             \<and> cte_wp_at' (isMDBParentOf cte) (mdbNext (cteMDBNode cte)) s'))"
  apply (subst descendants_of_empty_state_relation)
    apply assumption
   apply (clarsimp elim!: cte_wp_at_weakenE)
  apply (simp add: descendants_of'_def)
  apply safe
    apply (drule spec[where x="mdbNext (cteMDBNode cte)"])
    apply (erule notE, rule subtree.direct_parent)
      apply (clarsimp simp: mdb_next_unfold cte_wp_at_ctes_of)
     apply (simp add: nullPointer_def)
    apply (clarsimp simp: parentOf_def cte_wp_at_ctes_of)
   apply (clarsimp simp: cte_wp_at_ctes_of)
   apply (drule(1) subtree_first_step)
   apply clarsimp
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (drule(1) subtree_first_step)
  apply clarsimp
  done

lemma select_bind_spec_corres':
  "\<lbrakk>P sa \<Longrightarrow> x \<in> S; spec_corres sa r P P' (f x) g\<rbrakk>
\<Longrightarrow> spec_corres sa r P P' (select S >>= f) g"
   apply (clarsimp simp add: spec_corres_def
                         corres_underlying_def bind_def
                         select_def
         | drule(1) bspec | erule rev_bexI | rule conjI)+
   done

lemma cap_revoke_mdb_stuff4:
  "\<lbrakk> (s, s') \<in> state_relation; cte_wp_at ((=) cap) p s;
     cte_wp_at' ((=) cte) (cte_map p) s'; invs s; valid_list s; invs' s';
     cap \<noteq> cap.NullCap; cteCap cte \<noteq> NullCap;
     descendants_of p (cdt s) \<noteq> {} \<rbrakk>
     \<Longrightarrow> \<exists>p'. mdbNext (cteMDBNode cte) = cte_map p'
         \<and> next_child p (cdt_list s) = Some p'"
  apply(subgoal_tac "descendants_of p (cdt s) \<noteq> {}")
   prefer 2
   apply simp
  apply (subst(asm) cap_revoke_mdb_stuff1)
         apply assumption+
  apply (clarsimp simp: cte_wp_at_ctes_of state_relation_def)
  apply (drule(1) pspace_relation_cte_wp_atI[where x="mdbNext c" for c])
   apply clarsimp
  apply clarsimp
  apply (intro exI, rule conjI [OF refl])
  apply(simp add: cdt_list_relation_def)
  apply(erule_tac x="fst p" in allE, erule_tac x="snd p" in allE)
  apply(case_tac "cte", simp)
  apply(case_tac "next_slot p (cdt_list s) (cdt s)")
   apply(simp add: next_slot_def empty_list_empty_desc next_child_None_empty_desc)
  apply(frule cte_at_next_slot')
     apply(erule invs_mdb)
    apply(simp add: invs_def valid_state_def finite_depth)
   apply(assumption)
  apply(simp add: next_slot_def empty_list_empty_desc)
  apply(frule invs_valid_pspace, simp add: valid_pspace_def)
  apply(rule cte_map_inj_eq)
       apply(simp add: cte_wp_at_def)+
       done

lemma cteRevoke_corres':
  "spec_corres s (dc \<oplus> dc)
      (einvs and simple_sched_action and cte_at ptr)
      (invs' and sch_act_simple and cte_at' (cte_map ptr))
      (cap_revoke ptr) (\<lambda>s. cteRevoke (cte_map ptr) s)"
proof (induct rule: cap_revoke.induct)
  case (1 slot s')
  show ?case
    apply (subst cap_revoke.simps)
    apply (subst cteRevoke.simps[abs_def])
    apply (simp add: liftE_bindE next_revoke_cap_def select_ext_def bind_assoc)
    apply (rule spec_corres_symb_exec_l_Ex2)
     apply (clarsimp simp: cte_wp_at_def)
    apply (rule spec_corres_symb_exec_l_Ex2)
     apply (simp add: in_monad)
    apply (rule spec_corres_symb_exec_r_Ex)
       apply (clarsimp elim!: use_valid [OF _ getCTE_inv])
      apply (clarsimp simp: cte_at'_def getCTE_def)
     apply (rule no_fail_pre, wp)
     apply clarsimp
    apply (simp add: in_monad in_get_cap_cte_wp_at
                              in_getCTE_cte_wp_at')
    apply (rule_tac F="cap_relation cap (cteCap cte)"
              in spec_corres_req)
     apply (clarsimp | erule(2) state_relation_cap_relation)+
    apply (case_tac "cap = cap.NullCap")
     apply (simp add: whenE_def)
    apply (case_tac "cteCap cte = NullCap")
     apply (simp add: whenE_def)
    apply (case_tac "descendants_of slot (cdt s') = {}")
     apply (case_tac "mdbNext (cteMDBNode cte) = nullPointer")
      apply (simp add: whenE_def)
     apply (simp add: whenE_def[where P=True])
     apply (rule spec_corres_symb_exec_r_Ex)
        apply (clarsimp elim!: use_valid [OF _ getCTE_inv])
       apply clarsimp
       apply (subgoal_tac "cte_at' (mdbNext (cteMDBNode cte)) s")
        apply (clarsimp simp: getCTE_def cte_at'_def)
       apply (drule invs_mdb')
       apply (clarsimp simp: cte_wp_at_ctes_of valid_mdb'_def valid_mdb_ctes_def nullPointer_def)
       apply (erule (2) valid_dlistEn)
       apply simp
      apply (rule no_fail_pre, wp)
      apply clarsimp
      apply (drule invs_mdb')
      apply (clarsimp simp: cte_wp_at_ctes_of valid_mdb'_def valid_mdb_ctes_def nullPointer_def)
      apply (erule (2) valid_dlistEn)
      apply simp
     apply (rule_tac F="\<not> isMDBParentOf cte nextCTE"
               in spec_corres_req)
      apply (clarsimp simp: in_getCTE_cte_wp_at')
      apply (subst(asm) cap_revoke_mdb_stuff1, assumption+)
      apply (clarsimp simp: cte_wp_at'_def)
     apply (simp add: whenE_def)
    apply (rule_tac F="mdbNext (cteMDBNode cte) \<noteq> nullPointer"
              in spec_corres_req)
     apply clarsimp
     apply (subst(asm) cap_revoke_mdb_stuff1, assumption+)
     apply (clarsimp simp: cte_wp_at'_def)
    apply (simp add: whenE_def[where P=True])
    apply (rule spec_corres_symb_exec_r_Ex)
       apply (clarsimp elim!: use_valid [OF _ getCTE_inv])
      apply (subgoal_tac "cte_at' (mdbNext (cteMDBNode cte)) s")
       apply (clarsimp simp: getCTE_def cte_at'_def)
      apply clarsimp
      apply (drule invs_mdb')
      apply (clarsimp simp: cte_wp_at_ctes_of valid_mdb'_def valid_mdb_ctes_def nullPointer_def)
      apply (erule (2) valid_dlistEn)
      apply simp
     apply (rule no_fail_pre, wp)
     apply clarsimp
     apply (drule invs_mdb')
     apply (clarsimp simp: cte_wp_at_ctes_of valid_mdb'_def valid_mdb_ctes_def nullPointer_def)
     apply (erule (2) valid_dlistEn)
     apply simp
    apply (simp add: in_monad in_get_cap_cte_wp_at
                              in_getCTE_cte_wp_at')
    apply(case_tac "next_child slot (cdt_list s')")
     apply(rule_tac F="False" in spec_corres_req)
      apply(clarsimp)
      apply(frule next_child_NoneD)
      apply(simp add: empty_list_empty_desc)
     apply(simp)
    apply (rule_tac F="valid_list s'" in spec_corres_req,simp)
    apply (frule next_child_child_set, assumption)
    apply simp
    apply (rule spec_corres_symb_exec_l_Ex2)
     apply (simp add: in_monad)
    apply (rule spec_corres_symb_exec_l_Ex2)
     apply (simp add: in_monad)
     apply (drule next_childD, simp)
     apply (simp add: child_descendant)
    apply (rule spec_corres_symb_exec_l_Ex2)
     apply (clarsimp simp: in_monad)
     apply (drule next_childD, simp)
     apply (clarsimp)
     apply (drule child_descendant)
     apply (drule descendants_of_cte_at, erule invs_mdb)
     apply (clarsimp simp: cte_wp_at_def)
    apply (simp add: in_monad)
    apply(case_tac "capa = cap.NullCap")
     apply(rule_tac F="False" in spec_corres_req)
      apply(clarsimp)
      apply(drule next_childD, simp)
      apply(clarsimp)
      apply(drule child_descendant)
      apply(drule cap_revoke_mdb_stuff3)
       apply(erule invs_mdb)
      apply(clarsimp simp: cte_wp_at_def)
     apply(simp)
    apply (simp)
    apply (rule_tac F="isMDBParentOf cte nextCTE"
             in spec_corres_req)
     apply clarsimp
     apply(frule cap_revoke_mdb_stuff1, (simp add: in_get_cap_cte_wp_at)+)
     apply (clarsimp simp: cte_wp_at'_def)

    apply (rule spec_corres_req)
     apply clarsimp
     apply (rule cap_revoke_mdb_stuff4, (simp add: in_get_cap_cte_wp_at)+)
    apply (clarsimp simp: whenE_def)
    apply (rule spec_corres_guard_imp)
      apply (rule spec_corres_splitE' [OF cteDelete_corres])
        apply (rule spec_corres_splitE' [OF preemptionPoint_corres])
          apply (rule "1.hyps",
                   (simp add: cte_wp_at_def in_monad select_def next_revoke_cap_def select_ext_def
                     | assumption | rule conjI refl)+)[1]
         apply (wp cap_delete_cte_at cteDelete_invs' cteDelete_sch_act_simple
                   preemptionPoint_invR preemption_point_inv' | clarsimp)+
     apply (clarsimp simp: cte_wp_at_cte_at)
     apply(drule next_childD, simp)
     apply(clarsimp, drule child_descendant)
     apply (fastforce simp: emptyable_def dest: reply_slot_not_descendant)
    apply (clarsimp elim!: cte_wp_at_weakenE')
    done
qed

lemmas cteRevoke_corres = use_spec_corres [OF cteRevoke_corres']

crunch invokeCNode
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  (ignore: finaliseSlot
     simp: crunch_simps filterM_mapM unless_def
           arch_recycleCap_improve_cases
       wp: crunch_wps undefined_valid finaliseSlot_preservation)

lemmas invokeCNode_typ_ats [wp] = typ_at_lifts [OF invokeCNode_typ_at']

crunch cteMove
  for st_tcb_at'[wp]: "st_tcb_at' P t"
  (wp: crunch_wps)

lemma threadSet_st_tcb_at2:
  assumes x: "\<forall>tcb. P (tcbState tcb) \<longrightarrow> P (tcbState (f tcb))"
  shows      "\<lbrace>st_tcb_at' P t\<rbrace> threadSet f t' \<lbrace>\<lambda>rv. st_tcb_at' P t\<rbrace>"
  including no_pre
  apply (simp add: threadSet_def pred_tcb_at'_def)
  apply (wp setObject_tcb_strongest)
  apply (rule hoare_strengthen_post, rule getObject_tcb_sp)
  apply (clarsimp simp: obj_at'_def x)
  done

crunch "cancelBadgedSends"
  for st_tcb_at_simplish[wp]: "st_tcb_at' (\<lambda>st. P st \<or> simple' st) t"
  (wp: crunch_wps threadSet_st_tcb_at2
   simp: crunch_simps filterM_mapM makeObject_tcb unless_def)

lemma cancelBadgedSends_st_tcb_at':
  assumes x: "\<And>st. simple' st \<Longrightarrow> P st"
  shows      "\<lbrace>st_tcb_at' P t\<rbrace> cancelBadgedSends a b \<lbrace>\<lambda>_. st_tcb_at' P t\<rbrace>"
  apply (rule hoare_chain)
    apply (rule cancelBadgedSends_st_tcb_at_simplish[where P=P and t=t])
   apply (auto simp: x elim!: pred_tcb'_weakenE)
  done

lemmas cteRevoke_st_tcb_at'
    = cteRevoke_preservation [OF cteDelete_st_tcb_at']
lemmas cteRevoke_st_tcb_at_simplish
    = cteRevoke_st_tcb_at'[where P="\<lambda>st. Q st \<or> simple' st",
                           simplified] for Q

lemmas finaliseSlot_st_tcb_at'
    = finaliseSlot_preservation [OF finaliseCap2_st_tcb_at'
                                    emptySlot_pred_tcb_at'
                                    capSwapForDelete_st_tcb_at'
                                    updateCap_pred_tcb_at']
lemmas finaliseSlot_st_tcb_at_simplish
    = finaliseSlot_st_tcb_at'[where P="\<lambda>st. Q st \<or> simple' st",
                              simplified] for Q

lemma updateCap_valid_objs [wp]:
  "\<lbrace>\<lambda>s. valid_objs' s \<and> s \<turnstile>' cap\<rbrace>
  updateCap ptr cap
  \<lbrace>\<lambda>r. valid_objs'\<rbrace>"
  unfolding updateCap_def
    apply (wp setCTE_valid_objs getCTE_wp)
  apply clarsimp
  apply (erule cte_at_cte_wp_atD)
  done

end

lemma (in mdb_move) [intro!]:
  shows "mdb_chain_0 m" using valid
  by (auto simp: valid_mdb_ctes_def)

lemma (in mdb_move) m'_badged:
  "m' p = Some (CTE cap node)
  \<Longrightarrow> if p = dest then mdbFirstBadged node = mdbFirstBadged src_node \<and> cap = cap'
     else if p = src then \<not> mdbFirstBadged node \<and> cap = NullCap
     else \<exists>node'. m p = Some (CTE cap node') \<and> mdbFirstBadged node = mdbFirstBadged node'"
  using src dest neq
  apply (clarsimp simp: m'_def n_def modify_map_cases nullMDBNode_def)
  apply (rule conjI, clarsimp)
  apply clarsimp
  apply auto
  done

lemma (in mdb_move) m'_next:
  "m' \<turnstile> p \<leadsto> p' \<Longrightarrow>
  if p = src then p' = 0
  else if p = dest then m \<turnstile> src \<leadsto> p'
  else if p' = dest then m \<turnstile> p \<leadsto> src
  else m \<turnstile> p \<leadsto> p'"
  using src dest src_0 dest_0 dlist neq src_neq_prev
  apply (simp add: m'_def n_def)
  apply (simp add: mdb_next_unfold)
  apply (elim exE conjE)
  apply (case_tac z)
  apply (rename_tac cap node)
  apply simp
  apply (simp add: modify_map_cases)
  apply (cases "mdbPrev src_node = p")
   apply clarsimp
   apply (erule_tac p=src in valid_dlistEp, assumption)
    apply clarsimp
   apply clarsimp
  apply simp
  apply (cases "p=src", simp)
  apply clarsimp
  apply (case_tac "mdbNext node = p")
   apply clarsimp
  apply clarsimp
  apply (erule_tac p=p in valid_dlistEn, assumption)
   apply clarsimp
  apply (clarsimp simp: prev)
  done

lemma (in mdb_move) sameRegionAs_parent_eq:
  "sameRegionAs cap cap' = sameRegionAs cap src_cap"
  using parency unfolding weak_derived'_def
  by (simp add: ARM_HYP.sameRegionAs_def2) (* FIXME arch-split *)

lemma (in mdb_move) m'_cap:
  "m' p = Some (CTE c node) \<Longrightarrow>
  if p = src then c = NullCap
  else if p = dest then c = cap'
  else \<exists>node'. m p = Some (CTE c node')"
  using src dest neq
  apply (simp add: m'_def n_def)
  apply (auto simp add: modify_map_if split: if_split_asm)
  done

context mdb_move
begin

interpretation Arch . (*FIXME: arch-split*)

lemma m_to_src:
  "m \<turnstile> p \<leadsto> src = (p \<noteq> 0 \<and> p = mdbPrev src_node)"
  apply (insert src)
  apply (rule iffI)
   apply (clarsimp simp add: mdb_next_unfold)
   apply (rule conjI, clarsimp)
   apply (case_tac z)
   apply clarsimp
   apply (erule_tac p=p in dlistEn, clarsimp)
   apply clarsimp
  apply (clarsimp simp add: mdb_next_unfold)
  apply (erule dlistEp, clarsimp)
  apply clarsimp
  done

lemma m_from_prev_src:
  "m \<turnstile> mdbPrev src_node \<leadsto> p = (mdbPrev src_node \<noteq> 0 \<and> p = src)"
  apply (insert src)
  apply (rule iffI)
   apply (clarsimp simp: mdb_next_unfold)
   apply (rule conjI, clarsimp)
   apply (erule dlistEp, clarsimp)
   apply clarsimp
  apply (clarsimp simp: mdb_next_unfold)
  apply (erule dlistEp, clarsimp)
  apply clarsimp
  done

lemma m'_nextD:
  "m' \<turnstile> p \<leadsto> p' \<Longrightarrow>
  (if p = src then p' = 0
  else if p = dest then m \<turnstile> src \<leadsto> p'
  else if p = mdbPrev src_node then p' = dest \<and> p \<noteq> 0
  else m \<turnstile> p \<leadsto> p')"
  using src dest src_0 dest_0 dlist neq src_neq_prev
  apply (simp add: m'_def n_def)
  apply (simp add: mdb_next_unfold)
  apply (elim exE conjE)
  apply (case_tac z)
  apply simp
  apply (simp add: modify_map_cases)
  apply (cases "mdbPrev src_node = p")
   apply clarsimp
  apply simp
  apply (cases "p=src", simp)
  apply clarsimp
  done


lemmas prev_src = prev_p_next

lemma m'_next_eq:
  notes if_cong [cong]
  shows
  "m' \<turnstile> p \<leadsto> p' =
  (if p = src then p' = 0
  else if p = dest then m \<turnstile> src \<leadsto> p'
  else if p = mdbPrev src_node then p' = dest \<and> p \<noteq> 0
  else m \<turnstile> p \<leadsto> p')"
  apply (insert src dest)
  apply (rule iffI)
   apply (drule m'_nextD, simp)
  apply (cases "p=0")
   apply (clarsimp simp: mdb_next_unfold split: if_split_asm)
  apply (simp split: if_split_asm)
     apply (simp add: mdb_next_unfold m'_def n_def modify_map_cases)
    apply (simp add: mdb_next_unfold m'_def n_def modify_map_cases neq)
   apply (simp add: mdb_next_unfold m'_def n_def modify_map_cases neq)
   apply clarsimp
   apply (drule prev_src)
   apply (clarsimp simp: mdb_next_unfold)
   apply (case_tac z)
   apply clarsimp
  apply (clarsimp simp: mdb_next_unfold m'_def n_def modify_map_cases)
  apply (cases "mdbNext src_node = p")
   apply (clarsimp)
   apply (case_tac z)
   apply clarsimp
  apply clarsimp
  done

declare dest_0 [simp]

lemma m'_swp_eq:
  "m' \<turnstile> p \<leadsto> p' = m \<turnstile> s_d_swap p src dest \<leadsto> s_d_swap p' src dest"
  by (auto simp add: m'_next_eq s_d_swap_def m_to_src m_from_prev_src)

lemma m'_tranclD:
  "m' \<turnstile> p \<leadsto>\<^sup>+ p' \<Longrightarrow> m \<turnstile> s_d_swap p src dest \<leadsto>\<^sup>+ s_d_swap p' src dest"
  apply (erule trancl.induct)
   apply (fastforce simp: m'_swp_eq)
  apply (fastforce simp: m'_swp_eq intro: trancl_trans)
  done

lemma m_tranclD:
  "m \<turnstile> p \<leadsto>\<^sup>+ p' \<Longrightarrow> m' \<turnstile> s_d_swap p src dest \<leadsto>\<^sup>+ s_d_swap p' src dest"
  apply (erule trancl.induct)
   apply (fastforce simp: m'_swp_eq)
  apply (fastforce simp: m'_swp_eq intro: trancl_trans)
  done

lemma m'_trancl_eq:
  "m' \<turnstile> p \<leadsto>\<^sup>+ p' = m \<turnstile> s_d_swap p src dest \<leadsto>\<^sup>+ s_d_swap p' src dest"
  by (auto dest: m_tranclD m'_tranclD)

lemma m'_rtrancl_eq:
  "m' \<turnstile> p \<leadsto>\<^sup>* p' = m \<turnstile> s_d_swap p src dest \<leadsto>\<^sup>* s_d_swap p' src dest"
  by (auto simp: rtrancl_eq_or_trancl m'_trancl_eq s_d_swap_def)

lemma m_cap:
  "m p = Some (CTE c node) \<Longrightarrow>
  if p = src then \<exists>node'. c = src_cap \<and> m' dest = Some (CTE cap' node')
  else if p = dest then \<exists>node'. c = NullCap  \<and> m' src = Some (CTE NullCap node')
  else \<exists>node'. m' p = Some (CTE c node')"
  apply (auto simp: src dest)
  apply (auto simp: m'_def n_def src dest modify_map_if neq)
  done

lemma sameRegion_cap'_src [simp]:
  "sameRegionAs cap' c = sameRegionAs src_cap c"
  using parency unfolding weak_derived'_def
  apply (case_tac "isReplyCap src_cap"; clarsimp)
   apply (clarsimp simp: capMasterCap_def arch_capMasterCap_def
                   split: capability.splits arch_capability.splits;
          fastforce simp: sameRegionAs_def ARM_HYP_H.sameRegionAs_def isCap_simps
                    split: if_split_asm)+ (* FIXME arch-split *)
  done

lemma mdb_chunked_arch_assms_src[simp]:
  "mdb_chunked_arch_assms cap' = mdb_chunked_arch_assms src_cap"
  by (simp add: mdb_chunked_arch_assms_def)

lemma chunked':
  "mdb_chunked m'"
  using chunked
  apply (clarsimp simp: mdb_chunked_def)
  apply (drule m'_cap)+
  apply (clarsimp simp: m'_trancl_eq sameRegion_cap'_src split: if_split_asm)
    apply (erule_tac x=src in allE)
    apply (erule_tac x="s_d_swap p' src dest" in allE)
    apply (clarsimp simp: src s_d_swap_other)
    apply (rule conjI)
     apply (clarsimp simp: is_chunk_def m'_rtrancl_eq m'_trancl_eq s_d_swap_other)
     apply (erule_tac x="s_d_swap p'' src dest" in allE)
     apply clarsimp
     apply (drule_tac p="s_d_swap p'' src dest" in m_cap)
     apply (clarsimp simp: s_d_swap_def split: if_split_asm)
    apply (clarsimp simp: is_chunk_def m'_rtrancl_eq m'_trancl_eq s_d_swap_other)
    apply (erule_tac x="s_d_swap p'' src dest" in allE)
    apply clarsimp
    apply (drule_tac p="s_d_swap p'' src dest" in m_cap)
    apply (clarsimp simp: s_d_swap_def sameRegionAs_parent_eq split: if_split_asm)
   apply (simp add: s_d_swap_other)
   apply (erule_tac x=p in allE)
   apply (erule_tac x=src in allE)
   apply (clarsimp simp: src sameRegionAs_parent_eq)
   apply (rule conjI)
    apply (clarsimp simp: is_chunk_def m'_rtrancl_eq m'_trancl_eq s_d_swap_other)
    apply (erule_tac x="s_d_swap p'' src dest" in allE)
    apply clarsimp
    apply (drule_tac p="s_d_swap p'' src dest" in m_cap)
    apply (clarsimp simp: s_d_swap_def sameRegionAs_parent_eq split: if_split_asm)
   apply (clarsimp simp: is_chunk_def m'_rtrancl_eq m'_trancl_eq s_d_swap_other)
   apply (erule_tac x="s_d_swap p'' src dest" in allE)
   apply clarsimp
   apply (drule_tac p="s_d_swap p'' src dest" in m_cap)
   apply (clarsimp simp: s_d_swap_def sameRegionAs_parent_eq split: if_split_asm)
  apply (simp add: s_d_swap_other)
  apply (erule_tac x=p in allE)
  apply (erule_tac x=p' in allE)
  apply clarsimp
  apply (rule conjI)
   apply (clarsimp simp: is_chunk_def m'_rtrancl_eq m'_trancl_eq s_d_swap_other)
   apply (erule_tac x="s_d_swap p'' src dest" in allE)
   apply clarsimp
   apply (drule_tac p="s_d_swap p'' src dest" in m_cap)
   apply (clarsimp simp: s_d_swap_def sameRegionAs_parent_eq split: if_split_asm)
  apply (clarsimp simp: is_chunk_def m'_rtrancl_eq m'_trancl_eq s_d_swap_other)
  apply (erule_tac x="s_d_swap p'' src dest" in allE)
  apply clarsimp
  apply (drule_tac p="s_d_swap p'' src dest" in m_cap)
  apply (clarsimp simp: s_d_swap_def sameRegionAs_parent_eq split: if_split_asm)
  done

lemma isUntypedCap':
  "isUntypedCap cap' = isUntypedCap src_cap"
  using parency unfolding weak_derived'_def
  by (clarsimp simp: weak_derived'_def dest!: capMaster_isUntyped)

lemma capRange':
  "capRange cap' = capRange src_cap"
  using parency unfolding weak_derived'_def
  by (clarsimp simp: weak_derived'_def dest!: capMaster_capRange)

lemma untypedRange':
  "untypedRange cap' = untypedRange src_cap"
  using parency unfolding weak_derived'_def
  by (clarsimp simp: weak_derived'_def dest!: capMaster_untypedRange)

lemmas ut' = isUntypedCap' capRange' untypedRange'

lemma m'_revocable:
  "m' p = Some (CTE c node) \<Longrightarrow>
  if p = src then \<not>mdbRevocable node
  else if p = dest then mdbRevocable node = mdbRevocable src_node
  else \<exists>node'. m p = Some (CTE c node') \<and> mdbRevocable node = mdbRevocable node'"
  apply (insert src dest neq)
  apply (frule m'_cap)
  apply (clarsimp simp: m'_def n_def modify_map_if nullMDBNode_def split: if_split_asm)
  done

lemma isIRQHandlerCap_cap'[simp]:
  "isIRQHandlerCap cap' = isIRQHandlerCap src_cap"
  using parency unfolding weak_derived'_def
  by (auto simp: weak_derived'_def isCap_simps)

lemma cteMove_valid_mdb_helper:
  "(isUntypedCap cap' \<Longrightarrow> cap' = src_cap) \<Longrightarrow>valid_mdb_ctes m'"
proof
  note sameRegion_cap'_src [simp del]
  note dest_0 [simp del] src_0 [simp del]
  note src_next [simp del]
  note rtrancl0 [simp del]

  show "valid_dlist m'" by (rule dlist')
  show "no_0 m'" by (rule no_0')

  have chain: "mdb_chain_0 m" ..

  have mp: "cte_mdb_prop m dest (\<lambda>m. mdbPrev m = nullPointer \<and> mdbNext m = nullPointer)" using dest prev nxt
    unfolding cte_mdb_prop_def
    by (simp add: nullPointer_def)
  hence nsd: "\<not> m \<turnstile> mdbNext src_node \<leadsto>\<^sup>* dest" using dlist
    by (auto elim: next_rtrancl_tranclE dest: null_mdb_no_trancl [OF _ no_0])

  have sd: "mdbNext src_node \<noteq> 0 \<Longrightarrow> mdbNext src_node \<in> dom m"
  proof -
    assume T: "mdbNext src_node \<noteq> 0"
    have "m \<turnstile> src \<leadsto> mdbNext src_node" by (rule m_p_next)
    moreover have "m \<turnstile> src \<leadsto>\<^sup>+ 0" using chain src unfolding mdb_chain_0_def by (clarsimp simp: dom_def)
    ultimately have "m \<turnstile> mdbNext src_node \<leadsto>\<^sup>+ 0" using T
      by (auto elim: tranclE2' simp: next_unfold')
    thus "mdbNext src_node \<in> dom m"
      by - (erule tranclE2', (clarsimp simp: next_unfold')+)
  qed

  let ?m = "(modify_map
       (modify_map (modify_map m (mdbPrev src_node) (cteMDBNode_update (mdbNext_update (%_. dest)))) src
         (cteMDBNode_update (mdbNext_update (%_. (mdbNext nullMDBNode)))))
       dest (cteMDBNode_update (mdbNext_update (%_. (mdbNext src_node)))))"

  let ?goal =  "mdb_chain_0 ?m"
  {
    assume "mdbPrev src_node = 0" and T: "mdbNext src_node = 0"
    hence ms: "m (mdbPrev src_node) = None" using no_0 by (simp add: no_0_def)
    hence ?goal using T
      by (auto simp: modify_map_None [where m = m, OF ms] nullPointer_def
               intro!: mdb_chain_0_modify_map_0)
  } moreover
  {
    assume "mdbPrev src_node \<noteq> 0" and "mdbNext src_node = 0"
    hence ?goal
      apply -
      apply (simp add: nullMDBNode_def nullPointer_def)
      apply (subst modify_map_addr_com [where y = dest], simp add: neq)+
      apply (rule mdb_chain_0_modify_map_0)
       apply (rule mdb_chain_0_modify_map_next)
          apply (rule mdb_chain_0_modify_map_0 [OF chain no_0])
         apply clarsimp
        apply (clarsimp simp: dest)
       apply (subst next_update_is_modify [symmetric], rule dest)
        apply simp
       apply (subst next_update_lhs_rtrancl)
        apply simp
        apply (rule no_0_lhs_tranclI [OF no_0 dest_0])
       apply simp
       apply (rule no_0_lhs_tranclI [OF no_0])
       apply simp
      apply clarsimp
      done
  } moreover
  {
    assume "mdbPrev src_node = 0" and T: "mdbNext src_node \<noteq> 0"
    hence ms: "m (mdbPrev src_node) = None" using no_0 by (simp add: no_0_def)
    hence ?goal using T
      apply (simp add: modify_map_None nullPointer_def)
      apply (subst modify_map_addr_com [OF neq])
      apply (rule mdb_chain_0_modify_map_0)
       apply (rule mdb_chain_0_modify_map_next [OF chain no_0 sd, OF T nsd])
      apply clarsimp
      done
  } moreover
  {
    assume U: "mdbPrev src_node \<noteq> 0" and T: "mdbNext src_node \<noteq> 0"
    hence ?goal using dlist
      apply -
      apply (simp add: nullPointer_def)
      apply (subst modify_map_addr_com [where y = dest], simp add: neq)+
      apply (rule mdb_chain_0_modify_map_0)
      apply (rule mdb_chain_0_modify_map_next)
      apply (rule mdb_chain_0_modify_map_next [OF chain no_0 sd nsd, OF T])
         apply clarsimp
         apply (clarsimp simp: dest)
       apply (subst next_update_is_modify [symmetric], rule dest)
       apply simp
       apply (subst next_update_lhs_rtrancl)
       apply simp
       apply (rule nsd)
       apply simp
       apply (rule no_next_prev_rtrancl [OF valid], rule src, rule U)
       apply clarsimp
       done
   }
   ultimately have ?goal
     apply (cases "mdbPrev src_node = 0")
     apply (cases "mdbNext src_node = 0")
     apply auto[2]
     apply (cases "mdbNext src_node = 0")
     apply auto
     done

  thus "mdb_chain_0 m'"
    unfolding m'_def n_def
    apply -
    apply (rule mdb_chain_0_modify_map_prev)
    apply (subst modify_map_addr_com [OF src_neq_prev])
    apply (subst modify_map_addr_com [OF prev_neq_dest2])
     apply (rule mdb_chain_0_modify_map_replace)
    apply (subst modify_map_addr_com [OF neq_sym])+
     apply (rule mdb_chain_0_modify_map_replace)
    apply (subst modify_map_com [ where g = "(cteCap_update (%_. cap'))"],
      case_tac x, simp)+
    apply (rule mdb_chain_0_modify_map_inv)
    apply (subst modify_map_com [ where g = "(cteCap_update (%_. capability.NullCap))"],
      case_tac x, simp)+
    apply (erule mdb_chain_0_modify_map_inv)
    apply simp
    apply simp
    done

  from parency
  have SGI_src_cap: "isArchSGISignalCap src_cap \<Longrightarrow> cap' = src_cap"
    unfolding weak_derived'_def
    by (clarsimp simp: isCap_simps)

  from valid
  have "valid_badges m" ..
  thus "valid_badges m'" using src dest parency
    apply (clarsimp simp: valid_badges_def2 valid_arch_badges_def)
    apply (drule m'_badged)+
    apply (drule m'_next)
    apply (clarsimp simp add: weak_derived'_def split: if_split_asm)
       apply (erule_tac x=src in allE, erule_tac x=p' in allE,
              erule allE, erule impE, erule exI)
       apply (clarsimp simp: SGI_src_cap)
      apply (erule_tac x=p in allE, erule_tac x=src in allE,
             erule allE, erule impE, erule exI)
      apply clarsimp
     apply (clarsimp simp: isCap_simps)
    apply blast
    done

  from valid
  have "caps_contained' m" by (simp add: valid_mdb_ctes_def)
  with src dest neq parency
  show "caps_contained' m'"
    apply (clarsimp simp: caps_contained'_def)
    apply (drule m'_cap)+
    apply (clarsimp split: if_split_asm)
       apply (clarsimp dest!: capRange_untyped)
      apply (erule_tac x=src in allE, erule_tac x=p' in allE)
      apply (clarsimp simp add: weak_derived'_def)
      apply (drule capMaster_untypedRange)
      apply clarsimp
      apply blast
     apply (erule_tac x=p in allE, erule_tac x=src in allE)
     apply (clarsimp simp: weak_derived'_def)
     apply (frule capMaster_isUntyped)
     apply (drule capMaster_capRange)
     apply clarsimp
     apply blast
    by fastforce

  show "mdb_chunked m'" by (rule chunked')

  from untyped_mdb
  show "untyped_mdb' m'"
    apply (simp add: untyped_mdb'_def)
    apply clarsimp
    apply (drule m'_cap)+
    apply (clarsimp simp: descendants split: if_split_asm)
     apply (erule_tac x=src in allE)
     apply (erule_tac x=p' in allE)
     apply (simp add: src ut')
    apply (erule_tac x=p in allE)
    apply (erule_tac x=src in allE)
    apply (simp add: src ut')
    done

  assume isUntypedCap_eq:"isUntypedCap cap' \<Longrightarrow> cap' = src_cap"
  from untyped_inc
  show "untyped_inc' m'"
    using isUntypedCap_eq
    apply (simp add: untyped_inc'_def)
    apply clarsimp
    apply (drule m'_cap)+
    apply (clarsimp simp: descendants split: if_split_asm)
      apply (erule_tac x=src in allE)
      apply (erule_tac x=p' in allE)
      apply (clarsimp simp add: src ut')
      apply (intro conjI impI)
       apply clarsimp+
     apply (erule_tac x=p in allE)
     apply (erule_tac x=src in allE)
     apply (clarsimp simp add: src ut')
     apply (intro conjI impI)
      apply clarsimp+
    apply (erule_tac x=p in allE)
    apply (erule_tac x=p' in allE)
    apply clarsimp
    done

  note if_cong [cong]

  from not_null parency
  have "src_cap \<noteq> NullCap \<and> cap' \<noteq> NullCap"
    by (clarsimp simp: weak_derived'_def)
  moreover
  from valid
  have "valid_nullcaps m" ..
  ultimately
  show vn': "valid_nullcaps m'"
    apply (clarsimp simp: valid_nullcaps_def)
    apply (frule m'_cap)
    apply (insert src dest)
    apply (frule spec, erule allE, erule (1) impE)
    apply (clarsimp split: if_split_asm)
     apply (simp add: n_def m'_def)
     apply (simp add: modify_map_if)
    apply (simp add: n_def m'_def)
    apply (simp add: modify_map_if)
    apply (clarsimp split: if_split_asm)
     apply (erule disjE)
      apply clarsimp
     apply (erule allE, erule allE, erule (1) impE)
     apply clarsimp
     apply (insert dlist)
     apply (erule_tac p=src in valid_dlistEn, assumption)
      apply clarsimp
     apply (clarsimp simp: nullMDBNode_def nullPointer_def)
    apply (erule allE, erule allE, erule (1) impE)
    apply clarsimp
    apply (erule_tac p=src in valid_dlistEp, assumption)
     apply clarsimp
    apply (clarsimp simp: nullMDBNode_def nullPointer_def)
    done

  from valid
  have "ut_revocable' m" ..
  thus "ut_revocable' m'" using src dest parency
    apply (clarsimp simp: ut_revocable'_def)
    apply (frule m'_cap)
    apply (frule m'_revocable)
    apply (clarsimp split: if_split_asm)
    apply (subgoal_tac "isUntypedCap src_cap")
     apply simp
    apply (clarsimp simp: weak_derived'_def dest!: capMaster_isUntyped)
    done

  from src
  have src': "m' src = Some (CTE NullCap nullMDBNode)"
    by (simp add: m'_def n_def modify_map_if)
  with dlist' no_0'
  have no_prev_of_src': "\<And>p. \<not>m' \<turnstile> p \<leadsto> src"
    apply clarsimp
    apply (frule (3) vdlist_nextD)
    apply (simp add: mdb_prev_def mdb_next_unfold nullPointer_def)
    done

  from valid
  have "class_links m" ..
  thus "class_links m'" using src dest parency
    apply (clarsimp simp: class_links_def weak_derived'_def)
    apply (case_tac cte)
    apply (case_tac cte')
    apply clarsimp
    apply (case_tac "p'=src")
     apply (simp add: no_prev_of_src')
    apply (drule m'_next)
    apply (drule m'_cap)+
    apply (clarsimp split: if_split_asm)
      apply (fastforce dest!: capMaster_capClass)
     apply (fastforce dest!: capMaster_capClass)
    apply fastforce
    done

  show "irq_control m'" using src dest parency
    apply (clarsimp simp: irq_control_def)
    apply (frule m'_revocable)
    apply (drule m'_cap)
    apply (clarsimp split: if_split_asm)
     apply (clarsimp simp add: weak_derived'_def)
     apply (frule irq_revocable, rule irq_control)
     apply clarsimp
     apply (drule m'_cap)
     apply (clarsimp split: if_split_asm)
     apply (drule (1) irq_controlD, rule irq_control)
     apply simp
    apply (frule irq_revocable, rule irq_control)
    apply clarsimp
    apply (drule m'_cap)
    apply (clarsimp split: if_split_asm)
     apply (clarsimp simp: weak_derived'_def)
     apply (drule (1) irq_controlD, rule irq_control)
     apply simp
    apply (erule (1) irq_controlD, rule irq_control)
    done

  have distz: "distinct_zombies m"
    using valid by (simp add: valid_mdb_ctes_def)

  thus "distinct_zombies m'"
    apply (simp add: m'_def distinct_zombies_nonCTE_modify_map)
    apply (simp add: n_def distinct_zombies_nonCTE_modify_map
                     modify_map_apply src dest neq)
    apply (erule distinct_zombies_switchE, rule dest, rule src)
     apply simp
    apply (cut_tac parency)
    apply (clarsimp simp: weak_derived'_def)
    done

  have "reply_masters_rvk_fb m" using valid ..
  thus "reply_masters_rvk_fb m'" using neq parency
    apply (simp add: m'_def n_def reply_masters_rvk_fb_def
                     ball_ran_modify_map_eq)
    apply (simp add: modify_map_apply m_p dest)
    apply (intro ball_ran_fun_updI, simp_all)
     apply (frule bspec, rule ranI, rule m_p)
     apply (clarsimp simp: weak_derived'_def)
     apply (drule master_eqE[where F=isReplyCap], simp add: gen_isCap_Master)
    apply (simp add: isCap_simps)+
    done

qed

end

context begin interpretation Arch . (*FIXME: arch-split*)

lemma cteMove_iflive'[wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s
      \<and> cte_wp_at' (\<lambda>c. weak_derived' (cteCap c) cap) src s
      \<and> cte_wp_at' (\<lambda>c. cteCap c \<noteq> NullCap) src s
      \<and> cte_wp_at' (\<lambda>c. cteCap c = NullCap) dest s\<rbrace>
     cteMove cap src dest
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  unfolding cteMove_def
  apply simp
  apply wp
        apply (simp only: if_live_then_nonz_cap'_def imp_conv_disj
                          ex_nonz_cap_to'_def)
        apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift
                  hoare_vcg_ex_lift updateCap_cte_wp_at_cases
                  getCTE_wp hoare_weak_lift_imp)+
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (drule(1) if_live_then_nonz_capE')
  apply (clarsimp simp: ex_nonz_cap_to'_def cte_wp_at_ctes_of)
  apply (drule_tac x="(id (src := dest, dest := src)) cref" in spec)
  apply (clarsimp dest!: weak_derived_zobj split: if_split_asm)
  done

lemma cteMove_valid_pspace' [wp]:
  "\<lbrace>\<lambda>x. valid_pspace' x \<and>
            cte_wp_at' (\<lambda>c. weak_derived' (cteCap c) capability) word1 x \<and>
            cte_wp_at' (\<lambda>c. isUntypedCap (cteCap c) \<longrightarrow> capability = cteCap c) word1 x \<and>
            cte_wp_at' (\<lambda>c. cteCap c \<noteq> NullCap) word1 x \<and>
            x \<turnstile>' capability \<and>
            cte_wp_at' (\<lambda>c. cteCap c = capability.NullCap) word2 x\<rbrace>
  cteMove capability word1 word2
  \<lbrace>\<lambda>y. valid_pspace'\<rbrace>"
  unfolding cteMove_def
  apply (simp add: pred_conj_def valid_pspace'_def valid_mdb'_def)
  apply (wp sch_act_wf_lift valid_queues_lift
    cur_tcb_lift updateCap_no_0  updateCap_ctes_of_wp getCTE_wp | simp)+
  apply (clarsimp simp: invs'_def valid_state'_def)+
  apply (clarsimp dest!: cte_at_cte_wp_atD)
  apply (rule_tac x = cte in exI)
  apply clarsimp
  apply (clarsimp dest!: cte_at_cte_wp_atD)
  apply (rule_tac x = ctea in exI)
  apply (clarsimp simp: isCap_simps)
  apply rule
   apply (clarsimp elim!: valid_mdb_ctesE)
  apply (case_tac ctea)
  apply (case_tac cte)
  apply (rule_tac old_dest_node = "cteMDBNode cte" and src_cap = "cteCap ctea" in
    mdb_move.cteMove_valid_mdb_helper)
  prefer 2
   apply (clarsimp simp: cte_wp_at_ctes_of weak_derived'_def isCap_simps simp del: not_ex)
  apply unfold_locales
         apply (simp_all add: valid_mdb'_def cte_wp_at_ctes_of nullPointer_def weak_derived'_def)
  apply clarsimp
  done

lemma cteMove_ifunsafe':
  "\<lbrace>if_unsafe_then_cap'
      and cte_wp_at' (\<lambda>c. cteCap c = capability.NullCap) dest
      and ex_cte_cap_to' dest
      and cte_wp_at' (\<lambda>c. weak_derived' (cteCap c) cap) src\<rbrace>
     cteMove cap src dest
   \<lbrace>\<lambda>rv. if_unsafe_then_cap'\<rbrace>"
  apply (rule hoare_pre)
   apply (simp add: ifunsafe'_def3 cteMove_def o_def)
   apply (wp getCTE_wp')
  apply (clarsimp simp: cte_wp_at_ctes_of cteCaps_of_def)
  apply (subgoal_tac "ex_cte_cap_to' cref s")
   apply (clarsimp simp: ex_cte_cap_to'_def cte_wp_at_ctes_of)
   apply (rule_tac x="(id (dest := src, src := dest)) crefb"
                in exI)
   apply (auto simp: modify_map_def dest!: weak_derived_cte_refs
              split: if_split_asm)[1]
  apply (case_tac "cref = dest")
   apply simp
  apply (rule if_unsafe_then_capD'[where P="\<lambda>cte. cteCap cte \<noteq> NullCap"])
    apply (clarsimp simp add: cte_wp_at_ctes_of modify_map_def
                       split: if_split_asm)
   apply simp+
  done

lemma cteMove_idle'[wp]:
  "\<lbrace>\<lambda>s. valid_idle' s\<rbrace>
     cteMove cap src dest
   \<lbrace>\<lambda>rv. valid_idle'\<rbrace>"
  apply (simp add: cteMove_def)
  apply (wp updateCap_idle' | simp)+
  apply (wp getCTE_wp')
  apply (clarsimp simp: valid_idle'_def cte_wp_at_ctes_of weak_derived'_def)
  done

crunch cteMove
  for ksInterrupt[wp]: "\<lambda>s. P (ksInterruptState s)"
  (wp: crunch_wps)

lemma cteMove_irq_handlers' [wp]:
  "\<lbrace>\<lambda>s. valid_irq_handlers' s
      \<and> cte_wp_at' (\<lambda>c. weak_derived' (cteCap c) cap) src s
      \<and> cte_wp_at' (\<lambda>c. cteCap c = NullCap) dest s\<rbrace>
     cteMove cap src dest
   \<lbrace>\<lambda>rv. valid_irq_handlers'\<rbrace>"
  apply (simp add: valid_irq_handlers'_def irq_issued'_def)
  apply (rule hoare_pre)
   apply (rule hoare_use_eq [where f=ksInterruptState, OF cteMove_ksInterrupt])
   apply (simp add: cteMove_def)
   apply (wp getCTE_wp)
  apply (clarsimp simp: cte_wp_at_ctes_of ran_def)
  apply (subst(asm) imp_ex, subst(asm) all_comm)
  apply (drule_tac x="(id (src := dest, dest := src)) a" in spec)
  apply (clarsimp simp: modify_map_def split: if_split_asm)
  apply (auto simp: cteCaps_of_def weak_derived'_def)
  done

lemmas cteMove_valid_irq_node'[wp]
    = valid_irq_node_lift[OF cteMove_ksInterrupt cteMove_typ_at']

crunch cteMove
  for valid_arch_state'[wp]: "valid_arch_state'"
  (wp: crunch_wps)

crunch cteMove
  for global_refs_noop[wp]: "\<lambda>s. P (global_refs' s)"
  (wp: crunch_wps)
crunch cteMove
  for gsMaxObjectSize[wp]: "\<lambda>s. P (gsMaxObjectSize s)"
  (wp: crunch_wps)

lemma cteMove_global_refs' [wp]:
  "\<lbrace>\<lambda>s. valid_global_refs' s
      \<and> cte_wp_at' (\<lambda>c. weak_derived' (cteCap c) cap) src s
      \<and> cte_wp_at' (\<lambda>c. cteCap c = NullCap) dest s\<rbrace>
     cteMove cap src dest
   \<lbrace>\<lambda>rv. valid_global_refs'\<rbrace>"
  apply (rule hoare_name_pre_state, clarsimp simp: valid_global_refs'_def)
  apply (frule_tac p=src and cte="the (ctes_of s src)" in cte_at_valid_cap_sizes_0)
   apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (simp add: valid_refs'_cteCaps valid_cap_sizes_cteCaps)
  apply (rule hoare_pre)
   apply (rule hoare_use_eq [where f=global_refs', OF cteMove_global_refs_noop])
   apply (rule hoare_use_eq [where f=gsMaxObjectSize], wp)
   apply (simp add: cteMove_def)
   apply (wp getCTE_wp)
  apply (clarsimp simp: cte_wp_at_ctes_of ran_def all_conj_distrib[symmetric]
                        imp_conjR[symmetric])
  apply (subst(asm) imp_ex, subst(asm) all_comm)
  apply (drule_tac x="(id (dest := src, src := dest)) a" in spec)
  apply (clarsimp simp: modify_map_def cteCaps_of_def
                 split: if_split_asm dest!: weak_derived_capRange_capBits)
  apply auto?
  done

lemma cteMove_urz [wp]:
  "\<lbrace>\<lambda>s. untyped_ranges_zero' s
      \<and> valid_pspace' s
      \<and> cte_wp_at' (\<lambda>c. weak_derived' (cteCap c) cap) src s
      \<and> cte_wp_at' (\<lambda>c. isUntypedCap (cteCap c) \<longrightarrow> cap = cteCap c) src s
      \<and> cte_wp_at' (\<lambda>c. cteCap c = NullCap) dest s\<rbrace>
     cteMove cap src dest
   \<lbrace>\<lambda>rv. untyped_ranges_zero'\<rbrace>"
  apply (clarsimp simp: cteMove_def)
  apply (rule hoare_pre)
   apply (wp untyped_ranges_zero_lift getCTE_wp' | simp)+
  apply (clarsimp simp: cte_wp_at_ctes_of
             split del: if_split)
  apply (erule untyped_ranges_zero_delta[where xs="[src, dest]"],
    (clarsimp simp: modify_map_def)+)
  apply (clarsimp simp: ran_restrict_map_insert modify_map_def
                        cteCaps_of_def untypedZeroRange_def[where ?x0.0=NullCap])
  apply (drule weak_derived_untypedZeroRange[OF weak_derived_sym'], clarsimp)
  apply auto
  done

crunch updateMDB
  for valid_bitmaps[wp]: valid_bitmaps
  (rule: valid_bitmaps_lift)

(* FIXME: arch-split *)
lemma haskell_assert_inv:
  "haskell_assert Q L \<lbrace>P\<rbrace>"
  by wpsimp

lemma cteMove_invs' [wp]:
  "\<lbrace>\<lambda>x. invs' x \<and> ex_cte_cap_to' word2 x \<and>
            cte_wp_at' (\<lambda>c. weak_derived' (cteCap c) capability) word1 x \<and>
            cte_wp_at' (\<lambda>c. isUntypedCap (cteCap c) \<longrightarrow> capability = cteCap c) word1 x \<and>
            cte_wp_at' (\<lambda>c. (cteCap c) \<noteq> NullCap) word1 x \<and>
            x \<turnstile>' capability \<and>
            cte_wp_at' (\<lambda>c. cteCap c = capability.NullCap) word2 x\<rbrace>
     cteMove capability word1 word2
   \<lbrace>\<lambda>y. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def pred_conj_def)
  apply (rule hoare_pre)
   apply ((rule hoare_vcg_conj_lift, (wp cteMove_ifunsafe')[1])
                  | rule hoare_vcg_conj_lift[rotated])+
      apply (unfold cteMove_def)
      apply (wp cur_tcb_lift valid_queues_lift haskell_assert_inv
                sch_act_wf_lift ct_idle_or_in_cur_domain'_lift2 tcb_in_cur_domain'_lift)+
  apply clarsimp
  done

lemma cteMove_cte_wp_at:
  "\<lbrace>\<lambda>s. cte_at' ptr s \<and> (if p = ptr  then (Q capability.NullCap) else (if p' = ptr then Q cap else cte_wp_at' (Q \<circ> cteCap) ptr s))\<rbrace>
  cteMove cap p p'
  \<lbrace>\<lambda>_ s. cte_wp_at' (\<lambda>c. Q (cteCap c)) ptr s\<rbrace>"
  unfolding cteMove_def
  apply (fold o_def)
  apply (wp updateCap_cte_wp_at_cases updateMDB_weak_cte_wp_at getCTE_wp hoare_weak_lift_imp|simp add: o_def)+
  apply (clarsimp simp: cte_wp_at_ctes_of)
  done

lemma cteMove_ex:
  "\<lbrace>ex_cte_cap_to' ptr and
    cte_wp_at' (weak_derived' cap o cteCap) p and
    cte_wp_at' ((=) NullCap o cteCap) p' and
    K (p \<noteq> p') \<rbrace>
  cteMove cap p p'
  \<lbrace>\<lambda>_. ex_cte_cap_to' ptr\<rbrace>"
  unfolding ex_cte_cap_to'_def
  apply (rule hoare_pre)
   apply (rule hoare_use_eq_irq_node' [OF cteMove_ksInterrupt])
   apply (wp hoare_vcg_ex_lift cteMove_cte_wp_at)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (case_tac "cref = p")
   apply simp
   apply (rule_tac x=p' in exI)
   apply (clarsimp simp: weak_derived'_def dest!: capMaster_same_refs)
  apply (rule_tac x=cref in exI)
  apply clarsimp
  done

lemmas cteMove_typ_at_lifts [wp] = typ_at_lifts [OF cteMove_typ_at']

lemmas finalise_slot_corres'
    = rec_del_corres[where args="FinaliseSlotCall slot exp",
                     simplified rec_del_concrete.simps,
                     simplified, folded finalise_slot_def] for slot exp
lemmas finalise_slot_corres = use_spec_corres [OF finalise_slot_corres']

lemma corres_disj_abs:
  "\<lbrakk> corres rv P R f g; corres rv Q R f g \<rbrakk>
        \<Longrightarrow> corres rv (\<lambda>s. P s \<or> Q s) R f g"
  by (auto simp: corres_underlying_def)

crunch updateCap
  for ksMachine[wp]: "\<lambda>s. P (ksMachineState s)"

lemma cap_relation_same:
  "\<lbrakk> cap_relation cap cap'; cap_relation cap cap'' \<rbrakk>
         \<Longrightarrow> cap' = cap''"
  by (clarsimp split: cap_relation_split_asm
                      arch_cap.split_asm)

crunch updateCap
  for gsUserPages[wp]: "\<lambda>s. P (gsUserPages s)"
crunch    updateCap
  for gsCNodes[wp]: "\<lambda>s. P (gsCNodes s)"
crunch updateCap
  for ksWorkUnitsCompleted[wp]: "\<lambda>s. P (ksWorkUnitsCompleted s)"
crunch updateCap
  for ksDomSchedule[wp]: "\<lambda>s. P (ksDomSchedule s)"
crunch updateCap
  for ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"
crunch updateCap
  for ksDomainTime[wp]: "\<lambda>s. P (ksDomainTime s)"

crunch updateCap
  for rdyq_projs[wp]:
    "\<lambda>s. P (ksReadyQueues s) (tcbSchedNexts_of s) (tcbSchedPrevs_of s) (\<lambda>d p. inQ d p |< tcbs_of' s)"

lemma corres_null_cap_update:
  "cap_relation cap cap' \<Longrightarrow>
   corres dc (invs and cte_wp_at ((=) cap) slot)
             (invs' and cte_at' (cte_map slot))
        (set_cap cap slot) (updateCap (cte_map slot) cap')"
  apply (rule corres_caps_decomposition[rotated])
             apply (wp updateCap_ctes_of_wp)+
          apply (clarsimp simp: cte_wp_at_ctes_of modify_map_apply
                                fun_upd_def[symmetric])
          apply (frule state_relation_pspace_relation)
          apply (frule(1) pspace_relation_ctes_ofI, clarsimp+)
          apply (drule(1) cap_relation_same)
          apply (case_tac cte)
          apply (clarsimp simp: cte_wp_at_caps_of_state fun_upd_idem)
          apply (clarsimp simp: state_relation_def)
          apply (erule_tac P="\<lambda>caps. cdt_relation caps m ctes" for m ctes in rsubst)
          apply (rule ext, clarsimp simp: cte_wp_at_caps_of_state eq_commute)
         apply(clarsimp simp: cdt_list_relation_def state_relation_def)
         apply(case_tac "next_slot (a, b) (cdt_list s) (cdt s)")
          apply(simp)
         apply(clarsimp)
         apply(erule_tac x=a in allE, erule_tac x=b in allE)
         apply(simp)
         apply(clarsimp simp: modify_map_def split: if_split_asm)
         apply(case_tac z)
         apply(clarsimp)
        apply (simp add: state_relation_def)
       apply (simp add: state_relation_def)
      apply (clarsimp simp: state_relation_def fun_upd_def[symmetric]
                            cte_wp_at_caps_of_state fun_upd_idem)
     apply (clarsimp simp: state_relation_def)
    apply (clarsimp simp: state_relation_def ghost_relation_of_heap)
   apply (clarsimp simp: state_relation_def ghost_relation_of_heap)
  apply (subst return_bind[where x="()", symmetric], subst updateCap_def,
         rule corres_split_forwards')
     apply (rule corres_guard_imp, rule getCTE_symb_exec_r, simp+)
    prefer 3
    apply clarsimp
    apply (rule setCTE_corres)
    apply (wp | simp)+
   apply (fastforce elim!: cte_wp_at_weakenE)
  apply wp
  apply fastforce
  done

declare corres_False' [simp]

lemma invokeCNode_corres:
  "cnodeinv_relation ci ci' \<Longrightarrow>
   corres (dc \<oplus> dc)
     (einvs and simple_sched_action and valid_cnode_inv ci)
     (invs' and sch_act_simple and valid_cnode_inv' ci')
     (invoke_cnode ci) (invokeCNode ci')"
  apply (simp add: invoke_cnode_def invokeCNode_def)
  apply (cases ci, simp_all)
        apply clarsimp
        apply (rule corres_guard_imp)
          apply (rule cteInsert_corres)
            apply simp+
         apply (clarsimp simp: invs_def valid_state_def valid_pspace_def
                        elim!: cte_wp_at_cte_at)
        apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def)
       apply clarsimp
       apply (rule corres_guard_imp)
         apply (erule cteMove_corres)
        apply (clarsimp simp: cte_wp_at_caps_of_state real_cte_tcb_valid)
       apply (clarsimp simp: cte_wp_at_ctes_of)
       apply (rule cteRevoke_corres)
     apply (rule corres_guard_imp [OF cteDelete_corres])
      apply (clarsimp simp: cte_at_typ cap_table_at_typ halted_emptyable)
     apply simp
    apply (rename_tac cap1 cap2 p1 p2 p3)
    apply (elim conjE exE)
    apply (intro impI conjI)
     apply simp
     apply (rule corres_guard_imp)
       apply (rule_tac F="wellformed_cap cap1 \<and> wellformed_cap cap2"
              in corres_gen_asm)
       apply (erule (1) cteSwap_corres [OF refl refl], simp+)
      apply (simp add: invs_def valid_state_def valid_pspace_def
                       real_cte_tcb_valid valid_cap_def2)
     apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def
                           cte_wp_at_ctes_of weak_derived'_def)
    apply (simp split del: if_split)
    apply (rule_tac F = "cte_map p1 \<noteq> cte_map p3" in corres_req)
     apply clarsimp
     apply (drule (2) cte_map_inj_eq [OF _ cte_wp_at_cte_at cte_wp_at_cte_at])
        apply clarsimp
       apply clarsimp
      apply clarsimp
     apply simp
    apply simp
    apply (rule corres_guard_imp)
      apply (rule corres_split)
         apply (erule cteMove_corres)
        apply (erule cteMove_corres)
       apply wp
       apply (simp add: cte_wp_at_caps_of_state)
       apply (wp cap_move_caps_of_state cteMove_cte_wp_at [simplified o_def])+
     apply (simp add: real_cte_tcb_valid invs_def valid_state_def valid_pspace_def)
     apply (elim conjE exE)
     apply (drule(3) real_cte_weak_derived_not_reply_masterD)+
     apply (clarsimp simp: cte_wp_at_caps_of_state
                           ex_cte_cap_to_cnode_always_appropriate_strg
                           cte_wp_at_conj)
    apply (simp add: cte_wp_at_ctes_of)
    apply (elim conjE exE)
    apply (intro impI conjI)
            apply fastforce
           apply (fastforce simp: weak_derived'_def)
          apply simp
         apply (erule weak_derived_sym')
        apply clarsimp
       apply simp
      apply clarsimp
     apply simp
    apply clarsimp
   apply clarsimp
   apply (rename_tac prod)
   apply (simp add: getThreadCallerSlot_def locateSlot_conv objBits_simps)
   apply (rule corres_guard_imp)
     apply (rule corres_split[OF getCurThread_corres])
       apply (subgoal_tac "thread + 2^cte_level_bits * tcbCallerSlot = cte_map (thread, tcb_cnode_index 3)")
        prefer 2
        apply (simp add: cte_map_def tcb_cnode_index_def tcbCallerSlot_def shiftl_t2n')
       apply (rule corres_split[OF getSlotCap_corres])
          apply simp
         apply (rule_tac P="\<lambda>s. (is_reply_cap cap \<or> cap = cap.NullCap) \<and>
       (is_reply_cap cap \<longrightarrow>
        (einvs and cte_at (threada, tcb_cnode_index 3) and
         cte_wp_at (\<lambda>c. c = cap.NullCap) prod and
         real_cte_at prod and valid_cap cap and
         K ((threada, tcb_cnode_index 3) \<noteq> prod)) s)" and
        P'="\<lambda>s. (isReplyCap rv' \<and> \<not> capReplyMaster rv') \<longrightarrow> (invs' and
         cte_wp_at'
          (\<lambda>c. weak_derived' rv' (cteCap c) \<and>
               cteCap c \<noteq> capability.NullCap)
          (cte_map (threada, tcb_cnode_index 3)) and
         cte_wp_at' (\<lambda>c. cteCap c = capability.NullCap) (cte_map prod)) s" in corres_inst)
         apply (case_tac cap, simp_all add: isCap_simps is_cap_simps split: bool.split)[1]
         apply clarsimp
         apply (rule corres_guard_imp)
           apply (rule cteMove_corres)
           apply (simp add: real_cte_tcb_valid)+
        apply (wp get_cap_wp)
       apply (simp add: getSlotCap_def)
       apply (wp getCTE_wp)+
    apply clarsimp
    apply (rule conjI)
     apply (rule tcb_at_cte_at)
      apply fastforce
     apply (simp add: tcb_cap_cases_def)
    apply (clarsimp simp: cte_wp_at_cte_at)
    apply (rule conjI)
     apply (frule tcb_at_invs)
     apply (frule_tac ref="tcb_cnode_index 3" and Q="is_reply_cap or (=) cap.NullCap"
                   in tcb_cap_wp_at)
        apply (clarsimp split: Structures_A.thread_state.split_asm)+
     apply (clarsimp simp: cte_wp_at_def is_cap_simps all_rights_def)
    apply clarsimp
    apply (rule conjI, simp add: cte_wp_valid_cap invs_valid_objs)
    apply (clarsimp simp: cte_wp_at_def is_cap_simps all_rights_def)
   apply clarsimp
   apply (rule conjI, fastforce)
   apply (rule conjI, fastforce)
   apply (clarsimp simp: cte_wp_at_ctes_of isCap_simps)
  apply clarsimp
  apply (case_tac "has_cancel_send_rights x7",
                frule has_cancel_send_rights_ep_cap,
                simp add: is_cap_simps)
   apply (clarsimp simp: when_def unless_def isCap_simps)
   apply (rule corres_guard_imp)
     apply (rule cancelBadgedSends_corres)
    apply (simp add: valid_cap_def)
   apply (simp add: valid_cap'_def)
  apply (clarsimp)
  done

lemma updateCap_noop_irq_handlers:
  "\<lbrace>valid_irq_handlers' and cte_wp_at' (\<lambda>cte. cteCap cte = cap) slot\<rbrace>
     updateCap slot cap
   \<lbrace>\<lambda>rv. valid_irq_handlers'\<rbrace>"
  apply (simp add: valid_irq_handlers'_def irq_issued'_def)
  apply (rule hoare_pre)
   apply (rule hoare_use_eq[where f=ksInterruptState, OF updateCap_ksInterruptState])
   apply wp
  apply (simp, subst(asm) tree_cte_cteCap_eq[unfolded o_def])
  apply (simp split: option.split_asm
                add: modify_map_apply fun_upd_idem)
  done

crunch updateCap
  for ct_idle_or_in_cur_domain'[wp]: ct_idle_or_in_cur_domain'
  (rule: ct_idle_or_in_cur_domain'_lift2)

lemma updateCap_noop_invs:
  "\<lbrace>invs' and cte_wp_at' (\<lambda>cte. cteCap cte = cap) slot\<rbrace>
     updateCap slot cap
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def
                   valid_pspace'_def valid_mdb'_def)
  apply (rule hoare_pre)
   apply (wp updateCap_ctes_of_wp updateCap_iflive'
             updateCap_ifunsafe' updateCap_idle'
             valid_irq_node_lift
             updateCap_noop_irq_handlers sch_act_wf_lift
             untyped_ranges_zero_lift)
  apply (clarsimp simp: cte_wp_at_ctes_of modify_map_apply)
  apply (strengthen untyped_ranges_zero_delta[where xs=Nil, mk_strg I E])
  apply (case_tac cte)
  apply (clarsimp simp: fun_upd_idem cteCaps_of_def modify_map_apply
                        valid_mdb'_def)
  apply (frule(1) ctes_of_valid')
  apply (frule(1) valid_global_refsD_with_objSize)
  apply clarsimp
  apply (rule_tac P="(=) cte" for cte in if_unsafe_then_capD')
    apply (simp add: cte_wp_at_ctes_of)
   apply assumption
  apply clarsimp
  done

lemmas make_zombie_or_noop_or_arch_invs
    = hoare_vcg_disj_lift [OF updateCap_noop_invs
   hoare_vcg_disj_lift [OF make_zombie_invs' arch_update_updateCap_invs],
   simplified]

lemma invokeCNode_invs' [wp]:
  "\<lbrace>invs' and sch_act_simple and valid_cnode_inv' cinv\<rbrace>
    invokeCNode cinv \<lbrace>\<lambda>y. invs'\<rbrace>"
  unfolding invokeCNode_def
  apply (cases cinv)
        apply (wp cteRevoke_invs' cteInsert_invs | simp split del: if_split)+
        apply (clarsimp simp: cte_wp_at_ctes_of is_derived'_def isCap_simps badge_derived'_def)
        apply (erule(1) valid_irq_handlers_ctes_ofD)
        apply (clarsimp simp: invs'_def valid_state'_def)
       defer
       apply (wp cteRevoke_invs' | simp)+
      apply (clarsimp simp:cte_wp_at_ctes_of)
      apply (erule weak_derived_sym')
     defer
     apply (simp add: getSlotCap_def getThreadCallerSlot_def locateSlot_conv)
     apply (rule hoare_pre)
      apply (wp haskell_fail_wp getCTE_wp|wpc)+
     apply (clarsimp simp: cte_wp_at_ctes_of)
     apply (case_tac ctea)
     apply clarsimp
     apply (erule ctes_of_valid_cap')
     apply fastforce
    apply (wp cteDelete_invs'|simp split del: if_split)+
    apply (wp cteMove_ex cteMove_cte_wp_at)+
   apply (clarsimp simp:cte_wp_at_ctes_of)
   apply (fastforce simp: isCap_simps weak_derived'_def)
  apply (rule hoare_pre)
   apply simp
   apply (wp | wpc | simp add: unless_def)+
  done

declare withoutPreemption_lift [wp]

crunch capSwapForDelete
  for irq_states'[wp]: valid_irq_states'

lemma setVCPU_valid_irq_states' [wp]:
  "setObject p (vcpu::vcpu) \<lbrace>valid_irq_states'\<rbrace>"
  by (wp valid_irq_states_lift')

crunch writeVCPUHardwareReg, readVCPUHardwareReg, check_export_arch_timer
  for irq_masks[wp]: "\<lambda>s. P (irq_masks s)"

crunch vcpuUpdate, vcpuWriteReg, vcpuSaveReg, vcpuRestoreReg, vcpuReadReg
  for irq_states'[wp]: valid_irq_states'
  and ksInterrupt[wp]: "\<lambda>s. P (ksInterruptState s)"
  (ignore: getObject setObject)

lemma saveVirtTimer_irq_states'[wp]:
  "saveVirtTimer vcpu_ptr \<lbrace>valid_irq_states'\<rbrace>"
  unfolding saveVirtTimer_def
  by (wpsimp simp: read_cntpct_def get_cntv_off_64_def get_cntv_cval_64_def
             wp: doMachineOp_irq_states')

lemma restoreVirtTimer_irq_states'[wp]:
  "restoreVirtTimer vcpu_ptr \<lbrace>valid_irq_states'\<rbrace>"
  unfolding restoreVirtTimer_def isIRQActive_def
  by (simp add: liftM_bind)
     (wpsimp wp: maskInterrupt_irq_states' getIRQState_wp hoare_vcg_imp_lift' doMachineOp_irq_states'
             simp: if_apply_def2 set_cntv_off_64_def read_cntpct_def set_cntv_cval_64_def)

crunch
  vcpuDisable, vcpuEnable, vcpuRestore, vcpuRestoreReg, vcpuSaveReg,
  vcpuUpdate, vgicUpdateLR, vcpuSave
  for irq_states' [wp]: valid_irq_states'
  (wp: crunch_wps maskInterrupt_irq_states'[where b=True, simplified] no_irq no_irq_mapM_x
   simp: crunch_simps no_irq_isb no_irq_dsb
         set_gic_vcpu_ctrl_hcr_def setSCTLR_def setHCR_def get_gic_vcpu_ctrl_hcr_def
         getSCTLR_def get_gic_vcpu_ctrl_lr_def get_gic_vcpu_ctrl_apr_def
         get_gic_vcpu_ctrl_vmcr_def
         set_gic_vcpu_ctrl_vmcr_def set_gic_vcpu_ctrl_apr_def uncurry_def
         set_gic_vcpu_ctrl_lr_def
   ignore: saveVirtTimer)

crunch finaliseCap
  for irq_states'[wp]: valid_irq_states'
  (wp: crunch_wps unless_wp getASID_wp no_irq
       no_irq_invalidateLocalTLB_ASID no_irq_setHardwareASID
       no_irq_setCurrentPD no_irq_invalidateLocalTLB_VAASID
       no_irq_cleanByVA_PoU FalseI
   simp: crunch_simps armv_contextSwitch_HWASID_def writeContextIDAndPD_def o_def)

lemma finaliseSlot_IRQInactive':
  "s \<turnstile> \<lbrace>valid_irq_states'\<rbrace> finaliseSlot' a b
  \<lbrace>\<lambda>_. valid_irq_states'\<rbrace>, \<lbrace>\<lambda>rv s. intStateIRQTable (ksInterruptState s) rv \<noteq> irqstate.IRQInactive\<rbrace>"
proof (induct rule: finalise_spec_induct)
  case (1 sl exp s)
  show ?case
    apply (rule hoare_pre_spec_validE)
     apply (subst finaliseSlot'_simps_ext)
     apply (simp only: split_def)
     apply (wp "1.hyps")
            apply (unfold Let_def split_def fst_conv snd_conv
                          case_Zombie_assert_fold haskell_fail_def)
            apply (wp getCTE_wp' preemptionPoint_invR| simp add: o_def irq_state_independent_HI)+
            apply (rule hoare_post_imp[where Q'="\<lambda>_. valid_irq_states'"])
             apply simp
            apply wp[1]
           apply (rule spec_strengthen_postE)
            apply (rule "1.hyps", (assumption|rule refl)+)
           apply simp
          apply (wp hoare_drop_imps hoare_vcg_all_lift | simp add: locateSlot_conv)+
    done
qed

lemma finaliseSlot_IRQInactive:
  "\<lbrace>valid_irq_states'\<rbrace> finaliseSlot a b
  -, \<lbrace>\<lambda>rv s. intStateIRQTable (ksInterruptState s) rv \<noteq> irqstate.IRQInactive\<rbrace>"
  apply (unfold validE_E_def)
  apply (rule hoare_strengthen_postE)
  apply (rule use_spec(2) [OF finaliseSlot_IRQInactive', folded finaliseSlot_def])
   apply (rule TrueI)
  apply assumption
  done

lemma finaliseSlot_irq_states':
  "\<lbrace>valid_irq_states'\<rbrace> finaliseSlot a b \<lbrace>\<lambda>rv. valid_irq_states'\<rbrace>"
  by (wp finaliseSlot_preservation | clarsimp)+

lemma cteDelete_IRQInactive:
  "\<lbrace>valid_irq_states'\<rbrace> cteDelete x y
  -, \<lbrace>\<lambda>rv s. intStateIRQTable (ksInterruptState s) rv \<noteq> irqstate.IRQInactive\<rbrace>"
  apply (simp add: cteDelete_def split_def)
  apply (wp whenE_wp)
   apply (rule hoare_strengthen_postE)
     apply (rule validE_E_validE)
     apply (rule finaliseSlot_IRQInactive)
    apply simp
   apply simp
  apply assumption
  done

lemma cteDelete_irq_states':
  "\<lbrace>valid_irq_states'\<rbrace> cteDelete x y
  \<lbrace>\<lambda>rv. valid_irq_states'\<rbrace>"
  apply (simp add: cteDelete_def split_def)
  apply (wp whenE_wp)
   apply (rule hoare_strengthen_postE)
     apply (rule valid_validE)
     apply (rule finaliseSlot_irq_states')
    apply simp
   apply simp
  apply assumption
  done

lemma preemptionPoint_IRQInactive_spec:
  "s \<turnstile> \<lbrace>valid_irq_states'\<rbrace> preemptionPoint
  \<lbrace>\<lambda>_. valid_irq_states'\<rbrace>, \<lbrace>\<lambda>rv s. intStateIRQTable (ksInterruptState s) rv \<noteq> irqstate.IRQInactive\<rbrace>"
  apply wp
  apply (rule hoare_pre, wp preemptionPoint_invR)
   apply clarsimp+
  done

lemma cteRevoke_IRQInactive':
  "s \<turnstile> \<lbrace>valid_irq_states'\<rbrace> cteRevoke x
  \<lbrace>\<lambda>_. \<top>\<rbrace>, \<lbrace>\<lambda>rv s. intStateIRQTable (ksInterruptState s) rv \<noteq> irqstate.IRQInactive\<rbrace>"
proof (induct rule: cteRevoke.induct)
  case (1 p s')
  show ?case
    apply (subst cteRevoke.simps)
    apply (wp "1.hyps" unlessE_wp whenE_wp preemptionPoint_IRQInactive_spec
              cteDelete_IRQInactive cteDelete_irq_states' getCTE_wp')+
    apply clarsimp
    done
qed

lemma cteRevoke_IRQInactive:
  "\<lbrace>valid_irq_states'\<rbrace> cteRevoke x
  -, \<lbrace>\<lambda>rv s. intStateIRQTable (ksInterruptState s) rv \<noteq> irqstate.IRQInactive\<rbrace>"
  apply (unfold validE_E_def)
  apply (rule use_spec)
  apply (rule cteRevoke_IRQInactive')
  done

lemma inv_cnode_IRQInactive:
  "\<lbrace>valid_irq_states'\<rbrace> invokeCNode cnode_inv
  -, \<lbrace>\<lambda>rv s. intStateIRQTable (ksInterruptState s) rv \<noteq> irqstate.IRQInactive\<rbrace>"
  apply (simp add: invokeCNode_def)
  apply (wp hoare_TrueI [where P=\<top>] cteRevoke_IRQInactive finaliseSlot_IRQInactive
             cteDelete_IRQInactive
             whenE_wp
           | wpc
           | simp add:  split_def)+
  done

end

end
