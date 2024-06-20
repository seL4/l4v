(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory CNode_DP
imports Invocation_DP RWHelper_DP
begin

lemma decode_cnode_copy_same_parent_rvu:
  "\<lbrakk>intent = CNodeCopyIntent dest_index dest_depth src_index src_depth rights;
   cap_object cap = cap_object target;
   get_index caps 0 = Some (cap ,cap_ref);
   \<forall>cap'. reset_cap_asid cap' = reset_cap_asid src_cap
     \<longrightarrow> Q (InsertCall (derived_cap (update_cap_rights (cap_rights cap' \<inter> rights) cap'))
    (cap_object cap, offset src_index sz)
    (cap_object target, offset dest_index sz)) \<rbrakk> \<Longrightarrow>
  \<lbrace> K (one_lvl_lookup target (unat dest_depth) sz \<and>
  guard_equal target dest_index (unat dest_depth) \<and>
  is_cnode_cap target \<and>
  one_lvl_lookup cap (unat src_depth) sz \<and>
  guard_equal cap src_index (unat src_depth) \<and>
  is_cnode_cap cap) and
  < (cap_object cap) \<mapsto>f CNode (empty_cnode sz)
   \<and>* (cap_object cap, offset src_index sz) \<mapsto>c src_cap
   \<and>* (cap_object target, offset dest_index sz) \<mapsto>c NullCap \<and>* R>
  and K (unat src_depth \<le> word_bits \<and> 0 < unat src_depth \<and>
  unat dest_depth \<le> word_bits \<and> 0 < unat dest_depth) \<rbrace>
  decode_cnode_invocation target target_ref caps intent
  \<lbrace>\<lambda>rv s. Q rv\<rbrace>, -"
  apply (clarsimp simp:user_pointer_at_def Let_def)
  apply (clarsimp simp: decode_cnode_invocation_def split_def split: sum.splits)
  apply (wp whenE_wp | simp)+
        apply (rule validE_validE_R)
        apply (wp derive_cap_invE)+
      apply (rule validE_validE_R)
      apply (rule lookup_slot_for_cnode_op_rvu' [where r=sz and cap=src_cap])
     apply simp
     apply wp+
    apply (rule validE_validE_R)
    apply (rule lookup_slot_for_cnode_op_rvu'[where r=sz and cap=NullCap])
   apply (simp, wp throw_on_none_rv validE_R_validE)
  apply (clarsimp split: option.splits)
  apply (intro conjI)
    apply (clarsimp dest!: mapu_dest_opt_cap simp:conj_comms)
    apply (clarsimp simp: sep_conj_assoc user_pointer_at_def Let_def)
    apply sep_solve
   apply clarsimp
   apply (rule conjI)
    apply (sep_select_asm 2)
    apply (clarsimp dest!: opt_cap_sep_imp simp:conj_comms)
   apply (clarsimp simp: sep_conj_assoc user_pointer_at_def Let_def)+
  apply sep_solve
  done

lemma invoke_cnode_insert_cdl_current_domain[wp]:
  "\<lbrace>\<lambda>s. P (cdl_current_domain s)\<rbrace>
    invoke_cnode (InsertCall cap src_slot dest_slot)
   \<lbrace>\<lambda>_ s. P (cdl_current_domain s) \<rbrace>"
  apply (simp add: invoke_cnode_def)
  apply (rule hoare_pre)
   apply (wp | wpc | clarsimp)+
  done

lemma invoke_cnode_move_cdl_current_domain[wp]:
  "\<lbrace>\<lambda>s. P (cdl_current_domain s)\<rbrace>
    invoke_cnode (MoveCall a b c)
   \<lbrace>\<lambda>_ s. P (cdl_current_domain s) \<rbrace>"
  apply (simp add: invoke_cnode_def)
  apply (rule hoare_pre)
   apply (wp | wpc | clarsimp)+
  done

lemma seL4_CNode_Mint_sep:
  "\<lbrace>\<lambda>s.
     \<guillemotleft>root_tcb_id \<mapsto>f tcb \<and>*
     (root_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*

     \<comment> \<open>Root CNode.\<close>
     cnode_id \<mapsto>f CNode (empty_cnode root_size) \<and>*
     \<comment> \<open>Client cnode.\<close>
     dest_id \<mapsto>f CNode (empty_cnode dest_size) \<and>*

     \<comment> \<open>Cap to the root CNode.\<close>
     (root_tcb_id, tcb_cspace_slot) \<mapsto>c cnode_cap \<and>*
     \<comment> \<open>Cap to the client CNode.\<close>
     (cnode_id, dest_root_slot) \<mapsto>c dest_root_cap \<and>*
     \<comment> \<open>Cap that the root task has to its own CNode.\<close>
     (cnode_id, cnode_cap_slot) \<mapsto>c cnode_cap' \<and>*
     \<comment> \<open>Cap to be copied, in the root CNode.\<close>
     (cnode_id, src_slot) \<mapsto>c src_cap \<and>*
     \<comment> \<open>Where to copy the cap (in the client CNode).\<close>
     (dest_id, dest_slot) \<mapsto>c NullCap \<and>*
      R\<guillemotright> s \<and>

     valid_src_cap src_cap data \<and>
     one_lvl_lookup cnode_cap 32 root_size \<and>
     one_lvl_lookup cnode_cap' (unat src_depth) root_size \<and>
     one_lvl_lookup dest_root_cap (unat dest_depth) dest_size \<and>

     \<comment> \<open>We need some word invariants\<close>
     unat src_depth \<le> word_bits \<and>
     0 < unat src_depth \<and>
     unat dest_depth \<le> word_bits \<and>
     0 < unat dest_depth \<and>
     is_tcb tcb \<and>
     is_cnode_cap dest_root_cap \<and>
     is_cnode_cap cnode_cap \<and>
     is_cnode_cap cnode_cap' \<and>
     guard_equal cnode_cap' src_index (unat src_depth) \<and>
     guard_equal dest_root_cap dest_index (unat dest_depth) \<and>
     guard_equal cnode_cap src_root word_bits \<and>
     guard_equal cnode_cap dest_root word_bits \<and>


     \<comment> \<open>Caps point to the right objects.\<close>
     cap_object cnode_cap = cnode_id \<and>
     cap_object cnode_cap' = cnode_id \<and>
     cap_object dest_root_cap = dest_id \<and>

     \<comment> \<open>Cap slots match their cptrs.\<close>
     dest_root_slot = offset dest_root root_size \<and>
     cnode_cap_slot = offset src_root root_size \<and>
     src_slot = offset src_index root_size \<and>
     dest_slot = offset dest_index dest_size \<and>

     cap' = update_cap_data_det data (update_cap_rights (cap_rights src_cap \<inter> rights) src_cap) \<and>
     (is_ep_cap src_cap \<or> is_ntfn_cap src_cap \<longrightarrow> cap_badge src_cap = 0) \<and>
     cap_has_type src_cap \<and> \<not> is_untyped_cap src_cap
  \<rbrace>
  seL4_CNode_Mint dest_root dest_index dest_depth src_root src_index src_depth rights data
  \<lbrace>\<lambda>_. \<guillemotleft> root_tcb_id \<mapsto>f tcb \<and>*
       cnode_id \<mapsto>f CNode (empty_cnode root_size) \<and>*
       dest_id \<mapsto>f CNode (empty_cnode dest_size) \<and>*
       (root_tcb_id, tcb_cspace_slot) \<mapsto>c cnode_cap \<and>*
       (root_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
       (cnode_id, dest_root_slot) \<mapsto>c dest_root_cap \<and>*
       (cnode_id, cnode_cap_slot) \<mapsto>c cnode_cap' \<and>*
       (cnode_id, src_slot) \<mapsto>c src_cap \<and>*
       (dest_id, dest_slot) \<mapsto>c derived_cap cap' \<and>* R\<guillemotright>\<rbrace>"
  apply (simp add:seL4_CNode_Mint_def sep_state_projection2_def)
  apply (rule do_kernel_op_pull_back)
  apply (rule hoare_name_pre_state)
  apply (simp add:is_tcb_def split:cdl_object.split_asm)
  apply (rename_tac cdl_tcb)
  apply (rule hoare_pre)
   apply (rule call_kernel_with_intent_allow_error_helper[where check=True,simplified,rotated -1])
               apply assumption
              apply fastforce
             apply (clarsimp simp:sep_conj_assoc)
             apply (rule hoare_post_imp[OF _
             set_cap_wp])
             apply (sep_select 5,assumption)
            apply wp[1]
           apply (rule_tac P = "root_tcb_id \<mapsto>f Tcb cdl_tcb \<and>*
                      (root_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
                      cnode_id \<mapsto>f CNode (empty_cnode root_size) \<and>*
                      dest_id \<mapsto>f CNode (empty_cnode dest_size) \<and>*
                      (root_tcb_id, tcb_cspace_slot) \<mapsto>c cnode_cap \<and>*
                      (cnode_id, offset dest_root root_size) \<mapsto>c dest_root_cap \<and>*
                      (cnode_id, offset src_root root_size) \<mapsto>c cnode_cap' \<and>*
                      (cnode_id, offset src_index root_size) \<mapsto>c src_cap \<and>*
                      (dest_id, offset dest_index dest_size) \<mapsto>c NullCap \<and>* R"
                      in mark_tcb_intent_error_sep_inv)
          apply wp[1]
         apply (rule corrupt_ipc_buffer_sep_inv)
        apply (rule_tac P = "(\<exists>cap''. reset_cap_asid cap'' = reset_cap_asid cap' \<and>
                          iv = InvokeCNode (InsertCall (derived_cap cap'')
                               (cap_object cnode_cap, offset src_index root_size)
                               (cap_object dest_root_cap,offset dest_index dest_size)))"
        in hoare_gen_asmEx)
        apply (elim conjE exE)
        apply simp
        apply (rule false_e_explode)
        apply (rule no_exception_conj')
         apply (wp cnode_insert_cap_cdl_current_thread)[1]
        apply (rule no_exception_conj')
         apply (wp)[1]
        apply (rule hoare_strengthen_postE)
          apply (rule_tac R = "(root_tcb_id, tcb_pending_op_slot) \<mapsto>c RestartCap \<and>* R" for R
          in invoke_cnode_insert_cap')
          apply simp
         apply (rule conjI[rotated])
          apply (rule sep_any_imp_c'_conj[where cap = RestartCap])
          apply (frule sep_map_c_asid_reset[where ptr = "(cap_object dest_root_cap, offset dest_index dest_size)"
          ,OF reset_cap_asid_derived])
          apply simp
          apply (sep_solve)
         apply sep_solve
        apply (assumption)
       apply (rule_tac Q'="\<lambda>r. (\<lambda>s. cdl_current_thread s = Some root_tcb_id \<and>
                cdl_current_domain s = minBound) and
                < (root_tcb_id, tcb_pending_op_slot) \<mapsto>c RestartCap \<and>* Q > and
                K (\<exists>cap''. reset_cap_asid cap'' = reset_cap_asid cap' \<and> iv = InvokeCNode
                (InsertCall (derived_cap cap'') (cap_object cnode_cap, offset src_index root_size)
                (cap_object dest_root_cap, offset dest_index dest_size)))" for Q
                in hoare_strengthen_post[rotated])
        apply (clarsimp simp:cap_of_insert_call_def)
        apply (rule conjI)
         apply (sep_select 2,assumption)
        apply (rule conjI)
         apply (drule reset_cap_asid_cap_type)
         apply (simp)
        apply (rule_tac x = cap'' in exI)
        apply (simp add:reset_cap_asid_derived)
       apply (wp set_cap_wp set_cap_all_scheduable_tcbs)[1]
      apply (rule_tac P = "is_cnode_cap (fst (c,ref))" in hoare_gen_asmEx)
      apply (clarsimp simp: decode_invocation_simps split_def)
      apply (rule liftME_wp)
      apply (rule decode_cnode_mint_rvu)
     apply (simp add:lookup_extra_caps_def mapME_def sequenceE_def get_index_def)
     apply (rule wp_no_exception_seq)
      apply wp[1]
     apply clarsimp
     apply (rule lookup_cap_and_slot_rvu[where r = root_size and
    cap = cnode_cap and cap'=cnode_cap'])
    apply (rule hoare_pre)
     apply (rule lookup_cap_and_slot_rvu[where r = root_size and
    cap = cnode_cap and cap' = dest_root_cap])
    defer
    apply (clarsimp simp:Let_def)
    apply (wp hoare_vcg_ball_lift
              sep_inv_to_all_scheduable_tcbs[OF update_thread_intent_update]
              hoare_vcg_imp_lift hoare_vcg_ex_lift hoare_vcg_all_lift
              is_cnode_cap_guard_equal update_thread_intent_update update_thread_cnode_at
            | clarsimp)+
   apply (intro conjI impI)
    apply (sep_solve)
   apply sep_solve
  apply (clarsimp simp:conj_comms cnode_non_ep)
  apply (thin_tac "(P \<and>* Q) (sep_state_projection sa)" for P Q)
  apply (clarsimp simp:user_pointer_at_def Let_def word_bits_def)
  apply (intro conjI impI allI, simp_all)
                   apply (clarsimp simp:sep_conj_assoc)
                   apply sep_solve
                  apply (frule reset_cap_asid_cnode_cap)
                   apply clarsimp
                  apply (simp add: cnode_cap_non_ep_related get_index_def)[1]
                 apply (clarsimp simp:sep_conj_assoc)
                 apply sep_solve
                apply (clarsimp dest!: reset_cap_asid_cnode_cap)
               apply sep_solve
              apply clarsimp+
            apply (fastforce cong: cap_type_bad_cong dest!: reset_cap_asid_cnode_cap)+
      apply (drule(1) reset_cap_asid_cnode_cap | simp)+
      apply (clarsimp simp:sep_conj_assoc)
      apply sep_solve
     apply (clarsimp dest!:reset_cap_asid_cnode_cap)
    apply (clarsimp dest!:reset_cap_asid_cnode_cap)
   apply (metis reset_cap_asid_update_cap_data reset_cap_asid_update_cap_rights)
  apply (sep_solve)
  done

lemma seL4_CNode_Mutate_sep:
  "\<lbrace>\<lambda>s. \<guillemotleft>
     root_tcb_id \<mapsto>f tcb \<and>*
     (root_tcb_id, tcb_pending_op_slot) \<mapsto>c - \<and>*

     \<comment> \<open>Root CNode.\<close>
     cnode_id \<mapsto>f CNode (empty_cnode root_size) \<and>*
     \<comment> \<open>Client cnode.\<close>
     dest_id \<mapsto>f CNode (empty_cnode dest_size) \<and>*

     \<comment> \<open>Cap to the root CNode.\<close>
     (root_tcb_id, tcb_cspace_slot) \<mapsto>c cnode_cap \<and>*
     \<comment> \<open>Cap to the client CNode.\<close>
     (cnode_id, dest_root_slot) \<mapsto>c dest_root_cap \<and>*
     \<comment> \<open>Cap that the root task has to its own CNode.\<close>
     (cnode_id, cnode_cap_slot) \<mapsto>c cnode_cap' \<and>*
     \<comment> \<open>Cap to be copied, in the root CNode.\<close>
     (cnode_id, src_slot) \<mapsto>c src_cap \<and>*
     \<comment> \<open>Where to copy the cap (in the client CNode).\<close>
     (dest_id, dest_slot) \<mapsto>c NullCap \<and>*
      R\<guillemotright> s \<and>

     one_lvl_lookup cnode_cap 32 root_size \<and>
     one_lvl_lookup cnode_cap' (unat src_depth) root_size \<and>
     one_lvl_lookup dest_root_cap (unat dest_depth) dest_size \<and>

     \<comment> \<open>We need some word invariants\<close>
     unat src_depth \<le> word_bits \<and>
     0 < unat src_depth \<and>
     unat dest_depth \<le> word_bits \<and>
     0 < unat dest_depth \<and>

     is_tcb tcb \<and>
     is_cnode_cap dest_root_cap \<and>
     is_cnode_cap cnode_cap \<and>
     is_cnode_cap cnode_cap' \<and>
     guard_equal cnode_cap' src_index (unat src_depth) \<and>
     guard_equal cnode_cap src_index (unat src_depth) \<and>
     guard_equal dest_root_cap dest_index (unat dest_depth ) \<and>
     guard_equal cnode_cap src_root word_bits \<and>
     guard_equal cnode_cap dest_root word_bits \<and>
     \<comment> \<open>Caps point to the right objects.\<close>
     cap_object cnode_cap = cnode_id \<and>
     cap_object cnode_cap' = cnode_id \<and>
     cap_object dest_root_cap = dest_id \<and>

     \<comment> \<open>Cap slots match their cptrs.\<close>
     dest_root_slot = offset dest_root root_size \<and>
     cnode_cap_slot = offset src_root root_size \<and>
     src_slot = offset src_index root_size \<and>
     dest_slot = offset dest_index dest_size \<and>

     cap' = update_cap_data_det data src_cap \<and>
     valid_src_cap src_cap data \<and> \<not> ep_related_cap src_cap \<and> cap_has_type src_cap
   \<rbrace>
  seL4_CNode_Mutate dest_root dest_index dest_depth src_root src_index src_depth data
  \<lbrace>\<lambda>_. \<guillemotleft> root_tcb_id \<mapsto>f tcb \<and>*
       cnode_id \<mapsto>f CNode (empty_cnode root_size) \<and>*
       dest_id \<mapsto>f CNode (empty_cnode dest_size) \<and>*
       (root_tcb_id, tcb_cspace_slot) \<mapsto>c cnode_cap \<and>*
       (root_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
       (cnode_id, dest_root_slot) \<mapsto>c dest_root_cap \<and>*
       (cnode_id, cnode_cap_slot) \<mapsto>c cnode_cap' \<and>*
       (cnode_id, src_slot) \<mapsto>c NullCap \<and>*
       (dest_id, dest_slot) \<mapsto>c cap' \<and>* R\<guillemotright>\<rbrace>"
  apply (simp add:seL4_CNode_Mutate_def sep_state_projection2_def)
  apply (rule do_kernel_op_pull_back)
   apply (rule hoare_pre)
   apply (rule_tac
               intent_op = "CNodeIntent (CNodeMutateIntent dest_index dest_depth src_index src_depth data)"
           and intent_cptr = dest_root
           and intent_extra = "[src_root]" in call_kernel_with_intent_no_fault_helper)
            apply (clarsimp simp:sep_conj_assoc)
            apply (rule hoare_post_imp[OF _
              set_cap_wp])
            apply (sep_select 5,assumption)
           apply wp
          apply wp
         apply (rule_tac P = "\<exists>dcap.
           reset_cap_asid dcap = reset_cap_asid src_cap \<and>
           iv = InvokeCNode
           (MoveCall (update_cap_data_det data dcap)
           (cap_object cnode_cap', offset src_index root_size)
           (cap_object dest_root_cap, offset dest_index dest_size))"
           in hoare_gen_asmEx)
         apply clarsimp
         apply (rule false_e_explode)
         apply (rule no_exception_conj')
          apply (wp cnode_move_cap_cdl_current_thread)[1]
         apply (rule no_exception_conj')
          apply wp[1]
         apply (rule hoare_strengthen_postE)
           apply (rule_tac R = "(root_tcb_id, tcb_pending_op_slot) \<mapsto>c RestartCap \<and>* R" for R
             in invoke_cnode_move_cap)
          apply clarsimp
          apply (rule conjI[rotated])
           apply (rule sep_any_imp_c'_conj[where cap = RestartCap])
           apply (subst(asm) sep_map_c_asid_reset[where cap' = " (update_cap_data_det data src_cap)"])
           apply (simp add:reset_cap_asid_update_cap_data)
            apply (sep_solve)
          apply sep_solve
         apply (assumption)
        apply (rule_tac Q'="\<lambda>r. < (root_tcb_id, tcb_pending_op_slot) \<mapsto>c RestartCap \<and>* Q >
          and (\<lambda>a. cdl_current_thread a = Some root_tcb_id
                 \<and> cdl_current_domain a = minBound) and K(\<exists>dcap.
           reset_cap_asid dcap = reset_cap_asid src_cap \<and>
           iv = InvokeCNode
           (MoveCall (update_cap_data_det data dcap)
           (cap_object cnode_cap', offset src_index root_size)
           (cap_object dest_root_cap, offset dest_index dest_size)))" for Q
          in hoare_strengthen_post[rotated])
         apply (clarsimp)
         apply (intro conjI)
          apply (sep_solve)
         apply fastforce
        apply (wp set_cap_wp set_cap_all_scheduable_tcbs)
       apply (rule_tac P = "is_cnode_cap c" in hoare_gen_asmEx)
       apply (simp add:decode_invocation_simps)
       apply (rule liftME_wp)
       apply (rule decode_cnode_mutate_rvu)
      apply (simp add:lookup_extra_caps_def Let_def mapME_def sequenceE_def get_index_def)
      apply (rule wp_no_exception_seq)
       apply wp
      apply (rule lookup_cap_and_slot_rvu[where r = root_size])
     apply (rule lookup_cap_and_slot_rvu[where r = root_size])
    apply (rule validE_validE_R)
    apply (rule hoare_pre)
     apply (rule lookup_cap_and_slot_rvu[where r = root_size])
    apply (clarsimp simp:get_index_def)
   defer
   apply (wp hoare_vcg_ball_lift sep_inv_to_all_scheduable_tcbs[OF update_thread_intent_update]
     hoare_vcg_imp_lift hoare_vcg_ex_lift hoare_vcg_all_lift
     update_thread_intent_update update_thread_cnode_at | clarsimp simp:Let_def)+
  apply (clarsimp simp:conj_comms)
  apply (intro conjI impI ballI)[1]
        apply (clarsimp dest!:sep_map_f_tcb_at simp:object_at_def)
       apply (clarsimp simp:user_pointer_at_def Let_def word_bits_def)
       apply (intro conjI,simp+)
       apply (clarsimp simp:sep_conj_assoc)
       apply sep_solve
      apply (clarsimp simp:user_pointer_at_def Let_def word_bits_def)
      apply (intro conjI allI)
       apply (simp add:cnode_non_ep cong: cap_type_bad_cong)+
      apply (clarsimp simp:sep_conj_assoc)
      apply sep_solve
   apply (clarsimp simp:user_pointer_at_def Let_def word_bits_def)
   apply (intro conjI allI)
             apply (fastforce cong: cap_type_bad_cong)+
        apply (drule(1) reset_cap_asid_cnode_cap | simp)+
    apply (clarsimp simp:sep_conj_assoc)
    apply sep_solve
   apply clarsimp
   apply (intro conjI,fastforce cong: cap_type_bad_cong)
     apply (metis cap_object_reset_cap_asid)
    apply (fastforce)
   apply sep_solve
  apply (clarsimp simp:user_pointer_at_def
          Let_def word_bits_def cnode_cap_non_ep_related)
  apply (clarsimp simp:sep_conj_assoc)
  apply fastforce
  done

lemma seL4_CNode_Move_sep:
  "\<lbrace>\<lambda>s. \<guillemotleft>
     root_tcb_id \<mapsto>f tcb \<and>*
     (root_tcb_id, tcb_pending_op_slot) \<mapsto>c - \<and>*

     \<comment> \<open>Root CNode.\<close>
     cnode_id \<mapsto>f CNode (empty_cnode root_size) \<and>*
     \<comment> \<open>Client cnode.\<close>
     dest_id \<mapsto>f CNode (empty_cnode dest_size) \<and>*

     \<comment> \<open>Cap to the root CNode.\<close>
     (root_tcb_id, tcb_cspace_slot) \<mapsto>c cnode_cap \<and>*
     \<comment> \<open>Cap to the client CNode.\<close>
     (cnode_id, dest_root_slot) \<mapsto>c dest_root_cap \<and>*
     \<comment> \<open>Cap that the root task has to its own CNode.\<close>
     (cnode_id, cnode_cap_slot) \<mapsto>c cnode_cap' \<and>*
     \<comment> \<open>Cap to be copied, in the root CNode.\<close>
     (cnode_id, src_slot) \<mapsto>c src_cap \<and>*
     \<comment> \<open>Where to copy the cap (in the client CNode).\<close>
     (dest_id, dest_slot) \<mapsto>c NullCap \<and>*
      R\<guillemotright> s \<and>

     one_lvl_lookup cnode_cap 32 root_size \<and>
     one_lvl_lookup cnode_cap' (unat src_depth) root_size \<and>
     one_lvl_lookup dest_root_cap (unat dest_depth) dest_size \<and>

     \<comment> \<open>We need some word invariants\<close>
     unat src_depth \<le> word_bits \<and>
     0 < unat src_depth \<and>
     unat dest_depth \<le> word_bits \<and>
     0 < unat dest_depth \<and>

     is_tcb tcb \<and>
     is_cnode_cap dest_root_cap \<and>
     is_cnode_cap cnode_cap \<and>
     is_cnode_cap cnode_cap' \<and>
     guard_equal cnode_cap' src_index (unat src_depth) \<and>
     guard_equal cnode_cap src_index (unat src_depth) \<and>
     guard_equal dest_root_cap dest_index (unat dest_depth ) \<and>
     guard_equal cnode_cap src_root word_bits \<and>
     guard_equal cnode_cap dest_root word_bits \<and>

     \<comment> \<open>Caps point to the right objects.\<close>
     cap_object cnode_cap = cnode_id \<and>
     cap_object cnode_cap' = cnode_id \<and>
     cap_object dest_root_cap = dest_id \<and>

     \<comment> \<open>Cap slots match their cptrs.\<close>
     dest_root_slot = offset dest_root root_size \<and>
     cnode_cap_slot = offset src_root root_size \<and>
     src_slot = offset src_index root_size \<and>
     dest_slot = offset dest_index dest_size \<and>

     src_cap \<noteq> NullCap
   \<rbrace>
  seL4_CNode_Move dest_root dest_index dest_depth src_root src_index src_depth
  \<lbrace>\<lambda>_. \<guillemotleft> root_tcb_id \<mapsto>f tcb \<and>*
       cnode_id \<mapsto>f CNode (empty_cnode root_size) \<and>*
       dest_id \<mapsto>f CNode (empty_cnode dest_size) \<and>*
       (root_tcb_id, tcb_cspace_slot) \<mapsto>c cnode_cap \<and>*
       (root_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
       (cnode_id, dest_root_slot) \<mapsto>c dest_root_cap \<and>*
       (cnode_id, cnode_cap_slot) \<mapsto>c cnode_cap' \<and>*
       (cnode_id, src_slot) \<mapsto>c NullCap \<and>*
       (dest_id, dest_slot) \<mapsto>c src_cap \<and>* R\<guillemotright>\<rbrace>"
  apply (simp add:seL4_CNode_Move_def sep_state_projection2_def)
  apply (rule do_kernel_op_pull_back)
   apply (rule hoare_pre)
   apply (rule_tac
               intent_op = "CNodeIntent (CNodeMoveIntent dest_index dest_depth src_index src_depth)"
           and intent_cptr = dest_root
           and intent_extra = "[src_root]" in call_kernel_with_intent_no_fault_helper)
            apply (clarsimp simp:sep_conj_assoc)
            apply (rule hoare_post_imp[OF _ set_cap_wp])
            apply (sep_select 5,assumption)
           apply wp
          apply wp
         apply (rule_tac P = "\<exists>dcap. reset_cap_asid dcap = reset_cap_asid src_cap \<and>
                                iv = InvokeCNode (MoveCall dcap
                                                    (cap_object cnode_cap', offset src_index root_size)
                                                    (cap_object dest_root_cap, offset dest_index dest_size))"
           in hoare_gen_asmEx)
         apply clarsimp
         apply (rule false_e_explode)
         apply (rule no_exception_conj')
          apply (wp cnode_move_cap_cdl_current_thread)[1]
         apply (rule no_exception_conj')
          apply wp[1]
         apply (rule hoare_strengthen_postE)
           apply (rule_tac R = "(root_tcb_id, tcb_pending_op_slot) \<mapsto>c RestartCap \<and>* R" for R
             in invoke_cnode_move_cap)
          apply clarsimp
          apply (rule conjI[rotated])
           apply (rule sep_any_imp_c'_conj[where cap = RestartCap])
           apply (subst(asm) sep_map_c_asid_reset[where cap' = "src_cap"])
           apply simp
           apply (sep_solve)
          apply sep_solve
         apply (assumption)
        apply (rule_tac Q'="\<lambda>r. < (root_tcb_id, tcb_pending_op_slot) \<mapsto>c RestartCap \<and>* Q>
          and (\<lambda>a. cdl_current_thread a = Some root_tcb_id
                 \<and> cdl_current_domain a = minBound) and K(\<exists>dcap.
           reset_cap_asid dcap = reset_cap_asid src_cap \<and>
           iv = InvokeCNode
           (MoveCall dcap
           (cap_object cnode_cap', offset src_index root_size)
           (cap_object dest_root_cap, offset dest_index dest_size)))" for Q
          in hoare_strengthen_post[rotated])
         apply (clarsimp)
           apply (sep_select 3,assumption)
        apply (wp set_cap_wp set_cap_all_scheduable_tcbs)
       apply (rule_tac P = "is_cnode_cap c" in hoare_gen_asmEx)
       apply (simp add:decode_invocation_simps)
       apply (rule liftME_wp)
       apply (rule decode_cnode_move_rvu)
      apply (simp add:lookup_extra_caps_def Let_def
        mapME_def sequenceE_def get_index_def)
      apply (rule wp_no_exception_seq)
       apply wp
      apply (rule lookup_cap_and_slot_rvu[where r = root_size])
     apply (rule lookup_cap_and_slot_rvu[where r = root_size])
    apply (rule validE_validE_R)
    apply (rule hoare_pre)
     apply (rule lookup_cap_and_slot_rvu[where r = root_size])
    apply (clarsimp simp:get_index_def)
   defer
   apply (wp hoare_vcg_ball_lift sep_inv_to_all_scheduable_tcbs[OF update_thread_intent_update]
     hoare_vcg_imp_lift hoare_vcg_ex_lift hoare_vcg_all_lift
     update_thread_intent_update update_thread_cnode_at | clarsimp simp:Let_def)+
  apply (clarsimp simp:conj_comms)
  apply (intro conjI impI ballI)
        apply (clarsimp dest!:sep_map_f_tcb_at simp:object_at_def)
       apply (clarsimp simp:user_pointer_at_def Let_def word_bits_def)
       apply (intro conjI,simp+)
       apply (clarsimp simp:sep_conj_assoc)
       apply sep_solve[1]
      apply (clarsimp simp:user_pointer_at_def Let_def word_bits_def)
      apply (intro conjI allI)
       apply (simp add:cnode_non_ep cong: cap_type_bad_cong)+
      apply (clarsimp simp:sep_conj_assoc)
      apply sep_solve[1]
   apply (clarsimp simp:user_pointer_at_def Let_def word_bits_def)
   apply (intro conjI allI)
             apply (fastforce cong: cap_type_bad_cong)+
        apply (drule(1) reset_cap_asid_cnode_cap | simp | fast)+
    apply (clarsimp simp:sep_conj_assoc)
    apply sep_solve[1]
   apply (clarsimp cong: cap_type_bad_cong)
   apply sep_solve
   apply (simp add:sep_any_map_c_imp)
  apply (clarsimp simp:user_pointer_at_def
          Let_def word_bits_def cnode_cap_non_ep_related)
  apply (clarsimp simp:sep_conj_assoc)
  apply (intro conjI,fastforce+)
  done

(* FIXME, move *)
lemma update_cap_rights_reset_cap_asid:
  "\<lbrakk>reset_cap_asid cap = reset_cap_asid cap'; rights = rights'\<rbrakk>
  \<Longrightarrow> reset_cap_asid (update_cap_rights rights cap) = reset_cap_asid (update_cap_rights rights' cap')"
  by (case_tac cap',auto simp: update_cap_rights_def dest!:reset_cap_asid_simps2 )


(* Slightly different to the rules above.
 * This lemma copies a cap from the root cnode to
 * the root cnode (rather than to a different cnode).
 *)
lemma seL4_CNode_Copy_sep:
  "\<lbrace>\<lambda>s. \<guillemotleft>root_tcb_id \<mapsto>f tcb \<and>*
         (root_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
         cnode_id \<mapsto>f CNode (empty_cnode root_size) \<and>*
         (root_tcb_id, tcb_cspace_slot) \<mapsto>c cnode_cap \<and>*
         (cnode_id, cnode_cap_slot) \<mapsto>c cnode_cap' \<and>*
         (cnode_id, src_slot) \<mapsto>c src_cap \<and>*
         (cnode_id, dest_slot) \<mapsto>c NullCap \<and>* R\<guillemotright>
         s \<and>
        one_lvl_lookup cnode_cap 32 root_size \<and>
        one_lvl_lookup cnode_cap' (unat src_depth) root_size \<and>
        one_lvl_lookup cnode_cap' (unat dest_depth) root_size \<and>
        unat src_depth \<le> word_bits \<and>
        0 < unat src_depth \<and>
        unat dest_depth \<le> word_bits \<and>
        0 < unat dest_depth \<and>
        is_tcb tcb \<and>
        is_cnode_cap cnode_cap \<and>
        is_cnode_cap cnode_cap' \<and>
        guard_equal cnode_cap src_index (unat src_depth) \<and>
        guard_equal cnode_cap' src_index (unat src_depth) \<and>
        guard_equal cnode_cap' dest_index (unat dest_depth) \<and>
        guard_equal cnode_cap src_root word_bits \<and>
        guard_equal cnode_cap dest_root word_bits \<and>
        src_index' = src_index \<and>
        cap_object cnode_cap = cnode_id \<and>
        cap_object cnode_cap' = cnode_id \<and>
        cnode_cap_slot = offset dest_root root_size \<and>
        cnode_cap_slot = offset src_root root_size \<and>
        src_slot = offset src_index root_size \<and>
        dest_slot = offset dest_index root_size \<and>
        cap_has_type src_cap \<and>
        \<not> is_untyped_cap src_cap\<rbrace>
   seL4_CNode_Copy dest_root dest_index dest_depth src_root src_index' src_depth UNIV
   \<lbrace>\<lambda>_. \<guillemotleft>root_tcb_id \<mapsto>f tcb \<and>*
         cnode_id \<mapsto>f CNode (empty_cnode root_size) \<and>*
         (root_tcb_id, tcb_cspace_slot) \<mapsto>c cnode_cap \<and>*
         (root_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
         (cnode_id, cnode_cap_slot) \<mapsto>c cnode_cap' \<and>*
         (cnode_id, src_slot) \<mapsto>c src_cap \<and>*
         (cnode_id, dest_slot) \<mapsto>c derived_cap (update_cap_rights (cap_rights src_cap) src_cap) \<and>* R\<guillemotright>\<rbrace>"
  apply (simp add:seL4_CNode_Copy_def sep_state_projection2_def)
  apply (rule do_kernel_op_pull_back)
  apply (rule hoare_name_pre_state)
  apply (simp add:is_tcb_def split:cdl_object.split_asm)
  apply (rule hoare_pre)
   apply (rule call_kernel_with_intent_allow_error_helper[where check=True,simplified,rotated -1])
                apply assumption
               apply fastforce
              apply (clarsimp simp:sep_conj_assoc)
              apply (rule hoare_post_imp[OF _
              set_cap_wp])
              apply (sep_select 4,assumption)
             apply wp[1]
            apply (rule_tac P = "root_tcb_id \<mapsto>f tcb \<and>*
              (root_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
              cnode_id \<mapsto>f CNode (empty_cnode root_size) \<and>*
              (root_tcb_id, tcb_cspace_slot) \<mapsto>c cnode_cap \<and>*
              (cnode_id, offset src_root root_size) \<mapsto>c cnode_cap' \<and>*
              (cnode_id, offset src_index root_size) \<mapsto>c src_cap \<and>*
              (cnode_id, offset dest_index root_size) \<mapsto>c NullCap \<and>* R"
              in mark_tcb_intent_error_sep_inv)
            apply wp[1]
           apply (rule corrupt_ipc_buffer_sep_inv)
         apply (rule_tac P = "(\<exists>cap''. reset_cap_asid cap'' = reset_cap_asid src_cap
           \<and> iv = InvokeCNode (InsertCall (derived_cap (update_cap_rights (cap_rights cap'') cap''))
           (cap_object cnode_cap', offset src_index root_size)
           (cap_object cnode_cap', offset dest_index root_size)))"
           in hoare_gen_asmEx)
         apply (elim conjE exE)
         apply simp
         apply (rule false_e_explode)
         apply (rule no_exception_conj')
          apply (wp cnode_insert_cap_cdl_current_thread)[1]
         apply (rule no_exception_conj')
          apply wp[1]
         apply (rule hoare_strengthen_postE)
           apply (rule_tac R = "(root_tcb_id, tcb_pending_op_slot) \<mapsto>c RestartCap \<and>* R" for R
             in invoke_cnode_insert_cap')
            apply simp
          apply (rule conjI[rotated])
           apply (rule sep_any_imp_c'_conj[where cap = RestartCap])
           apply (frule sep_map_c_asid_reset[where ptr = "(cnode_id, offset dest_index root_size)"
             ,OF reset_cap_asid_derived[OF update_cap_rights_reset_cap_asid]])
             apply (erule cap_rights_reset_cap_asid)
            apply simp
           apply (sep_solve)
          apply sep_solve
         apply (assumption)
        apply (rule_tac Q'="\<lambda>r. (\<lambda>s. cdl_current_thread s = Some root_tcb_id
                                    \<and> cdl_current_domain s = minBound) and
          < (root_tcb_id, tcb_pending_op_slot) \<mapsto>c RestartCap \<and>* Q> and
          K (\<exists>cap''. reset_cap_asid cap'' = reset_cap_asid src_cap \<and> iv = InvokeCNode
          (InsertCall (derived_cap (update_cap_rights (cap_rights cap'') cap'')) (cnode_id, offset src_index root_size)
          (cnode_id, offset dest_index root_size)))" for Q
          in hoare_strengthen_post[rotated])
          apply (clarsimp simp:cap_of_insert_call_def)
          apply (rule conjI)
           apply (sep_select 2,assumption)
          apply (rule conjI)
           apply (drule reset_cap_asid_cap_type)
           apply (simp)
          apply (rule_tac x = cap'' in exI)
          apply (simp add:reset_cap_asid_derived)
        apply (wp set_cap_wp set_cap_all_scheduable_tcbs)[1]
       apply (rule_tac P = "(fst (c,ref)) = cnode_cap'
         \<and> get_index cs 0 = Some (cnode_cap',(cap_object cnode_cap',
          offset src_root root_size))" in hoare_gen_asmEx)
       apply (clarsimp simp: decode_invocation_simps split_def)
       apply (rule liftME_wp)
       apply wp
       apply (rule decode_cnode_copy_same_parent_rvu[where src_cap = src_cap and cap = cnode_cap'])
          apply (rule refl)
         apply simp
        apply fastforce
       apply clarsimp
       apply (rule_tac x = cap' in exI)
       apply fastforce
      apply (simp add:lookup_extra_caps_def Let_def
        mapME_def sequenceE_def get_index_def)
      apply (rule wp_no_exception_seq)
       apply wp[1]
       apply clarsimp
      apply (rule lookup_cap_and_slot_rvu[where r = root_size])
     apply (rule hoare_pre)
      apply (rule lookup_cap_and_slot_rvu[where r = root_size])
     defer
   apply (clarsimp simp:Let_def)
   apply (wp hoare_vcg_ball_lift sep_inv_to_all_scheduable_tcbs[OF update_thread_intent_update]
     hoare_vcg_imp_lift hoare_vcg_ex_lift hoare_vcg_all_lift is_cnode_cap_guard_equal
     update_thread_intent_update update_thread_cnode_at | clarsimp simp:Let_def)+
  apply (intro conjI impI)
    apply sep_solve
   apply sep_solve
   apply (clarsimp simp:conj_comms)
  apply (thin_tac "(P \<and>* Q) (sep_state_projection sa)" for P Q)
  apply (rule conjI)
   apply (clarsimp simp:user_pointer_at_def Let_def word_bits_def)
   apply (intro conjI,simp+)
   apply sep_solve
  apply (intro conjI impI ballI allI, simp_all)
          apply (frule reset_cap_asid_cnode_cap)
           apply clarsimp
          apply (simp add: cnode_cap_non_ep_related get_index_def)[1]
         apply (clarsimp simp:user_pointer_at_def Let_def word_bits_def sep_conj_assoc)
         apply sep_solve
        apply (fastforce dest!: reset_cap_asid_cnode_cap)+
     apply sep_solve
    apply (drule(1) reset_cap_asid_cnode_cap | simp)+
    apply (clarsimp simp:sep_conj_assoc)
    apply sep_solve
   apply (clarsimp dest!:reset_cap_asid_cnode_cap)
  apply (clarsimp dest!:reset_cap_asid_cnode_cap)
  apply sep_solve
  done

end

