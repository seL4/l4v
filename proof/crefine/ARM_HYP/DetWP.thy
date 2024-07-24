(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory DetWP
imports "Lib.DetWPLib" "CBaseRefine.Include_C"
begin

context begin interpretation Arch . (*FIXME: arch-split*)

lemma det_wp_doMachineOp [wp]:
  "det_wp (\<lambda>_. P) f \<Longrightarrow> det_wp (\<lambda>_. P) (doMachineOp f)"
  apply (simp add: doMachineOp_def split_def)
  apply (rule det_wp_pre, wp)
      apply (erule det_wp_select_f)
     apply wp+
  apply simp
  done

lemma det_wp_loadWordUser [wp]:
  "det_wp (pointerInUserData x and K (is_aligned x 2)) (loadWordUser x)"
  apply (simp add: loadWordUser_def loadWord_def)
  apply (rule det_wp_pre, wp)
    apply (rule det_wp_pre, wp)
    apply clarsimp
    apply assumption
   apply wp
  apply (clarsimp simp: is_aligned_mask)
  done

declare det_wp_liftM[wp]

declare det_wp_assert_opt[wp]

declare det_wp_when[wp]

declare det_wp_unless[wp]

declare word_neq_0_conv [simp del]

lemma det_wp_loadObject_default [wp]:
  "det_wp (\<lambda>s. \<exists>obj. projectKO_opt ko = Some (obj::'a) \<and>
                      is_aligned p (objBits obj) \<and> q = p
                      \<and> case_option True (\<lambda>x. 2 ^ (objBits obj) \<le> x - p) n)
           (loadObject_default p q n ko :: ('a::pre_storable) kernel)"
  apply (simp add: loadObject_default_def split_def projectKO_def
                   alignCheck_def alignError_def magnitudeCheck_def
                   unless_def)
  apply (rule det_wp_pre)
   apply (wp case_option_wp)
  apply (clarsimp simp: is_aligned_mask[symmetric])
  apply simp
  done

lemma det_wp_getTCB [wp]:
  "det_wp (tcb_at' t) (getObject t :: tcb kernel)"
  apply (simp add: getObject_def split_def)
  apply (rule det_wp_pre)
   apply (wp|wpc)+
  apply (clarsimp simp add: obj_at'_def projectKOs objBits_simps
                      cong: conj_cong option.case_cong)
  apply (simp add: lookupAround2_known1)
  apply (rule ps_clear_lookupAround2, assumption+)
    apply simp
   apply (erule is_aligned_no_overflow)
  apply (simp add: word_bits_def)
  done

lemma det_wp_setObject_other [wp]:
  fixes ob :: "'a :: pspace_storable"
  assumes x: "updateObject ob = updateObject_default ob"
  shows "det_wp (obj_at' (\<lambda>k::'a. objBits k = objBits ob) ptr)
                  (setObject ptr ob)"
  apply (simp add: setObject_def x split_def updateObject_default_def
                   magnitudeCheck_def
                   projectKO_def2 alignCheck_def alignError_def)
  apply (rule det_wp_pre)
   apply (wp )
  apply (clarsimp simp: is_aligned_mask[symmetric] obj_at'_def
                        objBits_def[symmetric] projectKOs
                        project_inject lookupAround2_known1)
  apply (erule(1) ps_clear_lookupAround2)
    apply simp
   apply (erule is_aligned_get_word_bits)
    apply (subst add_diff_eq[symmetric])
    apply (erule is_aligned_no_wrap')
    apply simp
   apply simp
  apply fastforce
  done

lemma det_wp_setTCB [wp]:
  "det_wp (tcb_at' t) (setObject t (v::tcb))"
  apply (rule det_wp_pre)
   apply (wp|wpc|simp)+
  apply (clarsimp simp: objBits_simps)
  done

lemma det_wp_threadGet [wp]:
  "det_wp (tcb_at' t) (threadGet f t)"
  apply (simp add: threadGet_def)
  apply (rule det_wp_pre, wp)
  apply simp
  done

lemma det_wp_threadSet [wp]:
  "det_wp (tcb_at' t) (threadSet f t)"
  apply (simp add: threadSet_def)
  apply (rule det_wp_pre, wp)
  apply simp
  done

lemma det_wp_asUser [wp]:
  "det f \<Longrightarrow> det_wp (tcb_at' t) (asUser t f)"
  apply (simp add: asUser_def split_def)
  apply (rule det_wp_pre)
   apply wp
      apply (drule det_wp_det)
      apply (erule det_wp_select_f)
     apply wp+
   apply (rule_tac Q'="\<lambda>_. tcb_at' t" in hoare_post_imp)
    apply simp
   apply wp
  apply simp
  done

lemma wordSize_def':
  "wordSize = 4"
  unfolding wordSize_def wordBits_def
  by (simp add: word_size)

lemma det_wp_getMRs:
  "det_wp (tcb_at' thread and case_option \<top> valid_ipc_buffer_ptr' buffer) (getMRs thread buffer mi)"
  apply (clarsimp simp: getMRs_def)
  apply (rule det_wp_pre)
   apply (wp det_mapM det_getRegister order_refl det_wp_mapM)
   apply (simp add: word_size)
   apply (wp asUser_inv mapM_wp' getRegister_inv)
  apply clarsimp
  apply (rule conjI)
   apply (simp add: pointerInUserData_def wordSize_def' word_size)
   apply (erule valid_ipc_buffer_ptr'D2)
    apply (rule word_mult_less_mono1)
      apply (erule order_le_less_trans)
      apply (simp add: msgMaxLength_def max_ipc_words)
     apply simp
    apply (simp add: max_ipc_words)
   apply (simp add: is_aligned_mult_triv2 [where n = 2, simplified] word_bits_conv)
  apply (erule valid_ipc_buffer_ptr_aligned_2)
  apply (simp add: wordSize_def' is_aligned_mult_triv2 [where n = 2, simplified] word_bits_conv)
  done

end

end
