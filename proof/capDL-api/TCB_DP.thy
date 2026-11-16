(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory TCB_DP
imports
  KHeap_DP
  Invocation_DP
begin

lemma restart_null_wp:
  "\<lbrace> <  (tcb,tcb_pending_op_slot) \<mapsto>c NullCap
     \<and>*  (tcb, tcb_replycap_slot) \<mapsto>c-
     \<and>*  R > \<rbrace>
     restart tcb
  \<lbrace>\<lambda>_.  < (tcb,tcb_pending_op_slot) \<mapsto>c RestartCap
     \<and>* (tcb, tcb_replycap_slot) \<mapsto>c (MasterReplyCap tcb) \<and>* R > \<rbrace>"
  apply (clarsimp simp: restart_def)
  apply (wp set_cap_wp[sep_wand_wp] hoare_pre_cont[where f=chaos])
  apply (frule opt_cap_sep_imp)
  apply (clarsimp simp: is_pending_cap_def dest!: reset_cap_asid_simps2)
  apply sep_solve
  done

lemma not_memory_cap_reset_asid:
   " \<lbrakk> ~is_memory_cap tcb_cap; reset_cap_asid tcb_cap = reset_cap_asid cap\<rbrakk> \<Longrightarrow>
       cap = tcb_cap"
  apply (drule reset_cap_asid_id)
  apply (clarsimp simp: is_memory_cap_def split: cdl_cap.splits)
  done

lemma not_memory_cap_reset_asid':
   " \<lbrakk>reset_cap_asid cap = reset_cap_asid tcb_cap; ~is_memory_cap tcb_cap\<rbrakk> \<Longrightarrow>
       cap = tcb_cap"
  apply (clarsimp simp: not_memory_cap_reset_asid)
  done

lemma tcb_update_thread_slot_wp:
 "\<lbrace><(target_tcb, thread_slot) \<mapsto>c - \<and>* tcb_cap_slot \<mapsto>c TcbCap target_tcb \<and>* R> and K (\<not> is_untyped_cap (ipc_buffer_cap))\<rbrace>
     tcb_update_thread_slot target_tcb tcb_cap_slot thread_slot (ipc_buffer_cap, ipc_buffer_slot)
    \<lbrace>\<lambda>_. <(target_tcb, thread_slot) \<mapsto>c ipc_buffer_cap \<and>* tcb_cap_slot \<mapsto>c TcbCap target_tcb \<and>* R>\<rbrace>, \<lbrace>E\<rbrace>"
  apply (clarsimp simp: tcb_update_thread_slot_def)
  apply (rule hoare_name_pre_state)
  apply (clarsimp)
  apply wp
     apply (wp insert_cap_child_wp)
    apply (wp insert_cap_sibling_wp get_cap_rv)+
  apply (safe)
   apply (sep_solve)
  apply (drule not_memory_cap_reset_asid')
   apply (clarsimp simp: is_memory_cap_def split:cdl_cap.splits)
  apply (clarsimp)
  done

lemma tcb_empty_thread_slot_wpE:
  "\<lbrace><(target_tcb,slot) \<mapsto>c NullCap \<and>* R>\<rbrace>
  tcb_empty_thread_slot target_tcb slot
  \<lbrace>\<lambda>_. <(target_tcb,slot) \<mapsto>c NullCap \<and>* R>\<rbrace>, \<lbrace>E\<rbrace>"
  apply (clarsimp simp: tcb_empty_thread_slot_def | wp hoare_FalseE[where f="delete_cap x" for x])+
  apply (clarsimp dest!:opt_cap_sep_imp simp:reset_cap_asid_simps2)
  done

lemma tcb_update_ipc_buffer_wp':
"\<lbrace>< (ipc_buffer_slot) \<mapsto>c cap \<and>* (target_tcb, tcb_ipcbuffer_slot) \<mapsto>c NullCap \<and>* tcb_cap_slot \<mapsto>c (TcbCap target_tcb) \<and>* R>
    and K (is_frame_cap cap \<and> reset_cap_asid cap = reset_cap_asid ipc_buffer_cap)\<rbrace>
 tcb_update_ipc_buffer target_tcb tcb_cap_slot (ipc_buffer_cap, ipc_buffer_slot)
\<lbrace>\<lambda>_. <(target_tcb, tcb_ipcbuffer_slot) \<mapsto>c ipc_buffer_cap \<and>* tcb_cap_slot \<mapsto>c (TcbCap target_tcb) \<and>* (ipc_buffer_slot) \<mapsto>c cap \<and>* R>\<rbrace>, \<lbrace>E\<rbrace>"
  apply (rule hoare_name_pre_stateE)
  apply (clarsimp simp: tcb_update_ipc_buffer_def)
  apply (wp whenE_wp tcb_update_thread_slot_wp[sep_wandise] get_cap_rv[where cap=cap])
    apply (rule hoare_allI)
    apply (rule hoare_impI)
    apply (clarsimp)
    apply (safe)
     apply (wp)
    apply (clarsimp simp: cdl_same_arch_obj_as_def)
    apply (clarsimp simp: cap_type_def split: cdl_cap.splits dest!:reset_cap_asid_cap_type)
   apply (wp tcb_empty_thread_slot_wpE[sep_wandise])
  apply (clarsimp)
  apply (sep_cancel)+
  apply (safe)
    apply (sep_solve)+
  apply (clarsimp simp: cdl_same_arch_obj_as_def cap_type_def reset_cap_asid_def split: cdl_cap.splits dest!:reset_cap_asid_cap_type)
  done

lemma tcb_update_vspace_root_wp':
 "\<lbrace>< (vrt_slot) \<mapsto>c cap \<and>* (target_tcb, tcb_vspace_slot) \<mapsto>c NullCap \<and>* tcb_cap_slot \<mapsto>c (TcbCap target_tcb) \<and>*  R>
    and K (is_pd_cap cap \<and> reset_cap_asid cap = reset_cap_asid vrt_cap) \<rbrace>
 tcb_update_vspace_root target_tcb tcb_cap_slot (vrt_cap, vrt_slot)
\<lbrace>\<lambda>_. < (target_tcb, tcb_vspace_slot) \<mapsto>c vrt_cap \<and>* tcb_cap_slot \<mapsto>c (TcbCap target_tcb) \<and>* (vrt_slot) \<mapsto>c cap \<and>* R>\<rbrace>, \<lbrace>E\<rbrace>"
  apply (rule hoare_name_pre_stateE)
  apply (clarsimp simp: tcb_update_vspace_root_def)
  apply (wp whenE_wp tcb_update_thread_slot_wp[sep_wand_side_wpE'] get_cap_rv)+
   apply (wp hoare_vcg_conj_liftE1)
    apply (wp tcb_empty_thread_slot_wpE[sep_wand_wpE], (clarsimp simp: sep_conj_assoc | sep_solve) +)
   apply (wp tcb_empty_thread_slot_wpE[sep_wand_wpE], (clarsimp simp: sep_conj_assoc | sep_solve) +)
  apply (repeat_new \<open>rule conjI | clarsimp simp: sep_conj_assoc | sep_cancel\<close>)
   apply (drule reset_cap_asid_cap_type)+
   apply (clarsimp simp: cap_type_def split: cdl_cap.splits )
  apply (clarsimp simp: sep_conj_assoc | sep_cancel+)+
  apply (clarsimp simp: cdl_same_arch_obj_as_def cap_type_def split: cdl_cap.splits dest!:reset_cap_asid_cap_type)
done



lemma is_cnode_cap_not_memory_cap:
  "is_cnode_cap cap \<Longrightarrow> \<not> is_memory_cap cap"
  by (clarsimp simp: cap_type_def is_memory_cap_def split: cdl_cap.splits)

lemma tcb_update_cspace_root_wp:
 "\<lbrace>< (crt_slot) \<mapsto>c cap \<and>* (target_tcb, tcb_cspace_slot) \<mapsto>c NullCap \<and>* tcb_cap_slot \<mapsto>c (TcbCap target_tcb) \<and>*  R>
   and  K (\<not> is_untyped_cap (crt_cap) \<and> is_cnode_cap cap \<and> cap_object cap = cap_object crt_cap)\<rbrace>
 tcb_update_cspace_root target_tcb tcb_cap_slot (crt_cap, crt_slot)
\<lbrace>\<lambda>_. < (target_tcb, tcb_cspace_slot) \<mapsto>c crt_cap \<and>* tcb_cap_slot \<mapsto>c (TcbCap target_tcb) \<and>* (crt_slot) \<mapsto>c cap \<and>* R>\<rbrace>, \<lbrace>E\<rbrace>"
  apply (rule hoare_name_pre_stateE)
  apply (clarsimp simp: tcb_update_cspace_root_def cong:cap_type_bad_cong)
  apply (wpsimp wp: whenE_wp tcb_update_thread_slot_wp[sep_wand_side_wpE] get_cap_rv
                    hoare_vcg_conj_liftE1)
    apply (wpsimp wp: tcb_empty_thread_slot_wpE[sep_wand_wpE] simp: sep_conj_assoc)
   apply (wpsimp wp: hoare_vcg_all_liftE_R[THEN hoare_vcg_conj_elimE[rotated]]
                     hoare_vcg_const_imp_liftE_R
                     tcb_empty_thread_slot_wpE[sep_wand_wpE]
          split_del: if_split simp: if_apply_def2)
  apply (clarsimp)
  apply (repeat_new \<open>rule conjI | clarsimp simp: sep_conj_assoc | sep_cancel\<close>)
  apply (drule not_memory_cap_reset_asid')
   apply (erule is_cnode_cap_not_memory_cap)
  apply clarsimp
  done

lemma sep_map_c_asid_reset'': "\<lbrakk>(ptr \<mapsto>c cap) s ; reset_cap_asid cap' = reset_cap_asid cap\<rbrakk> \<Longrightarrow>  (ptr \<mapsto>c cap') s"
  apply (clarsimp dest!: sep_map_c_asid_reset[where ptr=ptr])
done

lemma invoke_tcb_threadcontrol_wp':
  "(\<exists>x y z. faultep = Some fltep \<and>
  croot = Some x \<and>  vroot = Some y \<and> ipc_buffer = Some z \<and>
  crt_slot = snd x \<and> vrt_slot = snd y \<and> ipcbuff_slot = snd z \<and>
  is_pd_cap vrt_cap \<and> is_frame_cap ipcbuff_cap \<and>
  is_cnode_cap crt_cap' \<and>
  is_cnode_cap crt_cap \<and> cap_object crt_cap = cap_object crt_cap' \<and>
  reset_cap_asid crt_cap = reset_cap_asid (fst x) \<and>
  reset_cap_asid vrt_cap = reset_cap_asid (fst y) \<and>
  reset_cap_asid ipcbuff_cap = reset_cap_asid (fst z) ) \<Longrightarrow>
  \<lbrace>       < target_tcb \<mapsto>f Tcb tcb \<and>*
         (vrt_slot) \<mapsto>c vrt_cap  \<and>*
         (target_tcb, tcb_cspace_slot) \<mapsto>c NullCap \<and>*
         tcb_cap_slot \<mapsto>c TcbCap target_tcb \<and>*
         (crt_slot) \<mapsto>c crt_cap'  \<and>*
         (target_tcb, tcb_vspace_slot) \<mapsto>c NullCap \<and>*
         (ipcbuff_slot) \<mapsto>c ipcbuff_cap \<and>*
         (target_tcb, tcb_ipcbuffer_slot) \<mapsto>c NullCap \<and>*
         R> \<rbrace>
 invoke_tcb  (ThreadControl target_tcb tcb_cap_slot faultep croot vroot ipc_buffer)
\<lbrace>\<lambda>_.  <(target_tcb, tcb_ipcbuffer_slot) \<mapsto>c ipcbuff_cap \<and>*
       tcb_cap_slot \<mapsto>c (TcbCap target_tcb)   \<and>*
       (ipcbuff_slot) \<mapsto>c ipcbuff_cap                    \<and>*
       (target_tcb, tcb_vspace_slot) \<mapsto>c vrt_cap    \<and>*
       (vrt_slot) \<mapsto>c vrt_cap                       \<and>*
       (target_tcb, tcb_cspace_slot) \<mapsto>c crt_cap    \<and>*
       (crt_slot) \<mapsto>c crt_cap' \<and>*
       target_tcb \<mapsto>f Tcb (tcb\<lparr>cdl_tcb_fault_endpoint := fltep\<rparr>) \<and>* R >\<rbrace>, \<lbrace>E\<rbrace>"
  apply (rule hoare_name_pre_stateE)
  apply (clarsimp simp: invoke_tcb_def)
  apply (wp set_cdl_tcb_fault_endpoint_wp[sep_wand_wp] tcb_update_ipc_buffer_wp'[sep_wand_side_wpE]
    tcb_update_vspace_root_wp'[sep_wand_side_wpE] tcb_update_cspace_root_wp[where cap = crt_cap',sep_wand_side_wpE]
     | clarsimp | fastforce)+
    apply (clarsimp cong:cap_type_bad_cong)
   apply wp
   apply (wp set_cdl_tcb_fault_endpoint_wp[sep_wand_wp] tcb_update_ipc_buffer_wp'[sep_wand_side_wpE]
     tcb_update_vspace_root_wp'[sep_wand_side_wpE] tcb_update_cspace_root_wp[where cap = crt_cap,sep_wand_side_wpE]
      | clarsimp | fastforce)+
  apply (frule sep_map_c_asid_reset[where ptr=vrt_slot and cap=vrt_cap])
  apply (frule sep_map_c_asid_reset[where ptr="(target_tcb, tcb_vspace_slot)" and cap=vrt_cap])
  apply (frule sep_map_c_asid_reset[where ptr="(target_tcb,tcb_ipcbuffer_slot)" and cap=ipcbuff_cap])
  apply (clarsimp simp: sep_conj_assoc pred_conj_def cong:cap_type_bad_cong
     | sep_cancel | safe)+
  apply (frule sep_map_c_asid_reset[where ptr="(target_tcb,tcb_cspace_slot)" and cap=crt_cap])
  apply simp
done

lemma decode_tcb_invocation_wp[wp]:
"\<lbrace>P\<rbrace>
decode_tcb_invocation cap cap_ref caps (TcbConfigureIntent fault_ep cspace_root_data vspace_root_data buffer)
\<lbrace>\<lambda>_. P\<rbrace>, \<lbrace>\<lambda>_. P\<rbrace>"
  apply (clarsimp simp: decode_tcb_invocation_def)
  apply wp
  apply (clarsimp)
done

lemma throw_on_none_rvR:
 "\<lbrace>\<lambda>s. case x of None \<Rightarrow> True | Some y \<Rightarrow> P y s\<rbrace>
    throw_on_none x
  \<lbrace>P\<rbrace>, -"
  apply (clarsimp simp: throw_on_none_def split:option.splits)
  apply (safe, wp+)
done

lemma decode_invocation_tcb_rv':
"\<lbrace>\<lambda>s. P (
     ThreadControl
        (cap_object cap)
         cap_ref
        (Some fault_ep)
        (Some (cdl_update_cnode_cap_data croot_cap cspace_root_data, croot_slot))
        (Some (vroot_cap, vroot_slot))
        (Some ((reset_mem_mapping ipcbuff_cap),ipcbuff_slot))) s \<and>
   caps = [(croot_cap,croot_slot), (vroot_cap,vroot_slot), (ipcbuff_cap, ipcbuff_slot)]@xs \<and>
   cap_has_object cap \<and> buffer \<noteq> 0 \<rbrace>
decode_tcb_invocation cap cap_ref caps (TcbConfigureIntent fault_ep cspace_root_data vspace_root_data buffer)
\<lbrace>P\<rbrace>, -"
  apply (clarsimp simp: decode_tcb_invocation_def)
  apply wp
      apply (wp throw_on_none_rvR)+
  apply (safe)
  apply (clarsimp simp: get_index_def)
done

lemma decode_tcb_invocation_simps:
  "is_tcb_cap cap \<Longrightarrow>
  decode_invocation cap cap_ref caps (TcbIntent intent) = liftME InvokeTcb (decode_tcb_invocation cap cap_ref caps intent)"
  apply (clarsimp simp: decode_invocation_def)
  apply (clarsimp simp: decode_invocation_def
     get_tcb_intent_def throw_opt_def cap_type_def
     split:cdl_cap.splits )
done

lemma decode_invocation_tcb_rv'':
" \<lbrakk>buffer \<noteq> 0\<rbrakk> \<Longrightarrow>
  \<lbrace>\<lambda>s.\<exists>croot_cap vroot_cap ipcbuff_cap.
      is_tcb_cap cap \<and>
      caps = [(croot_cap,croot_slot), (vroot_cap,vroot_slot), (ipcbuff_cap, ipcbuff_slot)]@xs \<and>
      cap_has_object cap \<and>
      P (InvokeTcb $
        ThreadControl
        (cap_object cap)
         cap_ref
        (Some fault_ep)
        (Some (cdl_update_cnode_cap_data (croot_cap) cspace_root_data, croot_slot))
        (Some (vroot_cap, vroot_slot))
        (Some ((reset_mem_mapping ipcbuff_cap),ipcbuff_slot))) s\<rbrace>
  decode_invocation cap cap_ref caps (TcbIntent $ TcbConfigureIntent fault_ep cspace_root_data vspace_root_data buffer)
  \<lbrace>P\<rbrace>, -"
  apply (clarsimp)
  apply (unfold validE_def validE_R_def)
  apply (rule hoare_name_pre_state)
  apply (unfold validE_def[symmetric] validE_R_def[symmetric])
  apply (clarsimp simp: decode_tcb_invocation_simps cap_type_def)
  apply (wp)
  apply (clarsimp simp: comp_def)
  apply (wp decode_invocation_tcb_rv')
  apply (clarsimp simp: split_def)
  apply (safe)
         apply fastforce+
done

lemma tcb_empty_thread_slot_wp_inv: "\<lbrace><(target_tcb,slot) \<mapsto>c NullCap \<and>* R> and P \<rbrace> tcb_empty_thread_slot target_tcb slot \<lbrace>\<lambda>_. P\<rbrace> "
  apply (simp add:tcb_empty_thread_slot_def whenE_def | wp)+
    apply (rule valid_validE)
    apply (rule hoare_pre_cont)
   apply simp
   apply wp+
  apply (clarsimp dest!:opt_cap_sep_imp simp:reset_cap_asid_simps2)
  done


lemma sep_map_anyD:
  "(m p e \<and>* P ) s \<Longrightarrow> (sep_any m p \<and>* P) s"
  by sep_solve

lemma invoke_tcb_ThreadControl_cur_thread:
  "\<lbrakk>\<forall>vcap capref. (vroot = Some (vcap,capref)) \<longrightarrow> cap_type vcap \<noteq> Some UntypedType
   ;\<forall>ccap capref. (croot = Some (ccap,capref)) \<longrightarrow> cap_type ccap \<noteq> Some UntypedType \<rbrakk>
   \<Longrightarrow> \<lbrace>(\<lambda>s. P (cdl_current_thread s))  and
    <(target_tcb, tcb_cspace_slot) \<mapsto>c NullCap \<and>*
     (target_tcb, tcb_vspace_slot) \<mapsto>c NullCap \<and>*
     (target_tcb, tcb_ipcbuffer_slot) \<mapsto>c NullCap \<and>*
     target_tcb \<mapsto>f Tcb tcb \<and>* R >
  \<rbrace> invoke_tcb (ThreadControl target_tcb tcb_cap_slot faultep croot vroot ipc_buffer)
  \<lbrace>\<lambda>_ s. P  (cdl_current_thread s) \<rbrace>"
  including no_pre
  apply (simp add:invoke_tcb_def comp_def)
    apply (wp whenE_wp
      tcb_empty_thread_slot_wp_inv
      [where R = "(target_tcb, tcb_vspace_slot) \<mapsto>c -
        \<and>* (target_tcb,tcb_cspace_slot) \<mapsto>c -
        \<and>* target_tcb \<mapsto>f - \<and>* R"] hoare_drop_imps
      |wpc
      |simp add:tcb_update_ipc_buffer_def
    tcb_update_thread_slot_def)+
    apply (clarsimp simp:conj_comms)
    apply (rule hoare_strengthen_postE[OF valid_validE,rotated],assumption)
     apply (fastforce split:option.splits)
     apply (wp hoare_drop_imps whenE_wp
       | simp add: tcb_update_vspace_root_def tcb_update_thread_slot_def)+
         apply (rule hoare_post_imp[OF _  insert_cap_child_wp])
        apply (sep_erule_concl refl_imp sep_any_imp, assumption)
       apply wp
         apply (rule hoare_post_imp[OF _  insert_cap_sibling_wp])
       apply (sep_erule_concl refl_imp sep_any_imp)+
       apply (assumption)
       apply (rule_tac Q'="\<lambda>r s. P (cdl_current_thread s)
         \<and> (<(target_tcb, tcb_vspace_slot) \<mapsto>c -
         \<and>* (target_tcb, tcb_cspace_slot) \<mapsto>c -
         \<and>* (target_tcb, tcb_ipcbuffer_slot) \<mapsto>c NullCap
         \<and>* target_tcb \<mapsto>f - \<and>* R> s)
         " in hoare_post_imp)
       apply (clarsimp simp:sep_conj_ac)
       apply wp+
     apply (rule_tac Q'="\<lambda>r s. P (cdl_current_thread s)
       \<and> (<(target_tcb, tcb_vspace_slot) \<mapsto>c -
       \<and>* (target_tcb,tcb_cspace_slot) \<mapsto>c -
       \<and>* (target_tcb, tcb_ipcbuffer_slot) \<mapsto>c NullCap
       \<and>* target_tcb \<mapsto>f - \<and>* R> s)
       " in hoare_strengthen_postE[rotated -1])
       apply assumption
      apply (wp tcb_empty_thread_slot_wp_inv)
     apply clarsimp
     apply (sep_solve)
    apply (wp hoare_drop_imps whenE_wp
      | simp add: tcb_update_vspace_root_def tcb_update_thread_slot_def)+
        apply (rule hoare_post_imp[OF _  insert_cap_child_wp])
        apply (sep_select 2)
        apply (drule sep_map_c_any)
        apply assumption
       apply wp
       apply (rule hoare_post_imp[OF _ insert_cap_sibling_wp])
       apply (sep_select 2)
       apply (drule sep_map_c_any)
       apply assumption
      apply (rule_tac Q'="\<lambda>r s. P (cdl_current_thread s)
        \<and> (<(target_tcb, tcb_vspace_slot) \<mapsto>c -
        \<and>* (target_tcb,tcb_cspace_slot) \<mapsto>c -
        \<and>* (target_tcb, tcb_ipcbuffer_slot) \<mapsto>c NullCap
        \<and>* target_tcb \<mapsto>f -
        \<and>* R> s)
        " in hoare_post_imp)
       apply (clarsimp simp:sep_conj_ac)
      apply wp+
     apply (rule_tac Q'="\<lambda>r s. P (cdl_current_thread s)
       \<and> (<(target_tcb, tcb_vspace_slot) \<mapsto>c -
       \<and>* (target_tcb, tcb_cspace_slot) \<mapsto>c -
       \<and>* (target_tcb, tcb_ipcbuffer_slot) \<mapsto>c NullCap
       \<and>* target_tcb \<mapsto>f - \<and>* R> s)
       " in hoare_strengthen_postE[rotated -1])
      apply assumption
     apply (wp tcb_empty_thread_slot_wp_inv)
    apply clarsimp
    apply sep_solve
    apply (rule_tac Q'="\<lambda>r s. P (cdl_current_thread s)
       \<and> (<(target_tcb, tcb_vspace_slot) \<mapsto>c NullCap
      \<and>* (target_tcb,tcb_cspace_slot) \<mapsto>c -
      \<and>* (target_tcb, tcb_ipcbuffer_slot) \<mapsto>c NullCap
      \<and>* target_tcb \<mapsto>f - \<and>* R> s)
       " in hoare_strengthen_postE[rotated -1])
     apply assumption
    apply (wp whenE_wp |wpc|simp add:tcb_update_cspace_root_def)+
      apply (wp hoare_drop_imps whenE_wp
        | simp add: tcb_update_vspace_root_def tcb_update_thread_slot_def)+
        apply (rule hoare_post_imp[OF _  insert_cap_child_wp])
        apply (sep_schem)
       apply wp
       apply (rule hoare_post_imp[OF _ insert_cap_sibling_wp], sep_schem)
      apply (rule_tac Q'="\<lambda>r s. P (cdl_current_thread s)
        \<and> (<(target_tcb, tcb_vspace_slot) \<mapsto>c NullCap
        \<and>* (target_tcb,tcb_cspace_slot) \<mapsto>c -
        \<and>* (target_tcb, tcb_ipcbuffer_slot) \<mapsto>c NullCap
        \<and>* target_tcb \<mapsto>f - \<and>* R> s)
        \<and> cap_type (fst x2) \<noteq> Some UntypedType" in hoare_post_imp)
       apply (clarsimp simp:sep_conj_ac, sep_solve)
      apply wp+
     apply (rule_tac P = "cap_type (fst x2) \<noteq> Some UntypedType" in hoare_gen_asmEx)
     apply (rule_tac Q'="\<lambda>r s. P (cdl_current_thread s)
       \<and> (<(target_tcb, tcb_vspace_slot) \<mapsto>c NullCap
       \<and>* (target_tcb, tcb_cspace_slot) \<mapsto>c -
       \<and>* (target_tcb, tcb_ipcbuffer_slot) \<mapsto>c NullCap
       \<and>* target_tcb \<mapsto>f - \<and>* R> s)
       " in hoare_strengthen_postE[rotated -1])
      apply clarsimp
      apply assumption
     apply (wp tcb_empty_thread_slot_wp_inv)
    apply clarsimp
   apply clarsimp
   apply (intro conjI impI impI allI)
   apply sep_solve+
  apply (rule hoare_pre)
   apply (wp|wpc|simp)+
   apply (rule_tac Q'="\<lambda>r s. P (cdl_current_thread s)
          \<and> (<(target_tcb, tcb_vspace_slot) \<mapsto>c NullCap
          \<and>* (target_tcb,tcb_cspace_slot) \<mapsto>c NullCap
          \<and>* (target_tcb, tcb_ipcbuffer_slot) \<mapsto>c NullCap
          \<and>* target_tcb \<mapsto>f - \<and>* R> s)" in hoare_post_imp)
    apply clarsimp
    apply (sep_select_asm 2)
    apply (intro conjI impI allI)
          apply sep_solve
         apply assumption+
    apply sep_solve
   apply wp
   apply (rule hoare_post_imp[OF _ set_cdl_tcb_fault_endpoint_wp[where tcb = tcb]])
    apply (drule sep_map_anyD)
    apply (sep_select 4)
    apply assumption
   apply clarsimp
   apply (auto, (sep_solve)+)
   done

lemma update_thread_current_thread_inv[wp]:
  "\<lbrace>\<lambda>s. P (cdl_current_thread s)\<rbrace>
  update_thread target_tcb (cdl_tcb_fault_endpoint_update (\<lambda>_. x)) \<lbrace>\<lambda>_ s. P (cdl_current_thread s)\<rbrace>"
  apply (clarsimp simp: update_thread_def)
  apply (wp)
   apply (case_tac t)
           apply (clarsimp)+
         apply (wp)
        apply (clarsimp)+
  apply (wp)
  apply (clarsimp)
done

lemma decode_invocation_tcb_current_thread_inv[wp]:
 "\<lbrace>\<lambda>s. is_tcb_cap c \<and> P (cdl_current_thread s)\<rbrace>
       decode_invocation c (a, b) cs
        (TcbIntent (TcbConfigureIntent fault_ep cspace_root_data vspace_root_data buffer_addr))
  \<lbrace>\<lambda>_ s. P (cdl_current_thread s) \<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp: decode_tcb_invocation_simps)
  apply (wp)
  apply (clarsimp simp: comp_def)
  apply (wp)
  apply (clarsimp)
done

lemma is_tcb_cap_is_object:  "is_tcb_cap tcb_cap  \<Longrightarrow> TcbCap (cap_object tcb_cap) = tcb_cap"
  by (clarsimp simp: cap_type_def split: cdl_cap.splits)


lemma reset_cap_asid_mem_mapping:
  "\<lbrakk>is_frame_cap buffer_frame_cap; reset_cap_asid xc = reset_cap_asid buffer_frame_cap\<rbrakk> \<Longrightarrow>
    reset_cap_asid buffer_frame_cap = reset_cap_asid (reset_mem_mapping xc)"
  apply (clarsimp simp: cap_type_def split:cdl_cap.splits)
  apply (clarsimp simp: reset_cap_asid_def split:cdl_cap.splits)
done

lemma split_error_validE: "\<lbrakk>\<And>P. \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. P\<rbrace>, \<lbrace>\<lambda>_. P\<rbrace>; \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, - \<rbrakk> \<Longrightarrow> \<lbrace>P and E\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>\<lambda>_. E\<rbrace>"
  apply (clarsimp simp: valid_def validE_def validE_R_def split: sum.splits)
  apply (safe, fastforce+)
done

lemma "\<lbrakk><cur_thread \<mapsto>f root_tcb \<and>* R> s; is_tcb root_tcb \<rbrakk> \<Longrightarrow> \<exists>x. <cur_thread \<mapsto>f Tcb x \<and>* R> s"
  apply (clarsimp simp: is_tcb_def split: cdl_object.splits)
  apply (rule)
  apply (sep_solve)
done

lemma cap_object_update_cnode_data[simp]:
  "cap_object (cdl_update_cnode_cap_data cap data) = cap_object cap"
  by (simp add:cdl_update_cnode_cap_data_def cap_object_def
    split:cdl_cap.splits)

lemma reset_cap_asid_tcb:
  "is_tcb_cap cap \<Longrightarrow> reset_cap_asid cap = cap"
  by (simp add:cap_type_def split:cdl_cap.splits)

definition
  "invoke_tcb_cspace tinv = (case tinv of (InvokeTcb
             (ThreadControl obj slot (Some fault_ep) (Some x) (Some y) (Some z)))
  \<Rightarrow> x)"

definition
  "invoke_tcb_vspace tinv = (case tinv of (InvokeTcb
             (ThreadControl obj slot (Some fault_ep) (Some x) (Some y) (Some z)))
  \<Rightarrow> y)"

definition
  "invoke_tcb_ipcbuffer tinv = (case tinv of (InvokeTcb
             (ThreadControl obj slot (Some fault_ep) (Some x) (Some y) (Some z)))
  \<Rightarrow> z)"


lemma cap_typeD:
  "is_tcb_cap tcb_cap \<Longrightarrow> \<exists>x. tcb_cap = TcbCap x"
  by (simp add:cap_type_def split:cdl_cap.split_asm)

lemma invoke_tcb_ThreadControl_cdl_current_domain:
  "\<lbrakk>\<forall>vcap capref. (vroot = Some (vcap,capref)) \<longrightarrow> cap_type vcap \<noteq> Some UntypedType
   ;\<forall>ccap capref. (croot = Some (ccap,capref)) \<longrightarrow> cap_type ccap \<noteq> Some UntypedType \<rbrakk>
   \<Longrightarrow> \<lbrace>(\<lambda>s. P (cdl_current_domain s))  and
    <(target_tcb, tcb_cspace_slot) \<mapsto>c NullCap \<and>*
     (target_tcb, tcb_vspace_slot) \<mapsto>c NullCap \<and>*
     (target_tcb, tcb_ipcbuffer_slot) \<mapsto>c NullCap \<and>*
     target_tcb \<mapsto>f Tcb tcb \<and>* R >
  \<rbrace> invoke_tcb (ThreadControl target_tcb tcb_cap_slot faultep croot vroot ipc_buffer)
  \<lbrace>\<lambda>_ s. P  (cdl_current_domain s) \<rbrace>"
  apply (simp add:invoke_tcb_def comp_def)
    apply (wp whenE_wp
      tcb_empty_thread_slot_wp_inv
      [where R = "(target_tcb, tcb_vspace_slot) \<mapsto>c -
        \<and>* (target_tcb,tcb_cspace_slot) \<mapsto>c -
        \<and>* target_tcb \<mapsto>f - \<and>* R"] hoare_drop_imps
      |wpc
      |simp add:tcb_update_ipc_buffer_def
    tcb_update_thread_slot_def)+
    apply (clarsimp simp:conj_comms)
    apply (rule hoare_strengthen_postE[OF valid_validE,rotated],assumption)
     apply (fastforce split:option.splits)
     apply (wp hoare_drop_imps whenE_wp
       | simp add: tcb_update_vspace_root_def tcb_update_thread_slot_def)+
         apply (rule hoare_post_imp[OF _  insert_cap_child_wp])
         apply (sep_schem)
       apply wp
         apply (rule hoare_post_imp[OF _  insert_cap_sibling_wp])
       apply (sep_schem)
       apply (rule_tac Q'="\<lambda>r s. P (cdl_current_domain s)
         \<and> (<(target_tcb, tcb_vspace_slot) \<mapsto>c -
         \<and>* (target_tcb, tcb_cspace_slot) \<mapsto>c -
         \<and>* (target_tcb, tcb_ipcbuffer_slot) \<mapsto>c NullCap
         \<and>* target_tcb \<mapsto>f - \<and>* R> s)
         " in hoare_post_imp)
         apply (clarsimp simp: sep_conj_ac, sep_solve)
        apply wp+
      apply (rule_tac Q'="\<lambda>r s. P (cdl_current_domain s)
       \<and> (<(target_tcb, tcb_vspace_slot) \<mapsto>c -
       \<and>* (target_tcb,tcb_cspace_slot) \<mapsto>c -
       \<and>* (target_tcb, tcb_ipcbuffer_slot) \<mapsto>c NullCap
       \<and>* target_tcb \<mapsto>f - \<and>* R> s)
       " in hoare_strengthen_postE[rotated -1])
        apply assumption
       apply (wp tcb_empty_thread_slot_wp_inv)
      apply clarsimp
      apply (sep_solve)
     apply (wp hoare_drop_imps whenE_wp
      | simp add: tcb_update_vspace_root_def tcb_update_thread_slot_def)+
         apply (rule hoare_post_imp[OF _  insert_cap_child_wp])
         apply (sep_select 2)
         apply (drule sep_map_c_any)
         apply assumption
        apply wp
        apply (rule hoare_post_imp[OF _ insert_cap_sibling_wp])
        apply (sep_select 2)
        apply (drule sep_map_c_any)
        apply assumption
       apply (rule_tac Q'="\<lambda>r s. P (cdl_current_domain s)
        \<and> (<(target_tcb, tcb_vspace_slot) \<mapsto>c -
        \<and>* (target_tcb,tcb_cspace_slot) \<mapsto>c -
        \<and>* (target_tcb, tcb_ipcbuffer_slot) \<mapsto>c NullCap
        \<and>* target_tcb \<mapsto>f -
        \<and>* R> s)
        " in hoare_post_imp)
        apply (clarsimp simp:sep_conj_ac)
       apply wp+
     apply (rule_tac Q'="\<lambda>r s. P (cdl_current_domain s)
       \<and> (<(target_tcb, tcb_vspace_slot) \<mapsto>c -
       \<and>* (target_tcb, tcb_cspace_slot) \<mapsto>c -
       \<and>* (target_tcb, tcb_ipcbuffer_slot) \<mapsto>c NullCap
       \<and>* target_tcb \<mapsto>f - \<and>* R> s)
       " in hoare_strengthen_postE[rotated -1])
       apply assumption
      apply (wp tcb_empty_thread_slot_wp_inv)
     apply clarsimp
     apply sep_solve
    apply (rule_tac Q'="\<lambda>r s. P (cdl_current_domain s)
       \<and> (<(target_tcb, tcb_vspace_slot) \<mapsto>c NullCap
      \<and>* (target_tcb,tcb_cspace_slot) \<mapsto>c -
      \<and>* (target_tcb, tcb_ipcbuffer_slot) \<mapsto>c NullCap
      \<and>* target_tcb \<mapsto>f - \<and>* R> s)
       " in hoare_strengthen_postE[rotated -1])
      apply assumption
     apply (wp whenE_wp |wpc|simp add:tcb_update_cspace_root_def)+
       apply (wp hoare_drop_imps whenE_wp
        | simp add: tcb_update_vspace_root_def tcb_update_thread_slot_def)+
         apply (rule hoare_post_imp[OF _  insert_cap_child_wp])
         apply (sep_select 2)
         apply (drule sep_map_c_any)
         apply assumption
        apply wp
        apply (rule hoare_post_imp[OF _ insert_cap_sibling_wp])
        apply (sep_select 2)
        apply (drule sep_map_c_any)
        apply assumption
       apply (rule_tac Q'="\<lambda>r s. P (cdl_current_domain s)
        \<and> (<(target_tcb, tcb_vspace_slot) \<mapsto>c NullCap
        \<and>* (target_tcb,tcb_cspace_slot) \<mapsto>c -
        \<and>* (target_tcb, tcb_ipcbuffer_slot) \<mapsto>c NullCap
        \<and>* target_tcb \<mapsto>f - \<and>* R> s)
        \<and> cap_type (fst x2) \<noteq> Some UntypedType" in hoare_post_imp)
        apply (clarsimp simp:sep_conj_ac)
       apply wp+
     apply (rule_tac P = "cap_type (fst x2) \<noteq> Some UntypedType" in hoare_gen_asmEx)
     apply (rule_tac Q'="\<lambda>r s. P (cdl_current_domain s)
       \<and> (<(target_tcb, tcb_vspace_slot) \<mapsto>c NullCap
       \<and>* (target_tcb, tcb_cspace_slot) \<mapsto>c -
       \<and>* (target_tcb, tcb_ipcbuffer_slot) \<mapsto>c NullCap
       \<and>* target_tcb \<mapsto>f - \<and>* R> s)
       " in hoare_strengthen_postE[rotated -1])
       apply clarsimp
       apply assumption
      apply (wp tcb_empty_thread_slot_wp_inv)
     apply clarsimp
    apply clarsimp
    apply (intro conjI impI impI allI)
                 apply sep_solve+
   apply (rule hoare_pre)
    apply (wp|wpc|simp)+
    apply (rule_tac Q'="\<lambda>r s. P (cdl_current_domain s)
          \<and> (<(target_tcb, tcb_vspace_slot) \<mapsto>c NullCap
          \<and>* (target_tcb,tcb_cspace_slot) \<mapsto>c NullCap
          \<and>* (target_tcb, tcb_ipcbuffer_slot) \<mapsto>c NullCap
          \<and>* target_tcb \<mapsto>f - \<and>* R> s)" in hoare_post_imp)
     apply clarsimp
     apply (sep_select_asm 2)
     apply (intro conjI impI allI)
         apply sep_solve
        apply assumption+
     apply sep_solve
    apply wp
    apply (rule hoare_post_imp[OF _ set_cdl_tcb_fault_endpoint_wp[where tcb = tcb]])
    apply (drule sep_map_anyD)
    apply (sep_select 4)
    apply assumption+
  apply clarsimp
  apply (auto, sep_solve+)
  done

lemma TCB_Configure_wp:
assumes unify: "cnode_id = cap_object cnode_cap \<and>
     tcb_id = cap_object tcb_cap \<and>
     offset tcb_root root_size = tcb_cap_slot \<and>
     offset cspace_root root_size = cspace_slot \<and>
     offset vspace_root root_size = vspace_slot \<and>
     offset buffer_frame_root root_size =  buffer_frame_slot"
shows
  "\<lbrakk>
     is_pd_cap vspace_cap; is_frame_cap buffer_frame_cap;
     is_cnode_cap cspace_cap;
     is_cnode_cap cnode_cap;
     buffer_addr \<noteq> 0;
     cap_has_object tcb_cap;
    \<comment> \<open>Caps point to the right objects.\<close>
     one_lvl_lookup cnode_cap word_bits root_size;
     guard_equal cnode_cap tcb_root word_bits;
     guard_equal cnode_cap cspace_root word_bits;
     guard_equal cnode_cap vspace_root word_bits;
     guard_equal cnode_cap buffer_frame_root word_bits;
     cspace_cap' = update_cap_data_det cspace_root_data cspace_cap;
     new_tcb_fields = update_tcb_fault_endpoint fault_ep tcb;
     ~ ep_related_cap tcb_cap;
     is_tcb root_tcb;
     is_tcb_cap tcb_cap;
     ~is_memory_cap tcb_cap;
     cnode_id = cap_object cnode_cap;
     tcb_id = cap_object tcb_cap;
     offset tcb_root root_size = tcb_cap_slot;
     offset cspace_root root_size = cspace_slot;
     offset vspace_root root_size = vspace_slot;
     offset buffer_frame_root root_size =  buffer_frame_slot\<rbrakk>
   \<Longrightarrow> \<lbrace>\<lambda>s.
     \<guillemotleft>root_tcb_id \<mapsto>f root_tcb \<and>*
     (root_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*

     \<comment> \<open>Root CNode.\<close>
     cnode_id \<mapsto>f CNode (empty_cnode root_size) \<and>*
     \<comment> \<open>Cap to the root CNode.\<close>
     (root_tcb_id, tcb_cspace_slot) \<mapsto>c cnode_cap \<and>*
     \<comment> \<open>Cap that the root task has to its own CNode.\<close>
     (cnode_id, cnode_cap_slot) \<mapsto>c cnode_cap' \<and>*

     \<comment> \<open>TCB's stuff\<close>
     tcb_id    \<mapsto>f Tcb tcb \<and>*

     \<comment> \<open>Where to copy the cap from (in the client CNode).\<close>
     (cnode_id, tcb_cap_slot) \<mapsto>c tcb_cap \<and>*
     (cnode_id, cspace_slot)  \<mapsto>c cspace_cap \<and>*
     (cnode_id, vspace_slot)  \<mapsto>c vspace_cap \<and>*
     (cnode_id, buffer_frame_slot) \<mapsto>c buffer_frame_cap \<and>*

     \<comment> \<open>Cap to the TCB.\<close>
     (tcb_id, tcb_cspace_slot) \<mapsto>c NullCap \<and>*
     (tcb_id, tcb_vspace_slot) \<mapsto>c NullCap \<and>*
     (tcb_id, tcb_ipcbuffer_slot) \<mapsto>c NullCap \<and>*
      R\<guillemotright> s \<and>
      cap_object cnode_cap = cnode_id \<and>
      cap_object cnode_cap' = cnode_id \<and>

      cap_object tcb_cap    = tcb_id \<and>
      tcb_cap_slot = offset tcb_root root_size \<and>

      cspace_slot = offset cspace_root root_size \<and>
      vspace_slot = offset vspace_root root_size \<and>
      buffer_frame_slot = offset buffer_frame_root root_size \<rbrace>
  seL4_TCB_Configure tcb_root fault_ep
                     cspace_root cspace_root_data
                     vspace_root vspace_root_data
                     buffer_addr buffer_frame_root
  \<lbrace>\<lambda>rv s. \<guillemotleft>root_tcb_id \<mapsto>f root_tcb \<and>*
       (root_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*

       \<comment> \<open>Root CNode.\<close>
       cnode_id \<mapsto>f CNode (empty_cnode root_size) \<and>*
       \<comment> \<open>Cap to the root CNode.\<close>
       (root_tcb_id, tcb_cspace_slot) \<mapsto>c cnode_cap \<and>*
       \<comment> \<open>Cap that the root task has to its own CNode.\<close>
       (cnode_id, cnode_cap_slot) \<mapsto>c cnode_cap' \<and>*

       \<comment> \<open>TCB's stuff\<close>
       tcb_id    \<mapsto>f Tcb new_tcb_fields \<and>*

       \<comment> \<open>Where to copy the cap from (in the client CNode).\<close>
       (cnode_id, tcb_cap_slot) \<mapsto>c tcb_cap \<and>*
       (cnode_id, cspace_slot)  \<mapsto>c cspace_cap \<and>*
       (cnode_id, vspace_slot)  \<mapsto>c vspace_cap \<and>*
       (cnode_id, buffer_frame_slot) \<mapsto>c buffer_frame_cap \<and>*

       \<comment> \<open>Cap to the TCB.\<close>
       (tcb_id, tcb_cspace_slot) \<mapsto>c (cdl_update_cnode_cap_data cspace_cap cspace_root_data)\<and>*
       (tcb_id, tcb_vspace_slot) \<mapsto>c vspace_cap \<and>*
       (tcb_id, tcb_ipcbuffer_slot) \<mapsto>c buffer_frame_cap \<and>*
       R\<guillemotright> s\<rbrace>"
  using unify
  apply (simp add: seL4_TCB_Configure_def sep_state_projection2_def)
  apply (simp only: is_tcb_def split:cdl_object.splits)
  apply (rename_tac cdl_tcb sz)
  apply (rule hoare_pre)
   apply (wp do_kernel_op_pull_back)
   apply (rule_tac tcb=cdl_tcb in call_kernel_with_intent_allow_error_helper
                [where check = True and Perror = \<top>,simplified])
                apply (fastforce)
               apply (rule hoare_strengthen_post[OF set_cap_wp])
               apply (sep_schem)
              apply (wp+)[4]
          apply (rule_tac P= "
          \<exists>cspace_cap' vspace_cap' buffer_frame_cap'.
          iv = (InvokeTcb $
          ThreadControl
          (cap_object tcb_cap)
          (cnode_id, tcb_cap_slot)
          (Some fault_ep)
          (Some (cspace_cap', (cnode_id, cspace_slot)))
          (Some (vspace_cap', (cnode_id, vspace_slot)))
          (Some (buffer_frame_cap', (cnode_id, buffer_frame_slot) ))) \<and>
          reset_cap_asid (cdl_update_cnode_cap_data cspace_cap cspace_root_data) = reset_cap_asid cspace_cap' \<and>
          reset_cap_asid vspace_cap = reset_cap_asid vspace_cap' \<and>
          reset_cap_asid buffer_frame_cap = reset_cap_asid (buffer_frame_cap') " in hoare_gen_asmEx)
          apply (simp)
          apply (elim exE)
          supply [[simproc del: defined_all]]
          apply simp
          apply (rule false_e_explode)
          apply (rule no_exception_conj')
           apply (wp invoke_tcb_ThreadControl_cur_thread)[1]
            apply (clarsimp cong:reset_cap_asid_cap_type)
           apply (clarsimp dest!:reset_cap_asid_cap_type)
          apply (rule no_exception_conj')
           apply (wp invoke_tcb_ThreadControl_cdl_current_domain)[1]
            apply (clarsimp cong:reset_cap_asid_cap_type)
           apply (clarsimp dest!:reset_cap_asid_cap_type)
          apply (rule hoare_strengthen_postE)
            apply (rule_tac R = "(root_tcb_id, tcb_pending_op_slot) \<mapsto>c RestartCap \<and>* R'" for R' in
            invoke_tcb_threadcontrol_wp'[where vrt_cap = vspace_cap and
            crt_cap = "cdl_update_cnode_cap_data cspace_cap cspace_root_data" and
            ipcbuff_cap = buffer_frame_cap and tcb = tcb])
            apply (rule_tac x = "invoke_tcb_cspace iv" in  exI)
            apply (rule_tac x = "invoke_tcb_vspace iv" in exI)
            apply (rule_tac x = "invoke_tcb_ipcbuffer iv" in exI)
            apply (intro exI conjI,simp_all add:invoke_tcb_cspace_def
           invoke_tcb_vspace_def invoke_tcb_ipcbuffer_def)[1]
           apply (rule conjI)
            prefer 2
            apply (simp add: sep_conj_assoc update_tcb_fault_endpoint_def)
            apply (clarsimp simp:unify dest!:cap_typeD)
            apply (rule sep_map_c_any[where cap = RestartCap])
            apply (sep_schem)
           apply sep_solve
          apply assumption
         apply (rule_tac Q'="\<lambda>r s. cdl_current_thread s = Some root_tcb_id \<and>
          cdl_current_domain s = minBound \<and>
          (\<exists>cspace_cap' vspace_cap' buffer_frame_cap'.
          iv = (InvokeTcb $
          ThreadControl (cap_object tcb_cap) (cnode_id, tcb_cap_slot) (Some fault_ep)
          (Some (cspace_cap', cnode_id, cspace_slot)) (Some (vspace_cap', cnode_id, vspace_slot))
          (Some (buffer_frame_cap', cnode_id, buffer_frame_slot))) \<and>
          reset_cap_asid (cdl_update_cnode_cap_data cspace_cap cspace_root_data) = reset_cap_asid cspace_cap' \<and>
          reset_cap_asid vspace_cap = reset_cap_asid vspace_cap' \<and>
          reset_cap_asid buffer_frame_cap = reset_cap_asid buffer_frame_cap')
          \<and> <cap_object tcb_cap \<mapsto>f Tcb tcb \<and>*
          (cap_object cnode_cap, vspace_slot) \<mapsto>c vspace_cap \<and>*
          (cap_object tcb_cap, tcb_cspace_slot) \<mapsto>c NullCap \<and>*
          (cap_object cnode_cap, tcb_cap_slot) \<mapsto>c TcbCap (cap_object tcb_cap) \<and>*
          (cap_object cnode_cap, cspace_slot) \<mapsto>c cspace_cap \<and>*
          (cap_object tcb_cap, tcb_vspace_slot) \<mapsto>c NullCap \<and>*
          (cap_object cnode_cap, buffer_frame_slot) \<mapsto>c buffer_frame_cap \<and>*
          (cap_object tcb_cap, tcb_ipcbuffer_slot) \<mapsto>c NullCap \<and>*
          (root_tcb_id, tcb_pending_op_slot) \<mapsto>c RestartCap \<and>*
          root_tcb_id \<mapsto>f Tcb cdl_tcb \<and>*
          cap_object cnode_cap \<mapsto>f CNode (empty_cnode root_size) \<and>*
          (root_tcb_id, tcb_cspace_slot) \<mapsto>c cnode_cap \<and>* (cap_object cnode_cap, cnode_cap_slot) \<mapsto>c cnode_cap' \<and>* R> s"
          in hoare_strengthen_post)
          apply wp
          apply clarsimp
          apply (rule hoare_strengthen_post[OF set_cap_wp])
          apply (sep_schem)
         apply clarsimp
         apply (rule conjI, sep_solve, sep_solve)
        apply clarsimp
        apply (rule no_exception_conjE)
         apply wp[1]
        apply (rule no_exception_conjE)
         apply wp[1]
        apply (rule no_exception_conjE)
         apply (wp  decode_invocation_tcb_rv''[simplified, where xs="[]" and
         croot_slot="(cnode_id, cspace_slot)" and
         vroot_slot="(cnode_id, vspace_slot)" and
         ipcbuff_slot="(cnode_id, buffer_frame_slot)"])+
        apply (rule_tac P="is_tcb_cap c" in hoare_gen_asmEx )
        apply (rule split_error_validE)
         apply (clarsimp simp: decode_tcb_invocation_simps)
         including no_pre
         apply (wp)
         apply (clarsimp simp: comp_def)
         apply (wp+)[2]
       apply (simp add:lookup_extra_caps_def Let_def
       mapME_def sequenceE_def get_index_def bindE_assoc)
       apply (rule wp_no_exception_seq)
        apply (rule wp_no_exception_seq)
         apply (rule wp_no_exception_seq)
          apply wp[1]
         apply (rule lookup_cap_and_slot_rvu[where r=root_size and cap=cnode_cap and cap'=buffer_frame_cap])
        apply (rule lookup_cap_and_slot_rvu[where r=root_size and cap=cnode_cap and cap'=vspace_cap])
       apply (clarsimp simp: split_def)
       apply (rule_tac P="a=tcb_cap \<and> (aa, b) = (cap_object cnode_cap, offset tcb_root root_size)" in hoare_gen_asmEx)
       apply (clarsimp)[1]
       apply (rule lookup_cap_and_slot_rvu[where r=root_size and cap=cnode_cap and cap'=cspace_cap])
      apply (rule hoare_weaken_preE)
       apply (rule lookup_cap_and_slot_rvu[where r=root_size and cap=cnode_cap and cap'=tcb_cap])
      apply (erule_tac Q="cdl_current_domain s = minBound" in conjE)
      apply (assumption)
     apply (simp add: split_def)
     apply clarsimp
     apply (wp hoare_vcg_ball_lift hoare_vcg_conj_lift hoare_vcg_imp_lift hoare_vcg_all_lift)
          apply (rule update_thread_intent_update)
         apply (wp hoare_vcg_ball_lift
                   hoare_vcg_imp_lift hoare_vcg_ex_lift hoare_vcg_all_lift
                   update_thread_intent_update)+
    defer
    apply (clarsimp)
    apply (intro conjI allI impI disjI2)
             apply (clarsimp dest!:reset_cap_asid_cnode_cap simp:cnode_cap_reset_asid)+
             apply sep_cancel+
             apply (clarsimp simp:is_tcb_cap_is_object)
            apply sep_solve
           apply (clarsimp simp: dest!:reset_cap_asid_cnode_cap)
          apply (drule reset_cap_asid_mem_mapping[where buffer_frame_cap = buffer_frame_cap,rotated])
           apply simp
          apply simp
         apply (clarsimp simp: unify user_pointer_at_def Let_unfold sep_conj_assoc, sep_solve)+
      apply (clarsimp simp:reset_cap_asid_tcb)+
    apply (clarsimp simp: unify user_pointer_at_def Let_unfold sep_conj_assoc, sep_solve)
   apply (clarsimp simp: unify user_pointer_at_def Let_unfold sep_conj_assoc, sep_solve)
  apply clarsimp
  apply (drule_tac x = tcb_cap in spec)
  apply (clarsimp cong:cap_type_bad_cong)
  apply (drule_tac x = cspace_cap in spec,clarsimp)
  apply (elim impE exE,fastforce)
  apply (elim impE allE conjE,fastforce)
  apply clarsimp
  apply (drule use_sep_true_for_sep_map_c)
   apply assumption
  apply (sep_select_asm 4)
  apply (sep_solve)
  done

lemma reset_cap_asid_pending:
  "reset_cap_asid cap' = reset_cap_asid cap
    \<Longrightarrow> is_pending_cap cap' = is_pending_cap cap"
  by (simp add: reset_cap_asid_def is_pending_cap_def split: cdl_cap.split_asm)

lemma restart_cdl_current_domain:
  "\<lbrace>\<lambda>s. <(ptr,tcb_pending_op_slot) \<mapsto>c cap \<and>* \<top> > s \<and> \<not> is_pending_cap cap
      \<and> P (cdl_current_domain s)\<rbrace> restart ptr \<lbrace>\<lambda>r s. P (cdl_current_domain s)\<rbrace>"
  apply (simp add:restart_def)
  apply (wpsimp wp: hoare_pre_cont[where f=chaos])
  apply (drule opt_cap_sep_imp)
  apply (clarsimp dest!: reset_cap_asid_pending)
  done


lemma restart_cdl_current_thread:
  "\<lbrace>\<lambda>s. <(ptr,tcb_pending_op_slot) \<mapsto>c cap \<and>* \<top> > s \<and> \<not> is_pending_cap cap
      \<and> P (cdl_current_thread s)\<rbrace> restart ptr \<lbrace>\<lambda>r s. P (cdl_current_thread s)\<rbrace>"
  apply (simp add:restart_def)
  apply (wpsimp wp: hoare_pre_cont[where f=chaos])
  apply (drule opt_cap_sep_imp)
  apply (clarsimp dest!: reset_cap_asid_pending)
  done

lemma seL4_TCB_WriteRegisters_wp:
  "\<lbrakk> is_cnode_cap cnode_cap;
     \<comment> \<open>Caps point to the right objects.\<close>
     one_lvl_lookup cnode_cap word_bits root_size;
     guard_equal cnode_cap tcb_ref word_bits;
     is_tcb root_tcb;
     is_tcb_cap tcb_cap;
     tcb_id = cap_object tcb_cap \<rbrakk> \<Longrightarrow>
   \<lbrace> \<guillemotleft> root_tcb_id \<mapsto>f root_tcb
     \<and>* (root_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap
     \<and>* (root_tcb_id, tcb_cspace_slot) \<mapsto>c cnode_cap
     \<and>* tcb_id \<mapsto>f tcb
     \<and>* (tcb_id, tcb_pending_op_slot) \<mapsto>c NullCap
     \<and>* (tcb_id, tcb_boundntfn_slot) \<mapsto>c bound_ntfn_cap
     \<and>* cap_object cnode_cap \<mapsto>f CNode (empty_cnode root_size)
     \<and>* (cap_object cnode_cap, offset tcb_ref root_size) \<mapsto>c tcb_cap
     \<and>* R \<guillemotright> \<rbrace>
   seL4_TCB_WriteRegisters tcb_ref False 0 num_regs regs
   \<lbrace>\<lambda>_.  \<guillemotleft> root_tcb_id \<mapsto>f root_tcb
     \<and>* (root_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap
     \<and>* (root_tcb_id, tcb_cspace_slot) \<mapsto>c cnode_cap
     \<and>* tcb_id \<mapsto>f tcb
     \<and>* (tcb_id, tcb_pending_op_slot) \<mapsto>c NullCap
     \<and>* (tcb_id, tcb_boundntfn_slot) \<mapsto>c bound_ntfn_cap
     \<and>* cap_object cnode_cap \<mapsto>f CNode (empty_cnode root_size)
     \<and>* (cap_object cnode_cap, offset tcb_ref root_size) \<mapsto>c tcb_cap
     \<and>* R \<guillemotright> \<rbrace>"
  apply (simp add: seL4_TCB_WriteRegisters_def sep_state_projection2_def is_tcb_def
            split: cdl_object.splits)
  apply (rename_tac cdl_tcb)
  apply (wp do_kernel_op_pull_back)
   apply (rule hoare_post_imp[OF _ call_kernel_with_intent_allow_error_helper[
                                     where check = False,simplified]])
                apply (rename_tac rv s)
                apply clarsimp
                apply (case_tac rv, (clarsimp,assumption)+)[1]
               apply fastforce
              apply (rule hoare_strengthen_post[OF set_cap_wp])
              apply (sep_select 3,sep_cancel)
             apply (wp+)[4]
         apply (rule_tac P= "iv = (InvokeTcb $ WriteRegisters (cap_object tcb_cap) False)"
                      in hoare_gen_asmEx)
         apply (clarsimp simp: invoke_tcb_def)
         apply (wp restart_cdl_current_thread[where cap = RestartCap]
                   restart_cdl_current_domain[where cap = RestartCap])
        apply (wp set_cap_wp hoare_vcg_conj_lift)
         apply (rule_tac R1="root_tcb_id \<mapsto>f Tcb cdl_tcb  \<and>* Q" for Q
                      in hoare_post_imp[OF _ set_cap_wp])
         apply sep_solve
        apply wp
       apply (rule_tac P = "c = TcbCap (cap_object tcb_cap)" in hoare_gen_asmEx)
       apply (simp add: decode_invocation_def throw_opt_def get_tcb_intent_def decode_tcb_invocation_def)
       apply wp
      apply (clarsimp simp: conj_comms lookup_extra_caps_def mapME_def sequenceE_def)
      apply (rule returnOk_wp)
     apply (rule lookup_cap_and_slot_rvu[where r=root_size and cap=cnode_cap and cap'=tcb_cap])
    apply clarsimp
    apply (wp hoare_vcg_ball_lift hoare_vcg_conj_lift hoare_vcg_imp_lift hoare_vcg_all_lift)
      apply (wp update_thread_intent_update)+
   apply clarify
   apply (drule_tac x = tcb_cap in spec)
   apply clarsimp
   apply (erule use_sep_true_for_sep_map_c)
   apply sep_solve
  apply (intro conjI impI allI)
     apply (clarsimp simp: is_tcb_def reset_cap_asid_tcb
                    split: cdl_object.splits cdl_cap.splits)+
    apply (simp add: ep_related_cap_def cap_type_def cap_object_def
              split: cdl_cap.splits)
    apply ((rule conjI|sep_solve)+)[1]
   apply (clarsimp simp: user_pointer_at_def Let_unfold sep_conj_assoc is_tcb_def)
   apply sep_solve
  apply sep_solve
  done


lemma seL4_TCB_Resume_wp:
  "\<lbrakk> is_cnode_cap cnode_cap;
    \<comment> \<open>Caps point to the right objects.\<close>
     one_lvl_lookup cnode_cap word_bits root_size;
     guard_equal cnode_cap tcb_ref word_bits;
     is_tcb root_tcb;
     is_tcb_cap tcb_cap\<rbrakk> \<Longrightarrow>
   \<lbrace> \<guillemotleft> root_tcb_id \<mapsto>f root_tcb
     \<and>* (root_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap
     \<and>* (cap_object tcb_cap, tcb_pending_op_slot) \<mapsto>c NullCap
     \<and>* (cap_object tcb_cap, tcb_replycap_slot) \<mapsto>c -
     \<and>* (root_tcb_id, tcb_cspace_slot) \<mapsto>c cnode_cap
     \<and>* cap_object cnode_cap \<mapsto>f CNode (empty_cnode root_size)
     \<and>* (cap_object cnode_cap, offset tcb_ref root_size) \<mapsto>c tcb_cap
     \<and>* R \<guillemotright> \<rbrace>
  seL4_TCB_Resume tcb_ref
  \<lbrace>\<lambda>_.  \<guillemotleft> root_tcb_id \<mapsto>f root_tcb
    \<and>* (root_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap
    \<and>* (cap_object tcb_cap, tcb_pending_op_slot) \<mapsto>c RestartCap
    \<and>* (cap_object tcb_cap, tcb_replycap_slot) \<mapsto>c MasterReplyCap (cap_object tcb_cap)
    \<and>* (root_tcb_id, tcb_cspace_slot) \<mapsto>c cnode_cap
    \<and>* cap_object cnode_cap \<mapsto>f CNode (empty_cnode root_size)
    \<and>* (cap_object cnode_cap, offset tcb_ref root_size) \<mapsto>c tcb_cap
    \<and>* R \<guillemotright> \<rbrace>"
  apply (simp add:seL4_TCB_Resume_def sep_state_projection2_def
    is_tcb_def split:cdl_object.splits)
  apply (rename_tac cdl_tcb)
  apply (rule hoare_pre)
   apply (wp do_kernel_op_pull_back)
   apply (rule hoare_post_imp[OF _ call_kernel_with_intent_allow_error_helper
      [where check = True,simplified]])
                apply simp
               apply fastforce
              apply (rule hoare_strengthen_post[OF set_cap_wp])
              apply (sep_select 2,sep_cancel)
             apply (wp+)[4]
         apply (rule_tac P= "
           iv = (InvokeTcb $ Resume (cap_object tcb_cap))" in hoare_gen_asmEx)
         apply (clarsimp simp:invoke_tcb_def)
         apply (wp restart_cdl_current_thread[where cap = NullCap]
           restart_cdl_current_domain[where cap = NullCap])
         apply (rule_tac R1="root_tcb_id \<mapsto>f Tcb cdl_tcb
             \<and>* (root_tcb_id, tcb_pending_op_slot) \<mapsto>c RestartCap \<and>* Q" for Q in
             hoare_post_imp[OF _ restart_null_wp])
         apply (rule conjI,sep_solve)
         apply (rule sep_any_imp_c'_conj)
         apply sep_cancel
         apply sep_cancel
        apply simp
        apply (simp add:is_pending_cap_def conj_comms)
        apply (wp set_cap_wp hoare_vcg_conj_lift)
         apply (rule_tac R1 ="(cap_object tcb_cap, tcb_pending_op_slot) \<mapsto>c NullCap \<and>* (\<lambda>_. True)"
                         in hoare_post_imp[OF _ set_cap_wp])
         apply sep_cancel
         apply simp
        apply (rule_tac R1="root_tcb_id \<mapsto>f Tcb cdl_tcb  \<and>* Q" for Q in hoare_post_imp[OF _ set_cap_wp])
        apply (sep_select 4,sep_cancel)
        apply (sep_select 3,sep_cancel)
       apply (rule_tac P = "c = TcbCap (cap_object tcb_cap)" in hoare_gen_asmEx)
       apply (simp add: decode_invocation_def throw_opt_def get_tcb_intent_def decode_tcb_invocation_def)
       apply wp
      apply (clarsimp simp: lookup_extra_caps_def mapME_def sequenceE_def)
      apply (rule returnOk_wp)
     apply (rule lookup_cap_and_slot_rvu[where r=root_size and cap=cnode_cap and cap'=tcb_cap])
    apply clarsimp
    apply (wp hoare_vcg_conj_lift hoare_vcg_imp_lift hoare_vcg_all_lift)
      apply (wp update_thread_intent_update)+
   apply clarify
   apply (drule_tac x = tcb_cap in spec)
   apply clarsimp
   apply (erule use_sep_true_for_sep_map_c)
   apply sep_solve
  apply (intro conjI impI allI)
     apply (clarsimp simp:is_tcb_def reset_cap_asid_tcb
                    split:cdl_object.splits cdl_cap.splits)+
    apply (simp add: ep_related_cap_def cap_type_def cap_object_def
              split: cdl_cap.splits)
    apply (rule conjI)
     apply (metis (no_types, lifting) sep.mult_assoc sep_any_exist sep_normal_conj_absorb')
    apply ((rule conjI|sep_solve)+)[1]
   apply (clarsimp simp: user_pointer_at_def Let_unfold sep_conj_assoc is_tcb_def)
   apply sep_cancel+
  apply sep_solve
  done

end
