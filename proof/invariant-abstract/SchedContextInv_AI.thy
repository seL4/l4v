(*
 * Copyright 2018, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

theory SchedContextInv_AI
  imports "./$L4V_ARCH/ArchIpc_AI" "IpcDet_AI"

begin

lemmas MIN_BUDGET_nonzero = MIN_BUDGET_pos[simplified word_neq_0_conv[symmetric]]

lemmas sufficient_refills_defs = sufficient_refills_def refills_capacity_def

lemma tcb_yield_to_noncap: "tcb_at p s \<Longrightarrow>
  obj_at (same_caps (TCB (tcb_yield_to_update (\<lambda>y. new) (the (get_tcb p s))))) p s"
  apply (clarsimp simp: obj_at_def is_tcb_def)
  by (case_tac ko; clarsimp simp: ran_tcb_cap_cases get_tcb_rev)

lemma set_consumed_valid_objs[wp]:
  "\<lbrace>valid_objs\<rbrace> set_consumed scptr args \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  by (wpsimp simp: set_consumed_def)

lemma set_consumed_valid_idle[wp]:
  "\<lbrace>valid_idle\<rbrace> set_consumed scptr args \<lbrace>\<lambda>rv. valid_idle\<rbrace>"
  by (wpsimp simp: set_consumed_def)

lemma set_consumed_only_idle[wp]:
  "\<lbrace>only_idle\<rbrace> set_consumed scptr args \<lbrace>\<lambda>rv. only_idle\<rbrace>"
  by (wpsimp simp: set_consumed_def)

lemma set_consumed_iflive[wp]:
  "\<lbrace>if_live_then_nonz_cap\<rbrace> set_consumed scptr args \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  by (wpsimp simp: set_consumed_def)

lemma set_consumed_refs_of:
  "\<lbrace>(*(\<lambda>s. kheap s tptr = Some (TCB tcb) \<and> tcb_yield_to tcb = Some scp) and*) (\<lambda>s. P (state_refs_of s))\<rbrace>
        set_consumed scptr args \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  by (wpsimp simp: set_consumed_def)

lemma set_mrs_ct[wp]:
  "\<lbrace>\<lambda>s. P (cur_thread s)\<rbrace> set_mrs  thread buf msgs \<lbrace>\<lambda>rv s. P (cur_thread s)\<rbrace>"
  by (wpsimp simp: set_mrs_def zipWithM_x_mapM store_word_offs_def
         wp: mapM_wp' hoare_vcg_if_lift2 split_del: if_split)

lemma set_mrs_tcb_at_ct[wp]:
  "\<lbrace>\<lambda>s. tcb_at (cur_thread s) s\<rbrace> set_mrs thread buf msgs \<lbrace>\<lambda>rv s. tcb_at (cur_thread s) s\<rbrace>"
  apply (simp add: set_mrs_redux zipWithM_x_mapM split_def
                   store_word_offs_def
             cong: option.case_cong
              del: upt.simps)
  apply (wp mapM_wp' | wpcw | clarsimp dest!: get_tcb_SomeD
          | simp add: do_machine_op_def thread_set_def set_object_def tcb_at_typ obj_at_def)+
  done

lemma as_user_tcb_ct[wp]:
  "\<lbrace>\<lambda>s. tcb_at (cur_thread s) s\<rbrace> as_user t m \<lbrace>\<lambda>rv s. tcb_at (cur_thread s) s\<rbrace>"
  apply (simp add: as_user_def split_def)
  apply (wpsimp simp: wp: set_object_wp)
  apply (clarsimp simp: obj_at_def is_tcb)
  done

lemma as_user_ex_nonz[wp]:
  "\<lbrace>\<lambda>s. ex_nonz_cap_to (cur_thread s) s\<rbrace> as_user t m \<lbrace>\<lambda>rv s. ex_nonz_cap_to (cur_thread s) s\<rbrace>"
  apply (simp add: as_user_def split_def)
  apply (wpsimp simp: wp: set_object_wp)
  apply (clarsimp simp: ex_nonz_cap_to_def)
  apply (rule_tac x=aa in exI)
  apply (rule_tac x=ba in exI)
  apply (case_tac "t=aa", simp)
   defer
   apply (drule upd_other_cte_wp_at)
    prefer 2
    apply simp
   apply simp
  apply (clarsimp simp: fun_upd_def, subst cte_wp_at_after_update)
   apply (clarsimp simp: same_caps_def obj_at_def ran_tcb_cap_cases dest!: get_tcb_SomeD)
  by simp

lemma set_mrs_ex_nonz_ct[wp]:
  "\<lbrace>\<lambda>s. ex_nonz_cap_to (cur_thread s) s\<rbrace> set_mrs thread buf msgs \<lbrace>\<lambda>rv s. ex_nonz_cap_to (cur_thread s) s\<rbrace>"
  apply (rule set_mrs_thread_set_dmo)
   apply (wpsimp wp: ex_nonz_cap_to_pres simp: thread_set_def set_object_def simp_del: fun_upd_apply)
   apply (clarsimp dest!: get_tcb_SomeD simp: ex_nonz_cap_to_def simp del: fun_upd_apply)
   apply (rule_tac x=a in exI)
   apply (rule_tac x=b in exI)
   apply (case_tac "a=thread", simp)
    defer
    apply (drule upd_other_cte_wp_at)
     apply simp
    apply simp
   prefer 2
   apply (clarsimp simp: fun_upd_def, subst cte_wp_at_after_update)
    apply (clarsimp simp: same_caps_def obj_at_def ran_tcb_cap_cases dest!: get_tcb_SomeD)
   apply simp
  apply (wpsimp simp: do_machine_op_def ex_nonz_cap_to_def)
  done


crunches set_message_info, set_mrs,set_consumed
 for ct[wp]: "\<lambda>s. P (cur_thread s)"
 and tcb_at_ct[wp]: "\<lambda>s. tcb_at (cur_thread s) s"
 and ex_nonz_cap_to_ct[wp]: "\<lambda>s. ex_nonz_cap_to (cur_thread s) s"
(wp: valid_bound_tcb_typ_at set_object_typ_at mapM_wp
ignore: set_object as_user simp: zipWithM_x_mapM)

crunches set_message_info, set_mrs
 for cap_refs_in_kernel_window[wp]: "cap_refs_in_kernel_window"
 and cap_refs_respects_device_region[wp]: "cap_refs_respects_device_region"

lemma set_consumed_cap_refs_in_kernel_window[wp]:
  "\<lbrace>cap_refs_in_kernel_window\<rbrace> set_consumed scptr args \<lbrace>\<lambda>rv. cap_refs_in_kernel_window\<rbrace>"
  by (wpsimp simp: set_consumed_def ran_tcb_cap_cases)

lemma set_consumed_cap_refs_respects_device_region[wp]:
  "\<lbrace>cap_refs_respects_device_region\<rbrace> set_consumed scptr args \<lbrace>\<lambda>rv. cap_refs_respects_device_region\<rbrace>"
  by (wpsimp simp: set_consumed_def ran_tcb_cap_cases)

(*
lemma set_consumed_refs_of_ct[wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of s)(cur_thread s)\<rbrace>
      set_consumed scptr args \<lbrace>\<lambda>rv s. P (state_refs_of s)(cur_thread s)\<rbrace>"
  by (wpsimp simp: set_consumed_def)
*)

crunch it_ct[wp]: set_thread_state_act "\<lambda>s. P (idle_thread s) (cur_thread s)"

crunches set_consumed
 for aligned[wp]: pspace_aligned
 and distinct[wp]: pspace_distinct
(* and sc_at[wp]: "sc_at sc_ptr"*)
 and tcb_at[wp]: "tcb_at t"
 and cte_wp_at[wp]: "cte_wp_at P c"
 and interrupt_irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"
 and caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"
 and no_cdt[wp]: "\<lambda>s. P (cdt s)"
 and no_revokable[wp]: "\<lambda>s. P (is_original_cap s)"
 and state_hyp_refs_of[wp]: "\<lambda>s. P (state_hyp_refs_of s)"
 and valid_global_objs[wp]: "valid_global_objs"
 and valid_global_vspace_mappings[wp]: "valid_global_vspace_mappings"
 and valid_arch_caps[wp]: "valid_arch_caps"
 and only_idle[wp]: "only_idle"
 and ifunsafe[wp]: "if_unsafe_then_cap"
 and valid_arch[wp]: "valid_arch_state"
 and valid_irq_states[wp]: "valid_irq_states"
 and vms[wp]: "valid_machine_state"
 and valid_vspace_objs[wp]: "valid_vspace_objs"
 and valid_global_refs[wp]: "valid_global_refs"
 and v_ker_map[wp]: "valid_kernel_mappings"
 and equal_mappings[wp]: "equal_kernel_mappings"
 and valid_asid_map[wp]: "valid_asid_map"
 and pspace_in_kernel_window[wp]: "pspace_in_kernel_window"
 and pspace_respects_device_region[wp]: "pspace_respects_device_region"
 and cur_tcb[wp]: "cur_tcb"
 and ex_nonz_cap_to[wp]: "ex_nonz_cap_to t"
 and valid_ioc[wp]: "valid_ioc"
 and it[wp]: "\<lambda>s. P (idle_thread s)"
 and it_ct[wp]: "\<lambda>s. P (idle_thread s) (cur_thread s)"
 and typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
 and interrupt_states[wp]: "\<lambda>s. P (interrupt_states s)"
 and valid_irq_handlers[wp]: "valid_irq_handlers"
 and valid_mdb[wp]: valid_mdb
 and valid_idle[wp]: valid_idle
 and zombies[wp]: zombies_final
  (simp: Let_def tcb_yield_to_noncap zipWithM_x_mapM
    wp: hoare_drop_imps crunch_wps maybeM_inv ignore: set_consumed lookup_ipc_buffer)


crunches complete_yield_to
 for aligned[wp]: pspace_aligned
 and distinct[wp]: pspace_distinct
(* and sc_at[wp]: "sc_at sc_ptr"*)
 and tcb_at[wp]: "tcb_at t"
 and cte_wp_at[wp]: "cte_wp_at P c"
 and interrupt_irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"
 and caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"
 and no_cdt[wp]: "\<lambda>s. P (cdt s)"
 and state_hyp_refs_of[wp]: "\<lambda>s. P (state_hyp_refs_of s)"
 and no_revokable[wp]: "\<lambda>s. P (is_original_cap s)"
 and valid_global_objs[wp]: "valid_global_objs"
 and valid_global_vspace_mappings[wp]: "valid_global_vspace_mappings"
 and valid_arch_caps[wp]: "valid_arch_caps"
(* and only_idle[wp]: "only_idle"*)
 and ifunsafe[wp]: "if_unsafe_then_cap"
 and valid_arch[wp]: "valid_arch_state"
 and valid_irq_states[wp]: "valid_irq_states"
 and vms[wp]: "valid_machine_state"
 and valid_vspace_objs[wp]: "valid_vspace_objs"
 and valid_global_refs[wp]: "valid_global_refs"
 and v_ker_map[wp]: "valid_kernel_mappings"
 and equal_mappings[wp]: "equal_kernel_mappings"
 and valid_asid_map[wp]: "valid_asid_map"
 and pspace_in_kernel_window[wp]: "pspace_in_kernel_window"
 and cap_refs_in_kernel_window[wp]: "cap_refs_in_kernel_window"
 and cap_refs_respects_device_region[wp]: "cap_refs_respects_device_region"
 and pspace_respects_device_region[wp]: "pspace_respects_device_region"
 and cur_tcb[wp]: "cur_tcb"
(* and ex_nonz_cap_to[wp]: "ex_nonz_cap_to t"
 and valid_idle[wp]: valid_idle*)
 and valid_ioc[wp]: "valid_ioc"
 and it[wp]: "\<lambda>s. P (idle_thread s)"
 and typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
 and interrupt_states[wp]: "\<lambda>s. P (interrupt_states s)"
 and valid_irq_handlers[wp]: "valid_irq_handlers"
 and valid_mdb[wp]: valid_mdb
 and zombies[wp]: zombies_final
  (wp: maybeM_inv hoare_drop_imp sts_only_idle sts_valid_idle
   ignore: set_tcb_obj_ref get_sched_context)

lemma complete_yield_to_valid_objs[wp]:
  "\<lbrace>valid_objs\<rbrace> complete_yield_to tcb_ptr \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  by (wpsimp simp: complete_yield_to_def get_tcb_obj_ref_def maybeM_def
      wp: lookup_ipc_buffer_inv hoare_drop_imp)

lemma complete_yield_to_valid_idle[wp]:
  "\<lbrace>\<lambda>s. valid_idle s \<and> sym_refs (state_refs_of s)\<rbrace> complete_yield_to tcb_ptr \<lbrace>\<lambda>rv. valid_idle\<rbrace>"
  apply (clarsimp simp: complete_yield_to_def maybeM_def get_tcb_obj_ref_def)
  apply (rule hoare_seq_ext[OF _ thread_get_sp])
  apply (case_tac yt_opt; simp)
   apply wpsimp
  apply (rule hoare_seq_ext[OF _ lookup_ipc_buffer_inv])
  apply wpsimp
  apply (rule conjI)
   apply (clarsimp simp: obj_at_def valid_idle_def pred_tcb_at_def)
  apply (clarsimp simp: sym_refs_def)
  apply (erule_tac x = tcb_ptr in allE)
  apply (auto simp: valid_idle_def obj_at_def state_refs_of_def default_sched_context_def)
  done

lemma complete_yield_to_only_idle[wp]:
  "\<lbrace>only_idle\<rbrace> complete_yield_to tcb_ptr \<lbrace>\<lambda>rv. only_idle\<rbrace>"
  apply (clarsimp simp: complete_yield_to_def maybeM_def get_tcb_obj_ref_def)
  apply (rule hoare_seq_ext[OF _ thread_get_sp])
  apply (case_tac yt_opt; simp)
   apply wpsimp
  apply (rule hoare_seq_ext[OF _ lookup_ipc_buffer_inv])
  apply (rule hoare_seq_ext[OF _ assert_opt_inv])
  by (wpsimp wp: sts_only_idle)


lemma complete_yield_to_iflive[wp]:
  "\<lbrace>if_live_then_nonz_cap\<rbrace> complete_yield_to tcb_ptr \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  apply (clarsimp simp: complete_yield_to_def maybeM_def get_tcb_obj_ref_def)
  apply (rule hoare_seq_ext[OF _ thread_get_sp])
  apply (case_tac yt_opt; simp)
   apply wpsimp
  apply (rule hoare_seq_ext[OF _ lookup_ipc_buffer_inv])
  apply (rule hoare_seq_ext[OF _ assert_opt_inv])
  by wpsimp

lemma complete_yield_to_ex_nonz[wp]:
  "\<lbrace>ex_nonz_cap_to p\<rbrace> complete_yield_to tcb_ptr \<lbrace>\<lambda>rv. ex_nonz_cap_to p\<rbrace>"
  apply (clarsimp simp: complete_yield_to_def maybeM_def get_tcb_obj_ref_def)
  apply (rule hoare_seq_ext[OF _ thread_get_sp])
  apply (case_tac yt_opt; simp)
   apply wpsimp
  apply (rule hoare_seq_ext[OF _ lookup_ipc_buffer_inv])
  apply (rule hoare_seq_ext[OF _ assert_opt_inv])
  by wpsimp

crunches complete_yield_to
 for ct[wp]: "\<lambda>s. P (cur_thread s)"
 and it_ct[wp]: "\<lambda>s. P (idle_thread s) (cur_thread s)"
  (wp: maybeM_inv lookup_ipc_buffer_inv hoare_drop_imps crunch_wps)
(*
lemma complete_yield_to_refs_of_None:
notes set_sc_yf_refs_of [wp del]
notes refs_of_simps [simp del] shows
  "\<lbrace>\<lambda>s. obj_at (\<lambda>ko. \<exists>tcb. ko = TCB tcb \<and> tcb_yield_to tcb = None) tptr s
       \<and> P (state_refs_of s)\<rbrace>
    complete_yield_to tptr \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (clarsimp simp: complete_yield_to_def maybeM_def get_tcb_obj_ref_def split del: if_split)
  apply (rule hoare_seq_ext[OF _ thread_get_sp])
  apply (case_tac yt_opt; simp)
   apply wpsimp
(*   apply (clarsimp elim!: rsubst[where P=P] split del: if_split intro!: ext)
   apply (clarsimp simp: obj_at_def split del: if_split)
   apply clarsimp
   apply (fastforce simp: state_refs_of_def refs_of_def get_refs_def2 tcb_st_refs_of_def
      split: option.splits if_splits thread_state.splits) *)
  apply (rule hoare_assume_pre)
  apply (clarsimp simp: obj_at_def)
  done


lemma complete_yield_to_refs_of_Some:
notes set_sc_yf_refs_of [wp del]
notes refs_of_simps [simp del] shows
  "\<lbrace>(\<lambda>s. kheap s tptr = Some (TCB tcb) \<and> tcb_yield_to tcb = Some scp)(* bound_yt_tcb_at bound tptr*)
      and sc_yf_sc_at (\<lambda>x. x = Some tptr) scp
 and (\<lambda>s. P ((state_refs_of s)
       (tptr := {x \<in> state_refs_of s tptr. snd x = TCBBound \<or> snd x = TCBSchedContext},
scp := (state_refs_of s scp - {x \<in> state_refs_of s scp. snd x = SCYieldFrom}))))\<rbrace>
    complete_yield_to tptr \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (clarsimp simp: complete_yield_to_def maybeM_def get_tcb_obj_ref_def split del: if_split)
  apply (rule hoare_seq_ext[OF _ thread_get_sp])
  apply (case_tac yt_opt; simp add: pred_tcb_at_def)
  apply (rule hoare_assume_pre)
  apply (clarsimp simp: obj_at_def)
  apply (wpsimp simp: reply_unlink_tcb_def get_thread_state_def
                      get_object_def update_sched_context_def set_object_def
wp: set_consumed_refs_of hoare_drop_imp hoare_vcg_all_lift set_sc_yf_refs_of
simp_del: fun_upd_apply)
  apply (clarsimp simp: obj_at_def sc_yf_sc_at_def simp del: fun_upd_apply split del: if_split)
apply (case_tac "tptr=scp"; simp split: if_split_asm split del: if_split)
apply (clarsimp elim!: rsubst[where P=P] split del: if_split intro!: ext)

apply (fastforce split: if_split_asm
 simp: state_refs_of_def refs_of_def get_refs_def2 tcb_st_refs_of_def
split: thread_state.splits if_split)
  done
*)

lemma set_thread_state_bound_yt_tcb_at[wp]:
  "\<lbrace>bound_yt_tcb_at P t\<rbrace> set_thread_state p ts \<lbrace>\<lambda>_. bound_yt_tcb_at P t\<rbrace>"
  unfolding set_thread_state_def set_object_def
  by (wpsimp simp: pred_tcb_at_def obj_at_def get_tcb_def)

crunches set_thread_state_act
  for kheap_cur[wp]: "\<lambda>s. P (kheap s) (cur_thread s)"
  and obj_at_cur[wp]: "\<lambda>s. P (obj_at (Q (cur_thread s)) p s)"

lemma set_thread_state_bound_yt_tcb_at_ct[wp]:
  "\<lbrace>\<lambda>s. bound_yt_tcb_at P (cur_thread s) s\<rbrace>
     set_thread_state p ts \<lbrace>\<lambda>_ s. bound_yt_tcb_at P (cur_thread s) s\<rbrace>"
  unfolding set_thread_state_def set_object_def
  by (wpsimp simp: pred_tcb_at_def obj_at_def get_tcb_def)

lemma sssc_sc_yf_update_bound_yt_tcb_at_ct[wp]:
  "\<lbrace>\<lambda>s. bound_yt_tcb_at P (cur_thread s) s\<rbrace>
     set_sc_obj_ref sc_yield_from_update scp tcb \<lbrace>\<lambda>_ s. bound_yt_tcb_at P (cur_thread s) s\<rbrace>"
  unfolding set_sc_obj_ref_def update_sched_context_def set_object_def
  by (wpsimp simp: pred_tcb_at_def obj_at_def  wp: get_object_wp)

lemma complete_yield_to_bound_yt_tcb_at[wp]:
  "\<lbrace> bound_yt_tcb_at P t and K (t \<noteq> tcb_ptr) \<rbrace>
      complete_yield_to tcb_ptr \<lbrace>\<lambda>rv. bound_yt_tcb_at P t \<rbrace>"
  apply (rule hoare_gen_asm)
  apply (clarsimp simp: complete_yield_to_def)
  by (wpsimp simp: obj_at_def
      wp: hoare_vcg_ex_lift sbn_st_tcb_at_neq lookup_ipc_buffer_inv hoare_drop_imp)

crunch pred_tcb_at_ct[wp]: do_machine_op,store_word_offs "\<lambda>s. pred_tcb_at proj P (cur_thread s) s"
  (wp: crunch_wps hoare_vcg_if_lift2 simp: crunch_simps set_object_def)

lemma set_mrs_pred_tcb_at_ct[wp]:
  "\<lbrace>(\<lambda>s. pred_tcb_at proj P (cur_thread s) s)\<rbrace>
    set_mrs thread buf msgs \<lbrace>\<lambda>_ s. pred_tcb_at proj P (cur_thread s) s\<rbrace>"
  apply (clarsimp simp: set_mrs_def)
  apply (wpsimp split_del: if_split simp: zipWithM_x_mapM set_object_def wp: mapM_wp')
  apply (clarsimp simp: pred_tcb_at_def obj_at_def tcb_to_itcb_def dest!: get_tcb_SomeD)
  done

(* FIXME: replace this with as_user_pred_tcb_at which is stronger *)
lemma as_user_pred_tcb_at_ct[wp]:
  "\<lbrace>(\<lambda>s. pred_tcb_at proj P (cur_thread s) s)\<rbrace>
    as_user tptr f \<lbrace>\<lambda>_ s. pred_tcb_at proj P (cur_thread s) s\<rbrace>"
  apply (clarsimp simp: as_user_def)
  apply (wpsimp split_del: if_split simp: split_def set_object_def)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def tcb_to_itcb_def dest!: get_tcb_SomeD)
  done

lemma set_message_info_pred_tcb_at_ct[wp]:
  "\<lbrace>(\<lambda>s. pred_tcb_at proj P (cur_thread s) s)\<rbrace>
    set_message_info tptr f \<lbrace>\<lambda>_ s. pred_tcb_at proj P (cur_thread s) s\<rbrace>"
  by (wpsimp split_del: if_split simp: set_message_info_def split_def set_object_def)

lemma sched_context_update_consumed_pred_tcb_at_ct[wp]:
  "\<lbrace>(\<lambda>s. pred_tcb_at proj P (cur_thread s) s)\<rbrace>
    sched_context_update_consumed sc_ptr \<lbrace>\<lambda>_ s. pred_tcb_at proj P (cur_thread s) s\<rbrace>"
  apply (clarsimp simp: sched_context_update_consumed_def)
  apply (wpsimp wp: get_object_wp hoare_drop_imp get_sched_context_wp
            simp: split_def update_sched_context_def set_object_def)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def tcb_to_itcb_def)
  done

lemma set_consumed_pred_tcb_at_ct[wp]:
  "\<lbrace>(\<lambda>s. pred_tcb_at proj P (cur_thread s) s)\<rbrace>
    set_consumed sc_ptr args \<lbrace>\<lambda>_ s. pred_tcb_at proj P (cur_thread s) s\<rbrace>"
  apply (clarsimp simp: set_consumed_def)
  apply (wpsimp split_del: if_split simp: split_def set_object_def)
  done

lemma complete_yield_to_bound_yt_tcb_a_ct[wp]:
  "\<lbrace> (\<lambda>s. bound_yt_tcb_at ((=) None) (cur_thread s) s) \<rbrace>
      complete_yield_to tcb_ptr \<lbrace>\<lambda>rv s. bound_yt_tcb_at ((=) None) (cur_thread s) s \<rbrace>"
  apply (clarsimp simp: complete_yield_to_def)
  apply (wpsimp simp: obj_at_def set_tcb_obj_ref_def set_object_def fun_upd_idem
      wp: hoare_vcg_ex_lift sbn_st_tcb_at_neq lookup_ipc_buffer_inv hoare_drop_imp)
       apply (rule_tac Q="\<lambda>_ s. bound_yt_tcb_at ((=) None) (cur_thread s) s" in hoare_strengthen_post)
        apply (wpsimp simp: pred_tcb_at_def)
       apply (clarsimp simp: pred_tcb_at_def obj_at_def)
      apply (wpsimp wp: lookup_ipc_buffer_inv hoare_drop_imp)+
  done

lemma sts_sc_tcb_sc_at_not_ct[wp]:
  "\<lbrace> \<lambda>s. sc_tcb_sc_at (\<lambda>sctcb. \<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s) scp s\<rbrace>
   set_thread_state t s \<lbrace> \<lambda>rv s. sc_tcb_sc_at (\<lambda>sctcb. \<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s) scp s\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wp | simp add: set_object_def sc_tcb_sc_at_def)+
  by (clarsimp simp: obj_at_def is_tcb get_tcb_def split: kernel_object.splits)

lemma ssyf_sc_tcb_sc_at_not_ct[wp]:
  "\<lbrace> \<lambda>s. sc_tcb_sc_at (\<lambda>sctcb. \<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s) scp s\<rbrace>
   set_sc_obj_ref sc_yield_from_update sp new \<lbrace> \<lambda>rv s. sc_tcb_sc_at (\<lambda>sctcb. \<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s) scp s\<rbrace>"
  apply (simp add: set_sc_obj_ref_def update_sched_context_def)
  apply (wp get_object_wp | simp add: set_object_def sc_tcb_sc_at_def | wpc)+
  by (clarsimp simp: obj_at_def is_tcb get_tcb_def split: kernel_object.splits)

lemma styt_sc_tcb_sc_at_not_ct[wp]:
  "\<lbrace> \<lambda>s. sc_tcb_sc_at (\<lambda>sctcb. \<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s) scp s\<rbrace>
   set_tcb_obj_ref tcb_yield_to_update  sp new \<lbrace> \<lambda>rv s. sc_tcb_sc_at (\<lambda>sctcb. \<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s) scp s\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (wp get_object_wp | simp add: set_object_def sc_tcb_sc_at_def | wpc)+
  by (clarsimp simp: obj_at_def is_tcb get_tcb_def split: kernel_object.splits)

crunch sc_tcb_sc_at_not_ct[wp]: do_machine_op "\<lambda>s. sc_tcb_sc_at (\<lambda>sctcb. \<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s) scp s"
  (simp: crunch_simps split_def sc_tcb_sc_at_def wp: crunch_wps hoare_drop_imps)

crunch sc_tcb_sc_at_not_ct[wp]: store_word_offs "\<lambda>s. sc_tcb_sc_at (\<lambda>sctcb. \<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s) scp s"
  (simp: crunch_simps split_def wp: crunch_wps hoare_drop_imps ignore: do_machine_op)

lemma set_mrs_sc_tcb_sc_at_not_ct[wp]:
  "\<lbrace> \<lambda>s. sc_tcb_sc_at (\<lambda>sctcb. \<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s) scp s\<rbrace>
   set_mrs thread buf msgs \<lbrace> \<lambda>rv s. sc_tcb_sc_at (\<lambda>sctcb. \<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s) scp s\<rbrace>"
  apply (simp add: set_mrs_def)
  apply (wpsimp wp: get_object_wp mapM_wp' hoare_drop_imp split_del: if_split
         simp: split_def set_object_def zipWithM_x_mapM)
  by (clarsimp simp: sc_tcb_sc_at_def obj_at_def dest!: get_tcb_SomeD)

lemma set_message_info_sc_tcb_sc_at_not_ct[wp]:
  "\<lbrace> \<lambda>s. sc_tcb_sc_at (\<lambda>sctcb. \<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s) scp s\<rbrace>
   set_message_info thread info \<lbrace> \<lambda>rv s. sc_tcb_sc_at (\<lambda>sctcb. \<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s) scp s\<rbrace>"
  apply (simp add: set_message_info_def)
  apply (wpsimp wp: get_object_wp hoare_drop_imp split_del: if_split
          simp: split_def as_user_def set_object_def)
  by (clarsimp simp: sc_tcb_sc_at_def obj_at_def dest!: get_tcb_SomeD)

lemma sched_context_update_consumed_sc_tcb_sc_at_not_ct[wp]:
  "\<lbrace> \<lambda>s. sc_tcb_sc_at (\<lambda>sctcb. \<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s) scp s\<rbrace>
   sched_context_update_consumed sp \<lbrace> \<lambda>rv s. sc_tcb_sc_at (\<lambda>sctcb. \<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s) scp s\<rbrace>"
  apply (simp add: sched_context_update_consumed_def)
  apply (wpsimp wp: get_object_wp get_sched_context_wp hoare_drop_imp split_del: if_split
           simp: split_def update_sched_context_def set_object_def)
  by (clarsimp simp: sc_tcb_sc_at_def obj_at_def)

lemma set_consumed_sc_tcb_sc_at_not_ct[wp]:
  "\<lbrace> \<lambda>s. sc_tcb_sc_at (\<lambda>sctcb. \<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s) scp s\<rbrace>
   set_consumed sp buf \<lbrace> \<lambda>rv s. sc_tcb_sc_at (\<lambda>sctcb. \<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s) scp s\<rbrace>"
  apply (simp add: set_consumed_def)
  by (wpsimp wp: get_object_wp mapM_wp' hoare_drop_imp split_del: if_split
 simp: split_def set_message_info_def as_user_def set_mrs_def set_object_def sc_tcb_sc_at_def zipWithM_x_mapM)

lemma complete_yield_to_sc_tcb_sc_at_not_ct[wp]:
  "\<lbrace>(\<lambda>s. sc_tcb_sc_at (\<lambda>sctcb. \<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s) scp s) \<rbrace>
  complete_yield_to tcb_ptr \<lbrace>\<lambda>rv s. sc_tcb_sc_at (\<lambda>sctcb. \<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s) scp s \<rbrace>"
  apply (clarsimp simp: complete_yield_to_def maybeM_def)
  apply (rule hoare_seq_ext[OF _ gyt_sp])
  apply (case_tac yt_opt; clarsimp split del: if_split)
   apply wpsimp
  by (wpsimp simp: wp: hoare_vcg_ex_lift lookup_ipc_buffer_inv hoare_drop_imp)

crunches set_thread_state_act
  for ex_nonz_cap_to_ct[wp]: "\<lambda>s. ex_nonz_cap_to (cur_thread s) s"

lemma sts_ex_nonz_cap_to_ct[wp]:
  "\<lbrace>\<lambda>s. ex_nonz_cap_to (cur_thread s) s\<rbrace> set_thread_state t st \<lbrace>\<lambda>rv s. ex_nonz_cap_to (cur_thread s) s\<rbrace>"
  supply if_weak_cong[cong del]
  apply (wpsimp simp: set_thread_state_def set_object_def)
  apply (clarsimp dest!: get_tcb_SomeD)
  by (rule ex_cap_to_after_update; clarsimp simp: obj_at_def ran_tcb_cap_cases)

lemma set_sc_obj_ref_ex_nonz_cap_to_ct[wp]:
  "\<lbrace>\<lambda>s. ex_nonz_cap_to (cur_thread s) s\<rbrace> set_sc_obj_ref f p v \<lbrace>\<lambda>rv s. ex_nonz_cap_to (cur_thread s) s\<rbrace>"
  by (wpsimp simp: set_sc_obj_ref_def set_object_def)

lemma set_tcb_yt_ex_nonz_cap_to_ct[wp]:
  "\<lbrace>\<lambda>s. ex_nonz_cap_to (cur_thread s) s\<rbrace> set_tcb_obj_ref tcb_yield_to_update p v \<lbrace>\<lambda>rv s. ex_nonz_cap_to (cur_thread s) s\<rbrace>"
  supply if_weak_cong[cong del]
  apply (wpsimp simp: set_tcb_obj_ref_def set_object_def)
  apply (clarsimp dest!: get_tcb_SomeD)
  by (rule ex_cap_to_after_update; clarsimp simp: obj_at_def ran_tcb_cap_cases)

lemma complete_yield_to_ex_nonz_ct[wp]:
  "\<lbrace>\<lambda>s. ex_nonz_cap_to (cur_thread s) s\<rbrace> complete_yield_to tcb_ptr \<lbrace>\<lambda>rv s. ex_nonz_cap_to (cur_thread s) s\<rbrace>"
  apply (clarsimp simp: complete_yield_to_def maybeM_def get_tcb_obj_ref_def)
  apply (rule hoare_seq_ext[OF _ thread_get_sp])
  apply (case_tac yt_opt; simp)
   apply wpsimp
  apply (rule hoare_seq_ext[OF _ lookup_ipc_buffer_inv])
  apply (rule hoare_seq_ext[OF _ assert_opt_inv])
  by wpsimp

(*
lemma sts_no_st_refs_ct[wp]:
  "\<lbrace>(\<lambda>s. st_tcb_at (\<lambda>st. tcb_st_refs_of st = {}) (cur_thread s) s) and K( tcb_st_refs_of st = {})\<rbrace>
      set_thread_state tcb_ptr st \<lbrace>\<lambda>rv s. st_tcb_at (\<lambda>st. tcb_st_refs_of st = {}) (cur_thread s) s\<rbrace>"
  by (wpsimp simp: set_thread_state_def set_object_def pred_tcb_at_def obj_at_def)

lemma set_sc_obj_ref_no_st_refs_ct[wp]:
  "\<lbrace>(\<lambda>s. st_tcb_at (\<lambda>st. tcb_st_refs_of st = {}) (cur_thread s) s)\<rbrace>
      set_sc_obj_ref f scptr new \<lbrace>\<lambda>rv s. st_tcb_at (\<lambda>st. tcb_st_refs_of st = {}) (cur_thread s) s\<rbrace>"
  by (wpsimp simp: set_sc_obj_ref_def update_sched_context_def set_object_def pred_tcb_at_def obj_at_def
       wp: get_object_wp)

lemma set_tcb_obj_ref_no_st_refs_ct[wp]:
  "\<lbrace>(\<lambda>s. st_tcb_at (\<lambda>st. tcb_st_refs_of st = {}) (cur_thread s) s)\<rbrace>
      set_tcb_obj_ref tcb_yield_to_update scptr new \<lbrace>\<lambda>rv s. st_tcb_at (\<lambda>st. tcb_st_refs_of st = {}) (cur_thread s) s\<rbrace>"
  apply (wpsimp simp: set_tcb_obj_ref_def set_object_def wp: get_object_wp)
  by (clarsimp dest!: get_tcb_SomeD simp: pred_tcb_at_def obj_at_def)

lemma complete_yield_to_no_st_refs_ct[wp]:
  "\<lbrace>\<lambda>s. st_tcb_at (\<lambda>st. tcb_st_refs_of st = {}) (cur_thread s) s\<rbrace>
      complete_yield_to tcb_ptr \<lbrace>\<lambda>rv s. st_tcb_at (\<lambda>st. tcb_st_refs_of st = {}) (cur_thread s) s\<rbrace>"
  by (wpsimp simp: complete_yield_to_def
 wp: set_thread_state_st_tcb_at set_sc_obj_ref_no_st_refs_ct hoare_drop_imp)
*)
crunches refill_unblock_check
  for arch_state[wp]: "\<lambda>s. P (arch_state s)"
  and cur_sc_tcb[wp]: "cur_sc_tcb"
  (wp: crunch_wps hoare_vcg_if_lift2)

crunch valid_replies[wp]: refill_unblock_check "valid_replies_pred P"
  (simp: crunch_simps wp: crunch_wps)

lemma set_yf_sc_yf_sc_at:
  "\<lbrace>K (scp'= scp)\<rbrace>
   set_sc_obj_ref sc_yield_from_update scp' k
   \<lbrace>\<lambda>rv. sc_yf_sc_at (\<lambda>b. b = k) scp\<rbrace>"
  unfolding set_sc_obj_ref_def
  apply (wpsimp wp: update_sched_context_wp)
  apply (clarsimp simp: sc_at_pred_n_def obj_at_def)
  done

lemma complete_yield_to_sc_yf_sc_at_None:
  "\<lbrace>sc_yf_sc_at ((=) (Some tptr)) scp and invs\<rbrace>
   complete_yield_to tptr
   \<lbrace>\<lambda>rv. sc_yf_sc_at ((=) None) scp\<rbrace>"
  unfolding complete_yield_to_def
  apply (clarsimp simp: sc_at_pred_n_eq_commute)
  apply (wpsimp wp: set_yf_sc_yf_sc_at thread_get_wp simp: get_tcb_obj_ref_def)
  apply (clarsimp simp: obj_at_def sc_at_pred_n_def)
  apply (subgoal_tac "bound_yt_tcb_at (\<lambda>b. b = (Some scp)) tptr s")
   apply (clarsimp simp: obj_at_def sc_at_pred_n_def pred_tcb_at_def)
  apply (subgoal_tac "(scp, TCBYieldTo) \<in> state_refs_of s tptr")
   apply (clarsimp simp: pred_tcb_at_def obj_at_def state_refs_of_def refs_of_def
                  split: option.splits)
   apply (case_tac x2; clarsimp simp: get_refs_def split: option.splits)
  apply (rule sym_refsE; clarsimp)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def state_refs_of_def refs_of_def
                 split: option.splits)
  done

crunches sched_context_resume (* FIXME: investigate why wps doesn't work in the lemma below *)
  for tcb_at_ct[wp]: "\<lambda>s. tcb_at (cur_thread s) s"
  and ex_cap_ct[wp]: "\<lambda>s. ex_nonz_cap_to (cur_thread s) s"
  and state_refs_of_ct[wp]: "\<lambda>s. P (state_refs_of s) (cur_thread s)"
  and it_ct[wp]: "\<lambda>s. P (idle_thread s) (cur_thread s)"
  (wp: crunch_wps simp: crunch_simps)

lemma sched_context_yield_to_invs:
  notes refs_of_simps [simp del]
  shows
  "\<lbrace>invs and (\<lambda>s. cur_thread s \<noteq> idle_thread s ) \<comment> \<open> cur_thread must be set to Restart \<close>
    and (\<lambda>s. bound_yt_tcb_at ((=) None) (cur_thread s) s)
    and (\<lambda>s. sc_tcb_sc_at (\<lambda>sctcb.\<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s) scp s)
    and (\<lambda>s. ex_nonz_cap_to (cur_thread s) s) and ex_nonz_cap_to scp\<rbrace>
       sched_context_yield_to scp args \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (unfold sched_context_yield_to_def get_sc_obj_ref_def bind_assoc)
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply clarsimp
  apply (rule hoare_seq_ext[where B=
          "\<lambda>_. invs and (\<lambda>s. cur_thread s \<noteq> idle_thread s) and
               (\<lambda>s. bound_yt_tcb_at ((=) None) (cur_thread s) s) and
               (\<lambda>s. sc_yf_sc_at ((=) None) scp s) and
               (\<lambda>s. sc_tcb_sc_at (\<lambda>sctcb. \<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s) scp s) and
               (\<lambda>s. ex_nonz_cap_to (cur_thread s) s) and
               ex_nonz_cap_to scp", rotated])
   apply (wpsimp wp: complete_yield_to_invs hoare_drop_imps complete_yield_to_sc_yf_sc_at_None)
   apply (clarsimp simp: obj_at_def sc_at_pred_n_def)
  apply (clarsimp simp: sc_at_pred_n_eq_commute)
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def get_sc_obj_ref_def
           split_del: if_split
                  wp: valid_irq_node_typ hoare_vcg_if_lift2 thread_get_inv hoare_drop_imp
                      valid_ioports_lift)
  apply (intro conjI)
     apply (clarsimp simp: cur_tcb_def)
    apply (clarsimp simp: sc_at_pred_n_def obj_at_def is_sc_obj_def)
    apply (fastforce dest!: valid_objs_valid_sched_context_size)
   apply (erule delta_sym_refs)
    apply (clarsimp split: if_splits)
    apply (clarsimp simp: sc_at_pred_n_def obj_at_def pred_tcb_at_def is_sc_obj_def)
   apply (clarsimp split: if_splits)
     apply (clarsimp simp: sc_at_pred_n_def obj_at_def pred_tcb_at_def is_sc_obj_def)
    apply (clarsimp simp: obj_at_def pred_tcb_at_def state_refs_of_def refs_of_def get_refs_def
                   split: option.splits)
   apply (clarsimp simp: sc_at_pred_n_def obj_at_def state_refs_of_def refs_of_def get_refs_def
                  split: option.splits)
  apply (clarsimp simp: sc_at_pred_n_def obj_at_def valid_idle_def pred_tcb_at_def)
  apply (clarsimp dest!: idle_sc_no_ex_cap)
  done

text {* valid invocation definitions *}
primrec
  valid_sched_context_inv :: "sched_context_invocation \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
    "valid_sched_context_inv (InvokeSchedContextConsumed scptr args)
     = (sc_at scptr and ex_nonz_cap_to scptr)"
  | "valid_sched_context_inv (InvokeSchedContextBind scptr cap)
     = (ex_nonz_cap_to scptr and valid_cap cap and
          (case cap of ThreadCap t \<Rightarrow> bound_sc_tcb_at ((=) None) t
                                      and ex_nonz_cap_to t and sc_tcb_sc_at ((=) None) scptr
             | NotificationCap n _ _ \<Rightarrow>
                   obj_at (\<lambda>ko. \<exists>ntfn. ko = Notification ntfn \<and> ntfn_sc ntfn = None) n
                   and ex_nonz_cap_to n  and sc_ntfn_sc_at ((=) None) scptr
             | _ \<Rightarrow> \<lambda>_. False))"
  | "valid_sched_context_inv (InvokeSchedContextUnbindObject scptr cap)
     = (ex_nonz_cap_to scptr and valid_cap cap and
          (case cap of ThreadCap t \<Rightarrow>
                   ex_nonz_cap_to t and sc_tcb_sc_at (\<lambda>tcb. tcb = (Some t)) scptr and (\<lambda>s. t \<noteq> cur_thread s)
             | NotificationCap n _ _ \<Rightarrow>
                   ex_nonz_cap_to n and sc_ntfn_sc_at (\<lambda>ntfn. ntfn = (Some n)) scptr
             | _ \<Rightarrow> \<lambda>_. False))"
  | "valid_sched_context_inv (InvokeSchedContextUnbind scptr cap)
     = (sc_at scptr and ex_nonz_cap_to scptr and (\<lambda>s. obj_ref_of cap \<noteq> cur_thread s))"
  | "valid_sched_context_inv (InvokeSchedContextYieldTo scptr args)
     = (\<lambda>s. ex_nonz_cap_to scptr s
            \<and> bound_yt_tcb_at ((=) None) (cur_thread s) s
            \<and> sc_tcb_sc_at (\<lambda>sctcb. \<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s) scptr s)"

definition
  valid_refills_number :: "nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "valid_refills_number mrefills n \<equiv>
    mrefills \<le> (nat (1 << n) - core_sched_context_bytes) div refill_size_bytes + MIN_REFILLS"

primrec
  valid_sched_control_inv :: "sched_control_invocation \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
    "valid_sched_control_inv (InvokeSchedControlConfigure scptr budget period mrefills badge)
     = (obj_at (\<lambda>ko. \<exists>sc n. ko = SchedContext sc n \<and> valid_refills_number mrefills n) scptr
        and ex_nonz_cap_to scptr and K (MIN_REFILLS \<le> mrefills) (* mrefills = MIN_REFILLS + extra_refills *)
        and K (budget \<le> us_to_ticks maxTimer_us \<and> budget \<ge> MIN_BUDGET)
        and K (period \<le> us_to_ticks maxTimer_us \<and> budget \<ge> MIN_BUDGET)
        and K (budget \<le> period))"


text {* refill invariant proofs *}  (* FIXME move? Sporadic_AI? *)

definition valid_refill_amount :: "obj_ref \<Rightarrow> time \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_refill_amount scptr budget =
     (obj_at (\<lambda>ko. \<exists>sc n. ko= SchedContext sc n
      \<and> refills_sum (sc_refills sc) = budget) scptr)"

definition valid_refill_length :: "obj_ref \<Rightarrow> time \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_refill_length scptr budget =
     (obj_at (\<lambda>ko. \<exists>sc n. ko= SchedContext sc n
      \<and> 1 \<le> length (sc_refills sc)
      \<and> MIN_REFILLS \<le> sc_refill_max sc
      \<and> length (sc_refills sc) \<le> sc_refill_max sc
      \<and> (sc_period sc = 0 \<longrightarrow> (sc_refill_max sc = MIN_REFILLS
                               \<and> length (sc_refills sc) = MIN_REFILLS))) scptr)"

definition valid_refills :: "obj_ref \<Rightarrow> time \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_refills scptr budget =
     (obj_at (\<lambda>ko. \<exists>sc n. ko= SchedContext sc n
      \<and> refills_sum (sc_refills sc) = budget
      \<and> 1 \<le> length (sc_refills sc)
      \<and> MIN_REFILLS \<le> sc_refill_max sc
      \<and> length (sc_refills sc) \<le> sc_refill_max sc
      \<and> (sc_period sc = 0 \<longrightarrow> (sc_refill_max sc = MIN_REFILLS
                               \<and> length (sc_refills sc) = MIN_REFILLS))) scptr)"

lemma valid_refills_def2:
  "valid_refills = (\<lambda>p b. valid_refill_amount p b and valid_refill_length p b)"
  by (fastforce simp: valid_refills_def valid_refill_amount_def valid_refill_length_def obj_at_def)

definition sc_valid_refills :: "sched_context \<Rightarrow> time \<Rightarrow> bool"
where
  "sc_valid_refills sc budget =
      (refills_sum (sc_refills sc) = budget
      \<and> 1 \<le> length (sc_refills sc)
      \<and> MIN_REFILLS \<le> sc_refill_max sc
      \<and> length (sc_refills sc) \<le> sc_refill_max sc
      \<and> (sc_period sc = 0 \<longrightarrow> (sc_refill_max sc = MIN_REFILLS
                               \<and> length (sc_refills sc) = MIN_REFILLS)))"

lemma valid_refills_consumed_time_update[iff]:
  "valid_refills p b (consumed_time_update f s) = valid_refills p b s"
  by (simp add: valid_refills_def)

lemma valid_refills_scheduler_action_update[iff]:
  "valid_refills p b (scheduler_action_update f s) = valid_refills p b s"
  by (simp add: valid_refills_def)

lemma valid_refills_ready_queues_update[iff]:
  "valid_refills p b (ready_queues_update f s) = valid_refills p b s"
  by (simp add: valid_refills_def)

lemma valid_refills_release_queue_update[iff]:
  "valid_refills p b (release_queue_update f s) = valid_refills p b s"
  by (simp add: valid_refills_def)

lemma valid_refills_kheap_tcb_update[iff]:
  "tcb_at t s \<Longrightarrow> valid_refills p b (s\<lparr>kheap := kheap s(t \<mapsto> TCB tcb)\<rparr>) = valid_refills p b s"
  by (clarsimp simp: valid_refills_def obj_at_def is_tcb)

crunches tcb_sched_action,set_scheduler_action, refill_capacity, refill_sufficient,
tcb_release_enqueue, tcb_release_remove, refill_ready, reschedule_required, possible_switch_to
  for valid_refills[wp]: "valid_refills scp budget"
  (wp: dxo_wp_weak hoare_vcg_if_lift2 crunch_wps)

crunch valid_refills[wp]: tcb_sched_action,set_scheduler_action,refill_capacity,refill_sufficient
   "valid_refills scp budget"
crunch valid_refills[wp]: tcb_release_enqueue,tcb_release_remove,refill_ready "valid_refills scp budget"
  (wp: crunch_wps)

crunch valid_refills[wp]: reschedule_required,
possible_switch_to "valid_refills scp budget"
  (wp: dxo_wp_weak hoare_vcg_if_lift2 crunch_wps)

lemma valid_refills_exst [iff]:
  "valid_refills p b (trans_state f s) = valid_refills p b s"
  by (simp add: valid_refills_def valid_state_def)

lemma valid_refills_reprogram_timer_update [iff]:
  "valid_refills p b (reprogram_timer_update f s) = valid_refills p b s"
  by (simp add: valid_refills_def valid_state_def)

crunches postpone
  for valid_refills[wp]: "valid_refills sc b"
  (wp: crunch_wps)

lemma sched_context_resume_valid_refills[wp]:
  "\<lbrace>valid_refills scptr budget\<rbrace> sched_context_resume p \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"
  by (wpsimp simp: sched_context_resume_def wp: hoare_vcg_if_lift2 hoare_drop_imp)

crunch valid_refills[wp]: sort_queue "valid_refills scp budget"  (wp: mapM_wp')

lemma update_sched_context_valid_refills_no_budget_update_const:
  "\<lbrace>valid_refills scptr budget
     and K (scptr=p \<longrightarrow> sc_valid_refills newsc budget)\<rbrace>
     update_sched_context p (\<lambda>_. newsc)
      \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"
  by (wpsimp simp: valid_refills_def update_sched_context_def obj_at_def sc_valid_refills_def
          wp: set_object_wp get_object_wp)

lemma update_sched_context_valid_refills:
  "\<lbrace>valid_refills scptr budget
     and K (1 \<le> length (sc_refills newsc)\<and>MIN_REFILLS \<le> sc_refill_max newsc
         \<and> length (sc_refills newsc) \<le> sc_refill_max newsc
         \<and> (sc_period newsc = 0 \<longrightarrow> (sc_refill_max newsc = MIN_REFILLS
                               \<and> length (sc_refills newsc) = MIN_REFILLS)))\<rbrace>
     update_sched_context p (\<lambda>_. newsc)
      \<lbrace>\<lambda>_. valid_refills scptr (if p = scptr then refills_sum (sc_refills newsc) else budget)\<rbrace>"
  apply (wpsimp simp: valid_refills_def update_sched_context_def obj_at_def
          wp: set_object_wp get_object_wp split_del: if_split)
  by clarsimp

lemma update_sched_context_valid_refills':
  "\<lbrace>K (1 \<le> length (sc_refills newsc) \<and> MIN_REFILLS \<le> sc_refill_max newsc
          \<and> length (sc_refills newsc) \<le> sc_refill_max newsc
          \<and> (sc_period newsc = 0 \<longrightarrow> (sc_refill_max newsc = MIN_REFILLS
                               \<and> length (sc_refills newsc) = MIN_REFILLS)))\<rbrace>
   update_sched_context p (\<lambda>_. newsc)  \<lbrace>\<lambda>_. valid_refills p (refills_sum (sc_refills newsc))\<rbrace>"
  by (wpsimp simp: valid_refills_def update_sched_context_def obj_at_def
            wp: set_object_wp get_object_wp)

lemma update_sched_context_valid_refills_no_budget_update:
  "\<lbrace>valid_refills scptr budget and K (\<forall>sc. sc_valid_refills sc budget \<longrightarrow> sc_valid_refills (f sc) budget)\<rbrace>
     update_sched_context p f
      \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"
  apply (wpsimp simp: update_sched_context_def obj_at_def
          wp: set_object_wp get_object_wp)
  by (clarsimp simp: valid_refills_def obj_at_def sc_valid_refills_def)

lemma set_thread_state_valid_refills[wp]:
  "\<lbrace>valid_refills scptr budget\<rbrace> set_thread_state tp st \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"
  by (wpsimp wp: sts_obj_at_impossible simp: valid_refills_def)

lemma refill_add_tail_valid_refills:
  "\<lbrace>valid_refills scptr budget\<rbrace>
     refill_add_tail p new
      \<lbrace>\<lambda>_. valid_refills scptr (budget + (if scptr = p then r_amount new else 0))\<rbrace>"
  apply (wpsimp wp: get_refills_wp get_sched_context_wp set_object_wp get_object_wp
           simp: refill_add_tail_def set_refills_def update_sched_context_def split_del: if_split)
  by (clarsimp simp: valid_refills_def obj_at_def refills_sum_def)

lemma maybe_add_empty_tail_valid_refills:
  "\<lbrace>valid_refills scptr budget\<rbrace> maybe_add_empty_tail p \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"
  apply (wpsimp wp: get_refills_wp get_sched_context_wp set_object_wp get_object_wp
           simp: maybe_add_empty_tail_def refill_add_tail_def is_round_robin_def
                 set_refills_def update_sched_context_def)
  by (clarsimp simp: valid_refills_def obj_at_def refills_sum_def)

lemma refill_new_valid_refills[wp]:
  "\<lbrace>valid_refills scptr budget and K (MIN_REFILLS \<le> max_refills \<and> (period = 0 \<longrightarrow> max_refills = MIN_REFILLS))\<rbrace>
    refill_new p max_refills budget period \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"
  apply (wpsimp simp: refill_new_def update_sched_context_def maybe_add_empty_tail_def
           refill_add_tail_def set_refills_def is_round_robin_def
            wp:  set_object_wp get_object_wp get_sched_context_wp)
  by (clarsimp simp: valid_refills_def refills_sum_def obj_at_def MIN_REFILLS_def)

lemma refill_update_valid_refills[wp]:
  "\<lbrace>valid_refills scptr new_budget and
    K (MIN_REFILLS \<le> new_max_refills \<and> (new_period = 0 \<longrightarrow> new_max_refills = MIN_REFILLS))\<rbrace>
     refill_update p new_period new_budget new_max_refills
      \<lbrace>\<lambda>_. valid_refills scptr new_budget\<rbrace>"
  apply (clarsimp simp: refill_update_def)
  apply (rule hoare_assume_pre)
  apply (wpsimp simp: set_refills_def get_refills_def set_object_def is_round_robin_def
                      update_sched_context_def maybe_add_empty_tail_def refill_add_tail_def
                      update_sched_context_def
                split_del: if_split
                wp: get_object_wp get_sched_context_wp hoare_vcg_if_lift2)
  apply clarsimp
  apply (intro conjI impI; clarsimp simp: valid_refills_def obj_at_def refills_sum_def MIN_REFILLS_def)
  done

lemma sum_list_but_last[iff]:
  "lista \<noteq> [] \<Longrightarrow> sum_list (map r_amount (butlast lista)) + r_amount (last lista) =
            sum_list (map r_amount lista)"
  apply (subgoal_tac "sum_list (map r_amount (butlast lista)) + r_amount (last lista)
           = sum_list (map r_amount ((butlast lista) @ [last lista]))")
   apply (drule trans)
    prefer 2
    apply simp
   apply (subst append_butlast_last_id)
    apply blast+
  apply (clarsimp simp del:append_butlast_last_id)+
  done

lemma schedule_used_non_nil:
  "Suc 0 \<le> length (schedule_used x new)"
  by (induct x; clarsimp simp: Let_def)

lemma schedule_used_length':
  "length (schedule_used x new) = length x \<or> length (schedule_used x new) = length x + 1"
  by (induct x; clarsimp simp: Let_def)

lemma schedule_used_length:
  "length (schedule_used x new) =
   (if ((r_amount new < MIN_BUDGET \<and> 2 \<le> length x) \<or> (x \<noteq> [] \<and> r_time new \<le> r_time (last x)))
    then length x else length x + 1)"
  by (induct x; clarsimp simp: Let_def length_greater_0_conv[symmetric] simp del: length_greater_0_conv)

lemma schedule_used_sum [simp]:
  "refills_sum (schedule_used refills new) = refills_sum (refills @ [new])"
  apply (induct refills arbitrary: new, simp)
  apply (clarsimp simp: refills_sum_def Let_def)
  done

lemma refills_budget_check_pos:
  "\<lbrakk>refills_budget_check period usage rfls = (t, ls); Suc 0 \<le> length rfls\<rbrakk>
    \<Longrightarrow> Suc 0 \<le> length ls "
  apply (induct rfls arbitrary: t ls rule: refills_budget_check.induct)
   apply simp
  apply simp
  apply (clarsimp simp: split: if_split_asm)
  apply (clarsimp simp add: schedule_used_non_nil)
  done

lemma refills_budget_check_length[intro]:
  "Suc 0 \<le> length rfls \<Longrightarrow> Suc 0 \<le> length (snd (refills_budget_check period usage rfls))"
  apply (induct rfls arbitrary:  rule: refills_budget_check.induct)
   apply simp
  apply simp
  apply (clarsimp simp: split: if_split_asm)
  apply (clarsimp simp add: schedule_used_non_nil)
  done

lemma refills_budget_check_length_max[intro]:
  "length rfls \<le> L \<Longrightarrow> length (snd (refills_budget_check period usage rfls)) \<le> L"
  apply (induct rfls arbitrary: L rule: refills_budget_check.induct)
   apply simp
  apply simp
  apply (clarsimp simp: split: if_split_asm)
  apply (drule_tac x=L in meta_spec)
  apply (drule meta_mp)
  apply (clarsimp simp add: schedule_used_non_nil schedule_used_length)
  apply simp
  done

lemma refills_sum_cons[simp]: "refills_sum (a#rs) =  r_amount a + refills_sum rs"
  by (clarsimp simp: refills_sum_def)

lemma refills_sum_append[simp]: "refills_sum (rs1 @ rs) =  refills_sum rs1 + refills_sum rs"
  by (clarsimp simp: refills_sum_def)

lemma refills_sum_nil[simp]: "refills_sum [] = 0" by (clarsimp simp: refills_sum_def)

lemma refills_budget_check_sum [simp]:
  "refills_sum (snd (refills_budget_check period usage rfls)) = refills_sum (rfls)"
  apply (induct usage arbitrary: rfls rule: measure_induct[where f=id])
  apply simp
  apply (induct_tac rfls, simp)
  apply (clarsimp split: if_split_asm)
  apply (drule_tac x="x - r_amount a" in spec)
  apply (subgoal_tac "x - r_amount a < x")
   apply (clarsimp)
  by (simp add: word_diff_less)

lemma valid_refills_sc_update:
  "(valid_refills p b (s\<lparr>kheap := kheap s(p \<mapsto> SchedContext sc n)\<rparr>))
       = (sc_valid_refills sc b)"
  by (clarsimp simp: valid_refills_def obj_at_def sc_valid_refills_def)


definition
  sc_at_period :: "(time \<Rightarrow> bool) \<Rightarrow> obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "sc_at_period P  = obj_at (\<lambda>ko. \<exists>sc n. ko = SchedContext sc n \<and> P (sc_period sc))"

(* min_budget_merge *)

lemma min_budget_merge_bounded:
  "MIN_BUDGET \<le> refills_sum (a#ls) \<longrightarrow>
         MIN_BUDGET \<le> r_amount (hd (min_budget_merge b (a#ls)))"
  by (induction ls arbitrary: b a; clarsimp)
     (auto simp: add.commute add.left_commute)

lemma min_budget_merge_sufficient:
  "ls \<noteq> [] \<longrightarrow> MIN_BUDGET \<le> refills_sum ls \<longrightarrow>
         MIN_BUDGET \<le> r_amount (hd (min_budget_merge b ls))"
  by (cases ls; clarsimp simp: min_budget_merge_bounded)

lemma min_budget_merge_helper:
  "refills_sum (min_budget_merge b (r0#r1#rs)) = refills_sum (r0#r1#rs)"
  apply (induction rs arbitrary: r0 r1 b, clarsimp simp: refills_sum_def)
  apply (clarsimp)
  apply (drule_tac x="r1\<lparr>r_amount := r_amount r0 + r_amount r1\<rparr>" in meta_spec)
  apply (drule_tac x=a in meta_spec)
  apply (clarsimp simp: refills_sum_def)
 done

lemma min_budget_merge_refills_sum[iff]:
  "refills_sum (min_budget_merge b refills) = refills_sum refills"
  apply (cases refills, simp)
  apply (case_tac list, simp)
  by (simp only: min_budget_merge_helper)

lemma refill_split_check_valid_refills[wp]: (* applicable only when sc is not round_robin *)
  "\<lbrace>valid_refills scptr budget and (\<lambda>s. sc_at_period (\<lambda>p. p \<noteq> 0) (cur_sc s) s)\<rbrace>
   refill_split_check consumed
   \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"
  supply if_weak_cong[cong del] schedule_used.simps[simp del]
  apply (unfold refill_split_check_def)
  apply (simp add: Let_def set_refills_def update_sched_context_def sc_at_period_def obj_at_def
              split del: if_split)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rename_tac ctime)
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (clarsimp split del: if_split)
  apply (rename_tac sc)
  apply (case_tac "length (sc_refills sc) = sc_refill_max sc \<or>
             r_amount (refill_hd sc) - consumed < MIN_BUDGET")
   apply (case_tac "length (sc_refills sc) = Suc 0")
    apply (clarsimp split del: if_split)
    apply (wpsimp wp: get_refills_wp set_object_wp get_object_wp get_sched_context_wp
                      hoare_vcg_if_lift2 hoare_drop_imp
                simp: update_sched_context_def split_del: if_split)
    apply (case_tac "sc_refills x"; clarsimp simp: valid_refills_def obj_at_def refills_sum_def)
   apply clarsimp
   apply (wpsimp wp: get_refills_wp set_object_wp get_object_wp get_sched_context_wp
                     hoare_vcg_if_lift2 hoare_drop_imp
               simp: update_sched_context_def split_del: if_split)
   apply (case_tac "cur_sc s =scptr")
    apply (clarsimp simp: valid_refills_def obj_at_def schedule_used_length MIN_REFILLS_def
      split del: if_split)
    apply (rename_tac sc n)
    apply (case_tac "sc_refills sc", simp)
    apply (case_tac "list";
           clarsimp simp: valid_refills_def obj_at_def refills_sum_def
                          conjunct1[OF min_budget_merge_length, simplified]
                          schedule_used_non_nil)
    apply (rule le_trans)
     apply (rule conjunct2[OF min_budget_merge_length, simplified, OF schedule_used_non_nil])
    apply (subgoal_tac "length
             (schedule_used
               (aa\<lparr>r_amount := r_amount aa + (r_amount a - consumed)\<rparr> # lista)
               \<lparr>r_time = r_time a + sc_period sc, r_amount = consumed\<rparr>) \<le> Suc (Suc (length lista))")
     apply simp
    apply (simp add: schedule_used_length)
   apply (clarsimp simp: valid_refills_def obj_at_def)
  apply clarsimp
  apply (wpsimp wp: get_refills_wp set_object_wp get_object_wp get_sched_context_wp
                    hoare_vcg_if_lift2 hoare_drop_imp
              simp: update_sched_context_def split_del: if_split)
  apply (case_tac "cur_sc s=scptr")
   apply (clarsimp simp: valid_refills_def obj_at_def schedule_used_length MIN_REFILLS_def
              split del: if_split)
   apply (rename_tac sc n)
   apply (case_tac "sc_refills sc"; simp)
  apply (clarsimp simp: valid_refills_def obj_at_def)
  done

lemma set_min_budget_merge_valid_refills:
  "\<lbrace>valid_refills scptr budget
    and obj_at (\<lambda>ko. \<exists>n. ko = SchedContext sc n \<and> sc_period sc \<noteq> 0) p\<rbrace>
    set_refills p (min_budget_merge full (sc_refills sc)) \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"
apply (unfold set_refills_def)
  apply (wpsimp simp: set_refills_def update_sched_context_def set_object_def
                wp: get_object_wp get_sched_context_wp)
  apply (clarsimp simp: valid_refills_def obj_at_def)
  apply (drule min_budget_merge_length[of "sc_refills sc" full, simplified])
  apply auto
  done

crunch obj_at[wp]: refill_full "obj_at P p"

lemma refill_full_valid_refills[wp]:
  "\<lbrace>valid_refills scptr budget\<rbrace> refill_full p \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"
  by (wpsimp simp: refill_full_def)
lemma refills_budget_check_valid_refills:
  "\<lbrace>valid_refills scptr budget
    and obj_at (\<lambda>ko. \<exists>n. ko = SchedContext sc n \<and> sc_period sc \<noteq> 0) p\<rbrace>
    set_refills p (snd (refills_budget_check (sc_period sc) usage (sc_refills sc)))
   \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"
  apply (wpsimp simp: set_refills_def update_sched_context_def set_object_def
                wp: get_object_wp get_sched_context_wp)
  apply (clarsimp simp: valid_refills_def obj_at_def)
  apply (drule refills_budget_check_length[where rfls="sc_refills sc", simplified])
  apply auto
  done

lemma update_sc_consumed_valid_refills[wp]:
  "\<lbrace>valid_refills p budget and sc_at ptr\<rbrace>
   update_sched_context ptr (\<lambda>sc. sc_consumed_update f sc)
      \<lbrace>\<lambda>_. valid_refills p budget\<rbrace>"
  by (wpsimp simp: valid_refills_def update_sched_context_def obj_at_def
            wp: set_object_wp get_object_wp)

lemma update_min_budget_merge_valid_refills:
  "\<lbrace>valid_refills scptr budget and sc_at_period (\<lambda>p. p \<noteq> 0) p\<rbrace>
    update_sched_context p (sc_refills_update (min_budget_merge full))
    \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"
  apply (wpsimp simp: set_refills_def update_sched_context_def set_object_def
                wp: get_object_wp get_sched_context_wp)
  apply (clarsimp simp: valid_refills_def obj_at_def sc_at_period_def)
  apply (drule_tac ls="sc_refills x" in min_budget_merge_length[of _ full, simplified])
  apply auto
  done


lemma helper0:
  "\<lbrace>\<lambda>s. valid_refills scptr budget s \<and> cur_sc s = sc_ptr \<and>
        (\<exists>n. ko_at (SchedContext sc n) sc_ptr s) \<and> 0 < sc_period sc \<rbrace>
   set_refills sc_ptr
     (if 0 < fst (refills_budget_check (sc_period sc) usage (sc_refills sc))
      then let r1 = hd (snd (refills_budget_check (sc_period sc) usage (sc_refills sc)));
               r1' = r1\<lparr>r_time := r_time r1 + usage\<rparr>;
               rs = tl (snd (refills_budget_check (sc_period sc) usage (sc_refills sc)))
           in if rs \<noteq> [] \<and> can_merge_refill r1' (hd rs)
              then merge_refill r1' (hd rs) # tl rs else r1' # rs
      else snd (refills_budget_check (sc_period sc) usage (sc_refills sc)))
   \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"
  apply (wpsimp simp: set_refills_def update_sched_context_def set_object_def
                  wp: get_object_wp split_del: if_split)
  apply (clarsimp simp: obj_at_def valid_refills_def word_gt_0 split del: if_split)
  apply (case_tac "scptr=cur_sc s"; simp split del: if_split)
  apply (frule_tac period="(sc_period sca)" and usage=usage in refills_budget_check_length)
  apply (frule_tac period="(sc_period sca)" and usage=usage in refills_budget_check_length_max)
  apply (clarsimp simp: split del: if_split)
  apply (clarsimp simp: can_merge_refill_def merge_refill_def Let_def MIN_REFILLS_def
          split del: if_split cong: if_cong)
  apply (case_tac "snd (refills_budget_check (sc_period sc) usage (sc_refills sc))"; simp split del: if_split)
  apply (case_tac list; simp split del: if_split)
   apply (subst refills_budget_check_sum[of "(sc_period sc)" usage "(sc_refills sc)", symmetric])
   apply (simp split del: if_split)
   apply (clarsimp simp: split del: if_split)
   apply (intro conjI)
     defer
     apply (clarsimp+)[2]
   apply (subst refills_budget_check_sum[of "(sc_period sc)" usage "(sc_refills sc)", symmetric], simp split del: if_split)
   apply clarsimp
  apply (clarsimp simp: refill_sum_def)
  done

crunch sc_at_period[wp]: refill_full "sc_at_period P p"

lemma set_refills_sc_at_period[wp]:
  "\<lbrace>sc_at_period P p\<rbrace> set_refills sc_ptr refills \<lbrace>\<lambda>_. sc_at_period P p\<rbrace>"
  apply (wpsimp simp: set_refills_def update_sched_context_def set_object_def
             wp: get_object_wp)
  by (clarsimp simp: sc_at_period_def obj_at_def)

crunch sc_at_period'[wp]: refill_full "\<lambda>s. sc_at_period P (cur_sc s) s"

lemma set_refills_sc_at_period'[wp]:
  "\<lbrace>\<lambda>s. sc_at_period P (cur_sc s) s\<rbrace> set_refills sc_ptr refills \<lbrace>\<lambda>_ s. sc_at_period P (cur_sc s) s\<rbrace>"
  apply (wpsimp simp: set_refills_def update_sched_context_def set_object_def
             wp: get_object_wp)
  by (clarsimp simp: sc_at_period_def obj_at_def)

lemma refill_split_check_sc_at_period[wp]:
  "\<lbrace>sc_at_period P p\<rbrace> refill_split_check usage \<lbrace>\<lambda>_. sc_at_period P p\<rbrace>"
  apply (clarsimp simp: refill_split_check_def)
  apply (wpsimp simp: Let_def split_del: if_split wp: get_sched_context_wp)
  done

lemma refill_split_check_sc_at_period'[wp]:
  "\<lbrace>\<lambda>s. sc_at_period P (cur_sc s) s\<rbrace> refill_split_check usage \<lbrace>\<lambda>_ s. sc_at_period P (cur_sc s) s\<rbrace>"
  apply (clarsimp simp: refill_split_check_def)
  apply (wpsimp simp: Let_def split_del: if_split wp: get_sched_context_wp)
  done

lemma refill_budget_check_valid_refills[wp]:
   "\<lbrace>valid_refills scptr budget and (\<lambda>s. sc_at_period (\<lambda>p. p \<noteq> 0) (cur_sc s) s)\<rbrace>
    refill_budget_check usage capacity
    \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"
  supply if_weak_cong[cong del]
  apply (clarsimp simp: refill_budget_check_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (rule hoare_seq_ext[OF _ assert_sp])
  apply (rule hoare_seq_ext[OF _ assert_sp])
  apply (clarsimp split del: if_split simp: split_def)
  apply (case_tac "capacity = 0"; clarsimp split del: if_split)
   apply (wpsimp wp: update_min_budget_merge_valid_refills helper0 weak_if_wp)
  apply (wpsimp wp: update_min_budget_merge_valid_refills)
   apply (wpsimp simp: set_refills_def update_sched_context_def set_object_def wp: get_object_wp)
  apply (fastforce simp: valid_refills_def obj_at_def sc_at_period_def)
  done

lemma valid_refills_sc_consumed_update[iff]:
    "valid_refills p b (s\<lparr>kheap := kheap s(p' \<mapsto> SchedContext (sc\<lparr>sc_consumed:=x\<rparr>) n)\<rparr>)
         = valid_refills p b (s\<lparr>kheap := kheap s(p' \<mapsto> SchedContext sc n)\<rparr>)"
  by (clarsimp simp: valid_refills_def obj_at_def)

lemma valid_refills_domain_time_update[simp]:
  "valid_refills sc b (domain_time_update f s) = valid_refills sc b s"
  by (simp add: valid_refills_def)

crunches commit_domain_time
  for valid_refills[wp]: "valid_refills sc b"

lemma commit_time_valid_refills[wp]:
  "\<lbrace>\<lambda>s. valid_refills ptr budget s\<rbrace> commit_time \<lbrace>\<lambda>_ s. valid_refills ptr budget s\<rbrace>"
  apply (clarsimp simp: commit_time_def)
  apply (wpsimp simp: set_object_def sc_valid_refills_def
      wp: get_object_wp update_sc_consumed_valid_refills update_sched_context_valid_refills_no_budget_update
      simp_del: fun_upd_apply)
       apply (wpsimp simp: set_refills_def set_object_def update_sched_context_def
      wp: get_object_wp get_sched_context_wp )
      apply (wpsimp simp: sc_valid_refills_def
         wp: hoare_drop_imp hoare_vcg_all_lift refill_split_check_valid_refills get_sched_context_wp)
     apply (wpsimp wp: get_sched_context_wp)+
  apply (rule conjI; clarsimp split del: if_split)
   apply (rule conjI; clarsimp split del: if_split)
    apply (clarsimp simp: valid_refills_def obj_at_def refills_sum_def MIN_REFILLS_def)
    apply (case_tac "sc_refills sc", simp)
    apply (case_tac list; simp)
   apply (clarsimp simp: sc_valid_refills_def valid_refills_def obj_at_def refills_sum_def MIN_REFILLS_def)
   apply (clarsimp simp: sc_at_period_def obj_at_def)
  apply (clarsimp simp: sc_valid_refills_def valid_refills_def obj_at_def refills_sum_def MIN_REFILLS_def)
  done

lemmas valid_refills_kheap_tcb_update'[iff] = valid_refills_kheap_tcb_update[simplified fun_upd_def obj_at_def is_tcb]

lemma thread_set_valid_refills[wp]:
  "\<lbrace>valid_refills scptr budget\<rbrace> thread_set f tptr \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"
  apply (wpsimp simp: thread_set_def set_object_def simp_del: fun_upd_apply)
  apply (clarsimp simp: dest!:get_tcb_SomeD)
  done

lemma set_simple_ko_valid_refills[wp]:
  "\<lbrace>valid_refills scptr budget\<rbrace> set_simple_ko C ptr new \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"
  apply (wpsimp simp: set_simple_ko_def set_object_def partial_inv_def a_type_def
         wp: get_object_wp simp_del: fun_upd_apply split: kernel_object.splits)
  apply (intro conjI impI; clarsimp simp: valid_refills_def obj_at_def)
  done

lemma sc_replies_update_valid_refills[wp]:
  "\<lbrace>valid_refills scptr budget\<rbrace>
      set_sc_obj_ref sc_replies_update ptr new \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"
  apply (wpsimp simp: set_sc_obj_ref_def set_object_def
         wp: get_object_wp update_sched_context_valid_refills_no_budget_update get_sched_context_wp)
  apply (clarsimp simp: valid_refills_def obj_at_def sc_valid_refills_def)
  done

lemma sc_tcb_update_valid_refills[wp]:
  "\<lbrace>valid_refills scptr budget\<rbrace>
      set_sc_obj_ref sc_tcb_update ptr new \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"
  apply (wpsimp simp: set_sc_obj_ref_def set_object_def
         wp: get_object_wp update_sched_context_valid_refills_no_budget_update get_sched_context_wp)
  apply (clarsimp simp: valid_refills_def obj_at_def sc_valid_refills_def)
  done

lemma set_tcb_obj_ref_valid_refills[wp]:
  "\<lbrace>valid_refills scptr budget\<rbrace>
      set_tcb_obj_ref f ptr new \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"
  apply (wpsimp simp: set_tcb_obj_ref_def set_object_def
         wp: get_object_wp update_sched_context_valid_refills_no_budget_update get_sched_context_wp)
  apply (clarsimp simp: valid_refills_def obj_at_def sc_valid_refills_def dest!: get_tcb_SomeD)
  done

crunch valid_refills[wp]: update_sk_obj_ref, test_reschedule "valid_refills scp budget"
 (wp: update_sched_context_valid_refills_no_budget_update simp: )

lemma sched_context_donate_valid_refills[wp]:
  "\<lbrace>valid_refills scptr budget\<rbrace>
      sched_context_donate ptr callee \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"
  apply (wpsimp simp: sched_context_donate_def set_object_def get_sc_obj_ref_def
         wp: get_object_wp update_sched_context_valid_refills_no_budget_update get_sched_context_wp)
  done

lemma reply_push_valid_refills[wp]:
  "\<lbrace>valid_refills scptr budget\<rbrace>
      reply_push caller callee reply_ptr can_donate \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"
  apply (wpsimp simp: reply_push_def set_object_def partial_inv_def a_type_def no_reply_in_ts_def
         wp: get_object_wp update_sched_context_valid_refills_no_budget_update get_sched_context_wp
             hoare_drop_imp hoare_vcg_if_lift2 hoare_vcg_all_lift
         simp_del: fun_upd_apply split: kernel_object.splits)
  done

crunch valid_refills[wp]: reply_unlink_tcb "valid_refills scp budget"
 (wp: update_sched_context_valid_refills_no_budget_update gts_inv hoare_drop_imps)

locale SchedContextInv_AI =
  fixes state_ext_t :: "'state_ext::state_ext itself"
  fixes some_t :: "'t itself"
  assumes make_arch_fault_msg_valid_refills[wp]:
    "\<And>ft t. make_arch_fault_msg ft t \<lbrace>valid_refills scptr budget :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes lookup_ipc_buffer_valid_refills[wp]:
    "\<And>t b scptr budget.
      \<lbrace>valid_refills scptr budget :: 'state_ext state \<Rightarrow> bool\<rbrace>
        lookup_ipc_buffer b t
      \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"

lemma as_user_valid_refills[wp]:
  "\<lbrace>valid_refills scptr budget\<rbrace>
      as_user t f \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"
  apply (clarsimp simp: as_user_def split_def)
  apply (wpsimp wp: select_f_wp set_object_wp)
  by (clarsimp dest!: get_tcb_SomeD simp: valid_refills_def obj_at_def)

crunch valid_refills[wp]: set_message_info "valid_refills scp budget"
crunch valid_refills[wp]: set_cdt,set_original,set_extra_badge "valid_refills scp budget"
  (simp: valid_refills_def wp_del: set_original_wp)


lemma set_cap_valid_refills [wp]:
 "\<lbrace>valid_refills scp budget\<rbrace> set_cap c p \<lbrace>\<lambda>rv. valid_refills scp budget\<rbrace>"
  apply (simp add: set_cap_def split_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp)
  apply (fastforce simp: valid_refills_def obj_at_def)
  done

crunch valid_refills[wp]: update_cdt,set_untyped_cap_as_full "valid_refills scp budget"
  (wp: hoare_drop_imps crunch_wps simp: crunch_simps ignore: set_original)

crunch valid_refills[wp]: cap_insert "valid_refills scp budget"
  (wp: hoare_drop_imps)

lemma dmo_storeWord_valid_refills[wp]:
  "\<lbrace>valid_refills scp budget\<rbrace> do_machine_op (storeWord x y) \<lbrace>\<lambda>_. valid_refills scp budget\<rbrace>"
  by (simp add: do_machine_op_def valid_refills_def |  wp | wpc)+

lemma sched_context_update_consumed_valid_refills [wp]:
 "\<lbrace>valid_refills scp budget\<rbrace> sched_context_update_consumed scptr \<lbrace>\<lambda>rv. valid_refills scp budget\<rbrace>"
  apply (simp add: sched_context_update_consumed_def)
  apply (wpsimp simp: set_object_def
      wp: get_object_wp update_sched_context_valid_refills_no_budget_update_const get_sched_context_wp)
  apply (clarsimp simp: valid_refills_def obj_at_def sc_valid_refills_def)
  done

lemma set_mrs_valid_refills [wp]:
 "\<lbrace>valid_refills scp budget\<rbrace> set_mrs thread buf msgs \<lbrace>\<lambda>rv. valid_refills scp budget\<rbrace>"
  apply (simp add: set_mrs_def split_def)
  apply (wpsimp simp: set_object_def zipWithM_x_mapM_x wp: get_object_wp mapM_x_wp' split_del: if_split)
  apply (clarsimp simp: valid_refills_def obj_at_def get_tcb_SomeD)
  done

crunch valid_refills[wp]: copy_mrs "valid_refills scp budget"
  (wp: mapM_wp')

lemma transfer_caps_loop_valid_refills[wp]:
  "\<And>ep buffer n caps slots mi.
    \<lbrace>valid_refills scp budget\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. valid_refills scp budget\<rbrace>"
  by (wp transfer_caps_loop_pres cap_insert_valid_refills)


context SchedContextInv_AI begin

crunch valid_refills[wp]: do_ipc_transfer "valid_refills scp budget :: 'state_ext state \<Rightarrow> bool"

end

locale SchedContextInv_AI2 = SchedContextInv_AI state_ext_t some_t
  for state_ext_t :: "'state_ext::state_ext itself" and some_t :: "'t itself"+
  assumes send_ipc_valid_refills[wp]:
  "\<lbrace>valid_refills scptr budget\<rbrace> send_ipc block call badge can_grant can_donate thread epptr
      \<lbrace>\<lambda>_. valid_refills scptr budget :: 'state_ext state \<Rightarrow> bool\<rbrace>"
begin

crunch valid_refills[wp]: handle_timeout "valid_refills scp budget :: 'state_ext state \<Rightarrow> bool"

lemma end_timeslice_valid_refills[wp]:
  "end_timeslice canTimeout \<lbrace>valid_refills scptr budget :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  supply if_weak_cong[cong del]
  apply (clarsimp simp: end_timeslice_def)
  by (wpsimp simp: end_timeslice_def wp: hoare_drop_imps split_del: if_split)

lemma update_sched_context_valid_refills_sc_consumed_update:
  "\<lbrace>valid_refills scptr budget\<rbrace>
     update_sched_context p (\<lambda>sc. sc\<lparr>sc_consumed := sc_consumed sc + consumed\<rparr>)
      \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"
  by (wpsimp simp: update_sched_context_def obj_at_def
          wp: set_object_wp get_object_wp)

lemma charge_budget_valid_refills[wp]:
  "\<lbrace>valid_refills scptr budget :: 'state_ext state \<Rightarrow> bool\<rbrace>
     charge_budget capacity consumed canTimeout \<lbrace>\<lambda>_ s. valid_refills scptr budget s\<rbrace>"
  apply (clarsimp simp: charge_budget_def is_round_robin_def)
  apply (wpsimp wp: get_object_wp update_sched_context_valid_refills_sc_consumed_update assert_inv
      simp: Let_def is_round_robin_def refill_full_def)
       apply (wpsimp simp: set_refills_def update_sched_context_def set_object_def wp: get_object_wp)
      apply clarsimp
      apply (wpsimp wp: get_refills_wp refill_budget_check_valid_refills get_sched_context_wp)+
  apply (clarsimp simp: obj_at_def MIN_REFILLS_def sc_at_period_def valid_refills_def)
  apply (case_tac "sc_refills sc"; simp)
  apply (case_tac list; simp)
  done

lemma check_budget_valid_refills[wp]:
  "\<lbrace>valid_refills scptr budget :: 'state_ext state \<Rightarrow> bool\<rbrace> check_budget \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"
  apply (clarsimp simp: check_budget_def)
  by (wpsimp simp: is_round_robin_def refill_full_def refill_size_def refill_capacity_def
    wp: get_sched_context_wp get_refills_wp charge_budget_valid_refills)

lemma
  "\<lbrace>valid_refills scptr budget and
   valid_sched_control_inv (InvokeSchedControlConfigure scptr budget period mrefills badge)\<rbrace>
   invoke_sched_control_configure (InvokeSchedControlConfigure scptr budget period mrefills badge)
   \<lbrace>\<lambda>_. valid_refills scptr budget :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  apply (clarsimp simp: invoke_sched_control_configure_def)
  apply (rule conjI;
         wpsimp simp: invoke_sched_control_configure_def split_def
             wp: hoare_vcg_if_lift2 get_sched_context_wp commit_time_valid_refills hoare_gets_sp
                 hoare_drop_imp update_sched_context_valid_refills_no_budget_update hoare_when_wp
                 hoare_vcg_all_lift
            cong: if_cong conj_cong split_del: if_split)
  by (clarsimp simp: valid_refills_def sc_valid_refills_def obj_at_def MIN_REFILLS_def refills_sum_def)+

end

text {* invocation related lemmas *}

lemma sched_context_bind_tcb_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace>
      sched_context_bind_tcb sc tcb \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by (wpsimp simp: sched_context_bind_tcb_def)

lemma sched_context_yield_to_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace>
      sched_context_yield_to sc_ptr args \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by (wpsimp simp: sched_context_yield_to_def wp: hoare_drop_imp hoare_vcg_if_lift2)

lemma invoke_sched_context_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace>
     invoke_sched_context i
   \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by (cases i;
      wpsimp wp: dxo_wp_weak mapM_x_wp get_sched_context_wp
       simp: invoke_sched_context_def sched_context_bind_ntfn_def)

context notes if_weak_cong[cong del] begin
crunch typ_at[wp]: charge_budget "\<lambda>s. P (typ_at T p s)"
  (wp: hoare_drop_imp maybeM_inv simp: Let_def)
end

lemma check_budget_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> check_budget \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by (wpsimp simp: check_budget_def split_del: if_split
            wp: hoare_vcg_if_lift2 hoare_drop_imp)

context notes if_weak_cong[cong del] begin
crunch typ_at[wp]: commit_time "\<lambda>s. P (typ_at T p s)"
  (wp: hoare_drop_imp simp: Let_def)
end

crunch typ_at[wp]: tcb_release_remove "\<lambda>s. P (typ_at T p s)"
  (wp: hoare_drop_imp simp: Let_def)

lemma invoke_sched_control_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace>
     invoke_sched_control_configure i
   \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by (cases i; wpsimp simp: invoke_sched_control_configure_def
                  split_del: if_split wp: hoare_vcg_if_lift2 hoare_drop_imp)

lemma invoke_sched_context_tcb[wp]:
  "\<lbrace>tcb_at tptr\<rbrace> invoke_sched_context i \<lbrace>\<lambda>rv. tcb_at tptr\<rbrace>"
  by (simp add: tcb_at_typ invoke_sched_context_typ_at [where P=id, simplified])

lemma invoke_sched_control_tcb[wp]:
  "\<lbrace>tcb_at tptr\<rbrace> invoke_sched_control_configure i \<lbrace>\<lambda>rv. tcb_at tptr\<rbrace>"
  by (simp add: tcb_at_typ invoke_sched_control_typ_at [where P=id, simplified])

lemma invoke_sched_context_invs[wp]:
  "\<lbrace>invs and valid_sched_context_inv i and ct_active\<rbrace> invoke_sched_context i \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (cases i;
         wpsimp simp: invoke_sched_context_def set_consumed_def valid_sched_context_inv_def
                  wp: sched_context_yield_to_invs)
    apply (clarsimp simp: obj_at_def sc_tcb_sc_at_def sc_ntfn_sc_at_def is_sc_obj_def is_tcb
                          valid_cap_def idle_no_ex_cap ct_in_state_def
                   split: cap.split_asm)+
   apply (frule invs_valid_global_refs,
          fastforce simp: invs_valid_objs idle_sc_no_ex_cap idle_no_ex_cap)
  apply (fastforce simp: invs_def valid_state_def valid_pspace_def live_def ct_in_state_def
                         obj_at_def pred_tcb_at_def valid_idle_def
                   dest: if_live_then_nonz_capD2)
  done

lemma update_sc_badge_valid_replies:
  "\<lbrace>valid_replies_pred P and (\<lambda>s. (\<exists>n. ko_at (SchedContext sc n) p s))\<rbrace>
   update_sched_context p (\<lambda>_. sc\<lparr>sc_badge := i \<rparr>)
   \<lbrace>\<lambda>rv. valid_replies_pred P\<rbrace>"
  by (wpsimp wp: update_sched_context_wp,
      fastforce dest: ko_at_obj_congD)

lemma update_sc_refills_period_refill_max_valid_replies:
  "\<lbrace>valid_replies_pred P and (\<lambda>s. (\<exists>n. ko_at (SchedContext sc n) p s))\<rbrace>
   update_sched_context p (\<lambda>_. sc\<lparr>sc_period := period, sc_refill_max := m, sc_refills := r\<rparr>)
   \<lbrace>\<lambda>rv. valid_replies_pred P\<rbrace>"
  by (wpsimp wp: update_sched_context_wp,
      fastforce dest: ko_at_obj_congD)

lemma update_sc_refills_valid_replies[wp]:
  "\<lbrace>valid_replies_pred P and (\<lambda>s. (\<exists>n. ko_at (SchedContext sc n) p s))\<rbrace>
   update_sched_context p (\<lambda>_. sc\<lparr>sc_refills := r\<rparr>)
   \<lbrace>\<lambda>rv. valid_replies_pred P\<rbrace>"
  by (wpsimp wp: update_sched_context_wp,
      fastforce dest: ko_at_obj_congD)

lemma update_sc_badge_cur_sc_tcb:
  "\<lbrace>\<lambda>s. cur_sc_tcb s \<and> (\<exists>n. ko_at (SchedContext sc n) p s)\<rbrace>
   update_sched_context p (\<lambda>_. sc\<lparr>sc_badge := i\<rparr>)
   \<lbrace>\<lambda>rv. cur_sc_tcb\<rbrace>"
  by (wpsimp simp: update_sched_context_def set_object_def get_object_def cur_sc_tcb_def
                   sc_tcb_sc_at_def obj_at_def)

lemma update_sc_badge_invs:
  "\<lbrace>\<lambda>s. invs s \<and> p \<noteq> idle_sc_ptr \<and> (\<exists>n. ko_at (SchedContext sc n) p s)\<rbrace>
   update_sched_context p (\<lambda>_. sc\<lparr>sc_badge := i\<rparr>)
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                  wp: update_sched_context_valid_idle update_sc_badge_cur_sc_tcb
                      update_sc_badge_valid_replies)
  apply (auto simp: state_refs_of_def obj_at_def valid_obj_def live_def
             elim!: delta_sym_refs if_live_then_nonz_capD
             split: if_splits)
  done

(* FIXME copied from Syscall_AI *)
lemma thread_set_cap_to:
  "(\<And>tcb. \<forall>(getF, v)\<in>ran tcb_cap_cases. getF (f tcb) = getF tcb)
  \<Longrightarrow> \<lbrace>ex_nonz_cap_to p\<rbrace> thread_set f tptr \<lbrace>\<lambda>_. ex_nonz_cap_to p\<rbrace>"
  apply (clarsimp simp add: ex_nonz_cap_to_def)
  apply (wpsimp wp: hoare_ex_wp thread_set_cte_wp_at_trivial)
  apply auto
  done

lemma thread_set_timeout_fault_valid_mdb[wp]:
  "\<lbrace>valid_mdb\<rbrace> thread_set (tcb_fault_update (\<lambda>_. Some (Timeout badge))) t \<lbrace>\<lambda>rv. valid_mdb\<rbrace>"
  apply (simp add: thread_set_def set_object_def)
  apply (rule valid_mdb_lift)
    apply wp
    apply clarsimp
    apply (subst caps_of_state_after_update)
     apply (clarsimp simp: ran_tcb_cap_cases)
    apply simp
   apply (wp | simp)+
  done

lemma thread_set_timeout_fault_valid_irq_handlers[wp]:
  "\<lbrace>valid_irq_handlers\<rbrace> thread_set (tcb_fault_update (\<lambda>_. Some (Timeout badge))) t \<lbrace>\<lambda>rv. valid_irq_handlers\<rbrace>"
  apply (simp add: thread_set_def set_object_def)
  apply (rule valid_irq_handlers_lift)
    apply wp
    apply clarsimp
    apply (subst caps_of_state_after_update)
     apply (clarsimp simp: ran_tcb_cap_cases)
    apply simp
   apply (wp | simp)+
  done

lemma send_fault_ipc_invs':
  assumes set_endpoint_Q[wp]: "\<And>a b.\<lbrace>Q\<rbrace> set_endpoint a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes sts_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> set_thread_state a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes ext_Q[wp]: "\<And>a. \<lbrace>Q and valid_objs\<rbrace> possible_switch_to a \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes do_ipc_transfer_Q[wp]: "\<And>a b c d e. \<lbrace>Q and valid_objs and valid_mdb\<rbrace>
                                               do_ipc_transfer a b c d e \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes thread_set_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> thread_set a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes reply_push_Q[wp]: "\<And>a b c d. \<lbrace>Q\<rbrace> reply_push a b c d \<lbrace>\<lambda>_. Q\<rbrace>"
  assumes sched_context_donate_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> sched_context_donate a b \<lbrace>\<lambda>_. Q\<rbrace>"
  assumes reply_unlink_tcb_Q[wp]: "\<And>t r. \<lbrace>Q\<rbrace> reply_unlink_tcb t r \<lbrace>\<lambda>_. Q\<rbrace>"
  notes si_invs''[wp] = si_invs'_fault[where Q=Q]
  shows
  "\<lbrace>invs and Q
    and st_tcb_at active tptr and ex_nonz_cap_to tptr and K (valid_fault fault)
    and (\<lambda>s. \<exists>n. caps_of_state s (tptr, tcb_cnode_index n) = Some cap)
    and K (is_ep_cap cap) and (\<lambda>s. canDonate \<longrightarrow> bound_sc_tcb_at bound tptr s)\<rbrace>
   send_fault_ipc tptr cap fault canDonate
   \<lbrace>\<lambda>rv. invs and Q\<rbrace>"
  apply (cases "valid_fault fault"; simp)
  apply (clarsimp simp: send_fault_ipc_def)
  apply (wpsimp wp: test thread_set_invs_but_fault_tcbs
                    thread_set_no_change_tcb_state ex_nonz_cap_to_pres
                    thread_set_cte_wp_at_trivial
                    thread_set_no_change_tcb_sched_context
                    hoare_vcg_imp_lift gbn_wp
         | clarsimp simp: tcb_cap_cases_def
         | erule disjE)+
  apply (clarsimp simp: pred_tcb_at_def obj_at_def get_tcb_ko_at)
  apply (subst (asm) caps_of_state_tcb_index_trans, erule get_tcb_rev)
  apply (simp (no_asm) add: ex_nonz_cap_to_def cte_wp_at_cases2)
  apply (rule_tac x = tptr in exI)
  apply (rule_tac x = "tcb_cnode_index n" in exI)
  apply (clarsimp simp: obj_at_def tcb_cnode_map_def)
  done

lemmas send_fault_ipc_invs[wp] = send_fault_ipc_invs'[where Q=\<top>,simplified hoare_post_taut, OF TrueI TrueI TrueI TrueI TrueI,simplified]

lemma handle_timeout_Timeout_invs:
  "\<lbrace>invs and st_tcb_at active tptr\<rbrace>
     handle_timeout tptr (Timeout badge)  \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (clarsimp simp: handle_timeout_def)
  apply (wpsimp wp: thread_set_invs_trivial send_fault_ipc_invs
              simp: handle_timeout_def ran_tcb_cap_cases
                    thread_set_def valid_fault_def)
  apply (case_tac "tcb_timeout_handler y"; clarsimp)
  apply (rule conjI)
   apply (clarsimp simp: pred_tcb_at_def obj_at_def dest!: get_tcb_SomeD)
   apply (drule invs_iflive)
   apply (drule (1) if_live_then_nonz_capD2)
    apply (fastforce simp: live_def split: )
   apply clarsimp
  apply (rule_tac x=4 in exI)
  apply (auto simp: tcb_cnode_map_def caps_of_state_tcb_index_trans)
  done

lemma end_timeslice_invs:
  "\<lbrace>\<lambda>s. invs s \<and> ct_active s\<rbrace>
      end_timeslice t \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wpsimp simp: end_timeslice_def ct_in_state_def get_tcb_queue_def
          wp: handle_timeout_Timeout_invs hoare_drop_imp hoare_vcg_if_lift2)
  done

lemma invs_valid_refills:
  "\<lbrakk> invs s; ko_at (SchedContext sc n) scptr s\<rbrakk> \<Longrightarrow> Suc 0 \<le> length (sc_refills sc)"
  by (clarsimp dest!: invs_valid_objs elim!: obj_at_valid_objsE simp: valid_obj_def valid_sched_context_def)

lemma sched_context_nonref_update_invs[wp]:
  "\<lbrace>\<lambda>s. invs s \<and> scp \<noteq> idle_sc_ptr \<and> (\<exists>n. ko_at (SchedContext sc n) scp s)\<rbrace>
   update_sched_context scp (\<lambda>_. sc\<lparr> sc_period := period, sc_refill_max := m, sc_refills := r0#rs\<rparr>)
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def simp_del: refs_of_defs
                  wp: valid_ioports_lift update_sc_refills_period_refill_max_valid_replies
                      update_sched_context_valid_idle set_sc_others_cur_sc_tcb)
  apply (auto simp: state_refs_of_def obj_at_def valid_obj_def valid_sched_context_def live_def
                    live_sc_def
             elim!: delta_sym_refs if_live_then_nonz_capD
             split: if_splits)
  done

(* move to SchedContext_AI *)
lemma set_sc_refills_cur_sc_tcb[wp]:
  "\<lbrace>\<lambda>s. cur_sc_tcb s \<and> (\<exists>n. ko_at (SchedContext sc n) p s)\<rbrace>
   update_sched_context p (\<lambda>_. sc\<lparr>sc_refills := rs\<rparr>) \<lbrace>\<lambda>rv. cur_sc_tcb\<rbrace>"
  by (wpsimp simp: update_sched_context_def cur_sc_tcb_def sc_tcb_sc_at_def obj_at_def
               wp: set_object_wp get_object_wp)

lemma update_sc_refills_cur_sc_tcb[wp]:
  "\<lbrace>cur_sc_tcb\<rbrace> update_sched_context scp (sc_refills_update f) \<lbrace>\<lambda>rv. cur_sc_tcb\<rbrace>"
  by (wpsimp wp: update_sched_context_cur_sc_tcb_no_change)

lemma set_sc_refills_valid_idle:
  "\<lbrace>valid_idle and (\<lambda>s. (\<exists>n. ko_at (SchedContext sc n) p s))\<rbrace>
   update_sched_context p (\<lambda>_. sc\<lparr>sc_refills := r\<rparr>)
   \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  by (wpsimp simp: update_sched_context_def set_object_def get_object_def valid_idle_def
                   pred_tcb_at_def obj_at_def)

lemma sched_context_refill_update_invs:
  "\<lbrace>\<lambda>s. invs s \<and> (\<exists>n. ko_at (SchedContext sc n) scp s)\<rbrace>
   update_sched_context scp (\<lambda>_. sc\<lparr>sc_refills := r0#rs\<rparr>)
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def wp: set_sc_refills_valid_idle)
  apply (auto simp: state_refs_of_def obj_at_def valid_obj_def valid_sched_context_def live_def
                    live_sc_def
             elim!: delta_sym_refs if_live_then_nonz_capD
             split: if_splits)
  done

lemma update_sched_context_sc_consumed_update_invs:
  "\<lbrace>invs\<rbrace> update_sched_context scp (sc_consumed_update f) \<lbrace>\<lambda>_. invs\<rbrace>"
  by (wpsimp simp: invs_def valid_state_def valid_pspace_def simp_del: refs_of_defs
               wp: update_sched_context_valid_objs_same
                   update_sched_context_refs_of_same valid_irq_node_typ)

lemma update_sched_context_sc_refills_update_invs:
  "\<lbrace>\<lambda>s. invs s \<and> (\<forall>ls. 1 \<le> length ls \<longrightarrow> 1 \<le> length (f ls))\<rbrace>
   update_sched_context scp (sc_refills_update f)
   \<lbrace>\<lambda>_. invs\<rbrace>"
  by (wpsimp simp: invs_def valid_state_def valid_pspace_def valid_sched_context_def
               wp: update_sched_context_valid_objs_same valid_irq_node_typ
                   update_sched_context_refs_of_same)

lemma sc_consumed_add_valid_replies:
  "\<lbrace> valid_replies \<rbrace>
   update_sched_context scp (\<lambda>sc. sc\<lparr>sc_consumed := sc_consumed sc + consumed\<rparr>)
   \<lbrace> \<lambda>_. valid_replies \<rbrace>"
  by (wpsimp wp: update_sched_context_wp)

lemma sc_consumed_add_invs:
  "\<lbrace>\<lambda>s. invs s\<rbrace>
   update_sched_context scp (\<lambda>sc. sc\<lparr>sc_consumed := sc_consumed sc + consumed\<rparr>)
   \<lbrace>\<lambda>_. invs\<rbrace>"
  by (wpsimp simp: invs_def valid_state_def valid_pspace_def sc_consumed_update_eq[symmetric]
               wp: update_sched_context_valid_objs_same valid_irq_node_typ
                   update_sched_context_iflive_implies update_sched_context_refs_of_same)

lemma refill_update_invs:
  "\<lbrace>\<lambda>s. invs s \<and> sc_ptr \<noteq> idle_sc_ptr\<rbrace>
   refill_update sc_ptr new_period new_budget new_max_refills \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (wpsimp simp: refill_update_def)

lemma refill_budget_check_invs:
  "\<lbrace>\<lambda>s. invs s\<rbrace> refill_budget_check usage capacity \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (clarsimp simp: refill_budget_check_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (wpsimp simp: refill_budget_check_def refill_full_def refill_size_def split_def
                  wp: get_sched_context_wp static_imp_wp hoare_drop_imp
                      hoare_vcg_all_lift hoare_vcg_if_lift2
                      update_sched_context_sc_refills_update_invs
           split_del: if_split)
  apply (frule (1) invs_valid_refills)
  apply (clarsimp simp: min_budget_merge_length[THEN conjunct1, simplified])
  apply (intro conjI impI)
     apply (clarsimp simp: Let_def refills_budget_check_pos split: if_splits)+
  done

crunch ct_active[wp]: refill_full ct_active

lemma refill_split_check_ex_nonz_cap_to_ct[wp]:
  "\<lbrace>\<lambda>s. ex_nonz_cap_to (cur_thread s) s\<rbrace> refill_split_check usage
   \<lbrace>\<lambda>rv s. ex_nonz_cap_to (cur_thread s) s\<rbrace>"
  supply if_weak_cong[cong del]
  by (wpsimp simp: refill_split_check_def set_refills_def Let_def
               wp: get_sched_context_wp get_refills_wp hoare_drop_imp)

lemma refill_budget_check_ex_nonz_cap_to_ct[wp]:
  "\<lbrace>\<lambda>s. ex_nonz_cap_to (cur_thread s) s\<rbrace> refill_budget_check usage capacity
   \<lbrace>\<lambda>rv s. ex_nonz_cap_to (cur_thread s) s\<rbrace>"
  by (wpsimp simp: refill_budget_check_def set_refills_def is_round_robin_def refill_full_def
               wp: get_sched_context_wp get_refills_wp hoare_drop_imp hoare_vcg_if_lift2
        split_del: if_split)

lemma refill_budget_check_active[wp]:
  "\<lbrace>ct_active\<rbrace> refill_budget_check consumed capacity \<lbrace> \<lambda>_ . ct_active\<rbrace>"
  by (wpsimp simp: refill_budget_check_def set_refills_def
               wp: hoare_drop_imp get_sched_context_wp split_del: if_split)

lemma update_sched_context_bound_sc:
  "\<lbrace>\<lambda>s. bound_sc_tcb_at P (cur_thread s) s\<rbrace>
   update_sched_context scp f
   \<lbrace>\<lambda>rv s. bound_sc_tcb_at P (cur_thread s) s\<rbrace>"
  by (wpsimp simp: update_sched_context_def set_object_def get_object_def pred_tcb_at_def
                   obj_at_def)

lemma refill_full_bound_sc:
  "\<lbrace>\<lambda>s. bound_sc_tcb_at P (cur_thread s) s\<rbrace>
   refill_full p
   \<lbrace>\<lambda>rv s. bound_sc_tcb_at P (cur_thread s) s\<rbrace>"
  by (wpsimp simp: refill_full_def)

lemma refill_split_check_bound_sc:
  "\<lbrace>\<lambda>s. bound_sc_tcb_at P (cur_thread s) s\<rbrace>
   refill_split_check usage
   \<lbrace>\<lambda>rv s. bound_sc_tcb_at P (cur_thread s) s\<rbrace>"
  supply if_weak_cong[cong del]
  by (wpsimp simp: refill_split_check_def set_refills_def Let_def get_sched_context_def
                   get_object_def
               wp: update_sched_context_bound_sc)

lemma set_refills_bound_sc:
  "\<lbrace>\<lambda>s. bound_sc_tcb_at P (cur_thread s) s\<rbrace>
   set_refills sc_ptr refills
   \<lbrace>\<lambda>rv s. bound_sc_tcb_at P (cur_thread s) s\<rbrace>"
  by (wpsimp simp: set_refills_def wp: update_sched_context_bound_sc)

lemma refill_budget_check_bound_sc:
  "\<lbrace>\<lambda>s. bound_sc_tcb_at P (cur_thread s) s\<rbrace>
   refill_budget_check usage capacity
   \<lbrace>\<lambda>rv s. bound_sc_tcb_at P (cur_thread s) s\<rbrace>"
  supply if_split[split del]
  by (wpsimp simp: refill_budget_check_def
               wp: update_sched_context_bound_sc refill_full_bound_sc
                   refill_split_check_bound_sc set_refills_bound_sc)

lemma charge_budget_invs:
  "\<lbrace>invs\<rbrace>
   charge_budget capacity consumed canTimeout
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  supply if_split [split del]
  unfolding charge_budget_def is_round_robin_def
  apply clarsimp
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (wpsimp wp: end_timeslice_invs assert_inv hoare_vcg_if_lift2 gts_wp is_schedulable_wp)
    apply (rule_tac Q="\<lambda>_. invs" in hoare_strengthen_post[rotated])
     apply (clarsimp simp: ct_in_state_def runnable_eq pred_tcb_at_def obj_at_def is_schedulable_opt_def
                    split: option.splits)
     apply (subgoal_tac "cur_tcb s")
      apply (clarsimp simp: get_tcb_def cur_tcb_def tcb_at_def is_tcb split: option.splits kernel_object.splits)
     apply (wpsimp wp: end_timeslice_invs assert_inv hoare_vcg_if_lift2 gts_wp
                       hoare_vcg_all_lift  sc_consumed_add_invs refill_budget_check_invs
                 simp: Let_def)+
  done

lemma check_budget_invs[wp]:
  "\<lbrace>\<lambda>s. invs s\<rbrace> check_budget \<lbrace>\<lambda>rv. invs \<rbrace>"
  by (wpsimp simp: check_budget_def refill_full_def refill_size_def
               wp: get_refills_inv hoare_drop_imp get_sched_context_wp charge_budget_invs)

lemma tcb_sched_action_bound_sc[wp]:
  "\<lbrace>\<lambda>s. bound_sc_tcb_at bound (cur_thread s) s\<rbrace>
   tcb_sched_action action thread
   \<lbrace>\<lambda>rv s. bound_sc_tcb_at bound (cur_thread s) s\<rbrace>"
  by (wpsimp simp: tcb_sched_action_def set_tcb_queue_def get_tcb_queue_def
               wp: hoare_drop_imp hoare_vcg_all_lift)

lemma tcb_release_remove_bound_sc:
  "\<lbrace>\<lambda>s. bound_sc_tcb_at bound (cur_thread s) s\<rbrace>
   tcb_release_remove tcb_ptr
   \<lbrace>\<lambda>rv s. bound_sc_tcb_at bound (cur_thread s) s\<rbrace>"
  by (wpsimp simp: tcb_release_remove_def)

lemma update_sc_badge_cur_sc_tcb':
  "\<lbrace>cur_sc_tcb\<rbrace> update_sched_context p (sc_badge_update (\<lambda>_. badge)) \<lbrace>\<lambda>_. cur_sc_tcb\<rbrace>"
  by (wpsimp simp: update_sched_context_def set_object_def get_object_def
                   cur_sc_tcb_def sc_tcb_sc_at_def obj_at_def)

lemma update_sc_badge_invs':
  "\<lbrace>invs and K (p \<noteq> idle_sc_ptr)\<rbrace>
      update_sched_context p (sc_badge_update (\<lambda>_. badge)) \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def obj_at_def
                  wp: update_sched_context_valid_objs_same valid_irq_node_typ
                      update_sched_context_iflive_implies
                      update_sched_context_refs_of_same
                      update_sc_but_not_sc_replies_valid_replies'
                      update_sched_context_valid_idle
                      update_sc_badge_cur_sc_tcb'
            simp_del: fun_upd_apply)
  done

lemma invoke_sched_control_configure_invs[wp]:
  "\<lbrace>\<lambda>s. invs s \<and> valid_sched_control_inv i s \<and> bound_sc_tcb_at bound (cur_thread s) s\<rbrace>
   invoke_sched_control_configure i
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (cases i)
  apply (rename_tac sc_ptr budget period mrefills badge)
  apply (clarsimp simp: invoke_sched_control_configure_def split_def
             split del: if_split)
  apply (wpsimp simp: get_sched_context_def get_object_def obj_at_def
                  wp: refill_update_invs hoare_drop_imp commit_time_invs check_budget_invs
                      hoare_vcg_if_lift2 tcb_sched_action_bound_sc tcb_release_remove_bound_sc
                      update_sc_badge_invs')
  apply (auto simp: invs_def valid_state_def valid_pspace_def idle_sc_no_ex_cap)
  done

text {* set_thread_state and schedcontext/schedcontrol invocations *}

crunches set_thread_state_act
  for st_tcb_at_tc[wp]: "\<lambda>s. st_tcb_at P (cur_thread s) s"
  and bound_yt_tcb_at_ct[wp]: "\<lambda>s. bound_yt_tcb_at P (cur_thread s) s"
  and sc_tcb_sc_at_ct[wp]: "\<lambda>s. sc_tcb_sc_at (P (cur_thread s)) t s"
  and release_queue[wp]: "\<lambda>s. P (release_queue s)"

context begin

private method m =
  (((wpsimp wp: valid_cap_typ set_object_wp gets_the_inv simp: set_thread_state_def
     | clarsimp simp: sc_ntfn_sc_at_def sc_tcb_sc_at_def sc_yf_sc_at_def
               dest!: get_tcb_SomeD split: cap.split
     | fastforce simp: valid_cap_def sc_ntfn_sc_at_def obj_at_def ran_tcb_cap_cases
                       fun_upd_def get_tcb_def is_tcb sc_tcb_sc_at_def pred_tcb_at_def
                 intro!: ex_cap_to_after_update
                 split: cap.split_asm option.splits kernel_object.split_asm))+)[1]

lemma sts_valid_sched_context_inv:
  "\<lbrace>(\<lambda>s. t \<noteq> cur_thread s) and valid_sched_context_inv sci\<rbrace>
      set_thread_state t st \<lbrace>\<lambda>rv. valid_sched_context_inv sci\<rbrace>"
  apply (cases sci; clarsimp)
      apply wpsimp
     apply (rename_tac cap, case_tac cap; simp; m)
    apply (rename_tac cap, case_tac cap; simp; m)
   apply (rename_tac cap, case_tac cap; simp; m)
  apply m
  done

end

lemma sts_valid_sched_control_inv[wp]:
  "\<lbrace>valid_sched_control_inv sci\<rbrace> set_thread_state t st \<lbrace>\<lambda>rv. valid_sched_control_inv sci\<rbrace>"
  by (cases sci; wpsimp wp: sts_obj_at_impossible)

lemma decode_sched_context_inv_inv:
  "\<lbrace>P\<rbrace> decode_sched_context_invocation label sc_ptr excaps args \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (rule hoare_pre)
   apply (simp add: decode_sched_context_invocation_def whenE_def split del: if_split
          | wp_once hoare_drop_imp get_sk_obj_ref_inv get_sc_obj_ref_inv | wpcw)+
  done

lemma decode_sched_control_inv_inv:
  "\<lbrace>P\<rbrace> decode_sched_control_invocation label args excaps \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (rule hoare_pre)
   apply (simp add: decode_sched_control_invocation_def whenE_def unlessE_def split del: if_split
          | wp_once hoare_drop_imp get_sk_obj_ref_inv assertE_wp | wpcw)+
  done

lemma decode_sched_context_inv_wf:
  "\<lbrace>invs and sc_at sc_ptr and ex_nonz_cap_to sc_ptr and
     (\<lambda>s. \<forall>x\<in>set excaps. s \<turnstile> x) and
     (\<lambda>s. \<forall>x\<in>set excaps. \<forall>r\<in>zobj_refs x. ex_nonz_cap_to r s)\<rbrace>
     decode_sched_context_invocation label sc_ptr excaps args
   \<lbrace>valid_sched_context_inv\<rbrace>, -"
  apply (wpsimp simp: decode_sched_context_invocation_def whenE_def
                      get_sk_obj_ref_def get_tcb_obj_ref_def get_sc_obj_ref_def
           split_del: if_split
                  wp: hoare_vcg_if_splitE get_simple_ko_wp thread_get_wp' get_sched_context_wp)
  apply (intro conjI; intro impI allI)
    apply (erule ballE[where x="hd excaps"])
     prefer 2
     apply (drule hd_in_set, simp)
    apply (rule conjI; intro impI allI)
     apply simp
     apply (erule ballE[where x="hd excaps"])
      prefer 2
      apply (drule hd_in_set, simp)
     apply (erule_tac x=x in ballE)
      apply (clarsimp simp add: obj_at_def sc_ntfn_sc_at_def)
     apply clarsimp
    apply (erule ballE[where x="hd excaps"])
     prefer 2
     apply (drule hd_in_set, simp)
    apply (erule_tac x=x in ballE)
     prefer 2
     apply (drule hd_in_set, simp)
    apply (clarsimp simp: obj_at_def pred_tcb_at_def sc_tcb_sc_at_def)
   apply (frule invs_valid_global_refs, drule invs_valid_objs, clarsimp dest!: idle_no_ex_cap)
   apply (erule ballE[where x="hd excaps"])
    prefer 2
    apply (drule hd_in_set, simp)
   apply (rule conjI; intro impI allI)
    apply simp
    apply (erule ballE[where x="hd excaps"])
     prefer 2
     apply (drule hd_in_set, simp)
    apply (erule_tac x=x in ballE)
     apply (clarsimp simp: obj_at_def sc_ntfn_sc_at_def is_sc_obj_def)
    apply clarsimp
   apply (erule ballE[where x="hd excaps"])
    prefer 2
    apply (drule hd_in_set, simp)
   apply (erule_tac x=x in ballE)
    prefer 2
    apply (drule hd_in_set, simp)
   apply (clarsimp simp: obj_at_def pred_tcb_at_def sc_tcb_sc_at_def)
  apply (clarsimp simp: sc_tcb_sc_at_def obj_at_def is_sc_obj_def is_tcb pred_tcb_at_def
                        sc_yf_sc_at_def)
  done

lemma decode_sched_control_inv_wf:
  "\<lbrace>invs and
     (\<lambda>s. \<forall>x\<in>set excaps. s \<turnstile> x) and
     (\<lambda>s. \<forall>x\<in>set excaps. \<forall>r\<in>zobj_refs x. ex_nonz_cap_to r s)\<rbrace>
   decode_sched_control_invocation label args excaps
   \<lbrace>valid_sched_control_inv\<rbrace>, -"
  apply (wpsimp simp: decode_sched_control_invocation_def whenE_def unlessE_def assertE_def
           split_del: if_split)
  apply (erule ballE[where x="hd excaps"])
   prefer 2
   apply (drule hd_in_set, simp)
  apply (erule ballE[where x="hd excaps"])
   prefer 2
   apply (drule hd_in_set, simp)
  apply (clarsimp simp add: valid_cap_def obj_at_def is_sc_obj_def split: cap.split_asm)
  apply (case_tac ko; simp)
  apply (clarsimp simp: valid_refills_number_def refill_absolute_max_def MIN_REFILLS_def
                        us_to_ticks_mono[simplified mono_def] MIN_BUDGET_def
                        MIN_BUDGET_US_def ARM.kernelWCET_ticks_def)
  done

end