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
  "\<lbrace>\<comment> \<open>(\<lambda>s. kheap s tptr = Some (TCB tcb) \<and> tcb_yield_to tcb = Some scp) and\<close> (\<lambda>s. P (state_refs_of s))\<rbrace>
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

text \<open>valid invocation definitions\<close>
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
        and ex_nonz_cap_to scptr and K (MIN_REFILLS \<le> mrefills) \<comment> \<open>mrefills = MIN_REFILLS + extra_refills\<close>
        and K (budget \<le> us_to_ticks maxTimer_us \<and> budget \<ge> MIN_SC_BUDGET)
        and K (period \<le> us_to_ticks maxTimer_us \<and> budget \<ge> MIN_SC_BUDGET)
        and K (budget \<le> period))"


text \<open>refill invariant proofs\<close>  \<comment> \<open>FIXME move? Sporadic_AI?\<close>

definition valid_refill_amount :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_refill_amount scptr =
     (obj_at (\<lambda>ko. \<exists>sc n. ko= SchedContext sc n
      \<and> refills_sum (sc_refills sc) = sc_budget sc) scptr)"

definition
  no_overflow :: "refill list \<Rightarrow> bool"
where
  "no_overflow refills \<equiv>
      \<forall>n < length refills. unat (r_time (refills ! n)) + unat (r_amount (refills ! n))
                            \<le> unat (max_word :: time)"

lemma no_overflow_sublist:
  "\<lbrakk>no_overflow list; sublist new_list list\<rbrakk> \<Longrightarrow> no_overflow new_list"
  apply (simp add: sublist_def no_overflow_def)
  apply clarsimp
  apply (subgoal_tac "new_list ! n = (ps @ new_list @ ss) ! (n + length ps)")
   apply force
  by (simp add: nth_append)

lemma no_overflow_tail:
  "no_overflow (a # list) \<Longrightarrow> no_overflow list"
  by (force simp: no_overflow_def)

definition
  ordered_disjoint :: "refill list \<Rightarrow> bool"
where
  "ordered_disjoint refills \<equiv>
      \<forall>n < (length refills - Suc 0).
        unat (r_time (refills ! n)) + unat (r_amount (refills ! n))
          \<le> unat (r_time (refills ! (Suc n)))"

lemma ordered_disjoint_sublist:
  "\<lbrakk>ordered_disjoint list; sublist new_list list\<rbrakk> \<Longrightarrow> ordered_disjoint new_list"
  apply (simp add: sublist_def ordered_disjoint_def)
  apply clarsimp
  apply (subgoal_tac "new_list ! n = (ps @ new_list @ ss) ! (n + length ps)")
   apply (subgoal_tac "new_list ! Suc n = (ps @ new_list @ ss) ! Suc (n + length ps)")
    apply clarsimp
   apply (fastforce simp: nth_append)+
  done

lemma ordered_disjoint_tail:
  "ordered_disjoint (a # list) \<Longrightarrow> ordered_disjoint list"
  apply (clarsimp simp: ordered_disjoint_def)
  apply (drule_tac x="Suc n" in spec)
  by clarsimp

lemma ordered_disjoint_non_adjacent:
  "\<lbrakk>ordered_disjoint refills;
    k < length refills;
    l < length refills;
    k < l\<rbrakk>
   \<Longrightarrow> unat (r_time (refills ! k)) + unat (r_amount (refills ! k)) \<le> unat (r_time (refills ! l))"
  apply (induct refills arbitrary: k l rule: length_induct)
  apply (case_tac xs)
   apply simp
  apply (rename_tac a list)
  apply simp
  apply (drule_tac x=list in spec)
  apply clarsimp
  apply (elim impE; (clarsimp simp: no_overflow_tail ordered_disjoint_tail)?)
  apply (case_tac "k=0")
   apply simp
   apply (case_tac "l=1")
    apply (fastforce simp: ordered_disjoint_def)
   apply (rule_tac y="unat (r_time (list ! 0)) + unat (r_amount (list ! 0))" in order_trans)
    apply (rule_tac y="unat (r_time (list ! 0))" in order_trans)
    apply (fastforce simp: ordered_disjoint_def)+
  done

lemma ordered_disjoint_no_overflow_implies_sorted:
  "\<lbrakk>ordered_disjoint refills;
    no_overflow refills;
    k < length refills;
    l < length refills;
    k < l\<rbrakk>
   \<Longrightarrow> unat (r_time (refills ! k)) \<le> unat (r_time (refills ! l))"
  apply (frule ordered_disjoint_non_adjacent[where refills=refills and k=k and l=l]; assumption?)
  by linarith

definition
  window :: "refill list \<Rightarrow> ticks \<Rightarrow> bool"
where
  "window refills period \<equiv>
      unat (r_time (last refills)) + unat (r_amount (last refills))
       \<le> unat (r_time (hd refills)) + unat period"

lemma period_window_single:
  "\<lbrakk>refills = [a]\<rbrakk>
   \<Longrightarrow> window refills period = (unat (r_amount a) \<le> unat period)"
  unfolding window_def by fastforce

\<comment> \<open> FIXME: it would be nice to phrase the fourth conjunct as
            \<forall>refill \<in> set (sc_refills sc). MIN_BUDGET <= r_amount refill\<close>
definition sc_valid_refills :: "sched_context \<Rightarrow> bool"
where
  "sc_valid_refills sc =
      (refills_sum (sc_refills sc) = sc_budget sc
      \<and> ordered_disjoint (sc_refills sc)
      \<and> no_overflow (sc_refills sc)
      \<and> (\<forall>n < length (sc_refills sc). MIN_BUDGET \<le> r_amount ((sc_refills sc) ! n))
      \<and> window (sc_refills sc) (sc_period sc)
      \<and> 0 < length (sc_refills sc)
      \<and> length (sc_refills sc) \<le> sc_refill_max sc)"

definition valid_refills :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_refills scptr = obj_at (\<lambda>ko. \<exists>sc n. ko= SchedContext sc n \<and> sc_valid_refills sc) scptr"

lemma valid_refills_refills_sum:
  "valid_refills scp s \<Longrightarrow>
    obj_at (\<lambda>ko. \<exists>sc n. ko= SchedContext sc n
       \<and> refills_sum (sc_refills sc) = sc_budget sc) scp s"
  by (clarsimp simp: valid_refills_def sc_valid_refills_def obj_at_def)

lemma valid_refills_sc_refill_max:
  "valid_refills scp s \<Longrightarrow>
    obj_at (\<lambda>ko. \<exists>sc n. ko = SchedContext sc n
                        \<and> length (sc_refills sc) \<le> sc_refill_max sc) scp s"
  by (clarsimp simp: sc_valid_refills_def valid_refills_def obj_at_def)

lemma sc_valid_refills_refills_sum:
  "sc_valid_refills sc \<Longrightarrow> refills_sum (sc_refills sc) = sc_budget sc"
  by (clarsimp simp: sc_valid_refills_def)

(* FIXME maybe move? *)
lemma refills_sum_cons[simp]: "refills_sum (a#rs) =  r_amount a + refills_sum rs"
  by (clarsimp simp: refills_sum_def)

lemma refills_sum_append[simp]: "refills_sum (rs1 @ rs) =  refills_sum rs1 + refills_sum rs"
  by (clarsimp simp: refills_sum_def)

lemma refills_sum_nil[simp]: "refills_sum [] = 0" by (clarsimp simp: refills_sum_def)
(* end maybe move *)

(***** FIXME maybe move? *****)
(* unat addition *)
lemma sum_list_bounded_eq:
  "sum_list (map unat (ls :: time list)) = unat (budget :: time) \<Longrightarrow> sum_list (map unat ls) = unat (sum_list ls)"
  apply (induct ls arbitrary: budget, simp)
  apply clarsimp
  by (metis (no_types, hide_lams) le_add2 le_unat_uoi of_nat_add word_unat.Rep_inverse)

lemma sum_list_bounded_lt:
  "sum_list (map unat (ls :: time list)) < unat (budget :: time) \<Longrightarrow>sum_list (map unat ls) = unat (sum_list ls)"
  apply (induct ls arbitrary: budget, simp)
  apply clarsimp
  by (metis (mono_tags) add.commute add_lessD1 le_unat_uoi nat_less_le word_arith_nat_add)

lemma sum_list_bounded_le:
  "sum_list (map unat (ls :: time list)) \<le> unat (budget :: time) \<Longrightarrow>sum_list (map unat ls) = unat (sum_list ls)"
  apply (induct ls arbitrary: budget, simp)
  apply clarsimp
  by (metis add_leE le_unat_uoi word_arith_nat_add)

lemma "sum_list (map unat ls) = unat (sum_list ls) \<Longrightarrow> (\<forall>j::nat< length ls. \<forall>i::nat < j. unat (ls!j + ls!i) = unat (ls!j) + unat (ls!i))"
oops

(** end unat **)

(* FIXME: maybe move *)
(* FIXME: remove because unused? *)
lemma remove1_nth_rewrite:
  "(j::nat) < length ls \<Longrightarrow>
        set (remove1 (ls!j) ls)
                = set ((take j ls)
                          @ tl (drop j ls))"
  apply (subgoal_tac "remove1 (ls!j) ls = remove1 (ls!j) (take j ls @ (ls!j) # drop (j+1) ls)")
   apply (simp only: remove1_append)
   apply clarsimp
   apply (case_tac "(ls!j) \<in> set (take j ls)"; clarsimp)
proof -
  assume a1: "ls ! j \<in> set (take j ls)"
  have "tl (drop j ls) = drop (Suc j) ls"
    by (simp add: drop_Suc drop_tl)
  then show "insert (ls ! j) (set (remove1 (ls ! j) (take j ls)) \<union> set (drop (Suc j) ls)) = set (take j ls) \<union> set (tl (drop j ls))"
    using a1 split_list_first by fastforce
next
  assume a1: "ls ! j \<notin> set (take j ls)"
  have H1: "tl (drop j ls) = drop (Suc j) ls"
    by (simp add: drop_Suc drop_tl)
  then show "set (take j ls) \<union> set (drop (Suc j) ls) =
         set (take j ls) \<union> set (tl (drop j ls))" using H1 by auto
next
  assume a2: "j < length ls"
  show "remove1 (ls ! j) ls = remove1 (ls ! j) (take j ls @ ls ! j # drop (j + 1) ls)"
    by (simp add: Cons_nth_drop_Suc a2)
qed

(* FIXME: remove because unused? *)
lemma sum_list_elements_unat_sum':
  "\<lbrakk>Suc (Suc 0) \<le> length (ls::time list); sum_list (map unat ls) = unat (sum_list ls)\<rbrakk>
    \<Longrightarrow> \<forall>j < length ls. \<forall>i < j. unat (ls!i) + unat (ls!j) = unat (ls!i + ls!j)"
proof safe
  fix i j
  assume len: "Suc (Suc 0) \<le> length ls"
  assume sum_eq: "sum_list (map unat ls) = unat (sum_list ls)"
  assume H: "j < length ls" "i < j"
  have  "sum_list (map unat ls) =
          unat (ls!j) + unat (ls!i) + sum_list (map unat (remove1 (ls!i) (remove1 (ls!j) ls)))"
  proof -
    have setin_i': "ls!i \<in> set (remove1 (ls!j) ls)"
      proof
        have take_in: "(take j ls)!i \<in> set (take j ls)"
           using length_take nth_mem[where xs="take j ls" and n=i] H by clarsimp
        have take: "ls!i \<in> set (take j ls)"
          using nth_take[where xs=ls, OF H(2), symmetric] take_in by fastforce
        show ?this using take by simp
        next
        show "set (take j ls) \<subseteq> set (remove1 (ls!j) ls)"
         using remove1_nth_rewrite[where j=j and ls=ls] H by clarsimp
      qed
  have remove_j: "sum_list (map unat ls) =
            unat (ls!j) + sum_list (map unat (remove1 (ls!j) ls))"
    using H nth_mem[of j] sum_list_map_remove1 by fastforce
  also
  have remove_i: "sum_list (map unat (remove1 (ls!j) ls)) =
            unat (ls!i) + sum_list (map unat (remove1 (ls!i) (remove1 (ls!j) ls)))"
    using setin_i' sum_list_map_remove1 by fastforce
  then show ?thesis using remove_j by simp qed
  then have bounded: "unat (ls!j) + unat (ls!i) \<le> unat (sum_list ls)"
    using sum_eq by simp
  show " unat (ls!i) + unat (ls!j) = unat (ls!i + ls!j)"
    using sum_list_bounded_le[where ls="[ls!i, ls!j]" and budget="sum_list ls", simplified] bounded
    by fastforce
qed

(* FIXME: remove because unused? *)
lemmas sum_list_elements_unat_sum = sum_list_elements_unat_sum'[rule_format]

(***)

lemma valid_refills_consumed_time_update[iff]:
  "valid_refills p (consumed_time_update f s) = valid_refills p s"
  by (simp add: valid_refills_def)

lemma sum_list_replicate:
  "n * unat a = sum_list (map unat (replicate n a))"
  by (induct n arbitrary: a; simp)

lemma replicate_no_overflow:
  "n * unat (a :: time) \<le> unat (upper_bound :: time)
   \<Longrightarrow> unat (word_of_int n * a) = n * unat a"
  using sum_list_bounded_le[symmetric] sum_list_replicate
  by (metis (mono_tags, hide_lams) Num.of_nat_simps(5) word_of_nat word_unat.Rep_inverse)

lemma unat_MIN_BUDGET_MIN_SC_BUDGET:
  "unat MIN_BUDGET + unat MIN_BUDGET = unat MIN_SC_BUDGET"
  unfolding MIN_SC_BUDGET_def
  sorry (* unat_MIN_BUDGET_MIN_SC_BUDGET *)
  (* sorried until we have a principled approach to bounds on kernelWCET_ticks and us_to_ticks *)

lemma MIN_BUDGET_le_MIN_SC_BUDGET:
  "MIN_BUDGET \<le> MIN_SC_BUDGET"
  apply (simp add: MIN_BUDGET_def MIN_SC_BUDGET_def ARM.kernelWCET_ticks_def)
  apply (rule us_to_ticks_mono[simplified mono_def, rule_format])
  apply (simp add: word_le_nat_alt)
  using ARM.kernelWCET_us_no_overflow replicate_no_overflow
  by (metis mult_le_mono1 nat_le_linear numeral_le_iff of_nat_numeral rel_simps(2) rel_simps(4)
            word_of_nat)

\<comment> \<open>Function definitions and lemmas for showing that the unat sum of the r_amounts of a refill list
    does not overflow, and is equal to the budget of the scheduling context\<close>

fun
  refill_list_to_intervals :: "refill list \<Rightarrow> (nat set) list"
where
  "refill_list_to_intervals [] = []"
| "refill_list_to_intervals (r # rs) = [{unat (r_time r) ..< unat (r_time r) + unat (r_amount r)}]
                                        @ (refill_list_to_intervals rs)"

lemma refill_list_to_intervals_length:
  "length (refill_list_to_intervals refills) = length refills"
  by (induction refills; simp)

lemma max_closed_open_interval:
  "\<lbrakk>0 < b; {a ..< b} \<noteq> {}\<rbrakk> \<Longrightarrow> Max {a ..< b} = (b :: nat) - Suc 0"
  by (fastforce intro: linorder_class.Max_eqI)

lemma disjnt_max_min:
  "\<lbrakk>finite A; finite B; (Max A) < (Min B)\<rbrakk> \<Longrightarrow> A \<inter> B = {}"
  apply (rule ccontr)
  apply (frule int_not_emptyD)
  using Max_ge Min_le by (metis basic_trans_rules(23) leD)

lemma less_le_nonzero_helper:
  assumes "0 < a"
  shows "a \<le> b \<Longrightarrow> a - Suc 0 < b"
  using assms by linarith

lemma refill_list_to_intervals_finite:
  "l < length (refill_list_to_intervals refills) \<Longrightarrow> finite (refill_list_to_intervals refills ! l)"
  apply (induct refills arbitrary: l rule: length_induct)
  apply (case_tac xs, simp)
  by (case_tac "l=0") auto

lemma min_refill_list_to_intervals:
  "\<lbrakk>\<forall>m < length refills. r_amount (refills ! m) \<noteq> 0;
    l < length (refill_list_to_intervals refills)\<rbrakk>
   \<Longrightarrow> Min (refill_list_to_intervals refills ! l) = unat (r_time (refills ! l))"
  apply (induct refills arbitrary: l rule: length_induct)
  apply (case_tac xs, simp)
  apply (case_tac "l=0")
   by (fastforce simp add: unat_eq_1(1) unat_gt_0 Min_eq_iff)+

lemma disjoint_refill_list_to_intervals:
  "\<lbrakk>no_overflow refills;
    ordered_disjoint refills;
    \<forall>m < length refills. unat (r_amount (refills ! m)) \<noteq> 0;
    l < length (refill_list_to_intervals refills);
    k < l\<rbrakk>
   \<Longrightarrow> disjnt (refill_list_to_intervals refills ! k) (refill_list_to_intervals refills ! l)"
  apply (induct refills arbitrary: k l rule: length_induct)
  apply (case_tac xs)
   apply simp
  apply (rename_tac a list)
  apply simp
  apply (frule no_overflow_def[atomized, THEN iffD1])
  apply (frule ordered_disjoint_def[atomized, THEN iffD1])
  apply (simp add: disjnt_def)
  apply (case_tac "k = 0")
   apply clarsimp
   apply (frule_tac x=list in spec)
   apply (rule disjnt_max_min)
     apply blast
    apply (simp add: refill_list_to_intervals_finite)
   apply (subst min_refill_list_to_intervals)
     apply force
    apply simp
   apply (rule_tac y="unat (r_time a) + unat (r_amount a) - Suc 0" in le_less_trans)
    apply (rule preorder_class.eq_refl)
    apply (rule Max_eqI)
      apply force
     apply force
    apply (drule_tac x=0 and P="\<lambda>m. m<Suc (length list) \<longrightarrow> 0 < unat (r_amount ((a # list) ! m))"
                          in spec)
    apply simp
   apply (rule less_le_nonzero_helper)
    apply (drule_tac x=0 and P="\<lambda>m. m<Suc (length list) \<longrightarrow> 0 < unat (r_amount ((a # list) ! m))"
                          in spec)
    apply force
   apply (frule_tac refills="a # list" and k=0 and l="l" in ordered_disjoint_non_adjacent
          ; (fastforce simp: refill_list_to_intervals_length)?)
  apply clarsimp
  apply (drule_tac x=list in spec)
  apply (elim impE)
      apply blast
     apply (clarsimp simp: no_overflow_tail)
    apply (clarsimp simp: ordered_disjoint_tail)
   apply force
  by simp

lemma refills_sum_unat_intervals:
  "sum_list (map unat (map r_amount refills))
   = sum_list (map card (refill_list_to_intervals refills))"
  apply (induct refills rule: length_induct)
  by (case_tac xs; simp)

fun
  refill_list_to_subset :: "refill list \<Rightarrow> nat set"
where
  "refill_list_to_subset [] = {}"
| "refill_list_to_subset (r # rs) = {unat (r_time r) ..< unat (r_time r) + unat (r_amount r)}
                                    \<union> (refill_list_to_subset rs)"

lemma non_empty_intervals_implies_refill_list_to_subset_non_empty:
  "\<lbrakk>refills \<noteq> [];
    \<forall>m < length refills. unat (r_amount (refills ! m)) \<noteq> 0\<rbrakk>
   \<Longrightarrow> refill_list_to_subset refills \<noteq> {}"
  apply (case_tac refills)
  by (fastforce simp add: unat_eq_1(1))+

lemma no_overflow_refill_list_to_subset_finite:
  "no_overflow refills \<Longrightarrow> finite (refill_list_to_subset refills)"
  apply (induct refills rule: length_induct)
  apply (rename_tac xs)
  apply (case_tac xs)
   using no_overflow_tail by fastforce+

lemma min_refill_list_to_subset:
  "\<lbrakk>refills \<noteq> [];
    no_overflow refills;
    ordered_disjoint refills;
    \<forall>m < length refills. unat (r_amount (refills ! m)) \<noteq> 0\<rbrakk>
   \<Longrightarrow> Min (refill_list_to_subset refills) = unat (r_time (hd refills))"
  apply (induct refills rule: length_induct)
  apply (rename_tac xs)
  apply (case_tac xs)
   apply simp
  apply (rename_tac a list)
  apply (frule_tac x=list in spec)
  apply clarsimp
  apply (case_tac list)
   apply (subst Min_eq_iff; fastforce?)
  apply (drule_tac x=list in spec)
  apply (elim impE; fastforce?)
    apply (clarsimp simp: no_overflow_tail)
   apply (clarsimp simp: ordered_disjoint_tail)
  apply (subst Min_Un; fastforce?)
    apply (rule no_overflow_refill_list_to_subset_finite)
   apply (clarsimp simp: no_overflow_tail)
  apply (subgoal_tac "Min {unat (r_time a)..<unat (r_time a) + unat (r_amount a)}
                       = unat (r_time a)")
   apply (frule_tac k=0 and l=1 in ordered_disjoint_no_overflow_implies_sorted; fastforce?)
  apply (subst Min_eq_iff)
    by fastforce+

lemma disjoint_interval_list_implies_sum_is_bounded:
  "\<lbrakk>no_overflow refills;
    ordered_disjoint refills;
    \<forall>m < length refills. unat (r_amount (refills ! m)) \<noteq> 0\<rbrakk>
   \<Longrightarrow> sum_list (map card (refill_list_to_intervals refills))
       = card (refill_list_to_subset refills)"
  apply (induct refills rule: length_induct)
  apply (rename_tac xs)
  apply (case_tac xs)
   apply simp
  apply (rename_tac a list)
  apply (subgoal_tac "card ({unat (r_time a)..<unat (r_time a) + unat (r_amount a)})
                      = unat (r_amount a)")
   prefer 2
   apply force
  apply (drule_tac x=list in spec)
  apply clarsimp
  apply (elim impE; fastforce?)
    apply (clarsimp simp: no_overflow_tail)
   apply (clarsimp simp: ordered_disjoint_tail)
  apply (case_tac list, simp)
  apply (rename_tac aa lista)
  apply (subgoal_tac "card ({unat (r_time a)..<unat (r_time a) + unat (r_amount a)}
                            \<union> refill_list_to_subset list)
                      = card ({unat (r_time a)..<unat (r_time a) + unat (r_amount a)})
                        + card (refill_list_to_subset list)")
   apply simp
  apply (rule card_Un_disjoint)
    apply blast
   using no_overflow_refill_list_to_subset_finite apply fastforce
  apply simp
  apply (rule disjnt_max_min)
    apply blast
   using no_overflow_refill_list_to_subset_finite apply fastforce
  apply (subgoal_tac "Min ({unat (r_time aa)..<unat (r_time aa) + unat (r_amount aa)}
                            \<union> refill_list_to_subset lista)
                      = unat (r_time aa)")
   apply clarsimp
   apply (rule_tac y="unat (r_time a) + unat (r_amount a) - Suc 0" in le_less_trans)
    apply (rule preorder_class.eq_refl)
    apply (fastforce intro: Max_eqI)
   apply (rule less_le_nonzero_helper; fastforce?)
   apply (simp add: ordered_disjoint_def)
   apply (drule_tac x=0 in spec)
   apply clarsimp
  apply (subgoal_tac "{unat (r_time aa)..<unat (r_time aa) + unat (r_amount aa)}
                         \<union> refill_list_to_subset lista
                       = refill_list_to_subset (aa # lista)")
   prefer 2
   apply force
  apply (rule_tac s="refill_list_to_subset (aa # lista)" and P="\<lambda>t. Min t = unat (r_time aa)"
               in subst)
   apply presburger
  apply (subst min_refill_list_to_subset)
      apply force
     using no_overflow_tail apply presburger
    using ordered_disjoint_tail apply presburger
   apply (metis Suc_length_conv less_Suc_eq_0_disj nth_Cons_Suc unat_eq_zero unat_gt_0)
  by (metis list.sel(1))

lemma max_union:
  "\<lbrakk>finite A; finite B; B \<noteq> {}; Max A < Min B\<rbrakk>
   \<Longrightarrow> Max (A \<union> B) = Max B"
  apply (subst eq_Max_iff; blast?)
  apply (intro conjI)
   apply (metis (no_types, lifting) Max_Un Max_gr_iff Max_in Min_gr_iff UnE Un_empty
                  dual_order.strict_implies_not_eq finite_UnI max.strict_coboundedI2 notemptyI)
  by simp

lemma no_overflow_implies_refill_list_to_subset_max_bounded:
  "\<lbrakk>refills \<noteq> [];
    no_overflow refills;
    ordered_disjoint refills;
    \<forall>m < length refills. unat (r_amount (refills ! m)) \<noteq> 0\<rbrakk>
   \<Longrightarrow> Max (refill_list_to_subset refills) \<le> unat (max_word :: time)"
  apply (induct refills rule: length_induct)
  apply (rename_tac xs)
  apply (case_tac xs)
   apply simp
  apply (rename_tac a list)
  apply simp
  \<comment> \<open>we introduce a couple facts which will be useful below\<close>
  apply (subgoal_tac "no_overflow list")
   prefer 2
   apply (clarsimp simp: no_overflow_tail)
  apply (subgoal_tac "ordered_disjoint list")
   prefer 2
   apply (clarsimp simp: ordered_disjoint_tail)
  apply (drule_tac x=list in spec)
  apply (erule impE)
   apply blast
  apply (case_tac list)
   apply (subgoal_tac "refill_list_to_subset list = {}")
    prefer 2
    apply force
   apply (clarsimp simp: no_overflow_def)
  apply (subst max_union)
      apply blast
     apply (clarsimp dest!: no_overflow_tail simp: no_overflow_refill_list_to_subset_finite)
    apply (fastforce intro: non_empty_intervals_implies_refill_list_to_subset_non_empty)
   apply (subst max_closed_open_interval; (fastforce simp: unat_eq_zero)?)
   apply (rule less_le_nonzero_helper, fastforce)
   apply (subst min_refill_list_to_subset; fastforce?)
   apply (simp add: hd_conv_nth ordered_disjoint_def)
   by fastforce+

lemma no_overflow_implies_refill_list_to_subset_card_bounded:
  "\<lbrakk>refills \<noteq> [];
    no_overflow refills;
    ordered_disjoint refills;
    \<forall>m<length refills. unat (r_amount (refills ! m)) \<noteq> 0\<rbrakk>
   \<Longrightarrow> card (refill_list_to_subset refills) \<le> Suc (unat (max_word :: time))"
  apply (frule no_overflow_implies_refill_list_to_subset_max_bounded; fastforce?)
  apply (rule subset_eq_atLeast0_lessThan_card)
  apply (clarsimp simp: atLeastLessThanSuc_atLeastAtMost)
  apply (rule_tac y="Max (refill_list_to_subset refills)" in order_trans)
   apply (rule Max.coboundedI)
    apply (rule no_overflow_refill_list_to_subset_finite)
    by blast+

lemma no_overflow_ordered_disjoint_implies_refills_sum_unat_no_overflow:
  "\<lbrakk>refills \<noteq> [];
    no_overflow refills;
    ordered_disjoint refills;
    \<forall>m<length refills. unat (r_amount (refills ! m)) \<noteq> 0\<rbrakk>
   \<Longrightarrow> sum_list (map unat (map r_amount refills)) \<le> Suc (unat (max_word :: time))"
  apply (subst refills_sum_unat_intervals)
  apply (subst disjoint_interval_list_implies_sum_is_bounded; fastforce?)
   using disjoint_refill_list_to_intervals
  apply (simp add: refill_list_to_intervals_length disjoint_refill_list_to_intervals)
  apply (rule no_overflow_implies_refill_list_to_subset_card_bounded)
  by blast+

lemma sum_list_helper:
  "sum_list (map card (refill_list_to_intervals refills))
   = sum_list (map unat (map r_amount refills))"
  apply (induction refills rule: length_induct)
  by (case_tac xs, simp+)

lemma unat_sum_max_word:
  fixes w :: "'a::len word"
  shows "unat w + unat v = Suc (unat (max_word :: 'a word)) \<Longrightarrow> w + v = 0"
  using unat_word_ariths(1)
  by (metis max_word_eq plus_1_eq_Suc unat_1 word_pow_0 word_unat.Rep_eqD zadd_diff_inverse)

lemma unat_sum_list_of_words:
  fixes list :: "'a::len word list"
  shows " unat (sum_list list) = (sum_list (map unat list)) mod 2 ^ LENGTH('a)"
  apply (induct list rule: length_induct)
  apply (case_tac xs, simp)
  apply (drule_tac x=list in spec)
  apply simp
  by (metis rdmods(5) unat_word_ariths(1))

lemma sum_exact_overflow:
  "sum_list (map unat (list :: time list)) = Suc (unat (max_word :: time)) \<Longrightarrow> sum_list list = 0"
  apply (induct list rule: length_induct)
   apply (case_tac xs)
   apply simp
  apply (drule_tac x=list in spec)
  apply simp
  using unat_sum_list_of_words
  by (metis (no_types, hide_lams) unat_sum_max_word arith_simps(49)
             plus_nat.simps(2) rdmods(5) unat_eq_1(1) unat_eq_1(2) unat_word_ariths(1))

lemma exactly_max_word_plus_one_implies_unat_refills_sum_is_zero:
  "\<lbrakk>no_overflow refills;
    ordered_disjoint refills;
    \<forall>m < length refills. unat (r_amount (refills ! m)) \<noteq> 0;
    refill_list_to_subset refills = {0..unat (max_word :: time)}\<rbrakk>
   \<Longrightarrow> unat (refills_sum refills) = 0"
  supply map_map[simp del]
  apply (simp add: refills_sum_def word_le_nat_alt)
  apply (subgoal_tac "card (refill_list_to_subset refills) = Suc (unat max_word)")
   prefer 2
   apply simp
  apply (frule disjoint_interval_list_implies_sum_is_bounded; assumption?)
  apply (fastforce simp: sum_list_helper sum_exact_overflow)+
  done

lemma max_interval_helper:
  "\<lbrakk>A \<noteq> {}; finite A; card A = Suc b; Max A \<le> b\<rbrakk> \<Longrightarrow> A = {0..b}"
  apply (subst set_eq_subset)
  apply (intro conjI)
   apply (rule ccontr)
   apply clarsimp
  apply (rule ccontr)
  apply clarsimp
  apply (induct b)
   apply fast
  apply (rule ccontr)
  apply (subgoal_tac "A \<subset> {0..Suc b}")
   apply (subgoal_tac "card A < card {0..Suc b}")
    apply fastforce
   using psubset_card_mono apply blast
  apply (rule ccontr)
  using subset_not_subset_eq by force

lemma no_overflow_ordered_disjoint_non_zero_refills_implies_card_not_equal_to_suc_max_word:
  "\<lbrakk>refills \<noteq> [];
    no_overflow refills;
    ordered_disjoint refills;
    \<forall>m < length refills. unat (r_amount (refills ! m)) \<noteq> 0;
    MIN_BUDGET \<le> refills_sum refills\<rbrakk>
   \<Longrightarrow> \<not>card (refill_list_to_subset refills) = Suc (unat (max_word :: time))"
  apply (rule ccontr)
  apply simp
  apply (frule exactly_max_word_plus_one_implies_unat_refills_sum_is_zero; assumption?)
    apply blast
   apply (rule max_interval_helper; fastforce?)
    apply (erule no_overflow_refill_list_to_subset_finite)
   apply (rule no_overflow_implies_refill_list_to_subset_max_bounded; fastforce?)
  using MIN_BUDGET_pos apply (simp add: unat_eq_1(1))
  done

lemma unat_sum_list_at_most_unat_max_word:
  "\<lbrakk>refills \<noteq> [];
    no_overflow refills;
    ordered_disjoint refills;
    \<forall>m < length refills. unat (r_amount (refills ! m)) \<noteq> 0;
    MIN_BUDGET \<le> refills_sum refills\<rbrakk>
   \<Longrightarrow> sum_list (map unat (map r_amount refills)) \<le> unat (max_word :: time)"
  supply map_map[simp del]
  apply (frule no_overflow_ordered_disjoint_implies_refills_sum_unat_no_overflow; assumption?)
  apply (frule no_overflow_ordered_disjoint_non_zero_refills_implies_card_not_equal_to_suc_max_word
         ; assumption?)
  apply (subst sum_list_helper[symmetric])
  apply (subst disjoint_interval_list_implies_sum_is_bounded; assumption?)
  apply (subgoal_tac "sum_list (map unat (map r_amount refills))
                    = card (refill_list_to_subset refills)")
   apply linarith
  apply (subst sum_list_helper[symmetric])
  apply (subst disjoint_interval_list_implies_sum_is_bounded)
     apply (simp add: sc_valid_refills_def)+
  done

lemma unat_sum_list_equals_budget:
  "\<lbrakk>refills \<noteq> [];
    no_overflow refills;
    ordered_disjoint refills;
    \<forall>m < length refills. unat (r_amount (refills ! m)) \<noteq> 0;
    MIN_BUDGET \<le> refills_sum refills\<rbrakk>
   \<Longrightarrow> sum_list (map unat (map r_amount refills)) = unat (refills_sum refills)"
  supply map_map[simp del]
  apply (frule unat_sum_list_at_most_unat_max_word; assumption?)
  by (fastforce simp: refills_sum_def intro: sum_list_bounded_le)

lemma sc_valid_refills_unat_sum_list_at_most_unat_max_word:
  "\<lbrakk>sc_valid_refills sc;
    MIN_SC_BUDGET \<le> sc_budget sc\<rbrakk>
   \<Longrightarrow> sum_list (map unat (map r_amount (sc_refills sc))) \<le> unat (max_word :: time)"
  apply (rule unat_sum_list_at_most_unat_max_word)
      apply (simp add: sc_valid_refills_def)+
   apply (elim conjE)
   apply (metis MIN_BUDGET_pos gr0I unat_eq_zero word_le_less_eq word_not_simps(1))
  apply (simp add: sc_valid_refills_def refills_sum_def)
  using MIN_BUDGET_le_MIN_SC_BUDGET by force

lemma valid_refills_refills_unat_sum_equals_budget:
  "\<lbrakk>sc_valid_refills sc;
    MIN_SC_BUDGET \<le> sc_budget sc\<rbrakk>
   \<Longrightarrow> sum_list (map unat (map r_amount (sc_refills sc))) = unat (sc_budget sc)"
  supply map_map [simp del]
  apply (simp add: sc_valid_refills_def; elim conjE)
  apply (rule_tac s="refills_sum (sc_refills sc)" and t="sc_budget sc" in subst; assumption?)
  apply (rule unat_sum_list_equals_budget; fastforce?)
  apply (metis MIN_BUDGET_pos unat_eq_zero word_le_less_eq word_not_simps(1))
  using MIN_BUDGET_le_MIN_SC_BUDGET by force

lemma valid_refills_scheduler_action_update[iff]:
  "valid_refills p (scheduler_action_update f s) = valid_refills p s"
  by (simp add: valid_refills_def)

lemma valid_refills_ready_queues_update[iff]:
  "valid_refills p (ready_queues_update f s) = valid_refills p s"
  by (simp add: valid_refills_def)

lemma valid_refills_release_queue_update[iff]:
  "valid_refills p (release_queue_update f s) = valid_refills p s"
  by (simp add: valid_refills_def)

lemma valid_refills_kheap_tcb_update[iff]:
  "tcb_at t s \<Longrightarrow> valid_refills p (s\<lparr>kheap := kheap s(t \<mapsto> TCB tcb)\<rparr>) = valid_refills p s"
  by (clarsimp simp: valid_refills_def obj_at_def is_tcb)

crunches tcb_sched_action,set_scheduler_action, refill_capacity, refill_sufficient,
tcb_release_enqueue, tcb_release_remove, refill_ready, reschedule_required, possible_switch_to
  for valid_refills[wp]: "valid_refills scp"
  (wp: dxo_wp_weak hoare_vcg_if_lift2 crunch_wps)

crunch valid_refills[wp]: tcb_sched_action,set_scheduler_action,refill_capacity,refill_sufficient
   "valid_refills scp"
crunch valid_refills[wp]: tcb_release_enqueue,tcb_release_remove,refill_ready "valid_refills scp"
  (wp: crunch_wps)

crunch valid_refills[wp]: reschedule_required,
possible_switch_to "valid_refills scp"

  (wp: dxo_wp_weak hoare_vcg_if_lift2 crunch_wps)

lemma valid_refills_exst [iff]:
  "valid_refills p (trans_state f s) = valid_refills p s"
  by (simp add: valid_refills_def valid_state_def)

lemma valid_refills_reprogram_timer_update [iff]:
  "valid_refills p (reprogram_timer_update f s) = valid_refills p s"
  by (simp add: valid_refills_def valid_state_def)

crunches postpone
  for valid_refills[wp]: "valid_refills sc"
  (wp: crunch_wps)

lemma sched_context_resume_valid_refills[wp]:
  "\<lbrace>valid_refills scptr\<rbrace> sched_context_resume p \<lbrace>\<lambda>_. valid_refills scptr\<rbrace>"
  by (wpsimp simp: sched_context_resume_def wp: hoare_vcg_if_lift2 hoare_drop_imp)

lemma update_sched_context_valid_refills_no_budget_update_const:
  "\<lbrace>valid_refills scptr
     and K (scptr=p \<longrightarrow> sc_valid_refills newsc)\<rbrace>
     update_sched_context p (\<lambda>_. newsc)
      \<lbrace>\<lambda>_. valid_refills scptr\<rbrace>"
  by (wpsimp simp: valid_refills_def update_sched_context_def obj_at_def sc_valid_refills_def
          wp: set_object_wp get_object_wp)

lemma update_sched_context_valid_refills:
  "\<lbrace>valid_refills scptr
     and K (sc_valid_refills newsc)\<rbrace>
     update_sched_context p (\<lambda>_. newsc)
      \<lbrace>\<lambda>_. valid_refills scptr\<rbrace>"
  apply (wpsimp simp: valid_refills_def update_sched_context_def obj_at_def
          wp: set_object_wp get_object_wp split_del: if_split)
  by (clarsimp simp: sc_valid_refills_def)

lemma update_sched_context_valid_refills':
  "\<lbrace>K (sc_valid_refills newsc)\<rbrace>
   update_sched_context p (\<lambda>_. newsc)
  \<lbrace>\<lambda>_. valid_refills p\<rbrace>"
  by (wpsimp simp: valid_refills_def update_sched_context_def obj_at_def
               wp: set_object_wp get_object_wp)

lemma update_sched_context_valid_refills_no_budget_update:
  "\<lbrace>valid_refills scptr
        and K (\<forall>sc. sc_valid_refills sc \<longrightarrow> sc_valid_refills (f sc))\<rbrace>
    update_sched_context p f
   \<lbrace>\<lambda>_. valid_refills scptr\<rbrace>"
  apply (wpsimp simp: update_sched_context_def obj_at_def
                  wp: set_object_wp get_object_wp)
  by (clarsimp simp: valid_refills_def obj_at_def sc_valid_refills_def window_def)

lemma set_thread_state_valid_refills[wp]:
  "\<lbrace>valid_refills scptr\<rbrace> set_thread_state tp st \<lbrace>\<lambda>_. valid_refills scptr\<rbrace>"
  by (wpsimp wp: sts_obj_at_impossible simp: valid_refills_def)

(* FIXME move *)
lemma sorted_wrt_last_append:
  "\<lbrakk>\<And>x y z. P x y \<Longrightarrow> P y z \<Longrightarrow> P x z; sorted_wrt P (ls::'a list);
         P (last ls) new; ls \<noteq> []\<rbrakk>
      \<Longrightarrow> sorted_wrt P (ls @ [new])"
  apply (induction ls, simp)
  apply (clarsimp split: if_split_asm)
  by (drule_tac x="last ls" in bspec, simp) fastforce

lemma refill_new_valid_refills[wp]:
  "\<lbrace>(\<lambda>s. unat (cur_time s) + unat period \<le> unat (max_word :: time))
       and (\<lambda>s. if scptr \<noteq> p then valid_refills scptr s else \<exists>sc n. ko_at (SchedContext sc n) p s)
       and K (MIN_REFILLS \<le> max_refills \<and> budget \<le> period \<and> MIN_SC_BUDGET \<le> budget)\<rbrace>
     refill_new p max_refills budget period
    \<lbrace>\<lambda>_. valid_refills scptr\<rbrace>"
  apply (wpsimp simp: refill_new_def update_sched_context_def set_refills_def is_round_robin_def
                  wp: set_object_wp get_object_wp get_sched_context_wp)
  apply (clarsimp simp: valid_refills_def refills_sum_def obj_at_def MIN_REFILLS_def
                        sufficient_refills_defs ordered_disjoint_def no_overflow_def
                        window_def sc_valid_refills_def)
   apply (simp add: word_le_nat_alt MIN_BUDGET_le_MIN_SC_BUDGET)
  using word_le_nat_alt by fastforce

lemma refill_word_proof_helper:
  "\<lbrakk>unat (head_time :: time) + 2 * unat period \<le> unat (max_word :: time);
    larger \<le> period;
    smaller \<le> larger\<rbrakk>
    \<Longrightarrow> unat (head_time + period - (larger - smaller))
        = unat head_time + unat period - unat larger + unat smaller"
  apply (subgoal_tac "unat (head_time + period) = unat head_time + unat period")
   apply (subgoal_tac "unat (head_time + period - (larger - smaller))
                       = unat (head_time + period) - unat (larger - smaller)")
    apply (simp add: unat_sub)
    apply (metis word_le_nat_alt Nat.diff_add_assoc2 Nat.diff_diff_right unat_plus_simple
                 word_le_plus_either)
   apply (simp add: unat_plus_simple unat_sub word_le_imp_diff_le
                    word_le_plus_either word_le_nat_alt)
  apply (rule unat_add_lem', simp add: max_word_def)
  done

lemma refill_update_valid_refills[wp]:
  "\<lbrace>(\<lambda>s. unat (cur_time s) + 2 * unat new_period \<le> unat (max_word::time))
    and (\<lambda>s. \<exists>sc n. obj_at (\<lambda>ko. ko = SchedContext sc n
                \<and> unat (r_time (refill_hd sc)) + 2 * unat new_period \<le> unat (max_word :: time)) p s)
    and valid_refills scptr
    and K (MIN_REFILLS \<le> new_max_refills \<and> MIN_SC_BUDGET \<le> new_budget
           \<and> new_budget \<le> new_period)\<rbrace>
    refill_update p new_period new_budget new_max_refills
   \<lbrace>\<lambda>_. valid_refills scptr\<rbrace>"
  apply (unfold refill_update_def)
  apply (wpsimp simp: set_refills_def get_refills_def set_object_def is_round_robin_def
                      update_sched_context_def refill_ready_def sc_valid_refills_def
           split_del: if_split
                  wp: get_object_wp get_sched_context_wp hoare_vcg_if_lift2 set_object_wp)
  apply (intro conjI impI allI;
         clarsimp simp: obj_at_def valid_refills_def MIN_REFILLS_def refills_sum_def
                        not_le not_less MIN_BUDGET_nonzero
                 split: if_split_asm; intro conjI impI; fastforce?)

      \<comment> \<open>new_budget \<le> r_amount (refill_hd sc) and scptr is refill_ready\<close>
       apply (clarsimp simp: sc_valid_refills_def valid_refills_def ordered_disjoint_def
                             no_overflow_def window_def word_le_nat_alt)
        apply (rule order_trans[where y="unat MIN_SC_BUDGET"])
         using MIN_BUDGET_le_MIN_SC_BUDGET word_le_nat_alt apply fast
        apply (simp add: word_le_nat_alt)

    \<comment> \<open>new_budget \<le> r_amount (refill_hd sc) and scptr is not refill_ready\<close>
       apply (clarsimp simp: sc_valid_refills_def valid_refills_def ordered_disjoint_def
                             no_overflow_def window_def word_le_nat_alt)
        apply (rule order_trans[where y="unat MIN_SC_BUDGET"])
         using MIN_BUDGET_le_MIN_SC_BUDGET word_le_nat_alt apply fast
        apply (simp add: word_le_nat_alt)

   \<comment> \<open>r_amount (refill_hd sc) < new_budget and unused < MIN_BUDGET\<close>
     apply (clarsimp simp: sc_valid_refills_def valid_refills_def)
     apply (intro conjI)

        \<comment> \<open>ordered_disjoint\<close>
        apply (simp add: ordered_disjoint_def)
        apply (rename_tac sc n)
        apply (subgoal_tac "unat (r_time (refill_hd sc) + (new_period - MIN_BUDGET))
                            = unat (r_time (refill_hd sc)) + unat (new_period - MIN_BUDGET)")
         apply clarsimp
         apply (subgoal_tac "MIN_BUDGET \<le> new_budget")
          apply (simp add: unat_sub)
          using diff_le_mono word_le_nat_alt apply blast
         apply (simp add: word_le_nat_alt)
         apply (rule order_trans[where y="unat MIN_SC_BUDGET"])
          using MIN_BUDGET_le_MIN_SC_BUDGET word_le_nat_alt apply fast
         apply (simp add: word_le_nat_alt)
       apply (simp add: window_def word_le_nat_alt)
        apply (rule unat_add_lem')
        apply (subgoal_tac "unat (new_period - MIN_BUDGET) \<le> unat new_period")
         apply (simp add: max_word_def)
        apply (subgoal_tac "MIN_BUDGET \<le> new_period")
         apply (simp add: unat_sub)
        apply (meson MIN_BUDGET_le_MIN_SC_BUDGET le_trans word_le_nat_alt)

       \<comment> \<open>no_overflow\<close>
       apply (simp add: no_overflow_def)
       apply clarsimp
       apply (rename_tac sc n na)
       apply (case_tac "na=0")
        apply clarsimp
        apply (subgoal_tac "MIN_BUDGET \<le> new_budget")
         apply (simp add: unat_sub word_le_nat_alt)
        apply (meson MIN_BUDGET_le_MIN_SC_BUDGET le_trans word_le_nat_alt)
       apply clarsimp
       apply (subgoal_tac "unat (r_time (refill_hd sc) + (new_period - MIN_BUDGET))
                           = unat (r_time (refill_hd sc)) + unat (new_period - MIN_BUDGET)")
        apply clarsimp
        apply (subgoal_tac "MIN_BUDGET \<le> new_period")
         apply (simp add: unat_sub word_le_nat_alt)
        apply (meson MIN_BUDGET_le_MIN_SC_BUDGET le_trans word_le_nat_alt)
       apply (rule unat_add_lem')
       apply (subgoal_tac "MIN_BUDGET \<le> new_period")
        apply (simp add: unat_sub max_word_def)
       apply (meson MIN_BUDGET_le_MIN_SC_BUDGET le_trans word_le_nat_alt)

      \<comment> \<open>MIN_BUDGET\<close>
      apply clarsimp
      apply (rename_tac sc n na)
      apply (case_tac "na=0")
       apply clarsimp
       apply (simp add: word_le_nat_alt)
       apply (subgoal_tac "MIN_BUDGET \<le> new_budget")
        apply (simp add: unat_sub)
        apply (subgoal_tac "2 * unat MIN_BUDGET \<le> unat new_budget")
         apply linarith
        using unat_MIN_BUDGET_MIN_SC_BUDGET apply linarith
       using MIN_BUDGET_le_MIN_SC_BUDGET unat_MIN_BUDGET_MIN_SC_BUDGET word_le_nat_alt
       apply fastforce
      apply clarsimp

     \<comment> \<open>period_window\<close>
     apply (simp add: window_def)
     apply (rename_tac sc n)
     apply (subgoal_tac "unat (r_time (refill_hd sc) + (new_period - MIN_BUDGET))
                        = unat (r_time (refill_hd sc)) + unat (new_period - MIN_BUDGET)")
      apply clarsimp
      using word_le_nat_alt unat_sub MIN_BUDGET_le_MIN_SC_BUDGET
      apply (simp add: unat_arith_simps(1) unat_sub)
     apply (rule unat_add_lem')
     apply (subgoal_tac "unat (new_period - MIN_BUDGET) \<le> unat new_period")
      apply (simp add: max_word_def)
     using MIN_BUDGET_le_MIN_SC_BUDGET apply (meson le_trans word_le_nat_alt word_sub_le_iff)

    \<comment> \<open>two inconsistent cases\<close>
    apply (find_goal \<open>match premises in "new_budget < 2 * MIN_BUDGET" \<Rightarrow> \<open>-\<close>\<close>
           , force simp: MIN_SC_BUDGET_def)+

  \<comment> \<open>r_amount (refill_hd sc) < new_budget and MIN_BUDGET \<le> unused\<close>
  apply (simp add: sc_valid_refills_def valid_refills_def)
  apply (intro conjI)

     \<comment> \<open>ordered_disjoint\<close>
     apply (simp add: ordered_disjoint_def)
     apply clarsimp
     apply (rename_tac sc n)
     apply (frule order.strict_implies_order)
     apply (frule (2) refill_word_proof_helper[where larger=new_budget
              and head_time="r_time (refill_hd sc)"
              and smaller="r_amount (refill_hd sc)" for sc])
     apply clarsimp
     apply (metis Nat.add_diff_assoc add_leE le_eq_less_or_eq unat_arith_simps(1))

    \<comment> \<open>no_overflow\<close>
    apply (clarsimp simp: no_overflow_def)
    apply (rename_tac sc n na)
    apply (case_tac "na=0")
     apply (drule_tac x=0 and P="\<lambda>n. n < length (sc_refills sc)
                                       \<longrightarrow> unat (r_time (sc_refills sc ! n)) + unat (r_amount (sc_refills sc ! n))
                                            \<le> unat max_word" in spec)
     apply (simp add: hd_conv_nth max_word_def)
    apply clarsimp
    apply (frule order.strict_implies_order)
    apply (frule (2) refill_word_proof_helper[where larger=new_budget
                 and head_time="r_time (refill_hd sc)"
                 and smaller="r_amount (refill_hd sc)" for sc])
    apply (clarsimp simp: unat_sub word_le_nat_alt)

   \<comment> \<open>MIN_BUDGET\<close>
   apply clarsimp
   apply (case_tac "na=0")
    apply clarsimp
    apply (simp add: hd_conv_nth)
   apply clarsimp

  \<comment> \<open>period_window\<close>
  apply clarsimp
  apply (simp add: window_def)
  apply (frule_tac order.strict_implies_order)
  apply (frule refill_word_proof_helper[where larger=new_budget
           and head_time="r_time (refill_hd sc)"
          and smaller="r_amount (refill_hd sc)" for sc])
    apply simp
   apply blast
  apply clarsimp
  apply (simp add: unat_sub word_le_nat_alt)
  done

lemma schedule_used_sum [simp]:
  "refills_sum (schedule_used b refills new) = refills_sum (refills @ [new])"
  apply (clarsimp simp: refills_sum_def Let_def)
  apply (case_tac refills)
   apply simp
  apply simp
   apply (clarsimp simp: Let_def)
   apply (subgoal_tac "sum_list (map r_amount (butlast list)) + r_amount (last list)
                     = sum_list (map r_amount (butlast list @ [last list]))")
    prefer 2
    apply (metis (no_types, hide_lams) Groups.add_ac(2) list.simps(9) refills_sum_append
                  refills_sum_def rev_eq_Cons_iff rev_map sum_list.Cons sum_list.rev)
  by simp

(* schedule_used lemmas *)
lemma schedule_used_non_nil:
  "Suc 0 \<le> length (schedule_used b x new)"
  by (induct x; clarsimp simp: Let_def)

lemma schedule_used_length':
  "length (schedule_used b x new) = length x \<or> length (schedule_used b x new) = length x + 1"
  by (induct x; clarsimp simp: Let_def)

lemma schedule_used_length_max:
  "length (schedule_used full x new) \<le> Suc (length x)"
  using schedule_used_length' nat_le_linear by force

lemma schedule_used_length_full:
  "list \<noteq> [] \<longrightarrow> length (schedule_used True list new) = length list"
  by (case_tac list; fastforce simp: Let_def)

lemma ordered_disjoint_append:
  "\<lbrakk>left \<noteq> [] \<longrightarrow> ordered_disjoint left;
    right \<noteq> [] \<longrightarrow> ordered_disjoint right;
    left \<noteq> [] \<and> right \<noteq> [] \<longrightarrow> unat (r_time (last left)) + unat (r_amount (last left))
                                 \<le> unat (r_time (hd right));
    left @ right = result\<rbrakk>
   \<Longrightarrow> ordered_disjoint result"
  apply (clarsimp simp: ordered_disjoint_def)
  apply (case_tac left, clarsimp; case_tac right; fastforce?)
    apply (subst nth_append not_less)+
  apply (clarsimp split: if_splits)
  using last_conv_nth by (metis less_antisym list_exhaust_size_eq0 nth_Cons')

lemma no_overflow_append:
  "\<lbrakk>no_overflow left; no_overflow right; left @ right = result\<rbrakk>
   \<Longrightarrow> no_overflow result"
  apply (clarsimp simp: no_overflow_def)
  apply (subst nth_append not_less)+
  apply (drule_tac x="n - length left"
               and P="\<lambda>n. n < length right
                           \<longrightarrow> unat (r_time (right ! n)) + unat (r_amount (right ! n)) \<le> unat max_word"
                in spec)
  by simp

(* FIXME: maybe move? *)
lemma last_butlast_list:
  "butlast list \<noteq> []
   \<Longrightarrow> last (butlast list) = list ! (length list - Suc (Suc 0))"
  by (metis last_conv_nth One_nat_def butlast_conv_take diff_Suc_eq_diff_pred le_add_diff_inverse2
            le_simps(3) length_butlast less_add_one list_exhaust_size_eq0 nth_take zero_order(5))

lemma butlast_nonempty_length:
  "butlast list \<noteq> [] \<Longrightarrow> Suc 0 < length list"
  by (cases list, simp, force)

lemma schedule_used_ordered_disjoint:
  "\<lbrakk>ordered_disjoint list;
    \<forall>m < length list. MIN_BUDGET \<le> r_amount (list ! m);
    list \<noteq> [] \<longrightarrow> unat (r_time (last list)) + unat (r_amount (last list)) \<le> unat (r_time new)\<rbrakk>
   \<Longrightarrow> ordered_disjoint (schedule_used full list new)"
  apply (case_tac list)
   apply (simp add: ordered_disjoint_def)
  apply (rename_tac a lista)

  \<comment> \<open>first branch of schedule_used\<close>
  apply (case_tac "r_amount new < MIN_BUDGET \<and> \<not>full
                   \<and> 2 * MIN_BUDGET \<le> r_amount (last list) + r_amount new")
   apply simp
   apply (elim conjE)

   \<comment> \<open>we introduce some useful facts\<close>
   apply (subgoal_tac "MIN_BUDGET \<le> r_time new")
    prefer 2
    apply (clarsimp split: if_splits)
     apply (simp add: word_le_nat_alt)
    apply (fastforce simp: word_le_nat_alt last_conv_nth)
   apply (subgoal_tac "MIN_BUDGET - r_amount new \<le> r_time new")
    prefer 2
    apply (fastforce intro: order_trans[where y=MIN_BUDGET]
                      simp: word_sub_le_iff)
   apply (subgoal_tac "unat (r_time new - (MIN_BUDGET - r_amount new))
                       = unat (r_time new) - unat MIN_BUDGET + unat (r_amount new)")
    prefer 2
    apply (simp add: unat_sub word_le_nat_alt less_imp_le_nat unat_mono)
   \<comment> \<open>end of the proof of the useful facts\<close>

   apply (intro conjI impI allI)

    \<comment> \<open>list is of length one\<close>
    apply (clarsimp simp: Let_def split: if_split_asm)
    apply (simp add: ordered_disjoint_def)
    apply (subgoal_tac "unat (r_amount a - (MIN_BUDGET - r_amount new))
                        = unat (r_amount a) - unat (MIN_BUDGET) + unat (r_amount new)")
     apply clarsimp
     apply (subgoal_tac "unat MIN_BUDGET \<le> unat (r_amount a)")
      apply clarsimp
      using diff_le_mono apply blast
     using word_le_nat_alt apply fastforce
    apply (subgoal_tac "unat (r_amount a - (MIN_BUDGET - r_amount new))
                        = unat (r_amount a) - unat (MIN_BUDGET - r_amount new)")
     apply (frule order.strict_implies_order)
     apply (clarsimp simp: unat_sub word_le_nat_alt)
    apply (meson unat_sub word_le_imp_diff_le word_le_less_eq)

   \<comment> \<open>list is of length greater than one\<close>

   \<comment> \<open>another useful fact\<close>
   apply (subgoal_tac "unat MIN_BUDGET \<le> unat (r_amount (last lista))")
    prefer 2
    apply (drule_tac x="length (a#lista) - Suc 0"
                 and P="\<lambda>m. m < Suc (length lista)
                                 \<longrightarrow> MIN_BUDGET \<le> r_amount ((a # lista) ! m)"
                  in spec)
    apply (simp add: word_le_nat_alt)
    using last_conv_nth apply force
  \<comment> \<open>end of the proof of the useful fact\<close>

   apply (clarsimp simp: Let_def)
   apply (rule_tac left="a # butlast lista"
              and right="[last lista\<lparr>r_amount := r_amount (last lista) - (MIN_BUDGET - r_amount new)\<rparr>,
                                    \<lparr>r_time = r_time new - (MIN_BUDGET - r_amount new), r_amount = MIN_BUDGET\<rparr>]"
               in ordered_disjoint_append)
      apply clarsimp
      apply (rule ordered_disjoint_sublist; assumption?)
      apply (metis butlast.simps(2) sublist_butlast)
     apply (clarsimp simp: ordered_disjoint_def)
     apply (subgoal_tac "MIN_BUDGET - r_amount new \<le> r_amount (last lista)")
      apply (simp only: unat_sub)
     apply (rule order_trans[where y=MIN_BUDGET])
      apply (frule order.strict_implies_order)
      using word_sub_le_iff apply blast
     apply (simp add: word_le_nat_alt)
    apply (intro conjI impI)
    apply clarsimp
    apply (intro conjI impI)
     apply (frule_tac k=0 and l="length (a#lista) - Suc 0" in ordered_disjoint_non_adjacent
            ; fastforce?)
     using hd_conv_nth last_conv_nth apply force
    apply (simp add: last_butlast_list)
    apply (simp add: last_conv_nth)
    apply (simp add: ordered_disjoint_def)
    apply (drule_tac x="length (a # lista) - Suc (Suc 0)" in spec)
    apply (elim impE)
     apply force
    apply (subgoal_tac "Suc 0 < length lista \<longrightarrow> (a # lista) ! (length lista - Suc 0)
                                                  = lista ! (length lista - Suc (Suc 0))")
     apply (erule impE)
      apply (fastforce simp: butlast_nonempty_length)+

  \<comment> \<open>second branch of schedule_used\<close>
  apply (case_tac "r_amount new < MIN_BUDGET \<or> full")
   apply clarsimp
   apply (intro conjI impI)
      apply argo
     apply (simp add: ordered_disjoint_def)
    apply argo
   apply (clarsimp simp: Let_def)
   apply (rule_tac left="a # butlast lista"
               and right="[\<lparr>r_time = r_time new - r_amount (last lista),
                            r_amount = r_amount (last lista) + r_amount new\<rparr>]"
                in ordered_disjoint_append)
      apply clarsimp
      apply (rule ordered_disjoint_sublist; assumption?)
      apply (metis butlast.simps(2) sublist_butlast)
     apply clarsimp
     apply (simp add: ordered_disjoint_def)
    apply (intro conjI impI)
    apply clarsimp
    apply (intro conjI impI)
     apply (subgoal_tac "r_amount (last lista) \<le> r_time new")
      apply (simp add: unat_sub)
      apply (rule_tac y="unat (r_time (last lista))" in order_trans)
       apply (frule_tac refills="a # lista" and k=0 and l="length (a # lista) - Suc 0"
                     in ordered_disjoint_non_adjacent; fastforce?)
      using hd_conv_nth last_conv_nth apply force
      apply linarith
     using word_le_nat_alt apply fastforce
    apply (subgoal_tac "r_amount (last lista) \<le> r_time new")
     apply (simp add: unat_sub)
     apply (rule_tac y="unat (r_time (last lista))" in order_trans)
      apply (simp add: last_butlast_list)
      apply (simp add: last_conv_nth)
      apply (simp add: ordered_disjoint_def)
      apply (drule_tac x="length (a # lista) - Suc (Suc 0)" in spec)
      apply clarsimp
      apply (subgoal_tac "Suc 0 < length lista \<longrightarrow> (a # lista) ! (length lista - Suc 0)
                                                    = lista ! (length lista - Suc (Suc 0))")
       apply (subgoal_tac "Suc 0 < length lista")
        apply (fastforce simp: butlast_nonempty_length word_le_nat_alt unat_sub)+

  \<comment> \<open>last branch of schedule_used\<close>
  apply clarsimp
  apply (rule_tac left="a # lista" and right="[new]" in ordered_disjoint_append
         ; (fastforce simp: ordered_disjoint_def)?)
  done

lemma schedule_used_no_overflow:
  "\<lbrakk>no_overflow list;
    no_overflow [new];
    \<forall>m < length list. MIN_BUDGET \<le> r_amount (list ! m);
    list \<noteq> [] \<longrightarrow> unat (r_time (last list)) + unat (r_amount (last list)) \<le> unat (r_time new)\<rbrakk>
   \<Longrightarrow> no_overflow (schedule_used full list new)"
  apply (case_tac list)
   apply simp
  apply (rename_tac a lista)

  \<comment> \<open>we introduce a useful fact\<close>
  apply (subgoal_tac "MIN_BUDGET \<le> r_time new")
   prefer 2
   apply (drule_tac x="length list - Suc 0"
                and P="\<lambda>m. m < length list \<longrightarrow> MIN_BUDGET \<le> r_amount (list ! m)"
                 in spec)
   apply (clarsimp simp: word_le_nat_alt split: if_splits)
   apply (metis One_nat_def add_leD2 le_trans last_conv_nth)
  \<comment> \<open>end of the proof of the useful fact\<close>

  \<comment> \<open>first branch of schedule_used\<close>
  apply (case_tac "r_amount new < MIN_BUDGET \<and> \<not>full
                   \<and> 2 * MIN_BUDGET \<le> r_amount (last list) + r_amount new")
   apply (elim conjE)

   \<comment> \<open>we introduce a useful fact\<close>
   apply (subgoal_tac "unat (r_time new - (MIN_BUDGET - r_amount new))
                       = unat (r_time new) - unat MIN_BUDGET + unat (r_amount new)")
    prefer 2
    apply (subgoal_tac "unat (r_time new - (MIN_BUDGET - r_amount new))
                        = unat (r_time new) - unat (MIN_BUDGET - r_amount new)")
     apply (clarsimp simp: word_le_nat_alt)
     apply (simp add: unat_sub)
     apply (frule order.strict_implies_order)
     using Nat.diff_diff_right word_le_nat_alt apply blast
    apply (subgoal_tac "MIN_BUDGET - r_amount new \<le> r_time new")
     apply (simp add: unat_sub)
    apply (rule_tac y=MIN_BUDGET in order_trans)
     using word_le_less_eq word_sub_le_iff apply blast
    apply blast
   \<comment> \<open>end of the proof of the useful fact\<close>

   apply simp
   apply (intro conjI impI)

    \<comment> \<open>list of length one\<close>

    \<comment> \<open>another useful fact\<close>
    apply (subgoal_tac "MIN_BUDGET - r_amount new \<le> r_amount a")
     prefer 2
     apply (rule_tac y=MIN_BUDGET in order_trans)
      using word_le_less_eq word_sub_le_iff apply blast
     apply simp
    \<comment> \<open>end of the proof of the useful fact\<close>

    apply (simp add: no_overflow_def)
    apply (clarsimp simp: Let_def)
    apply (case_tac "n=0")
     apply clarsimp
     apply (subgoal_tac "unat (r_amount a - (MIN_BUDGET - r_amount new))
                         = unat (r_amount a) - unat (MIN_BUDGET - r_amount new)")
      apply linarith
     apply (simp add: unat_sub)
    apply (clarsimp simp: word_le_nat_alt)

   \<comment> \<open>list is of length greater than one\<close>

   \<comment> \<open>yet another useful fact\<close>
   apply (subgoal_tac "MIN_BUDGET - r_amount new \<le> r_amount (last lista)")
    prefer 2
    apply (rule_tac y=MIN_BUDGET in order_trans)
     using word_le_less_eq word_sub_le_iff apply blast
    apply (drule_tac x="length (a#lista) - Suc 0"
                 and P="\<lambda>m. m < Suc (length lista)
                            \<longrightarrow> MIN_BUDGET \<le> r_amount ((a # lista) ! m)"
                  in spec)
    using last_conv_nth apply fastforce
   \<comment> \<open>end of the proof of the useful fact\<close>

   apply (clarsimp simp: Let_def)
   apply (rule_tac left="a # butlast lista"
              and right="[last lista\<lparr>r_amount := r_amount (last lista) - (MIN_BUDGET - r_amount new)\<rparr>,
                                    \<lparr>r_time = r_time new - (MIN_BUDGET - r_amount new), r_amount = MIN_BUDGET\<rparr>]"
               in no_overflow_append)
      apply (rule no_overflow_sublist; assumption?)
      apply (metis butlast.simps(2) sublist_butlast)
    apply (simp add: no_overflow_def)
    apply clarsimp
    apply (case_tac "n=0")
     apply clarsimp
     apply (subgoal_tac "unat (r_amount (last lista) - (MIN_BUDGET - r_amount new))
                         = unat (r_amount (last lista)) - unat (MIN_BUDGET - r_amount new)")
      apply linarith
     apply (fastforce simp: unat_sub word_le_nat_alt)+

  \<comment> \<open>second branch of schedule_used\<close>
  apply (case_tac "r_amount new < MIN_BUDGET \<or> full")
   apply simp
   apply (intro conjI impI)

      apply (clarsimp simp: Let_def split: if_splits)
     apply (simp add: no_overflow_def)
     apply (subgoal_tac "unat (r_time new - r_amount a) = unat (r_time new) - unat (r_amount a)")
      apply (subgoal_tac "unat (r_amount a + r_amount new)
                          = unat (r_amount a) + unat (r_amount new)")
       apply (subgoal_tac "unat (r_amount a) \<le> unat (r_time new)")
        apply force
       apply force
      apply (rule unat_add_lem', simp add: max_word_def)
     apply (subgoal_tac "r_amount a \<le> r_time new")
      apply (blast intro: unat_sub)
     apply (simp add: word_le_nat_alt)

  \<comment> \<open>list of length greater than two\<close>
    apply (clarsimp simp: Let_def split: if_splits)
   apply (simp add: no_overflow_def)
   apply clarsimp
   apply (case_tac "n=0")
    apply clarsimp
    apply (drule_tac x=0 in spec)
    apply (clarsimp simp: Let_def)
   apply (clarsimp simp: Let_def)
   apply (case_tac "n < length (a # butlast (lista))")
    apply clarsimp
    apply (drule_tac x=n in spec)
    apply (subgoal_tac "(butlast lista @ [\<lparr>r_time = r_time new - r_amount (last lista),
                                           r_amount = r_amount (last lista) + r_amount new\<rparr>])
                         ! (n - Suc 0)
                         = (butlast lista) ! (n - Suc 0)")
     apply simp
     apply (subgoal_tac "butlast lista ! (n - Suc 0) = lista ! (n - Suc 0)")
      apply presburger
     apply (simp add: nth_butlast)
    apply (simp add: nth_append diff_less_mono)
   apply clarsimp
   apply (subgoal_tac "n = length (a # butlast (lista))")
    prefer 2
    apply force
   apply clarsimp
   apply (subgoal_tac "(butlast lista @ [\<lparr>r_time = r_time new - r_amount (last lista),
                                          r_amount = r_amount (last lista) + r_amount new\<rparr>])
                        ! (length lista - Suc 0)
                        = \<lparr>r_time = r_time new - r_amount (last lista),
                           r_amount = r_amount (last lista) + r_amount new\<rparr>")
    prefer 2
    apply (metis (no_types, hide_lams) Groups.add_ac(2) append_len2 length_Cons list.size(3)
                                       nth_append_length snoc_eq_iff_butlast)
   apply clarsimp
   apply (subgoal_tac "unat (r_amount (last lista) + r_amount new)
                       = unat (r_amount (last lista)) + unat (r_amount new)")
    apply clarsimp
    apply (subgoal_tac "r_amount (last lista) \<le> r_time new")
     apply (simp add: unat_sub)
    apply (simp add: unat_arith_simps(1))
   apply (rule unat_add_lem', simp add: max_word_def)

  \<comment> \<open>\<not> (r_amount new < MIN_BUDGET \<or> b)\<close>
  apply (simp add: no_overflow_def)
  apply clarsimp
  apply (case_tac "n=0")
   apply (drule_tac x=0 in spec)
  by (fastforce simp: nth_append)+

lemma schedule_used_MIN_BUDGET:
  "\<lbrakk>unat MIN_SC_BUDGET \<le> sum_list (map unat (map r_amount (list @ [new])));
    sum_list (map unat (map r_amount (list @ [new]))) \<le> unat (max_word :: time);
    \<forall>m < length list. MIN_BUDGET \<le> r_amount (list ! m)\<rbrakk>
   \<Longrightarrow> \<forall>m < length (schedule_used full list new).
              MIN_BUDGET \<le> r_amount ((schedule_used full list new) ! m)"
  supply map_map[simp del]
  apply (case_tac list)
   apply simp
   using word_le_nat_alt MIN_BUDGET_le_MIN_SC_BUDGET basic_trans_rules(23) apply blast
  apply (rename_tac a lista)

  \<comment> \<open>first branch of schedule_used\<close>

  apply (case_tac "r_amount new < MIN_BUDGET \<and> \<not>full
                   \<and> 2 * MIN_BUDGET \<le> r_amount (last list) + r_amount new")
   apply simp
   apply (intro conjI impI)
    apply (clarsimp simp: Let_def)
    apply (case_tac "m=0")
     apply clarsimp
     apply (simp add: word_le_nat_alt)
     apply (subgoal_tac "unat (r_amount a - (MIN_BUDGET - r_amount new))
                         = unat (r_amount a) - unat MIN_BUDGET + unat (r_amount new)")
      prefer 2
      apply (subgoal_tac "unat (r_amount a - (MIN_BUDGET - r_amount new))
                          = unat (r_amount a) - unat (MIN_BUDGET - r_amount new)")
       apply clarsimp
       apply (simp add: unat_sub)
       apply (clarsimp simp: unat_arith_simps(2))
      apply (subgoal_tac "MIN_BUDGET - r_amount new \<le> r_amount a")
       apply (simp add: unat_sub)
      apply (rule_tac y=MIN_BUDGET in order_trans)
       using word_le_less_eq word_sub_le_iff apply fastforce
      using MIN_BUDGET_le_MIN_SC_BUDGET word_le_nat_alt apply fast
     apply clarsimp
     apply (frule order.strict_implies_order)
     apply (simp add: add_le_imp_le_diff unat_MIN_BUDGET_MIN_SC_BUDGET)
    apply (clarsimp simp: Let_def)
   apply (clarsimp simp: Let_def)
   apply (case_tac "m < length (a # butlast lista)")
    apply (subgoal_tac "(a # butlast lista @ [last lista\<lparr>r_amount := r_amount (last lista) - (MIN_BUDGET - r_amount new)\<rparr>,
                                                        \<lparr>r_time = r_time new - (MIN_BUDGET - r_amount new), r_amount = MIN_BUDGET\<rparr>])
                         ! m
                         = (a # butlast lista) ! m")
     apply (clarsimp simp del: length_butlast)
     apply (drule_tac x=m in spec)
     apply (subgoal_tac "(a # butlast lista) ! m = (a # lista) ! m")
      prefer 2
      apply (metis butlast.simps(2) length_Cons nth_butlast)
     apply simp
    apply (metis append_Cons nth_append)
   apply (case_tac "m= length list - Suc 0")
    apply clarsimp
    apply (subgoal_tac "(a # butlast lista @ [last lista\<lparr>r_amount := r_amount (last lista) - (MIN_BUDGET - r_amount new)\<rparr>,
                                                        \<lparr>r_time = r_time new - (MIN_BUDGET - r_amount new), r_amount = MIN_BUDGET\<rparr>])
                         ! (length list - Suc 0)
                         = last lista\<lparr>r_amount := r_amount (last lista) - (MIN_BUDGET - r_amount new)\<rparr>")
     prefer 2
     apply (simp add: nth_append)
    apply clarsimp
    apply (simp add: word_le_nat_alt)
    apply (subgoal_tac "unat (r_amount (last lista) - (MIN_BUDGET - r_amount new))
                        = unat (r_amount (last lista)) - unat MIN_BUDGET + unat (r_amount new)")
     prefer 2
     apply (subgoal_tac "unat (r_amount (last lista) - (MIN_BUDGET - r_amount new))
                         = unat (r_amount (last lista)) - unat (MIN_BUDGET - r_amount new)")
      apply clarsimp
      apply (simp add: unat_sub)
      apply (subgoal_tac "unat MIN_BUDGET \<le> unat (r_amount (last lista))")
       apply (frule order.strict_implies_order)
       apply (simp add: word_le_nat_alt)
      apply (drule_tac x="length lista" in spec)
      apply (elim impE)
       apply linarith
      using last_conv_nth apply force
     apply (subgoal_tac "MIN_BUDGET - r_amount new \<le> r_amount (last lista)")
      apply (simp add: unat_sub)
     apply (rule_tac y=MIN_BUDGET in order_trans)
      using word_le_less_eq word_sub_le_iff apply fastforce
     apply (simp add: word_le_nat_alt)
     apply (drule_tac x="length lista" in spec)
     apply (elim impE)
      apply linarith
     using last_conv_nth apply force
    apply clarsimp
    apply (subgoal_tac "MIN_BUDGET \<le> r_amount (last lista)")
     apply (subgoal_tac "unat (2 * MIN_BUDGET) = 2 * unat MIN_BUDGET")
      apply (subgoal_tac "unat (r_amount (last lista) + r_amount new)
                          = unat (r_amount (last lista)) + unat (r_amount new)")
       apply linarith
      apply (rule unat_add_lem', simp add: max_word_def)
      apply (subgoal_tac "unat (r_amount (last lista)) \<le> sum_list (map unat (map r_amount lista))")
       apply linarith
      apply (rule member_le_sum_list)
      apply force
     using unat_MIN_BUDGET_MIN_SC_BUDGET MIN_SC_BUDGET_def apply force
    apply (simp add: word_le_nat_alt)
    apply (drule_tac x="length lista" in spec)
    apply (elim impE)
     apply linarith
    apply (simp add: last_conv_nth)
   apply clarsimp
   apply (subgoal_tac "(butlast lista @ [last lista\<lparr>r_amount := r_amount (last lista) - (MIN_BUDGET - r_amount new)\<rparr>,
                                                   \<lparr>r_time = r_time new - (MIN_BUDGET - r_amount new), r_amount = MIN_BUDGET\<rparr>])
                        ! (m - Suc 0)
                        = \<lparr>r_time = r_time new - (MIN_BUDGET - r_amount new), r_amount = MIN_BUDGET\<rparr>")
    prefer 2
    apply (subgoal_tac "m = Suc (length lista)")
     prefer 2
     apply linarith
    apply (simp add: nth_append)
   apply clarsimp

  \<comment> \<open>second branch of schedule_used\<close>
  apply (case_tac "r_amount new < MIN_BUDGET \<or> full")
   apply simp
   apply (intro conjI impI)

      \<comment> \<open>list of length one\<close>
      apply (clarsimp simp: Let_def split: if_splits)
     apply (simp add: word_le_nat_alt)
     apply (subgoal_tac "unat (r_amount a + r_amount new)
                         = unat (r_amount a) + unat (r_amount new)")
      using word_le_nat_alt MIN_BUDGET_le_MIN_SC_BUDGET apply linarith
     apply (rule unat_add_lem', simp add: max_word_def)
    apply (clarsimp simp: Let_def split: if_splits)
   apply (clarsimp simp: Let_def split: if_splits)
   apply (case_tac "m=0")
    apply force
   apply (case_tac "m < length (a # butlast lista)")
    apply (subgoal_tac "(a # butlast lista @ [\<lparr>r_time = r_time new - r_amount (last lista),
                                               r_amount = r_amount (last lista) + r_amount new\<rparr>])
                         ! m
                         = (a # butlast lista) ! m")
     apply (drule_tac x=m in spec)
     apply (clarsimp simp: nth_butlast)
    apply (simp add: nth_butlast nth_append)

   \<comment> \<open>list of length greater than one\<close>
   apply (clarsimp simp: Let_def)
   apply (subgoal_tac "(butlast lista @ [\<lparr>r_time = r_time new - r_amount (last lista),
                                          r_amount = r_amount (last lista) + r_amount new\<rparr>])
                        ! (m - Suc 0)
                        = \<lparr>r_time = r_time new - r_amount (last lista),
                           r_amount = r_amount (last lista) + r_amount new\<rparr>")
    apply clarsimp
    apply (subgoal_tac "unat (r_amount (last lista) + r_amount new)
                        = unat (r_amount (last lista)) + unat (r_amount new)")
     apply (drule_tac x="length lista" in spec)
     apply (fastforce simp: last_conv_nth word_le_nat_alt)
    apply (rule unat_add_lem')
    apply (subgoal_tac "unat (r_amount (last lista)) \<le> sum_list (map unat (map r_amount lista))")
     apply (simp add: max_word_def)
    apply (simp add: last_conv_nth)
    apply (rule member_le_sum_list, simp)
   apply (simp add: nth_butlast nth_append)

  \<comment> \<open>last branch of schedule_used\<close>
  apply clarsimp
  by (metis nth_append append_Cons length_Cons less_Suc_eq nth_append_length word_not_le)

lemma refill_word_proof_helper2:
  "\<lbrakk>usage \<le> r_amount (hd refills);
    ordered_disjoint refills;
    unat (r_amount (hd refills)) + unat (r_amount (hd (tl refills))) \<le> unat (max_word :: time);
    Suc 0 < length refills\<rbrakk>
   \<Longrightarrow> unat (r_time (hd (tl refills)) - (r_amount (hd refills) - usage))
       = unat (r_time (hd (tl refills))) - unat (r_amount (hd refills)) + unat usage
       \<and>
       unat (r_amount (hd (tl refills)) + (r_amount (hd refills) - usage))
       = unat (r_amount (hd (tl refills))) + unat (r_amount (hd refills)) - unat usage
       \<and> unat (r_amount (hd refills)) \<le> unat (r_time (hd (tl refills)))
       \<and> unat usage \<le> unat (r_amount (hd refills))"
  apply (intro conjI)
     apply (subgoal_tac "unat (r_amount (hd refills)) \<le> unat (r_time (hd (tl refills)))")
      apply (subgoal_tac "unat (r_time (hd (tl refills)) - (r_amount (hd refills) - usage))
                          = unat (r_time (hd (tl refills))) - unat (r_amount (hd refills) - usage)")
       apply (simp add: unat_sub word_le_nat_alt)
     apply (simp add: unat_arith_simps(1) unat_sub)
     apply (simp add: ordered_disjoint_def)
     apply (drule_tac x=0 in spec)
     apply (erule impE)
      apply fastforce
     apply (case_tac refills; force simp: hd_conv_nth)
    apply (subgoal_tac "unat (r_amount (hd (tl refills)) + (r_amount (hd refills) - usage))
                        = unat (r_amount (hd (tl refills))) + unat (r_amount (hd refills) - usage)")
     apply (metis Nat.diff_add_assoc2 add.commute unat_sub word_le_nat_alt)
    apply (rule unat_add_lem', simp add: unat_sub max_word_def)
   apply (simp add: ordered_disjoint_def)
   apply (drule_tac x=0 in spec)
   apply (erule impE)
    apply fastforce
   apply (case_tac refills; force simp: hd_conv_nth)
  apply (simp add: word_le_nat_alt)
  done

lemma tail_nonempty_length:
  "tl list \<noteq> [] \<Longrightarrow> Suc 0 < length list"
  by (cases list, simp, simp)

(* FIXME: develop strategy to shorten this proof *)
lemma refill_budget_check_valid_refills[wp]:
   "\<lbrace>(\<lambda>s. kheap s p = Some (SchedContext sc n)
          \<and> unat (r_time (refill_hd sc)) + 2 * unat (sc_period sc) + unat usage
                     \<le> unat (max_word :: time)
          \<and> MIN_SC_BUDGET \<le> sc_budget sc \<and> sc_budget sc \<le> sc_period sc)
      and valid_refills p\<rbrace>
    refill_budget_check usage
    \<lbrace>\<lambda>_. valid_refills p\<rbrace>"
  supply if_weak_cong[cong del] if_split[split del] schedule_used.simps[simp del] map_map[simp del]
  apply (clarsimp simp: refill_budget_check_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (wpsimp simp: set_refills_def update_sched_context_def set_object_def get_object_def
                      refill_full_def is_round_robin_def refill_ready_def
                  wp: set_object_wp get_object_wp)
  apply (clarsimp simp: obj_at_def set_object_def get_object_def)
  apply (intro conjI impI allI)

      \<comment> \<open>first branch of refill_budget_check - head overfill overrun. Reschedule in one refill\<close>
      apply (clarsimp simp: valid_refills_def obj_at_def set_object_def get_object_def
                     split: if_splits)
      apply (case_tac "p \<noteq> cur_sc s")
       apply clarsimp
      apply (simp add: sc_valid_refills_def)
      apply (intro conjI impI allI)
          apply (simp add: refills_sum_def)
          apply (simp add: ordered_disjoint_def)
         apply (simp add: no_overflow_def)
         apply (subgoal_tac "unat (r_time (refill_hd sc) + sc_period sc + usage)
                             = unat (r_time (refill_hd sc)) + unat (sc_period sc) + unat usage")
          apply (subgoal_tac "unat (sc_budget sc) \<le> unat (sc_period sc)")
           apply linarith
          apply (fastforce simp: word_le_nat_alt)
         apply (subgoal_tac "unat (r_time (refill_hd sc) + sc_period sc + usage)
                             = unat (r_time (refill_hd sc) + sc_period sc) + unat usage")
          apply clarsimp
          apply (rule unat_add_lem', simp add: max_word_def)
         apply (rule unat_add_lem')
         apply (subgoal_tac "unat (r_time (refill_hd sc) + sc_period sc)
                            = unat (r_time (refill_hd sc)) + unat (sc_period sc)")
          apply (simp add: max_word_def)
         apply (rule unat_add_lem', simp add: max_word_def)
        using MIN_BUDGET_le_MIN_SC_BUDGET apply force
       apply (simp add: window_def word_le_nat_alt)
      using le_def apply fastforce

     \<comment> \<open>second branch of refill_budget_check - head refill consumed exactly\<close>
     apply (clarsimp simp: valid_refills_def sc_valid_refills_def obj_at_def set_object_def
                           get_object_def
                    split: if_splits)
     apply (intro conjI)
           apply (simp add: refills_sum_def add_ac)
           apply (case_tac "sc_refills sc", force, simp)

          \<comment> \<open>ordered_disjoint\<close>
          apply (rule_tac full=False
                      and list="tl (sc_refills sc)"
                      and new="\<lparr>r_time = r_time (refill_hd sc) + sc_period sc,
                                r_amount = r_amount (refill_hd sc)\<rparr>"
                       in schedule_used_ordered_disjoint)
            apply (metis ordered_disjoint_tail hd_Cons_tl)
           apply clarsimp
           apply (drule_tac x="Suc m" in spec)
           apply (elim impE)
            apply linarith
           apply (metis list.exhaust_sel nth_Cons_Suc)
          apply (clarsimp simp: Let_def split: if_splits)
          apply (simp add: window_def)
          apply (subgoal_tac "unat (r_time (refill_hd sc) + sc_period sc)
                              = unat (r_time (refill_hd sc)) + unat (sc_period sc)")
           apply (subgoal_tac "refill_tl sc = last (tl (sc_refills sc))")
            apply clarsimp
           apply (simp add: last_tl)
          apply (rule unat_add_lem', simp add: max_word_def)

         \<comment> \<open>no_overflow\<close>
         apply (rule schedule_used_no_overflow)
            apply (metis no_overflow_tail hd_Cons_tl)
           apply (simp add: no_overflow_def)
           apply (subgoal_tac "unat (r_time (refill_hd sc) + sc_period sc)
                               = unat (r_time (refill_hd sc)) + unat (sc_period sc)")
            apply clarsimp
           apply (rule unat_add_lem', simp add: max_word_def)
          apply clarsimp
          apply (drule_tac x="Suc m" in spec)
          apply (elim impE)
           apply linarith
          apply (metis list.exhaust_sel nth_Cons_Suc)
         apply (clarsimp simp: Let_def split: if_splits)
         apply (simp add: window_def)
         apply (subgoal_tac "unat (r_time (refill_hd sc) + sc_period sc)
                             = unat (r_time (refill_hd sc)) + unat (sc_period sc)")
          apply clarsimp
          apply (subgoal_tac "refill_tl sc = last (tl (sc_refills sc))")
           apply argo
          apply (simp add: last_tl)
         apply (rule unat_add_lem', simp add: max_word_def)

       \<comment> \<open>MIN_BUDGET\<close>
        apply (subgoal_tac "sum_list (map unat (map r_amount (tl (sc_refills sc)
                                                              @ [\<lparr>r_time = r_time (refill_hd sc) + sc_period sc,
                                                                  r_amount = r_amount (refill_hd sc)\<rparr>])))
                            = unat (sc_budget sc)")
         apply (rule schedule_used_MIN_BUDGET)
           apply (clarsimp simp: word_le_nat_alt)
          apply (clarsimp simp: word_le_nat_alt)
         apply clarsimp
         apply (drule_tac x="Suc na" in spec)
         apply (elim impE)
          apply linarith
         apply (metis list.exhaust_sel nth_Cons_Suc)
        apply (frule unat_sum_list_equals_budget; assumption?)
          apply (metis MIN_BUDGET_nonzero unat_eq_1(1) word_le_0_iff)
         apply (simp add: refills_sum_def)
         using MIN_BUDGET_le_MIN_SC_BUDGET apply fastforce
        apply (case_tac "sc_refills sc", simp, fastforce)

      \<comment> \<open>period_window\<close>
       apply (case_tac "tl (sc_refills sc)")
        apply (simp add: schedule_used.simps window_def)
        apply (rule order_trans[where y="unat (sc_budget sc)"])
         apply (cases "sc_refills sc", fast, case_tac list, fastforce, fastforce)
        using unat_arith_simps(1) apply blast
       apply (clarsimp simp: Let_def window_def schedule_used.simps split: if_splits)
       apply (intro conjI impI)

          \<comment> \<open>first of five word proofs\<close>
          apply (rule order_trans[where y="unat (sc_budget sc)"])
           apply (fastforce simp: hd_conv_nth)
          apply (fastforce simp: unat_arith_simps(1))

         \<comment> \<open>second of the five word proofs\<close>
         apply (subgoal_tac "unat (r_time (refill_hd sc) + sc_period sc)
                             = unat (r_time (refill_hd sc)) + unat (sc_period sc)")
          apply clarsimp
          apply (simp add: ordered_disjoint_def)
          apply (drule_tac x=0 in spec)
          apply (elim impE)
            apply (force simp: tail_nonempty_length)
           apply (cases "sc_refills sc", simp, fastforce)
          apply (rule unat_add_lem', simp add: max_word_def)

         \<comment> \<open>third of the five word proofs\<close>
         apply (subgoal_tac "unat (r_time (refill_hd sc) + sc_period sc - (MIN_BUDGET - r_amount (refill_hd sc)))
                             = unat (r_time (refill_hd sc)) + unat (sc_period sc)
                               - unat MIN_BUDGET + unat (r_amount (refill_hd sc))")
          apply clarsimp
          apply (subgoal_tac "unat MIN_BUDGET \<le> unat (sc_period sc)")
           apply (clarsimp simp: ordered_disjoint_def)
           apply (drule_tac x=0 in spec)
           apply (elim impE)
            using hd_conv_nth apply fastforce
           using hd_conv_nth apply fastforce
          using MIN_BUDGET_le_MIN_SC_BUDGET word_le_nat_alt apply fastforce
         apply (subgoal_tac "unat (r_time (refill_hd sc) + sc_period sc - (MIN_BUDGET - r_amount (refill_hd sc)))
                             = unat (r_time (refill_hd sc) + sc_period sc)
                               - unat (MIN_BUDGET - r_amount (refill_hd sc))")
          apply (subgoal_tac "unat (r_time (refill_hd sc) + sc_period sc)
                              = unat (r_time (refill_hd sc)) + unat (sc_period sc)")
           apply clarsimp
           apply (simp add: unat_sub)
           apply (subgoal_tac "MIN_BUDGET \<le> sc_period sc")
            apply (simp add: hd_conv_nth word_le_not_less)
           using MIN_BUDGET_le_MIN_SC_BUDGET word_le_nat_alt apply fastforce
          apply (rule unat_add_lem', simp add: max_word_def)
         apply (metis Nat.add_0_right add_Suc_shift list.exhaust_sel list.size(4) nth_Cons_0
                      word_le_not_less zero_less_Suc)

        \<comment> \<open>fourth of the five word proofs\<close>
        apply (subgoal_tac "unat (r_time (refill_hd sc) + sc_period sc - r_amount (last list))
                            = unat (r_time (refill_hd sc)) + unat (sc_period sc)
                              - unat (r_amount (last list))")
         apply (subgoal_tac "unat (r_amount (last list)) \<le> unat (sc_period sc)")
          apply (subgoal_tac "unat (r_amount (last list) + r_amount (refill_hd sc))
                              = unat (r_amount (last list)) + unat (r_amount (refill_hd sc))")
           apply clarsimp
           apply (simp add: ordered_disjoint_def)
           apply (drule_tac x=0 in spec)
           apply (elim impE)
            apply (fastforce simp: hd_conv_nth)
           apply (fastforce simp: hd_conv_nth)
          apply (rule unat_add_lem', simp add: max_word_def)
         apply (rule order_trans[where y="unat (sc_budget sc)"])
          apply (metis hd_Cons_tl impossible_Cons le0 not_gr0 nth_Cons_0 word_not_le)
         apply (fastforce simp: unat_arith_simps(1))
        apply (subgoal_tac "unat (r_time (refill_hd sc) + sc_period sc - r_amount (last list))
                            = unat (r_time (refill_hd sc))
                              + unat (sc_period sc - r_amount (last list))")
         apply clarsimp
         apply (subgoal_tac "unat (r_amount (last list)) \<le> unat (sc_period sc)")
          apply (metis Nat.add_diff_assoc unat_arith_simps(1) unat_sub)
         apply (rule order_trans[where y="unat (sc_budget sc)"])
          apply (metis hd_Cons_tl impossible_Cons le0 not_gr0 nth_Cons_0 word_not_le)
         apply (fastforce simp: unat_arith_simps(1))
        apply (subgoal_tac "r_time (refill_hd sc) + sc_period sc - r_amount (last list)
                            = r_time (refill_hd sc) + (sc_period sc - r_amount (last list))")
         prefer 2
         apply fastforce
        apply (rule_tac s="r_time (refill_hd sc) + (sc_period sc - r_amount (last list))"
                    and t="r_time (refill_hd sc) + sc_period sc - r_amount (last list)"
                     in ssubst)
         apply blast
        apply (rule unat_add_lem')
        apply (subgoal_tac "r_amount (last list) \<le>sc_period sc")
         apply (simp add: unat_sub max_word_def)
        apply (metis (full_types) hd_Cons_tl impossible_Cons le0 not_gr0 nth_Cons_0 word_not_le)

       \<comment> \<open>last of the word proofs - similar to the second of the word proofs above\<close>
       apply (subgoal_tac "unat (r_time (refill_hd sc) + sc_period sc)
                          = unat (r_time (refill_hd sc)) + unat (sc_period sc)")
        apply clarsimp
        apply (simp add: ordered_disjoint_def)
        apply (drule_tac x=0 in spec)
        apply (elim impE)
         apply (simp add: tail_nonempty_length)
        apply (metis hd_Cons_tl nth_Cons_0 nth_Cons_Suc)
       apply (rule unat_add_lem', simp add: max_word_def)

      \<comment> \<open>length\<close>
      using schedule_used_non_nil neq_Nil_lengthI apply blast
     apply (subgoal_tac "length (tl (sc_refills sc)) = length (sc_refills sc) - Suc 0")
      apply (metis schedule_used_length_max Nitpick.size_list_simp(2) le_trans)
     apply simp

    \<comment> \<open>third branch of refill_budget_check - tail is empty,
         so just advance time of the single refill\<close>
    apply (clarsimp simp: valid_refills_def sc_valid_refills_def obj_at_def set_object_def
                             get_object_def
                   split: if_splits)
    apply (intro conjI)
         apply (subgoal_tac "sc_refills sc = [refill_hd sc]")
          apply (metis Nil_is_append_conv add.right_cancel append_Nil hd_append2 list.expand
                       list.sel(1) list.sel(3) neq_Nil_conv refills_sum_append refills_sum_cons
                       tl_append2)
         apply (metis list.exhaust_sel)
        apply (simp add: ordered_disjoint_def)
       apply (simp add: no_overflow_def)
       apply (subgoal_tac "unat (r_time (refill_hd sc)) + 2 * unat (sc_period sc) \<le> unat max_word")
        apply (frule_tac larger="r_amount (refill_hd sc)"
                     and smaller=usage
                      in refill_word_proof_helper)
          apply (simp add: word_le_nat_alt)
          apply (metis arith_simps(50) list.collapse refills_sum_cons refills_sum_nil)
         apply simp
        apply (subgoal_tac "unat (r_amount (refill_hd sc)) \<le> unat (sc_period sc)")
         apply linarith
        apply (metis list.exhaust_sel refills_sum_cons refills_sum_nil semiring_norm(51)
                     word_le_nat_alt)
       apply linarith
      apply (simp add: hd_conv_nth)
     apply (simp add: window_def)
     apply (rule order_trans[where y="unat (sc_budget sc)"])
      apply (metis arith_simps(50) le_def less_irrefl_nat list.exhaust_sel refills_sum_cons
                   refills_sum_nil)
     apply (simp add: word_le_nat_alt)
    apply (metis Nitpick.size_list_simp(2) length_0_conv)

   \<comment> \<open>fourth branch of refill_budget_check - remnant < MIN_BUDGET, so pop head,
        add remnant to second refill, and do schedule_used\<close>
   apply (clarsimp simp: valid_refills_def sc_valid_refills_def obj_at_def set_object_def
                          get_object_def
                  split: if_splits)

   \<comment> \<open>we introduce some facts which will be useful both for ordered_disjoint and no_overflow\<close>
   apply (frule word_le_not_less[THEN iffD2])
   apply (frule_tac refills="sc_refills sc" in unat_sum_list_equals_budget
          ; (simp add: refills_sum_def)?)
     apply (fastforce simp: MIN_BUDGET_pos unat_gt_0)
    using MIN_BUDGET_le_MIN_SC_BUDGET apply force
   apply (frule refill_word_proof_helper2[where usage=usage and refills="sc_refills sc"]
          ; fastforce?)
     apply (case_tac "sc_refills sc", fast, case_tac list, force, simp)
     apply (rule_tac y="unat (sc_budget sc)" in order_trans)
     apply linarith
     apply (simp add: word_le_nat_alt)
    apply (metis Nitpick.size_list_simp(2) Suc_less_eq2 length_greater_0_conv)
   apply (elim conjE)
   apply (subgoal_tac "unat (r_time (refill_hd sc) + sc_period sc)
                       = unat (r_time (refill_hd sc)) + unat (sc_period sc)")
    prefer 2
    apply (rule unat_add_lem', simp add: max_word_def)
   apply (subgoal_tac "MIN_BUDGET
                       \<le> r_amount (hd (tl (sc_refills sc))) + (r_amount (refill_hd sc) - usage)")
    prefer 2
    apply (simp add: word_le_nat_alt)
    apply (frule_tac x=0 in spec)
    apply (elim impE, fastforce)
    apply (frule_tac x=1 in spec)
    apply (elim impE)
     apply (force simp: tail_nonempty_length)
    apply (simp add: hd_conv_nth)
    apply (subgoal_tac "r_amount (sc_refills sc ! Suc 0) = r_amount (tl (sc_refills sc) ! 0)")
     apply force
    apply (metis length_greater_0_conv nth_tl)
   apply clarsimp
   \<comment> \<open>end of the proofs of the useful facts\<close>

   apply (intro conjI)

         \<comment> \<open>refills_sum\<close>
         apply (cases "sc_refills sc", fast, case_tac list, fastforce, simp add: add_ac)

       \<comment> \<open>ordered_disjoint\<close>
        apply (rule schedule_used_ordered_disjoint)
          apply (rule_tac left="[\<lparr>r_time = r_time (hd (tl (sc_refills sc))) - (r_amount (refill_hd sc) - usage),
                                  r_amount = r_amount (hd (tl (sc_refills sc))) + (r_amount (refill_hd sc) - usage)\<rparr>]"
                      and right="tl (tl (sc_refills sc))"
                       in ordered_disjoint_append)
             apply (simp add: ordered_disjoint_def)
            apply clarsimp
            apply (erule_tac list = "sc_refills sc" and new_list="tl (tl (sc_refills sc))"
                                                     in ordered_disjoint_sublist)
            using sublist_order.order.trans apply blast
           apply (intro impI)
           apply (clarsimp simp: ordered_disjoint_def)
           apply (drule_tac x=1 in spec)
           apply (elim impE)
            using tail_nonempty_length apply force
           apply (drule_tac x=1 in spec)
           apply (elim impE)
            using tail_nonempty_length apply force
           apply (cases "sc_refills sc", fast, case_tac list, force, simp add: hd_conv_nth)
         apply simp
         apply clarsimp
         apply (case_tac "m=0")
          apply clarsimp
         apply clarsimp
         apply (drule_tac x="m + Suc 0" in spec)
         apply (elim impE)
          apply linarith
         apply (cases "sc_refills sc", force, case_tac list, force, force)
        apply (intro conjI impI)
        apply (clarsimp split: if_splits)
        apply (intro conjI impI)
         apply (simp add: window_def)
         apply (subgoal_tac "refill_tl sc = hd (tl (sc_refills sc))")
          apply force
         apply (metis hd_conv_nth last_conv_nth last_tl length_tl list.size(3))
        apply (simp add: window_def)
        apply (subgoal_tac "refill_tl sc = last (tl (tl (sc_refills sc)))")
         apply argo
        apply (simp add: last_tl)

      \<comment> \<open>no_overflow\<close>
       apply (rule schedule_used_no_overflow)
          apply (rule no_overflow_append[where left="[\<lparr>r_time = r_time (hd (tl (sc_refills sc))) - (r_amount (refill_hd sc) - usage),
                                                       r_amount = r_amount (hd (tl (sc_refills sc))) + (r_amount (refill_hd sc) - usage)\<rparr>]"
                                           and right="tl (tl (sc_refills sc))"])
            apply (simp add: no_overflow_def)
            apply (drule_tac x=1 in spec)
            apply (elim impE)
             using tail_nonempty_length apply force
            apply (case_tac "sc_refills sc", fast, fastforce simp: hd_conv_nth)
           apply (erule no_overflow_sublist[where list="sc_refills sc"])
           using sublist_order.dual_order.trans apply blast
          apply force
         apply (simp add: no_overflow_def)
        apply (clarsimp split: if_split)
        apply (case_tac "m=0")
         apply clarsimp
        apply clarsimp
        apply (drule_tac x="m + Suc 0" in spec)
        apply (elim impE)
         apply linarith
        apply (cases "sc_refills sc", force, case_tac list, force, force)
       apply (intro conjI impI)
       apply (clarsimp split: if_splits)
       apply (intro conjI impI)
        apply (simp add: window_def)
        apply (subgoal_tac "refill_tl sc = hd (tl (sc_refills sc))")
         apply force
        apply (metis hd_conv_nth last_conv_nth last_tl length_tl list.size(3))
       apply (simp add: window_def)
       apply (subgoal_tac "refill_tl sc = last (tl (tl (sc_refills sc)))")
        apply argo
       apply (simp add: last_tl)

     \<comment> \<open>MIN_BUDGET\<close>
       apply (rule schedule_used_MIN_BUDGET)
        apply clarsimp
        apply (cases "sc_refills sc", blast, case_tac list, fastforce
               , simp add: word_le_nat_alt refills_sum_def)
       apply clarsimp
       apply (cases "sc_refills sc")
        apply fast
       apply (case_tac list)
        apply force
       apply (rule_tac y="unat (sc_budget sc)" in order_trans)
        apply fastforce
       apply (simp add: word_le_nat_alt)
      apply clarsimp
      apply (case_tac "na=0")
       apply clarsimp
      apply (drule_tac x="na + Suc 0" in spec)
      apply (elim impE)
       apply linarith
      apply (cases "sc_refills sc", force, case_tac list, force, force)

    \<comment> \<open>period_window\<close>
     apply (simp add: schedule_used.simps)
     apply (clarsimp simp: Let_def split: if_splits)
     apply (intro conjI impI)

          \<comment> \<open>list of length two, and first branch of schedule_used\<close>
          apply (frule order.strict_implies_order)
          apply (subgoal_tac "unat (r_time (refill_hd sc)) + 2 * unat (sc_period sc)
                              \<le> unat max_word")
           apply (frule_tac head_time="r_time (refill_hd sc)"
                        and period="sc_period sc"
                        and larger="MIN_BUDGET"
                        and smaller="usage"
                         in refill_word_proof_helper)
             using MIN_BUDGET_le_MIN_SC_BUDGET apply simp
            apply fastforce
           apply (simp add: window_def)
           apply (subgoal_tac "unat MIN_BUDGET \<le> unat (sc_period sc)")
            apply clarsimp
            apply (rule nat_move_sub_le)
            apply (simp add: ordered_disjoint_def)
            apply (drule_tac x=0 in spec)
            apply (elim impE)
            using tail_nonempty_length apply force
            apply (metis hd_conv_nth Nitpick.size_list_simp(2) nth_tl numeral_1_eq_Suc_0
                         zero_less_numeral)
           using word_le_nat_alt MIN_BUDGET_le_MIN_SC_BUDGET apply fastforce
          apply linarith

       \<comment> \<open>list of length two, and second branch of schedule used\<close>
         apply (subst period_window_single)
          apply simp
         apply clarsimp
         apply (rule order_trans[where y="unat (sc_budget sc)"])
          apply (cases "sc_refills sc", fast, case_tac list, fastforce)
          apply (simp add: add_ac)
         apply (simp add: word_le_nat_alt)

      \<comment> \<open>list of length two, and last branch of schedule_used\<close>
        apply (simp add: window_def)
        apply (rule nat_move_sub_le)
        apply (simp add: ordered_disjoint_def)
        apply (drule_tac x=0 in spec)
        apply (elim impE)
         using tail_nonempty_length apply force
        apply (metis Nitpick.size_list_simp(2) hd_conv_nth nth_tl numeral_1_eq_Suc_0
                     zero_less_numeral)

       \<comment> \<open>list of length greater than two, and first branch of schedule_used\<close>
       apply (simp add: window_def)
       apply (frule order.strict_implies_order)
       apply (subgoal_tac "unat (r_time (refill_hd sc)) + 2 * unat (sc_period sc) \<le> unat max_word")
        apply (frule_tac head_time="r_time (refill_hd sc)"
                     and period="sc_period sc"
                     and larger="MIN_BUDGET"
                     and smaller="usage"
                      in refill_word_proof_helper)
          using MIN_BUDGET_le_MIN_SC_BUDGET apply simp
         apply fastforce
        apply (simp add: window_def)
        apply (subgoal_tac "unat MIN_BUDGET \<le> unat (sc_period sc)")
         apply clarsimp
         apply (rule nat_move_sub_le)
         apply (simp add: ordered_disjoint_def)
         apply (drule_tac x=0 in spec)
         apply (elim impE)
          using tail_nonempty_length apply force
         apply (metis hd_conv_nth length_greater_0_conv nth_tl)
        using word_le_nat_alt MIN_BUDGET_le_MIN_SC_BUDGET apply fastforce
       apply linarith

     \<comment> \<open>list of length greater than two, and second branch of schedule_used\<close>
      apply (simp add: window_def)
      apply (subgoal_tac "unat (r_time (refill_hd sc) + sc_period sc - r_amount (last (tl (tl (sc_refills sc)))))
                          = unat (r_time (refill_hd sc)) + unat (sc_period sc)
                            - unat (r_amount (last (tl (tl (sc_refills sc)))))")
       apply (subgoal_tac "unat (r_amount (last (tl (tl (sc_refills sc)))) + usage)
                           = unat (r_amount (last (tl (tl (sc_refills sc))))) + unat usage")
        apply (subgoal_tac "unat (r_amount (last (tl (tl (sc_refills sc)))))
                            \<le> unat (sc_period sc)")
         apply clarsimp
         apply (rule nat_move_sub_le)
         apply (simp add: ordered_disjoint_def)
         apply (drule_tac x=0 in spec)
         apply (elim impE)
          using tail_nonempty_length apply force
         apply (metis hd_conv_nth list.exhaust_sel nth_Cons_Suc)
        apply (rule order_trans[where y="unat (sc_budget sc)"])
         apply (rule_tac t="unat (sc_budget sc)"
                     and s="sum_list (map unat (map r_amount (sc_refills sc)))"
                      in subst)
          apply clarsimp
         apply (rule member_le_sum_list)
         apply (simp add: last_tl)
        using word_le_nat_alt apply fast
       apply (rule unat_add_lem')
       apply (rule_tac y="unat (r_amount (last (tl (tl (sc_refills sc)))))
                          + unat (r_amount (refill_hd sc))"
                    in le_less_trans)
        apply clarsimp
       apply (rule_tac y="unat (sc_budget sc)" in le_less_trans)
        apply (simp add: add_ac)
        apply (cases "sc_refills sc", fast, case_tac list, force, clarsimp)
        apply (subgoal_tac "unat (r_amount (last lista))
                            \<le> sum_list (map unat (map r_amount lista))")
         apply linarith
        apply (rule member_le_sum_list)
        apply (simp add: last_tl)
       using max_word_def apply force
      apply (subgoal_tac "unat (r_time (refill_hd sc) + sc_period sc - r_amount (last (tl (tl (sc_refills sc)))))
                          = unat (r_time (refill_hd sc) + sc_period sc)
                            - unat (r_amount (last (tl (tl (sc_refills sc)))))")
       apply clarsimp
      apply (subgoal_tac "r_amount (last (tl (tl (sc_refills sc))))
                          \<le> r_time (refill_hd sc) + sc_period sc")
       apply (simp add: unat_sub)
      apply (simp add: word_le_nat_alt)
      apply (rule_tac y="unat (sc_budget sc)" in order_trans)
       apply (erule_tac t="unat (sc_budget sc)"
                    and s="sum_list (map unat (map r_amount (sc_refills sc)))"
                     in subst)
       apply (rule member_le_sum_list, simp add: last_tl)
      apply linarith

     \<comment> \<open>list of length greater than two, and last branch of schedule_used\<close>
     apply (simp add: window_def)
     apply (rule nat_move_sub_le)
     apply (simp add: ordered_disjoint_def)
     apply (drule_tac x=0 in spec)
     apply (elim impE)
      apply (metis gt_or_eq_0 list.exhaust_sel list.size(4) list_exhaust_size_eq0 nat_simps(1))
     apply (metis hd_conv_nth list.exhaust_sel nth_Cons_Suc)

    \<comment> \<open>length\<close>
    apply (metis schedule_used_non_nil Nitpick.size_list_simp(2) not_numeral_le_zero
                 numeral_1_eq_Suc_0)
   apply (rule_tac y="Suc (length (\<lparr>r_time = r_time (hd (tl (sc_refills sc))) - (r_amount (refill_hd sc) - usage),
                                    r_amount = r_amount (hd (tl (sc_refills sc))) + (r_amount (refill_hd sc) - usage)\<rparr>
                      # tl (tl (sc_refills sc))))"
                in order_trans)
    using schedule_used_length_max apply fast
   apply (subgoal_tac "length (\<lparr>r_time = r_time (hd (tl (sc_refills sc))) - (r_amount (refill_hd sc) - usage),
                                r_amount = r_amount (hd (tl (sc_refills sc))) + (r_amount (refill_hd sc) - usage)\<rparr>
                              # tl (tl (sc_refills sc)))
                       = length (sc_refills sc) - Suc 0")
    apply clarsimp
   apply (metis Nitpick.size_list_simp(2) append_len2 length_Cons length_append_singleton list.size(3))


  \<comment> \<open>last branch of refill_budget_check - remnant is at least MIN_BUDGET.
      We leave the remnant in place, and do schedule_used of usage\<close>
  apply (clarsimp simp: valid_refills_def sc_valid_refills_def obj_at_def set_object_def
                        get_object_def
                 split: if_splits)

  \<comment> \<open>we introduce some useful facts\<close>
  apply (frule_tac refills="sc_refills sc" in unat_sum_list_equals_budget
         ; (simp add: refills_sum_def)?)
    using MIN_BUDGET_pos word_le_nat_alt unat_gt_0 apply fastforce
   using MIN_BUDGET_le_MIN_SC_BUDGET apply force
  apply (subgoal_tac "unat (r_time (refill_hd sc) + usage)
                      = unat (r_time (refill_hd sc)) + unat usage")
   prefer 2
   apply (rule unat_add_lem', simp add: max_word_def)
  apply (subgoal_tac "unat (r_amount (refill_hd sc) - usage)
                      = unat (r_amount (refill_hd sc)) - unat usage")
   prefer 2
   using unat_sub word_not_le apply blast
  apply (subgoal_tac "unat (r_time (refill_hd sc) + sc_period sc)
                      = unat (r_time (refill_hd sc)) + unat (sc_period sc)")
   prefer 2
   apply (rule unat_add_lem', simp add: max_word_def)
  apply (subgoal_tac "unat (r_amount (refill_hd sc)) \<le> unat (sc_period sc)")
   prefer 2
   apply (rule_tac y="unat (sc_budget sc)" in order_trans)
    apply (erule_tac s="sum_list (map unat (map r_amount (sc_refills sc)))"
                 and t="unat (sc_budget sc)"
                  in subst)
    apply (rule_tac member_le_sum_list)
    apply force
   apply (simp add: word_le_nat_alt)
  apply (frule_tac y=usage and x="r_amount (refill_hd sc)" in leI)
  \<comment> \<open>end of the proof of useful facts\<close>

  apply (intro conjI)

       \<comment> \<open>refills_sum\<close>
        apply (cases "sc_refills sc", simp, simp)

       \<comment> \<open>ordered_disjoint\<close>
       apply (rule schedule_used_ordered_disjoint)
         apply (rule_tac left="[\<lparr>r_time = r_time (refill_hd sc) + usage,
                                 r_amount = r_amount (refill_hd sc) - usage\<rparr>]"
                     and right="tl (sc_refills sc)"
                      in ordered_disjoint_append)
            apply (simp add: ordered_disjoint_def)
           apply (simp add: ordered_disjoint_sublist)
          apply (clarsimp simp: unat_sub word_le_nat_alt ordered_disjoint_def)
          apply (drule_tac x=0 in spec)
          apply (elim impE)
           apply (metis Nitpick.size_list_simp(2) gt_or_eq_0 length_0_conv nat_simps(2)
                        semiring_norm(164) semiring_norm(50))
          apply (simp add: hd_conv_nth)
          apply (subgoal_tac "tl (sc_refills sc) ! 0 = sc_refills sc ! Suc 0")
           apply argo
          apply (meson length_greater_0_conv nth_tl)
         apply force
        apply clarsimp
        apply (case_tac "m=0")
         apply clarsimp
         apply force
        apply clarsimp
        apply (drule_tac x=m in spec)
        apply clarsimp
        apply (cases "sc_refills sc", fast, case_tac list, simp, force)
       apply (clarsimp split: if_splits)
       apply (intro conjI impI)
        apply (simp add: unat_sub word_le_nat_alt)
       apply (simp add: window_def)
       apply (subgoal_tac "refill_tl sc = last (tl (sc_refills sc))")
        apply (subgoal_tac "unat (r_time (refill_hd sc) + sc_period sc)
                            = unat (r_time (refill_hd sc)) + unat (sc_period sc)")
         apply clarsimp
        apply (rule unat_add_lem', simp add: max_word_def)
       apply (simp add: last_tl)

      \<comment> \<open>no_overflow\<close>
      apply (rule schedule_used_no_overflow)
         apply (rule_tac left="[\<lparr>r_time = r_time (refill_hd sc) + usage,
                                 r_amount = r_amount (refill_hd sc) - usage\<rparr>]"
                     and right="tl (sc_refills sc)"
                      in no_overflow_append)
           apply (simp add: no_overflow_def word_le_nat_alt)
          apply (drule_tac x=0 in spec)
          apply (metis hd_Cons_tl no_overflow_tail)
         apply fastforce
        apply (simp add: no_overflow_def)
       apply clarsimp
       apply (case_tac "m=0")
        apply simp
       apply clarsimp
       apply (drule_tac x=m in spec)
       apply (elim impE)
        apply blast
       apply (subgoal_tac "tl (sc_refills sc) ! (m - Suc 0) = sc_refills sc ! m")
        prefer 2
        apply (metis Nitpick.size_list_simp(2) length_ineq_not_Nil(1) less_handy_casesE
                     less_le_nonzero_helper minus_eq nat_Suc_less_le_imp nat_simps(2) nth_tl
                     semiring_norm(164))
       apply argo
      apply (clarsimp split: if_splits)
      apply (intro conjI impI)
       apply (simp add: word_le_nat_alt)
      apply (simp add: window_def)
      apply (subgoal_tac "refill_tl sc = last (tl (sc_refills sc))")
       apply argo
      apply (simp add: last_tl)

     \<comment> \<open>MIN_BUDGET\<close>
     apply (subgoal_tac "sum_list (map unat (map r_amount ((\<lparr>r_time = r_time (refill_hd sc) + usage,
                                                             r_amount = r_amount (refill_hd sc) - usage\<rparr>
                                                           # tl (sc_refills sc))
                                                           @ [\<lparr>r_time = r_time (refill_hd sc) + sc_period sc,
                                                               r_amount = usage\<rparr>])))
                         = unat (sc_budget sc)")
      prefer 2
      apply (cases "sc_refills sc")
       apply blast
      apply (case_tac list)
       apply (simp add: word_le_nat_alt refills_sum_def)
      apply (simp add: le_def unat_sub unat_arith_simps(2))
     apply (rule schedule_used_MIN_BUDGET)
       using word_le_nat_alt apply metis
      apply clarsimp
      using word_le_nat_alt apply fast
     apply clarsimp
     apply (case_tac "na=0")
      apply force
     apply (drule_tac x=na in spec)
     apply clarsimp
     apply (cases "sc_refills sc", fast, case_tac list, simp, force)

    \<comment> \<open>period window\<close>
    \<comment> \<open>first branch of schedule_used\<close>
    apply (case_tac "usage < MIN_BUDGET \<and> \<not>(length (sc_refills sc) = sc_refill_max sc)
                     \<and> 2 * MIN_BUDGET \<le> r_amount (last (tl (sc_refills sc))) + usage")

     \<comment> \<open>we introduce a useful fact\<close>
     apply (subgoal_tac "unat (r_time (refill_hd sc)) + 2 * unat (sc_period sc)
                         \<le> unat (max_word :: time)")
      prefer 2
      apply linarith
     apply (frule_tac head_time="r_time (refill_hd sc)"
                  and period="sc_period sc"
                  and larger="MIN_BUDGET"
                  and smaller="usage"
                   in refill_word_proof_helper)
       using MIN_BUDGET_le_MIN_SC_BUDGET apply force
      apply fastforce
     \<comment> \<open>end of the proof of the useful fact\<close>

     apply (clarsimp simp: schedule_used.simps Let_def split: if_splits)
     apply (intro conjI impI)

       \<comment> \<open>first of three branches (for the first branch of schedule_used)\<close>
       apply (simp add: window_def)
       apply (subgoal_tac "MIN_BUDGET \<le> sc_period sc")
        using word_le_nat_alt apply force
       using MIN_BUDGET_le_MIN_SC_BUDGET apply fastforce

      \<comment> \<open>second of the three  branches ((for the first branch of schedule_used)\<close>
      apply (subst period_window_single[where a="\<lparr>r_time = r_time (refill_hd sc) + sc_period sc - (r_amount (refill_hd sc) - usage),
                                                  r_amount = r_amount (refill_hd sc)\<rparr>"])
       apply simp
      apply clarsimp

     \<comment> \<open>last of the three branches (for the first branch of schedule_used)\<close>
     apply (simp add: window_def)
     apply (subgoal_tac "MIN_BUDGET \<le> sc_period sc")
      using word_le_nat_alt apply force
     using MIN_BUDGET_le_MIN_SC_BUDGET apply fastforce

    \<comment> \<open>second branch of schedule_used\<close>
    apply (case_tac "usage< MIN_BUDGET \<or> (length (sc_refills sc) = sc_refill_max sc)")
     apply (clarsimp simp: schedule_used.simps Let_def split: if_splits)
     apply (intro conjI impI; (simp add: window_def)?)

        \<comment> \<open>first of two branches (for the second branch of schedule_used)\<close>
        apply clarsimp
        apply (subgoal_tac "unat (r_time (refill_hd sc)) + 2 * unat (sc_period sc)
                            \<le> unat (max_word :: time)")
         prefer 2
         apply linarith
        apply (frule_tac head_time="r_time (refill_hd sc)"
                     and period="sc_period sc"
                     and larger="MIN_BUDGET"
                     and smaller="usage"
                      in refill_word_proof_helper)
          using MIN_BUDGET_le_MIN_SC_BUDGET apply force
         apply fastforce
        apply (simp add: window_def)
        apply (subgoal_tac "unat MIN_BUDGET \<le> unat (sc_period sc)")
         apply linarith
        using MIN_BUDGET_le_MIN_SC_BUDGET word_le_nat_alt apply fastforce

     \<comment> \<open>last of the two branches (for the second branch of schedule_used)\<close>
     \<comment> \<open>a useful fact\<close>
     apply (subgoal_tac "unat (r_amount (last (tl (sc_refills sc)))) \<le> unat (sc_period sc)")
      prefer 2
      apply (rule_tac y="unat (sc_budget sc)" in order_trans)
       apply (erule_tac s="sum_list (map unat (map r_amount (sc_refills sc)))"
                    and t="unat (sc_budget sc)"
                     in subst)
       apply (rule member_le_sum_list)
       apply (simp add: last_tl)
      apply (simp add: word_le_nat_alt)
     \<comment> \<open>end of the proof of the useful fact\<close>

     apply (subgoal_tac "unat (r_time (refill_hd sc) + sc_period sc - r_amount (last (tl (sc_refills sc))))
                         = unat (r_time (refill_hd sc)) + unat (sc_period sc)
                           - unat (r_amount (last (tl (sc_refills sc))))")
      apply (subgoal_tac "unat (r_amount (last (tl (sc_refills sc))) + usage)
                          = unat (r_amount (last (tl (sc_refills sc)))) + unat usage")
       apply (subgoal_tac "unat (r_amount (last (tl (sc_refills sc)))) \<le> unat (sc_period sc)")
        apply clarsimp
       apply blast
      apply (rule unat_add_lem', simp add: max_word_def)
     apply (subgoal_tac "unat (r_time (refill_hd sc) + sc_period sc - r_amount (last (tl (sc_refills sc))))
                         = unat (r_time (refill_hd sc) + sc_period sc)
                           - unat (r_amount (last (tl (sc_refills sc))))")
      apply clarsimp
     apply (subgoal_tac "r_amount (last (tl (sc_refills sc)))
                         \<le> r_time (refill_hd sc) + sc_period sc")
      apply (simp add: unat_sub)
     apply (simp add: word_le_nat_alt)

    \<comment> \<open>last branch of schedule_used\<close>
    apply (simp add: window_def schedule_used.simps)

   \<comment> \<open>length\<close>
   apply (metis schedule_used_non_nil Nitpick.size_list_simp(2) not_numeral_le_zero
                numeral_1_eq_Suc_0)
   apply (case_tac "length (sc_refills sc) < sc_refill_max sc")
   apply (subgoal_tac "length (\<lparr>r_time = r_time (refill_hd sc) + usage,
                                r_amount = r_amount (refill_hd sc) - usage\<rparr>
                               # tl (sc_refills sc))
                       = length (sc_refills sc)")
    apply (metis (no_types, hide_lams) schedule_used_length_max le_def le_trans nat_Suc_less_le_imp)
   apply clarsimp
  apply clarsimp
  apply (subgoal_tac "length (\<lparr>r_time = r_time (refill_hd sc) + usage,
                               r_amount = r_amount (refill_hd sc) - usage\<rparr>
                              # tl (sc_refills sc))
                      = length (sc_refills sc)")
   using schedule_used_length_full apply force
  apply clarsimp
  apply (metis diff_Suc_Suc list_exhaust_size_eq0 minus_nat.diff_0 old.nat.exhaust)
  done

lemma valid_refills_sc_update:
  "(valid_refills p (s\<lparr>kheap := kheap s(p \<mapsto> SchedContext sc n)\<rparr>))
       = sc_valid_refills sc"
  by (clarsimp simp: valid_refills_def obj_at_def sc_valid_refills_def)

definition
  sc_at_period :: "(time \<Rightarrow> bool) \<Rightarrow> obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "sc_at_period P  = obj_at (\<lambda>ko. \<exists>sc n. ko = SchedContext sc n \<and> P (sc_period sc))"

definition
  round_robin :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "round_robin ptr s \<equiv> \<exists>ko sc n. kheap s ptr = Some ko \<and> ko = SchedContext sc n
                         \<and> sc_budget sc = sc_period sc"

crunch obj_at[wp]: refill_full "obj_at P p"

lemma refill_full_valid_refills[wp]:
  "\<lbrace>valid_refills scptr\<rbrace> refill_full p \<lbrace>\<lambda>_. valid_refills scptr\<rbrace>"
  by (wpsimp simp: refill_full_def)

lemma update_sc_consumed_valid_refills[wp]:
  "\<lbrace>valid_refills p and sc_at ptr\<rbrace>
   update_sched_context ptr (\<lambda>sc. sc_consumed_update f sc)
      \<lbrace>\<lambda>_. valid_refills p\<rbrace>"
  by (wpsimp simp: valid_refills_def sc_valid_refills_def window_def
                      update_sched_context_def obj_at_def
                  wp: set_object_wp get_object_wp )

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

lemma non_empty_tail_length:
  "tl list \<noteq> [] \<Longrightarrow> Suc 0 \<le> length list"
  using le0 list.sel(2) not_less_eq_eq by blast

lemma valid_refills_sc_consumed_update[iff]:
    "valid_refills p (s\<lparr>kheap := kheap s(p' \<mapsto> SchedContext (sc\<lparr>sc_consumed:=x\<rparr>) n)\<rparr>)
         = valid_refills p (s\<lparr>kheap := kheap s(p' \<mapsto> SchedContext sc n)\<rparr>)"
  by (clarsimp simp: valid_refills_def sc_valid_refills_def obj_at_def window_def)

lemma valid_refills_domain_time_update[simp]:
  "valid_refills sc (domain_time_update f s) = valid_refills sc s"
  by (simp add: valid_refills_def)

crunches commit_domain_time
  for valid_refills[wp]: "valid_refills sc"

lemma refill_budget_check_round_robin_valid_refills[wp]:
   "\<lbrace>(\<lambda>s. kheap s p = Some (SchedContext sc n)
          \<and> unat (cur_time s) + 2 * unat (sc_budget sc) \<le> unat (max_word::time)
          \<and> unat usage + unat (sc_budget sc) \<le> unat (max_word::time)
          \<and> MIN_SC_BUDGET \<le> sc_budget sc
          \<and> MIN_REFILLS \<le> sc_refill_max sc)
     and valid_refills p\<rbrace>
    refill_budget_check_round_robin usage
    \<lbrace>\<lambda>_. valid_refills p\<rbrace>"
  supply if_split[split del]
  apply (clarsimp simp: refill_budget_check_round_robin_def is_round_robin_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ assert_sp])

  apply (case_tac "usage < MIN_BUDGET \<and> length (sc_refills sca) = Suc 0")
  apply (wpsimp simp: set_refills_def update_sched_context_def set_object_def get_object_def
                      valid_refills_def sc_valid_refills_def obj_at_def)

   \<comment> \<open>we introduce some useful facts\<close>
   apply (frule_tac unat_sum_list_equals_budget
          ; (simp add: refills_sum_def)?)
     using MIN_BUDGET_pos word_le_nat_alt unat_gt_0 apply fastforce
    using MIN_BUDGET_le_MIN_SC_BUDGET apply force

   apply (subgoal_tac "unat (r_amount (refill_hd sc)) \<le> unat (sc_budget sc)")
    prefer 2
    apply (erule_tac s="sum_list (map (unat \<circ> r_amount) (sc_refills sc))"
                     and t="unat (sc_budget sc)"
           in subst)
    apply (rule member_le_sum_list, simp)

   apply (subgoal_tac "MIN_BUDGET \<le> r_amount (refill_hd sc)")
    prefer 2
    apply (simp add: hd_conv_nth)

   apply (subgoal_tac "unat (cur_time s + r_amount (refill_hd sc) - MIN_BUDGET)
                       = unat (cur_time s) + unat (r_amount (refill_hd sc)) - unat MIN_BUDGET")
    prefer 2
    apply (subgoal_tac "unat (cur_time s + r_amount (refill_hd sc) - MIN_BUDGET)
                        = unat (cur_time s) + unat (r_amount (refill_hd sc) - MIN_BUDGET)")
     apply clarsimp
     apply (subgoal_tac "unat (cur_time s) + unat (r_amount (refill_hd sc)) - unat MIN_BUDGET
                         = unat (cur_time s) + (unat (r_amount (refill_hd sc)) - unat MIN_BUDGET)")
      prefer 2
      apply (simp add: unat_arith_simps(1))
     apply (simp add: unat_sub)
    apply (subgoal_tac "cur_time s + r_amount (refill_hd sc) - MIN_BUDGET
                        = cur_time s + (r_amount (refill_hd sc) - MIN_BUDGET)")
     prefer 2
     apply fastforce
    apply (erule_tac s="cur_time s + (r_amount (refill_hd sc) - MIN_BUDGET)"
                 and t="cur_time s + r_amount (refill_hd sc) - MIN_BUDGET"
                  in ssubst)
    apply (rule unat_add_lem', simp add: unat_sub max_word_def)
   \<comment> \<open>end of the proofs of the useful facts\<close>

   apply (clarsimp split: if_splits)
   apply (intro conjI impI
          ; (clarsimp simp: ordered_disjoint_def no_overflow_def window_def)?)
         apply (cases "sc_refills sc", blast, fastforce)
        apply (simp add: unat_arith_simps(1) unat_sub)
       apply (case_tac "na=0")
        apply (simp add: unat_sub)
       apply clarsimp
       apply (subgoal_tac "unat (cur_time s) + unat (r_amount (refill_hd sc)) - unat MIN_BUDGET + unat MIN_BUDGET
                           = unat (cur_time s) + unat (r_amount (refill_hd sc))")
        prefer 2
        apply (metis (no_types, hide_lams) eq_diff_iff le_trans nat_iffs(2) nat_simps(1)
                                           word_le_nat_alt)
       apply linarith
      apply (case_tac "na=0")
       apply (simp add: word_le_nat_alt unat_sub)
       apply (rule nat_move_sub_le)
       using unat_MIN_BUDGET_MIN_SC_BUDGET apply (simp add: MIN_SC_BUDGET_def)
      apply clarsimp
     apply (subgoal_tac "unat (cur_time s) + unat (r_amount (refill_hd sc)) - unat MIN_BUDGET + unat MIN_BUDGET
                         = unat (cur_time s) + unat (r_amount (refill_hd sc))")
      prefer 2
      apply (metis (no_types, hide_lams) eq_diff_iff le_trans nat_iffs(2) nat_simps(1) word_le_nat_alt)
     apply clarsimp
    apply (simp add: MIN_REFILLS_def)
   using MIN_BUDGET_le_MIN_SC_BUDGET apply force

  \<comment> \<open>\<not> (usage < MIN_BUDGET \<and> length (sc_refills sca) = Suc 0)\<close>
  \<comment> \<open>outer else branch\<close>
  apply (case_tac "\<not>(usage + MIN_BUDGET \<le> r_amount (refill_hd sc))")
   apply (wpsimp simp: set_refills_def update_sched_context_def set_object_def get_object_def
                       valid_refills_def sc_valid_refills_def obj_at_def
                split: if_splits)
   apply (intro conjI impI
          ; (clarsimp simp: ordered_disjoint_def no_overflow_def window_def)?)
    using MIN_BUDGET_le_MIN_SC_BUDGET apply simp
   apply (simp add: MIN_REFILLS_def)

  \<comment> \<open>final branch\<close>
  apply (wpsimp simp: set_refills_def update_sched_context_def set_object_def get_object_def
                      valid_refills_def sc_valid_refills_def obj_at_def
               split: if_splits)

  \<comment> \<open>some useful facts\<close>
  apply (frule unat_sum_list_equals_budget; (simp add: refills_sum_def)?)
    using MIN_BUDGET_pos word_le_nat_alt unat_gt_0 apply fastforce
   using MIN_BUDGET_le_MIN_SC_BUDGET apply force

  apply (subgoal_tac "unat (r_amount (refill_hd sc)) \<le> unat (sc_budget sc)")
   prefer 2
   apply (cases "sc_refills sc", fast, case_tac list, force, force)

  apply (subgoal_tac "length (sc_refills sc) \<noteq> Suc 0
                      \<longrightarrow> unat (r_amount (hd (tl (sc_refills sc)))) \<le> unat (sc_budget sc)")
   prefer 2
   apply (cases "sc_refills sc", fast, case_tac list, simp, force)

  apply (subgoal_tac "MIN_BUDGET \<le> sc_budget sc")
   prefer 2
   using MIN_BUDGET_le_MIN_SC_BUDGET apply force

  apply (subgoal_tac "usage \<le> r_amount (refill_hd sc)")
   prefer 2
   apply (simp add: word_le_nat_alt)
   apply (subgoal_tac "unat (usage + MIN_BUDGET) = unat usage + unat MIN_BUDGET")
    apply clarsimp
   apply (rule unat_add_lem', simp add: max_word_def)

  apply (subgoal_tac "unat (cur_time s + r_amount (refill_hd sc) - usage)
                      = unat (cur_time s) + unat (r_amount (refill_hd sc)) - unat usage")
   prefer 2
   apply (subgoal_tac "unat (cur_time s + r_amount (refill_hd sc) - usage)
                       = unat (cur_time s) + unat (r_amount (refill_hd sc) - usage)")
    apply clarsimp
    apply (simp add: unat_sub word_le_nat_alt)
   apply (subgoal_tac "cur_time s + r_amount (refill_hd sc) - usage
                       = cur_time s + (r_amount (refill_hd sc) - usage)")
    prefer 2
    apply fastforce
   apply (erule_tac s="cur_time s + (r_amount (refill_hd sc) - usage)"
                and t="cur_time s + r_amount (refill_hd sc) - usage"
                 in ssubst)
   apply (rule unat_add_lem', simp add: unat_sub max_word_def)

  apply (subgoal_tac "unat (usage + MIN_BUDGET) = unat usage + unat MIN_BUDGET")
   prefer 2
   apply (rule unat_add_lem', simp add: max_word_def word_le_nat_alt)

  apply (subgoal_tac "length (sc_refills sc) \<noteq> Suc 0
                      \<longrightarrow> unat (r_amount (hd (tl (sc_refills sc))) + usage)
                          = unat (r_amount (hd (tl (sc_refills sc)))) + unat usage")
   prefer 2
   apply (intro impI)
   apply (rule unat_add_lem', simp add: max_word_def)

  apply (subgoal_tac "length (sc_refills sc) \<noteq> Suc 0
                      \<longrightarrow> unat (r_amount (hd (sc_refills sc))) + unat (r_amount (hd (tl (sc_refills sc))))
                           \<le> unat (sc_budget sc)")
   prefer 2
   apply (intro impI)
   apply (cases "sc_refills sc", simp, case_tac list, simp, force)
  \<comment> \<open>end of the proof of the useful facts\<close>

  apply (intro conjI impI
         ; (clarsimp simp: ordered_disjoint_def no_overflow_def window_def)?)
            apply (cases "sc_refills sc", blast, fastforce)
           apply (simp add: unat_arith_simps(1) unat_sub)
          apply (case_tac "na=0")
           apply (simp add: unat_sub)
          apply clarsimp
          apply linarith
         apply (case_tac "na=0")
          apply (simp add: word_le_nat_alt unat_sub)
         apply simp
        apply (subgoal_tac "unat (cur_time s) + unat (r_amount (refill_hd sc)) - unat usage + unat usage
                            = unat (cur_time s) + unat (r_amount (refill_hd sc))")
         prefer 2
         apply (meson eq_diff_iff le_trans nat_iffs(2) nat_simps(1) unat_arith_simps(1))
        apply linarith
       apply (simp add: MIN_REFILLS_def)
      apply (cases "sc_refills sc", simp, case_tac list, fastforce, fastforce)
     apply (simp add: unat_sub word_le_nat_alt)
    apply (case_tac "na=0")
     apply (simp add: unat_sub)
    apply (simp add: word_le_nat_alt)
   apply (case_tac "na=0")
    apply (simp add: word_le_nat_alt unat_sub)
   apply (simp add: word_le_nat_alt)
   apply (drule_tac x=1 and P="\<lambda>n. n < 2 \<longrightarrow> unat MIN_BUDGET \<le> unat (r_amount (sc_refills sc ! n))"
                 in spec)
   apply clarsimp
   apply (metis Nitpick.size_list_simp(2) hd_conv_nth
                list.exhaust_sel n_not_Suc_n nth_Cons_Suc numeral_2_eq_2 unat_arith_simps(1)
                unat_plus_simple word_le_plus_either)
  apply (simp add: word_le_nat_alt)
  done

lemma commit_time_valid_refills[wp]:
  "\<lbrace>(\<lambda>s. kheap s ptr = Some (SchedContext sc n)
          \<and> unat (r_time (refill_hd sc)) + 2 * unat (sc_period sc) + unat (consumed_time s)
                     \<le> unat (max_word :: time)
          \<and> unat (cur_time s) + 2 * unat (sc_budget sc) \<le> unat (max_word :: time)
          \<and> MIN_REFILLS \<le> sc_refill_max sc
          \<and> MIN_SC_BUDGET \<le> sc_budget sc \<and> sc_budget sc \<le> sc_period sc) and
    (\<lambda>s. valid_refills ptr s)\<rbrace> commit_time \<lbrace>\<lambda>_ s. valid_refills ptr s\<rbrace>"
  apply (clarsimp simp: commit_time_def is_round_robin_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (clarsimp simp: when_def bind_assoc)
  apply (intro conjI impI)

   \<comment> \<open>0 < consumed and 0 < sc_refill_max\<close>
   apply (simp add: sc_refill_ready_def)
    apply (rule hoare_seq_ext[OF _ gets_sp])
    apply (rule hoare_seq_ext[OF _ assert_sp])
    apply (rule hoare_seq_ext[OF _ assert_sp])
    apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
    apply (clarsimp split: if_split)
    apply (intro conjI impI)

     \<comment> \<open>is_round_robin\<close>
     apply (wpsimp simp: set_object_def sc_valid_refills_def window_def
                     wp: get_object_wp update_sc_consumed_valid_refills
                         update_sched_context_valid_refills_no_budget_update sc_refill_ready_def
                         refill_budget_check_round_robin_valid_refills[where n=n and sc=sc]
                         hoare_drop_imps
               simp_del: fun_upd_apply)
      apply (simp add: word_le_nat_alt)

    \<comment> \<open>\<not>is_round_robin, and remaining cases\<close>
    by (wpsimp simp: set_object_def sc_valid_refills_def window_def
                 wp: get_object_wp update_sc_consumed_valid_refills hoare_drop_imps
                        update_sched_context_valid_refills_no_budget_update sc_refill_ready_def
                        refill_budget_check_valid_refills[where sc=sc and n=n]
           simp_del: fun_upd_apply)+

lemmas valid_refills_kheap_tcb_update'[iff] = valid_refills_kheap_tcb_update[simplified fun_upd_def obj_at_def is_tcb]

lemma thread_set_valid_refills[wp]:
  "\<lbrace>valid_refills scptr\<rbrace> thread_set f tptr \<lbrace>\<lambda>_. valid_refills scptr\<rbrace>"
  apply (wpsimp simp: thread_set_def set_object_def simp_del: fun_upd_apply)
  apply (clarsimp simp: dest!:get_tcb_SomeD)
  done

lemma set_simple_ko_valid_refills[wp]:
  "\<lbrace>valid_refills scptr\<rbrace> set_simple_ko C ptr new \<lbrace>\<lambda>_. valid_refills scptr\<rbrace>"
  apply (wpsimp simp: set_simple_ko_def set_object_def partial_inv_def a_type_def
         wp: get_object_wp simp_del: fun_upd_apply split: kernel_object.splits)
  apply (intro conjI impI; clarsimp simp: valid_refills_def obj_at_def)
  done

lemma sc_replies_update_valid_refills[wp]:
  "\<lbrace>valid_refills scptr\<rbrace>
      set_sc_obj_ref sc_replies_update ptr new \<lbrace>\<lambda>_. valid_refills scptr\<rbrace>"
  apply (wpsimp simp: set_sc_obj_ref_def set_object_def
         wp: get_object_wp update_sched_context_valid_refills_no_budget_update get_sched_context_wp)
  apply (clarsimp simp: valid_refills_def sc_valid_refills_def window_def obj_at_def)
  done

lemma sc_tcb_update_valid_refills[wp]:
  "\<lbrace>valid_refills scptr\<rbrace>
      set_sc_obj_ref sc_tcb_update ptr new \<lbrace>\<lambda>_. valid_refills scptr\<rbrace>"
  apply (wpsimp simp: set_sc_obj_ref_def set_object_def
         wp: get_object_wp update_sched_context_valid_refills_no_budget_update get_sched_context_wp)
  apply (clarsimp simp: valid_refills_def obj_at_def sc_valid_refills_def window_def)
  done

lemma set_tcb_obj_ref_valid_refills[wp]:
  "\<lbrace>valid_refills scptr\<rbrace>
      set_tcb_obj_ref f ptr new \<lbrace>\<lambda>_. valid_refills scptr\<rbrace>"
  apply (wpsimp simp: set_tcb_obj_ref_def set_object_def
         wp: get_object_wp update_sched_context_valid_refills_no_budget_update get_sched_context_wp)
  apply (clarsimp simp: valid_refills_def obj_at_def sc_valid_refills_def dest!: get_tcb_SomeD)
  done

crunch valid_refills[wp]: update_sk_obj_ref, test_reschedule "valid_refills scp"
 (wp: update_sched_context_valid_refills_no_budget_update simp: )

lemma sched_context_donate_valid_refills[wp]:
  "\<lbrace>valid_refills scptr\<rbrace>
      sched_context_donate ptr callee \<lbrace>\<lambda>_. valid_refills scptr\<rbrace>"
  apply (wpsimp simp: sched_context_donate_def set_object_def get_sc_obj_ref_def
         wp: get_object_wp update_sched_context_valid_refills_no_budget_update get_sched_context_wp)
  done

lemma reply_push_valid_refills[wp]:
  "\<lbrace>valid_refills scptr\<rbrace>
      reply_push caller callee reply_ptr can_donate \<lbrace>\<lambda>_. valid_refills scptr\<rbrace>"
  apply (wpsimp simp: reply_push_def set_object_def partial_inv_def a_type_def no_reply_in_ts_def
         wp: get_object_wp update_sched_context_valid_refills_no_budget_update get_sched_context_wp
             hoare_drop_imp hoare_vcg_if_lift2 hoare_vcg_all_lift
         simp_del: fun_upd_apply split: kernel_object.splits)
  done

crunch valid_refills[wp]: reply_unlink_tcb "valid_refills scp"
 (wp: update_sched_context_valid_refills_no_budget_update gts_inv hoare_drop_imps)

locale SchedContextInv_AI =
  fixes state_ext_t :: "'state_ext::state_ext itself"
  fixes some_t :: "'t itself"
  assumes make_arch_fault_msg_valid_refills[wp]:
    "\<And>ft t. make_arch_fault_msg ft t \<lbrace>valid_refills scpt :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes lookup_ipc_buffer_valid_refills[wp]:
    "\<And>t b scptr.
      \<lbrace>valid_refills scptr :: 'state_ext state \<Rightarrow> bool\<rbrace>
        lookup_ipc_buffer b t
      \<lbrace>\<lambda>_. valid_refills scptr\<rbrace>"

lemma as_user_valid_refills[wp]:
  "\<lbrace>valid_refills scptr\<rbrace>
      as_user t f \<lbrace>\<lambda>_. valid_refills scptr\<rbrace>"
  apply (clarsimp simp: as_user_def split_def)
  apply (wpsimp wp: select_f_wp set_object_wp)
  by (clarsimp dest!: get_tcb_SomeD simp: valid_refills_def obj_at_def)

crunch valid_refills[wp]: set_message_info "valid_refills scp"
crunch valid_refills[wp]: set_cdt,set_original,set_extra_badge "valid_refills scp"
  (simp: valid_refills_def wp_del: set_original_wp)


lemma set_cap_valid_refills [wp]:
 "\<lbrace>valid_refills scp\<rbrace> set_cap c p \<lbrace>\<lambda>rv. valid_refills scp\<rbrace>"
  apply (simp add: set_cap_def split_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp)
  apply (fastforce simp: valid_refills_def obj_at_def)
  done

crunch valid_refills[wp]: update_cdt,set_untyped_cap_as_full "valid_refills scp"
  (wp: hoare_drop_imps crunch_wps simp: crunch_simps ignore: set_original)

crunch valid_refills[wp]: cap_insert "valid_refills scp"
  (wp: hoare_drop_imps)

lemma dmo_storeWord_valid_refills[wp]:
  "\<lbrace>valid_refills scp\<rbrace> do_machine_op (storeWord x y) \<lbrace>\<lambda>_. valid_refills scp\<rbrace>"
  by (simp add: do_machine_op_def valid_refills_def |  wp | wpc)+

lemma sched_context_update_consumed_valid_refills [wp]:
 "\<lbrace>valid_refills scp\<rbrace> sched_context_update_consumed scptr \<lbrace>\<lambda>rv. valid_refills scp\<rbrace>"
  apply (simp add: sched_context_update_consumed_def)
  apply (wpsimp simp: set_object_def
                  wp: get_object_wp update_sched_context_valid_refills_no_budget_update_const
                      get_sched_context_wp)
  apply (clarsimp simp: valid_refills_def obj_at_def sc_valid_refills_def window_def)
  done

lemma set_mrs_valid_refills [wp]:
 "\<lbrace>valid_refills scp\<rbrace> set_mrs thread buf msgs \<lbrace>\<lambda>rv. valid_refills scp\<rbrace>"
  apply (simp add: set_mrs_def split_def)
  apply (wpsimp simp: set_object_def zipWithM_x_mapM_x wp: get_object_wp mapM_x_wp' split_del: if_split)
  apply (clarsimp simp: valid_refills_def obj_at_def get_tcb_SomeD)
  done

crunch valid_refills[wp]: copy_mrs "valid_refills scp"
  (wp: mapM_wp')

lemma transfer_caps_loop_valid_refills[wp]:
  "\<And>ep buffer n caps slots mi.
    \<lbrace>valid_refills scp\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. valid_refills scp\<rbrace>"
  by (wp transfer_caps_loop_pres cap_insert_valid_refills)


context SchedContextInv_AI begin

crunch valid_refills[wp]: do_ipc_transfer "valid_refills scp :: 'state_ext state \<Rightarrow> bool"

end

locale SchedContextInv_AI2 = SchedContextInv_AI state_ext_t some_t
  for state_ext_t :: "'state_ext::state_ext itself" and some_t :: "'t itself"+
  assumes send_ipc_valid_refills[wp]:
  "\<lbrace>valid_refills scptr\<rbrace> send_ipc block call badge can_grant can_donate thread epptr
      \<lbrace>\<lambda>_. valid_refills scptr :: 'state_ext state \<Rightarrow> bool\<rbrace>"
begin

crunch valid_refills[wp]: handle_timeout "valid_refills scp :: 'state_ext state \<Rightarrow> bool"

lemma end_timeslice_valid_refills[wp]:
  "end_timeslice canTimeout \<lbrace>valid_refills scptr :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  supply if_weak_cong[cong del]
  apply (clarsimp simp: end_timeslice_def)
  by (wpsimp simp: end_timeslice_def wp: hoare_drop_imps split_del: if_split)

lemma update_sched_context_valid_refills_sc_consumed_update:
  "\<lbrace>valid_refills scptr\<rbrace>
     update_sched_context p (\<lambda>sc. sc\<lparr>sc_consumed := sc_consumed sc + consumed\<rparr>)
      \<lbrace>\<lambda>_. valid_refills scptr\<rbrace>"
  by (wpsimp simp: update_sched_context_def obj_at_def
          wp: set_object_wp get_object_wp)

lemma charge_budget_valid_refills[wp]:
  "\<lbrace>(\<lambda>s. kheap s scptr = Some (SchedContext sc n)
          \<and> unat (r_time (refill_hd sc)) + 2 * unat (sc_period sc) + unat consumed
                     \<le> unat (max_word :: time)
          \<and> unat (cur_time s) + 2 * unat (sc_budget sc) \<le> unat (max_word::time)
          \<and> MIN_REFILLS \<le> sc_refill_max sc
          \<and> MIN_SC_BUDGET \<le> sc_budget sc \<and> sc_budget sc \<le> sc_period sc)
     and (valid_refills scptr :: 'state_ext state \<Rightarrow> bool)\<rbrace>
     charge_budget consumed canTimeout
    \<lbrace>\<lambda>_. valid_refills scptr\<rbrace>"
  apply (clarsimp simp: charge_budget_def is_round_robin_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (clarsimp split: if_splits)
  apply (intro conjI impI)

   \<comment> \<open>round robin\<close>
    apply (wpsimp wp: get_object_wp hoare_drop_imp set_object_wp hoare_drop_imps hoare_vcg_all_lift
                      update_sched_context_valid_refills_no_budget_update
                      refill_budget_check_round_robin_valid_refills[where sc=sc and n=n])
   apply (clarsimp simp: sc_valid_refills_def window_def word_le_nat_alt)

  \<comment> \<open>not round robin\<close>
  apply (wpsimp simp: set_object_def sc_valid_refills_def window_def
                  wp: get_object_wp update_sc_consumed_valid_refills
                      update_sched_context_valid_refills_no_budget_update sc_refill_ready_def
            simp_del: fun_upd_apply)
         apply (wpsimp wp: get_object_wp hoare_drop_imp set_object_wp
                           update_sched_context_valid_refills_no_budget_update
                           refill_budget_check_valid_refills[where sc=sc and n=n]
                     simp: sc_valid_refills_def window_def)+
  done

lemma check_budget_valid_refills[wp]:
  "\<lbrace>(\<lambda>s. kheap s scptr = Some (SchedContext sc n)
          \<and> unat (r_time (refill_hd sc)) + 2 * unat (sc_period sc) + unat (consumed_time s)
                     \<le> unat (max_word :: time)
          \<and> unat (cur_time s) + 2 * unat (sc_budget sc) \<le> unat (max_word::time)
          \<and> MIN_REFILLS \<le> sc_refill_max sc
          \<and> MIN_SC_BUDGET \<le> sc_budget sc \<and> sc_budget sc \<le> sc_period sc) and
     valid_refills scptr :: 'state_ext state \<Rightarrow> bool\<rbrace>
     check_budget
     \<lbrace>\<lambda>_. valid_refills scptr\<rbrace>"
  apply (clarsimp simp: check_budget_def refill_capacity_def get_refills_def bind_assoc)
  apply (wpsimp wp: charge_budget_valid_refills[where sc=sc and n=n]
              simp: valid_refills_def sc_valid_refills_def)+
  done

lemma update_sched_context_valid_refills_badge:
  "\<lbrace>valid_refills scptr\<rbrace>
    update_sched_context scptr (sc_badge_update (\<lambda>_. badge))
   \<lbrace>\<lambda>_. valid_refills scptr\<rbrace>"
  apply (simp add: update_sched_context_def)
  apply (wpsimp wp: set_object_wp get_object_wp)
  apply (clarsimp simp: valid_refills_def sc_valid_refills_def obj_at_def window_def)
  done

crunches commit_domain_time, get_sched_context
  for sc_at[wp]: "sc_at p"
  and ko_sc_at[wp]: "\<lambda>s. \<exists>sc n. ko_at (SchedContext sc n) p s"
  and ko_sc_at'[wp]: "\<lambda>s. ko_at (SchedContext sc n) p s"
  (wp: crunch_wps simp: crunch_simps)

end

text \<open>invocation related lemmas\<close>

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
   update_sched_context p (\<lambda>_. sc\<lparr>sc_period := period, sc_refill_max := m, sc_refills := r, sc_budget := b\<rparr>)
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

lemma sched_context_nonref_update_invs:
  "\<lbrace>\<lambda>s. invs s \<and> scp \<noteq> idle_sc_ptr \<and> (\<exists>n. ko_at (SchedContext sc n) scp s)\<rbrace>
   update_sched_context scp (\<lambda>_. sc\<lparr> sc_period := period, sc_refill_max := m, sc_refills := r0#rs,
                              sc_budget := budget\<rparr>)
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def simp_del: refs_of_defs
                  wp: valid_ioports_lift update_sc_refills_period_refill_max_valid_replies
                      update_sched_context_valid_idle set_sc_others_cur_sc_tcb)
  apply (auto simp: state_refs_of_def obj_at_def valid_obj_def valid_sched_context_def live_def
                    live_sc_def
             elim!: delta_sym_refs if_live_then_nonz_capD
             split: if_splits)
  done

lemma sched_context_nonref_update_invs_non_zero_length:
  "new_refills \<noteq> [] \<Longrightarrow>
   \<lbrace>\<lambda>s. invs s \<and> scp \<noteq> idle_sc_ptr \<and> (\<exists>n. ko_at (SchedContext sc n) scp s)\<rbrace>
   update_sched_context scp (\<lambda>_. sc\<lparr> sc_period := period, sc_refill_max := m, sc_refills := new_refills,
                              sc_budget := budget\<rparr>)
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def simp_del: refs_of_defs
                  wp: valid_ioports_lift update_sc_refills_period_refill_max_valid_replies
                      update_sched_context_valid_idle set_sc_others_cur_sc_tcb)
  apply (auto simp: state_refs_of_def obj_at_def valid_obj_def valid_sched_context_def live_def
                    live_sc_def
             elim!: delta_sym_refs if_live_then_nonz_capD
             split: if_splits)
  apply (meson list_exhaust_size_eq0 not_less_eq_eq zero_order(2))
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
  supply if_split[split del]
  unfolding refill_update_def
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply clarsimp
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (clarsimp simp: refill_ready_def is_round_robin_def bind_assoc)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (clarsimp split: if_split)
  apply (intro conjI impI allI)
         apply (wpsimp wp: sched_context_nonref_update_invs_non_zero_length)+
  done

lemma refill_budget_check_invs:
  "\<lbrace>\<lambda>s. invs s\<rbrace> refill_budget_check usage \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (clarsimp simp: refill_budget_check_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (wpsimp simp: refill_budget_check_def refill_full_def refill_size_def split_def
                  wp: get_sched_context_wp static_imp_wp hoare_drop_imp
                      hoare_vcg_all_lift hoare_vcg_if_lift2
                      update_sched_context_sc_refills_update_invs
           split_del: if_split)
  apply (frule (1) invs_valid_refills)
  apply (intro conjI impI)
    apply (fastforce intro: schedule_used_non_nil)
   apply (clarsimp simp: Let_def)+
  done

crunch ct_active[wp]: refill_full ct_active

lemma refill_budget_check_ex_nonz_cap_to_ct[wp]:
  "\<lbrace>\<lambda>s. ex_nonz_cap_to (cur_thread s) s\<rbrace> refill_budget_check usage
   \<lbrace>\<lambda>rv s. ex_nonz_cap_to (cur_thread s) s\<rbrace>"
  by (wpsimp simp: refill_budget_check_def set_refills_def is_round_robin_def refill_full_def
               wp: get_sched_context_wp get_refills_wp hoare_drop_imp hoare_vcg_if_lift2
        split_del: if_split)

lemma refill_budget_check_active[wp]:
  "\<lbrace>ct_active\<rbrace> refill_budget_check consumed \<lbrace> \<lambda>_ . ct_active\<rbrace>"
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

lemma set_refills_bound_sc:
  "\<lbrace>\<lambda>s. bound_sc_tcb_at P (cur_thread s) s\<rbrace>
   set_refills sc_ptr refills
   \<lbrace>\<lambda>rv s. bound_sc_tcb_at P (cur_thread s) s\<rbrace>"
  by (wpsimp simp: set_refills_def wp: update_sched_context_bound_sc)

lemma refill_budget_check_bound_sc:
  "\<lbrace>\<lambda>s. bound_sc_tcb_at P (cur_thread s) s\<rbrace>
   refill_budget_check usage
   \<lbrace>\<lambda>rv s. bound_sc_tcb_at P (cur_thread s) s\<rbrace>"
  supply if_split[split del]
  by (wpsimp simp: refill_budget_check_def is_round_robin_def refill_ready_def
               wp: update_sched_context_bound_sc refill_full_bound_sc
                   set_refills_bound_sc)

lemma charge_budget_invs:
  "\<lbrace>invs\<rbrace>
   charge_budget consumed canTimeout
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

text \<open>set_thread_state and schedcontext/schedcontrol invocations\<close>

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
                        us_to_ticks_mono[simplified mono_def] MIN_SC_BUDGET_def
                        MIN_SC_BUDGET_US_def MIN_BUDGET_def MIN_BUDGET_US_def
                        ARM.kernelWCET_ticks_def)
  done

end