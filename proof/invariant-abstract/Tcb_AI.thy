(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Tcb_AI
imports "./$L4V_ARCH/ArchCNodeInv_AI" SchedContextInv_AI IpcDet_AI
begin

context begin interpretation Arch .

requalify_facts
  arch_derive_is_arch rec_del_invs''

end

locale Tcb_AI_1 =
  fixes state_ext_t :: "'state_ext::state_ext itself"
  fixes is_cnode_or_valid_arch :: "cap \<Rightarrow> bool"
  assumes  activate_idle_invs:
  "\<And>thread. \<lbrace>(invs::'state_ext state \<Rightarrow> bool) and ct_idle\<rbrace>
     arch_activate_idle_thread thread
   \<lbrace>\<lambda>rv. invs and ct_idle\<rbrace>"
  assumes empty_fail_getRegister [intro!, simp]:
  "\<And>r. empty_fail (getRegister r)"
  assumes same_object_obj_refs:
  "\<And>cap cap'. \<lbrakk> same_object_as cap cap' \<rbrakk>
     \<Longrightarrow> obj_refs cap = obj_refs cap'"
  assumes arch_get_sanitise_register_info_inv[wp]:
    "\<And>ft P. arch_get_sanitise_register_info ft \<lbrace>P :: 'state_ext state \<Rightarrow> _\<rbrace>"
  assumes arch_post_modify_registers_invs[wp]:
  "\<And>c t. \<lbrace>\<lambda>(s::'state_ext state). invs s\<rbrace> arch_post_modify_registers c t
       \<lbrace>\<lambda>b s. invs s\<rbrace>"
  assumes arch_post_modify_registers_tcb_at[wp]:
  "\<And>c t a. \<lbrace>\<lambda>(s::'state_ext state). tcb_at a s\<rbrace> arch_post_modify_registers c t
       \<lbrace>\<lambda>b s. tcb_at a s\<rbrace>"
  assumes arch_post_modify_registers_ex_nonz_cap_to[wp]:
  "\<And>c t a. \<lbrace>\<lambda>(s::'state_ext state). ex_nonz_cap_to a s\<rbrace> arch_post_modify_registers c t
       \<lbrace>\<lambda>b s. ex_nonz_cap_to a s\<rbrace>"
  assumes arch_post_modify_registers_fault_tcb_at[wp]:
  "\<And>c t P a. \<lbrace>\<lambda>(s::'state_ext state). fault_tcb_at P a s\<rbrace> arch_post_modify_registers c t
       \<lbrace>\<lambda>b s. fault_tcb_at P a s\<rbrace>"
  assumes finalise_cap_not_cte_wp_at:
  "\<And>P cap fin. P cap.NullCap \<Longrightarrow> \<lbrace>\<lambda>s::'state_ext state. \<forall>cp \<in> ran (caps_of_state s). P cp\<rbrace>
                finalise_cap cap fin \<lbrace>\<lambda>rv s. \<forall>cp \<in> ran (caps_of_state s). P cp\<rbrace>"
  assumes table_cap_ref_max_free_index_upd[simp]: (* reordered to resolve dependency in tc_invs *)
  "\<And>cap. table_cap_ref (max_free_index_update cap) = table_cap_ref cap"

lemma set_consumed_ct_in_state[wp]: "\<lbrace>\<lambda>s. ct_in_state P s\<rbrace> set_consumed a buf \<lbrace>\<lambda>_ s. ct_in_state P s\<rbrace>"
  by (rule ct_in_state_thread_state_lift) wpsimp+

lemma complete_yield_to_ct_in_state[wp]:
  "\<lbrace>\<lambda>s. ct_in_state P s\<rbrace> complete_yield_to tptr \<lbrace>\<lambda>_ s. ct_in_state P s\<rbrace>"
  by (rule ct_in_state_thread_state_lift) wpsimp+

lemma (in Tcb_AI_1) activate_invs:
  "\<lbrace>(invs::'state_ext state \<Rightarrow> bool)\<rbrace> activate_thread \<lbrace>\<lambda>rv s. invs s \<and> (ct_running s \<or> ct_idle s)\<rbrace>"
  apply (unfold activate_thread_def get_tcb_obj_ref_def)
  apply (rule hoare_seq_ext [OF _ gets_sp])
  apply (rule hoare_seq_ext [OF _ thread_get_sp])
  apply (case_tac yt_opt, simp)
   apply (rule hoare_seq_ext [OF _ gts_sp])
   apply (rule_tac Q="st_tcb_at ((=) x) thread and invs and (\<lambda>s. cur_thread s = thread)" in hoare_weaken_pre)
    apply (rename_tac state)
    apply (case_tac state; simp)
      apply wp
      apply (clarsimp elim!: pred_tcb_weakenE
                       simp: ct_in_state_def)
     apply (rule_tac Q="\<lambda>rv. invs and ct_running" in hoare_post_imp, simp)
     apply (rule hoare_pre)
      apply (wp sts_invs_minor ct_in_state_set)
        apply simp
       apply (simp)+
       apply (wp hoare_post_imp [OF disjI1]
            | assumption
            | clarsimp elim!: st_tcb_weakenE)+
     apply (auto simp: invs_def valid_state_def valid_idle_def valid_pspace_def
                elim!: st_tcb_ex_cap pred_tcb_weakenE
                       fault_tcbs_valid_states_active,
            auto simp: st_tcb_def2 pred_tcb_at_def obj_at_def)[1]
    apply (rule_tac Q="\<lambda>rv. invs and ct_idle" in hoare_post_imp, simp)
    apply (wp activate_idle_invs hoare_post_imp [OF disjI2])
    apply (clarsimp simp: ct_in_state_def elim!: pred_tcb_weakenE)
   apply clarsimp
  apply (rule hoare_seq_ext)
   apply (rule hoare_K_bind)
   apply (rule hoare_seq_ext [OF _ gts_sp])
   apply (rule_tac Q="st_tcb_at ((=) state) thread and invs and (\<lambda>s. cur_thread s = thread)" in hoare_weaken_pre)
    apply (rename_tac state)
    apply (case_tac state; simp)
      apply wp
      apply (clarsimp elim!: pred_tcb_weakenE
      simp: ct_in_state_def)
     apply (rule_tac Q="\<lambda>rv. invs and ct_running" in hoare_post_imp, simp)
     apply (rule hoare_pre)
      apply (wp sts_invs_minor ct_in_state_set)
        apply simp
       apply (simp)+
       apply (wp  hoare_post_imp [OF disjI1] | assumption
               | clarsimp elim!: st_tcb_weakenE)+
     apply (auto simp: invs_def valid_state_def valid_idle_def valid_pspace_def
                elim!: st_tcb_ex_cap pred_tcb_weakenE
                       fault_tcbs_valid_states_active,
            auto simp: st_tcb_def2 pred_tcb_at_def obj_at_def)[1]
    apply (rule_tac Q="\<lambda>rv. invs and ct_idle" in hoare_post_imp, simp)
    apply (wp activate_idle_invs hoare_post_imp [OF disjI2])
    apply (clarsimp simp: ct_in_state_def elim!: pred_tcb_weakenE)
   apply clarsimp
   apply simp
  apply (wpsimp wp: complete_yield_to_invs)
  done

lemma cancel_ipc_no_refs:
  "\<lbrace>\<lambda>s. sym_refs (state_refs_of s) \<and> valid_objs s\<rbrace>
  cancel_ipc t \<lbrace>\<lambda>_. st_tcb_at (\<lambda>st'. tcb_st_refs_of st' = {}) t\<rbrace>"
  apply (rule hoare_strengthen_post)
   apply (rule cancel_ipc_simple_except_awaiting_reply)
  apply (auto elim: st_tcb_weakenE)
  done

crunch invs[wp]: test_possible_switch_to invs

lemma restart_invs[wp]:
  "\<lbrace>invs and tcb_at t and ex_nonz_cap_to t\<rbrace>
   restart t
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  unfolding restart_def
  apply (wpsimp wp: hoare_drop_imp sts_invs_minor cancel_ipc_no_refs
                    cancel_ipc_ex_nonz_cap_to_tcb gts_wp)
  apply (auto dest!: idle_no_ex_cap simp: invs_def valid_state_def valid_pspace_def)
  done

lemma restart_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> Tcb_A.restart t \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by (wpsimp simp: Tcb_A.restart_def wp: thread_get_wp cancel_ipc_typ_at
      | rule hoare_strengthen_post[where Q="\<lambda>rv s. P (typ_at T p s)"])+

lemma restart_tcb[wp]:
  "\<lbrace>tcb_at t'\<rbrace> Tcb_A.restart t \<lbrace>\<lambda>rv. tcb_at t'\<rbrace>"
  by (wpsimp simp: tcb_at_typ wp: restart_typ_at)

crunch ex_nonz_cap_to[wp]: update_restart_pc "ex_nonz_cap_to t"

lemma suspend_nonz_cap_to_tcb[wp]:
  "\<lbrace>\<lambda>s. ex_nonz_cap_to t s \<and> tcb_at t s \<and> valid_objs s\<rbrace>
     suspend t'
   \<lbrace>\<lambda>rv s. ex_nonz_cap_to t s\<rbrace>"
  unfolding suspend_def sched_context_cancel_yield_to_def
  by (wpsimp wp: cancel_ipc_ex_nonz_cap_to_tcb hoare_drop_imps)

lemmas suspend_tcb_at[wp] = tcb_at_typ_at [OF suspend_typ_at]

lemma readreg_invs:
  "\<lbrace>invs and tcb_at src and ex_nonz_cap_to src\<rbrace>
     invoke_tcb (tcb_invocation.ReadRegisters src susp n arch)
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (wpsimp wp: suspend_invs)
  apply (clarsimp simp: invs_def valid_state_def valid_pspace_def valid_idle_def
                 dest!: idle_no_ex_cap)
  done

lemma (in Tcb_AI_1) writereg_invs:
  "\<lbrace>(invs::'state_ext state \<Rightarrow> bool) and tcb_at dest and ex_nonz_cap_to dest\<rbrace>
     invoke_tcb (tcb_invocation.WriteRegisters dest resume values arch)
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (wpsimp |rule conjI)+

lemma (in Tcb_AI_1) copyreg_invs:
  "\<lbrace>(invs::'state_ext state \<Rightarrow> bool) and tcb_at src and tcb_at dest and ex_nonz_cap_to dest and
    ex_nonz_cap_to src\<rbrace>
     invoke_tcb (tcb_invocation.CopyRegisters dest src susp resume frames ints arch)
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wpsimp simp: if_apply_def2
                  wp: mapM_x_wp' suspend_invs suspend_nonz_cap_to_tcb static_imp_wp)
  apply (clarsimp simp: invs_def valid_state_def valid_pspace_def valid_idle_def suspend_def
                 dest!: idle_no_ex_cap)
  done

lemma out_invs_trivialT:
  assumes x: "\<And>tcb v. \<forall>(getF, setF)\<in>ran tcb_cap_cases. getF (fn v tcb) = getF tcb"
  assumes r:  "\<And>tcb v. tcb_arch_ref (fn v tcb) = tcb_arch_ref tcb" (* ARMHYP *)
  assumes z: "\<And>tcb v. tcb_state  (fn v tcb) = tcb_state  tcb"
  assumes z': "\<And>tcb v. tcb_bound_notification (fn v tcb) = tcb_bound_notification tcb"
  assumes y: "\<And>tcb v. tcb_sched_context (fn v tcb) = tcb_sched_context tcb"
  assumes y': "\<And>tcb v. tcb_yield_to (fn v tcb) = tcb_yield_to tcb"
  assumes z'': "\<And>tcb v. tcb_iarch (fn v tcb) = tcb_iarch tcb"
  assumes w: "\<And>tcb v. tcb_ipc_buffer (fn v tcb) = tcb_ipc_buffer tcb
                          \<or> tcb_ipc_buffer (fn v tcb) = 0"
  assumes a: "\<And>tcb v. tcb_fault (fn v tcb) = tcb_fault tcb"
  shows      "\<lbrace>invs\<rbrace> option_update_thread t fn v \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (case_tac v, simp_all add: option_update_thread_def)
  apply (rule thread_set_invs_trivial [OF x z z' y y' z'' w a r])
  done

lemmas out_invs_trivial = out_invs_trivialT [OF ball_tcb_cap_casesI]

lemma out_typ_at:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> option_update_thread t fn v \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  apply (case_tac v, simp_all add: option_update_thread_def)
  apply (rule thread_set_typ_at)
  done


lemma out_tcb[wp]:
  "\<lbrace>tcb_at t\<rbrace> option_update_thread t fn v \<lbrace>\<lambda>rv. tcb_at t\<rbrace>"
  by (simp add: tcb_at_typ, wp out_typ_at)


lemma out_valid_cap:
  "\<lbrace>valid_cap c\<rbrace> option_update_thread t fn v \<lbrace>\<lambda>rv. valid_cap c\<rbrace>"
  by (wp out_typ_at valid_cap_typ)


lemma out_cte_at:
  "\<lbrace>cte_at c\<rbrace> option_update_thread t fn v \<lbrace>\<lambda>rv. cte_at c\<rbrace>"
  by (wp out_typ_at valid_cte_at_typ)


lemma out_st_tcb:
  assumes x: "\<And>tcb v. tcb_state  (fn v tcb) = tcb_state  tcb"
  shows      "\<lbrace>st_tcb_at P t\<rbrace> option_update_thread t' fn v \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  apply (case_tac v, simp_all add: option_update_thread_def)
  apply (rule thread_set_no_change_tcb_state, rule x)
  done

lemma inQ_residue[simp]:
  "(P \<and> Q \<and> (P \<longrightarrow> R)) = (P \<and> Q \<and> R)"
  by fastforce

lemma set_simple_ko_valid_cap:
  "\<lbrace>valid_cap c\<rbrace> set_simple_ko f e ep \<lbrace>\<lambda>_. valid_cap c\<rbrace>"
  by (wp valid_cap_typ)


lemma si_cte_at[wp]:
  "\<lbrace>cte_at p\<rbrace> send_ipc bl c ba cg cgr t ep r \<lbrace>\<lambda>_. cte_at p\<rbrace>"
  by (wp valid_cte_at_typ)


lemma ri_cte_at[wp]:
  "\<lbrace>cte_at p\<rbrace> receive_ipc t cap is_blocking r \<lbrace>\<lambda>_. cte_at p\<rbrace>"
  by (wp valid_cte_at_typ)


lemma rai_cte_at[wp]:
  "\<lbrace>cte_at p\<rbrace> receive_signal t cap is_blocking \<lbrace>\<lambda>_. cte_at p\<rbrace>"
  by (wp valid_cte_at_typ)


lemma hf_cte_at[wp]:
  "\<lbrace>cte_at p\<rbrace> handle_fault t ft \<lbrace>\<lambda>_. cte_at p\<rbrace>"
  by (wp valid_cte_at_typ)


lemma cancel_all_ipc_tcb:
  "\<lbrace>tcb_at t\<rbrace> cancel_all_ipc ptr \<lbrace>\<lambda>_. tcb_at t\<rbrace>"
  by (simp add: tcb_at_typ, wp cancel_all_ipc_typ_at)

lemma thread_set_valid_objs':
  "\<lbrace>valid_objs and (\<lambda>s. \<forall>p t. valid_tcb p t s \<longrightarrow> valid_tcb p (f t) s)\<rbrace>
  thread_set f t
  \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  apply (simp add: thread_set_def)
  apply wp
  apply clarsimp
  apply (clarsimp dest!: get_tcb_SomeD simp: obj_at_def)
  apply (erule (1) pspace_valid_objsE)
  apply (simp add: valid_obj_def)
  done


lemma thread_set_valid_objs:
  "\<lbrace>valid_objs and K (\<forall>p (s::'z::state_ext state) t. valid_tcb p t s \<longrightarrow> valid_tcb p (f t) s)\<rbrace>
  (thread_set f t :: (unit,'z) s_monad)
  \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  apply (rule hoare_weaken_pre)
   apply (rule thread_set_valid_objs')
  apply simp
  done


lemma out_valid_objs:
  "\<lbrace>valid_objs and K (\<forall>p (s::'z::state_ext state) t x. valid_tcb p t s \<longrightarrow> valid_tcb p (f x t) s)\<rbrace>
  (option_update_thread a f t :: (unit,'z) s_monad)
  \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  apply (cases t)
   apply (simp add: option_update_thread_def)
   apply wp
   apply simp
  apply (simp add: option_update_thread_def)
  apply (wp thread_set_valid_objs)
  apply simp
  done


lemma out_cte_wp_at_trivialT:
  "(\<And>tcb v. \<forall>(getF, x)\<in>ran tcb_cap_cases. getF (f v tcb) = getF tcb)
   \<Longrightarrow> \<lbrace>\<lambda>s. P (cte_wp_at P' p s)\<rbrace>
  option_update_thread a f t
  \<lbrace>\<lambda>rv s. P (cte_wp_at P' p s)\<rbrace>"
  apply (simp add: option_update_thread_def cte_wp_at_caps_of_state)
  apply (rule hoare_pre)
   apply (wp thread_set_caps_of_state_trivial | simp | wpc)+
  done


lemma same_object_as_cte_refs:
  "\<lbrakk> same_object_as cap cap' \<rbrakk> \<Longrightarrow>
     cte_refs cap' = cte_refs cap"
  apply (rule ext, cases cap, simp_all add: same_object_as_def)
       apply (clarsimp simp: is_cap_simps bits_of_def
                      split: cap.split_asm)+
  done


lemma same_object_untyped_range:
  "\<lbrakk> same_object_as cap cap' \<rbrakk>
     \<Longrightarrow> untyped_range cap = {}"
  by (cases cap, (clarsimp simp: same_object_as_def is_cap_simps)+)


lemma same_object_zombies:
  "\<lbrakk> same_object_as cap cap' \<rbrakk>
     \<Longrightarrow> is_zombie cap = is_zombie cap'"
  by (cases cap, (clarsimp simp: same_object_as_def is_cap_simps
                          split: cap.split_asm)+)


lemma zombies_final_helperE:
  "\<lbrakk> caps_of_state s p = Some cap; r \<in> obj_refs cap; \<not> is_zombie cap;
     zombies_final s; caps_of_state s p' = Some cap'; r \<in> obj_refs cap' \<rbrakk>
     \<Longrightarrow> \<not> is_zombie cap'"
  apply (cases p', drule caps_of_state_cteD[simplified cte_wp_at_eq_simp],
         drule(2) zombies_final_helper)
  apply (fastforce simp: cte_wp_at_caps_of_state)
  done

lemma cap_badge_none_master:
  "(cap_badge (cap_master_cap cap) = None)
     = (cap_badge cap = None)"
  by (simp add: cap_master_cap_def split: cap.split)


lemma cap_master_eq_badge_none:
  "\<lbrakk> cap_master_cap cap = cap_master_cap cap' \<rbrakk>
        \<Longrightarrow> (cap_badge cap = None) = (cap_badge cap' = None)"
  apply (subst cap_badge_none_master[symmetric], simp)
  apply (simp add: cap_badge_none_master)
  done


lemma check_cap_inv2:
  assumes x: "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  shows      "\<lbrace>P and Q ()\<rbrace> check_cap_at cap slot f \<lbrace>Q\<rbrace>"
  unfolding check_cap_at_def
  by (wp x get_cap_wp, clarsimp)

lemmas check_cap_inv
    = check_cap_inv2[where P=P and Q="\<lambda>rv. P" for P, simplified pred_conj_def,
                     simplified]

declare in_image_op_plus[simp]

lemma tcb_cap_always_valid_strg:
  "(case tcb_cap_cases p of None \<Rightarrow> True | Some (getF, setF, restr) \<Rightarrow> \<forall>st. restr t st cap)
      \<and> (p = tcb_cnode_index 2 \<longrightarrow> (\<forall>ptr. valid_ipc_buffer_cap cap ptr))
         \<longrightarrow> tcb_cap_valid cap (t, p) s"
  by (clarsimp simp: tcb_cap_valid_def st_tcb_def2 tcb_at_def
              split: option.split_asm)

crunch not_cte_wp_at[wp]: unbind_maybe_notification "\<lambda>s. \<forall>cp\<in>ran (caps_of_state s). P cp"
  (wp: thread_set_caps_of_state_trivial simp: tcb_cap_cases_def)


lemma (in Tcb_AI_1) rec_del_all_caps_in_range:
  assumes x: "P cap.NullCap"
      and y: "\<And>x n zt. P (cap.ThreadCap x) \<Longrightarrow> P (cap.Zombie x zt n)"
      and z: "\<And>x y gd n zt. P (cap.CNodeCap x y gd) \<Longrightarrow> P (cap.Zombie x zt n)"
      and w: "\<And>x zt zt' n m. P (cap.Zombie x zt n) \<Longrightarrow> P (cap.Zombie x zt' m)"
  shows      "s \<turnstile> \<lbrace>\<lambda>(s::'state_ext state). \<forall>cp \<in> ran (caps_of_state s). P cp\<rbrace>
                     rec_del args
                  \<lbrace>\<lambda>rv s. \<forall>cp \<in> ran (caps_of_state s). P cp\<rbrace>,
                  \<lbrace>\<lambda>e s. \<forall>cp \<in> ran (caps_of_state s). P cp\<rbrace>"
proof (induct rule: rec_del.induct, simp_all only: rec_del_fails)
  case (1 slot exposed s')
  note hyps = "1.hyps"[simplified slot_rdcall.simps rec_del_call.simps simp_thms]
  show ?case
    apply (simp add: split_def)
    apply wp
     apply (wp empty_slot_caps_of_state)[1]
    apply (rule spec_strengthen_postE, rule hyps)
    apply (clarsimp simp add: x ball_ran_eq)
    done
next
  case (2 slot exposed s')
  note hyps = "2.hyps"[simplified slot_rdcall.simps rec_del_call.simps simp_thms]
  show ?case
  apply (simp add: split_def cong: if_cong)
  apply (wp hyps, simp+)
       apply ((wp irq_state_independent_AI preemption_point_inv | simp)+)[1]
      apply (simp only: simp_thms)
      apply (wp hyps, simp+)
     apply wp+
    apply (rule hoare_strengthen_post)
     apply (rule hoare_vcg_conj_lift)
      apply (rule finalise_cap_cases[where slot=slot])
     apply (rule hoare_vcg_conj_lift)
      apply (rule finalise_cap_equal_cap[where sl=slot])
     apply (rule finalise_cap_not_cte_wp_at[where P=P, OF x])
    apply (clarsimp simp: cte_wp_at_caps_of_state)
    apply (erule disjE)
     apply clarsimp
    apply (clarsimp simp: is_cap_simps ball_ran_eq)
    apply (subgoal_tac "P rv")
     apply (case_tac rv, simp_all add: fst_cte_ptrs_def gen_obj_refs_eq)[1]
       apply (simp add: z)
      apply (simp add: y)
     apply (simp split: option.split_asm, simp_all add: w gen_obj_refs_eq)[1]
    apply (cases slot, fastforce)
   apply (simp add: is_final_cap_def)
   apply (wp get_cap_wp)+
  apply clarsimp
  done
next
  case (3 ptr bits n slot s')
  show ?case
    apply simp
    apply wp+
    apply (cases slot)
    apply (clarsimp del: ballI simp: ball_ran_eq)
    done
next
  case (4 ptr bits n slot s')
  show ?case
    apply simp
    apply wp
     apply (wp get_cap_wp)[1]
    apply (rule spec_strengthen_postE, rule "4.hyps")
     apply (simp add: in_monad)
    apply (clarsimp del: ballI simp: ball_ran_eq)
    apply (fastforce simp: cte_wp_at_caps_of_state
                    elim: w)
    done
qed

abbreviation
 "no_cap_to_obj_dr_emp cap \<equiv> no_cap_to_obj_with_diff_ref cap {}"

lemma no_cap_to_obj_with_diff_ref_ran_caps_form:
  "no_cap_to_obj_dr_emp cap
     = (\<lambda>s. \<forall>cp \<in> ran (caps_of_state s).
              obj_refs cp = obj_refs cap \<longrightarrow> table_cap_ref cp = table_cap_ref cap)"
  apply (rule ext, simp add: no_cap_to_obj_with_diff_ref_def)
  apply (simp add: ball_ran_eq cte_wp_at_caps_of_state)
  apply auto
  done

context Tcb_AI_1 begin

primrec
  tcb_inv_wf'  :: "tcb_invocation \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "tcb_inv_wf' (tcb_invocation.Suspend t)
             = (tcb_at t and ex_nonz_cap_to t)"
| "tcb_inv_wf' (tcb_invocation.Resume t)
             = (tcb_at t and ex_nonz_cap_to t)"
| "tcb_inv_wf' (tcb_invocation.ThreadControlCaps t sl fh th croot vroot buf)
             = (tcb_at t and case_option \<top> (valid_cap \<circ> fst) croot
                        and K (case_option True (is_cnode_cap \<circ> fst) croot)
                        and case_option \<top> ((real_cte_at And ex_cte_cap_to) \<circ> snd) croot
                        and case_option \<top> (no_cap_to_obj_dr_emp \<circ> fst) croot
                        and case_option \<top> (valid_cap \<circ> fst) vroot
                        and K (case_option True (is_valid_vtable_root \<circ> fst) vroot)
                        and case_option \<top> (no_cap_to_obj_dr_emp \<circ> fst) vroot
                        and case_option \<top> ((real_cte_at And ex_cte_cap_to) \<circ> snd) vroot
                        and case_option \<top> (valid_cap \<circ> fst) fh
                        and K (case_option True (valid_fault_handler o fst) fh)
                        and case_option \<top> (\<lambda>(cap, slot). cte_wp_at ((=) cap) slot) fh
                        and case_option \<top> (no_cap_to_obj_dr_emp \<circ> fst) fh
                        and case_option \<top> ((real_cte_at And ex_cte_cap_to) \<circ> snd) fh
                        and case_option \<top> (valid_cap \<circ> fst) th
                        and K (case_option True (valid_fault_handler o fst) th)
                        and case_option \<top> (\<lambda>(cap, slot). cte_wp_at ((=) cap) slot) th
                        and case_option \<top> (no_cap_to_obj_dr_emp \<circ> fst) th
                        and case_option \<top> ((real_cte_at And ex_cte_cap_to) \<circ> snd) th
                        and (case_option \<top> (case_option \<top> (valid_cap o fst) o snd) buf)
                        and (case_option \<top> (case_option \<top>
                              (no_cap_to_obj_dr_emp o fst) o snd) buf)
                        and K (case_option True ((\<lambda>v. is_aligned v msg_align_bits) o fst) buf)
                        and K (case_option True (\<lambda>v. case_option True
                               ((swp valid_ipc_buffer_cap (fst v)
                                    and is_arch_cap and is_cnode_or_valid_arch)
                                              o fst) (snd v)) buf)
                        and (case_option \<top> (case_option \<top> ((cte_at And ex_cte_cap_to) o snd) o snd) buf)
                        and (\<lambda>s. {fh, th, croot, vroot, option_map undefined buf} \<noteq> {None}
                                    \<longrightarrow> cte_at sl s \<and> ex_cte_cap_to sl s)
                        and ex_nonz_cap_to t)"
| "tcb_inv_wf' (tcb_invocation.ThreadControlSched t sl fh mcp pr sc)
             = (tcb_at t
                        and case_option \<top> (valid_cap \<circ> fst) fh
                        and K (case_option True (valid_fault_handler o fst) fh)
                        and case_option \<top> (\<lambda>(cap, slot). cte_wp_at ((=) cap) slot) fh
                        and case_option \<top> (no_cap_to_obj_dr_emp \<circ> fst) fh
                        and case_option \<top> ((real_cte_at And ex_cte_cap_to) \<circ> snd) fh
                        and case_option \<top>
                              (case_option
                                (\<lambda>s. t \<noteq> cur_thread s)
                                (\<lambda>scptr. bound_sc_tcb_at ((=) None) t and ex_nonz_cap_to scptr
                                         and sc_tcb_sc_at ((=) None) scptr
                                         and (\<lambda>s. st_tcb_at (ipc_queued_thread_state) t s
                                                  \<longrightarrow> sc_at_pred (sc_released (cur_time s))
                                                                 scptr s)))
                              sc
                        and (\<lambda>s. fh \<noteq> None \<longrightarrow> cte_at sl s \<and> ex_cte_cap_to sl s)
                        and ex_nonz_cap_to t)"
| "tcb_inv_wf' (tcb_invocation.ReadRegisters src susp n arch)
             = (tcb_at src and ex_nonz_cap_to src)"
| "tcb_inv_wf' (tcb_invocation.WriteRegisters dest resume values arch)
             = (tcb_at dest and ex_nonz_cap_to dest)"
| "tcb_inv_wf' (tcb_invocation.CopyRegisters dest src suspend_source resume_target
                 trans_frame trans_int trans_arch)
             = (tcb_at dest and tcb_at src and ex_nonz_cap_to src and
                ex_nonz_cap_to dest)"
| "tcb_inv_wf' (NotificationControl t ntfn)
             = (tcb_at t and ex_nonz_cap_to t
                  and (case ntfn of None \<Rightarrow> \<top>
                          | Some ntfnptr \<Rightarrow> (obj_at (\<lambda>ko. \<exists>ntfn. ko = Notification ntfn
                                                \<and> (ntfn_bound_tcb ntfn = None)
                                                \<and> (\<forall>q. ntfn_obj ntfn \<noteq> WaitingNtfn q)) ntfnptr
                                          and ex_nonz_cap_to ntfnptr
                                          and bound_tcb_at ((=) None) t) ))"
| "tcb_inv_wf' (SetTLSBase t tls_base) = (tcb_at t and ex_nonz_cap_to t)"

fun
  tcb_inv_wf  :: "tcb_invocation \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "tcb_inv_wf (tcb_invocation.ThreadControlSched t sl fh mcp pr sc)
             = (tcb_inv_wf' (tcb_invocation.ThreadControlSched t sl fh mcp pr sc)
                        \<comment> \<open>NOTE: The auth TCB does not really belong in the tcb_invocation
                        type, and is only included so that we can assert here that the
                        priority we are setting is bounded by the MCP of some auth TCB.
                        Unfortunately, current proofs about the decode functions throw
                        away the knowledge that the auth TCB actually came from the
                        current thread's c-space, so this is not as strong an assertion as
                        we would like. Ideally, we would assert that there is some cap in
                        the current thread's c-space that is to a TCB whose MCP validates
                        the priority we are setting. We don't care which TCB is used as
                        the auth TCB; we only care that there exists some auth TCB
                        accessible from the current thread's c-space. Phrased that way, we
                        could drop the auth TCB from tcb_invocation. For now, we leave
                        this as future work.\<close>
                        and (\<lambda>s. case_option True (\<lambda>(pr, auth). mcpriority_tcb_at (\<lambda>mcp. pr \<le> mcp) auth s) pr)
                        and (\<lambda>s. case_option True (\<lambda>(mcp, auth). mcpriority_tcb_at (\<lambda>m. mcp \<le> m) auth s) mcp))"
| "tcb_inv_wf invocation = (tcb_inv_wf' invocation)"

end

locale Tcb_AI = Tcb_AI_1 state_ext_t is_cnode_or_valid_arch
  for state_ext_t :: "'state_ext::state_ext itself"
  and is_cnode_or_valid_arch :: "cap \<Rightarrow> bool" +
  assumes cap_delete_no_cap_to_obj_asid[wp]:
  "\<And>cap slot. \<lbrace>(no_cap_to_obj_dr_emp cap::'state_ext state \<Rightarrow> bool)\<rbrace>
     cap_delete slot
   \<lbrace>\<lambda>rv. no_cap_to_obj_dr_emp cap\<rbrace>"
  assumes install_tcb_cap_no_cap_to_obj_dr_emp[wp]:
  "\<And>cap target slot n slot_opt.
    \<lbrace>no_cap_to_obj_dr_emp cap and
     (\<lambda>s. \<forall>new_cap src_slot. slot_opt = Some (new_cap, src_slot)
                           \<longrightarrow> no_cap_to_obj_dr_emp new_cap s)\<rbrace>
    install_tcb_cap target slot n slot_opt
    \<lbrace>\<lambda>_. no_cap_to_obj_dr_emp cap\<rbrace>"
  assumes tcc_invs:
  "\<And>t croot vroot buf fh th mcp sl pr sc.
    \<lbrace>(invs::'state_ext state \<Rightarrow> bool)
      and tcb_inv_wf (ThreadControlCaps t sl fh th croot vroot buf )\<rbrace>
      invoke_tcb (ThreadControlCaps t sl fh th croot vroot buf )
    \<lbrace>\<lambda>rv. invs\<rbrace>"  (* need more on sc, fh and th *)
  assumes tcs_invs:
  "\<And>t croot vroot buf fh th mcp sl pr sc.
    \<lbrace>(invs::'state_ext state \<Rightarrow> bool)
      and tcb_inv_wf (ThreadControlSched t sl fh mcp pr sc)\<rbrace>
      invoke_tcb (ThreadControlSched t sl fh mcp pr sc)
    \<lbrace>\<lambda>rv. invs\<rbrace>"  (* need more on sc, fh and th *)
  assumes decode_set_ipc_inv[wp]:
  "\<And>P args cap slot excaps.
    \<lbrace>P::'state_ext state \<Rightarrow> bool\<rbrace> decode_set_ipc_buffer args cap slot excaps \<lbrace>\<lambda>rv. P\<rbrace>"
  assumes update_cap_valid:
  "\<And>cap s capdata rs p. valid_cap cap (s::'state_ext state) \<Longrightarrow>
   valid_cap (case capdata of
              None \<Rightarrow> cap_rights_update rs cap
            | Some x \<Rightarrow> update_cap_data p x
                     (cap_rights_update rs cap)) s"
  assumes check_valid_ipc_buffer_wp:
  "\<And>cap vptr P. \<lbrace>\<lambda>(s::'state_ext state). is_arch_cap cap \<and> is_cnode_or_valid_arch cap
          \<and> valid_ipc_buffer_cap cap vptr
          \<and> is_aligned vptr msg_align_bits
             \<longrightarrow> P s\<rbrace>
     check_valid_ipc_buffer vptr cap
   \<lbrace>\<lambda>rv. P\<rbrace>,-"
  assumes derive_no_cap_asid[wp]:
  "\<And>cap S slot. \<lbrace>(no_cap_to_obj_with_diff_ref cap S)::'state_ext state \<Rightarrow> bool\<rbrace>
     derive_cap slot cap
   \<lbrace>\<lambda>rv. no_cap_to_obj_with_diff_ref rv S\<rbrace>,-"
  assumes no_cap_to_obj_with_diff_ref_update_cap_data:
  "\<And>c S s P x. no_cap_to_obj_with_diff_ref c S (s::'state_ext state) \<longrightarrow>
    no_cap_to_obj_with_diff_ref (update_cap_data P x c) S s"


lemma out_no_cap_to_trivial:
  "(\<And>tcb v. \<forall>(getF, x)\<in>ran tcb_cap_cases. getF (f v tcb) = getF tcb)
   \<Longrightarrow> \<lbrace>no_cap_to_obj_with_diff_ref cap S\<rbrace>
         option_update_thread a f t
      \<lbrace>\<lambda>rv. no_cap_to_obj_with_diff_ref cap S\<rbrace>"
  apply (simp add: no_cap_to_obj_with_diff_ref_def)
  apply (wpsimp wp: hoare_vcg_const_Ball_lift out_cte_wp_at_trivialT
    | fast)+
  done

lemmas thread_set_no_cap_to_trivial = thread_set_no_cap_obj_ref_trivial

lemma (in Tcb_AI_1) checked_insert_no_cap_to:
  "\<lbrace>no_cap_to_obj_with_diff_ref c' {} and
        no_cap_to_obj_with_diff_ref a {}\<rbrace>
     check_cap_at a b (check_cap_at c d (cap_insert a b e))
   \<lbrace>\<lambda>r. no_cap_to_obj_with_diff_ref c' {}\<rbrace>"
  apply (simp add: check_cap_at_def cap_insert_def
                   cte_wp_at_caps_of_state set_untyped_cap_as_full_def
                   no_cap_to_obj_with_diff_ref_def)
  apply (wp get_cap_wp
               | simp split del: if_split)+
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (clarsimp dest!: same_object_obj_refs)
  apply (cases b, cases d, clarsimp)
  apply auto
  done

lemma thread_set_valid_objs'':
  "\<lbrace>valid_objs and (\<lambda>s. \<forall>tcb. get_tcb t s = Some tcb
        \<longrightarrow> valid_tcb t tcb s \<longrightarrow> valid_tcb t (f tcb) s)\<rbrace>
     thread_set f t
   \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  apply (simp add: thread_set_def set_object_def get_object_def)
  apply wp
  apply (clarsimp simp: fun_upd_def[symmetric])
  apply (frule(1) valid_tcb_objs)
  apply (rule valid_objs_tcb_update, simp_all add: tcb_at_def)
  done

lemma thread_set_tcb_ipc_buffer_cap_cleared_invs:
  "\<lbrace>invs and cte_wp_at (\<lambda>c. c = cap.NullCap) (t, tcb_cnode_index 2)\<rbrace>
     thread_set (tcb_ipc_buffer_update f) t
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (wp thread_set_valid_objs''
            thread_set_refs_trivial
            thread_set_hyp_refs_trivial
            thread_set_iflive_trivial
            thread_set_mdb
            thread_set_ifunsafe_trivial
            thread_set_cur_tcb
            thread_set_cur_sc_tcb
            thread_set_zombies_trivial
            thread_set_valid_idle_trivial
            thread_set_global_refs_triv
            valid_irq_node_typ valid_irq_handlers_lift
            thread_set_caps_of_state_trivial
            valid_ioports_lift
            thread_set_arch_caps_trivial
            thread_set_only_idle
            thread_set_cap_refs_in_kernel_window
            thread_set_valid_ioc_trivial
            thread_set_cap_refs_respects_device_region
            thread_set_valid_replies_trivial
            thread_set_fault_tcbs_valid_states_trivial
         | simp add: ran_tcb_cap_cases
         | rule conjI
         | erule disjE)+
  apply (clarsimp simp: valid_tcb_def dest!: get_tcb_SomeD)
  apply (rule conjI, simp add: ran_tcb_cap_cases)
  apply (cut_tac P="(=) v" and t="(t, tcb_cnode_index 2)" for v
            in  cte_wp_at_tcbI)
     apply simp
    apply fastforce
   apply (rule refl)
  apply (clarsimp simp: cte_wp_at_caps_of_state
                        valid_ipc_buffer_cap_def)
  done

lemma thread_set_tcb_valid:
  assumes x: "\<And>tcb. tcb_state (fn tcb) = tcb_state tcb"
  assumes w: "\<And>tcb. tcb_ipc_buffer (fn tcb) = tcb_ipc_buffer tcb
                     \<or> tcb_ipc_buffer (fn tcb) = 0"
  shows      "\<lbrace>tcb_cap_valid c p\<rbrace>
              thread_set fn t
              \<lbrace>\<lambda>rv. tcb_cap_valid c p\<rbrace>"
  apply (wpsimp wp: set_object_wp_strong simp: thread_set_def)
  apply (clarsimp simp: tcb_cap_valid_def
                 dest!: get_tcb_SomeD)
  apply (simp add: obj_at_def pred_tcb_at_def is_tcb x
            split: if_split_asm cong: option.case_cong prod.case_cong)
  apply (cut_tac tcb=y in w)
  apply auto
  done

lemma out_tcb_valid:
  assumes x: "\<And>tcb v. tcb_state  (fn v tcb) = tcb_state  tcb"
  assumes w: "\<And>tcb v. tcb_ipc_buffer (fn v tcb) = tcb_ipc_buffer tcb
                          \<or> tcb_ipc_buffer (fn v tcb) = 0"
  shows      "\<lbrace>tcb_cap_valid c p\<rbrace> option_update_thread t fn v
              \<lbrace>\<lambda>rv. tcb_cap_valid c p\<rbrace>"
  apply (case_tac v, simp_all add: option_update_thread_def)
  apply (rule thread_set_tcb_valid [OF x w])
  done


lemma thread_set_ipc_tcb_cap_valid:
  "\<lbrace>\<lambda>s. is_nondevice_page_cap cap
           \<and> (\<forall>ptr. valid_ipc_buffer_cap cap (f ptr))\<rbrace>
     thread_set (tcb_ipc_buffer_update f) t
   \<lbrace>\<lambda>rv. tcb_cap_valid cap (t, tcb_cnode_index 2)\<rbrace>"
  apply (simp add: thread_set_def set_object_def get_object_def)
  apply wp
  apply (clarsimp simp: tcb_cap_valid_def obj_at_def
                        pred_tcb_at_def is_tcb
                 dest!: get_tcb_SomeD)
  done

lemma update_mcpriority_valid_tcb[simp]:
  "valid_tcb p t s \<Longrightarrow> valid_tcb p (t\<lparr>tcb_mcpriority := x\<rparr>) s"
  by (simp add: valid_tcb_def ran_tcb_cap_cases)

lemma set_mcpriority_valid_objs[wp]:
  "\<lbrace>invs\<rbrace> set_mcpriority t x \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  unfolding set_mcpriority_def
  apply (wp thread_set_valid_objs')
  apply (simp add: Invariants_AI.invs_valid_objs)
  done

crunch valid_cap[wp]: set_mcpriority "valid_cap c"
crunch cte_at[wp]: set_mcpriority "cte_at c"

lemma set_mcpriority_invs[wp]:
  "\<lbrace>invs and tcb_at t\<rbrace> set_mcpriority t x \<lbrace>\<lambda>rv. invs\<rbrace>"
  unfolding set_mcpriority_def
  by (wp thread_set_valid_objs''
         thread_set_refs_trivial
         thread_set_hyp_refs_trivial
         thread_set_iflive_trivial
         thread_set_mdb
         thread_set_ifunsafe_trivial
         thread_set_cur_tcb
         thread_set_cur_sc_tcb
         thread_set_zombies_trivial
         thread_set_valid_idle_trivial
         thread_set_global_refs_triv
         valid_irq_node_typ valid_irq_handlers_lift
         thread_set_caps_of_state_trivial
         thread_set_arch_caps_trivial
         thread_set_only_idle
         thread_set_cap_refs_in_kernel_window
         thread_set_valid_ioc_trivial
         valid_ioports_lift
         thread_set_cap_refs_respects_device_region
         thread_set_valid_replies_trivial
         thread_set_fault_tcbs_valid_states_trivial
      | simp add: ran_tcb_cap_cases invs_def valid_state_def valid_pspace_def
      | rule conjI
      | erule disjE)+

lemma as_user_valid_cap[wp]:
  "\<lbrace>valid_cap c\<rbrace> as_user a b \<lbrace>\<lambda>rv. valid_cap c\<rbrace>"
  by (wp valid_cap_typ)

crunches sched_context_unbind_tcb, sched_context_bind_tcb
  for valid_cap[wp]: "valid_cap c"
  and cte_wp_at[wp]: "cte_wp_at P p"
  and caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"
  and no_cap_to_obj_with_diff_ref[wp]: "no_cap_to_obj_with_diff_ref c S"
  (rule: abs_typ_at_lifts no_cap_to_obj_with_diff_ref_lift
   ignore: set_tcb_obj_ref)

schematic_goal rec_del_CTEDeleteCall:
  "rec_del (CTEDeleteCall slot True) = ?X"
  by (rule ext) simp

schematic_goal rec_del_FinaliseSlot:
  "rec_del (FinaliseSlotCall slot True) = ?X"
  by (rule ext) simp

lemma finalise_cap_ep:
  "\<lbrace>cte_wp_at P p and K (slot \<noteq> p \<and> is_ep_cap cap)\<rbrace>
  finalise_cap cap is_final \<lbrace>\<lambda>rv s. cte_wp_at P p s \<and> fst rv = NullCap \<and> slot \<noteq> p\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (clarsimp simp: is_cap_simps)
  apply (wpsimp simp: comp_def)
  done

lemma cap_delete_ep:
  "\<lbrace>cte_wp_at valid_fault_handler slot and cte_wp_at P p and K (slot \<noteq> p)\<rbrace>
    cap_delete slot
   \<lbrace>\<lambda>_. cte_wp_at P p\<rbrace>, -"
  apply (simp add: cap_delete_def rec_del_CTEDeleteCall)
  apply (subst rec_del_FinaliseSlot)
  apply (simp cong: if_cong)
  apply (wp empty_slot_cte_wp_elsewhere|wpc)+
       apply (rule hoare_FalseE_R) (* `else` case will not be taken *)
      apply wpsimp+
     apply (rule hoare_strengthen_post, rule finalise_cap_ep[where P=P and p=p and slot=slot], clarsimp)
    apply (wpsimp wp: get_cap_wp)+
  apply (simp add: cte_wp_at_caps_of_state valid_fault_handler_def)
  done

lemma checked_insert_cte_wp_at_weak:
  "\<lbrace>cte_wp_at P p and K (p \<noteq> (target, ref) \<and> (\<forall>c. P c \<longrightarrow> \<not>is_untyped_cap c))\<rbrace>
     check_cap_at new_cap src_slot
      (check_cap_at (cap.ThreadCap target) slot
       (cap_insert new_cap src_slot (target, ref))) \<lbrace>\<lambda>rv. cte_wp_at P p\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (wpsimp wp: get_cap_wp cap_insert_weak_cte_wp_at2 simp: check_cap_at_def)
  done

lemma install_tcb_cap_cte_wp_at_ep:
  "\<lbrace>cte_wp_at valid_fault_handler (target, tcb_cnode_index n) and cte_wp_at P p and
    K (p \<noteq> (target, tcb_cnode_index n) \<and> (\<forall>c. P c \<longrightarrow> \<not>is_untyped_cap c))\<rbrace>
   install_tcb_cap target slot n slot_opt
   \<lbrace>\<lambda>rv. cte_wp_at P p\<rbrace>, -"
  apply (simp add: install_tcb_cap_def)
  by (wpsimp wp: checked_insert_cte_wp_at_weak cap_delete_ep hoare_vcg_const_imp_lift_R)

lemma tcb_ep_slot_cte_wp_at:
  "\<lbrakk> invs s; tcb_at t s; slot = 3 \<or> slot = 4 \<rbrakk> \<Longrightarrow>
  cte_wp_at valid_fault_handler (t, tcb_cnode_index slot) s"
  apply (rule pred_tcb_cap_wp_at)
     apply (fastforce simp: tcb_at_st_tcb_at tcb_at_typ[symmetric])
    apply fastforce
   apply (fastforce simp: tcb_cap_cases_def)
  apply (fastforce simp: tcb_cap_valid_def st_tcb_at_def obj_at_def is_tcb)
  done

lemmas tcb_ep_slot_cte_wp_ats =
  tcb_ep_slot_cte_wp_at[where slot=3, simplified]
  tcb_ep_slot_cte_wp_at[where slot=4, simplified]

lemma tcb_cap_valid_ep_strgs:
  "valid_fault_handler cap \<longrightarrow> tcb_cap_valid cap (t, tcb_cnode_index 3) s"
  "valid_fault_handler cap \<longrightarrow> tcb_cap_valid cap (t, tcb_cnode_index 4) s"
  by (auto simp: tcb_cap_valid_def st_tcb_at_def obj_at_def is_tcb)

crunches install_tcb_cap
  for valid_cap[wp]: "valid_cap cap"
  and cte_at[wp]: "cte_at p"
  and typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  and cur_thread[wp]: "(\<lambda>s. P (cur_thread s))"
  (wp: crunch_wps preemption_point_inv check_cap_inv simp: crunch_simps)

crunch typ_at[wp]: reorder_ntfn, reorder_ep, set_priority "\<lambda>s. P (typ_at T p s)"
  (wp: crunch_wps simp: crunch_simps)

crunches
  install_tcb_cap, sched_context_unbind_tcb, sched_context_bind_tcb, set_priority, thread_set
  for cap_table_at[wp]: "cap_table_at bits p"
  and tcb_at[wp]: "\<lambda>s. P (tcb_at p s)"
  (wp: cap_table_at_typ_at tcb_at_typ_at' crunch_wps)

crunch ex_nonz_cap_to[wp]: unbind_notification "ex_nonz_cap_to t"
 (wp: maybeM_inv ignore: set_tcb_obj_ref)

lemma sbn_has_reply[wp]:
  "\<lbrace>\<lambda>s. P (has_reply_cap t s)\<rbrace> set_tcb_obj_ref tcb_bound_notification_update tcb ntfnptr \<lbrace>\<lambda>rv s. P (has_reply_cap t s)\<rbrace>"
  apply (simp add: has_reply_cap_def cte_wp_at_caps_of_state)
  apply (wp)
  done

lemma ssc_has_reply[wp]:
  "\<lbrace>\<lambda>s. P (has_reply_cap t s)\<rbrace> set_tcb_obj_ref tcb_sched_context_update tcb scptr \<lbrace>\<lambda>rv s. P (has_reply_cap t s)\<rbrace>"
  apply (simp add: has_reply_cap_def cte_wp_at_caps_of_state)
  apply (wp)
  done

lemma syt_has_reply[wp]:
  "\<lbrace>\<lambda>s. P (has_reply_cap t s)\<rbrace> set_tcb_obj_ref tcb_yield_to_update tcb scptr \<lbrace>\<lambda>rv s. P (has_reply_cap t s)\<rbrace>"
  apply (simp add: has_reply_cap_def cte_wp_at_caps_of_state)
  apply (wp)
  done

lemma set_set_simple_ko_has_reply[wp]:
  "\<lbrace>\<lambda>s. P (has_reply_cap t s)\<rbrace> set_simple_ko f ntfnptr ntfn \<lbrace>\<lambda>rv s. P (has_reply_cap t s)\<rbrace>"
  by (simp add: has_reply_cap_def cte_wp_at_caps_of_state, wp)

lemma unbind_notification_has_reply[wp]:
  "\<lbrace>\<lambda>s. P (has_reply_cap t s)\<rbrace> unbind_notification t' \<lbrace>\<lambda>rv s. P (has_reply_cap t s)\<rbrace>"
  apply (simp add: unbind_notification_def has_reply_cap_def cte_wp_at_caps_of_state)
  apply (rule hoare_seq_ext[OF _ gbn_sp])
  apply (case_tac ntfnptr; wpsimp simp: maybeM_def)
  done

lemma set_ntfn_bound_some_tcb_valid_objs[wp]:
  "\<lbrace>valid_objs and bound_tcb_at ((=) None) tcbptr and
    obj_at (\<lambda>ko. \<exists>ntfn. ko = Notification ntfn \<and> (ntfn_bound_tcb ntfn = None) \<and>
                 (\<forall>q. ntfn_obj ntfn \<noteq> WaitingNtfn q)) ntfnptr\<rbrace>
   set_ntfn_obj_ref ntfn_bound_tcb_update ntfnptr (Some tcbptr) \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (wpsimp simp: update_sk_obj_ref_def obj_at_def wp: get_simple_ko_wp)
  apply (erule (1) valid_objsE)
  apply (clarsimp simp: valid_obj_def valid_ntfn_def pred_tcb_at_tcb_at split: ntfn.splits)
  done

lemma set_ntfn_bound_tcb_some_if_live_then_nonz_cap [wp]:
  "\<lbrace>if_live_then_nonz_cap and ex_nonz_cap_to ntfnptr\<rbrace>
   set_ntfn_obj_ref ntfn_bound_tcb_update ntfnptr (Some tcbptr) \<lbrace>\<lambda>_. if_live_then_nonz_cap\<rbrace>"
  by (wpsimp simp: update_sk_obj_ref_def wp: get_simple_ko_wp)

lemma set_ntfn_obj_ref_some_state_refs[wp]:
  "\<lbrace>\<lambda>s. P ((state_refs_of s) (ntfnptr := state_refs_of s ntfnptr \<union> {(tcbptr, NTFNBound)})) \<and>
        obj_at (\<lambda>ko. \<exists>ntfn. ko = Notification ntfn \<and> ntfn_bound_tcb ntfn = None \<and>
                     (\<forall>q. ntfn_obj ntfn \<noteq> WaitingNtfn q)) ntfnptr s\<rbrace>
   set_ntfn_obj_ref ntfn_bound_tcb_update ntfnptr (Some tcbptr) \<lbrace>\<lambda>_ s. P (state_refs_of s)\<rbrace>"
  apply (wpsimp simp: update_sk_obj_ref_def wp: get_simple_ko_wp)
  apply (clarsimp simp: obj_at_def)
  apply (erule rsubst[of P])
  apply (rule ext)
  apply clarsimp
  apply (rename_tac ntfn)
  apply (case_tac "ntfn_obj ntfn"; simp add: state_refs_of_def)
  done

lemma set_ntfn_obj_ref_valid_replies[wp]:
  "set_ntfn_obj_ref update ref new \<lbrace> valid_replies_pred P \<rbrace>"
  by (wpsimp wp: valid_replies_lift)

lemma set_ntfn_obj_ref_cur_sc_tcb[wp]:
  "set_ntfn_obj_ref update ref new \<lbrace>cur_sc_tcb\<rbrace>"
  by (wpsimp simp: update_sk_obj_ref_def)

lemma bind_notification_invs:
  "\<lbrace>bound_tcb_at ((=) None) tcbptr
    and obj_at (\<lambda>ko. \<exists>ntfn. ko = Notification ntfn \<and> ntfn_bound_tcb ntfn = None
                           \<and> (\<forall>q. ntfn_obj ntfn \<noteq> WaitingNtfn q)) ntfnptr
    and invs
    and ex_nonz_cap_to ntfnptr
    and ex_nonz_cap_to tcbptr\<rbrace>
     bind_notification tcbptr ntfnptr
   \<lbrace>\<lambda>_. invs\<rbrace>"
  supply if_weak_cong[cong del]
  apply (simp add: bind_notification_def invs_def valid_state_def valid_pspace_def)
  apply (wpsimp wp: ntfn_at_typ_at update_sk_obj_ref_typ_at valid_irq_node_typ valid_ioports_lift)
  apply (clarsimp simp: obj_at_def pred_tcb_at_def is_ntfn)
  apply (rule conjI, clarsimp simp: obj_at_def)
  apply clarsimp
  apply (rule conjI)
   apply (erule delta_sym_refs)
    apply (fastforce split: if_split_asm)
   apply (fastforce simp: state_refs_of_def pred_tcb_at_def2 obj_at_def get_refs_def2
                   split: if_split_asm)
  apply (clarsimp simp: idle_no_ex_cap)
  done

lemma (in Tcb_AI) tcbinv_invs:
  "\<lbrace>(invs::'state_ext state\<Rightarrow>bool) and tcb_inv_wf ti\<rbrace>
     invoke_tcb ti
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (case_tac ti, simp_all only:)
         apply ((wp writereg_invs readreg_invs copyreg_invs tcc_invs tcs_invs suspend_invs
                | simp add: valid_idle_def
                | clarsimp simp: invs_def valid_state_def valid_pspace_def
                          dest!: idle_no_ex_cap
                          split: option.split
                | rule conjI)+)[7]
   apply (rename_tac option)
   apply (case_tac option, simp_all)
    apply (rule hoare_pre)
     apply ((wp unbind_notification_invs get_simple_ko_wp | simp)+)[2]
   apply (wp bind_notification_invs)
   apply clarsimp
  apply wpsimp
  done

lemma range_check_inv[wp]:
  "\<lbrace>P\<rbrace> range_check a b c \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp add: range_check_def)
  apply (rule hoare_pre, wp)
  apply simp
  done

lemma decode_readreg_inv:
  "\<lbrace>P\<rbrace> decode_read_registers args (cap.ThreadCap t) \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (rule hoare_pre)
   apply (simp add: decode_read_registers_def whenE_def | rule conjI | clarsimp
          | wp (once) | wpcw)+
  done

lemma decode_writereg_inv:
  "\<lbrace>P\<rbrace> decode_write_registers args (cap.ThreadCap t) \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (rule hoare_pre)
   apply (simp   add: decode_write_registers_def whenE_def
           split del: if_split
          | wp (once) | wpcw)+
  done

lemma decode_copyreg_inv:
  "\<lbrace>P\<rbrace> decode_copy_registers args (cap.ThreadCap t) extras \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (rule hoare_pre)
   apply (simp   add: decode_copy_registers_def whenE_def
           split del: if_split
          | wp (once) | wpcw)+
  done

lemma decode_set_tls_base_inv:
  "\<lbrace>P\<rbrace> decode_set_tls_base args (cap.ThreadCap t) \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (rule hoare_pre)
   apply (simp   add: decode_set_tls_base_def whenE_def
           split del: if_split
          | wp (once) | wpcw)+
  done

lemma (in Tcb_AI) decode_readreg_wf:
  "\<lbrace>invs and tcb_at t and ex_nonz_cap_to t\<rbrace>
   decode_read_registers args (cap.ThreadCap t)
   \<lbrace>tcb_inv_wf\<rbrace>,-"
  apply (simp add: decode_read_registers_def whenE_def
             cong: list.case_cong)
  apply (rule hoare_pre)
   apply (wp | wpc)+
  apply simp
  done

lemma (in Tcb_AI) decode_writereg_wf:
  "\<lbrace>invs and tcb_at t and ex_nonz_cap_to t\<rbrace>
     decode_write_registers args (cap.ThreadCap t)
   \<lbrace>tcb_inv_wf\<rbrace>,-"
  apply (simp add: decode_write_registers_def whenE_def
             cong: list.case_cong)
  apply (rule hoare_pre)
   apply (wp | wpc)+
  apply simp
  done

lemma (in Tcb_AI) decode_copyreg_wf:
  "\<lbrace>invs and tcb_at t and ex_nonz_cap_to t
       and (\<lambda>s. \<forall>x \<in> set extras. s \<turnstile> x
                       \<and> (\<forall>y \<in> zobj_refs x. ex_nonz_cap_to y s))\<rbrace>
     decode_copy_registers args (cap.ThreadCap t) extras
   \<lbrace>tcb_inv_wf\<rbrace>,-"
  apply (simp add: decode_copy_registers_def whenE_def
             cong: list.case_cong split del: if_split)
  apply (rule hoare_pre)
   apply (wp | wpc)+
  apply (clarsimp simp: valid_cap_def[where c="cap.ThreadCap t" for t])
  done

lemma (in Tcb_AI) decode_set_tls_base_wf:
  "\<lbrace>invs and tcb_at t and ex_nonz_cap_to t\<rbrace>
     decode_set_tls_base args (cap.ThreadCap t)
   \<lbrace>tcb_inv_wf\<rbrace>,-"
  apply (simp add: decode_set_tls_base_def whenE_def
             cong: list.case_cong split del: if_split)
  apply wpsimp
  done

declare alternativeE_wp[wp]
declare alternativeE_R_wp[wp]

(*FIXME Move up*)
lemma OR_choice_E_weak_wp: "\<lbrace>P\<rbrace> f \<sqinter> g \<lbrace>Q\<rbrace>,- \<Longrightarrow> \<lbrace>P\<rbrace> OR_choice b f g \<lbrace>Q\<rbrace>,-"
  apply (simp add: validE_R_def validE_def OR_choice_weak_wp)
  done

lemma OR_choiceE_E_weak_wp: "\<lbrace>P\<rbrace> f \<sqinter> g \<lbrace>Q\<rbrace>,- \<Longrightarrow> \<lbrace>P\<rbrace> OR_choiceE b f g \<lbrace>Q\<rbrace>,-"
  apply (simp add: validE_R_def validE_def OR_choiceE_weak_wp)
  done

crunch inv: check_prio "P"
  (simp: crunch_simps)

lemma check_prio_wp:
  "\<lbrace>\<lambda>s. mcpriority_tcb_at (\<lambda>mcp. prio \<le> ucast mcp) auth s \<longrightarrow> Q s\<rbrace> check_prio prio auth \<lbrace>\<lambda>_. Q\<rbrace>, -"
  apply (clarsimp simp: check_prio_def)
  apply (wp thread_get_mcpriority_wp whenE_throwError_wp)
  apply (intro allI impI, elim mp pred_tcb_weakenE)
  apply fastforce
  done

lemma check_prio_wp_weak:
  "\<lbrace>\<lambda>s. mcpriority_tcb_at (\<lambda>mcp. ucast prio \<le> mcp) auth s \<longrightarrow> Q s\<rbrace> check_prio prio auth \<lbrace>\<lambda>_. Q\<rbrace>, -"
  apply (wp check_prio_wp)
  apply (intro allI impI, elim mp pred_tcb_weakenE)
  apply (simp add: le_ucast_ucast_le)
  done

lemma check_prio_lt_ct:
  "\<lbrace>\<top>\<rbrace> check_prio prio auth \<lbrace>\<lambda>rv s. mcpriority_tcb_at (\<lambda>mcp. prio \<le> ucast mcp) auth s\<rbrace>, -"
  by (wpsimp wp: check_prio_wp)

lemma check_prio_lt_ct_weak:
  "\<lbrace>\<top>\<rbrace> check_prio prio auth \<lbrace>\<lambda>rv s. mcpriority_tcb_at (\<lambda>mcp. ucast prio \<le> mcp) auth s\<rbrace>, -"
  by (wpsimp wp: check_prio_wp_weak)

lemma (in Tcb_AI) decode_set_priority_wf[wp]:
  "\<lbrace>invs and tcb_at t and ex_nonz_cap_to t\<rbrace>
        decode_set_priority args (ThreadCap t) slot excs \<lbrace>tcb_inv_wf\<rbrace>, -"
  by (wpsimp simp: decode_set_priority_def wp: check_prio_wp_weak whenE_throwError_wp)

lemma (in Tcb_AI) decode_set_mcpriority_wf[wp]:
  "\<lbrace>invs and tcb_at t and ex_nonz_cap_to t\<rbrace>
        decode_set_mcpriority args (ThreadCap t) slot excs \<lbrace>tcb_inv_wf\<rbrace>, -"
  by (wpsimp simp: decode_set_mcpriority_def wp: check_prio_wp_weak whenE_throwError_wp)

lemma check_handler_ep_inv[wp]:
  "\<lbrace>P\<rbrace> check_handler_ep n cap_slot \<lbrace>\<lambda>_. P\<rbrace>"
  unfolding check_handler_ep_def unlessE_def by wpsimp

lemma check_handler_ep_wpE[wp]:
  "\<lbrace>\<lambda>s. valid_fault_handler (fst cap_slot) \<longrightarrow> P cap_slot s\<rbrace> check_handler_ep n cap_slot \<lbrace>P\<rbrace>, -"
  unfolding check_handler_ep_def unlessE_def by wpsimp

lemma decode_update_sc_inv[wp]:
  "\<lbrace>P\<rbrace> decode_update_sc cap slot sc_cap \<lbrace>\<lambda>_. P\<rbrace>"
  unfolding decode_update_sc_def is_blocked_def by (wpsimp wp: hoare_drop_imps)

context Tcb_AI
begin

lemma decode_set_sched_params_wf[wp]:
  "\<lbrace>invs and tcb_at t and ex_nonz_cap_to t and
    cte_at slot and ex_cte_cap_to slot and
    (\<lambda>s. \<forall>x \<in> set excaps. s \<turnstile> fst x \<and> real_cte_at (snd x) s
                          \<and> cte_wp_at ((=) (fst x)) (snd x) s
                          \<and> (\<forall>y \<in> zobj_refs (fst x). ex_nonz_cap_to y s)
                          \<and> ex_cte_cap_to (snd x) s
                          \<and> no_cap_to_obj_dr_emp (fst x) s)\<rbrace>
   decode_set_sched_params args (ThreadCap t) slot excaps
   \<lbrace>tcb_inv_wf\<rbrace>, -"
  unfolding decode_set_sched_params_def decode_update_sc_def is_blocked_def
  apply (wpsimp simp: get_tcb_obj_ref_def
                wp: check_prio_wp_weak whenE_throwError_wp thread_get_wp gts_wp
                split_del: if_split)
  apply (clarsimp simp: split_paired_Ball)
  apply (rule conjI; clarsimp)
  apply (clarsimp simp: obj_at_def is_tcb pred_tcb_at_def is_cap_simps sc_tcb_sc_at_def
                        sc_at_ppred_def)
  apply (rule conjI, fastforce)
  apply (subgoal_tac "excaps ! Suc 0 \<in> set excaps")
   prefer 2
   apply fastforce
  apply (cases "excaps ! Suc 0")
  apply (clarsimp)
  done

end

definition
  is_thread_control_caps :: "tcb_invocation \<Rightarrow> bool"
where
 "is_thread_control_caps tinv \<equiv> case tinv of tcb_invocation.ThreadControlCaps a b c d e f g \<Rightarrow> True
 | _ \<Rightarrow> False"

definition
  is_thread_control_sched :: "tcb_invocation \<Rightarrow> bool"
where
 "is_thread_control_sched tinv \<equiv> case tinv of tcb_invocation.ThreadControlSched _ _ _ _ _ _ \<Rightarrow> True
 | _ \<Rightarrow> False"

primrec (nonexhaustive)
  thread_control_target :: "tcb_invocation \<Rightarrow> machine_word"
where
  "thread_control_target (tcb_invocation.ThreadControlCaps a _ _ _ _ _ _) = a"
| "thread_control_target (tcb_invocation.ThreadControlSched a _ _ _ _ _) = a"

lemma is_thread_control_caps_true[simp]:
  "is_thread_control_caps (tcb_invocation.ThreadControlCaps a b c d e f g)"
  by (simp add: is_thread_control_caps_def)

lemma is_thread_control_caps_def2:
  "is_thread_control_caps tinv =
    (\<exists>target slot fh th prio mcp croot vroot buffer sc.
        tinv = tcb_invocation.ThreadControlCaps target slot fh th croot vroot buffer)"
  by (cases tinv, simp_all add: is_thread_control_caps_def)

lemma decode_set_priority_is_tc[wp]:
  "\<lbrace>\<top>\<rbrace> decode_set_priority args cap slot excs \<lbrace>\<lambda>rv s. is_thread_control_sched rv\<rbrace>,-"
   by (wpsimp simp: decode_set_priority_def is_thread_control_sched_def)

lemma decode_set_priority_inv[wp]:
  "\<lbrace>P\<rbrace> decode_set_priority args cap slot excs \<lbrace>\<lambda>rv. P\<rbrace>"
  by (wpsimp simp: decode_set_priority_def wp: check_prio_inv whenE_inv)

lemma decode_set_mcpriority_inv[wp]:
  "\<lbrace>P\<rbrace> decode_set_mcpriority args cap slot excs \<lbrace>\<lambda>rv. P\<rbrace>"
  by (wpsimp simp: decode_set_mcpriority_def wp: check_prio_inv whenE_inv)

lemma decode_set_sched_params_inv[wp]:
  "\<lbrace>P\<rbrace> decode_set_sched_params args cap slot excs \<lbrace>\<lambda>rv. P\<rbrace>"
  by (wpsimp simp: decode_set_sched_params_def wp: check_prio_inv whenE_inv)

lemma derive_is_arch[wp]:
  "\<lbrace>\<lambda>s. is_arch_cap c\<rbrace> derive_cap slot c \<lbrace>\<lambda>rv s. rv \<noteq> NullCap \<longrightarrow> is_arch_cap rv\<rbrace>,-"
  apply (simp add: derive_cap_def cong: cap.case_cong)
  apply (rule hoare_pre)
   apply (wp arch_derive_is_arch | wpc | simp only: o_def is_arch_cap_def cap.simps)+
  apply fastforce
  done


lemma (in Tcb_AI) decode_set_ipc_wf[wp]:
  "\<lbrace>(invs::'state_ext state\<Rightarrow>bool) and tcb_at t and cte_at slot and ex_cte_cap_to slot
      and ex_nonz_cap_to t
      and (\<lambda>s. \<forall>x \<in> set excaps. s \<turnstile> fst x \<and> cte_at (snd x) s
                          \<and> ex_cte_cap_to (snd x) s
                          \<and> no_cap_to_obj_dr_emp (fst x) s)\<rbrace>
     decode_set_ipc_buffer args (cap.ThreadCap t) slot excaps
   \<lbrace>tcb_inv_wf\<rbrace>,-"
  supply if_weak_cong[cong del]
  apply (simp   add: decode_set_ipc_buffer_def whenE_def split_def
          split del: if_split)
  apply (rule hoare_pre, wp check_valid_ipc_buffer_wp)
     apply simp
     apply (wp derive_cap_valid_cap hoare_drop_imps)[1]
    apply wp+
  apply (clarsimp simp: neq_Nil_conv)
  done

lemma decode_set_ipc_is_tc[wp]:
  "\<lbrace>\<top>\<rbrace> decode_set_ipc_buffer args cap slot excaps \<lbrace>\<lambda>rv s. is_thread_control_caps rv\<rbrace>,-"
  supply if_weak_cong[cong del]
  apply (rule hoare_pre)
  apply (simp    add: decode_set_ipc_buffer_def split_def
           split del: if_split
            | wp)+
  apply fastforce?
  done

lemma slot_long_running_inv[wp]:
  "\<lbrace>P\<rbrace> slot_cap_long_running_delete ptr \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp add: slot_cap_long_running_delete_def)
  apply (wp | wpcw | simp add: is_final_cap_def)+
  done


lemma val_le_length_Cons:
  "n \<noteq> 0 \<Longrightarrow> (n \<le> length xs) = (\<exists>y ys. xs = y # ys \<and> (n - 1) \<le> length ys)"
  apply (cases xs, simp_all)
  apply (cases n, simp_all)
  done

lemma derive_cap_cnode[wp]:
  "\<lbrace>\<lambda>s. is_cnode_cap cap\<rbrace> derive_cap slot cap  \<lbrace>\<lambda>rv s. is_cnode_cap rv\<rbrace>, -"
  by (wpsimp simp: derive_cap_def) (auto intro: hoare_FalseE_R)

lemma decode_cv_space_inv[wp]:
  "\<lbrace>P\<rbrace> decode_cv_space args cap slot extras \<lbrace>\<lambda>rv. P\<rbrace>"
  unfolding decode_cv_space_def
  apply (wpsimp wp: hoare_drop_imps simp: comp_def split_del: if_split
         | rule valid_validE_E valid_validE_R)+
  done

lemma decode_cv_space_is_tc[wp]:
  "\<lbrace>\<top>\<rbrace> decode_cv_space args cap slot excs \<lbrace>\<lambda>rv s. is_thread_control_caps rv\<rbrace>,-"
  by (wpsimp simp: decode_cv_space_def simp_del: hoare_True_E_R split_del: if_split)

context Tcb_AI
begin

lemma (in Tcb_AI) decode_cv_space_wf[wp]:
  "\<lbrace>(invs::'state_ext state\<Rightarrow>bool)
          and tcb_at t and cte_at slot and ex_cte_cap_to slot
          and ex_nonz_cap_to t
          and (\<lambda>s. \<forall>x \<in> set cv_caps. s \<turnstile> fst x \<and> real_cte_at (snd x) s
                                     \<and> ex_cte_cap_to (snd x) s
                                     \<and> no_cap_to_obj_dr_emp (fst x) s)
          and K (2 \<le> length args \<and> 2 \<le> length cv_caps)\<rbrace>
  decode_cv_space (take 2 args) (ThreadCap t) slot cv_caps
  \<lbrace>tcb_inv_wf\<rbrace>, -"
  apply (simp add: decode_cv_space_def split del: if_split)
  apply (wpsimp wp: derive_cap_valid_cap simp: o_def split_del: if_split
         | rule hoare_drop_imps)+
  apply (simp add: update_cap_data_validI
                   no_cap_to_obj_with_diff_ref_update_cap_data
              del: length_greater_0_conv)
  done

lemma tcb_inv_set_space_strg:
  "\<lbrakk> tcb_inv_wf rv s; is_thread_control_caps rv; cte_at slot s; ex_cte_cap_to slot s;
     tcb_inv_wf (ThreadControlCaps t slot fh None None None None) s \<rbrakk> \<Longrightarrow>
  tcb_inv_wf (ThreadControlCaps t slot fh None (tc_new_croot rv) (tc_new_vroot rv) None ) s"
  by (cases rv; simp add: is_thread_control_caps_def)

lemma decode_set_space_wf[wp]:
  "\<lbrace>(invs::'state_ext state\<Rightarrow>bool)
    and tcb_at t and cte_at slot and ex_cte_cap_to slot
    and ex_nonz_cap_to t
    and (\<lambda>s. \<forall>x \<in> set extras. s \<turnstile> fst x \<and> real_cte_at (snd x) s
                               \<and> cte_wp_at ((=) (fst x)) (snd x) s
                               \<and> ex_cte_cap_to (snd x) s
                               \<and> no_cap_to_obj_dr_emp (fst x) s)\<rbrace>
     decode_set_space args (ThreadCap t) slot extras
   \<lbrace>tcb_inv_wf\<rbrace>,-"
  unfolding decode_set_space_def
  apply (wpsimp wp: hoare_vcg_const_imp_lift_R simp_del: tcb_inv_wf.simps
         | strengthen tcb_inv_set_space_strg
         | rule hoare_drop_imps)+
  apply (clarsimp simp: valid_fault_handler_def real_cte_at_cte)
  apply (prop_tac "set (take 2 (drop (Suc 0) extras)) \<subseteq> set extras")
   apply (meson basic_trans_rules(23) set_drop_subset set_take_subset)
  apply (intro conjI)
        apply blast
       apply fastforce
      apply (metis gr0I nth_mem zero_less_numeral crunch_simps(1) gr0I nth_mem rel_simps(51))+
  done

end

lemma decode_set_space_inv[wp]:
  "\<lbrace>P\<rbrace> decode_set_space args cap slot extras \<lbrace>\<lambda>rv. P\<rbrace>"
  unfolding decode_set_space_def
  by (wpsimp wp: hoare_drop_imps)

lemma decode_set_space_is_tc[wp]:
  "\<lbrace>\<top>\<rbrace> decode_set_space args cap slot extras \<lbrace>\<lambda>rv s. is_thread_control_caps rv\<rbrace>,-"
  apply (simp add: decode_set_space_def)
  apply (wp | simp only: is_thread_control_caps_true)+
  apply simp
  done

lemma decode_set_mcpriority_is_tc[wp]:
  "\<lbrace>\<top>\<rbrace> decode_set_mcpriority args cap slot excs \<lbrace>\<lambda>rv s. is_thread_control_sched rv\<rbrace>,-"
   by (wpsimp simp: decode_set_mcpriority_def is_thread_control_sched_def)

lemma decode_set_space_target[wp]:
  "\<lbrace>\<lambda>s. P (obj_ref_of cap)\<rbrace> decode_set_space args cap slot extras \<lbrace>\<lambda>rv s. P (thread_control_target rv)\<rbrace>,-"
  apply (simp add: decode_set_space_def)
  apply (wp | simp only: thread_control_target.simps)+
  apply simp
  done

(* FIXME: move *)
lemma boring_simp[simp]:
  "(if x then True else False) = x" by simp

context Tcb_AI
begin

lemma decode_cv_space_target[wp]:
  "\<lbrace>\<top>\<rbrace> decode_cv_space args (ThreadCap t) slot caps \<lbrace>\<lambda>rv s. thread_control_target rv = t\<rbrace>, -"
  unfolding decode_cv_space_def
  by (wpsimp split_del: if_split simp_del: hoare_True_E_R)

lemma decode_tcb_conf_wf[wp]:
  "\<lbrace>(invs::'state_ext state\<Rightarrow>bool)
         and tcb_at t and cte_at slot and ex_cte_cap_to slot
         and ex_nonz_cap_to t
         and (\<lambda>s. \<forall>x \<in> set extras. s \<turnstile> fst x \<and> real_cte_at (snd x) s
                                   \<and> ex_cte_cap_to (snd x) s
                                   \<and> t \<noteq> fst (snd x)
                                   \<and> no_cap_to_obj_dr_emp (fst x) s)\<rbrace>
   decode_tcb_configure args (cap.ThreadCap t) slot extras
   \<lbrace>tcb_inv_wf\<rbrace>,-"
  apply (clarsimp simp add: decode_tcb_configure_def)
  apply wp
      apply (rule_tac Q'="\<lambda>set_space s. tcb_inv_wf set_space s \<and> tcb_inv_wf set_params s
                                   \<and> is_thread_control_caps set_space \<and> is_thread_control_caps set_params
                                   \<and> thread_control_target set_space = t
                                   \<and> cte_at slot s \<and> ex_cte_cap_to slot s"
                      in hoare_post_imp_R)
       apply wpsimp
      apply (subst (asm) is_thread_control_caps_def2)
      apply (subst (asm) is_thread_control_caps_def2)
      apply clarsimp
     apply (wpsimp simp: real_cte_at_cte)+
  apply (fastforce dest!: in_set_takeD)
  done

lemma decode_tcb_conf_inv[wp]:
  "\<lbrace>P::'state_ext state \<Rightarrow> bool\<rbrace> decode_tcb_configure args cap slot extras \<lbrace>\<lambda>rv. P\<rbrace>"
  supply if_weak_cong[cong del]
  apply (clarsimp simp add: decode_tcb_configure_def decode_update_sc_def Let_def whenE_def
                 split del: if_split)
  apply (wpsimp wp: hoare_drop_imps)
  done

end

lemmas derived_cap_valid = derive_cap_valid_cap

lemma derived_cap_cnode_valid:
  "\<lbrace>\<lambda>s. is_cnode_cap c \<longrightarrow> valid_cap c s\<rbrace>
  derive_cap sl c
  \<lbrace>\<lambda>rv s. is_cnode_cap rv \<longrightarrow> valid_cap rv s\<rbrace>,-"
  apply (cases c)
          apply (simp_all add: derive_cap_def validE_R_def return_def
                               validE_def valid_def returnOk_def)
   apply (clarsimp simp: in_monad)
  apply (clarsimp simp add: liftME_def in_monad)
  apply (frule use_valid[OF _ arch_derive_is_arch[simplified validE_def validE_R_def]], simp)
  apply (clarsimp simp: is_cap_simps)
  done


crunch inv[wp]:  decode_unbind_notification P
(simp: whenE_def)

lemma decode_bind_notification_inv[wp]:
  "\<lbrace>P\<rbrace> decode_bind_notification cap excaps \<lbrace>\<lambda>_. P\<rbrace>"
  unfolding decode_bind_notification_def
  by (wpsimp wp: get_simple_ko_wp gbn_wp'
             simp: whenE_def if_apply_def2
             split_del: if_split)

crunch inv[wp]: decode_set_timeout_ep P

lemma (in Tcb_AI) decode_tcb_inv_inv:
  "\<lbrace>P::'state_ext state \<Rightarrow> bool\<rbrace> decode_tcb_invocation label args (cap.ThreadCap t) slot extras \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp add: decode_tcb_invocation_def Let_def decode_set_tls_base_def
             cong: if_cong
        split del: if_split)
  apply (rule hoare_pre)
   apply (wpc
        | wp decode_readreg_inv decode_writereg_inv
             decode_copyreg_inv decode_tcb_conf_inv
             decode_set_tls_base_inv)+
  apply simp
  done

lemma real_cte_at_not_tcb_at:
  "real_cte_at (x, y) s \<Longrightarrow> \<not> tcb_at x s"
  by (clarsimp simp: obj_at_def is_tcb is_cap_table)

context Tcb_AI begin
lemma decode_bind_notification_wf:
  "\<lbrace>invs and tcb_at t and ex_nonz_cap_to t
       and (\<lambda>s. \<forall>x \<in> set extras. s \<turnstile> (fst x) \<and> (\<forall>y \<in> zobj_refs (fst x). ex_nonz_cap_to y s))\<rbrace>
     decode_bind_notification (cap.ThreadCap t) extras
   \<lbrace>tcb_inv_wf\<rbrace>,-"
  apply (simp add: decode_bind_notification_def whenE_def
             cong: list.case_cong split del: if_split)
  apply (rule hoare_pre)
   apply (wp get_simple_ko_wp gbn_wp' | wpc)+
  apply (fastforce simp: valid_cap_def[where c="cap.ThreadCap t" for t] is_ntfn invs_def
                    valid_state_def valid_pspace_def
             elim!: obj_at_weakenE
             dest!: idle_no_ex_cap hd_in_set)
  done

lemma decode_unbind_notification_wf:
  "\<lbrace>invs and tcb_at t and ex_nonz_cap_to t\<rbrace>
     decode_unbind_notification (cap.ThreadCap t)
   \<lbrace>tcb_inv_wf\<rbrace>,-"
  apply (simp add: decode_unbind_notification_def)
  apply (rule hoare_pre)
   apply (wp gbn_wp' | wpc)+
  apply clarsimp
  done

lemma decode_set_timeout_ep_tc_inv[wp]:
  "\<lbrace>(invs::'state_ext state\<Rightarrow>_)
          and tcb_at t and ex_nonz_cap_to t
          and cte_at slot and ex_cte_cap_to slot
          and (\<lambda>s. \<forall>x \<in> set extras. s \<turnstile> fst x \<and> real_cte_at (snd x) s
                          \<and> cte_wp_at ((=) (fst x)) (snd x) s
                          \<and> ex_cte_cap_to (snd x) s
                          \<and> no_cap_to_obj_dr_emp (fst x) s)\<rbrace>
  decode_set_timeout_ep (ThreadCap t) slot extras \<lbrace>tcb_inv_wf\<rbrace>, -"
  unfolding decode_set_timeout_ep_def
  by (wpsimp simp: neq_Nil_conv)

lemma decode_tcb_inv_wf:
  "\<lbrace>invs and tcb_at t and ex_nonz_cap_to t
         and cte_at slot and ex_cte_cap_to slot
         and (\<lambda>(s::'state_ext state). \<forall>x \<in> set extras. real_cte_at (snd x) s \<and> s \<turnstile> fst x
                                 \<and> cte_wp_at ((=) (fst x)) (snd x) s
                                 \<and> ex_cte_cap_to (snd x) s
                                 \<and> (\<forall>y \<in> zobj_refs (fst x). ex_nonz_cap_to y s)
                                 \<and> no_cap_to_obj_dr_emp (fst x) s)\<rbrace>
      decode_tcb_invocation label args (cap.ThreadCap t) slot extras
   \<lbrace>tcb_inv_wf\<rbrace>,-"
  apply (simp add: decode_tcb_invocation_def Let_def cong: if_cong split del: if_split)
  apply (rule hoare_vcg_precond_impE_R)
   apply wpc
   apply (wp decode_tcb_conf_wf decode_readreg_wf
             decode_writereg_wf decode_copyreg_wf
             decode_bind_notification_wf decode_unbind_notification_wf
             decode_set_priority_wf decode_set_tls_base_wf)+
  apply (clarsimp simp: real_cte_at_cte)
  apply (fastforce simp: real_cte_at_not_tcb_at)
  done
end

lemma set_domain_invs[wp]:
  "set_domain t d \<lbrace>invs\<rbrace>"
  supply if_weak_cong[cong del]
  by (simp add: set_domain_def | wp)+

lemma invoke_domain_invs:
  "\<lbrace>invs\<rbrace>
     invoke_domain t d
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (simp add: invoke_domain_def | wp)+

lemma set_domain_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace>
     set_domain t d
   \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  supply if_weak_cong[cong del]
  by (simp add: set_domain_def | wp)+

lemma invoke_domain_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace>
     invoke_domain t d
   \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by (simp add: invoke_domain_def | wp)+

lemma decode_domain_inv_inv:
  "\<lbrace>P\<rbrace>
     decode_domain_invocation label args excs
   \<lbrace>\<lambda>rv. P\<rbrace>"
  by (simp add: decode_domain_invocation_def whenE_def split del: if_split | wp hoare_vcg_if_splitE | wpc)+

lemma decode_domain_inv_wf:
  "\<lbrace>valid_objs and valid_global_refs and
     (\<lambda>s. \<forall>x\<in>set excs. s \<turnstile> fst x) and
     (\<lambda>s. \<forall>x\<in>set excs. \<forall>r\<in>zobj_refs (fst x). ex_nonz_cap_to r s)\<rbrace>
     decode_domain_invocation label args excs
   \<lbrace>\<lambda>(t, d) s. tcb_at t s \<and> t \<noteq> idle_thread s\<rbrace>, -"
  apply (clarsimp simp: decode_domain_invocation_def whenE_def split del: if_split
        | wp hoare_vcg_if_splitE | wpc)+
  apply (erule ballE[where x="hd excs"])
   apply (clarsimp simp: valid_cap_simps)
   apply (drule(1) idle_no_ex_cap)
   apply (erule ballE[where x="hd excs"])
    apply simp+
    done

lemma tcb_bound_refs_no_NTFNBound:
  "(x, NTFNBound) \<notin> get_refs TCBBound a"
  by (simp add: get_refs_def split: option.splits)

lemma tcb_st_refs_of_no_NTFNBound:
  "(x, NTFNBound) \<notin> tcb_st_refs_of z"
  by (simp add: tcb_st_refs_of_def split: thread_state.splits)

lemma tcb_not_in_state_refs_of_tcb:
  "tcb_at a s \<Longrightarrow> (a, NTFNBound) \<notin> state_refs_of s a"
  apply (clarsimp simp: tcb_at_def obj_at_def is_tcb_def)
  apply (case_tac ko)
  apply simp_all
  apply (clarsimp simp: state_refs_of_def tcb_st_refs_of_def get_refs_def)
  apply (erule disjE)
  apply (rename_tac tcb_ext)
  apply (case_tac "tcb_state tcb_ext")
  apply (simp_all split: if_split_asm)
  apply (simp split: option.splits)
  done

lemma set_mcpriority_mc_priority_tcb_at_cases:
  "\<lbrace>\<lambda>s. (t = t' \<longrightarrow> P a) \<and> (t \<noteq> t' \<longrightarrow> mcpriority_tcb_at P t' s)\<rbrace>
   set_mcpriority t a
   \<lbrace>\<lambda>rv. mcpriority_tcb_at P t'\<rbrace>"
  by (wpsimp simp: set_mcpriority_def thread_set_def wp: set_object_wp)
     (fastforce simp: get_tcb_ko_at pred_tcb_at_def obj_at_def is_tcb)

lemma tcb_cap_cases_tcb_mcpriority:
  "\<forall>(getF, v)\<in>ran tcb_cap_cases.
         getF (tcb_mcpriority_update F tcb) = getF tcb"
  by (rule ball_tcb_cap_casesI, simp+)

crunches set_mcpriority
  for typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  and tcb_at[wp]: "\<lambda>s. P (tcb_at p s)"
  and cap_table_at[wp]: "cap_table_at bits p"
  and cte_wp_at[wp]: "cte_wp_at P p"
  and ex_nonz_cap_to[wp]: "ex_nonz_cap_to ref"
  and ct_in_state[wp]: "ct_in_state P"
  and sc_tcb_sc_at[wp]: "sc_tcb_sc_at P scptr"
  (wp: thread_set_cte_wp_at_trivial thread_set_cap_to tcb_at_typ_at
   simp: ran_tcb_cap_cases)

lemma set_mcpriority_st_tcb_at[wp]:
  "\<lbrace>st_tcb_at P t\<rbrace> set_mcpriority target a \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  unfolding set_mcpriority_def
  apply (wpsimp wp: thread_set_wp)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def dest!: get_tcb_SomeD)
  done

lemma set_mcpriority_no_cap_to_obj_with_diff_ref[wp]:
  "\<lbrace>no_cap_to_obj_with_diff_ref c S\<rbrace> set_mcpriority t mcp \<lbrace>\<lambda>rv. no_cap_to_obj_with_diff_ref c S\<rbrace>"
  by (simp add: set_mcpriority_def thread_set_no_cap_to_trivial tcb_cap_cases_tcb_mcpriority)

crunch caps_of_state[wp]: reorder_ntfn, reorder_ep, set_priority "\<lambda>s. P (caps_of_state s)"
  (wp: crunch_wps simp: crunch_simps)

crunch no_cap_to_obj_with_diff_ref[wp]: set_priority "no_cap_to_obj_with_diff_ref a S"
  (wp: crunch_wps no_cap_to_obj_with_diff_ref_lift)

lemma sc_tcb_sc_at_ready_queues_update[simp]:
  "sc_tcb_sc_at P t s \<Longrightarrow> sc_tcb_sc_at P t (ready_queues_update f s)"
  by (clarsimp simp: sc_tcb_sc_at_def obj_at_def)

lemma sc_tcb_sc_at_sch_act_update[simp]:
  "sc_tcb_sc_at P t s \<Longrightarrow> sc_tcb_sc_at P t (scheduler_action_update f s)"
  by (clarsimp simp: sc_tcb_sc_at_def obj_at_def)

(* FIXME move: KHeap_AI *)
lemma set_notification_obj_at_impossible:
  "\<forall>ep. \<not> (P (Notification ep)) \<Longrightarrow>
    \<lbrace>\<lambda>s. Q (obj_at P p s)\<rbrace> set_notification ptr endp \<lbrace>\<lambda>rv s. Q (obj_at P p s)\<rbrace>"
  apply (simp add: set_simple_ko_def set_object_def cong: kernel_object.case_cong)
  apply (wpsimp wp: get_object_wp set_object_at_obj)
  apply (clarsimp simp: obj_at_def split: option.splits)
  done

lemma reorder_ntfn_sc_tcb_sc_at[wp]:
  "reorder_ntfn ntfn_ptr tptr \<lbrace>\<lambda>s. Q (sc_tcb_sc_at P t s)\<rbrace>"
  by (wpsimp wp: get_simple_ko_wp simp: reorder_ntfn_def)

lemma reorder_ep_sc_tcb_sc_at[wp]:
  "reorder_ep ntfn_ptr tptr \<lbrace>\<lambda>s. Q (sc_tcb_sc_at P t s)\<rbrace>"
  by (wpsimp wp: get_simple_ko_wp simp: reorder_ntfn_def reorder_ep_def)

lemma thread_set_priority_ex_nonz_cap_to[wp]:
  "thread_set_priority t p \<lbrace>ex_nonz_cap_to p'\<rbrace>"
  by (simp add: ex_nonz_cap_to_def cte_wp_at_caps_of_state) wp

lemma thread_set_priority_pred_tcb_at[wp]:
  "thread_set_priority t p \<lbrace>pred_tcb_at proj P t'\<rbrace>"
  apply (simp add: pred_tcb_at_def thread_set_priority_def thread_set_def)
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: obj_at_def tcb_to_itcb_def dest!: get_tcb_SomeD)
  done

crunches set_priority
  for valid_cap[wp]: "valid_cap cap"
  and ex_nonz_cap_to[wp]: "ex_nonz_cap_to p"
  and idle_thread[wp]: "\<lambda>s. P (idle_thread s)"
  and pred_tcb_at[wp]: "pred_tcb_at proj P t"
  and sc_tcb_sc_at[wp]: "\<lambda>s. Q (sc_tcb_sc_at P t s)"
  (wp: crunch_wps)

crunch cte_wp_at'[wp]: reorder_ntfn, reorder_ep, reschedule_required "\<lambda>s. P (cte_wp_at P' p s)"
  (wp: crunch_wps)

lemma set_priority_cte_wp_at'[wp]:
  "\<lbrace>\<lambda>s. P (cte_wp_at P' p s)\<rbrace> set_priority tptr prio \<lbrace>\<lambda>r s. P (cte_wp_at P' p s)\<rbrace>"
  unfolding set_priority_def
  by (wpsimp wp: hoare_drop_imps simp: get_thread_state_def thread_get_def)

lemma mapM_priorities:
  "\<lbrace>\<lambda>s. (\<forall>t \<in> set qs. tcb_at t s) \<longrightarrow> P (map (tcb_priority o un_TCB o the o kheap s) qs) s\<rbrace>
  mapM (thread_get tcb_priority) qs \<lbrace>P\<rbrace>"
  apply (induct qs arbitrary: P)
   apply (wpsimp simp: mapM_Nil)
  apply (wpsimp simp: mapM_Cons)
    apply assumption
   apply (wpsimp wp: thread_get_wp')
  apply (clarsimp simp: obj_at_def is_tcb)
  done

lemma inj_on_snd_set_zip_map:
  "distinct xs \<Longrightarrow> inj_on snd (set (zip (map f xs) xs))"
  using distinct_map by fastforce

lemma tcb_ep_dequeue_append_valid_ntfn_rv:
  "\<lbrace>valid_ntfn ntfn and K (ntfn_obj ntfn = WaitingNtfn qs \<and> t \<in> set qs)\<rbrace>
   do qs' \<leftarrow> tcb_ep_dequeue t qs;
      tcb_ep_append t qs'
   od
   \<lbrace>\<lambda>rv s. valid_ntfn (ntfn_set_obj ntfn (WaitingNtfn rv)) s\<rbrace>"
  apply (simp only: tcb_ep_append_def tcb_ep_dequeue_def)
  apply (wp tcb_ep_find_index_wp)
  apply (rule conjI)
   apply (clarsimp simp: valid_ntfn_def split: option.split)
  apply (clarsimp simp: valid_ntfn_def simp del: imp_disjL dest!: findIndex_member)
  apply (intro conjI; clarsimp?)
          apply (fastforce dest: in_set_takeD in_set_dropD)
         apply (fastforce dest: in_set_dropD)
        apply (fastforce dest: in_set_dropD)
       apply (fastforce dest: in_set_dropD)
      apply (fastforce dest: in_set_takeD)
     apply (clarsimp simp: Int_Un_distrib set_take_disj_set_drop_if_distinct)
     apply (rule disjoint_subset_both[OF set_take_subset set_drop_subset])
     apply (simp add: Int_commute)
    apply (fastforce dest: in_set_takeD)
   apply (clarsimp simp: Int_Un_distrib set_take_disj_set_drop_if_distinct)
   apply (fastforce dest: in_set_takeD in_set_dropD)
  apply (clarsimp split: option.split)
  apply (case_tac ys; clarsimp)
  done

lemma reorder_ntfn_invs[wp]:
  "\<lbrace>invs and st_tcb_at (\<lambda>st. ntfn_blocked st = Some nptr) tptr\<rbrace> reorder_ntfn nptr tptr \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp only: reorder_ntfn_def)
  apply (subst bind_assoc[symmetric, where m="tcb_ep_dequeue tptr _"])
  apply (rule hoare_seq_ext)+
     apply (wpsimp wp: set_ntfn_minor_invs get_simple_ko_wp tcb_ep_dequeue_rv_wf'
                       tcb_ep_dequeue_append_valid_ntfn_rv hoare_vcg_conj_lift
                 simp: live_def live_ntfn_def pred_conj_def)+
  apply (frule valid_objs_ko_at[rotated], fastforce)
  apply (clarsimp simp: valid_obj_def valid_ntfn_def obj_at_def pred_tcb_at_def cong: conj_cong)
  apply (case_tac "tcb_state tcb"; clarsimp simp: ntfn_blocked_def get_ntfn_queue_def split: ntfn.splits)
  apply (rule context_conjI)
   apply (fastforce simp: refs_of_rev obj_at_def get_refs_def
                    dest: invs_sym_refs sym_refs_ko_atD[rotated]
                   split: option.splits)
  apply (intro conjI)
     apply fastforce
    apply (fastforce simp: valid_idle_def pred_tcb_at_def obj_at_def dest: invs_valid_idle)
   apply (erule_tac x="idle_thread s" in ballE; clarsimp?)
   apply (frule_tac p="nptr" in sym_refs_ko_atD[OF _ invs_sym_refs, rotated])
    apply (simp add: obj_at_def)
   apply (clarsimp simp: refs_of_rev obj_at_def is_tcb_def)
   apply (erule_tac x="(idle_thread s, NTFNSignal)" in ballE; simp)
   apply (fastforce simp: refs_of_rev valid_idle_def pred_tcb_at_def obj_at_def dest: invs_valid_idle)
  apply (fastforce simp: if_live_then_nonz_cap_def obj_at_def live_def live_ntfn_def dest: invs_iflive)
  done

lemma set_ep_minor_invs:
  "\<lbrace>invs and obj_at (\<lambda>ko. refs_of ko = ep_q_refs_of val) ptr
         and valid_ep val
         and (\<lambda>s. \<forall>typ. (idle_thread s, typ) \<notin> ep_q_refs_of val)
         and (\<lambda>s. live (Endpoint val) \<longrightarrow> ex_nonz_cap_to ptr s)\<rbrace>
   set_endpoint ptr val
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wpsimp wp: valid_irq_node_typ valid_ioports_lift
              simp: invs_def valid_state_def valid_pspace_def)
  apply (clarsimp simp: state_refs_of_def obj_at_def ext elim!: rsubst[where P = sym_refs])
  done

lemma monadic_rewrite_queue_of:
  "monadic_rewrite False True (K (ep \<noteq> IdleEP))
                   (return (queue_of ep)) (case_endpoint fail return return ep)"
  by (cases ep; clarsimp simp: queue_of_def monadic_rewrite_def)

lemma valid_ep_def':
  "valid_ep ep s = (ep \<noteq> IdleEP \<longrightarrow>  queue_of ep \<noteq> [] \<and> distinct (queue_of ep) \<and>
                                     (\<forall>t \<in> set (queue_of ep). tcb_at t s))"
  by (cases ep; fastforce simp: valid_ep_def queue_of_def)

lemma update_ep_queue_triv: "ep \<noteq> IdleEP \<Longrightarrow> update_ep_queue ep (queue_of ep) = ep"
  by (cases ep; clarsimp simp: queue_of_def)

lemma reorder_ep_invs[wp]:
  "\<lbrace>invs and st_tcb_at (\<lambda>st. ep_blocked st = Some nptr) tptr\<rbrace> reorder_ep nptr tptr \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp only: reorder_ep_def get_ep_queue_def)
  apply (wp set_ep_minor_invs hoare_drop_imps tcb_ep_dequeue_rv_wf'
            tcb_ep_dequeue_valid_ep tcb_ep_dequeue_inv tcb_ep_dequeue_rv_wf''
            tcb_ep_append_valid_ep tcb_ep_append_inv tcb_ep_append_rv_wf''')
    apply (rule monadic_rewrite_refine_valid[OF monadic_rewrite_queue_of, where P''=\<top>,simplified])
    apply (wp get_simple_ko_wp)+
  apply (clarsimp cong: conj_cong)
  apply (rename_tac ep)
  apply (frule valid_objs_ko_at[rotated], fastforce)
  apply (clarsimp simp: valid_obj_def valid_ep_def' pred_tcb_at_def obj_at_def cong: conj_cong)
  apply (subgoal_tac "tptr \<in> set (queue_of ep)")
   apply (rule context_conjI, clarsimp simp: queue_of_def)
   apply (clarsimp simp: update_ep_queue_triv)
   apply (intro conjI allI)
    apply (erule_tac x="idle_thread s" in ballE)
     apply (frule_tac p=nptr in sym_refs_ko_atD[OF _ invs_sym_refs, rotated])
      apply (simp add: obj_at_def)
     apply (clarsimp simp: refs_of_rev obj_at_def is_tcb_def)
     apply (erule_tac x="(idle_thread s, typ)" in ballE; simp)
     apply (fastforce simp: refs_of_rev valid_idle_def pred_tcb_at_def obj_at_def dest: invs_valid_idle)
    apply (case_tac ep; clarsimp simp: queue_of_def)
   apply (fastforce simp: if_live_then_nonz_cap_def obj_at_def live_def live_ntfn_def dest: invs_iflive)
  apply (frule invs_sym_refs)
  apply (drule_tac p=tptr in sym_refs_ko_atD[rotated])
   apply (simp add: obj_at_def)
  apply (clarsimp simp: ep_blocked_def obj_at_def queue_of_def
                 split: if_splits endpoint.splits thread_state.splits)
  done

lemma set_priority_invs[wp]:
  "\<lbrace>invs and ex_nonz_cap_to t\<rbrace> set_priority t p \<lbrace>\<lambda>_. invs\<rbrace>"
  unfolding set_priority_def
  by (wpsimp wp: gts_wp hoare_vcg_imp_lift' hoare_vcg_all_lift
           simp: thread_get_def get_tcb_queue_def pred_tcb_at_def obj_at_def)

lemma set_mcpriority_bound_sc_tcb_at[wp]:
  "set_mcpriority ref mcp \<lbrace>\<lambda>s. Q (bound_sc_tcb_at P t s)\<rbrace>"
  unfolding set_mcpriority_def
  apply (wpsimp wp: thread_set_wp)
  by (clarsimp simp: pred_tcb_at_def obj_at_def dest!: get_tcb_SomeD)

lemma thread_set_priority_bound_sc_tcb_at[wp]:
  "thread_set_priority ref p \<lbrace>\<lambda>s. Q (bound_sc_tcb_at P t s)\<rbrace>"
  unfolding thread_set_priority_def
  apply (wpsimp wp: thread_set_wp)
  by (clarsimp simp: pred_tcb_at_def obj_at_def dest!: get_tcb_SomeD)

crunches reorder_ntfn, reorder_ep
  for bound_sc_tcb_at[wp]: "\<lambda>s. Q (bound_sc_tcb_at P t s)"
  (wp: crunch_wps)

lemma set_priority_bound_sc_tcb_at[wp]:
  "set_priority ref p \<lbrace>\<lambda>s. Q (bound_sc_tcb_at P t s)\<rbrace>"
  unfolding set_priority_def
  by (wpsimp simp:  wp: hoare_drop_imps)

crunches cancel_all_ipc
  for bound_sc_tcb_at[wp]: "bound_sc_tcb_at P target"
  (wp: crunch_wps)

lemma cap_delete_fh_lift:
  assumes A: "\<And>x. \<lbrace>Q1\<rbrace> empty_slot (target, tcb_cnode_index 3) x \<lbrace>\<lambda>_. P\<rbrace>"
  and     C: "\<And>x. \<lbrace>Q2\<rbrace> cancel_all_ipc x \<lbrace>\<lambda>_. Q1\<rbrace>"
  and     B: "\<And>s. (P and invs and tcb_at target and L) s \<Longrightarrow> Q1 s"
  and     B': "\<And>s. (P and invs and tcb_at target and L) s \<Longrightarrow> Q2 s"
  shows  "\<lbrace>P and invs and tcb_at target and L\<rbrace>
   cap_delete (target, tcb_cnode_index 3)
   \<lbrace>\<lambda>_. P\<rbrace>"
  unfolding cap_delete_def
  apply wpsimp
   apply (subst rec_del_CTEDeleteCall)
   apply (wpsimp wp: A)
   apply (subst rec_del_FinaliseSlot)
   prefer 2
   apply assumption
  apply (rule hoare_vcg_seqE[rotated])
   apply (subst liftE_validE)
   apply (rule get_cap_sp)
  apply (subst hoare_pre_addE[where R="K (valid_fault_handler cap)"])
   apply clarsimp
   apply (subgoal_tac "cte_wp_at valid_fault_handler (target, tcb_cnode_index 3) s")
    apply (simp add: cte_wp_at_caps_of_state)
   apply (rule tcb_ep_slot_cte_wp_ats; clarsimp simp: pred_tcb_at_def obj_at_def is_tcb)
  apply (case_tac cap; simp add: valid_fault_handler_def)
   apply wpsimp
   apply (rule B, simp)
  apply wpsimp
        apply (rule hoare_FalseE)
      apply (rule hoare_FalseE)
      apply (rule hoare_FalseE)
     apply wpsimp
    apply (subst liftE_liftM_liftME)
    apply (wpsimp wp: liftME_wp C simp: is_final_cap_def)+
    apply (intro conjI impI; rule B B', simp)
  done

lemma install_tcb_cap_bound_sc_tcb_at[wp]:
  "\<lbrace>bound_sc_tcb_at P target' and tcb_at target and invs\<rbrace>
   install_tcb_cap target slot 3 slot_opt
   \<lbrace>\<lambda>_. bound_sc_tcb_at P target'\<rbrace>"
  unfolding install_tcb_cap_def
  by (wpsimp wp: check_cap_inv cap_delete_fh_lift hoare_vcg_const_imp_lift)

lemma install_tcb_cap_not_ipc_queued_thread[wp]:
  "\<lbrace>st_tcb_at (not ipc_queued_thread_state) t and tcb_at target and invs\<rbrace>
   install_tcb_cap target slot 3 slot_opt
   \<lbrace>\<lambda>_. st_tcb_at (not ipc_queued_thread_state) t\<rbrace>"
  unfolding install_tcb_cap_def
  by (wpsimp wp: check_cap_inv cap_delete_fh_lift cancel_all_ipc_st_tcb_at hoare_vcg_const_imp_lift
           simp: pred_neg_def st_tcb_at_tcb_at)

lemma set_simple_ko_sc_at_pred_n[wp]:
  "set_simple_ko g ep v \<lbrace> \<lambda>s. P (sc_at_pred_n N proj f t s) \<rbrace>"
  unfolding set_simple_ko_def
  apply (wpsimp wp: set_object_wp_strong get_object_wp)
  apply (intro conjI;
         clarsimp elim!: rsubst[where P=P] split: option.splits simp: sc_at_pred_n_def obj_at_def)
  done

crunches cancel_all_ipc
  for sc_tcb_sc_at[wp]: "\<lambda>s. Q (sc_tcb_sc_at P p s)"
  and ex_nonz_cap_to[wp]: "ex_nonz_cap_to t"
  (wp: crunch_wps simp: crunch_simps is_round_robin_def)

lemma valid_cap_not_ep_at_not_ep_cap:
  "\<lbrakk> r \<in> obj_refs cap; \<not> ep_at r s; s \<turnstile> cap \<rbrakk>
   \<Longrightarrow> \<not> is_ep_cap cap"
  by (auto simp: valid_cap_def is_cap_simps obj_at_def is_obj_defs a_type_def
          split: cap.splits
           dest: obj_ref_is_arch)

lemma cancel_all_ipc_ep[wp]:
  "cancel_all_ipc ptr \<lbrace>\<lambda>s. Q (ep_at t s)\<rbrace>"
  by (simp add: ep_at_typ, wp cancel_all_ipc_typ_at)

lemma install_tcb_cap_ex_nonz_cap_to:
  "\<lbrace>ex_nonz_cap_to t and invs and tcb_at t' and (not ep_at t)\<rbrace>
   install_tcb_cap t' slot 3 slot_opt
   \<lbrace>\<lambda>_. ex_nonz_cap_to t\<rbrace>"
  unfolding install_tcb_cap_def
  apply wpsimp
    apply (wpsimp wp: check_cap_inv cap_insert_ex_cap)
   apply (simp, rule valid_validE)
   apply (rule cap_delete_fh_lift[where L="not ep_at t"](* [where Q1="valid_objs and tcb_at t' and not ep_at t"] *))
      apply (wpsimp simp: ex_nonz_cap_to_def wp: hoare_vcg_ex_lift empty_slot_cte_wp_elsewhere)
     apply (rule_tac Q="\<lambda>_. valid_objs and ex_nonz_cap_to t and not ep_at t and tcb_at t'" in hoare_strengthen_post)
      apply (wpsimp simp: pred_neg_def wp: cancel_all_ipc_valid_objs cancel_all_ipc_tcb)
     apply (clarsimp simp: ex_nonz_cap_to_def)
     apply (rename_tac ref' x x' s ref index)
     apply (rule_tac x=ref in exI)
     apply (rule_tac x=index in exI)
     apply (clarsimp)
     apply (subgoal_tac "cte_wp_at (is_ep_cap or ((=) NullCap)) (t', tcb_cnode_index 3) s")
      apply (clarsimp simp: zobj_refs_to_obj_refs cte_wp_at_def get_cap_caps_of_state pred_neg_def)
      apply (subgoal_tac "cap = capa")
       apply (frule valid_cap_not_ep_at_not_ep_cap, assumption)
        apply (erule caps_of_state_valid[OF sym], assumption)
       apply (clarsimp simp: )
      apply (subst option.inject[symmetric])
      apply (clarsimp)
     apply (clarsimp simp: obj_at_def is_tcb)
     apply (subgoal_tac "valid_tcb t' tcb s")
      apply (clarsimp simp: valid_tcb_def tcb_cap_cases_def valid_fault_handler_def
                            cte_wp_at_caps_of_state tcb_at_def is_tcb)
      apply (subst (asm) caps_of_state_tcb_index_trans)
       apply (erule get_tcb_rev)
      apply (clarsimp simp: tcb_cnode_map_def)
     apply (clarsimp simp: valid_objs_def valid_obj_def dom_def)
     apply fastforce
    apply (clarsimp simp: ex_nonz_cap_to_def)
    apply (rename_tac ref x x' s ref' index)
    apply (rule_tac x=ref' in exI)
    apply (rule_tac x=index in exI)
    apply (clarsimp)
    apply (subgoal_tac "cte_wp_at (is_ep_cap or ((=) NullCap)) (t', tcb_cnode_index 3) s")
     apply (clarsimp simp: zobj_refs_to_obj_refs cte_wp_at_def get_cap_caps_of_state pred_neg_def)
     apply (subgoal_tac "cap = capa")
      apply (frule valid_cap_not_ep_at_not_ep_cap, assumption)
       apply (rule caps_of_state_valid[OF sym], assumption) apply clarsimp
      apply (clarsimp simp: )
     apply (subst option.inject[symmetric])
     apply (clarsimp)
    apply (clarsimp simp: obj_at_def is_tcb)
    apply (subgoal_tac "valid_objs s")
     apply (subgoal_tac "valid_tcb t' tcb s")
      apply (clarsimp simp: valid_tcb_def tcb_cap_cases_def valid_fault_handler_def
                            cte_wp_at_caps_of_state tcb_at_def is_tcb)
      apply (subst (asm) caps_of_state_tcb_index_trans)
       apply (erule get_tcb_rev)
      apply (clarsimp simp: tcb_cnode_map_def)
     apply (clarsimp simp: valid_objs_def valid_obj_def dom_def)
     apply fastforce
    apply clarsimp
   apply (clarsimp simp: invs_def valid_state_def valid_pspace_def pred_neg_def)
  apply clarsimp
  done

(* FIXME: move *)
lemma cte_wp_at_strengthen:
  "cte_wp_at P p s \<Longrightarrow> \<forall>c. P c \<longrightarrow> Q c \<Longrightarrow> cte_wp_at Q p s"
  by (auto simp add: cte_wp_at_cases)

(* FIXME: move *)
lemma bound_sc_tcb_at_idle_sc_idle_thread:
  "sym_refs (state_refs_of s)
   \<Longrightarrow> valid_idle s
   \<Longrightarrow> bound_sc_tcb_at (\<lambda>a. a = Some idle_sc_ptr) t s
   \<Longrightarrow> t = idle_thread_ptr"
  apply (subgoal_tac "bound_sc_tcb_at (\<lambda>a. a = Some idle_sc_ptr) idle_thread_ptr s")
  apply (erule sym_refs_bound_sc_tcb_at_inj[rotated], assumption, assumption)
  apply (clarsimp simp: invs_def valid_state_def valid_idle_def pred_tcb_at_def obj_at_def)
  done

(* FIXME: move *)
lemma maybeM_wp_drop_None:
  "(\<And>x. y = Some x \<Longrightarrow> \<lbrace>\<lambda>s. Q () s \<and> P x s\<rbrace> m x \<lbrace>Q\<rbrace>) \<Longrightarrow>
  \<lbrace>\<lambda>s. Q () s \<and> (\<forall>x. y = Some x \<longrightarrow> P x s)\<rbrace> maybeM m y \<lbrace>Q\<rbrace>"
  unfolding maybeM_def by (cases y; simp; wp)

end
