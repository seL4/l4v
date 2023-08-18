(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Tcb_AI
imports ArchCNodeInv_AI
begin

context begin interpretation Arch .

requalify_facts
  arch_derive_is_arch

end

locale Tcb_AI_1 =
  fixes state_ext_t :: "('state_ext::state_ext) itself"
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
  assumes arch_get_sanitise_register_info_invs[wp]:
  "\<And>t. \<lbrace>\<lambda>(s::'state_ext state). invs s\<rbrace> arch_get_sanitise_register_info t
       \<lbrace>\<lambda>b s. invs s\<rbrace>"
  assumes arch_get_sanitise_register_info_tcb_at[wp]:
  "\<And>t a. \<lbrace>\<lambda>(s::'state_ext state). tcb_at a s\<rbrace> arch_get_sanitise_register_info t
       \<lbrace>\<lambda>b s. tcb_at a s\<rbrace>"
  assumes arch_get_sanitise_register_info_ex_nonz_cap_to[wp]:
  "\<And>t a. \<lbrace>\<lambda>(s::'state_ext state). ex_nonz_cap_to a s\<rbrace> arch_get_sanitise_register_info t
       \<lbrace>\<lambda>b s. ex_nonz_cap_to a s\<rbrace>"
  assumes arch_post_modify_registers_invs[wp]:
  "\<And>c t. \<lbrace>\<lambda>(s::'state_ext state). invs s\<rbrace> arch_post_modify_registers c t
       \<lbrace>\<lambda>b s. invs s\<rbrace>"
  assumes arch_post_modify_registers_tcb_at[wp]:
  "\<And>c t a. \<lbrace>\<lambda>(s::'state_ext state). tcb_at a s\<rbrace> arch_post_modify_registers c t
       \<lbrace>\<lambda>b s. tcb_at a s\<rbrace>"
  assumes arch_post_modify_registers_ex_nonz_cap_to[wp]:
  "\<And>c t a. \<lbrace>\<lambda>(s::'state_ext state). ex_nonz_cap_to a s\<rbrace> arch_post_modify_registers c t
       \<lbrace>\<lambda>b s. ex_nonz_cap_to a s\<rbrace>"
  assumes finalise_cap_not_cte_wp_at:
  "\<And>P cap fin. P cap.NullCap \<Longrightarrow> \<lbrace>\<lambda>(s::'state_ext state). \<forall>cp \<in> ran (caps_of_state s). P cp\<rbrace>
                finalise_cap cap fin \<lbrace>\<lambda>rv s. \<forall>cp \<in> ran (caps_of_state s). P cp\<rbrace>"
  assumes table_cap_ref_max_free_index_upd[simp]: (* reordered to resolve dependency in tc_invs *)
  "\<And>cap. table_cap_ref (max_free_index_update cap) = table_cap_ref cap"

lemma ct_in_state_weaken:
  "\<lbrakk> ct_in_state Q s; \<And>st. Q st \<Longrightarrow> P st \<rbrakk> \<Longrightarrow> ct_in_state P s"
  by (clarsimp simp: ct_in_state_def pred_tcb_at_def obj_at_def)

lemma ct_in_state_exst_update[simp]: "ct_in_state P (trans_state f s) = ct_in_state P s"
  by (simp add: ct_in_state_def)

lemma set_thread_state_ct_st:
  "\<lbrace>\<lambda>s. if thread = cur_thread s then P st else ct_in_state P s\<rbrace>
        set_thread_state thread st
   \<lbrace>\<lambda>rv. ct_in_state P\<rbrace>"
  apply (simp add: set_thread_state_def set_object_def get_object_def)
  apply (wp|simp)+
  apply (clarsimp simp: ct_in_state_def pred_tcb_at_def obj_at_def)
  done

lemma (in Tcb_AI_1) activate_invs:
  "\<lbrace>(invs::'state_ext::state_ext state \<Rightarrow> bool)\<rbrace> activate_thread \<lbrace>\<lambda>rv s. invs s \<and> (ct_running s \<or> ct_idle s)\<rbrace>"
  apply (unfold activate_thread_def)
  apply (rule hoare_seq_ext [OF _ gets_sp])
  apply (rule hoare_seq_ext [OF _ gts_sp])
  apply (case_tac state, simp_all)
    apply wp
    apply (clarsimp elim!: pred_tcb_weakenE
                     simp: ct_in_state_def)
   apply (rule_tac Q="\<lambda>rv. invs and ct_running" in hoare_post_imp, simp)
   apply (rule hoare_pre)
    apply (wp sts_invs_minor ct_in_state_set)
      apply simp
     apply (simp | strengthen reply_cap_doesnt_exist_strg)+
     apply (wp as_user_ct hoare_post_imp [OF disjI1]
          | assumption
          | clarsimp elim!: st_tcb_weakenE)+
   apply (auto simp: invs_def valid_state_def
                         valid_idle_def valid_pspace_def
               elim: st_tcb_ex_cap pred_tcb_weakenE,
          auto simp: st_tcb_def2 pred_tcb_at_def obj_at_def)[1]
  apply (rule_tac Q="\<lambda>rv. invs and ct_idle" in hoare_post_imp, simp)
  apply (wp activate_idle_invs hoare_post_imp [OF disjI2])
  apply (clarsimp simp: ct_in_state_def elim!: pred_tcb_weakenE)
  done

crunch pred_tcb_at[wp]: setup_reply_master "pred_tcb_at proj P t"

crunch idle_thread[wp]: setup_reply_master "\<lambda>s. P (idle_thread s)"


lemma setup_reply_master_reply_master[wp]:
  "\<lbrace>valid_objs and tcb_at t\<rbrace> setup_reply_master t
   \<lbrace>\<lambda>rv. cte_wp_at (\<lambda>c. is_master_reply_cap c \<and> obj_ref_of c = t) (t, tcb_cnode_index 2)\<rbrace>"
  apply (simp add: setup_reply_master_def)
  apply (wp set_cap_cte_wp_at' get_cap_wp)
  apply (auto simp: tcb_cap_valid_def st_tcb_def2 cte_wp_at_caps_of_state is_cap_simps
              dest: tcb_cap_valid_caps_of_stateD)
  done

lemma setup_reply_master_has_reply[wp]:
  "\<lbrace>\<lambda>s. P (has_reply_cap t s)\<rbrace> setup_reply_master t' \<lbrace>\<lambda>rv s. P (has_reply_cap t s)\<rbrace>"
  apply (simp add: has_reply_cap_def is_reply_cap_to_def cte_wp_at_caps_of_state
                   setup_reply_master_def)
  apply (wp get_cap_wp)
  apply (clarsimp simp: cte_wp_at_caps_of_state elim!: rsubst[where P=P])
  apply (intro arg_cong[where f=Ex] ext)
  apply auto
  done

lemma setup_reply_master_nonz_cap[wp]:
  "\<lbrace>ex_nonz_cap_to p\<rbrace> setup_reply_master t \<lbrace>\<lambda>rv. ex_nonz_cap_to p\<rbrace>"
  apply (simp add: setup_reply_master_def ex_nonz_cap_to_def cte_wp_at_caps_of_state)
  apply (wp get_cap_wp)
  apply (simp add: cte_wp_at_caps_of_state)
  apply (rule impI, elim exEI)
  apply clarsimp
  done

lemma restart_invs[wp]:
  "\<lbrace>invs and tcb_at t and ex_nonz_cap_to t\<rbrace> restart t \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: restart_def)
  apply (rule hoare_seq_ext [OF _ gts_sp])
  apply (wp sts_invs_minor cancel_ipc_ex_nonz_cap_to_tcb
            hoare_vcg_disj_lift cancel_ipc_simple2
       | simp add: if_apply_def2
       | strengthen invs_valid_objs2)+
  apply (auto dest!: idle_no_ex_cap simp: invs_def valid_state_def valid_pspace_def)
  done

lemma restart_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> Tcb_A.restart t \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by (wpsimp simp: Tcb_A.restart_def wp: cancel_ipc_typ_at)

lemma restart_tcb[wp]:
  "\<lbrace>tcb_at t'\<rbrace> Tcb_A.restart t \<lbrace>\<lambda>rv. tcb_at t'\<rbrace>"
  by (wpsimp simp: tcb_at_typ wp: restart_typ_at)

crunch ex_nonz_cap_to[wp]: update_restart_pc "ex_nonz_cap_to t"

lemma suspend_nonz_cap_to_tcb[wp]:
  "\<lbrace>\<lambda>s. ex_nonz_cap_to t s \<and> tcb_at t s \<and> valid_objs s\<rbrace>
     suspend t'
   \<lbrace>\<lambda>rv s. ex_nonz_cap_to t s\<rbrace>"
  by (wp cancel_ipc_ex_nonz_cap_to_tcb | simp add: suspend_def)+

lemmas suspend_tcb_at[wp] = tcb_at_typ_at [OF suspend_typ_at]

lemma readreg_invs:
  "\<lbrace>invs and tcb_at src and ex_nonz_cap_to src\<rbrace>
     invoke_tcb (tcb_invocation.ReadRegisters src susp n arch)
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (simp | wp)+
     (clarsimp simp: invs_def valid_state_def valid_pspace_def
              dest!: idle_no_ex_cap)

lemma (in Tcb_AI_1) writereg_invs:
  "\<lbrace>(invs::'state_ext::state_ext state \<Rightarrow> bool) and tcb_at dest and ex_nonz_cap_to dest\<rbrace>
     invoke_tcb (tcb_invocation.WriteRegisters dest resume values arch)
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (wpsimp |rule conjI)+

lemma (in Tcb_AI_1) copyreg_invs:
  "\<lbrace>(invs::'state_ext::state_ext state \<Rightarrow> bool) and tcb_at src and tcb_at dest and ex_nonz_cap_to dest and
    ex_nonz_cap_to src\<rbrace>
     invoke_tcb (tcb_invocation.CopyRegisters dest src susp resume frames ints arch)
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wpsimp simp: if_apply_def2
                  wp: mapM_x_wp' suspend_nonz_cap_to_tcb hoare_weak_lift_imp)
  apply (clarsimp simp: invs_def valid_state_def valid_pspace_def suspend_def
                 dest!: idle_no_ex_cap)
  done

lemma out_invs_trivialT:
  assumes x: "\<And>tcb v. \<forall>(getF, setF)\<in>ran tcb_cap_cases. getF (fn v tcb) = getF tcb"
  assumes r:  "\<And>tcb v. tcb_arch_ref (fn v tcb) = tcb_arch_ref tcb" (* ARMHYP *)
  assumes z: "\<And>tcb v. tcb_state  (fn v tcb) = tcb_state  tcb"
  assumes z': "\<And>tcb v. tcb_bound_notification (fn v tcb) = tcb_bound_notification tcb"
  assumes z'': "\<And>tcb v. tcb_iarch (fn v tcb) = tcb_iarch tcb"
  assumes w: "\<And>tcb v. tcb_ipc_buffer (fn v tcb) = tcb_ipc_buffer tcb
                          \<or> tcb_ipc_buffer (fn v tcb) = 0"
  assumes y: "\<And>tcb v'. v = Some v' \<Longrightarrow> tcb_fault_handler (fn v' tcb) \<noteq> tcb_fault_handler tcb
                       \<longrightarrow> length (tcb_fault_handler (fn v' tcb)) = word_bits"
  assumes a: "\<And>tcb v. tcb_fault (fn v tcb) \<noteq> tcb_fault tcb
                       \<longrightarrow> (case tcb_fault (fn v tcb) of None \<Rightarrow> True
                                                   | Some f \<Rightarrow> valid_fault f)"
  shows      "\<lbrace>invs\<rbrace> option_update_thread t fn v \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (case_tac v, simp_all add: option_update_thread_def)
  apply (rule thread_set_invs_trivial [OF x z z' z'' w y a r])
  apply (auto intro: r)
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

lemma out_emptyable:
  assumes x: "\<And>tcb v. tcb_state  (fn v tcb) = tcb_state  tcb"
  shows      "\<lbrace>emptyable sl\<rbrace> option_update_thread t fn v
              \<lbrace>\<lambda>rv. emptyable sl\<rbrace>"
  by (wp emptyable_lift out_typ_at out_st_tcb x)

lemma inQ_residue[simp]:
  "(P \<and> Q \<and> (P \<longrightarrow> R)) = (P \<and> Q \<and> R)"
  by fastforce

lemma set_simple_ko_valid_cap:
  "\<lbrace>valid_cap c\<rbrace> set_simple_ko f e ep \<lbrace>\<lambda>_. valid_cap c\<rbrace>"
  by (wp valid_cap_typ)


lemma sts_cte_at[wp]:
  "\<lbrace>\<lambda>s. cte_at p s\<rbrace> set_thread_state t st \<lbrace>\<lambda>_ s. cte_at p s\<rbrace>"
  by (wp valid_cte_at_typ)


lemma as_user_cte_at[wp]:
  "\<lbrace>\<lambda>s. cte_at p s\<rbrace> as_user t m \<lbrace>\<lambda>_ s. cte_at p s\<rbrace>"
  by (wp valid_cte_at_typ)


lemma cap_insert_cte_at:
  "\<lbrace>cte_at p\<rbrace> cap_insert cap src dest \<lbrace>\<lambda>_. cte_at p\<rbrace>"
  by (wp valid_cte_at_typ)


lemma smrs_cte_at[wp]:
  "\<lbrace>cte_at p\<rbrace> set_mrs thread buf msgs \<lbrace>\<lambda>_. cte_at p\<rbrace>"
  by (wp valid_cte_at_typ)


lemma si_cte_at[wp]:
  "\<lbrace>cte_at p\<rbrace> send_ipc bl c ba cg cgr t ep \<lbrace>\<lambda>_. cte_at p\<rbrace>"
  by (wp valid_cte_at_typ)


lemma ri_cte_at[wp]:
  "\<lbrace>cte_at p\<rbrace> receive_ipc t cap is_blocking \<lbrace>\<lambda>_. cte_at p\<rbrace>"
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
      \<and> (p = tcb_cnode_index 4 \<longrightarrow> (\<forall>ptr. valid_ipc_buffer_cap cap ptr))
         \<longrightarrow> tcb_cap_valid cap (t, p) s"
  by (clarsimp simp: tcb_cap_valid_def st_tcb_def2 tcb_at_def
              split: option.split_asm)

declare thread_set_emptyable[wp]

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

locale Tcb_AI = Tcb_AI_1 state_ext_t is_cnode_or_valid_arch
  for state_ext_t :: "('state_ext::state_ext) itself"
  and is_cnode_or_valid_arch :: "cap \<Rightarrow> bool" +
  assumes cap_delete_no_cap_to_obj_asid[wp]:
  "\<And>cap slot. \<lbrace>(no_cap_to_obj_dr_emp cap::'state_ext state \<Rightarrow> bool)\<rbrace>
     cap_delete slot
   \<lbrace>\<lambda>rv. no_cap_to_obj_dr_emp cap\<rbrace>"
  assumes tc_invs:
  "\<And>a e f g b mcp sl pr.
    \<lbrace>(invs::'state_ext state \<Rightarrow> bool) and tcb_at a
        and (case_option \<top> (valid_cap o fst) e)
        and (case_option \<top> (valid_cap o fst) f)
        and (case_option \<top> (case_option \<top> (valid_cap o fst) o snd) g)
        and (case_option \<top> (cte_at o snd) e)
        and (case_option \<top> (cte_at o snd) f)
        and (case_option \<top> (case_option \<top> (cte_at o snd) o snd) g)
        and (case_option \<top> (no_cap_to_obj_dr_emp o fst) e)
        and (case_option \<top> (no_cap_to_obj_dr_emp o fst) f)
        and (case_option \<top> (case_option \<top> (no_cap_to_obj_dr_emp o fst) o snd) g)
        \<comment> \<open>NOTE: The auth TCB does not really belong in the tcb_invocation type, and
          is only included so that we can assert here that the priority we are setting is
          bounded by the MCP of some auth TCB. Unfortunately, current proofs about the
          decode functions throw away the knowledge that the auth TCB actually came from
          the current thread's c-space, so this is not as strong an assertion as we would
          like. Ideally, we would assert that there is some cap in the current thread's
          c-space that is to a TCB whose MCP validates the priority we are setting. We
          don't care which TCB is used as the auth TCB; we only care that there exists
          some auth TCB accessible from the current thread's c-space. Phrased that way,
          we could drop the auth TCB from tcb_invocation. For now, we leave this as
          future work.\<close>
        and (\<lambda>s. case_option True (\<lambda>(pr, auth). mcpriority_tcb_at (\<lambda>mcp. pr \<le> mcp) auth s) pr)
        and (\<lambda>s. case_option True (\<lambda>(mcp, auth). mcpriority_tcb_at (\<lambda>m. mcp \<le> m) auth s) mcp)
        and K (case_option True (is_cnode_cap o fst) e)
        and K (case_option True (is_valid_vtable_root o fst) f)
        and K (case_option True (\<lambda>v. case_option True
                           ((swp valid_ipc_buffer_cap (fst v)
                              and is_arch_cap and is_cnode_or_valid_arch)
                                 o fst) (snd v)) g)
        and K (case_option True (\<lambda>bl. length bl = word_bits) b)\<rbrace>
      invoke_tcb (ThreadControl a sl b mcp pr e f g)
    \<lbrace>\<lambda>rv. invs\<rbrace>"
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
  "\<lbrace>invs and cte_wp_at (\<lambda>c. c = cap.NullCap) (t, tcb_cnode_index 4)\<rbrace>
     thread_set (tcb_ipc_buffer_update f) t
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (rule hoare_pre)
   apply (wp thread_set_valid_objs''
             thread_set_refs_trivial
             thread_set_hyp_refs_trivial
             thread_set_iflive_trivial
             thread_set_mdb
             thread_set_ifunsafe_trivial
             thread_set_cur_tcb
             thread_set_zombies_trivial
             thread_set_valid_idle_trivial
             thread_set_global_refs_triv
             thread_set_valid_reply_caps_trivial
             thread_set_valid_reply_masters_trivial
             valid_irq_node_typ valid_irq_handlers_lift
             thread_set_caps_of_state_trivial valid_ioports_lift
             thread_set_arch_caps_trivial
             thread_set_only_idle
             thread_set_cap_refs_in_kernel_window
             thread_set_valid_ioc_trivial
             thread_set_cap_refs_respects_device_region
              | simp add: ran_tcb_cap_cases
              | rule conjI | erule disjE)+
  apply (clarsimp simp: valid_tcb_def dest!: get_tcb_SomeD)
  apply (rule conjI, simp add: ran_tcb_cap_cases)
  apply (cut_tac P="(=) v" and t="(t, tcb_cnode_index 4)" for v
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
   \<lbrace>\<lambda>rv. tcb_cap_valid cap (t, tcb_cnode_index 4)\<rbrace>"
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
  apply (wp thread_set_cte_at thread_set_valid_objs')
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
             thread_set_zombies_trivial
             thread_set_valid_idle_trivial
             thread_set_global_refs_triv
             thread_set_valid_reply_caps_trivial
             thread_set_valid_reply_masters_trivial
             valid_irq_node_typ valid_irq_handlers_lift
             thread_set_caps_of_state_trivial
             thread_set_arch_caps_trivial
             thread_set_only_idle
             thread_set_cap_refs_in_kernel_window
             thread_set_valid_ioc_trivial valid_ioports_lift
             thread_set_cap_refs_respects_device_region
              | simp add: ran_tcb_cap_cases invs_def valid_state_def valid_pspace_def
              | rule conjI | erule disjE)+


context Tcb_AI begin

primrec
  tcb_inv_wf  :: "tcb_invocation \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "tcb_inv_wf (tcb_invocation.Suspend t)
             = (tcb_at t and ex_nonz_cap_to t)"
| "tcb_inv_wf (tcb_invocation.Resume t)
             = (tcb_at t and ex_nonz_cap_to t)"
| "tcb_inv_wf (tcb_invocation.ThreadControl t sl fe mcp pr croot vroot buf)
             = (tcb_at t and case_option \<top> (valid_cap \<circ> fst) croot
                        and K (case_option True (is_cnode_cap \<circ> fst) croot)
                        and case_option \<top> ((cte_at and ex_cte_cap_to) \<circ> snd) croot
                        and case_option \<top> (no_cap_to_obj_dr_emp \<circ> fst) croot
                        and K (case_option True (is_valid_vtable_root \<circ> fst) vroot)
                        and case_option \<top> (valid_cap \<circ> fst) vroot
                        and case_option \<top> (no_cap_to_obj_dr_emp \<circ> fst) vroot
                        and case_option \<top> ((cte_at and ex_cte_cap_to) \<circ> snd) vroot
                        and (case_option \<top> (case_option \<top> (valid_cap o fst) o snd) buf)
                        and (case_option \<top> (case_option \<top>
                              (no_cap_to_obj_dr_emp o fst) o snd) buf)
                        and K (case_option True ((\<lambda>v. is_aligned v msg_align_bits) o fst) buf)
                        and K (case_option True (\<lambda>v. case_option True
                               ((swp valid_ipc_buffer_cap (fst v)
                                    and is_arch_cap and is_cnode_or_valid_arch)
                                              o fst) (snd v)) buf)
                        and (case_option \<top> (case_option \<top> ((cte_at and ex_cte_cap_to) o snd) o snd) buf)
                        and (\<lambda>s. {croot, vroot, option_map undefined buf} \<noteq> {None}
                                    \<longrightarrow> cte_at sl s \<and> ex_cte_cap_to sl s)
                        and K (case_option True (\<lambda>bl. length bl = word_bits) fe)
                        and (\<lambda>s. case_option True (\<lambda>(pr, auth). mcpriority_tcb_at (\<lambda>mcp. pr \<le> mcp) auth s) pr)
                        and (\<lambda>s. case_option True (\<lambda>(mcp, auth). mcpriority_tcb_at (\<lambda>m. mcp \<le> m) auth s) mcp)
                        and ex_nonz_cap_to t)"
| "tcb_inv_wf (tcb_invocation.ReadRegisters src susp n arch)
             = (tcb_at src and ex_nonz_cap_to src)"
| "tcb_inv_wf (tcb_invocation.WriteRegisters dest resume values arch)
             = (tcb_at dest and ex_nonz_cap_to dest)"
| "tcb_inv_wf (tcb_invocation.CopyRegisters dest src suspend_source resume_target
                 trans_frame trans_int trans_arch)
             = (tcb_at dest and tcb_at src and ex_nonz_cap_to src and
                ex_nonz_cap_to dest)"
| "tcb_inv_wf (NotificationControl t ntfn)
             = (tcb_at t and ex_nonz_cap_to t
                  and (case ntfn of None \<Rightarrow> \<top>
                          | Some ntfnptr \<Rightarrow> (obj_at (\<lambda>ko. \<exists>ntfn. ko = Notification ntfn
                                                \<and> (ntfn_bound_tcb ntfn = None)
                                                \<and> (\<forall>q. ntfn_obj ntfn \<noteq> WaitingNtfn q)) ntfnptr
                                          and ex_nonz_cap_to ntfnptr
                                          and bound_tcb_at ((=) None) t) ))"
| "tcb_inv_wf (SetTLSBase t tls_base) = (tcb_at t and ex_nonz_cap_to t)"

end

crunch ex_nonz_cap_to[wp]: unbind_notification "ex_nonz_cap_to t"

lemma sbn_has_reply[wp]:
  "\<lbrace>\<lambda>s. P (has_reply_cap t s)\<rbrace> set_bound_notification tcb ntfnptr \<lbrace>\<lambda>rv s. P (has_reply_cap t s)\<rbrace>"
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
  apply (case_tac ntfnptr, simp, wp, simp)
  apply (clarsimp)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (wp, clarsimp)
  done


lemma bind_notification_invs:
  shows
  "\<lbrace>bound_tcb_at ((=) None) tcbptr
    and obj_at (\<lambda>ko. \<exists>ntfn. ko = Notification ntfn \<and> (ntfn_bound_tcb ntfn = None)
                           \<and> (\<forall>q. ntfn_obj ntfn \<noteq> WaitingNtfn q)) ntfnptr
    and invs
    and ex_nonz_cap_to ntfnptr
    and ex_nonz_cap_to tcbptr\<rbrace>
     bind_notification tcbptr ntfnptr
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: bind_notification_def invs_def valid_state_def valid_pspace_def)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (wp valid_irq_node_typ set_simple_ko_valid_objs simple_obj_set_prop_at valid_ioports_lift
         | clarsimp simp:idle_no_ex_cap split del: if_split)+
  apply (intro conjI;
    (clarsimp simp: is_ntfn idle_no_ex_cap elim!: obj_at_weakenE)?)
   apply (erule (1) obj_at_valid_objsE)
   apply (clarsimp simp: valid_obj_def valid_ntfn_def pred_tcb_at_tcb_at
                  elim!: obj_atE
                  split: ntfn.splits)
  apply (rule conjI)
   apply (clarsimp simp: obj_at_def pred_tcb_at_def2)
  apply (rule impI, erule delta_sym_refs)
   apply (fastforce dest!: symreftype_inverse'
                     simp: ntfn_q_refs_of_def obj_at_def
                    split: ntfn.splits if_split_asm)
  apply (fastforce simp: state_refs_of_def pred_tcb_at_def2 obj_at_def
                         tcb_st_refs_of_def
                  split: thread_state.splits if_split_asm)
  done

lemma (in Tcb_AI) tcbinv_invs:
  "\<lbrace>(invs::('state_ext::state_ext) state\<Rightarrow>bool) and tcb_inv_wf ti\<rbrace>
     invoke_tcb ti
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (case_tac ti, simp_all only:)
         apply ((wp writereg_invs readreg_invs copyreg_invs tc_invs
              | simp
              | clarsimp simp: invs_def valid_state_def valid_pspace_def
                        dest!: idle_no_ex_cap
                        split: option.split
              | rule conjI)+)[6]
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

(*FIXME Move up*)
lemma OR_choice_E_weak_wp: "\<lbrace>P\<rbrace> f \<sqinter> g \<lbrace>Q\<rbrace>,- \<Longrightarrow> \<lbrace>P\<rbrace> OR_choice b f g \<lbrace>Q\<rbrace>,-"
  apply (simp add: validE_R_def validE_def OR_choice_weak_wp)
  done

lemma OR_choiceE_E_weak_wp: "\<lbrace>P\<rbrace> f \<sqinter> g \<lbrace>Q\<rbrace>,- \<Longrightarrow> \<lbrace>P\<rbrace> OR_choiceE b f g \<lbrace>Q\<rbrace>,-"
  apply (simp add: validE_R_def validE_def OR_choiceE_weak_wp)
  done

lemma thread_get_pred_tcb_at_wp:
  "\<lbrace>\<lambda>s. \<forall>f. pred_tcb_at proj ((=) f) t s \<longrightarrow> P f s \<rbrace> thread_get (proj \<circ> tcb_to_itcb) t \<lbrace>P\<rbrace>"
  apply (wp thread_get_wp')
  apply clarsimp
  apply (drule spec, erule mp)
  by (simp add: pred_tcb_at_def obj_at_def)

lemma thread_get_ret:
  "\<lbrace>\<top>\<rbrace> thread_get (proj \<circ> tcb_to_itcb) t \<lbrace>\<lambda>rv. pred_tcb_at proj ((=) rv) t\<rbrace>"
  apply (simp add: thread_get_def)
  apply wp
  by (clarsimp simp: pred_tcb_at_def)

lemmas get_mcpriority_wp =
  thread_get_pred_tcb_at_wp[where proj=itcb_mcpriority, simplified comp_def, simplified]

lemmas get_mcpriority_get =
  thread_get_ret[where proj=itcb_mcpriority, simplified comp_def, simplified]

crunch inv: check_prio "P"
  (simp: crunch_simps)

lemma check_prio_wp:
  "\<lbrace>\<lambda>s. mcpriority_tcb_at (\<lambda>mcp. prio \<le> ucast mcp) auth s \<longrightarrow> Q s\<rbrace> check_prio prio auth \<lbrace>\<lambda>_. Q\<rbrace>, -"
  apply (clarsimp simp: check_prio_def)
  apply (wp get_mcpriority_wp whenE_throwError_wp)
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

lemma (in Tcb_AI) decode_set_sched_params_wf[wp]:
  "\<lbrace>invs and tcb_at t and ex_nonz_cap_to t\<rbrace>
        decode_set_sched_params args (ThreadCap t) slot excs \<lbrace>tcb_inv_wf\<rbrace>, -"
  by (wpsimp simp: decode_set_sched_params_def wp: check_prio_wp_weak whenE_throwError_wp)

lemma decode_set_priority_is_tc[wp]:
  "\<lbrace>\<top>\<rbrace> decode_set_priority args cap slot excs \<lbrace>\<lambda>rv s. is_ThreadControl rv\<rbrace>,-"
  by (wpsimp simp: decode_set_priority_def)

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
  "\<lbrace>(invs::('state_ext::state_ext) state\<Rightarrow>bool) and tcb_at t and cte_at slot and ex_cte_cap_to slot
      and ex_nonz_cap_to t
      and (\<lambda>s. \<forall>x \<in> set excaps. s \<turnstile> fst x \<and> cte_at (snd x) s
                          \<and> ex_cte_cap_to (snd x) s
                          \<and> no_cap_to_obj_dr_emp (fst x) s)\<rbrace>
     decode_set_ipc_buffer args (cap.ThreadCap t) slot excaps
   \<lbrace>tcb_inv_wf\<rbrace>,-"
  apply (simp   add: decode_set_ipc_buffer_def whenE_def split_def
          split del: if_split)
  apply (rule hoare_pre, wp check_valid_ipc_buffer_wp)
     apply simp
     apply (wp derive_cap_valid_cap hoare_drop_imps)[1]
    apply wp+
  apply (clarsimp simp: neq_Nil_conv)
  done

lemma decode_set_ipc_is_tc[wp]:
  "\<lbrace>\<top>\<rbrace> decode_set_ipc_buffer args cap slot excaps \<lbrace>\<lambda>rv s. is_ThreadControl rv\<rbrace>,-"
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


lemma (in Tcb_AI) decode_set_space_wf[wp]:
  "\<lbrace>(invs::('state_ext::state_ext) state\<Rightarrow>bool)
  and tcb_at t and cte_at slot and ex_cte_cap_to slot
          and ex_nonz_cap_to t
          and (\<lambda>s. \<forall>x \<in> set extras. s \<turnstile> fst x \<and> cte_at (snd x) s
                          \<and> ex_cte_cap_to (snd x) s
                          \<and> t \<noteq> fst (snd x)
                          \<and> no_cap_to_obj_dr_emp (fst x) s)\<rbrace>
     decode_set_space args (ThreadCap t) slot extras
   \<lbrace>tcb_inv_wf\<rbrace>,-"
  apply (simp   add: decode_set_space_def whenE_def unlessE_def
          split del: if_split)
  apply (rule hoare_pre)
   apply (wp derive_cap_valid_cap
             | simp add: o_def split del: if_split
             | rule hoare_drop_imps)+
  apply (clarsimp split del: if_split simp: ball_conj_distrib
                   simp del: length_greater_0_conv)
  apply (simp add: update_cap_data_validI word_bits_def
                   no_cap_to_obj_with_diff_ref_update_cap_data
              del: length_greater_0_conv)
  done

lemma decode_set_space_inv[wp]:
  "\<lbrace>P\<rbrace> decode_set_space args cap slot extras \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp   add: decode_set_space_def whenE_def unlessE_def
          split del: if_split)
  apply (rule hoare_pre)
   apply (wp hoare_drop_imps | simp)+
  done

lemma decode_set_space_is_tc[wp]:
  "\<lbrace>\<top>\<rbrace> decode_set_space args cap slot extras \<lbrace>\<lambda>rv s. is_ThreadControl rv\<rbrace>,-"
  apply (rule hoare_pre)
   apply (simp   add: decode_set_space_def whenE_def unlessE_def
           split del: if_split)
   apply (wp | simp only: tcb_invocation.disc)+
  done

lemma decode_set_mcpriority_is_tc[wp]:
  "\<lbrace>\<top>\<rbrace> decode_set_mcpriority args cap slot excs \<lbrace>\<lambda>rv s. is_ThreadControl rv\<rbrace>,-"
  by (wpsimp simp: decode_set_mcpriority_def)

lemma decode_set_space_target[wp]:
  "\<lbrace>\<lambda>s. P (obj_ref_of cap)\<rbrace>
   decode_set_space args cap slot extras
   \<lbrace>\<lambda>rv s. P (tc_target rv)\<rbrace>,-"
  unfolding decode_set_space_def
  by (wpsimp split_del: if_split)

(* FIXME: move to lib and rename*)
lemma boring_simp[simp]:
  "(if x then True else False) = x" by simp

lemma (in Tcb_AI) decode_tcb_conf_wf[wp]:
  "\<lbrace>(invs::('state_ext::state_ext) state\<Rightarrow>bool)
         and tcb_at t and cte_at slot and ex_cte_cap_to slot
         and ex_nonz_cap_to t
         and (\<lambda>s. \<forall>x \<in> set extras. s \<turnstile> fst x \<and> cte_at (snd x) s
                                 \<and> ex_cte_cap_to (snd x) s
                                 \<and> t \<noteq> fst (snd x)
                                 \<and> no_cap_to_obj_dr_emp (fst x) s)\<rbrace>
     decode_tcb_configure args (cap.ThreadCap t) slot extras
   \<lbrace>tcb_inv_wf\<rbrace>,-"
  apply (clarsimp simp add: decode_tcb_configure_def Let_def)
  apply (rule hoare_pre)
   apply wp
      apply (rule_tac Q'="\<lambda>set_space s. tcb_inv_wf set_space s \<and> tcb_inv_wf set_params s
                              \<and> is_ThreadControl set_space \<and> is_ThreadControl set_params
                              \<and> tc_target set_space = t
                              \<and> cte_at slot s \<and> ex_cte_cap_to slot s"
                 in hoare_post_imp_R)
       apply wp
      apply (clarsimp simp: is_ThreadControl_def cong: option.case_cong)
     apply (wp | simp add: whenE_def split del: if_split)+
  apply (clarsimp simp: linorder_not_less val_le_length_Cons
                   del: ballI)
  done

lemma (in Tcb_AI) decode_tcb_conf_inv[wp]:
  "\<lbrace>P::'state_ext state \<Rightarrow> bool\<rbrace> decode_tcb_configure args cap slot extras \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (clarsimp simp add: decode_tcb_configure_def Let_def whenE_def
                 split del: if_split)
  apply (rule hoare_pre, wp)
  apply simp
  done


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
  by (wpsimp wp: get_simple_ko_wp gbn_wp
             simp: whenE_def if_apply_def2
             split_del: if_split)

lemma (in Tcb_AI) decode_tcb_inv_inv:
  "\<lbrace>P::'state_ext state \<Rightarrow> bool\<rbrace>
     decode_tcb_invocation label args (cap.ThreadCap t) slot extras
   \<lbrace>\<lambda>rv. P\<rbrace>"
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
   apply (wp get_simple_ko_wp gbn_wp | wpc)+
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
   apply (wp gbn_wp | wpc)+
  apply clarsimp
  done

lemma decode_tcb_inv_wf:
  "\<lbrace>invs and tcb_at t and ex_nonz_cap_to t
         and cte_at slot and ex_cte_cap_to slot
         and (\<lambda>(s::'state_ext::state_ext state). \<forall>x \<in> set extras. real_cte_at (snd x) s \<and> s \<turnstile> fst x
                                 \<and> ex_cte_cap_to (snd x) s
                                 \<and> (\<forall>y \<in> zobj_refs (fst x). ex_nonz_cap_to y s)
                                 \<and> no_cap_to_obj_dr_emp (fst x) s)\<rbrace>
      decode_tcb_invocation label args (cap.ThreadCap t) slot extras
   \<lbrace>tcb_inv_wf\<rbrace>,-"
  apply (simp add: decode_tcb_invocation_def Let_def
              cong: if_cong split del: if_split)
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

lemma out_pred_tcb_at_preserved:
  "\<lbrakk> \<And>tcb x. tcb_state (f x tcb) = tcb_state tcb \<rbrakk> \<Longrightarrow>
   \<lbrace>st_tcb_at P t\<rbrace> option_update_thread t' f opt \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  apply (cases opt, simp_all add: option_update_thread_def)
  apply (rule thread_set_no_change_tcb_state)
  apply simp
  done

lemma pred_tcb_at_arch_state[simp]:
  "pred_tcb_at proj P t (arch_state_update f s) = pred_tcb_at proj P t s"
  by (simp add: pred_tcb_at_def obj_at_def)

lemma invoke_domain_invs:
  "\<lbrace>invs\<rbrace>
     invoke_domain t d
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (simp add: invoke_domain_def | wp)+

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
  "(x, NTFNBound) \<notin> tcb_bound_refs a"
  by (simp add: tcb_bound_refs_def split: option.splits)

lemma tcb_st_refs_of_no_NTFNBound:
  "(x, NTFNBound) \<notin> tcb_st_refs_of z"
  by (simp add: tcb_st_refs_of_def split: thread_state.splits)

lemma tcb_not_in_state_refs_of_tcb:
  "tcb_at a s \<Longrightarrow> (a, NTFNBound) \<notin> state_refs_of s a"
  apply (clarsimp simp: tcb_at_def obj_at_def is_tcb_def)
  apply (case_tac ko)
  apply simp_all
  apply (clarsimp simp: state_refs_of_def tcb_st_refs_of_def tcb_bound_refs_def)
  apply (erule disjE)
  apply (rename_tac tcb_ext)
  apply (case_tac "tcb_state tcb_ext")
  apply simp_all
  apply (simp split: option.splits)
  done

lemma ntfn_bound_refs_def2:
  "ntfn_bound_refs t = set_option t \<times> {NTFNBound}"
  by (clarsimp simp: ntfn_bound_refs_def split: option.splits)

lemma unbind_notification_sym_refs[wp]:
  "\<lbrace>\<lambda>s. sym_refs (state_refs_of s) \<and> valid_objs s \<and> tcb_at a s\<rbrace>
     unbind_notification a
   \<lbrace>\<lambda>rv s. sym_refs (state_refs_of s)\<rbrace>"
  apply (simp add: unbind_notification_def)
  apply (rule hoare_seq_ext [OF _ gbn_sp])
  apply (case_tac ntfnptr, simp_all)
   apply (wp, simp)
  apply (rule hoare_seq_ext [OF _ get_simple_ko_sp])
  apply (wp | wpc | simp)+
  apply (rule conjI)
   apply (fastforce simp: obj_at_def pred_tcb_at_def)
  apply (rule impI, clarsimp)
  apply (rule delta_sym_refs, assumption)
   apply (fastforce simp: obj_at_def pred_tcb_at_def ntfn_q_refs_of_def
                          state_refs_of_def
                    split: if_split_asm)
  apply (auto simp: valid_obj_def obj_at_def ntfn_bound_refs_def2 symreftype_inverse'
                    ntfn_q_refs_of_def tcb_ntfn_is_bound_def state_refs_of_def
                    tcb_st_refs_of_def tcb_bound_refs_def2
              split: ntfn.splits thread_state.splits if_split_asm
              dest!: sym_refs_bound_tcb_atD refs_in_ntfn_bound_refs
              elim!: obj_at_valid_objsE
              intro!: ntfn_q_refs_no_NTFNBound)
  done

lemma tcb_cap_cases_tcb_mcpriority:
  "\<forall>(getF, v)\<in>ran tcb_cap_cases.
         getF (tcb_mcpriority_update F tcb) = getF tcb"
  by (rule ball_tcb_cap_casesI, simp+)

crunch tcb_at[wp]: set_mcpriority "tcb_at r"

lemma set_mcpriority_no_cap_to_obj_with_diff_ref[wp]:
  "\<lbrace>no_cap_to_obj_with_diff_ref c S\<rbrace> set_mcpriority t mcp \<lbrace>\<lambda>rv. no_cap_to_obj_with_diff_ref c S\<rbrace>"
  by (simp add: set_mcpriority_def thread_set_no_cap_to_trivial tcb_cap_cases_tcb_mcpriority)

end
