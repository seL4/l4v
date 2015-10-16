(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory Tcb_AI
imports CNodeInv_AI
begin
 
lemma ct_in_state_weaken:
  "\<lbrakk> ct_in_state Q s; \<And>st. Q st \<Longrightarrow> P st \<rbrakk> \<Longrightarrow> ct_in_state P s"
  by (clarsimp simp: ct_in_state_def pred_tcb_at_def obj_at_def)

lemma ct_in_state_exst_update[simp]: "ct_in_state P (trans_state f s) = ct_in_state P s"
  by (simp add: ct_in_state_def)

lemma set_thread_state_ct_st:
  "\<lbrace>\<lambda>s. if thread = cur_thread s then P st else ct_in_state P s\<rbrace>
        set_thread_state thread st
   \<lbrace>\<lambda>rv. ct_in_state P\<rbrace>"
  apply (simp add: set_thread_state_def set_object_def)
  apply (wp|simp)+
  apply (clarsimp simp: ct_in_state_def pred_tcb_at_def obj_at_def)
  done

lemma activate_idle_invs:
  "\<lbrace>invs and ct_idle\<rbrace>
     arch_activate_idle_thread thread
   \<lbrace>\<lambda>rv. invs and ct_idle\<rbrace>"
  by (simp add: arch_activate_idle_thread_def)

lemma activate_invs:
  "\<lbrace>invs\<rbrace> activate_thread \<lbrace>\<lambda>rv s. invs s \<and> (ct_running s \<or> ct_idle s)\<rbrace>"
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
  apply (wp set_cap_cte_wp_at')
  apply (rule hoare_strengthen_post, rule get_cap_sp)
  apply clarsimp
  apply (frule(1) cte_wp_tcb_cap_valid[simplified cte_wp_at_eq_simp])
  apply (clarsimp simp: tcb_cap_valid_def st_tcb_def2)
  apply (auto simp: cte_wp_at_caps_of_state is_cap_simps)
  done


lemma setup_reply_master_has_reply[wp]:
  "\<lbrace>\<lambda>s. P (has_reply_cap t s)\<rbrace> setup_reply_master t' \<lbrace>\<lambda>rv s. P (has_reply_cap t s)\<rbrace>"
  apply (simp add: has_reply_cap_def cte_wp_at_caps_of_state
                   setup_reply_master_def)
  apply (rule hoare_pre, wp get_cap_wp)
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
  apply (rule hoare_pre)
  apply (wp sts_invs_minor ipc_cancel_ex_nonz_cap_to_tcb
            hoare_vcg_disj_lift ipc_cancel_simple2 
       | simp add: if_apply_def2
       | strengthen invs_valid_objs2)+
  apply (auto dest!: idle_no_ex_cap simp: invs_def valid_state_def valid_pspace_def)
  done

crunch typ_at[wp]: setup_reply_master "\<lambda>s. P (typ_at T p s)"

lemma restart_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> Tcb_A.restart t \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  apply (simp add: Tcb_A.restart_def)
  apply (wp ipc_cancel_typ_at | simp)+
  done


lemma restart_tcb[wp]:
  "\<lbrace>tcb_at t'\<rbrace> Tcb_A.restart t \<lbrace>\<lambda>rv. tcb_at t'\<rbrace>"
  by (simp add: tcb_at_typ, wp restart_typ_at)

lemma copyAreaToRegs_typ_at:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> copyAreaToRegs regs a b \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  apply (simp add: copyAreaToRegs_def)
  apply (wp thread_set_typ_at)
   apply (rule mapM_wp [where S=UNIV, simplified])
   apply (simp add: load_word_offs_def)
   apply wp
  done

lemma copyAreaToRegs_tcb'[wp]:
  "\<lbrace>tcb_at t\<rbrace> copyAreaToRegs regs a b \<lbrace>\<lambda>rv. tcb_at t\<rbrace>"
  by (simp add: tcb_at_typ, wp copyAreaToRegs_typ_at)


lemma empty_fail_getRegister [intro!, simp]:
  "empty_fail (getRegister r)"
  by (simp add: getRegister_def)


lemma copyRegsToArea_typ_at:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> copyRegsToArea regs a b \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  apply (simp add: copyRegsToArea_def)
  apply (wp zipWithM_x_inv)
   apply simp
  apply wp
  done

lemma copyRegsToArea_tcb'[wp]:
  "\<lbrace>tcb_at t\<rbrace> copyRegsToArea regs a b \<lbrace>\<lambda>rv. tcb_at t\<rbrace>"
  by (simp add: tcb_at_typ, wp copyRegsToArea_typ_at)


lemma copyRegsToArea_invs[wp]:
  "\<lbrace>invs\<rbrace> copyRegsToArea regs a b \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: copyRegsToArea_def)
  apply (wp zipWithM_x_inv)
   apply simp
  apply wp
  done


lemma copyAreaToRegs_invs[wp]:
  "\<lbrace>invs and tcb_at b\<rbrace> copyAreaToRegs regs a b \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: copyAreaToRegs_def)
  apply wp
    apply (rule thread_set_invs_trivial, (simp add: tcb_cap_cases_def)+)
   apply (rule mapM_wp [where S=UNIV, simplified])
   apply wp
  apply simp
  done


lemmas suspend_tcb_at[wp] = tcb_at_typ_at [OF suspend_typ_at]

lemma suspend_nonz_cap_to_tcb:
  "\<lbrace>\<lambda>s. ex_nonz_cap_to t s \<and> tcb_at t s \<and> valid_objs s\<rbrace>
     suspend t'
   \<lbrace>\<lambda>rv s. ex_nonz_cap_to t s\<rbrace>"
  apply (simp add: suspend_def)
  apply (wp ipc_cancel_ex_nonz_cap_to_tcb|simp)+
  done

lemma readreg_invs:
  "\<lbrace>invs and tcb_at src and ex_nonz_cap_to src\<rbrace>
     invoke_tcb (tcb_invocation.ReadRegisters src susp n arch)
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (simp | wp)+
     (clarsimp simp: invs_def valid_state_def valid_pspace_def
              dest!: idle_no_ex_cap)

lemma writereg_invs:
  "\<lbrace>invs and tcb_at dest and ex_nonz_cap_to dest\<rbrace>
     invoke_tcb (tcb_invocation.WriteRegisters dest resume values arch)
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (clarsimp | rule conjI | wp)+

lemma copyreg_invs:
  "\<lbrace>invs and tcb_at src and tcb_at dest and ex_nonz_cap_to dest and
    ex_nonz_cap_to src\<rbrace>
     invoke_tcb (tcb_invocation.CopyRegisters dest src susp resume frames ints arch)
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: if_apply_def2
            | wp mapM_x_wp' suspend_nonz_cap_to_tcb static_imp_wp)+
  apply (clarsimp simp: invs_def valid_state_def valid_pspace_def
                 dest!: idle_no_ex_cap)
  done

lemma out_invs_trivialT:
  assumes x: "\<And>tcb v. \<forall>(getF, setF)\<in>ran tcb_cap_cases. getF (fn v tcb) = getF tcb"
  assumes z: "\<And>tcb v. tcb_state  (fn v tcb) = tcb_state  tcb"
  assumes z': "\<And>tcb v. tcb_bound_aep (fn v tcb) = tcb_bound_aep tcb"
  assumes w: "\<And>tcb v. tcb_ipc_buffer (fn v tcb) = tcb_ipc_buffer tcb
                          \<or> tcb_ipc_buffer (fn v tcb) = 0"
  assumes y: "\<And>tcb v'. v = Some v' \<Longrightarrow> tcb_fault_handler (fn v' tcb) \<noteq> tcb_fault_handler tcb
                       \<longrightarrow> length (tcb_fault_handler (fn v' tcb)) = word_bits"
  assumes a: "\<And>tcb v. tcb_fault (fn v tcb) \<noteq> tcb_fault tcb
                       \<longrightarrow> (case tcb_fault (fn v tcb) of None \<Rightarrow> True
                                                   | Some f \<Rightarrow> valid_fault f)"
  shows      "\<lbrace>invs\<rbrace> option_update_thread t fn v \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (case_tac v, simp_all add: option_update_thread_def)
  apply (rule thread_set_invs_trivial [OF x z z' w y a])
  apply auto
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

lemma set_endpoint_valid_cap:
  "\<lbrace>valid_cap c\<rbrace> set_endpoint e ep \<lbrace>\<lambda>_. valid_cap c\<rbrace>"
  by (wp valid_cap_typ)


lemma set_endpoint_cte_at[wp]:
  "\<lbrace>cte_at p\<rbrace> set_endpoint ptr val \<lbrace>\<lambda>_. cte_at p\<rbrace>"
  by (wp valid_cte_at_typ)


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
  "\<lbrace>cte_at p\<rbrace> send_ipc bl c ba cg t ep \<lbrace>\<lambda>_. cte_at p\<rbrace>"
  by (wp valid_cte_at_typ)


lemma ri_cte_at[wp]:
  "\<lbrace>cte_at p\<rbrace> receive_ipc t cap \<lbrace>\<lambda>_. cte_at p\<rbrace>"
  by (wp valid_cte_at_typ)


lemma set_aep_cte_at[wp]:
  "\<lbrace>\<lambda>s. cte_at p s\<rbrace> set_async_ep p' aep \<lbrace>\<lambda>_ s. cte_at p s\<rbrace>"
  by (wp valid_cte_at_typ)



lemma rai_cte_at[wp]:
  "\<lbrace>cte_at p\<rbrace> receive_async_ipc t cap is_blocking \<lbrace>\<lambda>_. cte_at p\<rbrace>"
  by (wp valid_cte_at_typ)


lemma hf_cte_at[wp]:
  "\<lbrace>cte_at p\<rbrace> handle_fault t ft \<lbrace>\<lambda>_. cte_at p\<rbrace>"
  by (wp valid_cte_at_typ)


lemma do_ipc_transfer_cte_at[wp]:
  "\<lbrace>cte_at p\<rbrace> do_ipc_transfer s ep b g r d \<lbrace>\<lambda>_. cte_at p\<rbrace>"
  by (wp valid_cte_at_typ)


lemma ep_cancel_all_tcb:
  "\<lbrace>tcb_at t\<rbrace> ep_cancel_all ptr \<lbrace>\<lambda>_. tcb_at t\<rbrace>"
  by (simp add: tcb_at_typ, wp ep_cancel_all_typ_at)


lemma get_async_ep_sp:
  "\<lbrace>P\<rbrace> get_async_ep p \<lbrace>\<lambda>aep. ko_at (AsyncEndpoint aep) p and P\<rbrace>"
  apply (simp add: get_async_ep_def)
  apply wp
   prefer 2
   apply (rule get_object_sp)
  apply (case_tac kobj)
  apply (simp|wp)+
  done


lemma thread_set_valid_objs':
  "\<lbrace>valid_objs and (\<lambda>s. \<forall>p t. valid_tcb p t s \<longrightarrow> valid_tcb p (f t) s)\<rbrace>
  thread_set f t
  \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  apply (simp add: thread_set_def)
  apply wp
   apply (rule set_object_valid_objs)
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


lemma same_object_also_valid:
  "\<lbrakk> same_object_as cap cap'; s \<turnstile> cap'; wellformed_cap cap;
     cap_asid cap = None \<or> (\<exists>asid. cap_asid cap = Some asid \<and> 0 < asid \<and> asid \<le> 2^asid_bits - 1);
     cap_vptr cap = None; cap_asid_base cap = None \<rbrakk>
     \<Longrightarrow> s \<turnstile> cap"
  apply (cases cap,
         (clarsimp simp: same_object_as_def is_cap_simps cap_asid_def
                         wellformed_cap_def wellformed_acap_def
                         valid_cap_def bits_of_def cap_aligned_def
                   split: cap.split_asm arch_cap.split_asm option.splits)+)
  done


lemma same_object_as_cte_refs:
  "\<lbrakk> same_object_as cap cap' \<rbrakk> \<Longrightarrow>
     cte_refs cap' = cte_refs cap"
  apply (rule ext, cases cap, simp_all add: same_object_as_def)
       apply (clarsimp simp: is_cap_simps bits_of_def
                      split: cap.split_asm arch_cap.split_asm)+
  done


lemma same_object_untyped_range:
  "\<lbrakk> same_object_as cap cap' \<rbrakk>
     \<Longrightarrow> untyped_range cap = {}"
  by (cases cap, (clarsimp simp: same_object_as_def is_cap_simps)+)


lemma same_object_obj_refs:
  "\<lbrakk> same_object_as cap cap' \<rbrakk>
     \<Longrightarrow> obj_refs cap = obj_refs cap'"
  apply (cases cap, simp_all add: same_object_as_def)
       apply (clarsimp simp: is_cap_simps bits_of_def
                      split: cap.split_asm arch_cap.split_asm)+
     apply (rename_tac arch_cap, case_tac arch_cap, simp_all)+
  done


lemma same_object_zombies:
  "\<lbrakk> same_object_as cap cap' \<rbrakk>
     \<Longrightarrow> is_zombie cap = is_zombie cap'"
  by (cases cap, (clarsimp simp: same_object_as_def is_cap_simps
                          split: arch_cap.split_asm)+)


lemma zombies_final_helperE:
  "\<lbrakk> caps_of_state s p = Some cap; r \<in> obj_refs cap; \<not> is_zombie cap;
     zombies_final s; caps_of_state s p' = Some cap'; r \<in> obj_refs cap' \<rbrakk>
     \<Longrightarrow> \<not> is_zombie cap'"
  apply (cases p', drule caps_of_state_cteD[simplified cte_wp_at_eq_simp],
         drule(2) zombies_final_helper)
  apply (fastforce simp: cte_wp_at_caps_of_state)
  done


definition
  is_cnode_or_valid_arch :: "cap \<Rightarrow> bool"
where
 "is_cnode_or_valid_arch cap \<equiv>
    is_cnode_cap cap
     \<or> (is_arch_cap cap
          \<and> (is_pt_cap cap \<longrightarrow> cap_asid cap \<noteq> None)
          \<and> (is_pd_cap cap \<longrightarrow> cap_asid cap \<noteq> None))"


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


lemma cap_master_pt_pd:
  "cap_master_cap cap = cap_master_cap cap'
     \<Longrightarrow> (is_pt_cap cap = is_pt_cap cap')
            \<and> (is_pd_cap cap = is_pd_cap cap')"
  by (auto simp: is_pt_cap_def is_pd_cap_def
                 cap_master_cap_simps
          dest!: cap_master_cap_eqDs)


definition
  "pt_pd_asid cap \<equiv> case cap of
    Structures_A.ArchObjectCap (ARM_Structs_A.PageTableCap _ (Some (asid, _))) \<Rightarrow> Some asid
  | Structures_A.ArchObjectCap (ARM_Structs_A.PageDirectoryCap _ (Some asid)) \<Rightarrow> Some asid
  | _ \<Rightarrow> None"


lemmas pt_pd_asid_simps [simp] =
  pt_pd_asid_def [split_simps cap.split arch_cap.split option.split prod.split]


lemma checked_insert_is_derived:
  "\<lbrakk> same_object_as new_cap old_cap; is_cnode_or_valid_arch new_cap;
     obj_refs new_cap = obj_refs old_cap
         \<longrightarrow> table_cap_ref old_cap = table_cap_ref new_cap
            \<and> pt_pd_asid old_cap = pt_pd_asid new_cap\<rbrakk>
     \<Longrightarrow> is_derived m slot new_cap old_cap"
  apply (cases slot)
  apply (frule same_object_as_cap_master)
  apply (frule master_cap_obj_refs)
  apply (frule cap_master_eq_badge_none)
  apply (frule cap_master_pt_pd)
  apply (simp add: is_derived_def)
  apply clarsimp
  apply (auto simp: is_cap_simps cap_master_cap_def
                    is_cnode_or_valid_arch_def vs_cap_ref_def
                    table_cap_ref_def pt_pd_asid_def up_ucast_inj_eq
             split: cap.split_asm arch_cap.split_asm
                    option.split_asm)[1]
  done


lemma is_cnode_or_valid_arch_cap_asid:
  "is_cnode_or_valid_arch cap
       \<Longrightarrow> (is_pt_cap cap \<longrightarrow> cap_asid cap \<noteq> None)
             \<and> (is_pd_cap cap \<longrightarrow> cap_asid cap \<noteq> None)"
  by (auto simp add: is_cnode_or_valid_arch_def
                     is_cap_simps)


lemma checked_insert_tcb_invs[wp]:
  "\<lbrace>invs and cte_wp_at (\<lambda>c. c = cap.NullCap) (target, ref)
        and K (is_cnode_or_valid_arch new_cap) and valid_cap new_cap
        and tcb_cap_valid new_cap (target, ref)
        and K (is_pt_cap new_cap \<or> is_pd_cap new_cap
                         \<longrightarrow> cap_asid new_cap \<noteq> None)
        and (cte_wp_at (\<lambda>c. obj_refs c = obj_refs new_cap
                              \<longrightarrow> table_cap_ref c = table_cap_ref new_cap \<and>
                                 pt_pd_asid c = pt_pd_asid new_cap) src_slot)\<rbrace>
     check_cap_at new_cap src_slot
      (check_cap_at (cap.ThreadCap target) slot
       (cap_insert new_cap src_slot (target, ref))) \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: check_cap_at_def)
  apply (rule hoare_pre)
   apply (wp get_cap_wp)
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (frule caps_of_state_valid_cap[where p=src_slot], fastforce)
  apply (frule caps_of_state_valid_cap[where p=slot], fastforce)
  apply (rule conjI, simp only: ex_cte_cap_wp_to_def)
   apply (rule_tac x=slot in exI)
   apply (clarsimp simp: cte_wp_at_caps_of_state same_object_as_cte_refs)
   apply (clarsimp simp: same_object_as_def2 cap_master_cap_simps
                  dest!: cap_master_cap_eqDs)
   apply (clarsimp simp: valid_cap_def[where c="cap.ThreadCap x" for x])
   apply (erule cte_wp_atE[OF caps_of_state_cteD])
    apply (fastforce simp: obj_at_def is_obj_defs)
   apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (subgoal_tac "\<not> is_zombie new_cap")
    apply (simp add: same_object_zombies same_object_obj_refs)
    apply (erule(2) zombies_final_helperE)
      apply fastforce
     apply (fastforce simp add: cte_wp_at_caps_of_state)
    apply assumption
   apply (clarsimp simp: is_cnode_or_valid_arch_def is_cap_simps
                         is_valid_vtable_root_def)
  apply (rule conjI)
   apply (erule(1) checked_insert_is_derived, simp+)
  apply (auto simp: is_cnode_or_valid_arch_def is_cap_simps)
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

lemma thread_set_emptyable[wp]:
  assumes x: "\<And>tcb. tcb_state (fn tcb) = tcb_state tcb"
  shows      "\<lbrace>emptyable sl\<rbrace> thread_set fn p \<lbrace>\<lambda>rv. emptyable sl\<rbrace>"
  by (wp emptyable_lift x thread_set_no_change_tcb_state)


crunch not_cte_wp_at[wp]: unbind_maybe_aep "\<lambda>s. \<forall>cp\<in>ran (caps_of_state s). P cp"
  (wp: thread_set_caps_of_state_trivial simp: tcb_cap_cases_def)

lemma finalise_cap_not_cte_wp_at:
  assumes x: "P cap.NullCap"
  shows      "\<lbrace>\<lambda>s. \<forall>cp \<in> ran (caps_of_state s). P cp\<rbrace>
                finalise_cap cap fin
              \<lbrace>\<lambda>rv s. \<forall>cp \<in> ran (caps_of_state s). P cp\<rbrace>"
  apply (cases cap, simp_all)
       apply (wp suspend_caps_of_state hoare_vcg_all_lift
            | simp
            | rule impI
            | rule hoare_drop_imps)+
     apply (clarsimp simp: ball_ran_eq x)
    apply (wp delete_one_caps_of_state
         | rule impI
         | simp add: deleting_irq_handler_def get_irq_slot_def x ball_ran_eq)+
    done

lemma rec_del_all_caps_in_range:
  assumes x: "P cap.NullCap"
      and y: "\<And>x n zt. P (cap.ThreadCap x) \<Longrightarrow> P (cap.Zombie x zt n)"
      and z: "\<And>x y gd rs rs' n zt. P (cap.CNodeCap x y gd) \<Longrightarrow> P (cap.Zombie x zt n)"
      and w: "\<And>x zt zt' n m. P (cap.Zombie x zt n) \<Longrightarrow> P (cap.Zombie x zt' m)"
  shows      "s \<turnstile> \<lbrace>\<lambda>s. \<forall>cp \<in> ran (caps_of_state s). P cp\<rbrace>
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
    apply (rule hoare_pre_spec_validE)
     apply (wp hyps, simp+)
          apply ((wp irq_state_independent_AI preemption_point_inv | simp)+)[1]
         apply (simp only: simp_thms)
         apply (wp hyps, simp+)
        apply wp
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
        apply (case_tac rv, simp_all add: fst_cte_ptrs_def)[1]
          apply (simp add: z)
         apply (simp add: y)
        apply (simp split: option.split_asm, simp_all add: w)[1]
       apply (cases slot, fastforce)
      apply (simp add: is_final_cap_def)
      apply (wp get_cap_wp)
    apply clarsimp
    done
next
  case (3 ptr bits n slot s')
  show ?case
    apply simp
    apply wp
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

lemmas vs_cap_ref_simps =
  vs_cap_ref_def [split_simps cap.split arch_cap.split option.split prod.split]


lemma use_no_cap_to_obj_asid_strg:
  "(cte_at p s \<and> no_cap_to_obj_dr_emp cap s \<and> valid_cap cap s \<and> invs s)
         \<longrightarrow> cte_wp_at (\<lambda>c. obj_refs c = obj_refs cap
                \<longrightarrow> table_cap_ref c = table_cap_ref cap \<and> pt_pd_asid c = pt_pd_asid cap) p s"
  apply (clarsimp simp: cte_wp_at_caps_of_state
                     no_cap_to_obj_with_diff_ref_def
           simp del: split_paired_All)
  apply (frule caps_of_state_valid_cap, fastforce)
  apply (erule allE)+
  apply (erule (1) impE)+
  apply (simp add: table_cap_ref_def pt_pd_asid_def split: cap.splits arch_cap.splits option.splits prod.splits)
  apply (fastforce simp: table_cap_ref_def valid_cap_simps elim!: asid_low_high_bits)+
  done

lemma no_cap_to_obj_with_diff_ref_ran_caps_form:
  "no_cap_to_obj_dr_emp cap
     = (\<lambda>s. \<forall>cp \<in> ran (caps_of_state s).
              obj_refs cp = obj_refs cap \<longrightarrow> table_cap_ref cp = table_cap_ref cap)"
  apply (rule ext, simp add: no_cap_to_obj_with_diff_ref_def)
  apply (simp add: ball_ran_eq cte_wp_at_caps_of_state)
  apply auto
  done

lemma cap_delete_no_cap_to_obj_asid[wp]:
  "\<lbrace>no_cap_to_obj_dr_emp cap\<rbrace>
     cap_delete slot
   \<lbrace>\<lambda>rv. no_cap_to_obj_dr_emp cap\<rbrace>"
  apply (simp add: cap_delete_def
                   no_cap_to_obj_with_diff_ref_ran_caps_form)
  apply wp
  apply simp
  apply (rule use_spec)
  apply (rule rec_del_all_caps_in_range)
     apply (simp add: table_cap_ref_def[split_simps cap.split]
              | rule obj_ref_none_no_asid)+
  done

lemma out_no_cap_to_trivial:
  "(\<And>tcb v. \<forall>(getF, x)\<in>ran tcb_cap_cases. getF (f v tcb) = getF tcb)
   \<Longrightarrow> \<lbrace>no_cap_to_obj_with_diff_ref cap S\<rbrace>
         option_update_thread a f t
      \<lbrace>\<lambda>rv. no_cap_to_obj_with_diff_ref cap S\<rbrace>"
  apply (simp add: no_cap_to_obj_with_diff_ref_def)
  apply (wp hoare_vcg_const_Ball_lift out_cte_wp_at_trivialT)
  apply assumption
  done

lemma thread_set_no_cap_to_trivial:
  "(\<And>tcb. \<forall>(getF, v)\<in>ran tcb_cap_cases. getF (f tcb) = getF tcb) \<Longrightarrow>
   \<lbrace>no_cap_to_obj_with_diff_ref cap S\<rbrace>
     thread_set f t
   \<lbrace>\<lambda>rv. no_cap_to_obj_with_diff_ref cap S\<rbrace>"
  apply (simp add: no_cap_to_obj_with_diff_ref_def
                   cte_wp_at_caps_of_state)
  apply (wp hoare_vcg_all_lift thread_set_caps_of_state_trivial
            | simp)+
  done

lemma table_cap_ref_max_free_index_upd[simp]:
  "table_cap_ref (max_free_index_update cap) = table_cap_ref cap"
  by (simp add:free_index_update_def table_cap_ref_def split:cap.splits)

lemma checked_insert_no_cap_to:
  "\<lbrace>no_cap_to_obj_with_diff_ref c' {} and
        no_cap_to_obj_with_diff_ref a {}\<rbrace>
     check_cap_at a b (check_cap_at c d (cap_insert a b e))
   \<lbrace>\<lambda>r. no_cap_to_obj_with_diff_ref c' {}\<rbrace>"
  apply (simp add: check_cap_at_def cap_insert_def
                   cte_wp_at_caps_of_state set_untyped_cap_as_full_def
                   no_cap_to_obj_with_diff_ref_def)
  apply (wp get_cap_wp
               | simp split del: split_if)+
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
  apply (simp add: thread_set_def set_object_def)
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
             thread_set_valid_ioc_trivial
              | simp add: ran_tcb_cap_cases
              | rule conjI | erule disjE)+
  apply (clarsimp simp: valid_tcb_def dest!: get_tcb_SomeD)
  apply (rule conjI, simp add: ran_tcb_cap_cases)
  apply (cut_tac P="op = v" and t="(t, tcb_cnode_index 4)" for v
            in  cte_wp_at_tcbI)
     apply simp
    apply fastforce
   apply (rule refl)
  apply (clarsimp simp: cte_wp_at_caps_of_state
                        valid_ipc_buffer_cap_def)
  done

lemma thread_set_tcb_valid:
  assumes x: "\<And>tcb. tcb_state (fn tcb) = tcb_state  tcb"
  assumes w: "\<And>tcb. tcb_ipc_buffer (fn tcb) = tcb_ipc_buffer tcb
                          \<or> tcb_ipc_buffer (fn tcb) = 0"
  shows      "\<lbrace>tcb_cap_valid c p\<rbrace> thread_set fn t
              \<lbrace>\<lambda>rv. tcb_cap_valid c p\<rbrace>"
  apply (simp add: thread_set_def set_object_def, wp)
  apply (clarsimp simp: tcb_cap_valid_def
                 dest!: get_tcb_SomeD)
  apply (simp add: obj_at_def pred_tcb_at_def is_tcb x get_tcb_def
            split: split_if_asm cong: option.case_cong prod.case_cong)
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
  "\<lbrace>\<lambda>s. is_arch_cap cap
           \<and> (\<forall>ptr. valid_ipc_buffer_cap cap (f ptr))\<rbrace>
     thread_set (tcb_ipc_buffer_update f) t
   \<lbrace>\<lambda>rv. tcb_cap_valid cap (t, tcb_cnode_index 4)\<rbrace>"
  apply (simp add: thread_set_def set_object_def)
  apply wp
  apply (clarsimp simp: tcb_cap_valid_def obj_at_def
                        pred_tcb_at_def is_tcb
                 dest!: get_tcb_SomeD)
  done


lemma tc_invs:
  "\<lbrace>invs and tcb_at a
       and (case_option \<top> (valid_cap o fst) e)
       and (case_option \<top> (valid_cap o fst) f)
       and (case_option \<top> (case_option \<top> (valid_cap o fst) o snd) g)
       and (case_option \<top> (cte_at o snd) e)
       and (case_option \<top> (cte_at o snd) f)
       and (case_option \<top> (case_option \<top> (cte_at o snd) o snd) g)
       and (case_option \<top> (no_cap_to_obj_dr_emp o fst) e)
       and (case_option \<top> (no_cap_to_obj_dr_emp o fst) f)
       and (case_option \<top> (case_option \<top> (no_cap_to_obj_dr_emp o fst) o snd) g)
       and K (case_option True (is_cnode_cap o fst) e)
       and K (case_option True (is_valid_vtable_root o fst) f)
       and K (case_option True (\<lambda>v. case_option True
                          ((swp valid_ipc_buffer_cap (fst v)
                             and is_arch_cap and is_cnode_or_valid_arch)
                                o fst) (snd v)) g)
       and K (case_option True (\<lambda>bl. length bl = word_bits) b)\<rbrace>
      invoke_tcb (tcb_invocation.ThreadControl a sl b pr e f g)
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (rule hoare_gen_asm)+
  apply (simp add: split_def cong: option.case_cong)
  apply (rule hoare_vcg_precond_imp)
   apply wp
      apply ((simp only: simp_thms
        | rule wp_split_const_if wp_split_const_if_R
                   hoare_vcg_all_lift_R
                   hoare_vcg_E_elim hoare_vcg_const_imp_lift_R
                   hoare_vcg_R_conj
        | (wp out_invs_trivial case_option_wpE cap_delete_deletes
             cap_delete_valid_cap cap_insert_valid_cap out_cte_at
             cap_insert_cte_at cap_delete_cte_at out_valid_cap
             hoare_vcg_const_imp_lift_R hoare_vcg_all_lift_R
             thread_set_tcb_ipc_buffer_cap_cleared_invs
             thread_set_invs_trivial[OF ball_tcb_cap_casesI]
             hoare_vcg_all_lift thread_set_valid_cap out_emptyable
             check_cap_inv [where P="valid_cap c" for c]
             check_cap_inv [where P="tcb_cap_valid c p" for c p]
             check_cap_inv[where P="cte_at p0" for p0]
             check_cap_inv[where P="tcb_at p0" for p0]
             thread_set_cte_at
             thread_set_cte_wp_at_trivial[where Q="\<lambda>x. x", OF ball_tcb_cap_casesI]
             thread_set_no_cap_to_trivial[OF ball_tcb_cap_casesI]
             checked_insert_no_cap_to
             out_no_cap_to_trivial[OF ball_tcb_cap_casesI]
             thread_set_ipc_tcb_cap_valid
             static_imp_wp static_imp_conj_wp)[1]
        | simp add: ran_tcb_cap_cases dom_tcb_cap_cases[simplified]
                    emptyable_def
               del: hoare_True_E_R
        | wpc
        | strengthen use_no_cap_to_obj_asid_strg
                     tcb_cap_always_valid_strg[where p="tcb_cnode_index 0"]
                     tcb_cap_always_valid_strg[where p="tcb_cnode_index (Suc 0)"])+)
  apply (clarsimp simp: tcb_at_cte_at_0 tcb_at_cte_at_1[simplified]
                        is_cap_simps is_valid_vtable_root_def
                        is_cnode_or_valid_arch_def tcb_cap_valid_def
                        invs_valid_objs cap_asid_def vs_cap_ref_def
                 split: option.split_asm
       | rule conjI)+
  done

(* FIXME-AEP *)
primrec
  tcb_inv_wf  :: "tcb_invocation \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "tcb_inv_wf (tcb_invocation.Suspend t)
             = (tcb_at t and ex_nonz_cap_to t)"
| "tcb_inv_wf (tcb_invocation.Resume t)
             = (tcb_at t and ex_nonz_cap_to t)"
| "tcb_inv_wf (tcb_invocation.ThreadControl t sl fe pr croot vroot buf)
             = (tcb_at t and case_option \<top> (valid_cap \<circ> fst) croot
                        and K (case_option True (is_cnode_cap \<circ> fst) croot)
                        and case_option \<top> ((cte_at And ex_cte_cap_to) \<circ> snd) croot
                        and case_option \<top> (no_cap_to_obj_dr_emp \<circ> fst) croot
                        and K (case_option True (is_valid_vtable_root \<circ> fst) vroot)
                        and case_option \<top> (valid_cap \<circ> fst) vroot
                        and case_option \<top> (no_cap_to_obj_dr_emp \<circ> fst) vroot
                        and case_option \<top> ((cte_at And ex_cte_cap_to) \<circ> snd) vroot
                        and (case_option \<top> (case_option \<top> (valid_cap o fst) o snd) buf)
                        and (case_option \<top> (case_option \<top>
                              (no_cap_to_obj_dr_emp o fst) o snd) buf)
                        and K (case_option True ((\<lambda>v. is_aligned v msg_align_bits) o fst) buf)
                        and K (case_option True (\<lambda>v. case_option True
                               ((swp valid_ipc_buffer_cap (fst v)
                                    and is_arch_cap and is_cnode_or_valid_arch)
                                              o fst) (snd v)) buf)
                        and (case_option \<top> (case_option \<top> ((cte_at And ex_cte_cap_to) o snd) o snd) buf)
                        and (\<lambda>s. {croot, vroot, option_map undefined buf} \<noteq> {None}
                                    \<longrightarrow> cte_at sl s \<and> ex_cte_cap_to sl s)
                        and K (case_option True (\<lambda>bl. length bl = word_bits) fe)
                        and ex_nonz_cap_to t)"
| "tcb_inv_wf (tcb_invocation.ReadRegisters src susp n arch)
             = (tcb_at src and ex_nonz_cap_to src)"
| "tcb_inv_wf (tcb_invocation.WriteRegisters dest resume values arch)
             = (tcb_at dest and ex_nonz_cap_to dest)"
| "tcb_inv_wf (tcb_invocation.CopyRegisters dest src suspend_source resume_target
                 trans_frame trans_int trans_arch)
             = (tcb_at dest and tcb_at src and ex_nonz_cap_to src and
                ex_nonz_cap_to dest)"
| "tcb_inv_wf (AsyncEndpointControl t aep)
             = (tcb_at t and ex_nonz_cap_to t
                  and (case aep of None \<Rightarrow> \<top> 
                          | Some aepptr \<Rightarrow> (obj_at (\<lambda>ko. \<exists>aep. ko = AsyncEndpoint aep 
                                                \<and> (aep_bound_tcb aep = None) 
                                                \<and> (\<forall>q. aep_obj aep \<noteq> WaitingAEP q)) aepptr
                                          and ex_nonz_cap_to aepptr 
                                          and bound_tcb_at (op = None) t) ))"

crunch ex_nonz_cap_to[wp]: unbind_async_endpoint "ex_nonz_cap_to t"

lemma sba_has_reply[wp]:
  "\<lbrace>\<lambda>s. P (has_reply_cap t s)\<rbrace> set_bound_aep tcb aepptr \<lbrace>\<lambda>rv s. P (has_reply_cap t s)\<rbrace>"
  apply (simp add: has_reply_cap_def cte_wp_at_caps_of_state)
  apply (wp)
  done


lemma set_aep_has_reply[wp]:
  "\<lbrace>\<lambda>s. P (has_reply_cap t s)\<rbrace> set_async_ep aepptr aep \<lbrace>\<lambda>rv s. P (has_reply_cap t s)\<rbrace>"
  by (simp add: has_reply_cap_def cte_wp_at_caps_of_state, wp)
  
lemma unbind_async_endpoint_has_reply[wp]:
  "\<lbrace>\<lambda>s. P (has_reply_cap t s)\<rbrace> unbind_async_endpoint t' \<lbrace>\<lambda>rv s. P (has_reply_cap t s)\<rbrace>"
  apply (simp add: unbind_async_endpoint_def has_reply_cap_def cte_wp_at_caps_of_state)
  apply (rule hoare_seq_ext[OF _ gba_sp])
  apply (case_tac aepptr, simp, wp, simp)
  apply (clarsimp)
  apply (rule hoare_seq_ext[OF _ get_aep_sp])
  apply (wp, clarsimp)
  done


lemma bind_async_endpoint_invs:
  "\<lbrace>bound_tcb_at (op = None) tcbptr 
    and obj_at (\<lambda>ko. \<exists>aep. ko = AsyncEndpoint aep \<and> (aep_bound_tcb aep = None) 
                           \<and> (\<forall>q. aep_obj aep \<noteq> WaitingAEP q)) aepptr
    and invs
    and ex_nonz_cap_to aepptr 
    and ex_nonz_cap_to tcbptr\<rbrace>
     bind_async_endpoint tcbptr aepptr  
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: bind_async_endpoint_def invs_def valid_state_def valid_pspace_def)
  apply (rule hoare_seq_ext[OF _ get_aep_sp])
  apply (wp valid_irq_node_typ set_aep_valid_objs set_async_ep_obj_at 
         | clarsimp simp:idle_no_ex_cap)+
            apply (clarsimp simp: obj_at_def is_aep)
           apply (wp | clarsimp)+ 
         apply (rule conjI, rule impI)
          apply (clarsimp simp: obj_at_def pred_tcb_at_def2)
         apply (rule impI, erule delta_sym_refs)
          apply (fastforce dest!: symreftype_inverse' 
                            simp: aep_q_refs_of_def obj_at_def
                           split: aep.splits split_if_asm)
         apply (fastforce simp: state_refs_of_def pred_tcb_at_def2 obj_at_def 
                               tcb_st_refs_of_def 
                        split: thread_state.splits split_if_asm)
        apply (wp | clarsimp simp: is_aep)+
  apply (erule (1) obj_at_valid_objsE)
  apply (clarsimp simp: valid_obj_def valid_aep_def pred_tcb_at_tcb_at 
                 elim!: obj_atE 
                 split: aep.splits)
  done


lemma tcbinv_invs:
  "\<lbrace>invs and tcb_inv_wf ti\<rbrace>
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
    apply ((wp unbind_async_endpoint_invs get_aep_wp | simp)+)[2]
  apply (wp bind_async_endpoint_invs)
  apply clarsimp
  done


crunch typ_at[wp]: invoke_tcb "\<lambda>s. P (typ_at T p s)"
  (ignore: check_cap_at setNextPC zipWithM
       wp: hoare_drop_imps mapM_x_wp' check_cap_inv
     simp: crunch_simps)

lemma inj_ucast: "\<lbrakk> uc = ucast; is_up uc \<rbrakk> \<Longrightarrow> inj uc"
  apply simp
  apply (rule inj_on_inverseI)
  apply (rule ucast_up_ucast_id)
  apply assumption
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
            | wp_once | wpcw)+
  done

lemma decode_writereg_inv:
  "\<lbrace>P\<rbrace> decode_write_registers args (cap.ThreadCap t) \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (rule hoare_pre)
   apply (simp add: decode_write_registers_def whenE_def
                          split del: split_if
            | wp_once | wpcw)+
  done

lemma decode_copyreg_inv:
  "\<lbrace>P\<rbrace> decode_copy_registers args (cap.ThreadCap t) extras \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (rule hoare_pre)
   apply (simp add: decode_copy_registers_def whenE_def
                          split del: split_if
            | wp_once | wpcw)+
  done

lemma decode_readreg_wf:
  "\<lbrace>invs and tcb_at t and ex_nonz_cap_to t\<rbrace>
   decode_read_registers args (cap.ThreadCap t)
   \<lbrace>tcb_inv_wf\<rbrace>,-"
  apply (simp add: decode_read_registers_def whenE_def
             cong: list.case_cong)
  apply (rule hoare_pre)
   apply (wp | wpc)+
  apply simp
  done

lemma decode_writereg_wf:
  "\<lbrace>invs and tcb_at t and ex_nonz_cap_to t\<rbrace>
     decode_write_registers args (cap.ThreadCap t)
   \<lbrace>tcb_inv_wf\<rbrace>,-"
  apply (simp add: decode_write_registers_def whenE_def
             cong: list.case_cong)
  apply (rule hoare_pre)
   apply (wp | wpc)+
  apply simp
  done

lemma decode_copyreg_wf:
  "\<lbrace>invs and tcb_at t and ex_nonz_cap_to t
       and (\<lambda>s. \<forall>x \<in> set extras. s \<turnstile> x
                       \<and> (\<forall>y \<in> zobj_refs x. ex_nonz_cap_to y s))\<rbrace>
     decode_copy_registers args (cap.ThreadCap t) extras
   \<lbrace>tcb_inv_wf\<rbrace>,-"
  apply (simp add: decode_copy_registers_def whenE_def
             cong: list.case_cong split del: split_if)
  apply (rule hoare_pre)
   apply (wp | wpc)+
  apply (clarsimp simp: valid_cap_def[where c="cap.ThreadCap t" for t])
  done

declare alternativeE_wp[wp]
declare alternativeE_R_wp[wp]

(*FIXME Move up*)
lemma OR_choice_E_weak_wp: "\<lbrace>P\<rbrace> f \<sqinter> g \<lbrace>Q\<rbrace>,- \<Longrightarrow> \<lbrace>P\<rbrace> OR_choice b f g \<lbrace>Q\<rbrace>,-"
  apply (simp add: validE_R_def validE_def OR_choice_weak_wp)
  done

lemma decode_set_priority_wf[wp]:
  "\<lbrace>invs and tcb_at t and ex_nonz_cap_to t\<rbrace>
        decode_set_priority args (cap.ThreadCap t) slot \<lbrace>tcb_inv_wf\<rbrace>,-"
  apply (simp add: decode_set_priority_def split del: split_if)
  apply (rule hoare_pre)
   apply (wp OR_choice_E_weak_wp)
  apply simp
  done


definition
  is_thread_control :: "tcb_invocation \<Rightarrow> bool"
where
 "is_thread_control tinv \<equiv> case tinv of tcb_invocation.ThreadControl a b c d e f g \<Rightarrow> True | _ \<Rightarrow> False"


primrec
  thread_control_target :: "tcb_invocation \<Rightarrow> word32"
where
 "thread_control_target (tcb_invocation.ThreadControl a b c d e f g) = a"

lemma is_thread_control_true[simp]:
  "is_thread_control (tcb_invocation.ThreadControl a b c d e f g)"
  by (simp add: is_thread_control_def)

lemma is_thread_control_def2:
  "is_thread_control tinv =
    (\<exists>target slot faultep prio croot vroot buffer.
        tinv = tcb_invocation.ThreadControl target slot faultep prio croot vroot buffer)"
  by (cases tinv, simp_all add: is_thread_control_def)

lemma decode_set_priority_is_tc[wp]:
  "\<lbrace>\<top>\<rbrace> decode_set_priority args cap slot \<lbrace>\<lambda>rv s. is_thread_control rv\<rbrace>,-"
  apply (rule hoare_pre)
  apply (simp    add: decode_set_priority_def
           split del: split_if
            | wp OR_choice_E_weak_wp)+
  done


lemma decode_set_priority_inv[wp]:
  "\<lbrace>P\<rbrace> decode_set_priority args cap slot \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp add: decode_set_priority_def split del: split_if)
  apply (rule hoare_pre)
  apply (wp OR_choice_weak_wp)
  apply simp
  done

lemma check_valid_ipc_buffer_inv:
  "\<lbrace>P\<rbrace> check_valid_ipc_buffer vptr cap \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp add: check_valid_ipc_buffer_def whenE_def
             cong: cap.case_cong arch_cap.case_cong
             split del: split_if)
  apply (rule hoare_pre)
   apply (wp | simp split del: split_if | wpcw)+
  done

lemma check_valid_ipc_buffer_wp:
  "\<lbrace>\<lambda>s. is_arch_cap cap \<and> is_cnode_or_valid_arch cap
          \<and> valid_ipc_buffer_cap cap vptr
          \<and> is_aligned vptr msg_align_bits
             \<longrightarrow> P s\<rbrace>
     check_valid_ipc_buffer vptr cap
   \<lbrace>\<lambda>rv. P\<rbrace>,-"
  apply (simp add: check_valid_ipc_buffer_def whenE_def
             cong: cap.case_cong arch_cap.case_cong
             split del: split_if)
  apply (rule hoare_pre)
   apply (wp | simp split del: split_if | wpc)+
  apply (clarsimp simp: is_cap_simps is_cnode_or_valid_arch_def
                        valid_ipc_buffer_cap_def)
  done

lemma derive_is_arch[wp]:
  "\<lbrace>\<lambda>s. is_arch_cap c\<rbrace> derive_cap slot c \<lbrace>\<lambda>rv s. is_arch_cap rv\<rbrace>,-"
  apply (simp add: derive_cap_def cong: cap.case_cong)
  apply (rule hoare_pre)
   apply (wp | wpc | simp only: o_def is_arch_cap_def cap.simps)+
  apply fastforce
  done


lemma derive_no_cap_asid[wp]:
  "\<lbrace>no_cap_to_obj_with_diff_ref cap S\<rbrace>
     derive_cap slot cap
   \<lbrace>\<lambda>rv. no_cap_to_obj_with_diff_ref rv S\<rbrace>,-"
  apply (simp add: derive_cap_def arch_derive_cap_def
             cong: cap.case_cong)
  apply (rule hoare_pre)
   apply (wp | simp | wpc)+
  apply (auto simp add: no_cap_to_obj_with_diff_ref_Null,
         auto simp add: no_cap_to_obj_with_diff_ref_def
                        table_cap_ref_def)
  done


lemma decode_set_ipc_wf[wp]:
  "\<lbrace>invs and tcb_at t and cte_at slot and ex_cte_cap_to slot
      and ex_nonz_cap_to t
      and (\<lambda>s. \<forall>x \<in> set excaps. s \<turnstile> fst x \<and> cte_at (snd x) s
                          \<and> ex_cte_cap_to (snd x) s
                          \<and> no_cap_to_obj_dr_emp (fst x) s)\<rbrace>
     decode_set_ipc_buffer args (cap.ThreadCap t) slot excaps
   \<lbrace>tcb_inv_wf\<rbrace>,-"
  apply (simp   add: decode_set_ipc_buffer_def whenE_def split_def
          split del: split_if)
  apply (rule hoare_pre, wp check_valid_ipc_buffer_wp)
     apply simp
     apply (wp derive_cap_valid_cap hoare_drop_imps)[1]
    apply wp
  apply (clarsimp simp: neq_Nil_conv)
  done


lemma decode_set_ipc_is_tc[wp]:
  "\<lbrace>\<top>\<rbrace> decode_set_ipc_buffer args cap slot excaps \<lbrace>\<lambda>rv s. is_thread_control rv\<rbrace>,-"
  apply (rule hoare_pre)
  apply (simp    add: decode_set_ipc_buffer_def split_def
           split del: split_if
            | wp)+
  apply fastforce
  done


lemma decode_set_ipc_inv[wp]:
  "\<lbrace>P\<rbrace> decode_set_ipc_buffer args cap slot excaps \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp   add: decode_set_ipc_buffer_def whenE_def
                     split_def
          split del: split_if)
  apply (rule hoare_pre, wp check_valid_ipc_buffer_inv)
  apply simp
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


lemma no_cap_to_obj_with_diff_ref_update_cap_data:
  "no_cap_to_obj_with_diff_ref c S s \<longrightarrow>
    no_cap_to_obj_with_diff_ref (update_cap_data P x c) S s"
  apply (case_tac "update_cap_data P x c = cap.NullCap")
   apply (simp add: no_cap_to_obj_with_diff_ref_Null)
  apply (subgoal_tac "vs_cap_ref (update_cap_data P x c)
                                 = vs_cap_ref c")
   apply (simp add: no_cap_to_obj_with_diff_ref_def
                    update_cap_objrefs)
  apply (clarsimp simp: update_cap_data_closedform
                        table_cap_ref_def
                        arch_update_cap_data_def
                 split: cap.split)
  apply simp
  done


lemma decode_set_space_wf[wp]:
  "\<lbrace>invs and tcb_at t and cte_at slot and ex_cte_cap_to slot
          and ex_nonz_cap_to t
          and (\<lambda>s. \<forall>x \<in> set extras. s \<turnstile> fst x \<and> cte_at (snd x) s
                          \<and> ex_cte_cap_to (snd x) s
                          \<and> t \<noteq> fst (snd x)
                          \<and> no_cap_to_obj_dr_emp (fst x) s)\<rbrace>
     decode_set_space args (cap.ThreadCap t) slot extras
   \<lbrace>tcb_inv_wf\<rbrace>,-"
  apply (simp   add: decode_set_space_def whenE_def unlessE_def
          split del: split_if)
  apply (rule hoare_pre)
   apply (wp derive_cap_valid_cap
             | simp   add: is_valid_vtable_root_def o_def
                split del: split_if
             | rule hoare_drop_imps)+
  apply (clarsimp split del: split_if simp: ball_conj_distrib
                   simp del: length_greater_0_conv)
  apply (simp add: update_cap_data_validI word_bits_def
                   no_cap_to_obj_with_diff_ref_update_cap_data
              del: length_greater_0_conv)
  done


lemma decode_set_space_inv[wp]:
  "\<lbrace>P\<rbrace> decode_set_space args cap slot extras \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp   add: decode_set_space_def whenE_def unlessE_def
          split del: split_if)
  apply (rule hoare_pre)
   apply (wp hoare_drop_imps | simp)+
  done


lemma decode_set_space_is_tc[wp]:
  "\<lbrace>\<top>\<rbrace> decode_set_space args cap slot extras \<lbrace>\<lambda>rv s. is_thread_control rv\<rbrace>,-"
  apply (rule hoare_pre)
   apply (simp   add: decode_set_space_def whenE_def unlessE_def
           split del: split_if)
   apply (wp | simp only: is_thread_control_true)+
  done


lemma decode_set_space_target[wp]:
  "\<lbrace>\<lambda>s. P (obj_ref_of cap)\<rbrace> decode_set_space args cap slot extras \<lbrace>\<lambda>rv s. P (thread_control_target rv)\<rbrace>,-"
  apply (rule hoare_pre)
   apply (simp   add: decode_set_space_def whenE_def unlessE_def
           split del: split_if)
   apply (wp | simp only: thread_control_target.simps)+
  done

(* FIXME: move *)
lemma boring_simp[simp]:
  "(if x then True else False) = x" by simp


lemma decode_tcb_conf_wf[wp]:
  "\<lbrace>invs and tcb_at t and cte_at slot and ex_cte_cap_to slot
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
                               \<and> is_thread_control set_space \<and> is_thread_control set_params
                               \<and> thread_control_target set_space = t
                               \<and> cte_at slot s \<and> ex_cte_cap_to slot s"
                  in hoare_post_imp_R)
        apply wp
       apply (clarsimp simp: is_thread_control_def2 cong: option.case_cong)
      apply (wp | simp add: whenE_def split del: split_if)+
  apply (clarsimp simp: linorder_not_less val_le_length_Cons
                   del: ballI)
  done


lemma decode_tcb_conf_inv[wp]:
  "\<lbrace>P\<rbrace> decode_tcb_configure args cap slot extras \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (clarsimp simp add: decode_tcb_configure_def Let_def whenE_def
                 split del: split_if)
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
  done


lemma update_cap_valid:
  "valid_cap cap s \<Longrightarrow>
   valid_cap (case capdata of
              None \<Rightarrow> cap_rights_update rs cap
            | Some x \<Rightarrow> update_cap_data p x
                     (cap_rights_update rs cap)) s"
  apply (case_tac capdata, simp_all add: valid_cap_update_rights)
  apply (case_tac cap,
         simp_all add: update_cap_data_def cap_rights_update_def
                       is_cap_defs Let_def split_def valid_cap_def
                       badge_update_def the_cnode_cap_def cap_aligned_def
                       arch_update_cap_data_def
            split del: split_if)
     apply (simp add: badge_update_def cap_rights_update_def)
    apply (simp add: badge_update_def)
   apply simp
  apply (rename_tac arch_cap)
  using valid_validate_vm_rights[simplified valid_vm_rights_def]
  apply (case_tac arch_cap, simp_all add: acap_rights_update_def
                                     split: option.splits prod.splits)
  done

crunch inv[wp]:  decode_unbind_aep P
(simp: whenE_def)

lemma decode_bind_aep_inv[wp]:
  "\<lbrace>P\<rbrace> decode_bind_aep cap excaps \<lbrace>\<lambda>_. P\<rbrace>"
  unfolding decode_bind_aep_def
  by (rule hoare_pre) (wp get_aep_wp gba_wp | wpc | clarsimp simp: whenE_def split del: split_if)+

lemma decode_tcb_inv_inv:
  "\<lbrace>P\<rbrace> decode_tcb_invocation label args (cap.ThreadCap t) slot extras \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp add: decode_tcb_invocation_def Let_def
             cong: if_cong
        split del: split_if)
  apply (rule hoare_pre)
   apply (wpc
        | wp decode_readreg_inv decode_writereg_inv
             decode_copyreg_inv decode_tcb_conf_inv)+
  apply simp
  done

lemma real_cte_at_not_tcb_at:
  "real_cte_at (x, y) s \<Longrightarrow> \<not> tcb_at x s"
  by (clarsimp simp: obj_at_def is_tcb is_cap_table)

lemma decode_bind_aep_wf:
  "\<lbrace>invs and tcb_at t and ex_nonz_cap_to t
       and (\<lambda>s. \<forall>x \<in> set extras. s \<turnstile> (fst x) \<and> (\<forall>y \<in> zobj_refs (fst x). ex_nonz_cap_to y s))\<rbrace>
     decode_bind_aep (cap.ThreadCap t) extras
   \<lbrace>tcb_inv_wf\<rbrace>,-"
  apply (simp add: decode_bind_aep_def whenE_def
             cong: list.case_cong split del: split_if)
  apply (rule hoare_pre)
   apply (wp get_aep_wp gba_wp | wpc)+
  apply (fastforce simp: valid_cap_def[where c="cap.ThreadCap t" for t] is_aep invs_def
                    valid_state_def valid_pspace_def
             elim!: obj_at_weakenE
             dest!: idle_no_ex_cap hd_in_set)
  done

lemma decode_unbind_aep_wf:
  "\<lbrace>invs and tcb_at t and ex_nonz_cap_to t\<rbrace>
     decode_unbind_aep (cap.ThreadCap t)
   \<lbrace>tcb_inv_wf\<rbrace>,-"
  apply (simp add: decode_unbind_aep_def)
  apply (rule hoare_pre)
   apply (wp gba_wp | wpc)+
  apply clarsimp
  done

lemma decode_tcb_inv_wf:
  "\<lbrace>invs and tcb_at t and ex_nonz_cap_to t
         and cte_at slot and ex_cte_cap_to slot
         and (\<lambda>s. \<forall>x \<in> set extras. real_cte_at (snd x) s \<and> s \<turnstile> fst x
                                 \<and> ex_cte_cap_to (snd x) s
                                 \<and> (\<forall>y \<in> zobj_refs (fst x). ex_nonz_cap_to y s)
                                 \<and> no_cap_to_obj_dr_emp (fst x) s)\<rbrace>
      decode_tcb_invocation label args (cap.ThreadCap t) slot extras
   \<lbrace>tcb_inv_wf\<rbrace>,-"
  apply (simp add: decode_tcb_invocation_def Let_def
              cong: if_cong split del: split_if)
  apply (rule hoare_vcg_precond_impE_R)
   apply wpc
   apply (wp decode_tcb_conf_wf decode_readreg_wf
             decode_writereg_wf decode_copyreg_wf
             decode_bind_aep_wf decode_unbind_aep_wf)
  apply (clarsimp simp: real_cte_at_cte)
  apply (fastforce simp: real_cte_at_not_tcb_at)
  done

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

crunch pred_tcb_at: switch_to_thread "pred_tcb_at proj P t"
  (wp: crunch_wps simp: crunch_simps)

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
  by (simp add: decode_domain_invocation_def whenE_def split del: split_if | wp hoare_vcg_split_ifE | wpc)+

lemma decode_domain_inv_wf:
  "\<lbrace>valid_objs and valid_global_refs and
     (\<lambda>s. \<forall>x\<in>set excs. s \<turnstile> fst x) and
     (\<lambda>s. \<forall>x\<in>set excs. \<forall>r\<in>zobj_refs (fst x). ex_nonz_cap_to r s)\<rbrace>
     decode_domain_invocation label args excs
   \<lbrace>\<lambda>(t, d) s. tcb_at t s \<and> t \<noteq> idle_thread s\<rbrace>, -"
  apply (clarsimp simp: decode_domain_invocation_def whenE_def split del: split_if
        | wp hoare_vcg_split_ifE | wpc)+
  apply (erule ballE[where x="hd excs"])
   apply (clarsimp simp: valid_cap_simps)
   apply (drule(1) idle_no_ex_cap)
   apply (erule ballE[where x="hd excs"])
    apply simp+
    done
lemma tcb_bound_refs_no_AEPBound:
  "(x, AEPBound) \<notin> tcb_bound_refs a"
  by (simp add: tcb_bound_refs_def split: option.splits)

lemma tcb_st_refs_of_no_AEPBound:
  "(x, AEPBound) \<notin> tcb_st_refs_of z"
  by (simp add: tcb_st_refs_of_def split: thread_state.splits)

lemma tcb_not_in_state_refs_of_tcb:
  "tcb_at a s \<Longrightarrow> (a, AEPBound) \<notin> state_refs_of s a"
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

lemma aep_bound_refs_def2:
  "aep_bound_refs t = set_option t \<times> {AEPBound}"
  by (clarsimp simp: aep_bound_refs_def split: option.splits)

lemma unbind_async_endpoint_sym_refs[wp]:
  "\<lbrace>\<lambda>s. sym_refs (state_refs_of s) \<and> valid_objs s \<and> tcb_at a s\<rbrace> 
     unbind_async_endpoint a 
   \<lbrace>\<lambda>rv s. sym_refs (state_refs_of s)\<rbrace>"
  apply (simp add: unbind_async_endpoint_def)
  apply (rule hoare_seq_ext [OF _ gba_sp])
  apply (case_tac aepptr, simp_all)
   apply (wp, simp)
  apply (rule hoare_seq_ext [OF _ get_aep_sp])
  apply (wp | wpc | simp)+
  apply (rule conjI)
   apply (fastforce simp: obj_at_def pred_tcb_at_def)
  apply (rule impI, clarsimp)
  apply (rule delta_sym_refs, assumption)
   apply (fastforce simp: obj_at_def pred_tcb_at_def aep_q_refs_of_def
                          state_refs_of_def
                    split: split_if_asm)
  apply (auto simp: valid_obj_def obj_at_def aep_bound_refs_def2 symreftype_inverse'
                    aep_q_refs_of_def tcb_aep_is_bound_def state_refs_of_def
                    tcb_st_refs_of_def tcb_bound_refs_def2 
              split: aep.splits thread_state.splits split_if_asm
              dest!: sym_refs_bound_tcb_atD refs_in_aep_bound_refs
              elim!: obj_at_valid_objsE
              intro!: aep_q_refs_no_AEPBound)
  done

end
