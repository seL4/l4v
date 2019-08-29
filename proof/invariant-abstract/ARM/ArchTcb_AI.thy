(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory ArchTcb_AI
imports "../Tcb_AI"
begin

context Arch begin global_naming ARM

named_theorems Tcb_AI_asms


lemma activate_idle_invs[Tcb_AI_asms]:
  "\<lbrace>invs and ct_idle\<rbrace>
     arch_activate_idle_thread thread
   \<lbrace>\<lambda>rv. invs and ct_idle\<rbrace>"
  by (simp add: arch_activate_idle_thread_def)


lemma empty_fail_getRegister [intro!, simp, Tcb_AI_asms]:
  "empty_fail (getRegister r)"
  by (simp add: getRegister_def)


lemma same_object_also_valid:  (* arch specific *)
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

lemma same_object_obj_refs[Tcb_AI_asms]:
  "\<lbrakk> same_object_as cap cap' \<rbrakk>
     \<Longrightarrow> obj_refs cap = obj_refs cap'"
  apply (cases cap, simp_all add: same_object_as_def)
       apply ((clarsimp simp: is_cap_simps bits_of_def
                      split: cap.split_asm )+)
  by (cases "the_arch_cap cap"; cases "the_arch_cap cap'"; simp)


definition
  is_cnode_or_valid_arch :: "cap \<Rightarrow> bool"
where
 "is_cnode_or_valid_arch cap \<equiv>
    is_cnode_cap cap
     \<or> (is_arch_cap cap
          \<and> (is_pt_cap cap \<longrightarrow> cap_asid cap \<noteq> None)
          \<and> (is_pd_cap cap \<longrightarrow> cap_asid cap \<noteq> None))"


definition (* arch specific *)
  "pt_pd_asid cap \<equiv> case cap of
    ArchObjectCap (PageTableCap _ (Some (asid, _))) \<Rightarrow> Some asid
  | ArchObjectCap (PageDirectoryCap _ (Some asid)) \<Rightarrow> Some asid
  | _ \<Rightarrow> None"

lemmas pt_pd_asid_simps [simp] = (* arch specific *)
  pt_pd_asid_def [split_simps cap.split arch_cap.split option.split prod.split]

lemma checked_insert_is_derived: (* arch specific *)
  "\<lbrakk> same_object_as new_cap old_cap; is_cnode_or_valid_arch new_cap;
     obj_refs new_cap = obj_refs old_cap
         \<longrightarrow> table_cap_ref old_cap = table_cap_ref new_cap
            \<and> pt_pd_asid old_cap = pt_pd_asid new_cap\<rbrakk>
     \<Longrightarrow> is_derived m slot new_cap old_cap"
  apply (cases slot)
  apply (frule same_object_as_cap_master)
  apply (frule master_cap_obj_refs)
  apply (frule cap_master_eq_badge_none)
  apply (frule same_master_cap_same_types)
  apply (simp add: is_derived_def)
  apply clarsimp
  apply (auto simp: is_cap_simps cap_master_cap_def
                    is_cnode_or_valid_arch_def vs_cap_ref_def
                    table_cap_ref_def pt_pd_asid_def up_ucast_inj_eq
             split: cap.split_asm arch_cap.split_asm
                    option.split_asm)[1]
  done

lemma is_cnode_or_valid_arch_cap_asid: (* arch specific *)
  "is_cnode_or_valid_arch cap
       \<Longrightarrow> (is_pt_cap cap \<longrightarrow> cap_asid cap \<noteq> None)
             \<and> (is_pd_cap cap \<longrightarrow> cap_asid cap \<noteq> None)"
  by (auto simp add: is_cnode_or_valid_arch_def
                     is_cap_simps)

lemma same_object_as_Nulls[simp]:
  "\<not>same_object_as cap NullCap"
  "\<not>same_object_as NullCap cap"
  by (auto simp: same_object_as_def split: cap.splits)

lemma checked_insert_tcb_invs: (* arch specific *)
  "\<lbrace>invs and cte_wp_at (\<lambda>c. c = cap.NullCap) (target, ref)
        and K (is_cnode_or_valid_arch new_cap \<or> is_ep_cap new_cap \<or> new_cap = NullCap)
        and valid_cap new_cap
        and tcb_cap_valid new_cap (target, ref)
        and (\<lambda>s. is_ep_cap new_cap \<or> new_cap = NullCap
                         \<longrightarrow> cte_wp_at (\<lambda>c. c = new_cap \<or> c = NullCap) src_slot s)
        and (cte_wp_at (\<lambda>c. obj_refs c = obj_refs new_cap
                              \<longrightarrow> table_cap_ref c = table_cap_ref new_cap \<and>
                                 pt_pd_asid c = pt_pd_asid new_cap) src_slot)\<rbrace>
   check_cap_at new_cap src_slot
    (check_cap_at (cap.ThreadCap target) slot
     (cap_insert new_cap src_slot (target, ref)))
   \<lbrace>\<lambda>rv. invs\<rbrace>"
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
   apply (erule disjE)
    apply (erule(1) checked_insert_is_derived, simp+)
   apply (auto simp: is_cnode_or_valid_arch_def is_derived_def is_cap_simps)
  done

lemma checked_insert_tcb_invs': (* arch specific *)
  "\<lbrace>invs and cte_wp_at (\<lambda>c. c = cap.NullCap) (target, ref)
        and K (is_cnode_or_valid_arch new_cap) and valid_cap new_cap
        and tcb_cap_valid new_cap (target, ref)
        and (cte_wp_at (\<lambda>c. obj_refs c = obj_refs new_cap
                              \<longrightarrow> table_cap_ref c = table_cap_ref new_cap \<and>
                                 pt_pd_asid c = pt_pd_asid new_cap) src_slot)\<rbrace>
   check_cap_at new_cap src_slot
    (check_cap_at (cap.ThreadCap target) slot
     (cap_insert new_cap src_slot (target, ref)))
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wpsimp wp: checked_insert_tcb_invs)
  by (auto simp: is_cap_simps is_cnode_or_valid_arch_def)

crunches arch_get_sanitise_register_info, arch_post_modify_registers
  for tcb_at[wp, Tcb_AI_asms]: "tcb_at a"
  and invs[wp, Tcb_AI_asms]: invs
  and ex_nonz_cap_to[wp, Tcb_AI_asms]: "ex_nonz_cap_to a"
  and fault_tcb_at[wp, Tcb_AI_asms]: "fault_tcb_at P a"

lemma finalise_cap_not_cte_wp_at[Tcb_AI_asms]:
  assumes x: "P cap.NullCap"
  shows      "\<lbrace>\<lambda>s. \<forall>cp \<in> ran (caps_of_state s). P cp\<rbrace>
                finalise_cap cap fin
              \<lbrace>\<lambda>rv s. \<forall>cp \<in> ran (caps_of_state s). P cp\<rbrace>"
  apply (cases cap; (solves \<open>wpsimp\<close>)?)
    apply (wpsimp wp: hoare_drop_imps)
   apply (wpsimp wp: suspend_caps_of_state hoare_drop_imps hoare_vcg_all_lift)
   apply (fastforce simp: ran_def x split: if_splits)
  apply (wpsimp wp: delete_one_caps_of_state
              simp: deleting_irq_handler_def get_irq_slot_def ball_ran_eq x)
  done

lemma table_cap_ref_max_free_index_upd[simp,Tcb_AI_asms]:
  "table_cap_ref (max_free_index_update cap) = table_cap_ref cap"
  by (simp add: free_index_update_def table_cap_ref_def split: cap.splits)


interpretation Tcb_AI_1? : Tcb_AI_1
  where is_cnode_or_valid_arch = is_cnode_or_valid_arch
  by (unfold_locales; fact Tcb_AI_asms)


lemma use_no_cap_to_obj_asid_strg: (* arch specific *)
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

lemma cap_delete_no_cap_to_obj_asid[wp, Tcb_AI_asms]:
  "\<lbrace>no_cap_to_obj_dr_emp cap\<rbrace>
     cap_delete slot
   \<lbrace>\<lambda>rv. no_cap_to_obj_dr_emp cap\<rbrace>"
  apply (simp add: cap_delete_def
                   no_cap_to_obj_with_diff_ref_ran_caps_form)
  apply wp
  apply simp
  apply (rule use_spec)
  apply (rule rec_del_all_caps_in_range)
     apply (simp add: table_cap_ref_def[simplified, split_simps cap.split]
              | rule obj_ref_none_no_asid)+
  done

lemma as_user_ipc_tcb_cap_valid4[wp]:
  "\<lbrace>\<lambda>s. tcb_cap_valid cap (t, tcb_cnode_index 2) s\<rbrace>
    as_user a b
   \<lbrace>\<lambda>rv. tcb_cap_valid cap (t, tcb_cnode_index 2)\<rbrace>"
  apply (simp add: as_user_def set_object_def)
  apply (wp | wpc | simp)+
  apply (clarsimp simp: tcb_cap_valid_def obj_at_def
                        pred_tcb_at_def is_tcb
                 dest!: get_tcb_SomeD)
  apply (clarsimp simp: get_tcb_def)
  done

lemma thread_set_mcp_ex_nonz_cap_to[wp]:
  "\<lbrace>ex_nonz_cap_to a\<rbrace> thread_set (tcb_mcpriority_update g) t \<lbrace>\<lambda>rv. ex_nonz_cap_to a\<rbrace>"
  by (wpsimp wp: ex_nonz_cap_to_pres thread_set_cte_wp_at_trivial simp: tcb_cap_cases_def) auto

lemma is_cnode_or_valid_arch_simps[simp]:
  "is_cnode_or_valid_arch (CNodeCap r bits ga)"
  "is_cnode_or_valid_arch (ArchObjectCap (PageDirectoryCap r (Some ab)))"
  by (simp add: is_cnode_or_valid_arch_def is_cap_simps)+

lemma is_nondevice_page_cap_simps[simp]:
  "is_nondevice_page_cap (ArchObjectCap (PageCap False x32 x33 x34 x35))"
  by (simp add: is_cap_simps')

lemma valid_ipc_buffer_cap:
  "valid_ipc_buffer_cap c b =
  (c = NullCap \<or> (\<exists>p R sz a. c = ArchObjectCap (PageCap False p R sz a) \<and> is_aligned b msg_align_bits))"
  by (auto simp: valid_ipc_buffer_cap_def split: cap.splits arch_cap.splits bool.splits)

lemma install_tcb_cap_invs:
  "\<lbrace>invs and tcb_at target and
    (\<lambda>s. \<forall>new_cap src_slot.
       slot_opt = Some (new_cap, src_slot)
         \<longrightarrow> K (is_cnode_or_valid_arch new_cap \<or> is_ep_cap new_cap \<or> NullCap = new_cap) s
          \<and> valid_cap new_cap s
          \<and> tcb_cap_valid new_cap (target, tcb_cnode_index n) s
          \<and> (is_ep_cap new_cap \<or> new_cap = NullCap
                           \<longrightarrow> cte_wp_at (\<lambda>c. is_ep_cap c \<or> c = NullCap) (target, tcb_cnode_index n) s
                             \<and> cte_wp_at (\<lambda>c. c = new_cap \<or> c = NullCap) src_slot s)
          \<and> (case tcb_cap_cases (tcb_cnode_index n) of None \<Rightarrow> True | Some (getF, setF, restr) \<Rightarrow> \<forall>st. restr target st new_cap)
          \<and> (tcb_cnode_index n = tcb_cnode_index 2 \<longrightarrow> (\<forall>ptr. valid_ipc_buffer_cap new_cap ptr))
          \<and> real_cte_at src_slot s \<and> no_cap_to_obj_dr_emp new_cap s)\<rbrace>
   install_tcb_cap target slot n slot_opt
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: install_tcb_cap_def)
  apply (wpsimp wp: checked_insert_tcb_invs cap_delete_deletes
                    hoare_vcg_imp_lift_R
         | strengthen tcb_cap_always_valid_strg use_no_cap_to_obj_asid_strg
         | wpsimp wp: cap_delete_ep)+
  by (auto simp: typ_at_eq_kheap_obj cap_table_at_typ tcb_at_typ
                 is_cnode_or_valid_arch_def is_cap_simps real_cte_at_cte
          elim!: cte_wp_at_weakenE)

lemma install_tcb_cap_no_cap_to_obj_dr_emp[wp, Tcb_AI_asms]:
  "\<lbrace>no_cap_to_obj_dr_emp cap and
    (\<lambda>s. \<forall>new_cap src_slot. slot_opt = Some (new_cap, src_slot)
                          \<longrightarrow> no_cap_to_obj_dr_emp new_cap s)\<rbrace>
   install_tcb_cap target slot n slot_opt
   \<lbrace>\<lambda>_. no_cap_to_obj_dr_emp cap\<rbrace>"
  apply (simp add: install_tcb_cap_def)
  by (wpsimp wp: checked_insert_no_cap_to)

lemma is_cnode_or_valid_arch_is_cap_simps:
  "is_cnode_cap cap \<Longrightarrow> is_cnode_or_valid_arch cap"
  "is_valid_vtable_root cap \<Longrightarrow> is_cnode_or_valid_arch cap"
  by (auto simp: is_cnode_or_valid_arch_def is_valid_vtable_root_def is_cap_simps)+

lemma valid_vtable_root_is_arch_cap:
  "is_valid_vtable_root cap \<Longrightarrow> is_arch_cap cap"
  by (auto simp: ARM_A.is_valid_vtable_root_def is_cap_simps)

lemma tcc_invs[Tcb_AI_asms]:
  "\<lbrace>invs and tcb_inv_wf (ThreadControlCaps t sl fh th croot vroot buf)\<rbrace>
      invoke_tcb (ThreadControlCaps t sl fh th croot vroot buf)
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  supply if_cong[cong]
  apply (simp add: split_def install_tcb_frame_cap_def cong: option.case_cong)
  apply (simp only: simp_thms
         | (simp add: conj_comms del: hoare_True_E_R,
            strengthen imp_consequent[where Q="x = None" for x], simp cong: conj_cong)
         | rule hoare_vcg_E_elim hoare_vcg_imp_lift'
         | wp cap_delete_deletes
              hoare_vcg_const_imp_lift_R hoare_vcg_all_lift_R hoare_vcg_all_lift
              thread_set_tcb_ipc_buffer_cap_cleared_invs
              thread_set_invs_trivial[OF ball_tcb_cap_casesI]
              thread_set_cte_wp_at_trivial[where Q="\<lambda>x. x", OF ball_tcb_cap_casesI]
              thread_set_no_cap_to_trivial[OF ball_tcb_cap_casesI]
              thread_set_no_change_tcb_sched_context
              install_tcb_cap_invs
              checked_insert_tcb_invs[where ref="tcb_cnode_index 2"]
              thread_set_ipc_tcb_cap_valid gbn_wp
              static_imp_wp static_imp_conj_wp
         | simp add: not_pred_tcb
         | wpc
         | strengthen use_no_cap_to_obj_asid_strg
                      tcb_cap_always_valid_strg tcb_cap_valid_ep_strgs
         | wp cap_delete_ep install_tcb_cap_cte_wp_at_ep)+
  apply (clarsimp cong: conj_cong)
  apply (intro conjI impI;
         clarsimp simp: is_cnode_or_valid_arch_is_cap_simps tcb_ep_slot_cte_wp_ats real_cte_at_cte
                 dest!: valid_vtable_root_is_arch_cap)
      apply (all \<open>clarsimp simp: is_cap_simps cte_wp_at_caps_of_state\<close>)
     apply (all \<open>clarsimp simp: obj_at_def is_tcb typ_at_eq_kheap_obj cap_table_at_typ\<close>)
  by (auto simp: valid_ipc_buffer_cap)

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

(* fixme: move *)
lemma hoare_pre_add:
  "(\<forall>s. P s \<longrightarrow> R s) \<Longrightarrow> (\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<longleftrightarrow> \<lbrace>P and R\<rbrace> f \<lbrace>Q\<rbrace>)"
  apply (subst iff_conv_conj_imp)
  by(intro conjI impI; rule hoare_weaken_pre, assumption, clarsimp)

(* fixme: move *)
lemma hoare_pre_addE:
  "(\<forall>s. P s \<longrightarrow> R s) \<Longrightarrow> (\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>S\<rbrace> \<longleftrightarrow> \<lbrace>P and R\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>S\<rbrace>)"
  apply (subst iff_conv_conj_imp)
  by(intro conjI impI; rule hoare_weaken_preE, assumption, clarsimp)

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
  apply (subst hoare_pre_addE[where R="K (is_ep_cap cap \<or> cap = NullCap)"])
   apply clarsimp
   apply (subgoal_tac "cte_wp_at (\<lambda>c. is_ep_cap c \<or> c = NullCap) (target, tcb_cnode_index 3) s")
    apply (simp add: cte_wp_at_caps_of_state)
   apply (rule tcb_ep_slot_cte_wp_ats; clarsimp simp: pred_tcb_at_def obj_at_def is_tcb)
  apply (case_tac cap; simp)
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
  by (wpsimp wp: check_cap_inv cap_delete_fh_lift)

crunches empty_slot
  for sc_tcb_sc_at[wp]: "sc_tcb_sc_at P target"
  (wp: crunch_wps)

lemma set_simple_ko_sc_at_pred_n[wp]:
  "set_simple_ko g ep v \<lbrace> \<lambda>s. P (sc_at_pred_n N proj f t s) \<rbrace>"
  unfolding set_simple_ko_def
  apply (wpsimp wp: set_object_wp get_object_wp)
  apply (intro conjI;
         intro impI;
         erule rsubst[where P=P];
         clarsimp split: option.splits simp: sc_at_pred_n_def obj_at_def)
  done

crunches cancel_all_ipc
  for sc_tcb_sc_at[wp]: "sc_tcb_sc_at P target"
  and ex_nonz_cap_to[wp]: "ex_nonz_cap_to t"
  (wp: crunch_wps simp: crunch_simps)

lemma install_tcb_cap_sc_tcb_sc_at[wp]:
  "\<lbrace>sc_tcb_sc_at P d and invs and tcb_at target\<rbrace>
   install_tcb_cap target slot 3 slot_opt
   \<lbrace>\<lambda>_. sc_tcb_sc_at P d\<rbrace>"
  unfolding install_tcb_cap_def
  by (wpsimp wp: check_cap_inv cap_delete_fh_lift)

lemma valid_cap_not_ep_at_not_ep_cap:
  "\<lbrakk> r \<in> obj_refs cap; \<not> ep_at r s; s \<turnstile> cap \<rbrakk> \<Longrightarrow>
  \<not> is_ep_cap cap"
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
     apply (rule_tac x=ac in exI)
     apply (rule_tac x=bb in exI)
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
      apply (clarsimp simp: valid_tcb_def tcb_cap_cases_def cte_wp_at_caps_of_state tcb_at_def is_tcb)
      apply (subst (asm) caps_of_state_tcb_index_trans)
       apply (erule get_tcb_rev)
      apply (clarsimp simp: tcb_cnode_map_def)
     apply (clarsimp simp: valid_objs_def valid_obj_def dom_def)
     apply fastforce
    apply (clarsimp simp: ex_nonz_cap_to_def)
    apply (rule_tac x=ac in exI)
    apply (rule_tac x=bb in exI)
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
      apply (clarsimp simp: valid_tcb_def tcb_cap_cases_def cte_wp_at_caps_of_state tcb_at_def is_tcb)
      apply (subst (asm) caps_of_state_tcb_index_trans)
       apply (erule get_tcb_rev)
      apply (clarsimp simp: tcb_cnode_map_def)
     apply (clarsimp simp: valid_objs_def valid_obj_def dom_def)
     apply fastforce
    apply clarsimp
   apply (clarsimp simp: invs_def valid_state_def valid_pspace_def pred_neg_def)
  apply clarsimp
  done

lemma hoare_post_addE:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>_ s. R s \<and> Q s\<rbrace>, \<lbrace>T\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_ s. Q s\<rbrace>, \<lbrace>T\<rbrace>"
  by (erule hoare_post_impErr'; simp)

lemma cte_wp_at_strengthen:
  "cte_wp_at P p s \<Longrightarrow> \<forall>c. P c \<longrightarrow> Q c \<Longrightarrow> cte_wp_at Q p s"
  by (auto simp add: cte_wp_at_cases)

lemma sym_refs_bound_sc_tcb_at_eq:
  "sym_refs (state_refs_of s)
   \<Longrightarrow> bound_sc_tcb_at (\<lambda>a. a = Some t) x s
   \<Longrightarrow> bound_sc_tcb_at (\<lambda>a. a = Some t) y s
   \<Longrightarrow> x = y"
  apply (subst (asm) sym_refs_bound_sc_tcb_iff_sc_tcb_sc_at[OF refl refl], assumption)
  apply (subst (asm) sym_refs_bound_sc_tcb_iff_sc_tcb_sc_at[OF refl refl], assumption)
  apply (clarsimp simp: sc_at_pred_n_def obj_at_def)
  done

lemma bound_sc_tcb_at_idle_sc_idle_thread:
  "sym_refs (state_refs_of s)
   \<Longrightarrow> valid_idle s
   \<Longrightarrow> bound_sc_tcb_at (\<lambda>a. a = Some idle_sc_ptr) t s
   \<Longrightarrow> t = idle_thread_ptr"
  apply (subgoal_tac "bound_sc_tcb_at (\<lambda>a. a = Some idle_sc_ptr) idle_thread_ptr s")
  apply (erule sym_refs_bound_sc_tcb_at_eq[rotated], assumption, assumption)
  apply (clarsimp simp: invs_def valid_state_def valid_idle_def pred_tcb_at_def obj_at_def)
  done

lemma maybeM_wp_drop_None:
  "(\<And>x. y = Some x \<Longrightarrow> \<lbrace>\<lambda>s. Q () s \<and> P x s\<rbrace> m x \<lbrace>Q\<rbrace>) \<Longrightarrow>
  \<lbrace>\<lambda>s. Q () s \<and> (\<forall>x. y = Some x \<longrightarrow> P x s)\<rbrace> maybeM m y \<lbrace>Q\<rbrace>"
  unfolding maybeM_def by (cases y; simp; wp)

lemma tc_invs[Tcb_AI_asms]:
  "\<lbrace>invs and tcb_inv_wf (ThreadControlSched t sl fh mcp pr sc)\<rbrace>
   invoke_tcb (ThreadControlSched t sl fh  mcp pr sc)
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  supply if_cong[cong]
  apply (simp add: split_def cong: option.case_cong)
  apply (wpsimp wp: maybeM_wp_drop_None, assumption)
     apply (clarsimp cong: conj_cong)
     apply (wpsimp wp: maybeM_wp_drop_None hoare_vcg_all_lift hoare_vcg_imp_lift', assumption)
    apply (clarsimp cong: conj_cong)
    apply (wpsimp wp: maybeM_wp_drop_None hoare_vcg_all_lift hoare_vcg_imp_lift', assumption)
   apply (clarsimp cong: conj_cong)
   apply (rule hoare_post_addE[where R="invs and tcb_at t and ex_nonz_cap_to t"])
   apply (clarsimp cong: conj_cong)
   apply (rule hoare_vcg_E_elim)
    apply (wpsimp wp: install_tcb_cap_invs)
   apply (wpsimp wp: hoare_vcg_const_imp_lift_R hoare_vcg_all_lift_R
                     install_tcb_cap_invs hoare_vcg_imp_lift
                     install_tcb_cap_ex_nonz_cap_to
               simp: not_pred_tcb)
  apply simp
  apply (strengthen use_no_cap_to_obj_asid_strg tcb_cap_always_valid_strg tcb_cap_valid_ep_strgs)
  apply (clarsimp cong: conj_cong simp: pred_neg_def)
  apply (subgoal_tac "\<not>bound_sc_tcb_at (\<lambda>a. a = Some idle_sc_ptr) t s")
   apply (intro conjI impI;
          (clarsimp simp: is_cnode_or_valid_arch_is_cap_simps tcb_ep_slot_cte_wp_ats real_cte_at_cte
                  dest!: valid_vtable_root_is_arch_cap)?)
     apply (intro conjI impI)
      apply (erule cte_wp_at_strengthen, simp)
     apply (erule cte_wp_at_strengthen, simp)
    apply (clarsimp simp: obj_at_def is_ep is_tcb)
   apply (intro conjI; intro allI impI)
    apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb)
   apply (clarsimp simp: obj_at_def is_tcb typ_at_eq_kheap_obj cap_table_at_typ)
   apply (clarsimp simp: obj_at_def is_ep sc_at_pred_n_def)
  apply clarsimp
  apply (drule bound_sc_tcb_at_idle_sc_idle_thread[rotated, rotated], clarsimp, clarsimp)
  apply (fastforce simp: invs_def valid_state_def sc_at_pred_n_def
                         obj_at_def valid_idle_def
                 dest!: idle_no_ex_cap)
  done

lemma check_valid_ipc_buffer_inv:
  "\<lbrace>P\<rbrace> check_valid_ipc_buffer vptr cap \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp add: check_valid_ipc_buffer_def whenE_def
             cong: cap.case_cong arch_cap.case_cong
             split del: if_split)
  apply (rule hoare_pre)
   apply (wp | simp add: whenE_def if_apply_def2 | wpcw)+
  done

lemma check_valid_ipc_buffer_wp[Tcb_AI_asms]:
  "\<lbrace>\<lambda>(s::'state_ext::state_ext state). is_arch_cap cap \<and> is_cnode_or_valid_arch cap
          \<and> valid_ipc_buffer_cap cap vptr
          \<and> is_aligned vptr msg_align_bits
             \<longrightarrow> P s\<rbrace>
     check_valid_ipc_buffer vptr cap
   \<lbrace>\<lambda>rv. P\<rbrace>,-"
  apply (simp add: check_valid_ipc_buffer_def whenE_def
             cong: cap.case_cong arch_cap.case_cong
             split del: if_split)
  apply (rule hoare_pre)
   apply (wp | simp add: whenE_def split del: if_split | wpc)+
  apply (clarsimp simp: is_cap_simps is_cnode_or_valid_arch_def
                        valid_ipc_buffer_cap_def)
  done

lemma derive_no_cap_asid[wp,Tcb_AI_asms]:
  "\<lbrace>(no_cap_to_obj_with_diff_ref cap S)::'state_ext::state_ext state\<Rightarrow>bool\<rbrace>
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


lemma decode_set_ipc_inv[wp,Tcb_AI_asms]:
  "\<lbrace>P::'state_ext::state_ext state \<Rightarrow> bool\<rbrace> decode_set_ipc_buffer args cap slot excaps \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp   add: decode_set_ipc_buffer_def whenE_def
                     split_def
          split del: if_split)
  apply (rule hoare_pre, wp check_valid_ipc_buffer_inv)
  apply simp
  done

lemma no_cap_to_obj_with_diff_ref_update_cap_data[Tcb_AI_asms]:
  "no_cap_to_obj_with_diff_ref c S s \<longrightarrow>
    no_cap_to_obj_with_diff_ref (update_cap_data P x c) S s"
  apply (case_tac "update_cap_data P x c = NullCap")
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

lemma update_cap_valid[Tcb_AI_asms]:
  "valid_cap cap (s::'state_ext::state_ext state) \<Longrightarrow>
   valid_cap (case capdata of
              None \<Rightarrow> cap_rights_update rs cap
            | Some x \<Rightarrow> update_cap_data p x
                     (cap_rights_update rs cap)) s"
  apply (case_tac capdata, simp_all)[1]
  apply (case_tac cap,
         simp_all add: update_cap_data_def cap_rights_update_def
                       is_cap_defs Let_def split_def valid_cap_def
                       badge_update_def the_cnode_cap_def cap_aligned_def
                       arch_update_cap_data_def
            split del: if_split)
     apply (simp add: badge_update_def cap_rights_update_def)
    apply (simp add: badge_update_def)
   apply (simp add: word_bits_def)
  apply (rename_tac arch_cap)
  using valid_validate_vm_rights[simplified valid_vm_rights_def]
  apply (case_tac arch_cap, simp_all add: acap_rights_update_def
                                     split: option.splits prod.splits)
  done

crunch pred_tcb_at: switch_to_thread "pred_tcb_at proj P t"
  (wp: crunch_wps simp: crunch_simps)

crunch typ_at[wp]: invoke_tcb "\<lambda>s. P (typ_at T p s)"
  (simp: crunch_simps
     wp: hoare_drop_imps mapM_x_wp' check_cap_inv)

end

context begin interpretation Arch .

requalify_consts is_cnode_or_valid_arch
requalify_facts invoke_tcb_typ_at install_tcb_cap_invs valid_vtable_root_is_arch_cap
                is_cnode_or_valid_arch_is_cap_simps

end

global_interpretation Tcb_AI?: Tcb_AI
  where is_cnode_or_valid_arch = ARM.is_cnode_or_valid_arch
proof goal_cases
  interpret Arch .
  case 1 show ?case
  by (unfold_locales; (fact Tcb_AI_asms)?)

qed

end
