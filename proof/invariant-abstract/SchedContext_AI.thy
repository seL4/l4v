(*
 * Copyright 2018, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

theory SchedContext_AI
imports
  Lib.MonadicRewrite
  RealTime_AI
begin

(* FIXME - move *)
lemma get_tcb_exst_update:
  "get_tcb p (trans_state f s) = get_tcb p s"
  by (simp add: get_tcb_def)

lemma ct_in_state_trans_update[simp]: "ct_in_state st (trans_state f s) = ct_in_state st s"
  apply (simp add: ct_in_state_def)
  done

(* RT: sc_and_timer invs *)

lemma set_refills_valid_objs:
  "\<lbrace>valid_objs and K (length refills \<ge> 1)\<rbrace>
    set_refills sc_ptr refills \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  apply (wpsimp simp: set_refills_def set_object_def
                 wp: get_object_wp update_sched_context_valid_objs_same)
  by (clarsimp simp: valid_sched_context_def )

crunches commit_domain_time,set_next_interrupt,set_refills,refill_split_check
  for consumed_time[wp]: "\<lambda>s. P (consumed_time s)"
  and reprogram_timer[wp]: "\<lambda>s. P (reprogram_timer s)"
  and cur_sc[wp]: "\<lambda>s. P (cur_sc s)"
  and cur_time[wp]: "\<lambda>s. P (cur_time s)"
  and cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  and arch_state[wp]: "\<lambda>s. P (arch_state s)"
  and cur_sc_cur_thread[wp]: "\<lambda>s. P (cur_sc s) (cur_thread s)"
  (wp: crunch_wps simp: Let_def)

crunch reprogram_timer[wp]: commit_time "\<lambda>s. P (reprogram_timer s)"
  (wp: crunch_wps hoare_vcg_if_lift2 ignore: commit_domain_time)

lemma refill_unblock_check_reprogram_timer[wp]:
  "\<lbrace>\<lambda>s. \<forall>b. P b\<rbrace> refill_unblock_check param_a \<lbrace>\<lambda>_ s. P (reprogram_timer s)\<rbrace>"
  by (wpsimp simp: refill_unblock_check_def is_round_robin_def wp: crunch_wps hoare_vcg_if_lift2)

crunches refill_unblock_check
  for consumed_time[wp]: "\<lambda>s. P (consumed_time s)"
  and cur_sc[wp]: "\<lambda>s. P (cur_sc s)"
  and cur_time[wp]: "\<lambda>s. P (cur_time s)"
  and cur_sc_cur_thread[wp]: "\<lambda>s. P (cur_sc s) (cur_thread s)"
  (wp: crunch_wps hoare_vcg_if_lift2)

lemma rollback_time_consumed_time[wp]:
  "\<lbrace>\<lambda>s. \<forall>b. P b\<rbrace> rollback_time \<lbrace>\<lambda>_ s. P (consumed_time s)\<rbrace>"
  by (wpsimp simp: rollback_time_def)

lemma cur_time_consumed_time[wp]:
  "\<lbrace>\<lambda>s. \<forall>b. P b\<rbrace> rollback_time \<lbrace>\<lambda>_ s. P (cur_time s)\<rbrace>"
  by (wpsimp simp: rollback_time_def)

lemma rollback_time_cur_time[wp]:
  "\<lbrace>\<lambda>s. \<forall>a b. P a b\<rbrace> rollback_time \<lbrace>\<lambda>_ s. P (cur_time s) (consumed_time s)\<rbrace>"
  by (wpsimp simp: rollback_time_def wp: hoare_drop_imp)

lemma commit_time_consumed_time[wp]:
  "\<lbrace>\<lambda>s. \<forall>b. P b\<rbrace> commit_time \<lbrace>\<lambda>_ s. P (consumed_time s)\<rbrace>"
  by (wpsimp simp: commit_time_def)

crunches sc_and_timer
  for consumed_time[wp]: "\<lambda>s. P (consumed_time s)"
  and reprogram_timer[wp]: "\<lambda>s. P (reprogram_timer s)"
  (wp: crunch_wps hoare_vcg_if_lift2 ignore: set_next_interrupt)

lemma valid_sc_valid_refills:
   "\<lbrakk>valid_objs s; kheap s sc_ptr = Some (SchedContext sc n) \<rbrakk>
         \<Longrightarrow> length (sc_refills sc) \<ge> 1"
  by (fastforce simp: valid_objs_def valid_obj_def valid_sched_context_def)

lemma round_robin_inv[wp]: "\<lbrace>\<lambda>s. P s\<rbrace> is_round_robin x \<lbrace> \<lambda>_ s. P s\<rbrace>"
  by (wpsimp simp: is_round_robin_def)

lemma get_refills_sp:
  "\<lbrace>P\<rbrace> get_refills sc_ptr
  \<lbrace> \<lambda>r s. P s \<and> (\<exists>sc n. ko_at (SchedContext sc n) sc_ptr s \<and> r = sc_refills sc)\<rbrace>"
  apply (simp add: get_refills_def)
  apply (rule hoare_seq_ext[rotated])
   apply (rule get_sched_context_sp)
  apply (wp hoare_return_sp)
  apply clarsimp
  apply (rule_tac x=sc in exI, auto)
  done

lemma get_refills_wp:
  "\<lbrace>\<lambda>s. \<forall>r sc n. (ko_at (SchedContext sc n) sc_ptr s \<and> r = sc_refills sc) \<longrightarrow> P r s\<rbrace>
     get_refills sc_ptr
  \<lbrace> \<lambda>r s. P r s\<rbrace>"
  by (wpsimp simp: get_sched_context_def get_refills_def wp: get_object_wp) fastforce

lemma refills_merge_valid:
  "length ls \<ge> 1 \<Longrightarrow> 1 \<le> length (refills_merge_prefix ls)"
  apply (induct ls rule: refills_merge_prefix.induct)
  by (fastforce simp add: valid_sched_context_def)+

lemma refill_unblock_check_valid_objs[wp]:
  "\<lbrace>valid_objs\<rbrace> refill_unblock_check sc_ptr \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  apply (wpsimp wp: get_sched_context_wp get_refills_wp set_refills_valid_objs
      hoare_vcg_conj_lift hoare_drop_imp hoare_vcg_if_lift2
      simp: pred_conj_def refill_unblock_check_def obj_at_def
      split: kernel_object.splits)
  apply (frule_tac sc=sc in valid_sc_valid_refills[rotated], simp)
  apply (case_tac "sc_refills sc", simp)
  apply simp
  apply (auto simp: refills_merge_valid[simplified])
  done

lemma refill_split_check_valid_objs[wp]:
  "\<lbrace>valid_objs\<rbrace> refill_split_check sc_ptr usage \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  apply (wpsimp wp: get_sched_context_wp get_refills_sp set_refills_valid_objs
      hoare_vcg_conj_lift hoare_drop_imp hoare_vcg_if_lift2 get_refills_wp
      simp: pred_conj_def refill_split_check_def obj_at_def is_sc_obj_def Let_def
      split: kernel_object.splits split_del: if_split)
  apply (frule_tac sc=sc in valid_sc_valid_refills[rotated], simp)
  apply (case_tac "sc_refills sc", simp)
  apply (auto simp: refills_merge_valid[simplified])
  done

(* move to KHeap_AI *)
crunch valid_irq_states[wp]: set_sched_context,update_sched_context "valid_irq_states"
  (wp: crunch_wps simp: crunch_simps)

(* move to Invariants_AI *)
lemma valid_irq_states_consumed_time_update[iff]:
  "valid_irq_states (consumed_time_update f s) = valid_irq_states s"
  by (simp add: valid_irq_states_def)
lemma vms_consumed_time_update[iff]:
  "valid_machine_state (consumed_time_update f s) = valid_machine_state s"
  by (simp add: valid_machine_state_def)

(* move to Invariants_AI *)
lemma valid_irq_states_cur_time_update[iff]:
  "valid_irq_states (cur_time_update f s) = valid_irq_states s"
  by (simp add: valid_irq_states_def)
lemma vms_cur_time_update[iff]:
  "valid_machine_state (cur_time_update f s) = valid_machine_state s"
  by (simp add: valid_machine_state_def)

(* move to Invariants_AI *)
lemma valid_irq_states_reprogram_timer_update[iff]:
  "valid_irq_states (reprogram_timer_update f s) = valid_irq_states s"
  by (simp add: valid_irq_states_def)
lemma vms_reprogram_timer_update[iff]:
  "valid_machine_state (reprogram_timer_update f s) = valid_machine_state s"
  by (simp add: valid_machine_state_def)

(* move to Invariants_AI *)
lemma valid_irq_states_cur_sc_update[iff]:
  "valid_irq_states (cur_sc_update f s) = valid_irq_states s"
  by (simp add: valid_irq_states_def)
lemma vms_cur_c_update[iff]:
  "valid_machine_state (cur_sc_update f s) = valid_machine_state s"
  by (simp add: valid_machine_state_def)

(* move to ArchAcc_AI? *)
lemma cur_tcb_consumed_time_update[iff]:
  "cur_tcb (consumed_time_update f s) = cur_tcb s"
  by (simp add: cur_tcb_def)

(* move to ArchAcc_AI? *)
lemma cur_tcb_cur_time_update[iff]:
  "cur_tcb (cur_time_update f s) = cur_tcb s"
  by (simp add: cur_tcb_def)

(* move to ArchAcc_AI? *)
lemma cur_tcb_cur_sc_update[iff]:
  "cur_tcb (cur_sc_update f s) = cur_tcb s"
  by (simp add: cur_tcb_def)

(* move to ArchAcc_AI? *)
lemma cur_tcb_reprogram_timer_update[iff]:
  "cur_tcb (reprogram_timer_update f s) = cur_tcb s"
  by (simp add: cur_tcb_def)

lemma refs_of_sc_consumed_update[iff]:
  "refs_of_sc (sc_consumed_update f sc) = refs_of_sc sc"
  by simp

lemma refs_of_sc_refills_update[iff]:
  "refs_of_sc (sc_refills_update f sc) = refs_of_sc sc"
  by simp

lemma refs_of_sc_refill_max_update[iff]:
  "refs_of_sc (sc_refill_max_update f sc) = refs_of_sc sc"
  by simp

lemma refs_of_sc_badge_update[iff]:
  "refs_of_sc (sc_badge_update f sc) = refs_of_sc sc"
  by simp

lemma refs_of_sc_period_update[iff]:
  "refs_of_sc (sc_period_update f sc) = refs_of_sc sc"
  by simp

lemma refs_of_sched_context_sc_consumed_update[iff]:
  "refs_of (SchedContext (sc_consumed_update f sc) n) = refs_of (SchedContext sc n)"
  by simp

lemma refs_of_sched_context_sc_refills_update[iff]:
  "refs_of (SchedContext (sc_refills_update f sc) n) = refs_of (SchedContext sc n)"
  by simp

lemma refs_of_sched_context_sc_badge_update[iff]:
  "refs_of (SchedContext (sc_badge_update f sc) n) = refs_of (SchedContext sc n)"
  by simp

lemma set_refills_iflive[wp]:
  "\<lbrace>if_live_then_nonz_cap\<rbrace> set_refills ptr param_b \<lbrace>\<lambda>_. if_live_then_nonz_cap\<rbrace> "
  by (wpsimp simp: set_refills_def get_sched_context_def wp: hoare_vcg_all_lift get_object_wp)

lemma valid_sc_sc_consumed_update[iff]:
  "valid_sched_context (sc_consumed_update f sc) = valid_sched_context sc"
  by (fastforce simp: valid_sched_context_def)

lemma valid_sc_sc_badge_update[iff]:
  "valid_sched_context (sc_badge_update f sc) = valid_sched_context sc"
  by (fastforce simp: valid_sched_context_def)

lemma invs_consumed_time_update[iff]:
  "invs (consumed_time_update f s) = invs s"
  by (clarsimp simp: invs_def valid_state_def)

lemma invs_cur_time_update[iff]:
  "invs (cur_time_update f s) = invs s"
  by (clarsimp simp: invs_def valid_state_def)

lemma invs_cur_sc_update[iff]:
  "invs (cur_sc_update f s) = invs s"
  by (clarsimp simp: invs_def valid_state_def)

lemma invs_reprogram_timer_update[iff]:
  "invs (reprogram_timer_update f s) = invs s"
  by (clarsimp simp: invs_def valid_state_def)

lemma set_refills_zombies_final[wp]:
  "\<lbrace>zombies_final\<rbrace> set_refills ptr param_b \<lbrace>\<lambda>_. zombies_final\<rbrace> "
  by (wpsimp simp: set_refills_def)

(* Move *)
lemma if_fun_simp: "(\<lambda>x. if x = y then f y else f x) = f "
  by (rule all_ext) auto

lemma set_refills_valid_sc[wp]:
   "\<lbrace>valid_sched_context sc \<rbrace>
        set_refills ptr refills \<lbrace>\<lambda>rv. valid_sched_context sc\<rbrace>"
 by (wpsimp wp: valid_sc_typ simp: set_refills_def)

lemma set_refills_refs_of [wp]:
 "\<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace>
    set_refills ptr refills
  \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (wpsimp simp: set_refills_def get_sched_context_def
          simp_del: refs_of_defs fun_upd_apply
          wp: get_object_wp update_sched_context_refs_of_same)
  done

lemma set_refills_hyp_refs_of[wp]:
  "\<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace> set_refills ptr refills  \<lbrace>\<lambda>rv s. P (state_hyp_refs_of s)\<rbrace>"
  by (wpsimp simp: set_refills_def)

global_interpretation update_sched_context: non_reply_op "update_sched_context ptr f"
  by unfold_locales (wpsimp simp: update_sched_context_def reply_at_pred_def obj_at_def
                              wp: set_object_wp get_object_wp)

global_interpretation set_sched_context: non_reply_op "set_sched_context ptr sc"
  by unfold_locales (wpsimp simp: set_sched_context_def reply_at_pred_def obj_at_def
                              wp: set_object_wp get_object_wp)

(* FIXME: move *)
lemma update_sched_context_wp:
  "\<lbrace> \<lambda>s. \<forall>sc n. ko_at (SchedContext sc n) sc_ptr s
                \<longrightarrow> Q (s\<lparr>kheap := kheap s(sc_ptr \<mapsto> SchedContext (f sc) n)\<rparr>) \<rbrace>
    update_sched_context sc_ptr f
   \<lbrace> \<lambda>rv. Q \<rbrace>"
  by (wpsimp simp: update_sched_context_def wp: set_object_wp get_object_wp)

(* FIXME: move *)
lemma set_sched_context_wp:
  "\<lbrace> \<lambda>s. \<forall>sc' n. ko_at (SchedContext sc' n) sc_ptr s
                 \<longrightarrow> Q (s\<lparr>kheap := kheap s(sc_ptr \<mapsto> SchedContext sc n)\<rparr>) \<rbrace>
    set_sched_context sc_ptr sc
   \<lbrace> \<lambda>rv. Q \<rbrace>"
  by (wpsimp simp: set_sched_context_def wp: set_object_wp get_object_wp)

definition replies_with_sc_upd_replies ::
  "obj_ref list \<Rightarrow> obj_ref \<Rightarrow> (obj_ref \<times> obj_ref) set \<Rightarrow> (obj_ref \<times> obj_ref) set"
  where
  "replies_with_sc_upd_replies rs sc rs_with_sc \<equiv>
    {p. if snd p = sc then fst p \<in> set rs else p \<in> rs_with_sc}"

lemma replies_with_sc_replies_upd:
  "replies_with_sc (s\<lparr>kheap := kheap s(sc_ptr \<mapsto> SchedContext sc n)\<rparr>)
     = replies_with_sc_upd_replies (sc_replies sc) sc_ptr (replies_with_sc s)"
  by (auto simp: replies_with_sc_upd_replies_def replies_with_sc_def
                 sc_replies_sc_at_def obj_at_def)

(* Avoid using this directly. Use one of the following instead:
   - update_sc_but_not_sc_replies_valid_replies[wp]
   - update_sc_replies_valid_replies *)
lemma update_sched_context_valid_replies:
  "\<lbrace> \<lambda>s. \<forall>sc n. ko_at (SchedContext sc n) sc_ptr s
                \<longrightarrow> P (replies_with_sc_upd_replies (sc_replies (f sc)) sc_ptr (replies_with_sc s))
                      (replies_blocked s) \<rbrace>
    update_sched_context sc_ptr f
   \<lbrace> \<lambda>rv. valid_replies_pred P \<rbrace>"
  apply (rule hoare_lift_Pf2[where f=replies_blocked, rotated])
   apply (wp replies_blocked_lift)
  apply (wp update_sched_context_wp)
  by (clarsimp simp: sc_replies_sc_at_def obj_at_def replies_with_sc_replies_upd)

lemma set_sched_context_valid_replies:
  "\<lbrace> \<lambda>s. P (replies_with_sc_upd_replies (sc_replies sc) sc_ptr (replies_with_sc s))
           (replies_blocked s) \<rbrace>
    set_sched_context sc_ptr sc
   \<lbrace> \<lambda>rv. valid_replies_pred P \<rbrace>"
  apply (rule hoare_lift_Pf2[where f=replies_blocked, rotated])
   apply (wp replies_blocked_lift)
  apply (wp set_sched_context_wp)
  by (clarsimp simp: sc_replies_sc_at_def obj_at_def replies_with_sc_replies_upd)

lemma update_sc_replies_valid_replies:
  "\<lbrace> \<lambda>s. \<forall>rs. sc_replies_sc_at (\<lambda>rs'. set rs' = set rs) sc_ptr s
              \<longrightarrow> P (replies_with_sc_upd_replies (f rs) sc_ptr (replies_with_sc s))
                    (replies_blocked s) \<rbrace>
    update_sched_context sc_ptr (sc_replies_update f)
   \<lbrace> \<lambda>rv. valid_replies_pred P \<rbrace>"
  by (wpsimp wp: update_sched_context_valid_replies)
     (fastforce simp: sc_replies_sc_at_def obj_at_def elim!: rsubst2[of P, OF _ _ refl])

(* Avoid using this directly. Use one of the following instead:
   - update_sc_but_not_sc_replies_valid_replies[wp]
   - update_sc_replies_valid_replies *)
lemma update_sc_but_not_sc_replies_valid_replies':
  assumes "\<And>sc. sc_replies (f sc) = sc_replies sc"
  shows "update_sched_context sc_ptr f \<lbrace> valid_replies_pred P \<rbrace>"
  by (wpsimp wp: update_sched_context_valid_replies)
     (fastforce simp: replies_with_sc_upd_replies_def replies_with_sc_def
                      sc_replies_sc_at_def obj_at_def assms
               split: if_splits
               elim!: rsubst2[of P, OF _ _ refl])

lemma update_sc_but_not_sc_replies_valid_replies[wp]:
  "\<And>f. update_sched_context sc_ptr (sc_period_update f) \<lbrace> valid_replies_pred P \<rbrace>"
  "\<And>f. update_sched_context sc_ptr (sc_consumed_update f) \<lbrace> valid_replies_pred P \<rbrace>"
  "\<And>f. update_sched_context sc_ptr (sc_tcb_update f) \<lbrace> valid_replies_pred P \<rbrace>"
  "\<And>f. update_sched_context sc_ptr (sc_tcb_update f) \<lbrace> valid_replies_pred P \<rbrace>"
  "\<And>f. update_sched_context sc_ptr (sc_ntfn_update f) \<lbrace> valid_replies_pred P \<rbrace>"
  "\<And>f. update_sched_context sc_ptr (sc_refills_update f) \<lbrace> valid_replies_pred P \<rbrace>"
  "\<And>f. update_sched_context sc_ptr (sc_refill_max_update f) \<lbrace> valid_replies_pred P \<rbrace>"
  "\<And>f. update_sched_context sc_ptr (sc_badge_update f) \<lbrace> valid_replies_pred P \<rbrace>"
  "\<And>f. update_sched_context sc_ptr (sc_yield_from_update f) \<lbrace> valid_replies_pred P \<rbrace>"
  by (rule update_sc_but_not_sc_replies_valid_replies', simp)+

lemma set_refills_valid_replies[wp]:
  "set_refills ptr refills \<lbrace> valid_replies_pred P \<rbrace>"
  by (wpsimp simp: set_refills_def)

lemma set_refills_invs[wp]:
  "\<lbrace>invs and K (length refills \<ge> 1)\<rbrace> set_refills ptr refills \<lbrace>\<lambda>_. invs\<rbrace> "
  apply (wpsimp simp: set_refills_def invs_def valid_state_def valid_pspace_def
                wp: valid_irq_node_typ get_sched_context_wp
                    update_sched_context_valid_objs_same
                    update_sched_context_refs_of_same)
  by (clarsimp simp: valid_sched_context_def)

crunches refill_split_check
 for aligned[wp]: pspace_aligned
 and distinct[wp]: pspace_distinct
 and iflive[wp]: if_live_then_nonz_cap
 and sc_at[wp]: "sc_at sc_ptr"
 and cte_wp_at[wp]: "cte_wp_at P c"
 and interrupt_irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"
 and caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"
 and no_cdt[wp]: "\<lambda>s. P (cdt s)"
 and no_revokable[wp]: "\<lambda>s. P (is_original_cap s)"
 and valid_idle[wp]: valid_idle
 and valid_irq_handlers[wp]: valid_irq_handlers
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
 and cap_refs_in_kernel_window[wp]: "cap_refs_in_kernel_window"
 and cap_refs_respects_device_region[wp]: "cap_refs_respects_device_region"
 and pspace_respects_device_region[wp]: "pspace_respects_device_region"
 and cur_tcb[wp]: "cur_tcb"
 and valid_ioc[wp]: "valid_ioc"
 and typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  (simp: Let_def wp: hoare_drop_imps)

lemma refill_split_check_zombies[wp]:
  "\<lbrace>zombies_final\<rbrace> refill_split_check p u \<lbrace>\<lambda>rv. zombies_final\<rbrace>"
  by (wpsimp simp: refill_split_check_def Let_def split_del: if_split wp: hoare_drop_imp)

lemma refill_split_check_ex_cap[wp]:
  "\<lbrace>ex_nonz_cap_to p\<rbrace> refill_split_check p u \<lbrace>\<lambda>rv. ex_nonz_cap_to p\<rbrace>"
  by (wp ex_nonz_cap_to_pres)

lemma refill_split_check_mdb [wp]:
  "\<lbrace>valid_mdb\<rbrace> refill_split_check p u  \<lbrace>\<lambda>r. valid_mdb\<rbrace>"
  by (wpsimp wp: valid_mdb_lift)

lemma refill_split_check_hyp_refs_of[wp]:
  "\<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace> refill_split_check p u \<lbrace>\<lambda>rv s. P (state_hyp_refs_of s)\<rbrace>"
  by (wpsimp simp: refill_split_check_def Let_def split_del: if_split wp: hoare_drop_imp)

lemma refill_split_check_refs_of[wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace> refill_split_check p u \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  by (wpsimp simp: refill_split_check_def Let_def split_del: if_split wp: hoare_drop_imp)

lemma refill_split_check_invs[wp]: "\<lbrace>invs\<rbrace> refill_split_check p u \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wpsimp simp: refill_split_check_def Let_def split_del: if_split
             wp: hoare_drop_imp get_sched_context_wp get_refills_wp)
  apply simp
  done

declare refs_of_defs[simp del]
lemma refill_split_check_valid_sc[wp]:
   "\<lbrace>valid_sched_context sc\<rbrace> refill_split_check p u \<lbrace>\<lambda>rv. valid_sched_context sc\<rbrace>"
 by (wpsimp simp: refill_split_check_def Let_def split_del: if_split
            wp: hoare_drop_imp)

lemma set_sched_context_valid_irq_node [wp]:
  "\<lbrace>valid_irq_node\<rbrace> set_sched_context p sc  \<lbrace>\<lambda>r. valid_irq_node\<rbrace>"
  by (wpsimp wp: valid_irq_node_typ)

lemma valid_sc_kheap_update':
  "sc_at p s \<Longrightarrow> a_type ko = ASchedContext n \<Longrightarrow>
   valid_sched_context sc (s\<lparr>kheap := kheap s(p \<mapsto> ko)\<rparr>)
         = valid_sched_context sc s"
  apply (clarsimp simp: valid_sched_context_def valid_bound_obj_def obj_at_def is_obj_defs
      split: if_split_asm option.splits kernel_object.splits)
  apply safe
                      apply ((rule list_allI, assumption, clarsimp) | fastforce)+
  done

lemma valid_sc_kheap_update[simp]:
  "sc_at p s \<Longrightarrow>
   valid_sched_context sc (s\<lparr>kheap := kheap s(p \<mapsto> SchedContext sc' n)\<rparr>)
         = valid_sched_context sc s"
  apply (clarsimp simp: valid_sched_context_def valid_bound_obj_def obj_at_def is_obj_defs
      split: if_split_asm option.splits kernel_object.splits)
  apply safe
                      apply ((rule list_allI, assumption, clarsimp) | fastforce)+
  done

lemma set_sched_context_valid_sched_context[wp]:
  "\<lbrace>sc_at p and valid_sched_context x\<rbrace>
    set_sched_context p sc
   \<lbrace>\<lambda>r. valid_sched_context x\<rbrace>"
  by (wpsimp simp: set_sched_context_def wp: set_object_wp get_object_wp)

lemma set_sched_context_update_sched_context:
  "set_sched_context p sc = update_sched_context p (\<lambda>_. sc)"
  by (simp add: set_sched_context_def update_sched_context_def)

(* FIXME: move *)
lemma monadic_rewrite_sym:
  "monadic_rewrite False True P f g \<Longrightarrow> monadic_rewrite False True P g f"
  by (simp add: monadic_rewrite_def)

lemma monadic_rewrite_set_sched_context:
  "monadic_rewrite False True
     (\<lambda>s. \<forall>sc' n. ko_at (SchedContext sc' n) p s \<longrightarrow> sc = f sc')
     (set_sched_context p sc)
     (update_sched_context p f)"
  apply (simp add: set_sched_context_def update_sched_context_def)
  apply (rule monadic_rewrite_imp)
   apply (rule monadic_rewrite_bind[where Q="\<lambda>obj s. \<forall>sc' n. obj = SchedContext sc' n \<longrightarrow> sc = f sc'"
                                    , OF monadic_rewrite_refl])
    apply (fastforce simp: monadic_rewrite_def split: kernel_object.splits)
   apply (wpsimp wp: get_object_wp)
  by (fastforce simp: obj_at_def)

lemma hoare_rewrite_set_sched_context:
  assumes upd: "\<lbrace> P' \<rbrace> update_sched_context p f \<lbrace> \<lambda>rv. Q \<rbrace>"
  assumes sc: "\<And>s sc' n. P s \<Longrightarrow> ko_at (SchedContext sc' n) p s \<Longrightarrow> sc = f sc'"
  assumes pre: "\<And>s. P s \<Longrightarrow> P' s"
  shows "\<lbrace> P \<rbrace> set_sched_context p sc \<lbrace> \<lambda>rv. Q \<rbrace>"
  apply (rule hoare_pre)
   apply (rule monadic_rewrite_refine_valid[where F=False and P''=\<top>, simplified])
    apply (rule monadic_rewrite_sym)
    apply (rule monadic_rewrite_set_sched_context)
   apply (rule upd)
  by (clarsimp simp: sc pre)

lemma hoare_rewrite_update_sched_context:
  assumes upd: "\<lbrace> P' \<rbrace> set_sched_context p sc \<lbrace> \<lambda>rv. Q \<rbrace>"
  assumes sc: "\<And>s sc' n. P s \<Longrightarrow> ko_at (SchedContext sc' n) p s \<Longrightarrow> sc = f sc'"
  assumes pre: "\<And>s. P s \<Longrightarrow> P' s"
  shows "\<lbrace> P \<rbrace> update_sched_context p f \<lbrace> \<lambda>rv. Q \<rbrace>"
  apply (rule hoare_pre)
   apply (rule monadic_rewrite_refine_valid[where F=False and P''=\<top>, simplified])
    apply (rule monadic_rewrite_set_sched_context)
   apply (rule upd)
  by (clarsimp simp: sc pre)

(* FIXME: move *)
lemma subset_union_non_overlapping:
  "A \<inter> B = {} \<Longrightarrow> A \<subseteq> B \<union> C \<longleftrightarrow> A \<subseteq> C"
  "A \<inter> C = {} \<Longrightarrow> A \<subseteq> B \<union> C \<longleftrightarrow> A \<subseteq> B"
  by auto

lemma replies_with_sc_upd_replies_trivial:
  assumes "kheap s p = Some (SchedContext sc n)"
  assumes "set rs = set (sc_replies sc)"
  shows "replies_with_sc_upd_replies rs p (replies_with_sc s) = replies_with_sc s"
  using assms
  apply (clarsimp simp: replies_with_sc_upd_replies_def replies_with_sc_def
                        sc_replies_sc_at_def obj_at_def)
  apply (intro set_eqI iffI; clarsimp)
  done

lemma set_sc_consumed_invs:
  "\<lbrace>invs and (\<lambda>s. (\<exists>n. ko_at (SchedContext sc n) p s))\<rbrace>
      set_sched_context p (sc\<lparr>sc_consumed := i \<rparr>) \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def obj_at_def
                simp_del: fun_upd_apply
                wp: valid_ioports_lift set_sched_context_valid_replies)
  apply safe
     apply (fastforce simp: valid_obj_def)
    apply (fastforce simp: if_live_then_nonz_cap_def obj_at_def live_def)
   apply (fastforce simp: replies_with_sc_upd_replies_trivial)
  by (fastforce simp: state_refs_of_def refs_of_def fun_upd_idem)

lemma update_sched_context_valid_sched_context[wp]:
  "\<lbrace>sc_at p and valid_sched_context x\<rbrace>
    update_sched_context p f
   \<lbrace>\<lambda>r. valid_sched_context x\<rbrace>"
  by (wpsimp simp: update_sched_context_def wp: set_object_wp get_object_wp)

lemma update_sc_consumed_invs:
  "\<lbrace>invs and (\<lambda>s. (\<exists>n. ko_at (SchedContext sc n) p s))\<rbrace>
      update_sched_context p (\<lambda>sc. sc\<lparr>sc_consumed := i \<rparr>) \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (wpsimp simp: invs_def valid_state_def valid_pspace_def obj_at_def
             simp_del: fun_upd_apply
             wp: update_sched_context_valid_objs_same
                 update_sched_context_refs_of_same
                 valid_irq_node_typ)

lemma refill_unblock_check_invs: "\<lbrace>invs\<rbrace> refill_unblock_check r \<lbrace>\<lambda>rv. invs\<rbrace>"
    by (wpsimp simp: refill_unblock_check_def refills_merge_valid[simplified]
                     is_round_robin_def
               wp: get_refills_inv hoare_drop_imp get_sched_context_wp)

declare domain_time_update.state_refs_update[simp]

(* FIXME: move *)
lemma valid_mdb_domain_time_update[simp]:
  "valid_mdb (domain_time_update f s) = valid_mdb s"
  by (simp add: valid_mdb_def mdb_cte_at_def)

(* FIXME: move *)
lemma valid_ioc_domain_time_update[simp]:
  "valid_ioc (domain_time_update f s) = valid_ioc s"
  by (simp add: valid_ioc_def)

(* FIXME: move *)
lemma valid_irq_states_domain_time_update[simp]:
  "valid_irq_states (domain_time_update f s) = valid_irq_states s"
  by (simp add: valid_irq_states_def)

(* FIXME: move *)
lemma valid_machine_state_domain_time_update[simp]:
  "valid_machine_state (domain_time_update f s) = valid_machine_state s"
  by (simp add: valid_machine_state_def)

(* FIXME: move *)
lemma cur_tcb_domain_time_update[simp]:
  "cur_tcb (domain_time_update f s) = cur_tcb s"
  by (simp add: cur_tcb_def)

lemma commit_domain_time_valid_replies[wp]:
  "commit_domain_time \<lbrace> valid_replies_pred P \<rbrace>"
  by (wpsimp simp: commit_domain_time_def)

(* FIXME: move *)
lemma valid_sched_context_domain_time_update[simp]:
  "valid_sched_context p (domain_time_update f s) = valid_sched_context p s"
  by (simp add: valid_sched_context_def valid_bound_obj_def split: option.splits)

lemma refill_split_check_valid_replies[wp]:
  "refill_split_check sc_ptr usage \<lbrace> valid_replies_pred P \<rbrace>"
  by (wpsimp simp: refill_split_check_def Let_def split_del: if_split)

lemma commit_time_valid_replies[wp]:
  "commit_time \<lbrace> valid_replies_pred P \<rbrace>"
  by (wpsimp simp: commit_time_def wp: hoare_drop_imps cong: sched_context.fold_congs)

lemma update_sched_context_valid_objs_same_eq:
  "\<lbrace>\<lambda>s. valid_objs s \<and> (\<forall>sc. valid_sched_context sc s = valid_sched_context (f sc) s)\<rbrace>
     update_sched_context ref f \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (wpsimp simp: update_sched_context_def get_object_def wp: set_object_valid_objs)
  apply (auto simp: valid_obj_def valid_sched_context_def a_type_def obj_at_def)
  done

lemma commit_times_invs_helper:
  " \<lbrace>(\<lambda>s. invs s \<and>
             consumed_time s = consumed \<and>
             cur_sc s = csc \<and> sc_at csc s)\<rbrace>
       do x <- get_sched_context csc;
          xa <- gets cur_time;
          xb <- assert (sufficient_refills consumed (sc_refills x));
          y <- assert (r_time (refill_hd x) \<le> xa + kernelWCET_ticks);
          y <- commit_domain_time;
          y <-
          update_sched_context csc (\<lambda>sc. sc\<lparr>sc_consumed := sc_consumed sc + consumed\<rparr>);
          modify (consumed_time_update (\<lambda>_. 0))
       od
       \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (wpsimp simp: commit_time_def invs_def valid_state_def valid_pspace_def
                   set_refills_def is_round_robin_def consumed_time_update_arch.state_refs_update
                   commit_domain_time_def
               wp: valid_irq_node_typ update_sched_context_refs_of_same
                   update_sched_context_valid_objs_same_eq update_sched_context_iflive_same
             cong: sched_context.fold_congs)

lemma commit_time_invs:
  "commit_time \<lbrace>invs\<rbrace>"
  supply fun_upd_apply[simp del]
  apply (clarsimp simp: commit_time_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (case_tac "0 < consumed"; clarsimp split del: if_split simp: bind_assoc)
   apply (wpsimp wp: commit_times_invs_helper hoare_vcg_ex_lift)
   apply (clarsimp simp: obj_at_def is_sc_obj_def)
   apply (frule invs_valid_objs)
   apply (frule (1) valid_sched_context_size_objsI, simp)
  by (wpsimp simp: commit_time_def invs_def valid_state_def valid_pspace_def
                   set_refills_def is_round_robin_def consumed_time_update_arch.state_refs_update
                   commit_domain_time_def
               wp: valid_irq_node_typ update_sched_context_refs_of_same
                   update_sched_context_valid_objs_same_eq update_sched_context_iflive_same
             cong: sched_context.fold_congs)

crunches switch_sched_context
  for consumed_time[wp]: "\<lambda>s. P (consumed_time s)"
  and reprogram_timer[wp]: "\<lambda>s. P (reprogram_timer s)"
  and cur_time[wp]: "\<lambda>s. P (cur_time s)"
  and cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  (wp: crunch_wps hoare_vcg_if_lift2 simp: Let_def ignore: commit_domain_time)

crunch inv[wp]: refill_capacity,refill_sufficient,refill_ready "\<lambda>s. P s"

lemma switch_sched_context_invs[wp]:
  "\<lbrace>invs\<rbrace> switch_sched_context \<lbrace>\<lambda>_. invs \<rbrace>"
  by (wpsimp simp: switch_sched_context_def rollback_time_def get_tcb_queue_def
                   get_sc_obj_ref_def
         wp: hoare_if gbn_inv commit_time_invs refill_unblock_check_invs
             hoare_drop_imp hoare_vcg_if_lift2)

lemma set_next_interrupt_invs[wp]: "\<lbrace>invs\<rbrace> set_next_interrupt \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (wpsimp simp: set_next_interrupt_def
       wp: hoare_drop_imp get_sched_context_wp set_next_timer_interrupt_invs)

lemma sc_and_timer_invs: "\<lbrace>invs\<rbrace> sc_and_timer \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (wpsimp simp: sc_and_timer_def)

(* move to Invariants_AI *)
lemma ct_in_state_reprogram_timer_update[iff]:
  "ct_in_state st (reprogram_timer_update f s) = ct_in_state st s"
  by (simp add: ct_in_state_def)
lemma ct_in_state_consumed_time_update[iff]:
  "ct_in_state st (consumed_time_update f s) = ct_in_state st s"
  by (simp add: ct_in_state_def)
lemma ct_in_state_cur_time_update[iff]:
  "ct_in_state st (cur_time_update f s) = ct_in_state st s"
  by (simp add: ct_in_state_def)
lemma ct_in_state_cur_sc_update[iff]:
  "ct_in_state st (cur_sc_update f s) = ct_in_state st s"
  by (simp add: ct_in_state_def)

crunch pred_tcb_at[wp]: commit_time "\<lambda>s. P (pred_tcb_at proj f t s)"
  (simp: crunch_simps wp: crunch_wps)

lemma set_sched_context_ct_in_state[wp]:
  "\<lbrace> ct_in_state t \<rbrace> set_sched_context p sc \<lbrace> \<lambda>rv. ct_in_state t \<rbrace>"
  by (wpsimp simp: set_sched_context_def set_object_def get_object_def obj_at_def
                      pred_tcb_at_def ct_in_state_def simp_del: fun_upd_apply) fastforce

lemma update_sched_context_ct_in_state[wp]:
  "\<lbrace> ct_in_state t \<rbrace> update_sched_context p f \<lbrace> \<lambda>rv. ct_in_state t \<rbrace>"
  by (wpsimp simp: update_sched_context_def set_object_def get_object_def obj_at_def
                      pred_tcb_at_def ct_in_state_def simp_del: fun_upd_apply) fastforce

lemma set_refills_ct_in_state[wp]:
  "\<lbrace> ct_in_state t \<rbrace> set_refills p r \<lbrace> \<lambda>rv. ct_in_state t \<rbrace>"
  by (wpsimp simp: set_refills_def wp: get_sched_context_wp)

lemma refill_split_check_ct_in_state[wp]:
  "\<lbrace> ct_in_state t \<rbrace> refill_split_check csc consumed \<lbrace> \<lambda>rv. ct_in_state t \<rbrace>"
  by (wpsimp simp: refill_split_check_def Let_def split_del: if_split
             wp: get_sched_context_wp get_refills_wp)

(* FIXME: move *)
lemma ct_in_state_domain_time_update[simp]:
  "ct_in_state st (domain_time_update f s) = ct_in_state st s"
  by (simp add: ct_in_state_def)

crunch ct_in_state[wp]: commit_time "ct_in_state t"
  (simp: crunch_simps wp: crunch_wps)

lemma rollback_time_ct_in_state[wp]:
  "\<lbrace> ct_in_state t \<rbrace> rollback_time \<lbrace> \<lambda>rv. ct_in_state t \<rbrace>"
  by (wpsimp simp: rollback_time_def)

lemma refill_unblock_check_ct_in_state[wp]:
  "\<lbrace> ct_in_state t \<rbrace> refill_unblock_check csc \<lbrace> \<lambda>rv. ct_in_state t \<rbrace>"
  by (wpsimp wp: get_refills_wp get_sched_context_wp
       simp: refill_unblock_check_def is_round_robin_def refills_merge_valid[simplified])

lemma switch_sched_context_ct_in_state[wp]:
  "\<lbrace> ct_in_state t \<rbrace> switch_sched_context \<lbrace> \<lambda>rv. ct_in_state t \<rbrace>"
  by (wpsimp simp: switch_sched_context_def get_tcb_queue_def get_sc_obj_ref_def
             wp: hoare_drop_imp hoare_vcg_if_lift2)

(* FIXME Move *)
context Arch begin global_naming ARM

lemma set_next_interrupt_activatable:
  "\<lbrace>ct_in_state activatable\<rbrace> set_next_timer_interrupt t \<lbrace>\<lambda>rv. ct_in_state activatable\<rbrace>"
  apply (clarsimp simp: set_next_timer_interrupt_def)
  apply (wpsimp simp: ct_in_state_def wp: ct_in_state_thread_state_lift)
  done

end

lemma set_next_interrupt_activatable:
  "\<lbrace>ct_in_state activatable\<rbrace> set_next_interrupt \<lbrace>\<lambda>rv. ct_in_state activatable\<rbrace>"
  apply (clarsimp simp: set_next_interrupt_def set_next_timer_interrupt_def)
  apply (wpsimp simp: ct_in_state_def
      wp: hoare_drop_imp ct_in_state_thread_state_lift
         ARM.set_next_interrupt_activatable[simplified ARM.set_next_interrupt_activatable, simplified])
  done


lemma sc_and_timer_activatable:
  "\<lbrace>ct_in_state activatable\<rbrace> sc_and_timer \<lbrace>\<lambda>rv. ct_in_state activatable\<rbrace>"
  apply (wpsimp simp: sc_and_timer_def switch_sched_context_def get_tcb_queue_def get_sc_obj_ref_def
           wp: hoare_drop_imp modify_wp hoare_vcg_if_lift2 set_next_interrupt_activatable)
  done

lemma refill_add_tail_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> refill_add_tail sc_ptr rfl \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by (wpsimp simp: refill_add_tail_def wp: get_sched_context_wp get_refills_wp)

lemma maybe_add_empty_tail_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> maybe_add_empty_tail sc_ptr \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by (wpsimp simp: maybe_add_empty_tail_def wp: get_sched_context_wp)

lemma refill_new_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> refill_new sc_ptr new_period new_budget new_max_refills
      \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by (wpsimp simp: refill_new_def wp: get_sched_context_wp)

lemma refill_update_typ_at[wp]: (* check the definition *)
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> refill_update sc_ptr new_period new_budget new_max_refills
      \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by (wpsimp simp: refill_update_def wp: get_sched_context_wp)

crunch typ_at[wp]: is_schedulable "\<lambda>s. P (typ_at T p s)"
  (wp: crunch_wps select_ext_wp ignore: set_refills)

lemma sched_context_resume_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> sched_context_resume sc_ptr
      \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by (wpsimp simp: sched_context_resume_def
      wp: get_sched_context_wp hoare_vcg_if_lift2 hoare_drop_imp)


crunch invs[wp]: set_message_info invs
crunches set_message_info,sched_context_update_consumed
 for tcb_at[wp]: "tcb_at t"
 and cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  (wp: get_object_wp)

lemma set_sched_context_tcb_at_ct[wp]:
  "\<lbrace>\<lambda>s. tcb_at (cur_thread s) s\<rbrace> set_sched_context p sc \<lbrace>\<lambda>rv s. tcb_at (cur_thread s) s\<rbrace>"
  by (wpsimp simp: set_sched_context_def set_object_def obj_at_def is_tcb_def wp: get_object_wp)

lemma update_sched_context_tcb_at_ct[wp]:
  "\<lbrace>\<lambda>s. tcb_at (cur_thread s) s\<rbrace> update_sched_context p f \<lbrace>\<lambda>rv s. tcb_at (cur_thread s) s\<rbrace>"
  by (wpsimp simp: update_sched_context_def set_object_def obj_at_def is_tcb_def wp: get_object_wp)

lemma sched_context_update_consumed_tcb_at_ct[wp]:
  "\<lbrace>\<lambda>s. tcb_at (cur_thread s) s\<rbrace> sched_context_update_consumed scp \<lbrace>\<lambda>rv s. tcb_at (cur_thread s) s\<rbrace>"
  by (wpsimp simp: sched_context_update_consumed_def)

lemma sched_context_update_consumed_invs[wp]:
  "\<lbrace>invs\<rbrace> sched_context_update_consumed scp \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (wpsimp simp: sched_context_update_consumed_def
      wp: set_sc_consumed_invs get_sched_context_wp)

lemma set_sched_context_minor_invs: (* minor? *)
  "\<lbrace>invs and sc_at_pred (\<lambda>sc. sc) (\<lambda>sc. refs_of_sc sc = refs_of_sc sc'
                                         \<and> set (sc_replies sc) = set (sc_replies sc')) ptr
         and valid_sched_context sc'
         and (\<lambda>s. live_sc sc' \<longrightarrow> ex_nonz_cap_to ptr s)\<rbrace>
     set_sched_context ptr sc'
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                  wp: valid_irq_node_typ valid_ioports_lift set_sched_context_valid_replies
            simp_del: fun_upd_apply)
  apply (clarsimp simp: sc_at_pred_def obj_at_def replies_with_sc_upd_replies_trivial)
  apply (erule rsubst[of sym_refs], rule ext)
  by (clarsimp simp: state_refs_of_def refs_of_sc_def)

lemma ssc_refs_of_Some[wp]:
  "\<lbrace>\<lambda>s. P ((state_refs_of s)(t:= insert (sc, TCBSchedContext)
          {x \<in> state_refs_of s t. snd x \<noteq> TCBSchedContext}))\<rbrace>
   set_tcb_obj_ref tcb_sched_context_update t (Some sc)
   \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (wpsimp simp: set_object_def wp: gets_the_wp)
  by (fastforce elim!: rsubst[where P=P] dest!: get_tcb_SomeD
                 simp: state_refs_of_def conj_disj_distribR get_refs_def2
                       get_tcb_rev pred_tcb_def2 mem_Times_iff tcb_st_refs_of_def
               intro!: ext split: thread_state.splits)

lemma ssc_refs_of_None[wp]:
  "\<lbrace>\<lambda>s. P ((state_refs_of s)(t:= {x \<in> state_refs_of s t. snd x \<noteq> TCBSchedContext}))\<rbrace>
   set_tcb_obj_ref tcb_sched_context_update t None
   \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (wpsimp simp: set_object_def wp: gets_the_wp)
  by (fastforce elim!: rsubst[where P=P] dest!: get_tcb_SomeD
                 simp: state_refs_of_def conj_disj_distribR get_refs_def2
                       get_tcb_rev pred_tcb_def2 mem_Times_iff tcb_st_refs_of_def
               intro!: ext split: thread_state.splits)


lemma zombies_kheap_update:
  "\<lbrakk> zombies_final s; obj_at (same_caps ko) t s \<rbrakk>
   \<Longrightarrow> zombies_final (s\<lparr>kheap := kheap s(t \<mapsto> ko)\<rparr>)"
  apply (simp add: zombies_final_def is_final_cap'_def2, elim allEI)
  apply (clarsimp simp: cte_wp_at_after_update fun_upd_def)
  done


text {* bind/unbind invs lemmas *}

global_interpretation set_sc_obj_ref: non_reply_op "set_sc_obj_ref f ref new"
  by (simp add: set_sc_obj_ref_def) unfold_locales

global_interpretation set_ntfn_obj_ref: non_reply_op "set_ntfn_obj_ref f ref new"
  by unfold_locales (auto intro: update_sk_obj_ref_sk_obj_at_pred)

global_interpretation sched_context_bind_ntfn: non_reply_op "sched_context_bind_ntfn sc ntfn"
  by unfold_locales (wpsimp simp: sched_context_bind_ntfn_def)

(* Avoid using this directly. Use one of the following instead:
   - set_sc_but_not_sc_replies_valid_replies[wp]
   - set_sc_replies_valid_replies *)
lemma set_sc_obj_ref_valid_replies:
  "\<lbrace> \<lambda>s. \<forall>sc n. ko_at (SchedContext sc n) sc_ptr s
                \<longrightarrow> P (replies_with_sc_upd_replies (sc_replies (f (K val) sc)) sc_ptr (replies_with_sc s))
                      (replies_blocked s) \<rbrace>
    set_sc_obj_ref f sc_ptr val
   \<lbrace> \<lambda>rv. valid_replies_pred P \<rbrace>"
  by (wpsimp simp: set_sc_obj_ref_def wp: update_sched_context_valid_replies)

lemma set_sc_replies_valid_replies:
  "\<lbrace> \<lambda>s. P (replies_with_sc_upd_replies replies sc_ptr (replies_with_sc s)) (replies_blocked s) \<rbrace>
    set_sc_obj_ref sc_replies_update sc_ptr replies
   \<lbrace> \<lambda>rv. valid_replies_pred P \<rbrace>"
  by (wpsimp wp: set_sc_obj_ref_valid_replies)

(* Avoid using this directly. Use one of the following instead:
   - set_sc_but_not_sc_replies_valid_replies[wp]
   - set_sc_replies_valid_replies *)
lemma set_sc_but_not_sc_replies_valid_replies':
  assumes "\<And>sc. sc_replies (f (\<lambda>_. v) sc) = sc_replies sc"
  shows "set_sc_obj_ref f sc_ptr v \<lbrace> valid_replies_pred P \<rbrace>"
  by (wpsimp wp: set_sc_obj_ref_valid_replies)
     (fastforce simp: replies_with_sc_upd_replies_def replies_with_sc_def
                      sc_replies_sc_at_def obj_at_def assms
               split: if_splits
               elim!: rsubst2[of P, OF _ _ refl])

lemma set_sc_but_not_sc_replies_valid_replies[wp]:
  "\<And>v. set_sc_obj_ref sc_period_update sc_ptr v \<lbrace> valid_replies_pred P \<rbrace>"
  "\<And>v. set_sc_obj_ref sc_consumed_update sc_ptr v \<lbrace> valid_replies_pred P \<rbrace>"
  "\<And>v. set_sc_obj_ref sc_tcb_update sc_ptr v \<lbrace> valid_replies_pred P \<rbrace>"
  "\<And>v. set_sc_obj_ref sc_tcb_update sc_ptr v \<lbrace> valid_replies_pred P \<rbrace>"
  "\<And>v. set_sc_obj_ref sc_ntfn_update sc_ptr v \<lbrace> valid_replies_pred P \<rbrace>"
  "\<And>v. set_sc_obj_ref sc_refills_update sc_ptr v \<lbrace> valid_replies_pred P \<rbrace>"
  "\<And>v. set_sc_obj_ref sc_refill_max_update sc_ptr v \<lbrace> valid_replies_pred P \<rbrace>"
  "\<And>v. set_sc_obj_ref sc_badge_update sc_ptr v \<lbrace> valid_replies_pred P \<rbrace>"
  "\<And>v. set_sc_obj_ref sc_yield_from_update sc_ptr v \<lbrace> valid_replies_pred P \<rbrace>"
  by (rule set_sc_but_not_sc_replies_valid_replies', simp)+

lemma sched_context_bind_ntfn_invs[wp]:
  "\<lbrace>invs and ex_nonz_cap_to sc and ex_nonz_cap_to ntfn
    and obj_at (\<lambda>ko. \<exists>ntfn. ko = Notification ntfn \<and> (ntfn_sc ntfn = None)) ntfn
    and sc_ntfn_sc_at (\<lambda>ntfn'. ntfn' = None) sc \<rbrace>
      sched_context_bind_ntfn sc ntfn \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wpsimp simp: sched_context_bind_ntfn_def invs_def valid_state_def
      valid_pspace_def update_sk_obj_ref_def
       wp: get_simple_ko_wp valid_irq_node_typ set_simple_ko_valid_objs simple_obj_set_prop_at
           valid_ioports_lift)
  apply (clarsimp simp: obj_at_def is_ntfn sc_ntfn_sc_at_def)
  apply (case_tac "sc=ntfn", simp)
  apply safe
   apply (frule valid_objs_valid_sched_context_size)
    apply fastforce
   apply (erule (1) valid_objsE)
   apply (clarsimp simp: valid_obj_def valid_ntfn_def obj_at_def is_sc_obj_def split: ntfn.splits)
  apply (erule delta_sym_refs)
   apply (fastforce simp: state_refs_of_def obj_at_def refs_of_ntfn_def split: if_splits)
  apply (clarsimp simp: state_refs_of_def refs_of_ntfn_def get_refs_def2
                  dest!: symreftype_inverse' split: if_splits)
  done

lemma sched_context_unbind_ntfn_invs[wp]:
  notes refs_of_simps[simp del]
  shows
  "\<lbrace>invs\<rbrace> sched_context_unbind_ntfn sc \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: sched_context_unbind_ntfn_def maybeM_def get_sc_obj_ref_def)
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def update_sk_obj_ref_def
      wp: valid_irq_node_typ set_simple_ko_valid_objs get_simple_ko_wp get_sched_context_wp
          valid_ioports_lift)
  apply (clarsimp simp: obj_at_def is_ntfn sc_ntfn_sc_at_def)
  apply (case_tac "sc=x", simp)
  apply safe
    apply (frule valid_objs_valid_sched_context_size)
     apply fastforce
    apply (erule_tac x=x in valid_objsE, simp)
    apply (clarsimp simp: valid_obj_def valid_ntfn_def obj_at_def is_sc_obj_def split: ntfn.splits)
   apply (drule_tac p=x in if_live_then_nonz_capD2, simp)
    apply (clarsimp simp: live_def live_ntfn_def, assumption)
  apply (frule sym_refs_ko_atD[where p=sc, rotated])
   apply (simp add: obj_at_def, elim conjE)
  apply (frule sym_refs_ko_atD[where ko="Notification x" for x, rotated])
   apply (simp add: obj_at_def, elim conjE)
  apply (erule delta_sym_refs)
   apply (fastforce simp: obj_at_def refs_of_ntfn_def refs_of_simps split: if_splits)
  by ((fastforce split: if_split_asm ntfn.splits dest!: symreftype_inverse'
        simp: obj_at_def get_refs_def2 refs_of_ntfn_def ntfn_q_refs_of_def image_iff refs_of_simps)+)

lemmas is_schedulable_inv[wp] = is_schedulable_wp[of "\<lambda>_. P" for P]

declare reprogram_timer_update_arch.state_refs_update[simp]

crunches sched_context_resume, test_possible_switch_to, tcb_release_remove, postpone
  for aligned[wp]: pspace_aligned
  and distinct[wp]: pspace_distinct
  and iflive[wp]: if_live_then_nonz_cap
  and typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  and sc_at[wp]: "sc_at sc_ptr"
  and cte_wp_at[wp]: "cte_wp_at P c"
  and irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"
  and it[wp]: "\<lambda>s. P (idle_thread s)"
  and no_cdt[wp]: "\<lambda>s. P (cdt s)"
  and no_revokable[wp]: "\<lambda>s. P (is_original_cap s)"
  and valid_irq_states[wp]: valid_irq_states
  and pspace_in_kernel_window[wp]: pspace_in_kernel_window
  and pspace_respects_device_region[wp]: pspace_respects_device_region
  and cur_tcb[wp]: cur_tcb
  and interrupt_states[wp]: "\<lambda>s. P (interrupt_states s)"
  and valid_mdb[wp]: valid_mdb
  and valid_objs[wp]: valid_objs
  and zombies[wp]: zombies_final
  and valid_irq_handlers[wp]: valid_irq_handlers
  and valid_ioc[wp]: valid_ioc
  and cap_refs_in_kernel_window[wp]: cap_refs_in_kernel_window
  and cap_refs_respects_device_region[wp]: cap_refs_respects_device_region
  and valid_idle[wp]: valid_idle
  and only_idle[wp]: only_idle
  and valid_arch_state[wp]: valid_arch_state
  and ifunsafe[wp]: if_unsafe_then_cap
  and valid_global_objs[wp]: valid_global_objs
  and valid_global_vspace_mappings[wp]: valid_global_vspace_mappings
  and valid_arch_caps[wp]: valid_arch_caps
  and valid_kernel_mappings[wp]: valid_kernel_mappings
  and equal_kernel_mappings[wp]: equal_kernel_mappings
  and valid_vspace_objs[wp]: valid_vspace_objs
  and valid_machine_state[wp]: valid_machine_state
  and valid_global_refs[wp]: valid_global_refs
  and valid_asid_map[wp]: valid_asid_map
  and state_hyp_refs_of[wp]: "\<lambda>s. P (state_hyp_refs_of s)"
  and state_refs_of[wp]: "\<lambda>s. P (state_refs_of s)"
  and caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"
  and ex_cap[wp]: "ex_nonz_cap_to p"
  (wp: crunch_wps)

lemma ssc_sc_tcb_update_bound_sc_tcb_at[wp]:
  "\<lbrace>bound_sc_tcb_at P t\<rbrace> set_sc_obj_ref sc_tcb_update scp tcb \<lbrace>\<lambda>rv. bound_sc_tcb_at P t\<rbrace>"
  by (wpsimp simp: set_sc_obj_ref_def)

lemma ssc_sc_yf_update_bound_sc_tcb_at[wp]:
  "\<lbrace>bound_sc_tcb_at P t\<rbrace> set_sc_obj_ref sc_yield_from_update scp tcb \<lbrace>\<lambda>rv. bound_sc_tcb_at P t\<rbrace>"
  by (wpsimp simp: set_sc_obj_ref_def)

lemma set_tcb_yt_update_bound_sc_tcb_at[wp]:
  "\<lbrace>bound_sc_tcb_at P t\<rbrace> set_tcb_obj_ref tcb_yield_to_update scp tcb \<lbrace>\<lambda>rv. bound_sc_tcb_at P t\<rbrace>"
  by (wpsimp simp: set_tcb_obj_ref_def set_object_def pred_tcb_at_def obj_at_def get_tcb_rev)

lemma set_tcb_queue_valid_replies[wp]:
  "set_tcb_queue d prio queue \<lbrace> valid_replies_pred P \<rbrace>"
  by (wpsimp simp: set_tcb_queue_def)

crunches sched_context_bind_tcb, update_sk_obj_ref
  for arch_state[wp]: "\<lambda>s. P (arch_state s)"
  (wp: crunch_wps)

crunches get_tcb_queue, get_sc_time, get_sc_obj_ref
  for inv[wp]: "P"
  (wp: hoare_drop_imps)

lemma tcb_sched_action_valid_replies[wp]:
  "tcb_sched_action act tcb_ptr \<lbrace> valid_replies_pred P \<rbrace>"
  by (wpsimp simp: tcb_sched_action_def)

lemma reschedule_required_valid_replies[wp]:
  "reschedule_required \<lbrace> valid_replies_pred P \<rbrace>"
  by (wpsimp simp: reschedule_required_def wp: hoare_drop_imps)

lemma possible_switch_to_valid_replies[wp]:
  "possible_switch_to tcb_ptr \<lbrace> valid_replies_pred P \<rbrace>"
  by (wpsimp simp: possible_switch_to_def)

lemma test_possible_switch_to_valid_replies[wp]:
  "test_possible_switch_to tcb_ptr \<lbrace> valid_replies_pred P \<rbrace>"
  by (wpsimp simp: test_possible_switch_to_def)

lemma tcb_release_enqueue_valid_replies[wp]:
  "tcb_release_enqueue tcb_ptr \<lbrace> valid_replies_pred P \<rbrace>"
  by (wpsimp simp: tcb_release_enqueue_def wp: mapM_wp')

lemma postpone_valid_replies[wp]:
  "postpone sc_ptr \<lbrace> valid_replies_pred P \<rbrace>"
  by (wpsimp simp: postpone_def wp: hoare_drop_imps)

lemma sched_context_resume_valid_replies[wp]:
  "sched_context_resume sc_ptr \<lbrace> valid_replies_pred P \<rbrace>"
  by (wpsimp simp: sched_context_resume_def wp: hoare_drop_imps)

lemma sched_context_bind_tcb_invs[wp]:
  "\<lbrace>invs
    and bound_sc_tcb_at ((=) None) tcb and ex_nonz_cap_to tcb
    and sc_tcb_sc_at ((=) None) sc and ex_nonz_cap_to sc\<rbrace>
      sched_context_bind_tcb sc tcb \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wpsimp simp: sched_context_bind_tcb_def invs_def valid_state_def
      valid_pspace_def set_sc_obj_ref_def
      wp: valid_irq_node_typ obj_set_prop_at get_sched_context_wp ssc_refs_of_Some
          update_sched_context_valid_objs_same valid_ioports_lift
          update_sched_context_iflive_update
          update_sched_context_refs_of_update)
  apply (clarsimp simp: obj_at_def is_sc_obj_def pred_tcb_at_def refs_of_sc_def get_refs_def2)
  apply (clarsimp simp: sc_tcb_sc_at_def obj_at_def)
  apply safe
     apply (erule (1) valid_objsE)
     apply (clarsimp simp: valid_obj_def valid_sched_context_def obj_at_def is_tcb)
    apply (frule valid_objs_valid_sched_context_size, fastforce)
    apply assumption
   apply (erule delta_sym_refs)
    apply (clarsimp simp: state_refs_of_def obj_at_def refs_of_sc_def split: if_splits)
   apply (clarsimp simp: state_refs_of_def refs_of_tcb_def get_refs_def2 image_iff
                         tcb_st_refs_of_def sc_tcb_sc_at_def obj_at_def
                  dest!: symreftype_inverse' split: if_splits)
    apply (clarsimp split: thread_state.split_asm if_split_asm)
   apply (clarsimp simp: refs_of_sc_def get_refs_def2 image_iff)
  apply (clarsimp simp: idle_no_ex_cap)
  done

lemma sched_context_unbind_valid_replies[wp]:
  "tcb_release_remove tcb_ptr \<lbrace> valid_replies_pred P \<rbrace>"
  by (wpsimp simp: tcb_release_remove_def)

lemma sched_context_unbind_tcb_invs[wp]:
  notes refs_of_simps[simp del]
  shows "\<lbrace>invs\<rbrace> sched_context_unbind_tcb sc_ptr \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wpsimp simp: sched_context_unbind_tcb_def invs_def valid_state_def
                      valid_pspace_def sc_tcb_sc_at_def obj_at_def is_tcb
          simp_del: fun_upd_apply
          wp: valid_irq_node_typ obj_set_prop_at get_sched_context_wp valid_ioports_lift)
  apply (rename_tac sc n tptr)
  apply (frule sym_refs_ko_atD[where p=sc_ptr, rotated])
   apply (simp add: obj_at_def, elim conjE)
  apply (simp only: refs_of_simps get_refs_def2)
  apply (case_tac "sc_ptr = tptr")
   apply (drule_tac x="(sc_ptr, SCTcb)" in bspec, simp)
   apply (fastforce dest:obj_at_state_refs_ofD)
  apply (drule_tac x="(tptr, SCTcb)" in bspec, simp)
  apply (clarsimp simp: obj_at_def)
  apply (case_tac ko;
         clarsimp simp: refs_of_simps refs_of_defs get_refs_def2 image_iff
                        ntfn_q_refs_of_def ep_q_refs_of_def
                  split: ntfn.split_asm endpoint.split_asm)
  apply (rename_tac tcb)
  apply (rule conjI)
   apply (erule delta_sym_refs)
    apply clarsimp
    apply (simp split: if_split_asm)
    apply (fastforce simp: get_refs_def2 image_iff refs_of_def refs_of_sc_def
                    dest!: symreftype_inverse')
   apply clarsimp
   apply (simp split: if_split_asm)
    apply (fastforce simp: get_refs_def2 image_iff refs_of_def refs_of_sc_def
                    dest!: symreftype_inverse')
   apply (intro conjI; clarsimp simp: state_refs_of_def refs_of_rev)
  apply (drule_tac p=tptr in if_live_then_nonz_capD2, simp, simp add: live_def)
  apply (fastforce dest: idle_no_ex_cap)
  done

lemma sched_context_unbind_all_tcbs_invs[wp]:
  "\<lbrace>invs\<rbrace> sched_context_unbind_all_tcbs sc_ptr \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (wpsimp simp: sched_context_unbind_all_tcbs_def sc_tcb_sc_at_def obj_at_def
       wp: get_sched_context_wp)

lemma set_reply_refs_of:
  "\<lbrace>\<lambda>s. P ((state_refs_of s) (rptr := refs_of_reply reply))\<rbrace>
     set_reply rptr reply
   \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  by (wp; fastforce simp: state_refs_of_def refs_of_reply_def
          elim!: rsubst[where P=P] split: option.splits)

lemma get_sc_replies_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> liftM sc_replies (get_sched_context scp) \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  by (wpsimp simp: obj_at_def)

(* FIXME: remove
lemma mapM_x_set_reply_sc_refs_of:
  notes refs_of_simps[simp del]
  shows
  "\<lbrace>\<lambda>s. P (foldl (\<lambda>f r. f(r:= (state_refs_of s r - {x \<in> state_refs_of s r. snd x = ReplySchedContext}))) (state_refs_of s) replies)\<rbrace>
       mapM_x (\<lambda>r. set_reply_obj_ref reply_sc_update r None) replies
   \<lbrace>\<lambda>rv s. P ((state_refs_of s))\<rbrace>"
  apply (induct replies)
   apply (clarsimp simp: mapM_x_def sequence_x_def)
  apply (clarsimp simp: mapM_x_Cons simp del: fun_upd_apply)
  apply (rule hoare_seq_ext)
   apply assumption
  apply (wp set_reply_sc_refs_of)
  apply (clarsimp elim!: rsubst[where P=P] split del: if_split simp del: fun_upd_apply)
proof -
  fix a :: "32 word" and repliesa :: "32 word list" and s :: "'a state"
  have "\<forall>f w. f(w := ((state_refs_of s)
                    (a := state_refs_of s a - {p \<in> state_refs_of s a. snd p = ReplySchedContext})) w
           - {p \<in> ((state_refs_of s) (a := state_refs_of s a - {p \<in> state_refs_of s a. snd p = ReplySchedContext})) w.
            snd p = ReplySchedContext}) = f(w := state_refs_of s w - {p \<in> state_refs_of s w. snd p = ReplySchedContext})"
    by (simp add: Collect_Diff_restrict_simp)
  then show "foldl (\<lambda>f w. f (w := state_refs_of s w - {p \<in> state_refs_of s w. snd p = ReplySchedContext})) ((state_refs_of s) (a := state_refs_of s a - {p \<in> state_refs_of s a. snd p = ReplySchedContext})) repliesa = foldl (\<lambda>f w. f (w := ((state_refs_of s) (a := state_refs_of s a - {p \<in> state_refs_of s a. snd p = ReplySchedContext})) w - {p \<in> ((state_refs_of s) (a := state_refs_of s a - {p \<in> state_refs_of s a. snd p = ReplySchedContext})) w. snd p = ReplySchedContext})) ((state_refs_of s) (a := state_refs_of s a - {p \<in> state_refs_of s a. snd p = ReplySchedContext})) repliesa"
    by presburger
qed
*)

definition if_Some :: "'a option \<Rightarrow> 'b \<Rightarrow> 'b set"
  where
  "if_Some opt r \<equiv> case opt of None \<Rightarrow> {} | _ \<Rightarrow> {r}"

lemmas if_Some_simps[simp] = if_Some_def [split_simps option.split]

global_interpretation set_reply: non_sc_op "set_reply r reply"
  by unfold_locales (wpsimp wp: set_simple_ko_wps simp: obj_at_def is_reply sc_at_pred_n_def)

lemma set_reply_valid_replies[wp]:
  "set_reply r reply \<lbrace> valid_replies_pred P \<rbrace>"
  by (wp valid_replies_lift)

lemma set_reply_obj_ref_valid_replies[wp]:
  "set_reply_obj_ref f r v \<lbrace> valid_replies_pred P \<rbrace>"
  by (wpsimp simp: update_sk_obj_ref_def wp: set_reply_valid_replies)

lemma replies_with_sc_upd_replies_subset:
  assumes "set rs \<subseteq> {r. (r, sc_ptr) \<in> rs_with_sc}"
  shows "replies_with_sc_upd_replies rs sc_ptr rs_with_sc \<subseteq> rs_with_sc"
  using assms by (auto simp: replies_with_sc_upd_replies_def)

lemma replies_with_sc_upd_replies_subset_valid_replies:
  assumes rep: "valid_replies rs_with_sc rs_blocked"
  assumes sub: "set rs \<subseteq> {r. (r,sc_ptr) \<in> rs_with_sc}"
  shows "valid_replies (replies_with_sc_upd_replies rs sc_ptr rs_with_sc) rs_blocked"
proof -
  note subs = replies_with_sc_upd_replies_subset[OF sub]
  note subf = subs[THEN image_mono[where f=fst], THEN subset_trans]
  show ?thesis using rep by (clarsimp simp: valid_replies_def subf inj_on_subset[OF _ subs])
qed

lemma sc_replies_sc_at_subset_replies_with_sc:
  assumes "sc_replies_sc_at (\<lambda>rs'. set rs \<subseteq> set rs') sc_ptr s"
  shows "set rs \<subseteq> {r. (r, sc_ptr) \<in> replies_with_sc s}"
  using assms by (auto simp: replies_with_sc_def sc_replies_sc_at_def obj_at_def)

lemmas replies_with_sc_upd_replies_subset' =
  replies_with_sc_upd_replies_subset[OF sc_replies_sc_at_subset_replies_with_sc]

lemmas replies_with_sc_upd_replies_subset_valid_replies' =
  replies_with_sc_upd_replies_subset_valid_replies[OF _ sc_replies_sc_at_subset_replies_with_sc]

lemmas replies_with_sc_upd_replies_nil =
  replies_with_sc_upd_replies_subset[of "[]", simplified]

lemmas replies_with_sc_upd_replies_nil_valid_replies =
  replies_with_sc_upd_replies_subset_valid_replies[where rs="[]", simplified]

lemma set_sc_replies_nil_valid_replies[wp]:
  "set_sc_obj_ref sc_replies_update sc_ptr [] \<lbrace> valid_replies_pred valid_replies \<rbrace>"
  by (wpsimp wp: set_sc_replies_valid_replies
           simp: replies_with_sc_upd_replies_subset_valid_replies)

(* FIXME: move to Invariants_AI *)
lemma in_state_refs_of_iff:
  "r \<in> state_refs_of s p \<longleftrightarrow> obj_at (\<lambda>obj. r \<in> refs_of obj) p s"
  by (auto simp: state_refs_of_def obj_at_def split: option.splits)

lemma sched_context_unbind_reply_invs[wp]:
  "\<lbrace>invs\<rbrace> sched_context_unbind_reply sc_ptr \<lbrace>\<lambda>rv. invs\<rbrace>"
  supply fun_upd_apply[simp del]
  apply (wpsimp wp: valid_irq_node_typ hoare_vcg_conj_lift valid_ioports_lift
              simp: sched_context_unbind_reply_def invs_def valid_state_def valid_pspace_def)
  apply (rule_tac V="sc_ptr \<noteq> hd (sc_replies sc)" in revcut_rl)
   apply (case_tac "sc_replies sc"; clarsimp)
   apply (clarsimp simp: obj_at_def)
   apply (erule (1) pspace_valid_objsE)
   apply (clarsimp simp: valid_obj_def valid_sched_context_def obj_at_def is_reply)
  supply fun_upd_apply[simp]
  apply (clarsimp cong: conj_cong)
  apply (rule_tac rfs'="state_refs_of s" in delta_sym_refs
         ; clarsimp simp: obj_at_def split: if_splits
         ; clarsimp simp: in_state_refs_of_iff obj_at_def get_refs_def2 refs_of_rev
                   split: option.splits)
  apply (rename_tac s sc n y reply sc' rs' n')
  apply (case_tac "sc_replies sc"; case_tac "sc_replies sc'"; clarsimp)
  apply (rename_tac s sc n sc_ptr' reply sc' rs' n' r rs)
  by (frule_tac x=sc_ptr and y=r and tp=ReplySchedContext in sym_refsE
      ; clarsimp simp: in_state_refs_of_iff obj_at_def get_refs_def2)

text {* more invs rules *}

crunches postpone
  for valid_irq_node[wp]: valid_irq_node
  (wp: crunch_wps)

lemma postpone_invs[wp]:
  "postpone t \<lbrace>invs\<rbrace>"
  by (wpsimp simp: invs_def valid_state_def valid_pspace_def wp: valid_ioports_lift)

lemma sched_context_resume_invs[wp]:
  "\<lbrace>invs\<rbrace> sched_context_resume scptr \<lbrace>\<lambda>_. invs\<rbrace>"
  by (wpsimp simp: sched_context_resume_def get_tcb_queue_def get_sc_obj_ref_def is_schedulable_def
       wp: hoare_vcg_if_lift2 get_refills_wp hoare_vcg_all_lift get_sched_context_wp thread_get_wp)

lemma refill_add_tail_invs[wp]:
  "\<lbrace>invs\<rbrace> refill_add_tail sc_ptr refills \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (wpsimp simp: refill_add_tail_def wp: get_sched_context_wp get_refills_wp)

lemma maybe_add_empty_tail_invs[wp]:
  "\<lbrace>invs\<rbrace> maybe_add_empty_tail sc_ptr \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (wpsimp simp: maybe_add_empty_tail_def)

lemma set_sc_othres_invs:
  "\<lbrace>invs and (\<lambda>s. (\<exists>n. ko_at (SchedContext sc n) p s))\<rbrace>
      set_sched_context p
          (sc\<lparr>sc_period := period,
              sc_refills := r#refills,
              sc_refill_max := max_refills\<rparr>) \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def obj_at_def
      simp_del: fun_upd_apply wp: valid_ioports_lift set_sched_context_valid_replies)
  apply safe
     apply (drule valid_objs_valid_sched_context, fastforce)
     apply (clarsimp simp: valid_sched_context_def)
    apply (drule_tac p=p in if_live_then_nonz_capD2, simp)
     apply (clarsimp simp: live_def live_sc_def, assumption)
   apply (erule replies_with_sc_upd_replies_subset_valid_replies')
   apply (clarsimp simp: sc_replies_sc_at_def obj_at_def)
  by (clarsimp simp: state_refs_of_def refs_of_def fun_upd_idem)

lemma update_sc_othres_invs:
  "\<lbrace>invs\<rbrace>
      update_sched_context p
          (\<lambda>sc. sc\<lparr>sc_period := period,
              sc_refills := r#refills,
              sc_refill_max := max_refills\<rparr>) \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def obj_at_def
                  wp: update_sched_context_valid_objs_same valid_irq_node_typ
                      update_sched_context_iflive_same
                      update_sched_context_refs_of_same
                      update_sc_but_not_sc_replies_valid_replies'
            simp_del: fun_upd_apply)
  by (clarsimp simp: valid_sched_context_def live_sc_def)

lemma refill_new_invs[wp]:
  "\<lbrace>invs\<rbrace> refill_new sc_ptr max_refills budget period \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (wpsimp simp: refill_new_def wp: get_sched_context_wp update_sc_othres_invs)

lemma set_consumed_invs[wp]:
  "\<lbrace>invs\<rbrace> set_consumed scp args \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (wpsimp simp: set_consumed_def)

(* FIXME: move *)
lemma invs_ready_queues_update[simp]:
  "invs (ready_queues_update f s) = invs s"
  by (simp add: invs_def valid_state_def)

lemma invs_release_queue_update[simp]:
  "invs (release_queue_update f s) = invs s"
  by (simp add: invs_def valid_state_def)

(* FIXME: move *)
lemma invs_scheduler_action_update[simp]:
  "invs (scheduler_action_update f s) = invs s"
  by (simp add: invs_def valid_state_def valid_irq_states_def)

lemma tcb_sched_action_invs[wp]:
  "\<lbrace>invs\<rbrace> tcb_sched_action action thread \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (wpsimp simp: tcb_sched_action_def set_tcb_queue_def get_tcb_queue_def
             wp: hoare_drop_imps hoare_vcg_all_lift)

lemma tcb_release_remove_invs[wp]:
  "\<lbrace>invs\<rbrace> tcb_release_remove thread \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (wpsimp simp: tcb_release_remove_def tcb_sched_dequeue_def
             wp: hoare_drop_imps hoare_vcg_all_lift)

lemma set_scheduler_action_invs[wp]:
  "\<lbrace>invs\<rbrace> set_scheduler_action action \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (wpsimp simp: set_scheduler_action_def)

lemma reschedule_required_invs[wp]:
  "\<lbrace>invs\<rbrace> reschedule_required \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (wpsimp simp: reschedule_required_def wp: hoare_drop_imps hoare_vcg_all_lift)

lemma possible_switch_to_invs[wp]:
  "\<lbrace>invs\<rbrace> possible_switch_to target \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (wpsimp simp: possible_switch_to_def)

lemma ssc_sc_yf_update_bound_yt_tcb_at[wp]:
  "\<lbrace>bound_yt_tcb_at P t\<rbrace> set_sc_obj_ref sc_yield_from_update scp tcb \<lbrace>\<lambda>rv. bound_yt_tcb_at P t\<rbrace>"
  by (wpsimp simp: set_sc_obj_ref_def)

lemma set_sched_context_ex_cap_cur_thread [wp]:
  "\<lbrace>\<lambda>s. ex_nonz_cap_to (cur_thread s) s\<rbrace>
     set_sched_context ptr val \<lbrace>\<lambda>rv s. ex_nonz_cap_to (cur_thread s) s\<rbrace>"
  apply (wpsimp simp: set_sched_context_def obj_at_def
          wp: set_object_wp get_object_wp ex_nonz_cap_to_pres)
  apply (rule ex_cap_to_after_update[simplified fun_upd_apply[symmetric]], simp)
  by (clarsimp simp: obj_at_def)

lemma update_sched_context_ex_cap_cur_thread [wp]:
  "\<lbrace>\<lambda>s. ex_nonz_cap_to (cur_thread s) s\<rbrace>
     update_sched_context ptr f \<lbrace>\<lambda>rv s. ex_nonz_cap_to (cur_thread s) s\<rbrace>"
  apply (wpsimp simp: update_sched_context_def obj_at_def
          wp: set_object_wp get_object_wp ex_nonz_cap_to_pres)
  apply (rule ex_cap_to_after_update[simplified fun_upd_apply[symmetric]], simp)
  by (clarsimp simp: obj_at_def)

(* FIXME Move *)
lemma ex_nonz_cap_to_reprogram_timer_update[iff]:
  "ex_nonz_cap_to w (reprogram_timer_update f s) = ex_nonz_cap_to w s"
   by (simp add: ex_nonz_cap_to_def)

crunches refill_unblock_check
 for aligned[wp]: pspace_aligned
 and distinct[wp]: pspace_distinct
 and iflive[wp]: if_live_then_nonz_cap
 and sc_at[wp]: "sc_at sc_ptr"
 and tcb_at[wp]: "tcb_at sc_ptr"
 and cte_wp_at[wp]: "cte_wp_at P c"
 and interrupt_irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"
 and caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"
 and no_cdt[wp]: "\<lambda>s. P (cdt s)"
 and state_refs_of[wp]: "\<lambda>s. P (state_refs_of s)"
 and cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
 and state_hyp_refs_of[wp]: "\<lambda>s. P (state_hyp_refs_of s)"
 and no_revokable[wp]: "\<lambda>s. P (is_original_cap s)"
 and valid_idle[wp]: valid_idle
 and valid_irq_handlers[wp]: valid_irq_handlers
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
 and cap_refs_in_kernel_window[wp]: "cap_refs_in_kernel_window"
 and cap_refs_respects_device_region[wp]: "cap_refs_respects_device_region"
 and pspace_respects_device_region[wp]: "pspace_respects_device_region"
 and cur_tcb[wp]: "cur_tcb"
 and valid_mdb[wp]: "valid_mdb"
 and valid_ioc[wp]: "valid_ioc"
 and ex_nonz_cap_to[wp]: "ex_nonz_cap_to p"
 and typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  (simp: Let_def wp: hoare_drop_imps hoare_vcg_if_lift2 zipWithM_x_inv ignore: set_mrs)

lemma refill_unblock_check_tcb_at_ct[wp]:
    "\<lbrace>\<lambda>s. tcb_at (cur_thread s) s\<rbrace> refill_unblock_check scp
       \<lbrace>\<lambda>rv s. tcb_at (cur_thread s) s\<rbrace>"
  by (wpsimp simp: refill_unblock_check_def set_refills_def is_tcb
      update_sched_context_def is_round_robin_def pred_tcb_at_def obj_at_def
       wp: hoare_vcg_if_lift2 set_object_wp get_object_wp get_sched_context_wp
           hoare_vcg_all_lift get_refills_wp)

lemma set_sc_obj_ref_tcb_at_ct[wp]:
    "\<lbrace>\<lambda>s. tcb_at (cur_thread s) s\<rbrace> set_sc_obj_ref f scp v
       \<lbrace>\<lambda>rv s. tcb_at (cur_thread s) s\<rbrace>"
  by (wpsimp simp: set_sc_obj_ref_def set_refills_def is_tcb
      update_sched_context_def is_round_robin_def pred_tcb_at_def obj_at_def
       wp: hoare_vcg_if_lift2 set_object_wp get_object_wp get_sched_context_wp
           hoare_vcg_all_lift get_refills_wp)

lemma refill_unblock_check_sc_tcb_at_ct:
    "\<lbrace>\<lambda>s. bound_sc_tcb_at ((=) None) (cur_thread s) s\<rbrace> refill_unblock_check scp
       \<lbrace>\<lambda>rv s. bound_sc_tcb_at ((=) None) (cur_thread s) s\<rbrace>"
  by (wpsimp simp: refill_unblock_check_def set_refills_def
      update_sched_context_def is_round_robin_def pred_tcb_at_def obj_at_def
       wp: hoare_vcg_if_lift2 set_object_wp get_object_wp get_sched_context_wp
           hoare_vcg_all_lift get_refills_wp)

(* FIXME Move *)
lemma ex_nonz_cap_to_reprogram_timer_update_ct:
  "ex_nonz_cap_to (cur_thread s) (reprogram_timer_update f s)
      = ex_nonz_cap_to (cur_thread s) s"
   by (simp add: ex_nonz_cap_to_def)

lemma refill_unblock_check_ex_nonz_cap_to_ct[wp]:
    "\<lbrace>\<lambda>s. ex_nonz_cap_to (cur_thread s) s\<rbrace> refill_unblock_check scp
       \<lbrace>\<lambda>rv s. ex_nonz_cap_to (cur_thread s) s\<rbrace>"
  by (wpsimp simp: refill_unblock_check_def set_refills_def is_round_robin_def
      wp: get_sched_context_wp get_refills_wp)

lemma refill_unblock_check_zombies[wp]:
  "\<lbrace>zombies_final\<rbrace> refill_unblock_check scp \<lbrace>\<lambda>_. zombies_final\<rbrace>"
  by (wpsimp simp: refill_unblock_check_def is_round_robin_def
        wp: get_refills_wp hoare_vcg_if_lift2 get_sched_context_wp)

lemma refill_unblock_check_state_refs_of_ct[wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of s) (cur_thread s)\<rbrace>
     refill_unblock_check scp \<lbrace>\<lambda>_ s. P (state_refs_of s) (cur_thread s)\<rbrace>"
  apply (wpsimp simp: refill_unblock_check_def is_round_robin_def set_refills_def
            update_sched_context_def set_object_def
        wp: get_refills_wp hoare_vcg_if_lift2 get_object_wp get_sched_context_wp)
  by (clarsimp simp: state_refs_of_def get_refs_def2 obj_at_def
            simp del: fun_upd_apply
            elim!: rsubst[where P="\<lambda>x. P x (cur_thread s)" for s] intro!: ext)

lemma refill_unblock_check_it_ct[wp]:
  "\<lbrace>\<lambda>s. P (idle_thread s) (cur_thread s)\<rbrace>
    refill_unblock_check scp \<lbrace>\<lambda>_ s. P (idle_thread s) (cur_thread s)\<rbrace>"
  by (wpsimp simp: refill_unblock_check_def is_round_robin_def set_refills_def
            update_sched_context_def set_object_def
        wp: get_refills_wp hoare_vcg_if_lift2 get_object_wp get_sched_context_wp)

lemma refill_capacity_sp:
  "\<lbrace>\<lambda>s. P s \<and> (\<exists>n. ko_at (SchedContext sc n) sc_ptr s)\<rbrace>
     refill_capacity sc_ptr usage \<lbrace> \<lambda>rv. K( rv = refills_capacity usage (sc_refills sc)) and P \<rbrace>"
  apply (clarsimp simp: refill_capacity_def)
  apply (rule hoare_seq_ext[OF _ get_refills_sp])
  apply wpsimp
  by (clarsimp simp: obj_at_def refills_capacity_def)


(* sched_context_yield_to is moved to the start of SchedContextInv_AI
because it needs to be after Ipc_AI *)

end