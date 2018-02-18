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
imports RealTime_AI
begin

(* FIXME - Move Invariants_AI *)
lemma invs_exst [iff]:
  "invs (trans_state f s) = invs s"
  by (simp add: invs_def valid_state_def)

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
  apply (wpsimp simp: set_refills_def valid_objs_def valid_obj_def
                 wp: get_sched_context_wp)
  apply (drule_tac x=sc_ptr in bspec)
  apply (fastforce simp: obj_at_def)
  by (auto simp: obj_at_def valid_sched_context_def)

crunches commit_domain_time,set_next_interrupt,set_refills,refill_split_check
  for consumed_time[wp]: "\<lambda>s. P (consumed_time s)"
  and reprogram_timer[wp]: "\<lambda>s. P (reprogram_timer s)"
  and cur_sc[wp]: "\<lambda>s. P (cur_sc s)"
  and cur_time[wp]: "\<lambda>s. P (cur_time s)"
  and cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  and cur_sc_cur_thread[wp]: "\<lambda>s. P (cur_sc s) (cur_thread s)"
  (wp: crunch_wps simp: Let_def)

crunch reprogram_timer[wp]: commit_time "\<lambda>s. P (reprogram_timer s)"
  (wp: crunch_wps hoare_vcg_if_lift2 ignore: commit_domain_time)

lemma refill_unblock_check_reprogram_timer[wp]:
  "\<lbrace>\<lambda>s. \<forall>b. P b\<rbrace> refill_unblock_check param_a \<lbrace>\<lambda>_ s. P (reprogram_timer s)\<rbrace>"
  by (wpsimp simp: refill_unblock_check_def wp: crunch_wps hoare_vcg_if_lift2)

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
  "\<lbrace>valid_objs and sc_at sc_ptr\<rbrace> refill_unblock_check sc_ptr \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  apply (rule hoare_assume_pre)
  apply (clarsimp simp: pred_def obj_at_def is_sc_obj_def)
  apply (case_tac ko; clarsimp simp:)
  apply (rename_tac sc n)
  apply (frule (1) valid_sc_valid_refills[rotated])
  apply (wpsimp wp: get_sched_context_wp get_refills_wp set_refills_valid_objs
      hoare_vcg_conj_lift hoare_drop_imp hoare_vcg_if_lift2
      simp: pred_conj_def refill_unblock_check_def obj_at_def is_sc_obj_def
      split: kernel_object.splits)
  apply (frule_tac sc=sca in valid_sc_valid_refills[rotated], simp)
  apply (case_tac "sc_refills sca", simp)
  apply simp
  apply (auto simp: refills_merge_valid[simplified])
  done

lemma refill_split_check_valid_objs[wp]:
  "\<lbrace>valid_objs and sc_at sc_ptr\<rbrace> refill_split_check sc_ptr usage \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  apply (rule hoare_assume_pre)
  apply (clarsimp simp: pred_def obj_at_def is_sc_obj_def)
  apply (case_tac ko; clarsimp simp:)
  apply (rename_tac sc n)
  apply (frule (1) valid_sc_valid_refills[rotated])
  apply (wpsimp wp: get_sched_context_wp get_refills_sp set_refills_valid_objs
      hoare_vcg_conj_lift hoare_drop_imp hoare_vcg_if_lift2
      simp: pred_conj_def refill_split_check_def obj_at_def is_sc_obj_def Let_def
      split: kernel_object.splits split_del: if_split)
  apply (frule_tac sc=sca in valid_sc_valid_refills[rotated], simp)
  apply (case_tac "sc_refills sca", simp)
  apply (auto simp: refills_merge_valid[simplified])
  done

(* move to KHeap_AI *)
crunch valid_irq_states[wp]: update_sched_context "valid_irq_states"
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

lemma refs_of_sched_context_sc_consumed_update[iff]:
  "refs_of (SchedContext (sc_consumed_update f sc) n) = refs_of (SchedContext sc n)"
  by simp

lemma refs_of_sched_context_sc_refills_update[iff]:
  "refs_of (SchedContext (sc_refills_update f sc) n) = refs_of (SchedContext sc n)"
  by simp

lemma sc_consumed_update_iflive [wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap s \<and> (live_sc sc \<longrightarrow> ex_nonz_cap_to ptr s)\<rbrace>
     update_sched_context ptr (sc_consumed_update f sc) \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  by (wpsimp simp: live_sc_def)

lemma sc_refills_update_iflive [wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap s \<and> (live_sc sc \<longrightarrow> ex_nonz_cap_to ptr s)\<rbrace>
     update_sched_context ptr (sc_refills_update f sc) \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  by (wpsimp simp: live_sc_def)

lemma set_refills_iflive[wp]:
  "\<lbrace>if_live_then_nonz_cap\<rbrace> set_refills ptr param_b \<lbrace>\<lambda>_. if_live_then_nonz_cap\<rbrace> "
  apply (wpsimp simp: set_refills_def get_sched_context_def wp: hoare_vcg_all_lift get_object_wp)
  apply (clarsimp simp: if_live_then_nonz_cap_def, drule_tac x=ptr in spec)
  apply (simp add: obj_at_def live_sc_def live_def)
  done

lemma valid_sc_sc_consumed_update[iff]:
  "valid_sched_context (sc_consumed_update f sc) = valid_sched_context sc"
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
 by (wpsimp wp: valid_sc_typ update_sched_context_typ_at simp: set_refills_def)

lemma set_refills_refs_of [wp]:
 "\<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace>
    set_refills ptr refills
  \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (wpsimp simp: set_refills_def get_sched_context_def
          simp_del: refs_of_defs fun_upd_apply
          wp: get_object_wp)
  apply (clarsimp simp: state_refs_of_def ext obj_at_def elim!: rsubst[where P = P])
  done

lemma set_refills_hyp_refs_of[wp]:
  "\<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace> set_refills ptr refills  \<lbrace>\<lambda>rv s. P (state_hyp_refs_of s)\<rbrace>"
  by (wpsimp simp: set_refills_def)

lemma set_refills_invs[wp]:
  "\<lbrace>invs and K (length refills \<ge> 1)\<rbrace> set_refills ptr refills \<lbrace>\<lambda>_. invs\<rbrace> "
  apply (wpsimp simp: set_refills_def invs_def valid_state_def valid_pspace_def
                wp: valid_irq_node_typ get_sched_context_wp)
  apply (rule conjI)
   apply (simp add: valid_objs_def valid_obj_def obj_at_def)
   apply (drule_tac x=ptr in bspec, fastforce)
    apply (clarsimp simp: valid_sched_context_def)
  apply (rule conjI)
   apply (simp add: if_live_then_nonz_cap_def)
   apply (drule_tac x=ptr in spec)
   apply (simp add: obj_at_def live_def live_sc_def)
  apply (frule (1) sym_refs_obj_atD[rotated])
  apply clarsimp
  apply (drule sym)
  apply (simp only: if_fun_simp)
  done

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
  by (wpsimp simp: refill_split_check_def Let_def split_del: if_splits wp: hoare_drop_imp)

lemma refill_split_check_ex_cap[wp]:
  "\<lbrace>ex_nonz_cap_to p\<rbrace> refill_split_check p u \<lbrace>\<lambda>rv. ex_nonz_cap_to p\<rbrace>"
  by (wp ex_nonz_cap_to_pres)

lemma refill_split_check_mdb [wp]:
  "\<lbrace>valid_mdb\<rbrace> refill_split_check p u  \<lbrace>\<lambda>r. valid_mdb\<rbrace>"
  by (wpsimp wp: valid_mdb_lift)

lemma refill_split_check_hyp_refs_of[wp]:
  "\<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace> refill_split_check p u \<lbrace>\<lambda>rv s. P (state_hyp_refs_of s)\<rbrace>"
  by (wpsimp simp: refill_split_check_def Let_def split_del: if_splits wp: hoare_drop_imp)

lemma refill_split_check_refs_of[wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace> refill_split_check p u \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  by (wpsimp simp: refill_split_check_def Let_def split_del: if_splits wp: hoare_drop_imp)

lemma refill_split_check_invs[wp]: "\<lbrace>invs\<rbrace> refill_split_check p u \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wpsimp simp: refill_split_check_def Let_def split_del: if_splits
             wp: hoare_drop_imp get_sched_context_wp)
  apply simp
  done

declare refs_of_defs[simp del]
lemma refill_split_check_valid_sc[wp]:
   "\<lbrace>valid_sched_context sc\<rbrace> refill_split_check p u \<lbrace>\<lambda>rv. valid_sched_context sc\<rbrace>"
 by (wpsimp simp: refill_split_check_def Let_def split_del: if_splits
            wp: hoare_drop_imp)

lemma update_sched_context_valid_irq_node [wp]:
  "\<lbrace>valid_irq_node\<rbrace> update_sched_context p sc  \<lbrace>\<lambda>r. valid_irq_node\<rbrace>"
  by (wpsimp wp: valid_irq_node_typ)

lemma update_sched_context_invs:
  "\<lbrace>invs and valid_sched_context sc and (\<lambda>s. live_sc sc \<longrightarrow> ex_nonz_cap_to p s)
     and (\<lambda>s. sym_refs ((state_refs_of s)(p := refs_of_sc sc)))\<rbrace>
      update_sched_context p sc \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (wpsimp simp: invs_def valid_state_def valid_pspace_def simp_del: fun_upd_apply)

lemma commit_time_invs: "\<lbrace>invs\<rbrace> commit_time \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wpsimp simp: commit_time_def simp_del: fun_upd_apply
                wp: update_sched_context_invs)
          apply (rule hoare_vcg_conj_lift)
           apply (wpsimp wp: static_imp_wp simp: set_refills_def)
          apply wpsimp
         apply (wpsimp simp_del: fun_upd_apply)
         apply (rule hoare_vcg_conj_lift)
          apply (wpsimp wp: static_imp_wp)
         apply wpsimp
        apply (wpsimp simp: is_round_robin_def simp_del: fun_upd_apply)
       apply (wpsimp wp: get_sched_context_wp)
      apply (wpsimp wp: hoare_vcg_all_lift simp_del: fun_upd_apply)+
  by (fastforce dest: invs_valid_objs invs_iflive invs_sym_refs
       simp: valid_objs_def obj_at_def valid_obj_def if_live_then_nonz_cap_def
             live_def live_sc_def fun_upd_idem refs_of_def state_refs_of_def)

lemma refill_unblock_check_invs: "\<lbrace>invs\<rbrace> refill_unblock_check r \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (wpsimp simp: refill_unblock_check_def refills_merge_valid[simplified]
                      is_round_robin_def
          wp: get_refills_inv hoare_drop_imp get_sched_context_wp)

crunches switch_sched_context
  for consumed_time[wp]: "\<lambda>s. P (consumed_time s)"
  and reprogram_timer[wp]: "\<lambda>s. P (reprogram_timer s)"
  and cur_time[wp]: "\<lambda>s. P (cur_time s)"
  and cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  (wp: crunch_wps hoare_vcg_if_lift2 simp: Let_def ignore: commit_domain_time)

lemma switch_sched_context_invs[wp]:
  "\<lbrace>invs\<rbrace> switch_sched_context \<lbrace>\<lambda>_. invs \<rbrace>"
  by (wpsimp simp: switch_sched_context_def rollback_time_def
         wp: hoare_if gbn_inv commit_time_invs refill_unblock_check_invs
             hoare_drop_imp hoare_vcg_if_lift2)

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

lemma set_refills_pred_tcb_at[wp]:
  "\<lbrace> pred_tcb_at proj f t \<rbrace> set_refills p r \<lbrace> \<lambda>rv. pred_tcb_at proj f t \<rbrace>"
  by (wpsimp simp: set_refills_def)

lemma refill_split_check_pred_tcb_at[wp]:
  "\<lbrace> pred_tcb_at proj f t \<rbrace> refill_split_check p u \<lbrace> \<lambda>rv. pred_tcb_at proj f t \<rbrace>"
  by (wpsimp wp: get_sched_context_wp simp: refill_split_check_def Let_def split_del: if_splits)

lemma commit_time_pred_tcb_at[wp]:
  "\<lbrace> pred_tcb_at proj f t \<rbrace> commit_time \<lbrace> \<lambda>rv. pred_tcb_at proj f t \<rbrace>"
  by (wpsimp simp: commit_time_def)

lemma update_sched_context_ct_in_state[wp]:
  "\<lbrace> ct_in_state t \<rbrace> update_sched_context p sc \<lbrace> \<lambda>rv. ct_in_state t \<rbrace>"
  by (wpsimp simp: update_sched_context_def set_object_def get_object_def obj_at_def
                      pred_tcb_at_def ct_in_state_def simp_del: fun_upd_apply) fastforce

lemma set_refills_ct_in_state[wp]:
  "\<lbrace> ct_in_state t \<rbrace> set_refills p r \<lbrace> \<lambda>rv. ct_in_state t \<rbrace>"
  by (wpsimp simp: set_refills_def)

lemma refill_split_check_ct_in_state[wp]:
  "\<lbrace> ct_in_state t \<rbrace> refill_split_check csc consumed \<lbrace> \<lambda>rv. ct_in_state t \<rbrace>"
  by (wpsimp simp: refill_split_check_def Let_def split_del: if_splits wp: get_sched_context_wp)

lemma commit_time_ct_in_state[wp]:
  "\<lbrace> ct_in_state t \<rbrace> commit_time \<lbrace> \<lambda>rv. ct_in_state t \<rbrace>"
  by (wpsimp simp: commit_time_def)

lemma rollback_time_ct_in_state[wp]:
  "\<lbrace> ct_in_state t \<rbrace> rollback_time \<lbrace> \<lambda>rv. ct_in_state t \<rbrace>"
  by (wpsimp simp: rollback_time_def)

lemma refill_unblock_check_ct_in_state[wp]:
  "\<lbrace> ct_in_state t \<rbrace> refill_unblock_check csc \<lbrace> \<lambda>rv. ct_in_state t \<rbrace>"
  by (wpsimp wp: get_refills_wp get_sched_context_wp
       simp: refill_unblock_check_def is_round_robin_def refills_merge_valid[simplified])

lemma switch_sched_context_ct_in_state[wp]:
  "\<lbrace> ct_in_state t \<rbrace> switch_sched_context \<lbrace> \<lambda>rv. ct_in_state t \<rbrace>"
  by (wpsimp simp: switch_sched_context_def wp: hoare_drop_imp hoare_vcg_if_lift2)

lemma sc_and_timer_activatable: "\<lbrace>ct_in_state activatable\<rbrace> sc_and_timer \<lbrace>\<lambda>rv. ct_in_state activatable\<rbrace>"
  apply (wpsimp simp: sc_and_timer_def switch_sched_context_def
           wp: hoare_drop_imp modify_wp hoare_vcg_if_lift2)
  done

text {* invocation related lemmas *}
(* RT FIXME: maybe move? *)

primrec
  valid_sched_context_inv :: "sched_context_invocation \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
    "valid_sched_context_inv (InvokeSchedContextConsumed scptr args)
     = (\<lambda>s. sc_at scptr s \<and> length args \<ge> 1)"
  | "valid_sched_context_inv (InvokeSchedContextBind scptr cap)
     = (\<lambda>s. sc_at scptr s \<and> valid_cap cap s)"
  | "valid_sched_context_inv (InvokeSchedContextUnbindObject scptr cap)
     = (\<lambda>s. sc_at scptr s \<and> valid_cap cap s)"
  | "valid_sched_context_inv (InvokeSchedContextUnbind scptr) = sc_at scptr"
  | "valid_sched_context_inv (InvokeSchedContextYieldTo scptr args)
     = (\<lambda>s. sc_at scptr s \<and> length args \<ge> 1)"
(*
definition
  valid_max_refills :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_max_refills ptr s \<equiv> )"
*)
primrec
  valid_sched_control_inv :: "sched_control_invocation \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
    "valid_sched_control_inv (InvokeSchedControlConfigure scptr budget period mrefills badge)
     = (\<lambda>s. sc_at scptr s
        (* probably also need something like \<and> mrefills \<le> max_extra_refills *))"

lemma invoke_sched_context_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace>
     invoke_sched_context i
   \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by (cases i;
      wpsimp wp: dxo_wp_weak mapM_wp'
       simp: invoke_sched_context_def sched_context_bind_ntfn_def sched_context_unbind_reply_def)

crunch inv[wp]: refill_capacity,refill_sufficient,refill_ready "\<lambda>s. P s"

lemma refill_add_tail_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> refill_add_tail sc_ptr rfl \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by (wpsimp simp: refill_add_tail_def wp: get_sched_context_wp)

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

lemma invoke_sched_control_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace>
     invoke_sched_control_configure i
   \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by (cases i; wpsimp simp: invoke_sched_control_configure_def split_del: if_splits
                  wp: hoare_vcg_if_lift2 hoare_drop_imp)


lemma invoke_sched_context_tcb[wp]:
  "\<lbrace>tcb_at tptr\<rbrace> invoke_sched_context i \<lbrace>\<lambda>rv. tcb_at tptr\<rbrace>"
  by (simp add: tcb_at_typ invoke_sched_context_typ_at [where P=id, simplified])

lemma invoke_sched_control_tcb[wp]:
  "\<lbrace>tcb_at tptr\<rbrace> invoke_sched_control_configure i \<lbrace>\<lambda>rv. tcb_at tptr\<rbrace>"
  by (simp add: tcb_at_typ invoke_sched_control_typ_at [where P=id, simplified])

crunch invs[wp]: set_message_info invs
crunches set_message_info,sched_context_update_consumed
 for tcb_at[wp]: "tcb_at t"
 and cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  (wp: get_object_wp)

lemma update_sched_context_tcb_at_ct[wp]:
  "\<lbrace>\<lambda>s. tcb_at (cur_thread s) s\<rbrace> update_sched_context p sc \<lbrace>\<lambda>rv s. tcb_at (cur_thread s) s\<rbrace>"
  by (wpsimp simp: update_sched_context_def set_object_def obj_at_def is_tcb_def wp: get_object_wp)

lemma sched_context_update_consumed_tcb_at_ct[wp]:
  "\<lbrace>\<lambda>s. tcb_at (cur_thread s) s\<rbrace> sched_context_update_consumed scp \<lbrace>\<lambda>rv s. tcb_at (cur_thread s) s\<rbrace>"
  by (wpsimp simp: sched_context_update_consumed_def)

(* RT FIXME Move *)
lemma [simp]:
 "live_sc (sc_consumed_update f sc) = live_sc sc"
 "live_sc (sc_period_update f sc) = live_sc sc"
 "live_sc (sc_refills_update g sc) = live_sc sc"
 "live_sc (sc_badge_update h sc) = live_sc sc"
  by (simp add: live_sc_def)+


lemma sched_context_update_consumed_invs[wp]:
  "\<lbrace>invs\<rbrace> sched_context_update_consumed scp \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wpsimp simp: sched_context_update_consumed_def wp: update_sched_context_invs get_sched_context_wp)
  by (fastforce dest: invs_valid_objs invs_iflive invs_sym_refs
       simp: valid_objs_def obj_at_def valid_obj_def if_live_then_nonz_cap_def
             live_def live_sc_def fun_upd_idem refs_of_def state_refs_of_def)

crunch interrupt_states[wp]: update_sched_context "\<lambda>s. P (interrupt_states s)"
  (wp: crunch_wps simp: crunch_simps)

lemma update_sched_context_minor_invs: (* minor? *)
  "\<lbrace>invs and obj_at (\<lambda>ko. refs_of ko = refs_of_sc val) ptr
         and valid_sched_context val
         and (\<lambda>s. live_sc val \<longrightarrow> ex_nonz_cap_to ptr s)\<rbrace>
     update_sched_context ptr val
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
          wp: valid_irq_node_typ simp_del: fun_upd_apply)
  apply (clarsimp simp: state_refs_of_def obj_at_def ext elim!: rsubst[where P = sym_refs])
  done
(*
lemma set_nofiticaion_invs:
  "\<lbrace>invs and valid_ntfn ntfn and (\<lambda>s. live_ntfn ntfn \<longrightarrow> ex_nonz_cap_to p s)
     and (\<lambda>s. sym_refs ((state_refs_of s)(p := refs_of_ntfn ntfn)))\<rbrace>
      set_notification p ntfn \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (wpsimp simp: invs_def valid_state_def valid_pspace_def live_def
      wp: valid_irq_node_typ simp_del: fun_upd_apply)

lemma set_reply_invs:
  "\<lbrace>invs and valid_reply reply and (\<lambda>s. live_reply reply \<longrightarrow> ex_nonz_cap_to p s)
     and (\<lambda>s. sym_refs ((state_refs_of s)(p := refs_of_reply reply)))\<rbrace>
      set_reply p reply \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (wpsimp simp: invs_def valid_state_def valid_pspace_def live_def refs_of_reply_def
      wp: valid_irq_node_typ simp_del: fun_upd_apply)

lemma valid_sc_sc_ntfn_update:
  " ntfn_at ntfn s \<Longrightarrow> valid_sched_context sc s \<Longrightarrow>
      valid_sched_context (sc_ntfn_update (K (Some ntfn)) sc) s"
  by (clarsimp simp: valid_sched_context_def)


lemma iflive_kheap_update:
  "\<lbrakk> if_live_then_nonz_cap s; live ko \<longrightarrow> ex_nonz_cap_to t s;
           obj_at (same_caps ko) t s \<rbrakk>
  \<Longrightarrow> if_live_then_nonz_cap (s\<lparr>kheap := kheap s(t \<mapsto> ko)\<rparr>)"
  unfolding fun_upd_def
  apply (simp add: if_live_then_nonz_cap_def, erule allEI)
  apply safe
   apply (clarsimp simp add: obj_at_def elim!: ex_cap_to_after_update
                   split: if_split_asm | (erule notE, erule ex_cap_to_after_update))+
  done
*)

(* RT FIXME: Move to Kheap?
lemma set_simple_k_sc_at[wp]:
  "\<lbrace> sc_at p \<rbrace> set_simple_ko f p' v \<lbrace>\<lambda>rv. sc_at p\<rbrace>"
  by (wpsimp simp: sc_at_typ wp: hoare_vcg_ex_lift set_simple_ko_typ_at)

lemma set_sk_sc_ntfn_sc_at[wp]:
  "\<lbrace> sc_ntfn_sc_at P p \<rbrace> set_simple_ko f p' v \<lbrace>\<lambda>rv. sc_ntfn_sc_at P p\<rbrace>"
  by (wpsimp simp: sc_ntfn_sc_at_def obj_at_def set_simple_ko_def set_object_def a_type_def
       wp: get_object_wp)
*)
lemma ssc_refs_of_Some[wp]:
  "\<lbrace>\<lambda>s. P ((state_refs_of s)(t:= insert (sc, TCBSchedContext)
          {x \<in> state_refs_of s t. snd x \<noteq> TCBSchedContext}))\<rbrace>
   set_tcb_obj_ref tcb_sched_context_update t (Some sc)
   \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (wpsimp simp: set_object_def wp: gets_the_wp)
  apply (fastforce elim!: rsubst[where P=P] dest!: get_tcb_SomeD
                   simp: state_refs_of_def conj_disj_distribR get_refs_def2
                         get_tcb_rev pred_tcb_def2 mem_Times_iff tcb_st_refs_of_def
                 intro!: ext split: thread_state.splits)
  done


(* RT FIXME: copied from IpcCancel_AI *)
lemma symreftype_inverse':
  "symreftype ref = ref' \<Longrightarrow> ref = symreftype ref'"
  by (cases ref) simp_all


lemma zombies_kheap_update:
  "\<lbrakk> zombies_final s; obj_at (same_caps ko) t s \<rbrakk>
   \<Longrightarrow> zombies_final (s\<lparr>kheap := kheap s(t \<mapsto> ko)\<rparr>)"
  apply (simp add: zombies_final_def is_final_cap'_def2, elim allEI)
  apply (clarsimp simp: cte_wp_at_after_update fun_upd_def)
  done


text {* bind/unbind invs lemmas *}


lemma sched_context_bind_ntfn_invs[wp]:
  "\<lbrace>invs and ex_nonz_cap_to sc and ex_nonz_cap_to ntfn
    and obj_at (\<lambda>ko. \<exists>ntfn. ko = Notification ntfn \<and> (ntfn_sc ntfn = None)) ntfn
    and sc_ntfn_sc_at (\<lambda>ntfn'. ntfn' = None) sc \<rbrace>
      sched_context_bind_ntfn sc ntfn \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wpsimp simp: sched_context_bind_ntfn_def invs_def valid_state_def
      valid_pspace_def update_sk_obj_ref_def
       wp: get_simple_ko_wp valid_irq_node_typ set_simple_ko_valid_objs simple_obj_set_prop_at)
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
      wp: valid_irq_node_typ set_simple_ko_valid_objs get_simple_ko_wp get_sched_context_wp)
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
  apply ((fastforce split: if_split_asm ntfn.splits dest!: symreftype_inverse'
        simp: obj_at_def get_refs_def2 refs_of_ntfn_def ntfn_q_refs_of_def image_iff refs_of_simps)+)
  done


lemma is_schedulable_inv[wp]: "\<lbrace>P\<rbrace> is_schedulable x inq \<lbrace> \<lambda>_. P\<rbrace>"
  by (wpsimp simp: is_schedulable_def)

lemma sched_context_resume_aligned[wp]:
  "\<lbrace>pspace_aligned\<rbrace> sched_context_resume param_a \<lbrace>\<lambda>_. pspace_aligned\<rbrace>"
  by (wpsimp simp: sched_context_resume_def refill_sufficient_def refill_ready_def is_schedulable_def
        wp: get_refills_wp get_sched_context_wp thread_get_wp)

lemma sched_context_resume_distinct[wp]:
  "\<lbrace>pspace_distinct\<rbrace> sched_context_resume param_a \<lbrace>\<lambda>_. pspace_distinct\<rbrace>"
  by (wpsimp simp: sched_context_resume_def refill_sufficient_def refill_ready_def is_schedulable_def
        wp: get_refills_wp get_sched_context_wp thread_get_wp)

lemma sched_context_resume_iflive[wp]:
  "\<lbrace>if_live_then_nonz_cap\<rbrace> sched_context_resume param_a \<lbrace>\<lambda>_. if_live_then_nonz_cap\<rbrace>"
  by (wpsimp simp: sched_context_resume_def refill_sufficient_def refill_ready_def is_schedulable_def
        wp: get_refills_wp get_sched_context_wp thread_get_wp)

lemma sched_context_resume_sc_at[wp]:
  "\<lbrace>sc_at sc_ptr\<rbrace> sched_context_resume param_a \<lbrace>\<lambda>_. sc_at sc_ptr\<rbrace>"
  by (wpsimp simp: sched_context_resume_def refill_sufficient_def refill_ready_def is_schedulable_def
        wp: get_refills_wp get_sched_context_wp thread_get_wp)

lemma sched_context_resume_cte_wp_at[wp]:
  "\<lbrace>cte_wp_at P c\<rbrace> sched_context_resume param_a \<lbrace>\<lambda>_. cte_wp_at P c\<rbrace>"
  by (wpsimp simp: sched_context_resume_def refill_sufficient_def refill_ready_def is_schedulable_def
        wp: get_refills_wp get_sched_context_wp thread_get_wp)

lemma sched_context_resume_interrupt_irq_node[wp]:
  "\<lbrace>\<lambda>s. P (interrupt_irq_node s)\<rbrace> sched_context_resume param_a \<lbrace>\<lambda>_ s. P (interrupt_irq_node s)\<rbrace>"
  apply (wpsimp simp: sched_context_resume_def refill_sufficient_def refill_ready_def is_schedulable_def
        wp: get_refills_wp valid_irq_node_typ get_sched_context_wp thread_get_wp)
  done

lemma sched_context_resume_it[wp]:
  "\<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> sched_context_resume param_a \<lbrace>\<lambda>_ s. P (idle_thread s)\<rbrace>"
  by (wpsimp simp: sched_context_resume_def refill_sufficient_def refill_ready_def is_schedulable_def
        wp: get_refills_wp get_sched_context_wp thread_get_wp)

lemma sched_context_resume_no_cdt[wp]:
  "\<lbrace>\<lambda>s. P (cdt s)\<rbrace> sched_context_resume param_a \<lbrace>\<lambda>_ s. P (cdt s)\<rbrace>"
  by (wpsimp simp: sched_context_resume_def refill_sufficient_def refill_ready_def is_schedulable_def
        wp: get_refills_wp get_sched_context_wp thread_get_wp)

lemma sched_context_resume_no_revokable[wp]:
  "\<lbrace>\<lambda>s. P (is_original_cap s)\<rbrace> sched_context_resume param_a \<lbrace>\<lambda>_ s. P (is_original_cap s)\<rbrace>"
  by (wpsimp simp: sched_context_resume_def refill_sufficient_def refill_ready_def is_schedulable_def
        wp: get_refills_wp get_sched_context_wp thread_get_wp)

lemma sched_context_resume_valid_irq_states[wp]:
  "\<lbrace>valid_irq_states\<rbrace> sched_context_resume param_a \<lbrace>\<lambda>_. valid_irq_states\<rbrace>"
  by (wpsimp simp: sched_context_resume_def refill_sufficient_def refill_ready_def is_schedulable_def
        wp: get_refills_wp get_sched_context_wp thread_get_wp)

lemma sched_context_resume_pspace_in_kernel_window[wp]:
  "\<lbrace>pspace_in_kernel_window\<rbrace> sched_context_resume param_a \<lbrace>\<lambda>_. pspace_in_kernel_window\<rbrace>"
  by (wpsimp simp: sched_context_resume_def refill_sufficient_def refill_ready_def is_schedulable_def
        wp: get_refills_wp get_sched_context_wp thread_get_wp)

lemma sched_context_resume_pspace_respects_device_region[wp]:
  "\<lbrace>pspace_respects_device_region\<rbrace> sched_context_resume param_a \<lbrace>\<lambda>_. pspace_respects_device_region\<rbrace>"
  by (wpsimp simp: sched_context_resume_def refill_sufficient_def refill_ready_def is_schedulable_def
        wp: get_refills_wp get_sched_context_wp thread_get_wp)

lemma sched_context_resume_cur_tcb[wp]:
  "\<lbrace>cur_tcb\<rbrace> sched_context_resume param_a \<lbrace>\<lambda>_. cur_tcb\<rbrace>"
  by (wpsimp simp: sched_context_resume_def refill_sufficient_def refill_ready_def is_schedulable_def
        wp: get_refills_wp get_sched_context_wp thread_get_wp)

lemma sched_context_resume_interrupt_states[wp]:
  "\<lbrace>\<lambda>s. P (interrupt_states s)\<rbrace> sched_context_resume param_a \<lbrace>\<lambda>_ s. P (interrupt_states s)\<rbrace>"
  by (wpsimp simp: sched_context_resume_def refill_sufficient_def refill_ready_def is_schedulable_def
        wp: get_refills_wp get_sched_context_wp thread_get_wp)

lemma sched_context_resume_valid_mdb[wp]:
  "\<lbrace>valid_mdb\<rbrace> sched_context_resume param_a \<lbrace>\<lambda>_. valid_mdb\<rbrace>"
  by (wpsimp simp: sched_context_resume_def refill_sufficient_def refill_ready_def is_schedulable_def
        wp: get_refills_wp get_sched_context_wp thread_get_wp)

lemma sched_context_resume_valid_objs[wp]:
  "\<lbrace>valid_objs\<rbrace> sched_context_resume param_a \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  by (wpsimp simp: sched_context_resume_def refill_sufficient_def refill_ready_def is_schedulable_def
        wp: get_refills_wp get_sched_context_wp thread_get_wp)

lemma sched_context_resume_zombies[wp]:
  "\<lbrace>zombies_final\<rbrace> sched_context_resume param_a \<lbrace>\<lambda>_. zombies_final\<rbrace>"
  by (wpsimp simp: sched_context_resume_def refill_sufficient_def refill_ready_def is_schedulable_def
        wp: get_refills_wp get_sched_context_wp thread_get_wp)

lemma sched_context_resume_valid_irq_handlers[wp]:
  "\<lbrace>valid_irq_handlers\<rbrace> sched_context_resume param_a \<lbrace>\<lambda>_. valid_irq_handlers\<rbrace>"
  by (wpsimp simp: sched_context_resume_def refill_sufficient_def refill_ready_def is_schedulable_def
        wp: get_refills_wp get_sched_context_wp thread_get_wp)

lemma sched_context_resume_valid_ioc[wp]:
  "\<lbrace>valid_ioc\<rbrace> sched_context_resume param_a \<lbrace>\<lambda>_. valid_ioc\<rbrace>"
  by (wpsimp simp: sched_context_resume_def refill_sufficient_def refill_ready_def is_schedulable_def
        wp: get_refills_wp get_sched_context_wp thread_get_wp)

lemma sched_context_resume_cap_refs_in_kernel_window[wp]:
  "\<lbrace>cap_refs_in_kernel_window\<rbrace> sched_context_resume param_a \<lbrace>\<lambda>_. cap_refs_in_kernel_window\<rbrace>"
  by (wpsimp simp: sched_context_resume_def refill_sufficient_def refill_ready_def is_schedulable_def
        wp: get_refills_wp get_sched_context_wp thread_get_wp)

lemma sched_context_resume_cap_refs_respects_device_region[wp]:
  "\<lbrace>cap_refs_respects_device_region\<rbrace> sched_context_resume param_a \<lbrace>\<lambda>_. cap_refs_respects_device_region\<rbrace>"
  by (wpsimp simp: sched_context_resume_def refill_sufficient_def refill_ready_def is_schedulable_def
        wp: get_refills_wp get_sched_context_wp thread_get_wp)

lemma sched_context_resume_valid_idle[wp]:
  "\<lbrace>valid_idle\<rbrace> sched_context_resume param_a \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  by (wpsimp simp: sched_context_resume_def refill_sufficient_def refill_ready_def is_schedulable_def
        wp: get_refills_wp get_sched_context_wp thread_get_wp)

lemma sched_context_resume_only_idle[wp]:
  "\<lbrace>only_idle\<rbrace> sched_context_resume param_a \<lbrace>\<lambda>_. only_idle\<rbrace>"
  by (wpsimp simp: sched_context_resume_def refill_sufficient_def refill_ready_def is_schedulable_def
        wp: get_refills_wp get_sched_context_wp thread_get_wp)

lemma sched_context_resume_valid_arch[wp]:
  "\<lbrace>valid_arch_state\<rbrace> sched_context_resume param_a \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  by (wpsimp simp: sched_context_resume_def refill_sufficient_def refill_ready_def is_schedulable_def
        wp: get_refills_wp get_sched_context_wp thread_get_wp)

lemma sched_context_resume_ifunsafe[wp]:
  "\<lbrace>if_unsafe_then_cap\<rbrace> sched_context_resume param_a \<lbrace>\<lambda>_. if_unsafe_then_cap\<rbrace>"
  by (wpsimp simp: sched_context_resume_def refill_sufficient_def refill_ready_def is_schedulable_def
        wp: get_refills_wp get_sched_context_wp thread_get_wp)

lemma sched_context_resume_valid_global_objs[wp]:
  "\<lbrace>valid_global_objs\<rbrace> sched_context_resume param_a \<lbrace>\<lambda>_. valid_global_objs\<rbrace>"
  by (wpsimp simp: sched_context_resume_def refill_sufficient_def refill_ready_def is_schedulable_def
        wp: get_refills_wp get_sched_context_wp thread_get_wp)

lemma sched_context_resume_valid_global_vspace_mappings[wp]:
  "\<lbrace>valid_global_vspace_mappings\<rbrace> sched_context_resume param_a \<lbrace>\<lambda>_. valid_global_vspace_mappings\<rbrace>"
  by (wpsimp simp: sched_context_resume_def refill_sufficient_def refill_ready_def is_schedulable_def
        wp: get_refills_wp get_sched_context_wp thread_get_wp)

lemma sched_context_resume_valid_arch_caps[wp]:
  "\<lbrace>valid_arch_caps\<rbrace> sched_context_resume param_a \<lbrace>\<lambda>_. valid_arch_caps\<rbrace>"
  by (wpsimp simp: sched_context_resume_def refill_sufficient_def refill_ready_def is_schedulable_def
        wp: get_refills_wp get_sched_context_wp thread_get_wp)

lemma sched_context_resume_v_ker_map[wp]:
  "\<lbrace>valid_kernel_mappings\<rbrace> sched_context_resume param_a \<lbrace>\<lambda>_. valid_kernel_mappings\<rbrace>"
  by (wpsimp simp: sched_context_resume_def refill_sufficient_def refill_ready_def is_schedulable_def
        wp: get_refills_wp get_sched_context_wp thread_get_wp)

lemma sched_context_resume_equal_mappings[wp]:
  "\<lbrace>equal_kernel_mappings\<rbrace> sched_context_resume param_a \<lbrace>\<lambda>_. equal_kernel_mappings\<rbrace>"
  by (wpsimp simp: sched_context_resume_def refill_sufficient_def refill_ready_def is_schedulable_def
        wp: get_refills_wp get_sched_context_wp thread_get_wp)

lemma sched_context_resume_valid_vspace_objs[wp]:
  "\<lbrace>valid_vspace_objs\<rbrace> sched_context_resume param_a \<lbrace>\<lambda>_. valid_vspace_objs\<rbrace>"
  by (wpsimp simp: sched_context_resume_def refill_sufficient_def refill_ready_def is_schedulable_def
        wp: get_refills_wp get_sched_context_wp thread_get_wp)

lemma sched_context_resume_vms[wp]:
  "\<lbrace>valid_machine_state\<rbrace> sched_context_resume param_a \<lbrace>\<lambda>_. valid_machine_state\<rbrace>"
  by (wpsimp simp: sched_context_resume_def refill_sufficient_def refill_ready_def is_schedulable_def
        wp: get_refills_wp get_sched_context_wp thread_get_wp)

lemma sched_context_resume_valid_global_refs[wp]:
  "\<lbrace>valid_global_refs\<rbrace> sched_context_resume param_a \<lbrace>\<lambda>_. valid_global_refs\<rbrace>"
  by (wpsimp simp: sched_context_resume_def refill_sufficient_def refill_ready_def is_schedulable_def
        wp: get_refills_wp get_sched_context_wp thread_get_wp)

lemma sched_context_resume_valid_asid_map[wp]:
  "\<lbrace>valid_asid_map\<rbrace> sched_context_resume param_a \<lbrace>\<lambda>_. valid_asid_map\<rbrace>"
  by (wpsimp simp: sched_context_resume_def refill_sufficient_def refill_ready_def is_schedulable_def
        wp: get_refills_wp get_sched_context_wp thread_get_wp)

lemma sched_context_resume_state_hyp_refs_of[wp]:
  "\<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace> sched_context_resume param_a \<lbrace>\<lambda>_ s. P (state_hyp_refs_of s)\<rbrace>"
  by (wpsimp simp: sched_context_resume_def refill_sufficient_def refill_ready_def is_schedulable_def
        wp: get_refills_wp get_sched_context_wp thread_get_wp)

lemma state_refs_of_reprogram_timer_update[simp]:
  "state_refs_of (reprogram_timer_update f s) = state_refs_of s"
  by (clarsimp simp: state_refs_of_def)

lemma sched_context_resume_state_refs_of[wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace> sched_context_resume param_a \<lbrace>\<lambda>_ s. P (state_refs_of s)\<rbrace>"
  apply (wpsimp simp: sched_context_resume_def refill_sufficient_def refill_ready_def is_schedulable_def
        wp: get_refills_wp get_sched_context_wp thread_get_wp)
  done

lemma sched_context_resume_no_caps_of_state[wp]:
  "\<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> sched_context_resume param_a \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  by (wpsimp simp: sched_context_resume_def refill_sufficient_def refill_ready_def is_schedulable_def
        wp: get_refills_wp get_sched_context_wp thread_get_wp)


lemma set_sc_obj_ref_ex_cap[wp]:
  "\<lbrace>ex_nonz_cap_to p\<rbrace> set_sc_obj_ref f p' v  \<lbrace>\<lambda>rv. ex_nonz_cap_to p\<rbrace>"
  by (wp ex_nonz_cap_to_pres)

lemma ssc_sc_tcb_update_bound_sc_tcb_at[wp]:
  "\<lbrace>bound_sc_tcb_at P t\<rbrace> set_sc_obj_ref sc_tcb_update scp tcb \<lbrace>\<lambda>rv. bound_sc_tcb_at P t\<rbrace>"
  by (wpsimp simp: set_sc_obj_ref_def)

lemma sched_context_bind_tcb_invs[wp]:
  "\<lbrace>invs and (\<lambda>s. tcb \<noteq> idle_thread s)
    and bound_sc_tcb_at (op = None) tcb and ex_nonz_cap_to tcb
    and sc_tcb_sc_at (op = None) sc and ex_nonz_cap_to sc\<rbrace>
      sched_context_bind_tcb sc tcb \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wpsimp simp: sched_context_bind_tcb_def invs_def valid_state_def
      valid_pspace_def set_sc_obj_ref_def
      wp: valid_irq_node_typ obj_set_prop_at get_sched_context_wp ssc_refs_of_Some)
  apply (clarsimp simp: obj_at_def is_sc_obj_def pred_tcb_at_def)
  apply (case_tac "sc=tcb", simp)
  apply safe
    apply (erule (1) valid_objsE)
    apply (clarsimp simp: valid_obj_def valid_sched_context_def obj_at_def is_tcb)
   apply (frule valid_objs_valid_sched_context_size)
    apply fastforce
   apply assumption
  apply (erule delta_sym_refs)
   apply (clarsimp simp: state_refs_of_def obj_at_def refs_of_sc_def split: if_splits)
  apply (clarsimp simp: state_refs_of_def refs_of_tcb_def get_refs_def2 image_iff
      tcb_st_refs_of_def sc_tcb_sc_at_def obj_at_def
      dest!: symreftype_inverse' split: if_splits)
   apply (clarsimp split: thread_state.split_asm if_split_asm)
  apply (clarsimp simp: refs_of_sc_def get_refs_def2 image_iff)
  done

lemma sched_context_unbind_tcb_invs[wp]:
  "\<lbrace>invs and sc_tcb_sc_at bound sc\<rbrace> sched_context_unbind_tcb sc \<lbrace>\<lambda>rv. invs\<rbrace>"
   sorry

lemma sched_context_unbind_all_tcbs_invs[wp]:
  "\<lbrace>invs\<rbrace> sched_context_unbind_all_tcbs sc \<lbrace>\<lambda>rv. invs\<rbrace>"
   sorry

lemma invoke_sched_context_invs[wp]:
  "\<lbrace>invs and valid_sched_context_inv i\<rbrace> invoke_sched_context i \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (cases i; wpsimp wp: dxo_wp_weak
          simp: invoke_sched_context_def set_consumed_def valid_sched_context_inv_def)
apply (drule invs_iflive)
  sorry


lemma invoke_sched_control_configure_invs[wp]:
  "\<lbrace>invs and valid_sched_control_inv i\<rbrace> invoke_sched_control_configure i \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (cases i; wpsimp simp: invoke_sched_control_configure_def split_del: if_splits
                  wp: hoare_vcg_if_lift2 hoare_drop_imp)

  sorry


lemma sts_valid_sched_context_inv:
  "\<lbrace>valid_sched_context_inv ai\<rbrace> set_thread_state t st \<lbrace>\<lambda>rv. valid_sched_context_inv ai\<rbrace>"
  sorry


lemma sts_valid_sched_control_inv:
  "\<lbrace>valid_sched_control_inv ai\<rbrace> set_thread_state t st \<lbrace>\<lambda>rv. valid_sched_control_inv ai\<rbrace>"
  sorry


lemma decode_sched_context_inv_inv:
  "\<lbrace>P\<rbrace>
     decode_sched_context_invocation label sc_ptr excaps args
   \<lbrace>\<lambda>rv. P\<rbrace>"
  sorry


lemma decode_sched_control_inv_inv:
  "\<lbrace>P\<rbrace>
     decode_sched_control_invocation label args excaps
   \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (wpsimp simp: decode_sched_control_invocation_def split_del: if_splits
             wp: hoare_vcg_if_lift2 hoare_drop_imp)


  sorry


lemma decode_sched_context_inv_wf:
  "\<lbrace>invs and sc_at sc_ptr and
     (\<lambda>s. \<forall>x\<in>set excaps. s \<turnstile> x) and
     (\<lambda>s. \<forall>x\<in>set excaps. \<forall>r\<in>zobj_refs x. ex_nonz_cap_to r s)\<rbrace>
     decode_sched_context_invocation label sc_ptr excaps args
   \<lbrace>valid_sched_context_inv\<rbrace>, -"
  sorry


lemma decode_sched_control_inv_wf:
  "\<lbrace>invs and
     (\<lambda>s. \<forall>x\<in>set excaps. s \<turnstile> x) and
     (\<lambda>s. \<forall>x\<in>set excaps. \<forall>r\<in>zobj_refs x. ex_nonz_cap_to r s)\<rbrace>
     decode_sched_control_invocation label args excaps
   \<lbrace>valid_sched_control_inv\<rbrace>, -"
  sorry


end