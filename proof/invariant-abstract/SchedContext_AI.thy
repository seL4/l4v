(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory SchedContext_AI
imports
  Lib.MonadicRewrite (* FIXME RT: avoid late Lib import *)
  RealTime_AI

begin

context begin interpretation Arch .

requalify_facts
  valid_global_refsD

end

lemma no_cap_to_idle_sc_ptr:
  "\<lbrakk>cte_wp_at ((=) (SchedContextCap a b)) slot s; invs s\<rbrakk> \<Longrightarrow> a \<noteq> idle_sc_ptr"
  by (fastforce simp: invs_def valid_state_def cap_range_def dest!: valid_global_refsD)

(* FIXME - move *)
lemma get_tcb_exst_update:
  "get_tcb p (trans_state f s) = get_tcb p s"
  by (simp add: get_tcb_def)

lemma ct_in_state_trans_update[simp]: "ct_in_state st (trans_state f s) = ct_in_state st s"
  apply (simp add: ct_in_state_def)
  done

(* RT: sc_and_timer invs *)
lemma set_refills_valid_objs:
  "set_refills sc_ptr refills \<lbrace>valid_objs\<rbrace>"
  apply (wpsimp simp: set_refills_def set_object_def
                  wp: get_object_wp update_sched_context_valid_objs_same)
  apply (clarsimp simp: valid_sched_context_def)
  done

crunches commit_domain_time, set_next_interrupt, set_refills, refill_budget_check
  for consumed_time[wp]: "\<lambda>s. P (consumed_time s)"
  and reprogram_timer[wp]: "\<lambda>s. P (reprogram_timer s)"
  and cur_sc[wp]: "\<lambda>s. P (cur_sc s)"
  and cur_time[wp]: "\<lambda>s. P (cur_time s)"
  and arch_state[wp]: "\<lambda>s. P (arch_state s)"
  and cur_sc_cur_thread[wp]: "\<lambda>s. P (cur_sc s) (cur_thread s)"
  and scheduler_action[wp]: "\<lambda>s. P (scheduler_action s)"
  (wp: crunch_wps simp: Let_def)

crunch reprogram_timer[wp]: commit_time "\<lambda>s. P (reprogram_timer s)"
  (wp: crunch_wps hoare_vcg_if_lift2 ignore: commit_domain_time)

crunches refill_unblock_check
  for consumed_time[wp]: "\<lambda>s. P (consumed_time s)"
  and cur_sc[wp]: "\<lambda>s. P (cur_sc s)"
  and cur_time[wp]: "\<lambda>s. P (cur_time s)"
  and cur_sc_cur_thread[wp]: "\<lambda>s. P (cur_sc s) (cur_thread s)"
  (wp: crunch_wps hoare_vcg_if_lift2)

(* FIXME: rename to is_round_robin_inv *)
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

lemmas refill_unblock_check_defs
  = refill_unblock_check_def is_round_robin_def merge_refills_def refill_pop_head_def
    refill_head_overlapping_loop_def set_refill_hd_def update_refill_hd_def

lemmas refill_budget_check_defs
  = refill_budget_check_def non_overlapping_merge_refills_def merge_refills_def refill_pop_head_def
    head_insufficient_loop_def handle_overrun_loop_def handle_overrun_loop_body_def
    set_refill_hd_def update_refill_hd_def refill_single_def refill_size_def

lemma update_sched_context_decompose:
   "update_sched_context scp (\<lambda>sc. f (g sc))
    = (do update_sched_context scp g; update_sched_context scp f od)"
  apply (rule ext)
  by (clarsimp simp: update_sched_context_def get_object_def set_object_def a_type_simps
                     gets_def get_def put_def return_def fail_def assert_def bind_def
                     gets_the_def assert_opt_def
              split: Structures_A.kernel_object.splits option.splits)

lemma update_refill_hd_rewrite:
  "update_refill_hd sc_ptr f =
   do refills \<leftarrow> get_refills sc_ptr;
      set_refills sc_ptr (f (hd refills) # (tl refills))
   od"
  apply (rule monad_eqI)
    apply (clarsimp simp: update_refill_hd_def update_sched_context_def get_refills_def
                          get_sched_context_def set_refills_def in_monad)
    apply (rename_tac ko; case_tac ko;
           clarsimp simp: set_object_def get_object_def in_monad cong: sched_context.fold_congs)
   apply (clarsimp simp: update_refill_hd_def update_sched_context_def get_refills_def
                         get_sched_context_def set_refills_def in_monad)
   apply (rename_tac ko ko'; case_tac ko;
          clarsimp simp: set_object_def get_object_def in_monad
                   cong: sched_context.fold_congs)
  apply (clarsimp simp: update_refill_hd_def update_sched_context_def get_refills_def get_sched_context_def
                        set_refills_def get_object_def snd_bind gets_the_def exec_gets assert_opt_def
                 split: option.splits)
  apply (rename_tac ko; case_tac ko;
         clarsimp simp: set_object_def get_object_def gets_the_def in_monad a_type_def
                        snd_gets snd_bind exec_gets return_def snd_assert snd_get exec_get snd_put)
  done

lemma update_refill_tl_rewrite:
  "update_refill_tl sc_ptr f =
   do refills \<leftarrow> get_refills sc_ptr;
      set_refills sc_ptr (butlast refills @ [f (last refills)])
   od"
  apply (rule monad_eqI)
    apply (clarsimp simp: update_refill_tl_def update_sched_context_def get_refills_def
                          get_sched_context_def set_refills_def in_monad)
    apply (rename_tac ko; case_tac ko;
           clarsimp simp: set_object_def get_object_def in_monad cong: sched_context.fold_congs)
   apply (clarsimp simp: update_refill_tl_def update_sched_context_def get_refills_def
                         get_sched_context_def set_refills_def in_monad)
   apply (rename_tac ko ko'; case_tac ko;
          clarsimp simp: set_object_def get_object_def in_monad
                   cong: sched_context.fold_congs)
  apply (clarsimp simp: update_refill_tl_def update_sched_context_def get_refills_def get_sched_context_def
                        set_refills_def get_object_def snd_bind gets_the_def exec_gets assert_opt_def
                 split: option.splits)
  apply (rename_tac ko; case_tac ko;
         clarsimp simp: set_object_def get_object_def gets_the_def in_monad a_type_def
                        snd_gets snd_bind exec_gets return_def snd_assert snd_get exec_get snd_put)
  done

lemma update_sched_context_set_refills_rewrite:
  "update_sched_context sc_ptr (sc_refills_update f) =
   do refills \<leftarrow> get_refills sc_ptr;
      set_refills sc_ptr (f refills)
   od"
  apply (rule monad_eqI)
    apply (clarsimp simp: update_sched_context_def get_refills_def
                          get_sched_context_def set_refills_def in_monad)
    apply (rename_tac ko; case_tac ko;
           clarsimp simp: set_object_def get_object_def in_monad cong: sched_context.fold_congs)
   apply (clarsimp simp:  update_sched_context_def get_refills_def
                         get_sched_context_def set_refills_def in_monad)
   apply (rename_tac ko ko'; case_tac ko;
          clarsimp simp: set_object_def get_object_def in_monad
                   cong: sched_context.fold_congs)
  apply (clarsimp simp:  update_sched_context_def get_refills_def get_sched_context_def
                        set_refills_def get_object_def snd_bind gets_the_def exec_gets assert_opt_def
                 split: option.splits)
  apply (rename_tac ko; case_tac ko;
         clarsimp simp: set_object_def get_object_def gets_the_def in_monad a_type_def
                        snd_gets snd_bind exec_gets return_def snd_assert snd_get exec_get snd_put)
  done

lemma update_refill_hd_valid_objs[wp]:
  "update_refill_hd sc_ptr f \<lbrace>valid_objs\<rbrace>"
  by (wpsimp simp: update_refill_hd_rewrite wp: set_refills_valid_objs)

lemma update_refill_tl_valid_objs[wp]:
  "update_refill_tl sc_ptr f \<lbrace>valid_objs\<rbrace>"
  by (wpsimp simp: update_refill_tl_rewrite wp: set_refills_valid_objs)

lemma refill_unblock_check_valid_objs[wp]:
  "refill_unblock_check sc_ptr \<lbrace>valid_objs\<rbrace>"
  by (wpsimp wp: set_refills_valid_objs whileLoop_wp' get_refills_wp
                 hoare_drop_imps
           simp: refill_unblock_check_defs)

lemma schedule_used_non_nil:
  "schedule_used b ls u \<noteq> []"
  by (induction ls; clarsimp simp: Let_def schedule_used_def)

lemma set_refills_wp:
  "\<lbrace>\<lambda>s. \<forall>sc n. obj_at ((=) (SchedContext sc n)) sc_ptr s
               \<longrightarrow> P (s\<lparr>kheap := kheap s(sc_ptr \<mapsto> SchedContext (sc\<lparr>sc_refills := refills\<rparr>) n)\<rparr>)\<rbrace>
     set_refills sc_ptr refills
   \<lbrace>\<lambda>r. P\<rbrace>"
  unfolding set_refills_def
  by (wpsimp wp: update_sched_context_wp)

lemma refill_pop_head_valid_objs[wp]:
  "refill_pop_head sc_ptr \<lbrace>valid_objs\<rbrace>"
  unfolding refill_pop_head_def by wpsimp

lemma head_insufficient_loop_valid_objs[wp]:
  "head_insufficient_loop usage \<lbrace>valid_objs\<rbrace>"
  unfolding head_insufficient_loop_def
  by (wpsimp wp: whileLoop_wp' simp: non_overlapping_merge_refills_def update_refill_hd_def)

lemma handle_overrun_loop_valid_objs[wp]:
  "handle_overrun_loop usage \<lbrace>valid_objs\<rbrace>"
  unfolding handle_overrun_loop_def handle_overrun_loop_body_def refill_single_def refill_size_def
  apply (wpsimp wp: whileLoop_wp' update_sched_context_valid_objs_same hoare_vcg_all_lift)
  apply (rule_tac Q="\<lambda>_. \<top>" in hoare_strengthen_post[rotated])
  apply (clarsimp simp: valid_sched_context_def)
  by (wpsimp wp: get_refills_wp simp: valid_sched_context_def)+

lemma refill_budget_check_valid_objs[wp]:
  "refill_budget_check usage \<lbrace>valid_objs\<rbrace>"
  apply (clarsimp simp: refill_budget_check_def)
  apply (rule hoare_seq_ext_skip, solves wpsimp)+
  apply (wpsimp wp: set_refills_valid_objs simp: update_refill_hd_def)
  done

(* FIXME RT: move to Invariants_AI *)
lemma valid_irq_states_consumed_time_update[iff]:
  "valid_irq_states (consumed_time_update f s) = valid_irq_states s"
  by (simp add: valid_irq_states_def)
lemma vms_consumed_time_update[iff]:
  "valid_machine_state (consumed_time_update f s) = valid_machine_state s"
  by (simp add: valid_machine_state_def)

(* FIXME RT: move to Invariants_AI *)
lemma valid_irq_states_cur_time_update[iff]:
  "valid_irq_states (cur_time_update f s) = valid_irq_states s"
  by (simp add: valid_irq_states_def)
lemma vms_cur_time_update[iff]:
  "valid_machine_state (cur_time_update f s) = valid_machine_state s"
  by (simp add: valid_machine_state_def)

(* FIXME RT: move to Invariants_AI *)
lemma valid_irq_states_reprogram_timer_update[iff]:
  "valid_irq_states (reprogram_timer_update f s) = valid_irq_states s"
  by (simp add: valid_irq_states_def)
lemma vms_reprogram_timer_update[iff]:
  "valid_machine_state (reprogram_timer_update f s) = valid_machine_state s"
  by (simp add: valid_machine_state_def)

(* FIXME RT: move to Invariants_AI *)
lemma valid_irq_states_cur_sc_update[iff]:
  "valid_irq_states (cur_sc_update f s) = valid_irq_states s"
  by (simp add: valid_irq_states_def)
lemma vms_cur_c_update[iff]:
  "valid_machine_state (cur_sc_update f s) = valid_machine_state s"
  by (simp add: valid_machine_state_def)

(* FIXME RT: move to ArchAcc_AI? *)
lemma cur_tcb_consumed_time_update[iff]:
  "cur_tcb (consumed_time_update f s) = cur_tcb s"
  by (simp add: cur_tcb_def)

(* FIXME RT: move to ArchAcc_AI? *)
lemma cur_sc_tcb_consumed_time_update[iff]:
  "cur_sc_tcb (consumed_time_update f s) = cur_sc_tcb s"
  by (simp add: cur_sc_tcb_def)

(* FIXME RT: move to ArchAcc_AI? *)
lemma cur_tcb_cur_time_update[iff]:
  "cur_tcb (cur_time_update f s) = cur_tcb s"
  by (simp add: cur_tcb_def)

(* FIXME RT: move to ArchAcc_AI? *)
lemma cur_sc_tcb_cur_time_update[iff]:
  "cur_sc_tcb (cur_time_update f s) = cur_sc_tcb s"
  by (simp add: cur_sc_tcb_def)

(* FIXME RT: move to ArchAcc_AI? *)
lemma cur_tcb_cur_sc_update[iff]:
  "cur_tcb (cur_sc_update f s) = cur_tcb s"
  by (simp add: cur_tcb_def)

(* FIXME RT: move to ArchAcc_AI? *)
lemma cur_tcb_reprogram_timer_update[iff]:
  "cur_tcb (reprogram_timer_update f s) = cur_tcb s"
  by (simp add: cur_tcb_def)

(* FIXME RT: move to ArchAcc_AI? *)
lemma cur_sc_tcb_reprogram_timer_update[iff]:
  "cur_sc_tcb (reprogram_timer_update f s) = cur_sc_tcb s"
  by (simp add: cur_sc_tcb_def)

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

lemma refs_of_sc_sporadic_update[iff]:
  "refs_of_sc (sc_sporadic_update f sc) = refs_of_sc sc"
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

lemma refs_of_sched_context_sc_sporadic_update[iff]:
  "refs_of (SchedContext (sc_sporadic_update f sc) n) = refs_of (SchedContext sc n)"
  by simp

lemma set_refills_iflive[wp]:
  "\<lbrace>if_live_then_nonz_cap\<rbrace> set_refills ptr param_b \<lbrace>\<lambda>_. if_live_then_nonz_cap\<rbrace> "
  by (wpsimp simp: set_refills_def get_sched_context_def wp: hoare_vcg_all_lift get_object_wp)

lemma
  shows valid_sc_sc_consumed_update[iff]:
  "valid_sched_context (sc_consumed_update f sc) = valid_sched_context sc"
  and valid_sc_sc_badge_update[iff]:
  "valid_sched_context (sc_badge_update g sc) = valid_sched_context sc"
  and valid_sc_sc_sporadic_update[iff]:
  "valid_sched_context (sc_sporadic_update h sc) = valid_sched_context sc"
  by (fastforce simp: valid_sched_context_def)+

lemma invs_consumed_time_update[iff]:
  "invs (consumed_time_update f s) = invs s"
  by (clarsimp simp: invs_def valid_state_def)

lemma invs_cur_time_update[iff]:
  "invs (cur_time_update f s) = invs s"
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

global_interpretation update_sched_context: non_ntfn_op "update_sched_context ptr f"
  by unfold_locales (wpsimp simp: update_sched_context_def ntfn_at_pred_def obj_at_def
                              wp: set_object_wp get_object_wp)

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

lemma update_sc_replies_valid_replies:
  "\<lbrace> \<lambda>s. \<forall>rs. sc_replies_sc_at (\<lambda>rs'. set rs' = set rs) sc_ptr s
              \<longrightarrow> P (replies_with_sc_upd_replies (f rs) sc_ptr (replies_with_sc s))
                    (replies_blocked s) \<rbrace>
    update_sched_context sc_ptr (sc_replies_update f)
   \<lbrace> \<lambda>rv. valid_replies_pred P \<rbrace>"
  by (wpsimp wp: update_sched_context_valid_replies)
     (fastforce simp: sc_replies_sc_at_def obj_at_def elim!: rsubst2[of P, OF _ _ refl])

lemma set_sc_replies_valid_replies:
  "\<lbrace> \<lambda>s. P (replies_with_sc_upd_replies replies sc_ptr (replies_with_sc s)) (replies_blocked s) \<rbrace>
    set_sc_obj_ref sc_replies_update sc_ptr replies
   \<lbrace> \<lambda>rv. valid_replies_pred P \<rbrace>"
  by (wpsimp wp: update_sched_context_valid_replies)

(* Avoid using this directly. Use one of the following instead:
   - update_sc_but_not_sc_replies_valid_replies[wp]
   - update_sc_replies_valid_replies *)
lemma update_sc_but_not_sc_replies_valid_replies_2:
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
  "\<And>f. update_sched_context sc_ptr (sc_sporadic_update f) \<lbrace> valid_replies_pred P \<rbrace>"
  "\<And>f. update_sched_context sc_ptr (sc_yield_from_update f) \<lbrace> valid_replies_pred P \<rbrace>"
  by (rule update_sc_but_not_sc_replies_valid_replies_2, simp)+

lemma update_sc_no_tcb_update[wp]:
  "update_sched_context scp f \<lbrace>ko_at (TCB tcb) t\<rbrace>"
  apply (clarsimp simp: update_sched_context_def)
  by (wpsimp simp: set_object_def wp: get_object_wp simp: obj_at_def)

lemma update_sched_context_sc_tcb_sc_at:
  "\<lbrace>\<lambda>s. Q (sc_tcb_sc_at P sc_ptr s) \<and> (\<forall>x. (P (sc_tcb x) = P (sc_tcb (f x))))\<rbrace>
   update_sched_context sc_ptr' f
   \<lbrace>\<lambda>_ s. Q (sc_tcb_sc_at P sc_ptr s)\<rbrace>"
  apply (wpsimp simp: update_sched_context_def wp: set_object_wp get_object_wp)
  by (clarsimp simp: obj_at_def sc_at_pred_n_def)

lemma set_refills_valid_replies[wp]:
  "set_refills ptr refills \<lbrace> valid_replies_pred P \<rbrace>"
  by (wpsimp simp: set_refills_def)

lemma sc_refills_update_sym_refs [wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace> update_sched_context ptr (sc_refills_update f)
   \<lbrace>\<lambda>_ s. P (state_refs_of s)\<rbrace>"
  by (wpsimp wp: update_sched_context_refs_of_same)

lemma sc_refills_update_valid_idle [wp]:
  "\<lbrace>valid_idle\<rbrace> update_sched_context ptr (sc_refills_update f) \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  by (wpsimp simp: update_sched_context_def set_object_def get_object_def valid_idle_def obj_at_def
                   pred_tcb_at_def)

lemma set_refills_valid_state [wp]:
  "\<lbrace>valid_state\<rbrace> set_refills sc_ptr refills
   \<lbrace>\<lambda>_. valid_state\<rbrace>"
  by (wpsimp simp: set_refills_def valid_state_def valid_pspace_def valid_sched_context_def
               wp: update_sched_context_valid_objs_same valid_irq_node_typ)

lemma set_refills_cur_tcb [wp]:
  "\<lbrace>cur_tcb\<rbrace> set_refills sc_ptr refills \<lbrace>\<lambda>_. cur_tcb\<rbrace>"
  by (wpsimp simp: set_refills_def)

lemma set_refills_cur_sc_tcb [wp]:
  "\<lbrace>cur_sc_tcb\<rbrace> set_refills sc_ptr refills \<lbrace>\<lambda>_. cur_sc_tcb\<rbrace>"
  by (wpsimp simp: set_refills_def update_sched_context_def set_object_def get_object_def
                   cur_sc_tcb_def sc_tcb_sc_at_def obj_at_def)

lemma set_refills_fault_tcbs_valid_states[wp]:
  "set_refills ptr refills \<lbrace>fault_tcbs_valid_states\<rbrace>"
  by (wpsimp simp: set_refills_def)

lemma set_refills_invs[wp]:
  "set_refills ptr refills \<lbrace>invs\<rbrace>"
  by (wpsimp simp: invs_def)

lemma set_refills_valid_idle[wp]:
  "\<lbrace>valid_idle\<rbrace> set_refills ptr refills \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  by (wpsimp simp: set_refills_def)

crunches refill_budget_check
  for ex_nonz_cap_tp[wp]: "\<lambda>s. ex_nonz_cap_to ptr s"
  (simp: crunch_simps wp: crunch_wps)

crunches head_insufficient_loop, handle_overrun_loop
  for if_live_then_nonz_cap[wp]: if_live_then_nonz_cap
  (wp: crunch_wps update_sched_context_iflive_implies)

lemma refill_budget_check_if_live_then_nonz_cap[wp]:
  "refill_budget_check usage \<lbrace>if_live_then_nonz_cap\<rbrace>"
  apply (wpsimp wp: whileLoop_wp' get_refills_wp hoare_drop_imps
                    hoare_vcg_all_lift hoare_vcg_if_lift2
              simp: refill_budget_check_def update_refill_hd_def)
  done

crunches refill_budget_check
  for aligned[wp]: pspace_aligned
  and distinct[wp]: pspace_distinct
  and sc_at[wp]: "sc_at sc_ptr"
  and cte_wp_at[wp]: "cte_wp_at P c"
  and interrupt_irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"
  and caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"
  and no_cdt[wp]: "\<lambda>s. P (cdt s)"
  and no_revokable[wp]: "\<lambda>s. P (is_original_cap s)"
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
  and fault_tcbs_valid_states [wp]: fault_tcbs_valid_states
  and valid_ioc[wp]: "valid_ioc"
  and typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  and pred_tcb_at[wp]: "\<lambda>s. Q (pred_tcb_at proj P t s)"
  (simp: Let_def wp: crunch_wps)

lemma refill_budget_check_zombies[wp]:
  "refill_budget_check usage \<lbrace>zombies_final\<rbrace>"
  apply (wpsimp simp: refill_budget_check_defs
                  wp: hoare_drop_imp whileLoop_wp')
  done

lemma refill_budget_check_mdb [wp]:
  "refill_budget_check usage \<lbrace>valid_mdb\<rbrace>"
  by (wpsimp wp: valid_mdb_lift)

lemma refill_budget_check_hyp_refs_of[wp]:
  "refill_budget_check usage \<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace>"
  apply (wpsimp simp: refill_budget_check_defs
                  wp: hoare_drop_imp whileLoop_wp')
  done

crunches head_insufficient_loop, handle_overrun_loop
  for state_refs_of[wp]: "\<lambda>s. P (state_refs_of s)"
  (wp: crunch_wps update_sched_context_refs_of_same simp: crunch_simps ignore: update_sched_context)

lemma refill_budget_check_refs_of[wp]:
  "refill_budget_check usage \<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace>"
  unfolding refill_budget_check_def is_round_robin_def
  apply (wpsimp wp: whileLoop_wp' update_sched_context_refs_of_same get_refills_wp
                    hoare_drop_imps hoare_vcg_all_lift
         split_del: if_split)
      apply (rule_tac Q="\<lambda>_ s. P (state_refs_of s)" in hoare_strengthen_post[rotated])
       apply clarsimp
      apply (wpsimp wp:)+
  done

lemma update_refill_hd_invs[wp]:
  "update_refill_hd sc_ptr f \<lbrace>invs\<rbrace>"
  by (wpsimp simp: update_refill_hd_rewrite)

lemma update_refill_tl_invs[wp]:
  "update_refill_tl sc_ptr f \<lbrace>invs\<rbrace>"
  by (wpsimp simp: update_refill_tl_rewrite)

lemma update_sched_context_sc_refills_update_invs[wp]:
  "update_sched_context sc_ptr (sc_refills_update f) \<lbrace>invs\<rbrace>"
  by (wpsimp simp: update_sched_context_set_refills_rewrite)

lemma refill_budget_check_round_robin_invs[wp]:
  "refill_budget_check_round_robin u \<lbrace>invs\<rbrace>"
  unfolding refill_budget_check_round_robin_def
  by (wpsimp simp: refill_budget_check_round_robin_def
               wp: hoare_drop_imp update_sched_context_wp)

lemma refill_budget_check_invs[wp]:
  "refill_budget_check usage \<lbrace>invs\<rbrace>"
  unfolding refill_budget_check_def
  apply (wpsimp simp: refill_budget_check_defs
                  wp: hoare_drop_imp whileLoop_wp' hoare_vcg_if_lift2)
  done

lemma update_sched_context_valid_irq_node [wp]:
  "\<lbrace>valid_irq_node\<rbrace> update_sched_context p sc  \<lbrace>\<lambda>r. valid_irq_node\<rbrace>"
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

lemma update_sched_context_valid_sched_context[wp]:
  "\<lbrace>sc_at p and valid_sched_context x\<rbrace>
    update_sched_context p sc
   \<lbrace>\<lambda>r. valid_sched_context x\<rbrace>"
  by (wpsimp simp: update_sched_context_def wp: set_object_wp get_object_wp)

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

lemma sc_tcb_update_cur_sc_tcb:
  "\<lbrace>\<lambda>s. cur_sc_tcb s \<and>
        (sc_ptr \<noteq> cur_sc s \<or> scheduler_action s \<noteq> resume_cur_thread)\<rbrace>
   update_sched_context sc_ptr (sc_tcb_update f)
   \<lbrace>\<lambda>rv. cur_sc_tcb\<rbrace>"
   by (wpsimp simp: update_sched_context_def set_object_def get_object_def
                    cur_sc_tcb_def sc_tcb_sc_at_def obj_at_def)

lemma update_sched_context_cur_sc_tcb_None:
  "\<lbrace>cur_sc_tcb and sc_tcb_sc_at ((=) None) sc\<rbrace> update_sched_context sc f \<lbrace>\<lambda>_. cur_sc_tcb\<rbrace>"
  by (wpsimp simp: update_sched_context_def set_object_def get_object_def cur_sc_tcb_def
                   sc_tcb_sc_at_def obj_at_def)

lemma update_sched_context_cur_sc_tcb_no_change:
  "\<lbrace>cur_sc_tcb and K (\<forall>x. sc_tcb (f x) = sc_tcb x)\<rbrace>
   update_sched_context sc f
   \<lbrace>\<lambda>_. cur_sc_tcb\<rbrace>"
  by (wpsimp simp: update_sched_context_def set_object_def get_object_def cur_sc_tcb_def
                   sc_tcb_sc_at_def obj_at_def)

lemmas sc_consumed_update_cur_sc_tcb[wp] =
  update_sched_context_cur_sc_tcb_no_change [where f = "(sc_consumed_update f)" for f, simplified]

lemmas sc_refills_update_cur_sc_tcb[wp] =
  update_sched_context_cur_sc_tcb_no_change [where f = "(sc_refills_update f)" for f, simplified]

lemmas sc_yield_from_update_cur_sc_tcb[wp] =
  update_sched_context_cur_sc_tcb_no_change [where f = "(sc_yield_from_update f)" for f, simplified]

lemmas sc_ntfn_update_cur_sc_tcb[wp] =
  update_sched_context_cur_sc_tcb_no_change [where f = "(sc_ntfn_update f)" for f, simplified]

lemmas sc_replies_update_cur_sc_tcb[wp] =
  update_sched_context_cur_sc_tcb_no_change [where f = "(sc_replies_update f)" for f, simplified]

lemma sc_consumed_update_valid_idle [wp]:
  "update_sched_context p (sc_consumed_update f) \<lbrace>valid_idle\<rbrace>"
  by (wpsimp simp: update_sched_context_def set_object_def get_object_def valid_idle_def
                   obj_at_def pred_tcb_at_def)

lemma sc_consumed_update_invs[wp]:
  "update_sched_context p (sc_consumed_update f) \<lbrace>invs\<rbrace>"
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def obj_at_def
                  wp: update_sched_context_valid_objs_same update_sched_context_refs_of_same
                      update_sched_context_valid_replies)
  by (fastforce simp: replies_with_sc_upd_replies_trivial)

lemma sc_consumed_update_sym_refs[wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace> update_sched_context p (sc_consumed_update f)
   \<lbrace>\<lambda>_ s. P (state_refs_of s)\<rbrace>"
  by (wpsimp wp: update_sched_context_refs_of_same)

crunches refill_unblock_check
  for ex_nonz_cap_to[wp]: "\<lambda>s. ex_nonz_cap_to ptr s"
  (simp: crunch_simps is_round_robin_def wp: crunch_wps)

lemma refill_unblock_check_if_live_then_nonz_cap[wp]:
  "refill_unblock_check usage \<lbrace>if_live_then_nonz_cap\<rbrace>"
  apply (clarsimp simp: refill_unblock_check_defs)
  apply (wpsimp wp: whileLoop_wp' get_refills_wp hoare_drop_imps)
  done

crunches refill_unblock_check
  for aligned[wp]: pspace_aligned
  and distinct[wp]: pspace_distinct
  and sc_at[wp]: "sc_at sc_ptr"
  and cte_wp_at[wp]: "cte_wp_at P c"
  and interrupt_irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"
  and caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"
  and no_cdt[wp]: "\<lambda>s. P (cdt s)"
  and no_revokable[wp]: "\<lambda>s. P (is_original_cap s)"
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
  and fault_tcbs_valid_states [wp]: fault_tcbs_valid_states
  and valid_ioc[wp]: "valid_ioc"
  and valid_replies[wp]: valid_replies
  and valid_idle[wp]: valid_idle
  and valid_irq_node[wp]: valid_irq_node
  and valid_ioports[wp]: valid_ioports
  and cur_sc_tcb[wp]: cur_sc_tcb
  and pred_tcb_at[wp]: "\<lambda>s. Q (pred_tcb_at proj P t s)"
  (simp: Let_def is_round_robin_def wp: crunch_wps hoare_vcg_if_lift2 ignore: update_sched_context)

lemmas refill_unblock_check_typ_ats [wp] =
  abs_typ_at_lifts [OF refill_unblock_check_typ_at]

lemma refill_unblock_check_zombies[wp]:
  "refill_unblock_check sc_ptr \<lbrace>zombies_final\<rbrace>"
  apply (wpsimp simp: refill_unblock_check_defs
                  wp: hoare_drop_imp whileLoop_wp')
  done

lemma refill_unblock_check_mdb [wp]:
  "refill_unblock_check sc_ptr \<lbrace>valid_mdb\<rbrace>"
  by (wpsimp wp: valid_mdb_lift)

lemma refill_unblock_check_hyp_refs_of[wp]:
  "refill_unblock_check sc_ptr \<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace>"
  apply (wpsimp simp: refill_unblock_check_defs
                  wp: hoare_drop_imp whileLoop_wp')
  done

lemma refill_unblock_check_refs_of[wp]:
  "refill_unblock_check sc_ptr \<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace>"
  apply (wpsimp simp: refill_unblock_check_defs
                  wp: hoare_drop_imp whileLoop_wp')
  apply (clarsimp simp: state_refs_of_def)
  done

lemma refill_unblock_check_valid_state [wp]:
  "refill_unblock_check sc_ptr \<lbrace>valid_state\<rbrace>"
  apply (wpsimp simp: valid_state_def valid_pspace_def pred_conj_def)
  done

lemma refill_unblock_check_invs [wp]:
  "refill_unblock_check sc_ptr \<lbrace>invs\<rbrace>"
  apply (wpsimp simp: invs_def)
  done

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

crunches head_insufficient_loop, handle_overrun_loop
  for valid_replies_pred[wp]: "valid_replies_pred P"
  (wp: crunch_wps ignore: update_sched_context)

lemma refill_budget_check_valid_replies[wp]:
  "refill_budget_check usage \<lbrace> valid_replies_pred P \<rbrace>"
  apply (wpsimp simp: refill_budget_check_def
                  wp: get_refills_wp whileLoop_wp' hoare_drop_imps
                      hoare_vcg_all_lift hoare_vcg_if_lift2)
  done

lemma commit_time_valid_replies[wp]:
  "commit_time \<lbrace> valid_replies_pred P \<rbrace>"
  by (wpsimp simp: commit_time_def refill_budget_check_round_robin_def update_refill_tl_def
                   update_refill_hd_def
               wp: hoare_drop_imps cong: sched_context.fold_congs)

lemma sc_consumed_update_eq:
  "(\<lambda>sc. sc_consumed_update (\<lambda>v. v + x) sc) = (\<lambda>sc. sc\<lparr>sc_consumed := sc_consumed sc + x\<rparr>)"
  by auto

lemma update_sched_context_domain_time_consumed_time[wp]:
  "update_sched_context csc f \<lbrace>\<lambda>s. P (domain_time s)  (consumed_time s)\<rbrace>"
   by (wpsimp simp: update_sched_context_def wp: set_object_wp get_object_wp)

lemma cur_sc_tcb_domain_time[simp]:
  "cur_sc_tcb (s\<lparr>domain_time := k\<rparr>) = cur_sc_tcb s"
  by (clarsimp simp: cur_sc_tcb_def)

lemma commit_times_invs_helper:
  " \<lbrace>\<lambda>s. invs s \<and>
         consumed_time s = consumed \<and>
         cur_sc s = csc\<rbrace>
       do y <- update_sched_context csc (\<lambda>sc. sc\<lparr>sc_consumed := sc_consumed sc + consumed\<rparr>);
          y <- commit_domain_time;
          modify (consumed_time_update (\<lambda>_. 0))
       od
       \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                      consumed_time_update_arch.state_refs_update
                      commit_domain_time_def sc_consumed_update_eq[symmetric]
                  wp: valid_irq_node_typ hoare_vcg_imp_lift')
  done

lemma commit_time_invs:
  "commit_time \<lbrace>invs\<rbrace>"
  supply fun_upd_apply[simp del]
  apply (clarsimp simp: commit_time_def num_domains_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (case_tac "sc_active sc"; clarsimp split del: if_split simp: bind_assoc)
   apply (rule hoare_seq_ext[OF _ gets_sp])
   apply (rename_tac csc sc consumed)
   apply (case_tac "0 < consumed"; simp split del: if_split add: bind_assoc)
    apply (wpsimp wp: commit_times_invs_helper hoare_vcg_ex_lift
                simp: refill_budget_check_round_robin_def is_round_robin_def
                      update_refill_tl_def update_refill_hd_def)
   apply (clarsimp simp: obj_at_def is_sc_obj_def)
   apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                       consumed_time_update_arch.state_refs_update
                       commit_domain_time_def sc_consumed_update_eq[symmetric])
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                      consumed_time_update_arch.state_refs_update
                      commit_domain_time_def)
  done

crunches switch_sched_context
  for cur_time[wp]: "\<lambda>s. P (cur_time s)"
  and cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  (wp: crunch_wps hoare_vcg_if_lift2 simp: Let_def ignore: commit_domain_time)

lemma cur_sc_update_invs:
  "\<lbrace>\<lambda>s. valid_state s \<and> cur_tcb s \<and>
        bound_sc_tcb_at ((=) (Some sc_ptr)) (cur_thread s) s\<rbrace>
   modify (\<lambda>s. s\<lparr> cur_sc:= sc_ptr \<rparr>)
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (wpsimp simp: invs_def valid_state_def)
  apply (clarsimp simp: valid_pspace_def sym_refs_def cur_sc_tcb_def sc_tcb_sc_at_def obj_at_def
                        pred_tcb_at_def)
  apply (erule_tac x = "cur_thread s" in allE)
  apply (erule (1) valid_objsE)
  apply (clarsimp simp: valid_obj_def valid_tcb_def)
  apply (case_tac "tcb_sched_context tcb"; simp)
  apply (clarsimp simp: obj_at_def)
  apply (case_tac ko; simp)
        apply (auto simp: state_refs_of_def get_refs_def2)
  done

lemma sc_refills_update_bound_sc_tcb_at [wp]:
  "\<lbrace>\<lambda>s. bound_sc_tcb_at P (cur_thread s) s\<rbrace>
   update_sched_context p (sc_refills_update f)
   \<lbrace>\<lambda>_ s. bound_sc_tcb_at P (cur_thread s) s\<rbrace>"
  by (wpsimp simp: update_sched_context_def set_object_def get_object_def pred_tcb_at_def
                   obj_at_def)

lemma sc_consumed_update_bound_sc_tcb_at [wp]:
  "\<lbrace>\<lambda>s. bound_sc_tcb_at P (cur_thread s) s\<rbrace>
   update_sched_context p (sc_consumed_update f)
   \<lbrace>\<lambda>_ s. bound_sc_tcb_at P (cur_thread s) s\<rbrace>"
  by (wpsimp simp: update_sched_context_def set_object_def get_object_def pred_tcb_at_def
                   obj_at_def)

crunches commit_domain_time
  for valid_state [wp]: valid_state
  and cur_tcb [wp]: cur_tcb
  and fault_tcbs_valid_states [wp]: fault_tcbs_valid_states
  and bound_sc_tcb_at [wp]: "\<lambda>s. bound_sc_tcb_at ((=) (Some sc)) (cur_thread s) s"
  (simp: valid_state_def)

lemma set_refills_bound_sc_tcb_at_ct[wp]:
  "\<lbrace>\<lambda>s. bound_sc_tcb_at P (cur_thread s) s\<rbrace>
   set_refills sc_ptr refills
   \<lbrace>\<lambda>_ s. bound_sc_tcb_at P (cur_thread s) s\<rbrace>"
  by (wpsimp simp: set_refills_def update_sched_context_def set_object_def get_object_def
                   pred_tcb_at_def obj_at_def)

crunches handle_overrun_loop, head_insufficient_loop
  for bound_sc_tcb_at_ct[wp]: "\<lambda>s. bound_sc_tcb_at P (cur_thread s) s"
  (wp: crunch_wps ignore: update_sched_context)

lemma refill_budget_check_bound_sc_tcb_at_ct[wp]:
  "refill_budget_check usage \<lbrace>\<lambda>s. bound_sc_tcb_at P (cur_thread s) s\<rbrace>"
  unfolding refill_budget_check_def
  apply (wpsimp wp: whileLoop_wp' get_refills_wp hoare_drop_imps hoare_vcg_all_lift
                    hoare_vcg_if_lift2)
  done

lemma commit_time_bound_sc_tcb_at [wp]:
  "\<lbrace>\<lambda>s. bound_sc_tcb_at ((=) (Some sc)) (cur_thread s) s\<rbrace>
   commit_time
   \<lbrace>\<lambda>_ s. bound_sc_tcb_at ((=) (Some sc)) (cur_thread s) s\<rbrace>"
  by (wpsimp simp: commit_time_def sc_consumed_update_eq[symmetric]
                   refill_budget_check_round_robin_def update_refill_tl_def update_refill_hd_def
               wp: hoare_drop_imps)

lemma refill_unblock_check_bound_sc_tcb_at [wp]:
  "refill_unblock_check sc_ptr \<lbrace>\<lambda>s. bound_sc_tcb_at ((=) (Some sc)) (cur_thread s) s\<rbrace>"
  unfolding refill_unblock_check_defs
  apply (wpsimp wp: whileLoop_wp' get_refills_wp hoare_drop_imps)
  done

lemma set_next_interrupt_invs[wp]: "\<lbrace>invs\<rbrace> set_next_interrupt \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (wpsimp wp: hoare_drop_imp get_sched_context_wp dmo_setDeadline
           simp: set_next_interrupt_def)

lemma valid_state_consumed_time_update[iff]:
  "valid_state (consumed_time_update f s) = valid_state s"
  by (clarsimp simp: valid_state_def)

lemma sc_consumed_update_valid_state [wp]:
  "\<lbrace>valid_state\<rbrace> update_sched_context p (sc_consumed_update f) \<lbrace>\<lambda>_. valid_state\<rbrace>"
  by (wpsimp simp: valid_state_def valid_pspace_def
               wp: valid_irq_node_typ)

lemma sc_refills_update_valid_state [wp]:
  "\<lbrace>valid_state\<rbrace> update_sched_context p (sc_refills_update f) \<lbrace>\<lambda>_. valid_state\<rbrace>"
  by (wpsimp simp: valid_state_def valid_pspace_def
               wp: valid_irq_node_typ)

crunches head_insufficient_loop, handle_overrun_loop
  for valid_idle[wp]: valid_idle
  (wp: crunch_wps ignore: update_sched_context)

lemma refill_budget_check_valid_idle:
  "refill_budget_check usage \<lbrace>valid_idle\<rbrace>"
  unfolding refill_budget_check_def
  apply (wpsimp wp: whileLoop_wp' get_refills_wp hoare_drop_imps hoare_vcg_all_lift
                    hoare_vcg_if_lift2)
  done

lemma refill_budget_check_valid_state [wp]:
  "\<lbrace>valid_state\<rbrace> refill_budget_check usage \<lbrace>\<lambda>_. valid_state\<rbrace>"
  by (wpsimp simp: valid_state_def valid_pspace_def
               wp: valid_irq_node_typ valid_ioports_lift refill_budget_check_valid_idle)

lemma commit_time_valid_state [wp]:
  "\<lbrace>valid_state\<rbrace> commit_time \<lbrace>\<lambda>_. valid_state\<rbrace>"
  by (wpsimp simp: commit_time_def sc_consumed_update_eq[symmetric]
                   refill_budget_check_round_robin_def update_refill_tl_def update_refill_hd_def
               wp: hoare_drop_imps)

lemma commit_time_cur_tcb [wp]:
  "\<lbrace>cur_tcb\<rbrace> commit_time \<lbrace>\<lambda>_. cur_tcb\<rbrace>"
  by (wpsimp simp: commit_time_def refill_budget_check_round_robin_def update_refill_tl_def
                   update_refill_hd_def
               wp: hoare_drop_imps)

lemma commit_time_fault_tcbs_valid_states[wp]:
  "commit_time \<lbrace>fault_tcbs_valid_states\<rbrace>"
  by (wpsimp simp: commit_time_def refill_budget_check_round_robin_def update_refill_tl_def
                   update_refill_hd_def
               wp: hoare_drop_imps)

crunches switch_sched_context
  for fault_tcbs_valid_states [wp]: fault_tcbs_valid_states
  (wp: crunch_wps hoare_vcg_if_lift2 simp: Let_def ignore: commit_domain_time)

lemma switch_sched_context_invs [wp]:
  "\<lbrace>valid_state and cur_tcb\<rbrace> switch_sched_context \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: switch_sched_context_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (wpsimp simp: get_tcb_queue_def wp: cur_sc_update_invs hoare_drop_imps)
  apply (clarsimp simp: valid_state_def)
  done

lemma sc_and_timer_invs:
  "\<lbrace>valid_state and cur_tcb\<rbrace> sc_and_timer \<lbrace>\<lambda>rv. invs\<rbrace>"
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

lemma update_sched_context_ct_in_state[wp]:
  "\<lbrace> ct_in_state t \<rbrace> update_sched_context p f \<lbrace> \<lambda>rv. ct_in_state t \<rbrace>"
  by (wpsimp simp: update_sched_context_def set_object_def get_object_def obj_at_def
                      pred_tcb_at_def ct_in_state_def simp_del: fun_upd_apply) fastforce

lemma set_refills_ct_in_state[wp]:
  "\<lbrace> ct_in_state t \<rbrace> set_refills p r \<lbrace> \<lambda>rv. ct_in_state t \<rbrace>"
  by (wpsimp simp: set_refills_def wp: get_sched_context_wp)

crunches head_insufficient_loop, handle_overrun_loop
  for ct_in_state[wp]: "ct_in_state t"
  (wp: crunch_wps)

lemma refill_budget_check_ct_in_state[wp]:
  "refill_budget_check usage \<lbrace> ct_in_state t \<rbrace>"
  unfolding refill_budget_check_def
  apply (wpsimp wp: whileLoop_wp' get_refills_wp hoare_drop_imps hoare_vcg_all_lift
                    hoare_vcg_if_lift2)
  done

(* FIXME: move *)
lemma ct_in_state_domain_time_update[simp]:
  "ct_in_state st (domain_time_update f s) = ct_in_state st s"
  by (simp add: ct_in_state_def)

crunch ct_in_state[wp]: commit_time "ct_in_state t"
  (simp: crunch_simps wp: crunch_wps)

lemma refill_unblock_check_ct_in_state[wp]:
  "refill_unblock_check csc \<lbrace> ct_in_state t \<rbrace>"
  unfolding refill_unblock_check_defs
  apply (wpsimp wp: whileLoop_wp' get_refills_wp hoare_drop_imps)
  done

lemma switch_sched_context_ct_in_state[wp]:
  "\<lbrace> ct_in_state t \<rbrace> switch_sched_context \<lbrace> \<lambda>rv. ct_in_state t \<rbrace>"
  by (wpsimp simp: switch_sched_context_def get_tcb_queue_def get_sc_obj_ref_def
             wp: hoare_drop_imp hoare_vcg_if_lift2)

lemma set_next_interrupt_activatable:
  "\<lbrace>ct_in_state activatable\<rbrace> set_next_interrupt \<lbrace>\<lambda>rv. ct_in_state activatable\<rbrace>"
  apply (clarsimp simp: set_next_interrupt_def)
  apply (wpsimp simp: ct_in_state_def
      wp: hoare_drop_imp ct_in_state_thread_state_lift)
  done


lemma sc_and_timer_activatable:
  "\<lbrace>ct_in_state activatable\<rbrace> sc_and_timer \<lbrace>\<lambda>rv. ct_in_state activatable\<rbrace>"
  apply (wpsimp simp: sc_and_timer_def switch_sched_context_def get_tcb_queue_def get_sc_obj_ref_def
           wp: hoare_drop_imp modify_wp hoare_vcg_if_lift2 set_next_interrupt_activatable)
  done

crunches refill_new, refill_update
  for typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  (wp: crunch_wps)

lemma sched_context_resume_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> sched_context_resume sc_ptr
      \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by (wpsimp simp: sched_context_resume_def
      wp: get_sched_context_wp hoare_vcg_if_lift2 hoare_drop_imp)

crunch invs[wp]: set_message_info invs

crunches set_message_info, sched_context_update_consumed, unbind_from_sc
  for tcb_at[wp]: "\<lambda>s. P (tcb_at p s)"
  and cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  (wp: crunch_wps tcb_at_typ_at' maybeM_inv simp: crunch_simps)

lemma update_sched_context_tcb_at_ct[wp]:
  "\<lbrace>\<lambda>s. tcb_at (cur_thread s) s\<rbrace> update_sched_context p sc \<lbrace>\<lambda>rv s. tcb_at (cur_thread s) s\<rbrace>"
  by (wpsimp simp: update_sched_context_def set_object_def obj_at_def is_tcb_def wp: get_object_wp)

lemma sched_context_update_consumed_tcb_at_ct[wp]:
  "\<lbrace>\<lambda>s. tcb_at (cur_thread s) s\<rbrace> sched_context_update_consumed scp \<lbrace>\<lambda>rv s. tcb_at (cur_thread s) s\<rbrace>"
  by (wpsimp simp: sched_context_update_consumed_def)

lemma sched_context_update_consumed_invs[wp]:
  "sched_context_update_consumed scp \<lbrace>invs\<rbrace>"
  apply (simp add: sched_context_update_consumed_def)
  by wpsimp

lemma ssc_refs_of_Some[wp]:
  "\<lbrace>\<lambda>s. P ((state_refs_of s)(t:= insert (sc, TCBSchedContext)
          {x \<in> state_refs_of s t. snd x \<noteq> TCBSchedContext}))\<rbrace>
   set_tcb_obj_ref tcb_sched_context_update t (Some sc)
   \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (wpsimp wp: set_object_wp_strong)
  apply (erule rsubst[where P=P])
  apply (clarsimp simp: state_refs_of_def)
  apply (frule get_tcb_SomeD)
  apply (rule ext)
  apply (clarsimp simp: get_refs_def2 tcb_st_refs_of_def split: thread_state.splits)
  apply (intro conjI; fastforce)
  done

lemma ssc_refs_of_None[wp]:
  "\<lbrace>\<lambda>s. P ((state_refs_of s)(t:= {x \<in> state_refs_of s t. snd x \<noteq> TCBSchedContext}))\<rbrace>
   set_tcb_obj_ref tcb_sched_context_update t None
   \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (wpsimp wp: set_object_wp_strong)
  apply (erule rsubst[where P=P])
  apply (clarsimp simp: state_refs_of_def)
  apply (frule get_tcb_SomeD)
  apply (rule ext)
  apply (clarsimp simp: get_refs_def2 tcb_st_refs_of_def split: thread_state.splits)
  apply (intro conjI; fastforce)
  done

lemma zombies_kheap_update:
  "\<lbrakk> zombies_final s; obj_at (same_caps ko) t s \<rbrakk>
   \<Longrightarrow> zombies_final (s\<lparr>kheap := kheap s(t \<mapsto> ko)\<rparr>)"
  apply (simp add: zombies_final_def is_final_cap'_def2, elim allEI)
  apply (clarsimp simp: cte_wp_at_after_update fun_upd_def)
  done


text \<open>bind/unbind invs lemmas\<close>

global_interpretation set_ntfn_obj_ref: non_reply_op "set_ntfn_obj_ref f ref new"
  by unfold_locales (auto intro: update_sk_obj_ref_sk_obj_at_pred)

global_interpretation sched_context_bind_ntfn: non_reply_op "sched_context_bind_ntfn sc ntfn"
  by unfold_locales (wpsimp simp: sched_context_bind_ntfn_def)

lemma sched_context_bind_ntfn_invs[wp]:
  "\<lbrace>invs and ex_nonz_cap_to sc and ex_nonz_cap_to ntfn
    and obj_at (\<lambda>ko. \<exists>ntfn. ko = Notification ntfn \<and> (ntfn_sc ntfn = None)) ntfn
    and sc_ntfn_sc_at (\<lambda>ntfn'. ntfn' = None) sc\<rbrace>
   sched_context_bind_ntfn sc ntfn
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wpsimp simp: sched_context_bind_ntfn_def invs_def valid_state_def valid_pspace_def
                      update_sk_obj_ref_def
                  wp: get_simple_ko_wp valid_irq_node_typ set_simple_ko_valid_objs
                      simple_obj_set_prop_at valid_ioports_lift update_sched_context_valid_idle)
  apply (clarsimp simp: obj_at_def is_ntfn sc_ntfn_sc_at_def)
  apply (case_tac "sc=ntfn", simp)
  apply safe
    apply (frule valid_objs_valid_sched_context_size)
     apply fastforce
    apply (erule (1) valid_objsE)
    apply (clarsimp simp: valid_obj_def valid_ntfn_def obj_at_def is_sc_obj_def split: ntfn.splits)
   apply (erule delta_sym_refs)
    apply (fastforce simp: state_refs_of_def obj_at_def split: if_split_asm)
   apply (clarsimp simp: state_refs_of_def get_refs_def2
                  dest!: symreftype_inverse' split: if_splits)
  apply (fastforce simp: idle_sc_no_ex_cap)
  done

lemma sched_context_unbind_ntfn_invs[wp]:
  notes refs_of_simps[simp del]
  shows
  "\<lbrace>invs\<rbrace> sched_context_unbind_ntfn sc \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: sched_context_unbind_ntfn_def maybeM_def get_sc_obj_ref_def)
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def update_sk_obj_ref_def
                  wp: valid_irq_node_typ set_simple_ko_valid_objs get_simple_ko_wp
                      get_sched_context_wp valid_ioports_lift update_sched_context_valid_idle)
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
    apply (fastforce simp: obj_at_def refs_of_simps split: if_splits)
   apply (fastforce simp: get_refs_def2 refs_of_def obj_at_def
                   split: if_splits)
  apply (clarsimp simp: valid_idle_def obj_at_def)
  done

lemmas is_schedulable_inv[wp] = is_schedulable_wp[where P="\<lambda>_. P" for P, simplified]

declare reprogram_timer_update_arch.state_refs_update[simp]

crunches sched_context_resume, test_possible_switch_to, tcb_release_remove, postpone
  for aligned[wp]: pspace_aligned
  and distinct[wp]: pspace_distinct
  and iflive[wp]: if_live_then_nonz_cap
  and typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  and sc_at[wp]: "sc_at sc_ptr"
  and tcb_at[wp]: "tcb_at tptr"
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
  and fault_tcbs_valid_states[wp]: fault_tcbs_valid_states
  and pred_tcb_at[wp]: "\<lambda>s. Q (pred_tcb_at proj P t s)"
  (wp: crunch_wps simp: crunch_simps)

lemma set_tcb_yt_update_bound_sc_tcb_at[wp]:
  "\<lbrace>bound_sc_tcb_at P t\<rbrace> set_tcb_obj_ref tcb_yield_to_update scp tcb \<lbrace>\<lambda>rv. bound_sc_tcb_at P t\<rbrace>"
  by (wpsimp simp: set_tcb_obj_ref_def pred_tcb_at_def obj_at_def get_tcb_rev wp: set_object_wp_strong)

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
  by (wpsimp simp: tcb_release_enqueue_def wp: mapM_wp' cong: if_cong)

lemma postpone_valid_replies[wp]:
  "postpone sc_ptr \<lbrace> valid_replies_pred P \<rbrace>"
  by (wpsimp simp: postpone_def wp: hoare_drop_imps)

lemma sched_context_resume_valid_replies[wp]:
  "sched_context_resume sc_ptr \<lbrace> valid_replies_pred P \<rbrace>"
  by (wpsimp simp: sched_context_resume_def wp: hoare_drop_imps)

lemma possible_switch_to_cur_sc_tcb[wp]:
  "\<lbrace>cur_sc_tcb\<rbrace> possible_switch_to tcb \<lbrace>\<lambda>_. cur_sc_tcb\<rbrace>"
  by (wpsimp simp: possible_switch_to_def tcb_sched_action_def set_tcb_queue_def get_tcb_queue_def
                   thread_get_def reschedule_required_def set_scheduler_action_def
                   is_schedulable_def get_tcb_obj_ref_def cur_sc_tcb_def sc_tcb_sc_at_def
                   obj_at_def)

lemma test_possible_switch_to_cur_sc_tcb[wp]:
  "\<lbrace>cur_sc_tcb\<rbrace> test_possible_switch_to tcb \<lbrace>\<lambda>_. cur_sc_tcb\<rbrace>"
  by (wpsimp simp: test_possible_switch_to_def)

(* FIXME: move to Invariants_AI *)
lemma cur_sc_tcb_release_queue_update[simp]:
  "cur_sc_tcb (release_queue_update f s) = cur_sc_tcb s"
  by (clarsimp simp: cur_sc_tcb_def sc_tcb_sc_at_def)

lemma tcb_release_enqueue_cur_sc_tcb[wp]:
  "\<lbrace>cur_sc_tcb\<rbrace> tcb_release_enqueue tcb_ptr \<lbrace>\<lambda>_. cur_sc_tcb\<rbrace>"
  by (wpsimp simp: tcb_release_enqueue_def get_sc_time_def get_tcb_sc_def get_tcb_obj_ref_def
                   thread_get_def
             cong: if_cong wp: mapM_wp_inv)

lemma postpone_cur_sc_tcb[wp]:
  "\<lbrace>cur_sc_tcb\<rbrace> postpone sc \<lbrace>\<lambda>_. cur_sc_tcb\<rbrace>"
  by (wpsimp simp: postpone_def tcb_sched_action_def set_tcb_queue_def get_tcb_queue_def
                   thread_get_def get_sc_obj_ref_def)

lemma sched_context_resume_cur_sc_tcb[wp]:
  "\<lbrace>cur_sc_tcb\<rbrace> sched_context_resume sc \<lbrace>\<lambda>_. cur_sc_tcb\<rbrace>"
  by (wpsimp simp: sched_context_resume_def wp: hoare_drop_imp)

lemma set_scheduler_action_cur_sc_tcb [wp]:
  "\<lbrace>\<lambda>s. cur_sc_tcb s \<and> action \<noteq> resume_cur_thread\<rbrace> set_scheduler_action action \<lbrace>\<lambda>_. cur_sc_tcb\<rbrace>"
  by (wpsimp simp: set_scheduler_action_def cur_sc_tcb_def sc_tcb_sc_at_def obj_at_def)

lemma tcb_sched_action_cur_sc_tcb [wp]:
  "\<lbrace>cur_sc_tcb\<rbrace> tcb_sched_action action thread \<lbrace>\<lambda>_. cur_sc_tcb\<rbrace>"
  by (wpsimp simp: tcb_sched_action_def set_tcb_queue_def)

lemma reschedule_required_cur_sc_tcb [wp]:
  "\<lbrace>cur_sc_tcb\<rbrace> reschedule_required \<lbrace>\<lambda>_. cur_sc_tcb\<rbrace>"
  by (wpsimp simp: reschedule_required_def set_scheduler_action_def tcb_sched_action_def
                   set_tcb_queue_def get_tcb_queue_def thread_get_def is_schedulable_def
                   cur_sc_tcb_def sc_tcb_sc_at_def obj_at_def)

lemma sched_context_bind_tcb_invs[wp]:
  "\<lbrace>invs
    and bound_sc_tcb_at ((=) None) tcb and ex_nonz_cap_to tcb
    and sc_tcb_sc_at ((=) None) sc and ex_nonz_cap_to sc\<rbrace>
   sched_context_bind_tcb sc tcb
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (clarsimp simp: sched_context_bind_tcb_def invs_def valid_state_def valid_pspace_def)
  apply (wpsimp wp: valid_irq_node_typ obj_set_prop_at get_sched_context_wp ssc_refs_of_Some
                    update_sched_context_valid_objs_same valid_ioports_lift
                    update_sched_context_iflive_update update_sched_context_refs_of_update
                    update_sched_context_cur_sc_tcb_None update_sched_context_valid_idle
                    hoare_vcg_all_lift hoare_vcg_conj_lift | wp set_tcb_obj_ref_wp)+
  apply (fastforce simp: obj_at_def tcb_cap_cases_def tcb_st_refs_of_def is_sc_obj_def
                         pred_tcb_at_def sc_tcb_sc_at_def valid_sched_context_def
                         is_tcb valid_idle_def state_refs_of_def get_refs_def2
                   elim: ex_cap_to_after_update' delta_sym_refs valid_objs_valid_sched_context_size
                  dest!: symreftype_inverse' split: if_splits)
  done

lemma maybe_sched_context_bind_tcb_invs[wp]:
  "\<lbrace>invs and (\<lambda>s. tcb_at tcb s \<and> (bound_sc_tcb_at (\<lambda>x. x \<noteq> Some sc) tcb s \<longrightarrow>
                    ex_nonz_cap_to sc s \<and> ex_nonz_cap_to tcb s
                  \<and> sc_tcb_sc_at ((=) None) sc s \<and> bound_sc_tcb_at ((=) None) tcb s))\<rbrace>
   maybe_sched_context_bind_tcb sc tcb
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  unfolding maybe_sched_context_bind_tcb_def
  apply (wpsimp simp: get_tcb_obj_ref_def wp: thread_get_wp)
  apply (fastforce simp: pred_tcb_at_def obj_at_def is_tcb)
  done

lemma sched_context_unbind_valid_replies[wp]:
  "tcb_release_remove tcb_ptr \<lbrace> valid_replies_pred P \<rbrace>"
  by (wpsimp simp: tcb_release_remove_def)

crunches tcb_release_remove, tcb_sched_action, set_tcb_obj_ref
  for cur_sc_tcb[wp]: cur_sc_tcb
  and cur_sc[wp]: "\<lambda>s. P (cur_sc s)"
  and cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  and scheduler_action[wp]: "\<lambda>s. P (scheduler_action s)"
  (simp: crunch_simps)

lemma reschedule_required_cur_sc [wp]:
  "\<lbrace>\<lambda>s. P (cur_sc s)\<rbrace> reschedule_required \<lbrace>\<lambda>rv s. P (cur_sc s)\<rbrace>"
  by (wpsimp simp: reschedule_required_def set_scheduler_action_def tcb_sched_action_def
                   set_tcb_queue_def get_tcb_queue_def thread_get_def is_schedulable_def
                   cur_sc_tcb_def sc_tcb_sc_at_def obj_at_def)

lemma reschedule_required_scheduler_action [wp]:
  "\<lbrace>\<lambda>s. True\<rbrace>
   reschedule_required
   \<lbrace>\<lambda>rv s. scheduler_action s \<noteq> resume_cur_thread\<rbrace>"
  by (wpsimp simp: reschedule_required_def set_scheduler_action_def tcb_sched_action_def
                   set_tcb_queue_def get_tcb_queue_def thread_get_def is_schedulable_def
                   cur_sc_tcb_def sc_tcb_sc_at_def obj_at_def)

lemma sched_context_unbind_tcb_invs_helper:
  "\<lbrace>(\<lambda>s. invs s \<and> sc_ptr \<noteq> idle_sc_ptr \<and> (\<exists>n. ko_at (SchedContext sc n) sc_ptr s)
      \<and> (\<exists>y. sc_tcb sc = Some y))
    and (\<lambda>s. sc_ptr \<noteq> cur_sc s \<or> scheduler_action s \<noteq> resume_cur_thread)\<rbrace>
   do y <- tcb_sched_action tcb_sched_dequeue (the (sc_tcb sc));
      y <- tcb_release_remove (the (sc_tcb sc));
      y <- set_tcb_obj_ref tcb_sched_context_update (the (sc_tcb sc)) None;
      set_sc_obj_ref sc_tcb_update sc_ptr None
   od
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wpsimp simp: sched_context_unbind_tcb_def invs_def valid_state_def
                      valid_pspace_def sc_tcb_sc_at_def obj_at_def is_tcb
            simp_del: fun_upd_apply disj_not1
                  wp: valid_irq_node_typ obj_set_prop_at get_sched_context_wp valid_ioports_lift
                      sc_tcb_update_cur_sc_tcb hoare_vcg_disj_lift update_sched_context_valid_idle)
  apply (rename_tac tptr)
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
    subgoal by (fastforce simp: get_refs_def2 image_iff refs_of_def refs_of_sc_def
                          dest!: symreftype_inverse')
   apply clarsimp
   apply (simp split: if_split_asm)
    subgoal by (fastforce simp: get_refs_def2 image_iff refs_of_def refs_of_sc_def
                          dest!: symreftype_inverse')
   apply (intro conjI; clarsimp simp: state_refs_of_def get_refs_def2)
  apply (drule_tac p=tptr in if_live_then_nonz_capD2, simp, simp add: live_def)
  apply (fastforce dest: idle_no_ex_cap)
  done

lemma reschedule_required_sc_ptr [wp]:
  "\<lbrace>\<lambda>s. (\<exists>n. ko_at (SchedContext sc n) sc_ptr s)\<rbrace>
   reschedule_required
   \<lbrace>\<lambda>rv s. (\<exists>n. ko_at (SchedContext sc n) sc_ptr s)\<rbrace>"
  by (wpsimp simp: reschedule_required_def set_scheduler_action_def tcb_sched_action_def
                   set_tcb_queue_def get_tcb_queue_def thread_get_def is_schedulable_def
                   cur_sc_tcb_def sc_tcb_sc_at_def obj_at_def)

lemma sched_context_unbind_tcb_invs[wp]:
  notes refs_of_simps[simp del]
  shows "\<lbrace>\<lambda>s. invs s \<and> sc_ptr \<noteq> idle_sc_ptr\<rbrace> sched_context_unbind_tcb sc_ptr \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: sched_context_unbind_tcb_def)
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (simp add: assert_opt_def2)
  apply (rule hoare_seq_ext[OF _ assert_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
            simp_del: disj_not1
                  wp: sched_context_unbind_tcb_invs_helper valid_irq_node_typ valid_ioports_lift
                      hoare_vcg_disj_lift)
  apply (clarsimp simp: invs_def valid_state_def valid_pspace_def cur_sc_tcb_def sc_tcb_sc_at_def
                        obj_at_def)
  done

lemma maybe_sched_context_unbind_tcb_invs[wp]:
  notes refs_of_simps[simp del]
  shows "\<lbrace>\<lambda>s. invs s \<and> tcb_at tcb_ptr s \<and>
              (\<forall>xa. bound_sc_tcb_at (\<lambda>sc. sc = Some xa) tcb_ptr s \<longrightarrow>
                    (xa \<noteq> idle_sc_ptr))\<rbrace>
         maybe_sched_context_unbind_tcb tcb_ptr
         \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: maybe_sched_context_unbind_tcb_def)
  apply (wpsimp simp: get_tcb_obj_ref_def wp: thread_get_wp)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb)
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
  assumes rep: "valid_replies_2 rs_with_sc rs_blocked"
  assumes sub: "set rs \<subseteq> {r. (r,sc_ptr) \<in> rs_with_sc}"
  shows "valid_replies_2 (replies_with_sc_upd_replies rs sc_ptr rs_with_sc) rs_blocked"
proof -
  note subs = replies_with_sc_upd_replies_subset[OF sub]
  note subf = subs[THEN image_mono[where f=fst], THEN subset_trans]
  show ?thesis using rep by (clarsimp simp: valid_replies_defs subf inj_on_subset[OF _ subs])
qed

lemma replies_with_sc_upd_replies_new_valid_replies:
  "valid_replies_2 rs_with_sc rs_blocked
   \<Longrightarrow> set rs \<subseteq> fst ` rs_blocked
   \<Longrightarrow> \<forall>x\<in>(set rs). x \<notin> fst ` rs_with_sc
   \<Longrightarrow> valid_replies_2 (replies_with_sc_upd_replies rs sc_ptr rs_with_sc) rs_blocked"
  unfolding valid_replies_2_def replies_with_sc_upd_replies_def
  apply safe
   apply (clarsimp split: if_splits)
    apply (clarsimp simp: in_mono)
   apply (subgoal_tac "a \<in> fst ` rs_with_sc")
    apply (clarsimp simp: in_mono)
   apply (clarsimp simp: image_def)
   apply (rule_tac x="(a,b)" in bexI; simp)
  apply (clarsimp simp: inj_on_def image_def; safe; force)
  done

lemma sc_replies_sc_at_subset_replies_with_sc:
  assumes "sc_replies_sc_at (\<lambda>rs'. set rs \<subseteq> set rs') sc_ptr s"
  shows "set rs \<subseteq> {r. (r, sc_ptr) \<in> replies_with_sc s}"
  using assms by (auto simp: replies_with_sc_def sc_replies_sc_at_def obj_at_def)

lemmas replies_with_sc_upd_replies_subset' =
  replies_with_sc_upd_replies_subset[OF sc_replies_sc_at_subset_replies_with_sc]

lemmas replies_with_sc_upd_replies_subset_valid_replies_2 =
  replies_with_sc_upd_replies_subset_valid_replies[OF _ sc_replies_sc_at_subset_replies_with_sc]

lemmas replies_with_sc_upd_replies_nil =
  replies_with_sc_upd_replies_subset[of "[]", simplified]

lemmas replies_with_sc_upd_replies_nil_valid_replies =
  replies_with_sc_upd_replies_subset_valid_replies[where rs="[]", simplified]

lemma set_sc_replies_nil_valid_replies[wp]:
  "set_sc_obj_ref sc_replies_update sc_ptr [] \<lbrace> valid_replies \<rbrace>"
  by (wpsimp wp: update_sched_context_valid_replies
           simp: replies_with_sc_upd_replies_subset_valid_replies)

lemma set_reply_obj_ref_cur_sc_tcb[wp]:
  "\<lbrace>cur_sc_tcb\<rbrace> set_reply_obj_ref update r sc \<lbrace>\<lambda>rv. cur_sc_tcb\<rbrace>"
  by (wpsimp simp: update_sk_obj_ref_def)

lemma sched_context_unbind_reply_invs[wp]:
  "\<lbrace>invs\<rbrace> sched_context_unbind_reply sc_ptr \<lbrace>\<lambda>rv. invs\<rbrace>"
  supply fun_upd_apply[simp del]
  apply (wpsimp wp: valid_irq_node_typ hoare_vcg_conj_lift valid_ioports_lift
                    update_sched_context_valid_idle
              simp: sched_context_unbind_reply_def invs_def valid_state_def valid_pspace_def)
  apply (intro conjI)
   apply clarsimp
   apply (rule_tac V="sc_ptr \<noteq> hd (sc_replies sc)" in revcut_rl)
    apply (case_tac "sc_replies sc"; clarsimp)
    apply (clarsimp simp: obj_at_def)
    apply (erule (1) pspace_valid_objsE)
    apply (clarsimp simp: valid_obj_def valid_sched_context_def obj_at_def is_reply)
   supply fun_upd_apply[simp]
   apply (clarsimp cong: conj_cong)
   apply (rule_tac rfs'="state_refs_of s" in delta_sym_refs
          ; clarsimp simp: obj_at_def split: if_splits
          ; clarsimp simp: in_state_refs_of_iff get_refs_def2 refs_of_rev
                    split: option.splits)
   apply (rename_tac s sc n y reply sc' rs' n')
   apply (case_tac "sc_replies sc"; case_tac "sc_replies sc'"; clarsimp)
   apply (rename_tac s sc n sc_ptr' reply sc' rs' n' r rs)
   apply (frule_tac x=sc_ptr and y=r and tp=ReplySchedContext in sym_refsE
          ; clarsimp simp: in_state_refs_of_iff get_refs_def2)
  apply (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def)
  done

text \<open>more invs rules\<close>

crunches postpone
  for valid_irq_node[wp]: valid_irq_node
  (wp: crunch_wps simp: crunch_simps)

lemma postpone_invs[wp]:
  "postpone t \<lbrace>invs\<rbrace>"
  by (wpsimp simp: invs_def valid_state_def valid_pspace_def wp: valid_ioports_lift)

lemma sched_context_resume_invs[wp]:
  "\<lbrace>invs\<rbrace> sched_context_resume scptr \<lbrace>\<lambda>_. invs\<rbrace>"
  by (wpsimp simp: sched_context_resume_def get_tcb_queue_def is_schedulable_def is_tcb
               wp: thread_get_wp)

lemma set_sc_obj_ref_invs_no_change:
  "\<lbrakk> \<forall>sc. sc_replies (f (\<lambda>_. x) sc) = sc_replies sc;
     \<forall>sc. sc_tcb (f (\<lambda>_. x) sc) = sc_tcb sc;
     \<forall>sc. sc_ntfn (f (\<lambda>_. x) sc) = sc_ntfn sc;
     \<forall>sc. sc_yield_from (f (\<lambda>_. x) sc) = sc_yield_from sc \<rbrakk>
   \<Longrightarrow> \<lbrace>invs and K (p \<noteq> idle_sc_ptr)\<rbrace>
       set_sc_obj_ref f p x
       \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def obj_at_def
                  wp: update_sched_context_valid_objs_update valid_irq_node_typ
                      update_sched_context_iflive_implies
                      update_sched_context_refs_of_same
                      update_sc_but_not_sc_replies_valid_replies_2
                      update_sched_context_valid_idle
                      update_sched_context_cur_sc_tcb_no_change
            simp_del: fun_upd_apply)
  apply (clarsimp simp: valid_sched_context_def live_sc_def)
  done

lemma set_sc_obj_ref_not_ko_at_wp[wp]:
  "\<lbrace>\<lambda>s. \<forall>sc' n'. ko_at (SchedContext sc' n') p s \<longrightarrow> sc \<noteq> f (\<lambda>_. x) sc' \<or> n \<noteq> n'\<rbrace>
   set_sc_obj_ref f p x
   \<lbrace>\<lambda>_ s. \<not>ko_at (SchedContext sc n) p s\<rbrace>"
  unfolding update_sched_context_def
  apply (wpsimp wp: set_object_wp get_object_wp)
  apply (clarsimp simp: obj_at_def)
  done

lemma maybe_add_empty_tail_invs[wp]:
  "\<lbrace>invs and K (sc_ptr \<noteq> idle_sc_ptr)\<rbrace>
   maybe_add_empty_tail sc_ptr
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (wpsimp simp: maybe_add_empty_tail_def refill_add_tail_def is_round_robin_def
                  wp: set_sc_obj_ref_invs_no_change hoare_vcg_all_lift hoare_vcg_imp_lift'
                      hoare_vcg_disj_lift )
  done

lemma refill_new_invs[wp]:
  "\<lbrace>invs and K (sc_ptr \<noteq> idle_sc_ptr)\<rbrace>
   refill_new sc_ptr max_refills budget period
   \<lbrace>\<lambda>_. invs\<rbrace>"
  by (wpsimp simp: refill_new_def split_del: if_split
               wp: set_sc_obj_ref_invs_no_change hoare_vcg_all_lift hoare_vcg_imp_lift'
                   hoare_vcg_disj_lift )


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

lemma tcb_sched_action_invs[wp]:
  "\<lbrace>invs\<rbrace> tcb_sched_action action thread \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (wpsimp simp: tcb_sched_action_def set_tcb_queue_def get_tcb_queue_def
             wp: hoare_drop_imps hoare_vcg_all_lift)

lemma tcb_release_remove_invs[wp]:
  "\<lbrace>invs\<rbrace> tcb_release_remove thread \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (wpsimp simp: tcb_release_remove_def tcb_sched_dequeue_def
             wp: hoare_drop_imps hoare_vcg_all_lift)

lemma set_scheduler_action_invs[wp]:
  "\<lbrace>invs and K (action \<noteq> resume_cur_thread)\<rbrace> set_scheduler_action action \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wpsimp simp: set_scheduler_action_def)
  apply (clarsimp simp: invs_def valid_state_def cur_sc_tcb_def sc_tcb_sc_at_def obj_at_def)
  done

lemma reschedule_required_invs[wp]:
  "\<lbrace>invs\<rbrace> reschedule_required \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (wpsimp simp: reschedule_required_def wp: hoare_drop_imps hoare_vcg_all_lift)

lemma possible_switch_to_invs[wp]:
  "\<lbrace>invs\<rbrace> possible_switch_to target \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (wpsimp simp: possible_switch_to_def)

lemma update_sched_context_ex_cap_cur_thread [wp]:
  "\<lbrace>\<lambda>s. ex_nonz_cap_to (cur_thread s) s\<rbrace>
     update_sched_context ptr val \<lbrace>\<lambda>rv s. ex_nonz_cap_to (cur_thread s) s\<rbrace>"
  apply (wpsimp simp: update_sched_context_def obj_at_def
          wp: set_object_wp get_object_wp ex_nonz_cap_to_pres)
  apply (rule ex_cap_to_after_update[simplified fun_upd_apply[symmetric]], simp)
  by (clarsimp simp: obj_at_def)

lemma refill_unblock_check_tcb_at_ct[wp]:
  "refill_unblock_check scp \<lbrace>\<lambda>s. tcb_at (cur_thread s) s\<rbrace>"
  apply (rule hoare_lift_Pf[where f="\<lambda>s. cur_thread s", rotated], wp)
  apply wpsimp
  done

lemma refill_unblock_check_ex_nonz_cap_to_ct[wp]:
    "\<lbrace>\<lambda>s. ex_nonz_cap_to (cur_thread s) s\<rbrace> refill_unblock_check scp
       \<lbrace>\<lambda>rv s. ex_nonz_cap_to (cur_thread s) s\<rbrace>"
  apply (rule hoare_lift_Pf[where f="\<lambda>s. cur_thread s", rotated], wp)
  apply wpsimp
  done

lemma refill_unblock_check_state_refs_of_ct[wp]:
  "refill_unblock_check scp \<lbrace>\<lambda>s. P (state_refs_of s) (cur_thread s)\<rbrace>"
  apply (clarsimp simp: refill_unblock_check_defs)
  apply (rule hoare_seq_ext_skip, solves wpsimp)+
  apply (rule hoare_when_cases, simp)
  apply (rule hoare_seq_ext_skip, solves wpsimp)+
  apply (rule hoare_seq_ext_skip)
   apply (wpsimp simp: set_refills_def
                   wp: update_sched_context_wp get_refills_wp)
   apply (clarsimp simp: state_refs_of_def obj_at_def
                 intro!: ext elim!: rsubst[where P="\<lambda>x. P x (cur_thread s)" for s])+
  apply (wpsimp simp: set_refills_def
                  wp: update_sched_context_wp get_refills_wp whileLoop_wp')
   apply (clarsimp simp: state_refs_of_def obj_at_def
                 intro!: ext elim!: rsubst[where P="\<lambda>x. P x (cur_thread s)" for s])+
  done

lemma refill_unblock_check_it_ct[wp]:
  "refill_unblock_check scp \<lbrace>\<lambda>s. P (idle_thread s) (cur_thread s)\<rbrace>"
  apply (wpsimp simp: refill_unblock_check_defs set_refills_def update_sched_context_def
                      set_object_def
                  wp: get_refills_wp get_object_wp whileLoop_wp')
  done

lemma get_sc_refill_capacity_sp:
  "\<lbrace>\<lambda>s. P s \<and> (\<exists>n. ko_at (SchedContext sc n) sc_ptr s)\<rbrace>
   get_sc_refill_capacity sc_ptr usage
   \<lbrace> \<lambda>rv. K( rv = sc_refill_capacity usage sc) and P \<rbrace>"
  apply (clarsimp simp: get_sc_refill_capacity_def)
  apply wpsimp
  by (clarsimp simp: obj_at_def refill_capacity_def)

lemma maybe_sched_context_unbind_tcb_lift:
  assumes A: "\<And>scp. sched_context_unbind_tcb scp \<lbrace>P\<rbrace>"
  shows "\<And>tp. maybe_sched_context_unbind_tcb tp \<lbrace>P\<rbrace>"
  unfolding maybe_sched_context_unbind_tcb_def
  by (wpsimp wp: A hoare_drop_imps)

lemma maybe_sched_context_bind_tcb_lift:
  assumes A: "sched_context_bind_tcb sc_ptr tcb_ptr \<lbrace>P\<rbrace>"
  shows "maybe_sched_context_bind_tcb sc_ptr tcb_ptr \<lbrace>P\<rbrace>"
  unfolding maybe_sched_context_bind_tcb_def
  by (wpsimp wp: A hoare_drop_imps)

(* sched_context_yield_to is moved to the start of SchedContextInv_AI
because it needs to be after Ipc_AI *)

end
