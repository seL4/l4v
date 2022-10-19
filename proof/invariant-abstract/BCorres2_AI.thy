(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory BCorres2_AI
imports
  ArchEmptyFail_AI
begin

locale BCorres2_AI =
  fixes state  :: "'a::state_ext itself"
  assumes handle_arch_fault_reply_bcorres[wp]:
    "\<And>a b c d.
      bcorres (handle_arch_fault_reply a b c d :: 'a state \<Rightarrow> _)
              (handle_arch_fault_reply a b c d)"
  assumes arch_get_sanitise_register_info_bcorres[wp]:
    "\<And>t. bcorres (arch_get_sanitise_register_info t :: 'a state \<Rightarrow> _)
                  (arch_get_sanitise_register_info t)"
  assumes make_arch_fault_msg_bcorres[wp]:
    "\<And> a b.
      bcorres (make_arch_fault_msg a b :: 'a state \<Rightarrow> _)
              (make_arch_fault_msg a b)"
  assumes arch_switch_to_thread_bcorres[wp]:
    "\<And>t. bcorres (arch_switch_to_thread t :: 'a state \<Rightarrow> _)
        (arch_switch_to_thread t)"
  assumes arch_switch_to_idle_thread_bcorres[wp]:
    "bcorres (arch_switch_to_idle_thread :: 'a state \<Rightarrow> _)
        arch_switch_to_idle_thread"

crunch (bcorres)bcorres[wp]: deleting_irq_handler truncate_state
  (simp: gets_the_def swp_def)

lemma update_restart_pc_bcorres[wp]:
  "bcorres (update_restart_pc t) (update_restart_pc t)"
  by (wp
      | clarsimp simp: update_restart_pc_def as_user_def bind_select_f_bind'
                split: prod.splits)+

crunch (bcorres)bcorres[wp]: suspend, finalise_cap truncate_state

definition all_but_exst where
  "all_but_exst P \<equiv> (\<lambda>s. P (kheap s) (cdt s) (is_original_cap s)
                      (cur_thread s) (idle_thread s)
                      (machine_state s) (interrupt_irq_node s)
                      (interrupt_states s) (arch_state s))"

lemma ef_mk_ef: "empty_fail f \<Longrightarrow> mk_ef (f s) = f s"
  apply (clarsimp simp add: empty_fail_def mk_ef_def)
  apply (drule_tac x=s in spec)
  apply (case_tac "f s")
  apply force
  done

lemma all_but_obvious: "all_but_exst (\<lambda>a b c d e f g h i.
                    x = \<lparr>kheap = a, cdt = b, is_original_cap = c,
                     cur_thread = d, idle_thread = e,
                     machine_state = f, interrupt_irq_node = g,
                     interrupt_states = h, arch_state = i, exst = (exst x)\<rparr>) x"
  apply (simp add: all_but_exst_def)
  done

lemma bluh: assumes a: "x =
        \<lparr>kheap = kheap ba, cdt = cdt ba,
           is_original_cap = is_original_cap ba,
           cur_thread = cur_thread ba, idle_thread = idle_thread ba,
           machine_state = machine_state ba,
           interrupt_irq_node = interrupt_irq_node ba,
           interrupt_states = interrupt_states ba,
           arch_state = arch_state ba, exst = exst x\<rparr>"
     shows "x\<lparr>exst := exst ba\<rparr> = ba"
  apply (subst a)
  apply simp
  done

lemma valid_cs_trans_state[simp]: "valid_cs a b (trans_state g s) = valid_cs a b s"
  by(simp add: valid_cs_def)

lemmas obj_at[simp] = more_update.obj_at_update[of a b g s for a b g s]

lemma valid_tcb_state[simp]: "valid_tcb_state a (trans_state g s) = valid_tcb_state a s"
  by (simp add: valid_tcb_state_def split: thread_state.splits)

lemma valid_bound_ntfn[simp]: "valid_bound_ntfn a (trans_state g s) = valid_bound_ntfn a s"
  by (simp add: valid_bound_ntfn_def split: option.splits)

lemma valid_arch_tcb_trans[simp]: "valid_arch_tcb t (trans_state g s) = valid_arch_tcb t s"
  by (auto elim: valid_arch_tcb_pspaceI)

lemma valid_tcb_trans_state[simp]: "valid_tcb a b (trans_state g s) = valid_tcb a b s"
  apply (simp add: valid_tcb_def)
  done

lemmas valid_bound_tcb[simp] = valid_bound_tcb_exst[of a g s for a g s]

lemma valid_ep_trans_state[simp]: "valid_ep a (trans_state g s) = valid_ep a s"
  apply (simp add: valid_ep_def split: endpoint.splits)
  done

lemma valid_ntfn_trans_state[simp]: "valid_ntfn a (trans_state g s) = valid_ntfn a s"
  apply (simp add: valid_ntfn_def split: ntfn.splits)
  done

lemma valid_obj_trans_state[simp]: "valid_obj a b (trans_state g s) = valid_obj a b s"
  apply (simp add: valid_obj_def
              split: kernel_object.splits option.splits)
  done

lemma dxo_ex: "((),x :: det_ext state) \<in> fst (do_extended_op f s) \<Longrightarrow>
       \<exists>e :: det_ext. x = (trans_state (\<lambda>_. e) s)"
  apply (clarsimp simp add: do_extended_op_def
                            bind_def gets_def in_monad
                            select_f_def mk_ef_def
                            trans_state_update'
                            wrap_ext_op_det_ext_ext_def)
  apply force
  done


locale is_extended' =
  fixes f :: "'a det_ext_monad"
  assumes a: "\<And>P. \<lbrace>all_but_exst P\<rbrace> f \<lbrace>\<lambda>_. all_but_exst P\<rbrace>"

context is_extended' begin

lemmas v = use_valid[OF _ a, OF _ all_but_obvious,simplified all_but_exst_def, THEN bluh]

lemma ex_st: "(a,x :: det_ext state) \<in> fst (f s) \<Longrightarrow>
       \<exists>e :: det_ext. x = (trans_state (\<lambda>_. e) s)"
  apply (drule v)
  apply (simp add: trans_state_update')
  apply (rule_tac x="exst x" in exI)
  apply simp
  done

lemmas all_but_exst[wp] = a[simplified all_but_exst_def]

lemma lift_inv: "(\<And>s g. P (trans_state g s) = P s) \<Longrightarrow>
       \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. P\<rbrace>"
  apply (clarsimp simp add: valid_def)
  apply (drule ex_st)
  apply force
  done

abbreviation (input) "I P \<equiv> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_.P\<rbrace>"

lemma obj_at[wp]: "I (obj_at a b)" by (rule lift_inv,simp)

lemma st_tcb_at[wp]: "I (st_tcb_at a b)" by (rule lift_inv,simp)

lemma valid_obj[wp]: "I (valid_obj a b)" by (rule lift_inv,simp)

lemma valid_pspace[wp]: "I (valid_pspace)" by (rule lift_inv,simp)

lemma valid_mdb[wp]: "I valid_mdb" by (rule lift_inv,simp)

lemma valid_ioc[wp]: "I valid_ioc" by (rule lift_inv,simp)

lemma valid_idle[wp]: "I valid_idle" by (rule lift_inv,simp)

lemma only_idle[wp]: "I only_idle" by (rule lift_inv,simp)

lemma if_unsafe_then_cap[wp]: "I if_unsafe_then_cap" by (rule lift_inv,simp)

lemma valid_reply_caps[wp]: "I valid_reply_caps" by (rule lift_inv,simp)

lemma valid_reply_masters[wp]: "I valid_reply_masters" by (rule lift_inv,simp)

lemma valid_global_refs[wp]: "I valid_global_refs" by (rule lift_inv,simp)

lemma valid_arch_state[wp]: "I valid_arch_state" by (rule lift_inv,simp)

lemma valid_irq_node[wp]: "I valid_irq_node" by (rule lift_inv,simp)

lemma valid_irq_handlers[wp]: "I valid_irq_handlers" by (rule lift_inv,simp)

lemma valid_machine_state[wp]: "I valid_machine_state" by (rule lift_inv,simp)

lemma valid_vspace_objs[wp]: "I valid_vspace_objs" by (rule lift_inv,simp)

lemma valid_arch_caps[wp]: "I valid_arch_caps" by (rule lift_inv,simp)

lemma valid_global_objs[wp]: "I valid_global_objs" by (rule lift_inv,simp)

lemma valid_global_vspace_mappings[wp]: "I valid_global_vspace_mappings" by (rule lift_inv,simp)

lemma valid_kernel_mappings[wp]: "I valid_kernel_mappings" by (rule lift_inv,simp)

lemma equal_kernel_mappings[wp]: "I equal_kernel_mappings" by (rule lift_inv,simp)

lemma valid_asid_map[wp]: "I valid_asid_map" by (rule lift_inv,simp)

lemma pspace_in_kernel_window[wp]: "I pspace_in_kernel_window" by (rule lift_inv,simp)

lemma cap_refs_in_kernel_window[wp]: "I cap_refs_in_kernel_window" by (rule lift_inv,simp)

lemma invs[wp]: "I invs" by (rule lift_inv,simp)

lemma cur_tcb[wp]: "I cur_tcb" by (rule lift_inv,simp)

lemma  valid_objs[wp]: "I (valid_objs)" by (rule lift_inv,simp)

lemma pspace_aligned[wp]: "I (pspace_aligned)" by (rule lift_inv,simp)

lemma pspace_distinct[wp]: "I (pspace_distinct)" by (rule lift_inv,simp)

lemma caps_of_state[wp]: "I (\<lambda>s. P (caps_of_state s))" by (rule lift_inv,simp)

lemma cte_wp_at[wp]: "I (\<lambda>s. P (cte_wp_at P' p s))" by (rule lift_inv,simp)

lemma no_cap_to_obj_dr_emp[wp]: "I (no_cap_to_obj_dr_emp x)" by (rule lift_inv,simp)

lemma valid_vs_lookup[wp]: "I (valid_vs_lookup)"
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (rule lift_inv, simp)
  qed

lemma typ_at[wp]: "I (\<lambda>s. P (typ_at T p s))" by (rule lift_inv,simp)

lemmas typ_ats[wp] = abs_typ_at_lifts [OF typ_at]

end


locale is_extended = is_extended' +
  constrains f :: "unit det_ext_monad"
  assumes b: "empty_fail f"

context is_extended begin

lemma dxo_eq[simp]:
  "do_extended_op f = f"
  apply (simp add: do_extended_op_def all_but_exst_def
                   get_def select_f_def modify_def put_def
                   wrap_ext_op_det_ext_ext_def ef_mk_ef[OF b])
  apply (rule ext)
  apply (simp add: bind_def)
  apply rule
   apply simp
   apply safe
     apply (simp | force | frule v)+
  done

end


lemma all_but_exst_update[simp]:
  "all_but_exst P (trans_state f s) = all_but_exst P s"
  apply (simp add: all_but_exst_def)
  done

crunch all_but_exst[wp]: set_scheduler_action,tcb_sched_action,next_domain,
                         cap_move_ext "all_but_exst P"
  (simp: Let_def ignore_del: tcb_sched_action cap_move_ext)

crunch (empty_fail) empty_fail[wp]: cap_move_ext
  (ignore_del: cap_move_ext)

global_interpretation set_scheduler_action_extended: is_extended "set_scheduler_action a"
  by (unfold_locales; wp)

global_interpretation tcb_sched_action_extended: is_extended "tcb_sched_action a b"
  by (unfold_locales; wp)

global_interpretation next_domain_extended: is_extended "next_domain"
  by (unfold_locales; wp)

global_interpretation cap_move_ext: is_extended "cap_move_ext a b c d"
  by (unfold_locales; wp)


lemmas rec_del_simps_ext =
    rec_del.simps [THEN ext[where f="rec_del args" for args]]

lemma rec_del_s_bcorres[wp]:
notes rec_del.simps[simp del]
shows
"s_bcorres (rec_del c) (rec_del c) s"
  proof (induct s rule: rec_del.induct, simp_all only: fail_s_bcorres_underlying rec_del_simps_ext(5-))

  case (1 slot exposed s) show ?case
    apply (simp add: rec_del.simps)
    apply wp
    apply (simp split: prod.splits  | intro impI conjI allI)+
    apply (wp drop_sbcorres_underlying)[1]
    apply (wp "1")
    done

  next
  case (2 slot exposed s)

  show ?case
    apply (simp add: rec_del.simps)
    apply (wp "2" | wpc | simp split: prod.splits | intro impI conjI allI | (rule ssubst[rotated, where s="fst x" for x], rule "2",simp+) | wp (once) drop_sbcorres_underlying)+
    done
  next
  case (3 slot exposed s)
  show ?case
    apply (simp add: rec_del.simps)
    apply (wp | wp (once) drop_sbcorres_underlying)+
    done
  next
  case (4 slot exposed s)
  show ?case
    apply (simp add: rec_del.simps)
    apply (simp add: in_monad | wp "4" | intro impI conjI | wp (once) drop_sbcorres_underlying)+
    done
  qed


lemmas rec_del_bcorres[wp] = use_sbcorres_underlying[OF rec_del_s_bcorres]

lemma cap_delete_bcorres'[wp]:
  assumes finalise_cap_bcorres[wp]:
    "\<And>r ra. bcorres (finalise_cap r ra :: 'a::state_ext state \<Rightarrow> _) (finalise_cap r ra)"
  shows "bcorres (cap_delete slot :: 'a state \<Rightarrow> _) (cap_delete slot)"
  unfolding cap_delete_def
  apply wp
  apply (simp add: returnOk_bcorres_underlying)
  apply (wp rec_del_bcorres)
  done

lemma cap_revoke_s_bcorres:
  shows
  "s_bcorres (cap_revoke slot) (cap_revoke slot) s"
proof (induct rule: cap_revoke.induct[where ?a1.0=s])
  case (1 slot s)
  show ?case
    apply (simp add: cap_revoke.simps)
    apply wp
      apply (wp gets_s_bcorres_underlyingE' | simp)+
            apply (subgoal_tac "(Inr (exst s'a),s'a) \<in> fst (liftE (gets exst) s'a)")
             prefer 2
             apply (simp add: in_monad)
            apply (rule "1"[simplified],(simp add: in_monad | force)+)
           apply (simp add:  | force | wp drop_sbcorres_underlying)+
    done
qed

lemmas cap_revoke_bcorres[wp] = use_sbcorres_underlying[OF cap_revoke_s_bcorres]

crunch (bcorres)bcorres[wp]: "Tcb_A.restart",as_user,option_update_thread truncate_state (simp: gets_the_def ignore: clearMemory check_cap_at gets_the getRegister setRegister getRestartPC setNextPC)

lemma check_cap_at_bcorres[wp]: "bcorres f f' \<Longrightarrow> bcorres (check_cap_at a b f) (check_cap_at a b f')"
  apply (simp add: check_cap_at_def)
  apply (wp | simp)+
  done

lemma invoke_domain_bcorres[wp]: "bcorres (invoke_domain t d) (invoke_domain t d)"
  by (simp add: invoke_domain_def, wp)

lemma truncate_state_detype[simp]: "truncate_state (detype x s) = detype x (truncate_state s)"
  apply (simp add: detype_def trans_state_def)
  done

lemma resolve_address_bits'_sbcorres:
  shows
  "s_bcorres (resolve_address_bits' TYPE('a::state_ext) a)
            (resolve_address_bits' TYPE(unit) a) s"
proof (induct a arbitrary: s rule: resolve_address_bits'.induct[where ?a0.0="TYPE('a::state_ext)"])
  case (1 z cap cref s')
  show ?case
    apply (simp add: resolve_address_bits'.simps)
    apply (wp | wpc | intro impI conjI allI | simp split: cap.splits | (rule "1", (simp add: in_monad | force)+) | wp (once) drop_sbcorres_underlying)+
  done
qed

lemma resolve_address_bits_bcorres[wp]: "bcorres (resolve_address_bits a) (resolve_address_bits a)"
    apply (simp add: resolve_address_bits_def)
    apply (rule use_sbcorres_underlying)
    apply (rule resolve_address_bits'_sbcorres)
  done

lemma bcorres_cap_fault_on_failure[wp]: "bcorres f f' \<Longrightarrow> bcorres (cap_fault_on_failure a b f) (cap_fault_on_failure a b f')"
  apply (simp add: cap_fault_on_failure_def)
  apply wpsimp
  done

lemmas in_use_frame_truncate[simp] = more_update.in_user_frame_update[where f="\<lambda>_.()"]

lemma lookup_error_on_failure_bcorres[wp]: "bcorres b b' \<Longrightarrow> bcorres (lookup_error_on_failure a b) (lookup_error_on_failure a b')"
  apply (simp add: lookup_error_on_failure_def)
  apply wpsimp
  done

lemma empty_on_failure_bcorres[wp]: "bcorres f f' \<Longrightarrow> bcorres (empty_on_failure f) (empty_on_failure f')"
  apply (simp add: empty_on_failure_def)
  apply wpsimp
  done

lemma unify_failure_bcorres[wp]: "bcorres f f' \<Longrightarrow> bcorres (unify_failure f) (unify_failure f')"
  apply (simp add: unify_failure_def)
  apply wpsimp
  done

lemma const_on_failure_bcorres[wp]: "bcorres f f' \<Longrightarrow> bcorres (const_on_failure c f) (const_on_failure c f')"
  apply (simp add: const_on_failure_def)
  apply wpsimp
  done

crunch (bcorres)bcorres[wp]: lookup_target_slot,lookup_cap,load_cap_transfer truncate_state
  (* FIXME: Prove without referring to RISCV64-specific definition here?
     Was broken by touched-addrs -robs *)
  (simp: gets_the_def RISCV64_A.user_frames_of_def ignore: loadWord)

lemma get_receive_slots_bcorres[wp]: "bcorres (get_receive_slots a b) (get_receive_slots a b)"
  by (cases b; wpsimp)

lemma (in BCorres2_AI) make_fault_msg_bcorres[wp]:
  "bcorres (make_fault_msg a b :: 'a state \<Rightarrow> _) (make_fault_msg a b)"
  apply (cases a)
  apply (wp | wpc | simp | intro impI conjI allI)+
  done

lemma (in BCorres2_AI) handle_fault_reply_bcorres[wp]:
  "bcorres (handle_fault_reply a b c d :: 'a state \<Rightarrow> _) (handle_fault_reply a b c d)"
  apply (cases a)
  apply (wp | simp)+
  done

crunch (bcorres)bcorres[wp]: lookup_source_slot,ensure_empty,lookup_pivot_slot truncate_state

declare option.case_cong[cong]

crunch (bcorres)bcorres[wp]: range_check truncate_state

lemma decode_read_registers_bcorres[wp]: "bcorres (decode_read_registers a (cap.ThreadCap b)) (decode_read_registers a (cap.ThreadCap b))"
  apply (simp add: decode_read_registers_def)
  apply (wp | wpc | simp)+
  done

lemma decode_write_registers_bcorres[wp]: "bcorres (decode_write_registers a (cap.ThreadCap b)) (decode_write_registers a (cap.ThreadCap b))"
  apply (simp add: decode_write_registers_def)
  apply (wp | wpc | simp)+
  done

lemma decode_copy_registers_bcorres[wp]: "bcorres (decode_copy_registers a (cap.ThreadCap b) e) (decode_copy_registers a (cap.ThreadCap b) e)"
  apply (simp add: decode_copy_registers_def)
  apply (wp | wpc | simp)+
  done

lemma alternative_first:"x \<in> fst (f s) \<Longrightarrow> x \<in> fst ((f \<sqinter> g) s)"
  by (simp add: alternative_def)

lemma alternative_second:"x \<in> fst (g s) \<Longrightarrow> x \<in> fst ((f \<sqinter> g) s)"
  by (simp add: alternative_def)

lemma bcorres_underlying_dest: "bcorres_underlying l f k \<Longrightarrow> ((),s') \<in> fst (f s) \<Longrightarrow>
       ((),l s') \<in> fst (k (l s))"
  apply (clarsimp simp add: bcorres_underlying_def s_bcorres_underlying_def)
  apply force
  done

lemma trans_state_twice[simp]: "trans_state (\<lambda>_. e) (trans_state f s) = trans_state (\<lambda>_. e) s"
  by (rule trans_state_update'')

lemma guarded_sub_switch: "((),x) \<in> fst (guarded_switch_to word s) \<Longrightarrow>
       ((),x) \<in> fst (switch_to_thread word s)
       \<and> (\<exists>y. get_tcb False word s = Some y \<and> runnable (tcb_state y))"
  apply (clarsimp simp add: guarded_switch_to_def bind_def
                            get_thread_state_def
                            thread_get_def
                            in_monad)
  (* FIXME: broken by touched-addrs. some experimentation below -robs *)
  apply(clarsimp simp:touch_object_def touch_objects_def bind_def
    simpler_do_machine_op_addTouchedAddresses_def simpler_modify_def
    in_assert in_gets in_return split:option.splits if_splits)
  apply(insert get_tcb_True_False)
  apply(rename_tac tcb ko)
  apply(erule_tac x=ko in meta_allE)
  apply(erule_tac x=word in meta_allE)
  apply(erule_tac x=s in meta_allE)
  apply clarsimp
  apply(subgoal_tac "ko_at ko word s")
   prefer 2
   apply(clarsimp simp:get_tcb_def ta_filter_def obind_def obj_at_def)
  apply clarsimp
  apply(rule conjI)
   prefer 2
   apply force
  (* FIXME: Need some lemma saying switch_to_thread isn't impacted by adding word to the TA
     because the very first thing it does is add it to the TA anyway? -robs *)
  sorry

lemma truncate_state_updates[simp]:
  "truncate_state (scheduler_action_update f s) = truncate_state s"
  "truncate_state (ready_queues_update g s) = truncate_state s"
  by (rule trans_state_update'')+

lemma get_before_assert_opt:
  "do s \<leftarrow> assert_opt x; s' \<leftarrow> get; f s s' od
    = do s' \<leftarrow> get; s \<leftarrow> assert_opt x; f s s' od"
  apply (cases x, simp_all add: assert_opt_def)
  apply (simp add: ext exec_get)
  done

lemma s_bcorres_get_left:
  "(s_bcorres_underlying t (get >>= f) g s)
    = (s_bcorres_underlying t (f s) g s)"
  by (simp add: s_bcorres_underlying_def exec_get)

lemma get_outside_alternative:
  "alternative (get >>= f) g
    = do s \<leftarrow> get; alternative (f s) g od"
  by (simp add: alternative_def exec_get fun_eq_iff)

lemmas schedule_unfold_all = schedule_def allActiveTCBs_def
                        get_thread_state_def thread_get_def getActiveTCB_def

context BCorres2_AI begin

lemma switch_thread_bcorreses:
  "bcorres (switch_to_idle_thread :: 'a state \<Rightarrow> _) switch_to_idle_thread"
  "bcorres (switch_to_thread t :: 'a state \<Rightarrow> _) (switch_to_thread t)"
  apply (simp_all add: switch_to_idle_thread_def switch_to_thread_def)
  apply (wp | simp)+
  done

lemma guarded_switch_bcorres: "s_bcorres (guarded_switch_to t :: 'a state \<Rightarrow> _) schedule s"
  using switch_thread_bcorreses(2)[where t=t]
  apply (clarsimp simp: schedule_unfold_all s_bcorres_underlying_def
                        in_monad in_select
            split del: if_split)
  apply (drule guarded_sub_switch)
  sorry (* FIXME: broken by touched-addrs -robs
  apply (rule_tac x=t in exI, clarsimp split del: if_split)
  apply (drule_tac s=s in drop_sbcorres_underlying)
  apply (clarsimp simp: s_bcorres_underlying_def)
  apply (auto intro!: alternative_second)
  done
*)

end

lemma choose_thread_bcorres: "BCorres2_AI TYPE(det_ext)
    \<Longrightarrow> s_bcorres choose_thread schedule s"
  apply (frule BCorres2_AI.switch_thread_bcorreses(1))
  apply (simp add: choose_thread_def gets_def s_bcorres_get_left
                   BCorres2_AI.guarded_switch_bcorres)
  apply (clarsimp simp: schedule_def s_bcorres_underlying_def)
  apply (drule_tac s=s in drop_sbcorres_underlying)
  apply (clarsimp simp: s_bcorres_underlying_def)
  apply (auto intro!: alternative_second simp: exec_gets)
  done

lemma tcb_sched_action_bcorres:
  "bcorres (tcb_sched_action a b) (return ())"
  by (clarsimp simp: bcorres_underlying_def s_bcorres_underlying_def return_def
              dest!: tcb_sched_action_extended.ex_st)

(* FIXME move if useful *)
lemma if_s_bcorres_underlying[wp]:
  "(P \<Longrightarrow> s_bcorres_underlying t f f' s) \<Longrightarrow> (\<not>P \<Longrightarrow> s_bcorres_underlying t g g' s)
  \<Longrightarrow> s_bcorres_underlying t (if P then f else g) (if P then f' else g') s"
  by (simp add: return_s_bcorres_underlying)

lemma schedule_choose_new_thread_bcorres1:
  "BCorres2_AI TYPE(det_ext) \<Longrightarrow> bcorres schedule_choose_new_thread schedule"
  unfolding schedule_choose_new_thread_def
  apply (clarsimp simp: bcorres_underlying_def)
  apply (simp add: schedule_det_ext_ext_def s_bcorres_get_left
                   gets_def get_thread_state_def thread_get_def gets_the_def
                   bind_assoc get_before_assert_opt ethread_get_def schedule_switch_thread_fastfail_def
                   when_def)
  apply (rule conjI; clarsimp)
   apply (rule s_bcorres_underlying_split[where g'="\<lambda>_. return ()",
                  OF _ choose_thread_bcorres, simplified]
               s_bcorres_underlying_split[where f'="return ()", simplified]
         | fastforce simp: s_bcorres_underlying_def set_scheduler_action_def
                           when_def exec_gets simpler_modify_def return_def
                           next_domain_def Let_def)+
  sorry (* FIXME: Broken by experimental-tpspec. -robs
  done
  *)

lemma schedule_bcorres1:
  notes bsplits =
          s_bcorres_underlying_split[where g'="\<lambda>_. return ()",
                                     OF _ choose_thread_bcorres, simplified]
          s_bcorres_underlying_split[where g'="\<lambda>_. return ()",
                                     OF _ BCorres2_AI.guarded_switch_bcorres, simplified]
          s_bcorres_underlying_split[where f'="return ()", simplified]
  notes bdefs = schedule_det_ext_ext_def s_bcorres_get_left
                gets_def get_thread_state_def thread_get_def gets_the_def
                bind_assoc get_before_assert_opt ethread_get_def
                schedule_switch_thread_fastfail_def when_def
                tcb_sched_action_bcorres drop_sbcorres_underlying return_s_bcorres_underlying
  notes unfolds = s_bcorres_underlying_def set_scheduler_action_def
                   simpler_modify_def return_def
  shows "BCorres2_AI TYPE(det_ext) \<Longrightarrow> bcorres (schedule :: (unit,det_ext) s_monad) schedule"
  supply if_split[split del]
  apply (clarsimp simp: bcorres_underlying_def fail_def)
  apply (simp add: bdefs)
  sorry (* FIXME: broken by touched-addrs -robs
  apply (simp add: assert_opt_def)
  apply (simp split: option.split, intro conjI impI)
   apply (simp add: s_bcorres_underlying_def fail_def)
  apply clarsimp
  apply (split scheduler_action.split, intro conjI impI)
    (* resume current *)
    subgoal for s
      apply (clarsimp simp: s_bcorres_underlying_def schedule_def allActiveTCBs_def
                            in_monad in_select getActiveTCB_def
                       split: if_split)
      apply (fastforce simp add: switch_to_idle_thread_def in_monad in_select ex_bool_eq)
      done
   (* switch to *)
   subgoal for s cttcb
     apply clarsimp
     apply (rule bsplits)+
      apply (simp add: bdefs)
      apply (simp add: assert_opt_def)
      apply (split option.split, simp, intro conjI impI)
       apply (simp add: s_bcorres_underlying_def fail_def)

      apply (clarsimp simp: ethread_get_when_def split: if_split)

      apply (rule conjI; clarsimp)
       apply (simp add: bdefs)
       apply (simp add: assert_opt_def)
       apply (split option.split, simp, intro conjI impI)
        apply (simp add: s_bcorres_underlying_def fail_def)

       apply (clarsimp simp: bdefs split: if_split
              | rule conjI
              | rule bsplits
              | erule drop_sbcorres_underlying[OF schedule_choose_new_thread_bcorres1]
              | fastforce simp: unfolds)+
     done
  apply (clarsimp simp: bdefs split: if_split
         | rule conjI
         | rule bsplits
         | erule drop_sbcorres_underlying[OF schedule_choose_new_thread_bcorres1])+
  done
*)

end
