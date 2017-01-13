(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory BCorres2_AI
imports
  "../../lib/BCorres_UL"
  "./$L4V_ARCH/ArchEmptyFail_AI"
begin

locale BCorres2_AI =
  fixes state  :: "'a::state_ext itself"
  assumes handle_arch_fault_reply_bcorres[wp]:
    "\<And>a b c d.
      bcorres (handle_arch_fault_reply a b c d :: 'a state \<Rightarrow> _)
              (handle_arch_fault_reply a b c d)"
  assumes make_arch_fault_msg_bcorres[wp]:
    "\<And> a b.
      bcorres (make_arch_fault_msg a b :: 'a state \<Rightarrow> _)
              (make_arch_fault_msg a b)"

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
  apply (simp add: valid_obj_def split: kernel_object.splits)
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

lemma valid_arch_objs[wp]: "I valid_arch_objs" by (rule lift_inv,simp)

lemma valid_arch_caps[wp]: "I valid_arch_caps" by (rule lift_inv,simp)

lemma valid_global_objs[wp]:"I valid_global_objs" by (rule lift_inv,simp)

lemma valid_kernel_mappings[wp]: "I valid_kernel_mappings" by (rule lift_inv,simp)

lemma equal_kernel_mappings[wp]: "I equal_kernel_mappings" by (rule lift_inv,simp)

lemma valid_asid_map[wp]: "I valid_asid_map" by (rule lift_inv,simp)

lemma valid_global_vspace_mappings[wp]: "I valid_global_vspace_mappings" by (rule lift_inv,simp)

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
  (simp: Let_def)

crunch (empty_fail) empty_fail[wp]: cap_move_ext

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


lemma rec_del_s_bcorres: 
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
    apply (wp "2" | wpc | simp split: prod.splits | intro impI conjI allI | (rule ssubst[rotated, where s="fst x" for x], rule "2",simp+) | wp_once drop_sbcorres_underlying)+
    done
  next
  case (3 slot exposed s)
  show ?case
    apply (simp add: rec_del.simps)
    apply (wp | wp_once drop_sbcorres_underlying)+
    done
  next
  case (4 slot exposed s)
  show ?case
    apply (simp add: rec_del.simps)
    apply (simp add: in_monad | wp "4" | intro impI conjI | wp_once drop_sbcorres_underlying)+
    done
  qed


lemmas rec_del_bcorres = use_sbcorres_underlying[OF rec_del_s_bcorres]

crunch (bcorres)bcorres[wp]: cap_delete truncate_state
   
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

lemmas cap_revoke_bcorres = use_sbcorres_underlying[OF cap_revoke_s_bcorres]

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
    apply (wp | wpc | intro impI conjI allI | simp split: cap.splits | (rule "1", (simp add: in_monad | force)+) | wp_once drop_sbcorres_underlying)+
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

crunch (bcorres)bcorres[wp]: lookup_target_slot,lookup_cap,load_cap_transfer truncate_state (simp: gets_the_def ignore: loadWord)

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
       \<and> (\<exists>y. get_tcb word s = Some y \<and> runnable (tcb_state y))"
  apply (clarsimp simp add: guarded_switch_to_def bind_def
                            get_thread_state_def 
                            thread_get_def
                            in_monad)
  done

lemma truncate_state_updates[simp]:
  "truncate_state (scheduler_action_update f s) = truncate_state s"
  "truncate_state (ready_queues_update g s) = truncate_state s"
  by (rule trans_state_update'')+

(* the old schedule unit def no longer is a refinement of the det_ext def.

   if sched_act = resume_cur_thread and cur_thread = idle_thread,
     then there should be a path through schedule_unit which corresponds to a return().
   This used to be via switch_to_idle_thread, but now switch_to_idle_thread updates
     arm_globals_frame, so is no longer a return in this case. *)

(*The only nontrivial bcorres result. Since we don't have
  a proper calculus we just unfold everything. The refinement
  is made guard-less by asserting that we only switch to
  runnable threads inside of the deterministic scheduler
  (guaranteed by valid_sched) *)
(*
lemma schedule_bcorres[wp]: "bcorres (schedule :: (unit,det_ext) s_monad) schedule"

  apply (simp add: schedule_def)
  apply (clarsimp simp add: schedule_def gets_def bind_def get_def 
                            return_def s_bcorres_underlying_def
                            allActiveTCBs_def bcorres_underlying_def
                            select_def getActiveTCB_def
                            get_thread_state_def thread_get_def
                            gets_the_def assert_opt_def fail_def
                            )
  apply (case_tac "get_tcb (cur_thread s) s",simp_all)
  apply (case_tac "scheduler_action bb",simp_all add: in_monad)
  apply (case_tac "runnable (tcb_state aa)")
    apply (rule alternative_first)
    apply (clarsimp)
    apply (rule_tac x="cur_thread s" in exI)
    apply clarsimp
    apply (rule alternative_first)
    apply clarsimp+
   apply (rule alternative_second)
   apply (simp add: switch_to_idle_thread_def bind_def
                    gets_def get_def return_def arch_switch_to_idle_thread_def
                    in_monad)
   apply (case_tac "runnable (tcb_state aa)")
    apply clarsimp
    apply (drule tcb_sched_action_extended.ex_st set_scheduler_action_extended.ex_st)+
    apply clarsimp
    apply (drule bcorres_underlying_dest[OF guarded_switch_to_bcorres])
    apply (drule guarded_sub_switch,clarsimp)
    apply (rule alternative_first)
    apply clarsimp
    apply (rule_tac x=word in exI)
    apply (intro conjI impI)
      apply (rule alternative_second)
  
      apply simp
     apply (rule_tac x=y in exI)
     apply clarsimp
    apply simp
   apply clarsimp
   apply (drule set_scheduler_action_extended.ex_st)+
   apply clarsimp
   apply (drule bcorres_underlying_dest[OF guarded_switch_to_bcorres])
   apply (drule guarded_sub_switch,clarsimp)
   apply (rule alternative_first)
   apply clarsimp
   apply (rule_tac x=word in exI)
   apply clarsimp
  apply clarsimp
  apply (case_tac "runnable (tcb_state aa)")
   apply clarsimp
   apply (subgoal_tac "\<exists>e. s''a = trans_state (\<lambda>_. e) s''")
    prefer 2
    apply (erule impCE)
     apply (rule_tac x="exst s''" in exI)
     apply simp
    apply (erule next_domain_extended.ex_st)
   apply (drule tcb_sched_action_extended.ex_st set_scheduler_action_extended.ex_st)+
   apply clarsimp
   apply (drule choose_switch_or_idle)
   apply (elim exE disjE)
    apply (drule bcorres_underlying_dest[OF guarded_switch_to_bcorres])
    apply (drule guarded_sub_switch,clarsimp)
    apply (rule alternative_first)
    apply simp
    apply (rule_tac x=word in exI)
    apply clarsimp
    apply (rule alternative_second)
    apply clarsimp
   apply (drule bcorres_underlying_dest[OF switch_to_idle_thread_bcorres])
   apply simp
   apply (rule alternative_second)
   apply simp
  apply clarsimp
  apply (drule set_scheduler_action_extended.ex_st)+
  apply (subgoal_tac "\<exists>e. s''a = trans_state (\<lambda>_. e) s")
   prefer 2
   apply (erule impCE)
    apply (rule_tac x="exst s" in exI)
    apply simp
   apply (erule next_domain_extended.ex_st)
  apply clarsimp
  apply (drule choose_switch_or_idle)
  apply (elim exE disjE)
   apply (drule bcorres_underlying_dest[OF guarded_switch_to_bcorres])
   apply (drule guarded_sub_switch,clarsimp)
   apply (rule alternative_first)
   apply clarsimp
   apply (rule_tac x="word" in exI)
   apply clarsimp
  apply (rule alternative_second)
  apply (drule bcorres_underlying_dest[OF switch_to_idle_thread_bcorres])
  apply simp
  done
*)

end
