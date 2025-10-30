(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory BCorres_AI
imports
  Include_AI
  "Lib.BCorres_UL"
begin

unbundle l4v_word_context (* because of Lib.BCorres_UL *)

abbreviation "bcorres \<equiv> bcorres_underlying truncate_state"

abbreviation "s_bcorres \<equiv> s_bcorres_underlying truncate_state"

lemma dxo_bcorres[wp]:
  "bcorres (do_extended_op f) (do_extended_op f)"
  apply (simp add: do_extended_op_def)
  apply (simp add: bind_def select_f_def modify_def return_def get_def put_def gets_def)
  apply (simp add: split_def)
  apply (simp add: bcorres_underlying_def s_bcorres_underlying_def)
  apply (clarsimp simp: mk_ef_def wrap_ext_op_unit_def return_def)
  done

lemma OR_choice_bcorres[wp]:
  "bcorres f f' \<Longrightarrow> bcorres g g' \<Longrightarrow> bcorres (OR_choice b f g) (OR_choice b f' g')"
  apply (simp add: OR_choice_def wrap_ext_bool_unit_def)
  apply (rule get_bcorres)
  apply (simp add: bind_def select_f_def mk_ef_def modify_def return_def get_def put_def gets_def
                   select_def)
  apply (simp add: bcorres_underlying_def s_bcorres_underlying_def)
  apply (clarsimp simp: if_split_asm)
  apply (rule_tac x=ab in exI)
  apply force
  done

lemma OR_choiceE_bcorres[wp]:
  "bcorres f f' \<Longrightarrow> bcorres g g' \<Longrightarrow> bcorres (OR_choiceE b f g) (OR_choiceE b f' g')"
  apply (simp add: OR_choiceE_def wrap_ext_bool_unit_def)
  apply wp
  apply (simp add: bind_def select_f_def mk_ef_def modify_def return_def get_def put_def gets_def
                   select_def)
  apply (simp add: bcorres_underlying_def s_bcorres_underlying_def)
  apply (clarsimp simp: if_split_asm)
  apply (rule_tac x=ab in exI)
  apply force
  done

crunch_ignore (bcorres)
  (add: Nondet_Monad.bind gets modify get put do_extended_op empty_slot_ext mapM_x "when"
        select unless mapM catch bindE liftE whenE alternative cap_swap_ext
        cap_insert_ext cap_move_ext liftM create_cap_ext
        lookup_error_on_failure getActiveIRQ
        gets_the liftME zipWithM_x unlessE mapME_x handleE forM_x)

lemma bcorres_select_ext[wp]:
  "bcorres (select_ext a A) (select_ext a A)"
  by (clarsimp simp: select_ext_def bind_def gets_def return_def select_def assert_def get_def
                     select_switch_unit_def bcorres_underlying_def s_bcorres_underlying_def fail_def)

context Arch begin arch_global_naming

crunch arch_post_cap_deletion
  for (bcorres) bcorres[wp]: truncate_state

end

arch_requalify_facts
  arch_post_cap_deletion_bcorres

crunch
  set_original, set_object, set_cap, set_irq_state, deleted_irq_handler, get_cap,set_cdt, empty_slot
  for (bcorres) bcorres[wp]: truncate_state
  (simp: read_object_def)

lemma get_cap_det:
  "(r,s') \<in> fst (get_cap p s) \<Longrightarrow> get_cap p s = ({(r,s)}, False)"
  apply (cases p)
  apply (clarsimp simp: in_monad get_cap_def get_object_def read_object_def)
  apply (rename_tac ko caps; case_tac ko; simp add: fail_def)
  by (clarsimp simp: in_monad gets_the_def gets_def get_def bind_assoc assert_opt_def
                     fail_def return_def bind_def
              split: option.splits)+

lemma get_object_bcorres_any[wp]:
  "bcorres_underlying (trans_state e) (get_object a) (get_object a)"
  by (wpsimp simp: get_object_def read_object_def)

lemma get_cap_bcorres_any:
  "bcorres_underlying (trans_state e) (get_cap x) (get_cap x)"
  by (wpsimp simp: get_cap_def)

lemma get_cap_helper:
  "(fst (get_cap cref (trans_state e x)) =
    {(cap', trans_state e x)}) = (fst (get_cap cref x) = {(cap', x)})"
  apply (rule iffI)
   apply (cut_tac x=cref and e="\<lambda>_. exst x" in get_cap_bcorres_any)
   apply (simp add: bcorres_underlying_def)
   apply (drule_tac x="trans_state e x" in spec)
   apply (simp add: s_bcorres_underlying_def)
   apply (drule get_cap_det)
   apply (simp add: trans_state_update')
  apply (cut_tac x=cref and e="e" in get_cap_bcorres_any)
  apply (simp add: bcorres_underlying_def)
  apply (drule_tac x="x" in spec)
  apply (simp add: s_bcorres_underlying_def)
  apply (drule get_cap_det)
  apply simp
  done

lemma is_final_cap_bcorres[wp]:
  "bcorres (is_final_cap a) (is_final_cap a)"
  by (simp add: is_final_cap_def is_final_cap'_def gets_def get_cap_helper | wp)+

lemma read_object_truncate[simp]: "read_object a (truncate_state s) = read_object a s"
  by (clarsimp simp: read_object_def)

lemma get_tcb_truncate[simp]: "get_tcb a (truncate_state s) = get_tcb a s"
  by (simp add: get_tcb_def)

lemma read_sched_context_truncate[simp]: "read_sched_context a (truncate_state s) = read_sched_context a s"
  by (simp add: read_sched_context_def obind_def omonad_defs split: kernel_object.splits option.splits)

lemma read_refill_head_truncate[simp]:
  "read_refill_head sc_ptr (truncate_state s) = read_refill_head sc_ptr s"
  by (simp add: read_refill_head_def obind_def split: option.splits)

lemma read_sc_refill_capacity_truncate[simp]:
  "read_sc_refill_capacity sc_ptr usage (truncate_state s) = read_sc_refill_capacity sc_ptr usage s"
  by (simp add: read_sc_refill_capacity_def obind_def split: option.splits)

lemma read_sc_refill_ready_truncate[simp]:
  "read_sc_refill_ready a (truncate_state s) = read_sc_refill_ready a s"
  by (simp add: read_sc_refill_ready_def obind_def omonad_defs split: option.splits)

lemma read_sc_refill_sufficient_truncate[simp]:
  "read_sc_refill_sufficient sc_ptr usage (truncate_state s)
   = read_sc_refill_sufficient sc_ptr usage s"
  by (simp add: read_sc_refill_sufficient_def obind_def omonad_defs)

lemma read_sc_active_truncate[simp]:
  "read_sc_active a (truncate_state s) = read_sc_active a s"
  by (simp add: read_sc_active_def obind_def split: option.splits)

lemma in_release_queue_truncate[simp]:
  "in_release_queue t (truncate_state s) = in_release_queue t s"
  by (simp add: in_release_queue_def)

lemma schedulable_truncate[simp]:
  "schedulable t (truncate_state s) = schedulable t s"
  by (simp add: schedulable_def)

lemma gets_the_tcb_bcorres[wp]:
  "bcorres (gets_the (get_tcb t)) (gets_the (get_tcb t))"
  unfolding gets_the_def by wpsimp

lemma set_tcb_queue_bcorres[wp]:
  "bcorres (set_tcb_queue d prio q) (set_tcb_queue d prio q)"
  by (wpsimp simp: set_tcb_queue_def cong: if_cong)

lemma get_sc_refill_ready_bcorres[wp]:
  "bcorres (get_sc_refill_ready scp) (get_sc_refill_ready scp)"
  by (wpsimp simp: get_sc_refill_ready_def gets_the_def)

lemma refill_head_overlapping_truncate[simp]:
  "refill_head_overlapping a (truncate_state s) = refill_head_overlapping a s"
  by (simp add: refill_head_overlapping_def obind_def omonad_defs)

crunch
  refill_unblock_check
 for (bcorres) bcorres[wp]: truncate_state

crunch
  cancel_all_ipc, bind_notification, cancel_all_signals
 for (bcorres) bcorres[wp]: truncate_state

crunch get_tcb_obj_ref, get_sk_obj_ref
 for (bcorres) bcorres[wp]: truncate_state
  (simp: gets_the_def ignore: gets_the)

lemma unbind_maybe_notification_bcorres[wp]:
  "bcorres (unbind_maybe_notification a) (unbind_maybe_notification a)"
  by (wpsimp simp: unbind_maybe_notification_def)

lemma unbind_notification_bcorres[wp]:
  "bcorres (unbind_notification a) (unbind_notification a)"
  by (wpsimp simp: unbind_notification_def)

(*
lemma fast_finalise_bcorres[wp]:
  "bcorres (fast_finalise a b) (fast_finalise a b)"
  by (cases a; wpsimp)
*)

crunch get_irq_slot
  for (bcorres) bcorres[wp]: truncate_state (simp: gets_def)

lemma throw_on_false_bcorres[wp]:
  "bcorres f f' \<Longrightarrow>  bcorres (throw_on_false e f) (throw_on_false e f')"
  by (simp add: throw_on_false_def | wp)+

lemma preemption_point_bcorres[wp]:
  "bcorres preemption_point preemption_point"
  unfolding preemption_point_def is_cur_domain_expired_def andM_def ifM_def get_sc_active_def
            update_time_stamp_def
  by wpsimp

crunch cap_swap_for_delete
  for (bcorres) bcorres[wp]: truncate_state

end
