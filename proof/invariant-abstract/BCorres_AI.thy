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
        possible_switch_to reschedule_required set_priority
        set_thread_state_ext tcb_sched_action timer_tick
        lookup_error_on_failure getActiveIRQ
        gets_the liftME zipWithM_x unlessE mapME_x handleE forM_x)

lemma bcorres_select_ext[wp]:
  "bcorres (select_ext a A) (select_ext a A)"
  by (clarsimp simp: select_ext_def bind_def gets_def return_def select_def assert_def get_def
                     select_switch_unit_def bcorres_underlying_def s_bcorres_underlying_def fail_def)

context Arch begin

crunches arch_post_cap_deletion
  for (bcorres) bcorres[wp]: truncate_state

end

requalify_facts
  Arch.arch_post_cap_deletion_bcorres

crunches
  set_original, set_object, set_cap, set_irq_state, deleted_irq_handler, get_cap,set_cdt, empty_slot
  for (bcorres) bcorres[wp]: truncate_state
  (ignore: maskInterrupt)

lemma get_cap_det:
  "(r,s') \<in> fst (get_cap p s) \<Longrightarrow> get_cap p s = ({(r,s)}, False)"
  apply (cases p)
  apply (clarsimp simp add: in_monad get_cap_def get_object_def
                     split: kernel_object.split_asm)
   apply (clarsimp simp add: bind_def return_def assert_opt_def simpler_gets_def)
  apply (simp add: bind_def simpler_gets_def return_def assert_opt_def)
  done

lemma get_object_bcorres_any[wp]:
  "bcorres_underlying (trans_state e) (get_object a) (get_object a)"
  by (wpsimp simp: get_object_def)

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

lemma get_tcb_truncate[simp]: "get_tcb a (truncate_state s) = get_tcb a s"
  by (simp add: get_tcb_def)

crunches
  cancel_all_ipc, cancel_all_signals, unbind_maybe_notification, unbind_notification, bind_notification
  for (bcorres) bcorres[wp]: truncate_state
  (simp: gets_the_def ignore: gets_the)

lemma fast_finalise_bcorres[wp]:
  "bcorres (fast_finalise a b) (fast_finalise a b)"
  by (cases a; wpsimp)

crunches get_irq_slot
  for (bcorres) bcorres[wp]: truncate_state (simp: gets_def)

lemma throw_on_false_bcorres[wp]:
  "bcorres f f' \<Longrightarrow>  bcorres (throw_on_false e f) (throw_on_false e f')"
  by (simp add: throw_on_false_def | wp)+

crunch_ignore (bcorres) (add: getActiveIRQ)

lemma preemption_point_bcorres[wp]:
  "bcorres preemption_point preemption_point"
  unfolding preemption_point_def by wpsimp

crunches cap_swap_for_delete
  for (bcorres) bcorres[wp]: truncate_state

lemma gets_the_get_tcb_bcorres[wp]:
  "bcorres (gets_the (get_tcb a)) (gets_the (get_tcb a)) "
  by (wpsimp simp: gets_the_def bcorres_underlying_def assert_opt_def split: option.splits|rule conjI)+

end
