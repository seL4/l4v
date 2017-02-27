(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory BCorres_AI
imports
  Include_AI
  "../../lib/BCorres_UL"
  "../../spec/abstract/Syscall_A"
begin

abbreviation "bcorres \<equiv> bcorres_underlying truncate_state"

abbreviation "s_bcorres \<equiv> s_bcorres_underlying truncate_state"

lemma dxo_bcorres[wp]:
  "bcorres (do_extended_op f)
        (do_extended_op f)"
  apply (simp add: do_extended_op_def)
  apply (simp add: bind_def select_f_def modify_def return_def get_def put_def gets_def)
  apply (simp add: split_def)
  apply (simp add: bcorres_underlying_def s_bcorres_underlying_def)
  apply (clarsimp simp: mk_ef_def wrap_ext_op_unit_def return_def)
  done

lemma OR_choice_bcorres[wp]:
  "bcorres f f' \<Longrightarrow> bcorres g g' \<Longrightarrow> bcorres (OR_choice b f g) (OR_choice b f' g')"
  apply (simp add: OR_choice_def  wrap_ext_bool_unit_def)
  apply (rule get_bcorres)
  apply (simp add: 
 bind_def select_f_def mk_ef_def modify_def return_def get_def put_def gets_def select_def)
  apply (simp add: split_def)

  apply (simp add: bcorres_underlying_def s_bcorres_underlying_def)
  apply (clarsimp simp: if_split_asm)
  apply (rule_tac x=ab in exI)
  apply (intro conjI impI)
   apply simp
   apply force
  apply simp
  apply force
  done

lemma liftE_bcorres[wp]: "bcorres f f' \<Longrightarrow> bcorres (liftE f) (liftE f')"
  by (simp add: liftE_def | wp)+

lemma liftE_bind_bcorres[wp]: "bcorres (f >>= g) (f' >>= g') \<Longrightarrow> bcorres (liftE f >>=E g) (liftE f' >>=E g')"
  apply (simp add: gets_def bcorres_underlying_def s_bcorres_underlying_def get_def bind_def return_def split_def liftE_def bindE_def lift_def)
  done

lemma OR_choiceE_bcorres[wp]:
  "bcorres f f' \<Longrightarrow> bcorres g g' \<Longrightarrow> bcorres (OR_choiceE b f g) (OR_choiceE b f' g')"
  apply (simp add: OR_choiceE_def  wrap_ext_bool_unit_def)
  apply wp
  apply (simp add: 
 bind_def select_f_def mk_ef_def modify_def return_def get_def put_def gets_def select_def)
  apply (simp add: split_def)

  apply (simp add: bcorres_underlying_def s_bcorres_underlying_def)
  apply (clarsimp simp: if_split_asm)
  apply (rule_tac x=ab in exI)
  apply (intro conjI impI)
   apply simp
   apply force
  apply simp
  apply force
  done

lemma select_f_bcorres[wp]: "bcorres (select_f f) (select_f f)"
  apply (simp add: select_f_def bcorres_underlying_def s_bcorres_underlying_def)
  apply force
  done

lemma returnOk_bcorres_underlying[wp]: "bcorres_underlying t (returnOk a) (returnOk a)"
  apply (simp add: returnOk_def)
  apply wp
  done


lemma bcorres_underlying_if[wp]:
  "(b \<Longrightarrow> bcorres_underlying t f f') \<Longrightarrow>  (\<not>b \<Longrightarrow> bcorres_underlying t g g') \<Longrightarrow>
  bcorres_underlying t (if b then f else g) (if b then f' else g')"
  apply (case_tac b,simp+)
  done

lemma assert_opt_bcorres_underlying[wp]: "bcorres_underlying t (assert_opt f) (assert_opt f)"
  apply (simp add: assert_opt_def)
  apply (wp | wpc | simp)+
  done

crunch_ignore (bcorres)
  (add: bind gets modify get put do_extended_op empty_slot_ext mapM_x "when"
        select unless mapM catch bindE liftE whenE alternative cap_swap_ext
        cap_insert_ext cap_move_ext liftM create_cap_ext 
        attempt_switch_to reschedule_required set_priority
        switch_if_required_to set_thread_state_ext
        tcb_sched_action timer_tick
        lookup_error_on_failure getActiveIRQ
        gets_the liftME zipWithM_x unlessE mapME_x handleE)

lemma bcorres_select_ext[wp]: "bcorres (select_ext a A) (select_ext a A)"
  apply (clarsimp simp add: select_ext_def bind_def gets_def return_def select_def assert_def
                   select_switch_unit_def get_def bcorres_underlying_def s_bcorres_underlying_def fail_def)
  done

crunch (bcorres)bcorres[wp]: set_original,set_object,set_cap,set_irq_state,
                        deleted_irq_handler,get_cap,set_cdt,empty_slot
truncate_state (ignore: maskInterrupt) 

lemma get_cap_det:
  "(r,s') \<in> fst (get_cap p s) \<Longrightarrow> get_cap p s = ({(r,s)}, False)"
  apply (cases p)
  apply (clarsimp simp add: in_monad get_cap_def get_object_def
                     split: Structures_A.kernel_object.split_asm)
   apply (clarsimp simp add: bind_def return_def assert_opt_def simpler_gets_def)
  apply (simp add: bind_def simpler_gets_def return_def assert_opt_def)
  done


lemma get_object_bcorres_any: "bcorres_underlying (trans_state e) (get_object a) (get_object a)"
  apply (simp add: get_object_def | wp)+
  done

lemma get_cap_bcorres_any: "bcorres_underlying (trans_state e) (get_cap x) (get_cap x)"
  apply (simp add: get_cap_def)
  apply (wp get_object_bcorres_any | wpc | simp)+
  done


lemma get_cap_helper: "(fst (get_cap cref (trans_state e x)) =
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
  apply (simp add: is_final_cap_def is_final_cap'_def gets_def get_cap_helper | wp)+
  done



lemma get_tcb_truncate[simp]: "get_tcb a (truncate_state s) = get_tcb a s"
  apply (simp add: get_tcb_def)
  done

crunch (bcorres)bcorres[wp]: cancel_all_ipc,cancel_all_signals,unbind_maybe_notification,unbind_notification, bind_notification truncate_state (simp: gets_the_def ignore: gets_the)

lemma fast_finalise_bcorres[wp]:
  "bcorres (fast_finalise a b) (fast_finalise a b)"
  apply (cases a)
  apply (simp | wp | wpc)+
  done

lemma bcorres_unless[wp]: "bcorres f f' \<Longrightarrow> bcorres (unless a f) (unless a f')"
  apply (simp add: unless_def | wp)+
  done

lemma bcorres_select[wp]: "A \<subseteq> B \<Longrightarrow> bcorres (select A) (select B)"
  apply (simp add: bcorres_underlying_def select_def s_bcorres_underlying_def)
  apply force
  done


crunch (bcorres)bcorres[wp]: get_irq_slot truncate_state (simp: gets_def)

lemma catch_bcorres[wp]: "bcorres f f' \<Longrightarrow>  (\<And>x. bcorres (g x) (g' x)) \<Longrightarrow> bcorres (f <catch> g) (f' <catch> g')"
  apply (simp add: catch_def | wp | wpc)+
  done

lemma whenE_bcorres_underlying[wp]: "(P = P' \<Longrightarrow> P \<Longrightarrow> bcorres_underlying t f f') \<Longrightarrow> P = P'  \<Longrightarrow> bcorres_underlying t (whenE P f) (whenE P' f')"
  apply (clarsimp simp add: whenE_def)
  apply wp
  done

lemma unlessE_bcorres[wp]: "bcorres f f' \<Longrightarrow> bcorres (unlessE P f) (unlessE P f')"
  apply (clarsimp simp add: unlessE_def | wp)+
  done


lemma throw_on_false_bcorres[wp]: "bcorres f f' \<Longrightarrow>  bcorres (throw_on_false e f) (throw_on_false e f')"
  apply (simp add: throw_on_false_def | wp)+
  done

context Arch begin

lemma gets_the_get_tcb_bcorres[wp]: "bcorres (gets_the (get_tcb a)) (gets_the (get_tcb a)) "
  apply (simp add: gets_the_def bcorres_underlying_def assert_opt_def| wp | wpc| clarsimp)+
  apply (case_tac r; simp add: fail_s_bcorres_underlying return_s_bcorres_underlying)
  apply (simp add: gets_s_bcorres_underlying)
done


crunch (bcorres)bcorres[wp]: arch_finalise_cap truncate_state (simp: swp_def ignore: forM_x) (* FIXME ARMHYP *)

crunch (bcorres)bcorres[wp]: prepare_thread_delete truncate_state (simp: swp_def)

end

requalify_facts Arch.arch_finalise_cap_bcorres Arch.prepare_thread_delete_bcorres

declare arch_finalise_cap_bcorres[wp] prepare_thread_delete_bcorres[wp]


crunch (bcorres)bcorres[wp]: "IpcCancel_A.suspend",deleting_irq_handler truncate_state (simp: gets_the_def swp_def ignore: gets_the ignore: throw_on_false)

lemma finalise_cap_bcorres[wp]: "bcorres (finalise_cap a b) (finalise_cap a b)"
  apply (cases a)
  apply (wp | wpc | simp | intro impI allI conjI)+
  done

lemma alternative_bcorres[wp]: "bcorres f f' \<Longrightarrow>  bcorres g g' \<Longrightarrow> bcorres (f \<sqinter> g) (f' \<sqinter> g')"
  apply (simp add: alternative_def bcorres_underlying_def s_bcorres_underlying_def)
  apply force
  done

crunch_ignore (bcorres) (add: getActiveIRQ)

lemma preemption_point_bcorres[wp]: "bcorres preemption_point preemption_point"
  apply (simp add: preemption_point_def)
  apply (wp | wpc | simp | intro impI allI conjI)+
  done

crunch (bcorres)bcorres[wp]: cap_swap_for_delete truncate_state

end
