(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory Include_AI
imports
  "./$L4V_ARCH/ArchCrunchSetup_AI"
  "../../lib/Monad_WP/wp/Eisbach_WP"
  "../../spec/abstract/Syscall_A"
  "../../lib/LemmaBucket"
  "../../lib/ListLibLemmas"
begin

no_notation bind_drop (infixl ">>" 60)

(* Clagged from Bits_R *)

crunch_ignore (add:
  bind return "when" get gets fail 
  assert put modify unless select
  alternative assert_opt gets_the
  returnOk throwError lift bindE
  liftE whenE unlessE throw_opt 
  assertE liftM liftME sequence_x 
  zipWithM_x mapM_x sequence mapM sequenceE_x
  sequenceE mapME mapME_x catch select_f
  handleE' handleE handle_elseE forM forM_x
  zipWithM filterM forME_x)

crunch_ignore (add: cap_fault_on_failure lookup_error_on_failure
  without_preemption const_on_failure ignore_failure
  empty_on_failure unify_failure throw_on_false)

crunch_ignore (add:
  storeWord storeWordVM loadWord setRegister getRegister getRestartPC
  set_register get_register setNextPC maskInterrupt)

crunch_ignore (add:
  cap_swap_ext cap_move_ext cap_insert_ext empty_slot_ext create_cap_ext tcb_sched_action
  reschedule_required set_thread_state_ext switch_if_required_to
  attempt_switch_to timer_tick set_priority retype_region_ext)

end
