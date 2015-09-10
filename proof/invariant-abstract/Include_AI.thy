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
  BCorres_AI
  "../../lib/wp/Eisbach_WP"
  "../../spec/abstract/Syscall_A"
  "../../lib/LemmaBucket"
  "../../lib/ListLibLemmas"
begin

no_notation bind_drop (infixl ">>" 60)

(* Clagged from Bits_R *)

crunch_ignore (add:
  bind return when get gets fail 
  assert put modify unless select
  alternative assert_opt gets_the
  returnOk throwError lift bindE
  liftE whenE unlessE throw_opt 
  assertE liftM liftME sequence_x 
  zipWithM_x mapM_x sequence mapM sequenceE_x
  mapME_x catch select_f
  handleE' handleE handle_elseE forM forM_x
  zipWithM)

crunch_ignore (add: cap_fault_on_failure lookup_error_on_failure)

crunch_ignore (add:
  storeWord storeWordVM loadWord setRegister getRegister getRestartPC
  debugPrint set_register get_register invalidateTLB_ASID invalidateTLB_VAASID
  cleanByVA cleanByVA_PoU invalidateByVA invalidateByVA_I invalidate_I_PoU
  cleanInvalByVA branchFlush clean_D_PoU cleanInvalidate_D_PoC cleanInvalidateL2Range
  invalidateL2Range cleanL2Range flushBTAC writeContextID isb dsb dmb
  setHardwareASID setCurrentPD setNextPC maskInterrupt clearMemory throw_on_false)

crunch_ignore (add:
  cap_swap_ext cap_move_ext cap_insert_ext empty_slot_ext create_cap_ext tcb_sched_action
  reschedule_required set_thread_state_ext switch_if_required_to
  attempt_switch_to timer_tick set_priority retype_region_ext)

end
