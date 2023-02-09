(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Include_AI
imports
  Lib.Lib
  ArchCrunchSetup_AI
  Monads.Eisbach_WP
  Monads.Strengthen_Setup
  ASpec.Syscall_A
  Lib.LemmaBucket
  Lib.ListLibLemmas
  Lib.LemmaBucket
  Lib.SplitRule
  Rights_AI
begin

no_notation bind_drop (infixl ">>" 60)

unbundle l4v_word_context

(* Clagged from Bits_R *)

crunch_ignore (add: NonDetMonad.bind return "when" get gets fail assert put modify
  unless select alternative assert_opt gets_the returnOk throwError lift
  bindE liftE whenE unlessE throw_opt assertE liftM liftME sequence_x
  zipWithM_x mapM_x sequence mapM sequenceE_x sequenceE mapME mapME_x
  catch select_f handleE' handleE handle_elseE forM forM_x zipWithM
  filterM forME_x)

crunch_ignore (add: cap_fault_on_failure lookup_error_on_failure
  without_preemption const_on_failure ignore_failure empty_on_failure
  unify_failure throw_on_false preemption_point)

crunch_ignore (add:
  storeWord storeWordVM loadWord setRegister getRegister getRestartPC
  setNextPC)

crunch_ignore (add:
  cap_swap_ext cap_move_ext cap_insert_ext empty_slot_ext create_cap_ext
  reschedule_required set_thread_state_ext tcb_sched_action
  possible_switch_to timer_tick set_priority retype_region_ext)

end
