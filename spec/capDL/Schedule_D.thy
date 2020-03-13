(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Schedule_D
imports KHeap_D
begin

(*
 * Collect the set of runnable threads in the system.
 *)
definition
  all_active_tcbs :: "cdl_state \<Rightarrow> cdl_object_id set"
where
  "all_active_tcbs state \<equiv> {x \<in> dom (cdl_objects state).
      \<exists> a. (cdl_objects state) x = Some (Tcb a)
          \<and> ( ((cdl_tcb_caps a) tcb_pending_op_slot) = (Some RunningCap) \<or> ((cdl_tcb_caps a) tcb_pending_op_slot) = (Some RestartCap))}"

definition
  active_tcbs_in_domain :: "word8 \<Rightarrow> cdl_state \<Rightarrow> cdl_object_id set"
where
  "active_tcbs_in_domain domain state  = {x \<in> dom (cdl_objects state).
      \<exists> a. (cdl_objects state) x = Some (Tcb a)
          \<and> ( ((cdl_tcb_caps a) tcb_pending_op_slot) = (Some RunningCap) \<or> ((cdl_tcb_caps a) tcb_pending_op_slot) = (Some RestartCap))
          \<and> cdl_tcb_domain a = domain }"

(*
 * Switch to a new thread.
 *)
definition
  switch_to_thread :: "cdl_object_id option \<Rightarrow> unit k_monad"
where
  "switch_to_thread target \<equiv>
     modify (\<lambda> t. t\<lparr> cdl_current_thread := target \<rparr>)"

definition
  change_current_domain :: "unit k_monad"
where
  "change_current_domain = do
     next_domain \<leftarrow> select UNIV;
     modify      (\<lambda>s. s\<lparr> cdl_current_domain := next_domain \<rparr>)
   od"
(*
 * Scheduling is fully nondeterministic at this level.
 *)
definition
  schedule :: "unit k_monad"
where
  "schedule \<equiv> do
     change_current_domain;
     next_domain \<leftarrow> gets cdl_current_domain;
     threads     \<leftarrow> gets (active_tcbs_in_domain next_domain);
     next_thread \<leftarrow> select threads;
     switch_to_thread (Some next_thread)
   od \<sqinter> do
     change_current_domain;
     switch_to_thread None
   od"


end


