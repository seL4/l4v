(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
The TCB and thread related specifications.
*)

chapter "Threads and TCBs"

theory Tcb_A
imports Schedule_A "$L4V_ARCH/ArchTcb_A"
begin

context begin interpretation Arch .

requalify_consts
  arch_activate_idle_thread
  sanitise_register
  arch_get_sanitise_register_info
  arch_post_modify_registers

end

section "Activating Threads"

text \<open>Reactivate a thread if it is not already running.\<close>
definition
  restart :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad" where
 "restart thread \<equiv> do
    state \<leftarrow> get_thread_state thread;
    sc_opt \<leftarrow> get_tcb_obj_ref tcb_sched_context thread;
    when (\<not> runnable state \<and> \<not> idle state) $ do
      cancel_ipc thread;
      set_thread_state thread Restart;
      maybeM sched_context_resume sc_opt;
      test_possible_switch_to thread
    od
  od"

text \<open>This action is performed at the end of a system call immediately before
control is restored to a used thread. If it needs to be restarted then its
program counter is set to the operation it was performing rather than the next
operation. The idle thread is handled specially.\<close>
definition
  activate_thread :: "(unit, 'z::state_ext) s_monad" where
  "activate_thread \<equiv> do
     thread \<leftarrow> gets cur_thread;
     yt_opt \<leftarrow> get_tcb_obj_ref tcb_yield_to thread;
     when (yt_opt\<noteq>None) $ complete_yield_to thread;
     state \<leftarrow> get_thread_state thread;
     (case state
       of Running \<Rightarrow> return ()
        | Restart \<Rightarrow> (do
            pc \<leftarrow> as_user thread getRestartPC;
            as_user thread $ setNextPC pc;
            set_thread_state thread Running
          od)
        | IdleThreadState \<Rightarrow> arch_activate_idle_thread thread
        | _ \<Rightarrow> fail)
   od"

section "Thread Message Formats"

definition
  load_word_offs :: "obj_ref \<Rightarrow> nat \<Rightarrow> (machine_word,'z::state_ext) s_monad" where
 "load_word_offs ptr offs \<equiv>
    do_machine_op $ loadWord (ptr + of_nat (offs * word_size))"
definition
  load_word_offs_word :: "obj_ref \<Rightarrow> data \<Rightarrow> (machine_word,'z::state_ext) s_monad" where
 "load_word_offs_word ptr offs \<equiv>
    do_machine_op $ loadWord (ptr + (offs * word_size))"

text \<open>Copy message registers from one thread to another.\<close>
definition
  copy_mrs :: "obj_ref \<Rightarrow> obj_ref option \<Rightarrow> obj_ref \<Rightarrow>
               obj_ref option \<Rightarrow> length_type \<Rightarrow> (length_type,'z::state_ext) s_monad" where
  "copy_mrs sender sbuf receiver rbuf n \<equiv>
   do
     hardware_mrs \<leftarrow> return $ take (unat n) msg_registers;
     mapM (\<lambda>r. do
         v \<leftarrow> as_user sender $ getRegister r;
         as_user receiver $ setRegister r v
       od) hardware_mrs;
     buf_mrs \<leftarrow> case (sbuf, rbuf) of
       (Some sb_ptr, Some rb_ptr) \<Rightarrow> mapM (\<lambda>x. do
                                       v \<leftarrow> load_word_offs sb_ptr x;
                                       store_word_offs rb_ptr x v
                                     od)
               [length msg_registers + 1 ..< Suc (unat n)]
     | _ \<Rightarrow> return [];
     return $ min n $ nat_to_len $ length hardware_mrs + length buf_mrs
   od"

text \<open>The ctable and vtable slots of the TCB.\<close>
definition
  get_tcb_ctable_ptr :: "obj_ref \<Rightarrow> cslot_ptr" where
  "get_tcb_ctable_ptr tcb_ref \<equiv> (tcb_ref, tcb_cnode_index 0)"

definition
  get_tcb_vtable_ptr :: "obj_ref \<Rightarrow> cslot_ptr" where
  "get_tcb_vtable_ptr tcb_ref \<equiv> (tcb_ref, tcb_cnode_index 1)"

text \<open>Optionally update the tcb at an address.\<close>
definition
  option_update_thread :: "obj_ref \<Rightarrow> ('a \<Rightarrow> tcb \<Rightarrow> tcb) \<Rightarrow> 'a option \<Rightarrow> (unit,'z::state_ext) s_monad" where
 "option_update_thread thread fn \<equiv> case_option (return ()) (\<lambda>v. thread_set (fn v) thread)"

text \<open>Check that a related capability is at an address. This is done before
calling @{const cap_insert} to avoid a corner case where the would-be parent of
the cap to be inserted has been moved or deleted.\<close>
definition
  check_cap_at :: "cap \<Rightarrow> cslot_ptr \<Rightarrow> (unit,'z::state_ext) s_monad \<Rightarrow> (unit,'z::state_ext) s_monad" where
 "check_cap_at cap slot m \<equiv> do
    cap' \<leftarrow> get_cap slot;
    when (same_object_as cap cap') m
  od"


text \<open>Helper function for binding notifications\<close>
definition
  bind_notification :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "bind_notification tcbptr ntfnptr \<equiv> do
     set_ntfn_obj_ref ntfn_bound_tcb_update ntfnptr $ Some tcbptr;
     set_tcb_obj_ref tcb_bound_notification_update tcbptr $ Some ntfnptr
   od"

text \<open>The definitions of install\_tcb\_cap, install\_tcb\_frame\_cap and invoke\_tcb are moved to
InvocationFuns\_A.thy;
for MCS, the function preemption\_point is defined in InvocationFuns\_A.thy which imports Ipc\_R.
This is because of the dependency on update\_time\_stamp and check\_budget. Some invocation functions
that call preemption\_point, namely, invoke\_untyped, invoke\_cnode, and invoke\_tcb, are also
defined in InvocationFuns\_A.thy\<close>

definition
  set_domain :: "obj_ref \<Rightarrow> domain \<Rightarrow> (unit, 'z::state_ext) s_monad" where
  "set_domain tptr new_dom \<equiv> do
     cur \<leftarrow> gets cur_thread;
     tcb_sched_action tcb_sched_dequeue tptr;
     thread_set_domain tptr new_dom;
     sched \<leftarrow> is_schedulable tptr;
     when sched $ tcb_sched_action tcb_sched_enqueue tptr; \<comment> \<open>schedulable and dequeued\<close>
     when (tptr = cur) $ reschedule_required
   od"

definition invoke_domain:: "obj_ref \<Rightarrow> domain \<Rightarrow> (data list,'z::state_ext) p_monad"
where
  "invoke_domain thread domain \<equiv>
     liftE (do set_domain thread domain; return [] od)"

text \<open>Get all of the message registers, both from the sending thread's current
register file and its IPC buffer.\<close>
definition
  get_mrs :: "obj_ref \<Rightarrow> obj_ref option \<Rightarrow> message_info \<Rightarrow>
              (message list,'z::state_ext) s_monad" where
  "get_mrs thread buf info \<equiv> do
     context \<leftarrow> thread_get (arch_tcb_get_registers o tcb_arch) thread;
     cpu_mrs \<leftarrow> return (map context msg_registers);
     buf_mrs \<leftarrow> case buf
       of None      \<Rightarrow> return []
        | Some pptr \<Rightarrow> mapM (\<lambda>x. load_word_offs pptr x)
               [length msg_registers + 1 ..< Suc msg_max_length];
     return (take (unat (mi_length info)) $ cpu_mrs @ buf_mrs)
   od"

end
