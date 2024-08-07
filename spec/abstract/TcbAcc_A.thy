(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
TCB accessor functions
*)

chapter "Accessors for Threads and TCBs"

theory TcbAcc_A
imports CSpace_A
begin

arch_requalify_consts (A)
  in_user_frame

text \<open>Store or load a word at an offset from an IPC buffer.\<close>
definition
  store_word_offs :: "obj_ref \<Rightarrow> nat \<Rightarrow> machine_word \<Rightarrow> (unit,'z::state_ext) s_monad" where
 "store_word_offs ptr offs v \<equiv>
    do s \<leftarrow> get;
       assert (in_user_frame (ptr + of_nat (offs * word_size)) s);
       do_machine_op $ storeWord (ptr + of_nat (offs * word_size)) v
    od"


(* Needed for page invocations. *)
definition
  set_message_info :: "obj_ref \<Rightarrow> message_info \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "set_message_info thread info \<equiv>
     as_user thread $ setRegister msg_info_register $
                      message_info_to_data info"


definition
  set_mrs :: "obj_ref \<Rightarrow> obj_ref option \<Rightarrow> message list \<Rightarrow> (length_type,'z::state_ext) s_monad" where
  "set_mrs thread buf msgs \<equiv>
   do
     tcb \<leftarrow> gets_the $ get_tcb thread;
     context \<leftarrow> return (arch_tcb_get_registers (tcb_arch tcb));
     new_regs \<leftarrow> return (\<lambda>reg. if reg \<in> set (take (length msgs) msg_registers)
                              then msgs ! (the_index msg_registers reg)
                              else context reg);
     set_object thread (TCB (tcb \<lparr> tcb_arch := arch_tcb_set_registers new_regs (tcb_arch tcb) \<rparr>));
     remaining_msgs \<leftarrow> return (drop (length msg_registers) msgs);
     case buf of
     None      \<Rightarrow> return $ nat_to_len (min (length msg_registers) (length msgs))
   | Some pptr \<Rightarrow> do
       zipWithM_x (\<lambda>x. store_word_offs pptr x)
          [length msg_registers + 1 ..< Suc msg_max_length] remaining_msgs;
       return $ nat_to_len $ min (length msgs) msg_max_length
     od
   od"

end
