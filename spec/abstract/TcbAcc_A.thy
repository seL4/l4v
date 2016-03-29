(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

(* 
TCB accessor functions
*)

chapter "Accessors for Threads and TCBs"

theory TcbAcc_A
imports CSpace_A
begin

text {* Store or load a word at an offset from an IPC buffer. *}
definition
  store_word_offs :: "obj_ref \<Rightarrow> nat \<Rightarrow> machine_word \<Rightarrow> (unit,'z::state_ext) s_monad" where
 "store_word_offs ptr offs v \<equiv>
    do s \<leftarrow> get;
       assert (in_user_frame (ptr + of_nat (offs * word_size)) s);
       do_machine_op $ storeWord (ptr + of_nat (offs * word_size)) v
    od"

text {* Set the message registers of a thread. *}
definition
  set_mrs :: "obj_ref \<Rightarrow> obj_ref option \<Rightarrow> message list \<Rightarrow> (length_type,'z::state_ext) s_monad" where
  "set_mrs thread buf msgs \<equiv>
   do
     tcb \<leftarrow> gets_the $ get_tcb thread;
     context \<leftarrow> return (tcb_context tcb);
     new_regs \<leftarrow> return (\<lambda>reg. if reg \<in> set (take (length msgs) msg_registers)
                              then msgs ! (the_index msg_registers reg)
                              else context reg);
     set_object thread (TCB (tcb \<lparr> tcb_context := new_regs \<rparr>));
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