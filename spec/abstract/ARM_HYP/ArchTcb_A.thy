(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "ARM-Specific TCB and thread related specifications"

theory ArchTcb_A
imports "../Tcb_A"
begin

context Arch begin global_naming ARM_A

text {* Get all of the message registers, both from the sending thread's current
register file and its IPC buffer. *}
definition
  get_mrs :: "obj_ref \<Rightarrow> obj_ref option \<Rightarrow> message_info \<Rightarrow>
              (message list,'z::state_ext) s_monad" where
  "get_mrs thread buf info \<equiv> do
     context \<leftarrow> thread_get (tcb_context o tcb_arch) thread;
     cpu_mrs \<leftarrow> return (map context msg_registers);
     buf_mrs \<leftarrow> case buf
       of None      \<Rightarrow> return []
        | Some pptr \<Rightarrow> mapM (\<lambda>x. load_word_offs pptr x)
               [length msg_registers + 1 ..< Suc msg_max_length];
     return (take (unat (mi_length info)) $ cpu_mrs @ buf_mrs)
   od"

text {*
This theory provides architecture-specific definitions and datatypes
for virtual-memory support.
*}

text {* Copy a set of registers from a thread to memory and vice versa. *}
definition
  copyRegsToArea :: "register list \<Rightarrow> obj_ref \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "copyRegsToArea regs thread ptr \<equiv> do
     context \<leftarrow> thread_get (tcb_context o tcb_arch) thread;
     zipWithM_x (store_word_offs ptr)
       [0 ..< length regs]
       (map context regs)
  od"

definition
  copyAreaToRegs :: "register list \<Rightarrow> obj_ref \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "copyAreaToRegs regs ptr thread \<equiv> do
     old_regs \<leftarrow> thread_get (tcb_context o tcb_arch) thread;
     vals \<leftarrow> mapM (load_word_offs ptr) [0 ..< length regs];
     vals2 \<leftarrow> return $ zip vals regs;
     vals3 \<leftarrow> return $ map (\<lambda>(v, r). (sanitiseRegister r v, r)) vals2;
     new_regs \<leftarrow> return $ foldl (\<lambda>rs (v, r). rs ( r := v )) old_regs vals3;
     thread_set (\<lambda>tcb. tcb \<lparr> tcb_arch := (tcb_arch tcb)\<lparr> tcb_context := new_regs \<rparr> \<rparr>) thread
   od"

end

end
