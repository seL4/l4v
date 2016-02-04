(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)


theory MachineExports
imports "./$L4V_ARCH/MachineOps"
begin
  
unqualify_types (in "$L4V_ARCH")
  machine_word 
  vmfault_type
  irq

unqualify_consts (in "$L4V_ARCH")
  "getActiveIRQ :: (irq option) machine_monad"
  "maskInterrupt :: bool \<Rightarrow> irq \<Rightarrow> unit machine_monad"
  "freeMemory :: machine_word \<Rightarrow> nat \<Rightarrow> unit machine_monad"
  "loadWord :: machine_word \<Rightarrow> machine_word machine_monad"
  "storeWord :: machine_word \<Rightarrow> machine_word \<Rightarrow> unit machine_monad"
  "storeWordVM :: machine_word \<Rightarrow> machine_word \<Rightarrow> unit machine_monad"
  "setNextPC :: machine_word \<Rightarrow> unit user_monad"
  "getRestartPC :: machine_word user_monad"
  "setRegister :: register \<Rightarrow> machine_word \<Rightarrow> unit user_monad"
  "getRegister :: register \<Rightarrow> machine_word user_monad"
  "sanitiseRegister :: register \<Rightarrow> machine_word \<Rightarrow> machine_word"
  "initContext :: (register * machine_word) list"
  "exceptionMessage :: register list"
  "syscallMessage :: register list"
  "gpRegisters :: register list"
  "frameRegisters :: register list"
  "setInterruptMode :: irq \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> unit machine_monad"

end
