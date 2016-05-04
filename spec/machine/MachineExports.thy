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

context begin interpretation Arch .
  
requalify_types
  machine_word 
  vmfault_type
  irq

requalify_consts
  getActiveIRQ
  maskInterrupt
  freeMemory
  loadWord
  storeWord
  storeWordVM
  setNextPC
  getRestartPC
  setRegister
  getRegister
  sanitiseRegister
  initContext
  exceptionMessage
  syscallMessage
  gpRegisters
  frameRegisters
  ackInterrupt
  resetTimer
  maxIRQ
  minIRQ

end

end
