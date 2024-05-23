(*
 * Copyright 2022, Proofcraft Pty Ltd
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "AARCH64 Machine Types"

theory MachineTypes
imports
  Word_Lib.WordSetup
  Monads.Nondet_Empty_Fail
  Monads.Nondet_Reader_Option
  Lib.HaskellLib_H
  Platform
begin

context Arch begin global_naming AARCH64

#INCLUDE_SETTINGS keep_constructor=hyp_fault_type
#INCLUDE_SETTINGS keep_constructor=virt_timer

text \<open>
  An implementation of the machine's types, defining register set
  and some observable machine state.
\<close>

section "Types"

#INCLUDE_HASKELL SEL4/Machine/RegisterSet/AARCH64.hs CONTEXT AARCH64 decls_only NOT UserContext UserMonad Word getRegister setRegister newContext FPUState newFPUState

#INCLUDE_HASKELL SEL4/Object/Structures/AARCH64.hs CONTEXT AARCH64 ONLY VPPIEventIRQ VirtTimer
(*<*)

end

context begin interpretation Arch .
requalify_types register vcpureg vppievent_irq virt_timer
end

context Arch begin global_naming AARCH64

#INCLUDE_HASKELL SEL4/Machine/RegisterSet/AARCH64.hs CONTEXT AARCH64 instanceproofs
#INCLUDE_HASKELL SEL4/Object/Structures/AARCH64.hs CONTEXT AARCH64 instanceproofs ONLY VPPIEventIRQ VirtTimer
(*>*)
#INCLUDE_HASKELL SEL4/Machine/RegisterSet/AARCH64.hs CONTEXT AARCH64 bodies_only NOT getRegister setRegister newContext newFPUState

section "Machine State"

text \<open>
  Most of the machine state is left underspecified at this level.
  We know it exists, we will declare some interface functions, but
  at this level we do not have access to how this state is transformed
  or what effect it has on the machine.
\<close>
typedecl machine_state_rest

end

qualify AARCH64 (in Arch)

record
  machine_state =
  irq_masks :: "AARCH64.irq \<Rightarrow> bool"
  irq_state :: nat
  underlying_memory :: "machine_word \<Rightarrow> word8"
  device_state :: "machine_word \<Rightarrow> word8 option"
  machine_state_rest :: AARCH64.machine_state_rest

axiomatization
  irq_oracle :: "nat \<Rightarrow> AARCH64.irq"
where
  irq_oracle_max_irq: "\<forall>n. irq_oracle n <= AARCH64.maxIRQ"

end_qualify

context Arch begin global_naming AARCH64

text \<open>
  The machine monad is used for operations on the state defined above.
\<close>
type_synonym 'a machine_monad = "(machine_state, 'a) nondet_monad"

end

translations
  (type) "'c AARCH64.machine_monad" <= (type) "(AARCH64.machine_state, 'c) nondet_monad"

context Arch begin global_naming AARCH64

text \<open>
  After kernel initialisation all IRQs are masked.
\<close>
definition
  "init_irq_masks \<equiv> \<lambda>_. True"

text \<open>
  The initial contents of the user-visible memory is 0.
\<close>
definition
  init_underlying_memory :: "machine_word \<Rightarrow> word8"
  where
  "init_underlying_memory \<equiv> \<lambda>_. 0"

text \<open>
  We leave open the underspecified rest of the machine state in
  the initial state.
\<close>
definition
  init_machine_state :: machine_state where
 "init_machine_state \<equiv> \<lparr> irq_masks = init_irq_masks,
                         irq_state = 0,
                         underlying_memory = init_underlying_memory,
                         device_state = Map.empty,
                         machine_state_rest = undefined \<rparr>"

#INCLUDE_HASKELL SEL4/Machine/Hardware/AARCH64.hs CONTEXT AARCH64 ONLY \
  PT_Type \
  VMFaultType HypFaultType vmFaultTypeFSR VMPageSize pageBits ptTranslationBits \
  pageBitsForSize \
  hcrVCPU hcrNative vgicHCREN sctlrDefault sctlrEL1VM actlrDefault gicVCPUMaxNumLR \
  vcpuBits

end

context begin interpretation Arch .
requalify_types vmpage_size
end

context Arch begin global_naming AARCH64

#INCLUDE_HASKELL SEL4/Machine/Hardware/AARCH64.hs CONTEXT AARCH64 instanceproofs ONLY VMFaultType HypFaultType VMPageSize

end
end
