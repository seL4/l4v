(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "ARM Machine Types"

theory MachineTypes
imports
  Word_Lib.WordSetup
  Monads.Nondet_Empty_Fail
  Monads.Nondet_Reader_Option
  Setup_Locale
  Platform
begin

context Arch begin arch_global_naming

text \<open>
  An implementation of the machine's types, defining register set
  and some observable machine state.
\<close>

section "Types"

#INCLUDE_HASKELL SEL4/Machine/RegisterSet/ARM.lhs CONTEXT ARM decls_only NOT UserContext UserMonad Word getRegister setRegister newContext FPUState newFPUState
(*<*)

end

arch_requalify_types register

context Arch begin arch_global_naming

#INCLUDE_HASKELL SEL4/Machine/RegisterSet/ARM.lhs CONTEXT ARM instanceproofs
(*>*)
#INCLUDE_HASKELL SEL4/Machine/RegisterSet/ARM.lhs CONTEXT ARM bodies_only NOT getRegister setRegister newContext newFPUState

section "Machine State"

text \<open>
  Most of the machine state is left underspecified at this level.
  We know it exists, we will declare some interface functions, but
  at this level we do not have access to how this state is transformed
  or what effect it has on the machine.
\<close>
typedecl machine_state_rest

text \<open>
  The exclusive monitors state is observable in user mode.
  The type for this is the type used in the Cambridge HOL4 ARM model.
\<close>
type_synonym exclusive_monitors = "(word32 \<Rightarrow> bool) list \<times> (word32 \<times> nat \<Rightarrow> bool)"

text \<open>
  The full machine state is the state observable by the kernel plus
  the underspecified rest above. The observable parts are the
  interrupt controller (which IRQs are masked) and the memory of the
  machine. The latter is shadow state: kernel memory is kept in a
  separate, more abstract datatype; user memory is reflected down
  to the underlying memory of the machine.
\<close>
end

qualify ARM (in Arch)

record
  machine_state =
  irq_masks :: "ARM.irq \<Rightarrow> bool"
  irq_state :: nat
  underlying_memory :: "word32 \<Rightarrow> word8"
  device_state :: "word32 \<Rightarrow> word8 option"
  exclusive_state :: ARM.exclusive_monitors
  machine_state_rest :: ARM.machine_state_rest

axiomatization
  irq_oracle :: "nat \<Rightarrow> ARM.irq"
where
  irq_oracle_max_irq: "\<forall> n. irq_oracle n <= Kernel_Config.maxIRQ"

end_qualify

context Arch begin arch_global_naming

text \<open>
  The machine monad is used for operations on the state defined above.
\<close>
type_synonym 'a machine_monad = "(machine_state, 'a) nondet_monad"

end

translations
  (type) "'c ARM.machine_monad" <= (type) "(ARM.machine_state, 'c) nondet_monad"

context Arch begin arch_global_naming

text \<open>
  After kernel initialisation all IRQs are masked.
\<close>
definition
  "init_irq_masks \<equiv> \<lambda>_. True"

text \<open>
  The initial contents of the user-visible memory is 0.
\<close>
definition
  init_underlying_memory :: "word32 \<Rightarrow> word8"
  where
  "init_underlying_memory \<equiv> \<lambda>_. 0"

text \<open>
  The initial exclusive state is the same constant
  that clearExMonitor defaults it to.
\<close>

consts' default_exclusive_state :: exclusive_monitors

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
                         exclusive_state = default_exclusive_state,
                         machine_state_rest = undefined \<rparr>"


(* Machine/Hardware/ARM.lhs - hardware_asid, vmfault_type and vmpage_size *)
#INCLUDE_HASKELL SEL4/Machine/Hardware/ARM.lhs CONTEXT ARM ONLY HardwareASID VMFaultType VMPageSize HypFaultType pageBits pageBitsForSize

end

arch_requalify_types vmpage_size

context Arch begin arch_global_naming

#INCLUDE_HASKELL SEL4/Machine/Hardware/ARM.lhs CONTEXT ARM instanceproofs ONLY HardwareASID VMFaultType VMPageSize HypFaultType

end
end
