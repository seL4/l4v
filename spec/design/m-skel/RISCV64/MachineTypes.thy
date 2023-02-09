(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "RISCV 64bit Machine Types"

theory MachineTypes
imports
  "Word_Lib.WordSetup"
  "Monads.OptionMonadND"
  "Lib.HaskellLib_H"
  Platform
begin

context Arch begin global_naming RISCV64

text \<open>
  An implementation of the machine's types, defining register set
  and some observable machine state.
\<close>

section "Types"

#INCLUDE_HASKELL SEL4/Machine/RegisterSet/RISCV64.hs CONTEXT RISCV64 decls_only NOT UserContext UserMonad Word getRegister setRegister newContext
(*<*)

end

context begin interpretation Arch .
requalify_types register
end

context Arch begin global_naming RISCV64

#INCLUDE_HASKELL SEL4/Machine/RegisterSet/RISCV64.hs CONTEXT RISCV64 instanceproofs
(*>*)
#INCLUDE_HASKELL SEL4/Machine/RegisterSet/RISCV64.hs CONTEXT RISCV64 bodies_only NOT getRegister setRegister newContext

section "Machine State"

text \<open>
  Most of the machine state is left underspecified at this level.
  We know it exists, we will declare some interface functions, but
  at this level we do not have access to how this state is transformed
  or what effect it has on the machine.
\<close>
typedecl machine_state_rest

end

qualify RISCV64 (in Arch)

record
  machine_state =
  irq_masks :: "RISCV64.irq \<Rightarrow> bool"
  irq_state :: nat
  time_state :: nat \<comment> \<open>position in the time oracle\<close>
  last_machine_time :: "64 word" \<comment> \<open>value we read from timer device\<close>
  underlying_memory :: "machine_word \<Rightarrow> word8"
  device_state :: "machine_word \<Rightarrow> word8 option"
  machine_state_rest :: RISCV64.machine_state_rest

axiomatization
  irq_oracle :: "nat \<Rightarrow> RISCV64.irq"
where
  irq_oracle_max_irq: "\<forall>n. irq_oracle n <= RISCV64.maxIRQ"

text \<open>The values the timer device will return (how much time passed since last query)\<close>
axiomatization
  time_oracle :: "nat \<Rightarrow> nat"

end_qualify

context Arch begin global_naming RISCV64

text \<open>
  The machine monad is used for operations on the state defined above.
\<close>
type_synonym 'a machine_monad = "(machine_state, 'a) nondet_monad"

end

translations
  (type) "'c RISCV64.machine_monad" <= (type) "(RISCV64.machine_state, 'c) nondet_monad"

context Arch begin global_naming RISCV64

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
                         time_state = 0,
                         last_machine_time = 0,
                         underlying_memory = init_underlying_memory,
                         device_state = Map.empty,
                         machine_state_rest = undefined \<rparr>"

#INCLUDE_HASKELL SEL4/Machine/Hardware/RISCV64.hs CONTEXT RISCV64 ONLY VMFaultType HypFaultType vmFaultTypeFSR VMPageSize pageBits ptTranslationBits pageBitsForSize

end

context begin interpretation Arch .
requalify_types vmpage_size
end

context Arch begin global_naming RISCV64

#INCLUDE_HASKELL SEL4/Machine/Hardware/RISCV64.hs CONTEXT RISCV64 instanceproofs ONLY VMFaultType HypFaultType VMPageSize

end
end
