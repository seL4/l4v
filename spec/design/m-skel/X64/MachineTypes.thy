(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "x86-64bit Machine Types"

theory MachineTypes
imports
  Word_Lib.WordSetup
  Monads.Empty_Fail
  Monads.No_Fail
  Monads.Reader_Option_ND
  Lib.HaskellLib_H
  Platform
begin

context Arch begin global_naming X64

text \<open>
  An implementation of the machine's types, defining register set
  and some observable machine state.
\<close>

section "Types"

#INCLUDE_HASKELL SEL4/Machine/RegisterSet/X64.lhs CONTEXT X64 decls_only NOT UserContext UserMonad Word getRegister setRegister newContext
(*<*)

end

context begin interpretation Arch .
requalify_types register gdtslot
end

context Arch begin global_naming X64

#INCLUDE_HASKELL SEL4/Machine/RegisterSet/X64.lhs CONTEXT X64 instanceproofs
(*>*)
#INCLUDE_HASKELL SEL4/Machine/RegisterSet/X64.lhs CONTEXT X64 bodies_only NOT getRegister setRegister newContext

section "Machine State"

text \<open>
  Most of the machine state is left underspecified at this level.
  We know it exists, we will declare some interface functions, but
  at this level we do not have access to how this state is transformed
  or what effect it has on the machine.
\<close>
typedecl machine_state_rest

end

qualify X64 (in Arch)

record
  machine_state =
  irq_masks :: "X64.irq \<Rightarrow> bool"
  irq_state :: nat
  underlying_memory :: "word64 \<Rightarrow> word8"
  device_state :: "word64 \<Rightarrow> word8 option"
  machine_state_rest :: X64.machine_state_rest

consts irq_oracle :: "nat \<Rightarrow> word8"

end_qualify

context Arch begin global_naming X64

text \<open>
  The machine monad is used for operations on the state defined above.
\<close>
type_synonym 'a machine_monad = "(machine_state, 'a) nondet_monad"

end

translations
  (type) "'c X64.machine_monad" <= (type) "(X64.machine_state, 'c) nondet_monad"

context Arch begin global_naming X64

text \<open>
  After kernel initialisation all IRQs are masked.
\<close>
definition
  "init_irq_masks \<equiv> \<lambda>_. True"

text \<open>
  The initial contents of the user-visible memory is 0.
\<close>
definition
  init_underlying_memory :: "word64 \<Rightarrow> word8"
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

#INCLUDE_HASKELL SEL4/Machine/Hardware/X64.lhs CONTEXT X64 ONLY VMFaultType HypFaultType VMPageSize VMMapType pageBits ptTranslationBits pageBitsForSize

end

context begin interpretation Arch .
requalify_types vmpage_size vmmap_type
end

context Arch begin global_naming X64

#INCLUDE_HASKELL SEL4/Machine/Hardware/X64.lhs CONTEXT X64 instanceproofs ONLY VMFaultType HypFaultType VMPageSize VMMapType

end
end
