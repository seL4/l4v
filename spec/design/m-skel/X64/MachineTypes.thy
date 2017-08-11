(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "x86-64bit Machine Types"

theory MachineTypes
imports
  "../../../lib/Word_Lib/Enumeration"
  "../../../lib/$L4V_ARCH/WordSetup"
  "../../../lib/Monad_WP/NonDetMonad"
  "../../../lib/HaskellLib_H"
  Platform
begin

context Arch begin global_naming X64

text {*
  An implementation of the machine's types, defining register set
  and some observable machine state.
*}

section "Types"

#INCLUDE_HASKELL SEL4/Machine/RegisterSet/X64.lhs CONTEXT X64 decls_only
(*<*)

section "Machine Words"

type_synonym machine_word_len = 64

definition
  word_size_bits :: "'a :: numeral"
where
  "word_size_bits \<equiv> 3"

end

context begin interpretation Arch .
requalify_types register gdtslot
end

context Arch begin global_naming X64

#INCLUDE_HASKELL SEL4/Machine/RegisterSet/X64.lhs CONTEXT X64 instanceproofs
(*>*)
#INCLUDE_HASKELL SEL4/Machine/RegisterSet/X64.lhs CONTEXT X64 bodies_only

section "Machine State"

text {*
  Most of the machine state is left underspecified at this level.
  We know it exists, we will declare some interface functions, but
  at this level we do not have access to how this state is transformed
  or what effect it has on the machine.
*}
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

text {*
  The machine monad is used for operations on the state defined above.
*}
type_synonym 'a machine_monad = "(machine_state, 'a) nondet_monad"

end

translations
  (type) "'c X64.machine_monad" <= (type) "(X64.machine_state, 'c) nondet_monad"

context Arch begin global_naming X64

text {*
  After kernel initialisation all IRQs are masked.
*}
definition
  "init_irq_masks \<equiv> \<lambda>_. True"

text {*
  The initial contents of the user-visible memory is 0.
*}
definition
  init_underlying_memory :: "word64 \<Rightarrow> word8"
  where
  "init_underlying_memory \<equiv> \<lambda>_. 0"

text {*
  We leave open the underspecified rest of the machine state in
  the initial state.
*}
definition
  init_machine_state :: machine_state where
 "init_machine_state \<equiv> \<lparr> irq_masks = init_irq_masks,
                         irq_state = 0,
                         underlying_memory = init_underlying_memory,
                         device_state = empty,
                         machine_state_rest = undefined \<rparr>"

#INCLUDE_HASKELL SEL4/Machine/Hardware/X64.lhs CONTEXT X64 ONLY HardwareASID VMFaultType HypFaultType VMPageSize VMMapType pageBits ptTranslationBits pageBitsForSize

end

context begin interpretation Arch .
requalify_types vmpage_size vmmap_type
end

context Arch begin global_naming X64

#INCLUDE_HASKELL SEL4/Machine/Hardware/X64.lhs CONTEXT X64 instanceproofs ONLY HardwareASID VMFaultType HypFaultType VMPageSize VMMapType

end
end
