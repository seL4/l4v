(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter {* ARM\_HYP Machine Types *}

theory MachineTypes
imports
  "../../../lib/Monad_WP/NonDetMonad"
  "../Setup_Locale"
  Platform
begin
context Arch begin global_naming ARM_HYP

#INCLUDE_SETTINGS keep_constructor=hyp_fault_type

text {*
  An implementation of the machine's types, defining register set
  and some observable machine state.
*}

section "Types"

#INCLUDE_HASKELL SEL4/Machine/RegisterSet/ARM_HYP.lhs CONTEXT ARM_HYP decls_only
(*<*)

type_synonym machine_word_len = 32

definition
  word_size_bits :: "'a :: numeral"
where
  "word_size_bits \<equiv> 2"

end

context begin interpretation Arch .
requalify_types register

end

context Arch begin global_naming ARM_HYP

#INCLUDE_HASKELL SEL4/Machine/RegisterSet/ARM_HYP.lhs CONTEXT ARM_HYP instanceproofs
(*>*)
#INCLUDE_HASKELL SEL4/Machine/RegisterSet/ARM_HYP.lhs CONTEXT ARM_HYP bodies_only

section "Machine State"

text {*
  Most of the machine state is left underspecified at this level.
  We know it exists, we will declare some interface functions, but
  at this level we do not have access to how this state is transformed
  or what effect it has on the machine.
*}
typedecl machine_state_rest

text {*
  The exclusive monitors state is observable in user mode.
  The type for this is the type used in the Cambridge HOL4 ARM model.
*}
type_synonym exclusive_monitors = "(word32 \<Rightarrow> bool) list \<times> (word32 \<times> nat \<Rightarrow> bool)"

text {*
  The full machine state is the state observable by the kernel plus
  the underspecified rest above. The observable parts are the
  interrupt controller (which IRQs are masked) and the memory of the
  machine. The latter is shadow state: kernel memory is kept in a
  separate, more abstract datatype; user memory is reflected down
  to the underlying memory of the machine.
*}
end

qualify ARM_HYP (in Arch)

record
  machine_state =
  irq_masks :: "ARM_HYP.irq \<Rightarrow> bool"
  irq_state :: nat
  underlying_memory :: "word32 \<Rightarrow> word8"
  device_state :: "word32 \<Rightarrow> word8 option"
  exclusive_state :: ARM_HYP.exclusive_monitors
  machine_state_rest :: ARM_HYP.machine_state_rest

consts irq_oracle :: "nat \<Rightarrow> 10 word"

axiomatization irq_oracle_max_irqInst where
  irq_oracle_max_irq: "\<forall> n. (irq_oracle n) <= ARM_HYP.maxIRQ"

end_qualify

context Arch begin global_naming ARM_HYP

text {*
  The machine monad is used for operations on the state defined above.
*}
type_synonym 'a machine_monad = "(machine_state, 'a) nondet_monad"

end

translations
  (type) "'c ARM_HYP.machine_monad" <= (type) "(ARM_HYP.machine_state, 'c) nondet_monad"

context Arch begin global_naming ARM_HYP

text {*
  After kernel initialisation all IRQs are masked.
*}
definition
  "init_irq_masks \<equiv> \<lambda>_. True"

text {*
  The initial contents of the user-visible memory is 0.
*}
definition
  init_underlying_memory :: "word32 \<Rightarrow> word8"
  where
  "init_underlying_memory \<equiv> \<lambda>_. 0"

text {*
  The initial exclusive state is the same constant
  that clearExMonitor defaults it to.
*}

consts' default_exclusive_state :: exclusive_monitors

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
                         exclusive_state = default_exclusive_state,
                         machine_state_rest = undefined \<rparr>"


(* Machine/Hardware/ARM.lhs - hardware_asid, vmfault_type and vmpage_size *)
#INCLUDE_HASKELL SEL4/Machine/Hardware/ARM_HYP.lhs CONTEXT ARM_HYP ONLY HardwareASID VMFaultType HypFaultType VMPageSize pageBits pageBitsForSize

end

context begin interpretation Arch .
requalify_types vmpage_size
end

context Arch begin global_naming ARM_HYP

#INCLUDE_HASKELL SEL4/Machine/Hardware/ARM_HYP.lhs CONTEXT ARM_HYP instanceproofs ONLY HardwareASID VMFaultType HypFaultType VMPageSize

end
end
