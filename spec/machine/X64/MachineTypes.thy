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
  "../../../lib/Enumeration"
  "../../../lib/WordSetup"
  "../../../lib/wp/NonDetMonad"
  "../../../lib/HaskellLib_H"
  Platform
begin
context Arch begin global_naming X64

(* !!! Generated File !!! Skeleton in ../spec/design/m-skel *)

text {*
  An implementation of the machine's types, defining register set 
  and some observable machine state.
*}

section "Types"

datatype register =
    RAX
  | RBX
  | RCX
  | RDX
  | RSI
  | RDI
  | RBP
  | R8
  | R9
  | R10
  | R11
  | R12
  | R13
  | R14
  | R15
  | DS
  | ES
  | FS
  | GS
  | FaultInstruction
  | TLS_BASE
  | PADDING_REGISTER
  | ErrorRegister
  | NextIP
  | CS
  | RFLAGS
  | RSP
  | SS

type_synonym machine_word = "word64"

datatype gdtslot =
    GDT_NULL
  | GDT_CS_0
  | GDT_DS_0
  | GDT_TSS
  | GDT_TSS_Padding
  | GDT_CS_3
  | GDT_DS_3
  | GDT_TLS
  | GDT_IPCBUF
  | GDT_ENTRIES

consts'
gdtToSel :: "gdtslot \<Rightarrow> machine_word"

consts'
gdtToSel_masked :: "gdtslot \<Rightarrow> machine_word"

consts'
initContext :: "(register * machine_word) list"

consts'
sanitiseRegister :: "register \<Rightarrow> machine_word \<Rightarrow> machine_word"

(*<*)
end
context begin interpretation Arch .
requalify_types register gdtslot
end
context Arch begin global_naming X64

end
qualify X64 (in Arch) 
(* register instance proofs *)
(*<*)
instantiation register :: enum begin
interpretation Arch .
definition
  enum_register: "enum_class.enum \<equiv> 
    [ 
      RAX,
      RBX,
      RCX,
      RDX,
      RSI,
      RDI,
      RBP,
      R8,
      R9,
      R10,
      R11,
      R12,
      R13,
      R14,
      R15,
      DS,
      ES,
      FS,
      GS,
      FaultInstruction,
      TLS_BASE,
      PADDING_REGISTER,
      ErrorRegister,
      NextIP,
      CS,
      RFLAGS,
      RSP,
      SS
    ]"


definition
  "enum_class.enum_all (P :: register \<Rightarrow> bool) \<longleftrightarrow> Ball UNIV P"

definition
  "enum_class.enum_ex (P :: register \<Rightarrow> bool) \<longleftrightarrow> Bex UNIV P"

  instance
  apply intro_classes
   apply (safe, simp)
   apply (case_tac x)
  apply (simp_all add: enum_register enum_all_register_def enum_ex_register_def)
  by fast+
end

instantiation register :: enum_alt
begin
interpretation Arch .
definition
  enum_alt_register: "enum_alt \<equiv> 
    alt_from_ord (enum :: register list)"
instance ..
end

instantiation register :: enumeration_both
begin
interpretation Arch .
instance by (intro_classes, simp add: enum_alt_register)
end

(*>*)
end_qualify
context Arch begin global_naming X64

end
qualify X64 (in Arch) 
(* gdtslot instance proofs *)
(*<*)
instantiation gdtslot :: enum begin
interpretation Arch .
definition
  enum_gdtslot: "enum_class.enum \<equiv> 
    [ 
      GDT_NULL,
      GDT_CS_0,
      GDT_DS_0,
      GDT_TSS,
      GDT_TSS_Padding,
      GDT_CS_3,
      GDT_DS_3,
      GDT_TLS,
      GDT_IPCBUF,
      GDT_ENTRIES
    ]"


definition
  "enum_class.enum_all (P :: gdtslot \<Rightarrow> bool) \<longleftrightarrow> Ball UNIV P"

definition
  "enum_class.enum_ex (P :: gdtslot \<Rightarrow> bool) \<longleftrightarrow> Bex UNIV P"

  instance
  apply intro_classes
   apply (safe, simp)
   apply (case_tac x)
  apply (simp_all add: enum_gdtslot enum_all_gdtslot_def enum_ex_gdtslot_def)
  by fast+
end

instantiation gdtslot :: enum_alt
begin
interpretation Arch .
definition
  enum_alt_gdtslot: "enum_alt \<equiv> 
    alt_from_ord (enum :: gdtslot list)"
instance ..
end

instantiation gdtslot :: enumeration_both
begin
interpretation Arch .
instance by (intro_classes, simp add: enum_alt_gdtslot)
end

(*>*)
end_qualify
context Arch begin global_naming X64

(*>*)
definition
"capRegister \<equiv> RBX"

definition
"msgInfoRegister \<equiv> RSI"

definition
"msgRegisters \<equiv> [RDI, RBP]"

definition
"badgeRegister \<equiv> capRegister"

definition
"frameRegisters \<equiv> FaultInstruction # RSP # RFLAGS # [RAX  .e.  R15]"

definition
"gpRegisters \<equiv> [TLS_BASE, FS, GS]"

definition
"exceptionMessage \<equiv> [FaultInstruction, RSP, RFLAGS]"

definition
"syscallMessage \<equiv> [RAX  .e.  RBP] @ [NextIP, RSP, RFLAGS]"

defs gdtToSel_def:
"gdtToSel g\<equiv> (fromIntegral (fromEnum g) `~shiftL~` 3 ) || 3"

defs gdtToSel_masked_def:
"gdtToSel_masked g \<equiv> gdtToSel g || 3"

definition
"selCS3 \<equiv> gdtToSel_masked GDT_CS_3"

definition
"selDS3 \<equiv> gdtToSel_masked GDT_DS_3"

definition
"selTLS \<equiv> gdtToSel_masked GDT_TLS"

definition
"selIPCBUF \<equiv> gdtToSel_masked GDT_IPCBUF"

definition
"selCS0 \<equiv> gdtToSel_masked GDT_CS_0"

definition
"selDS0 \<equiv> gdtToSel GDT_DS_0"

defs initContext_def:
"initContext\<equiv> [(DS, selDS3), (ES, selDS3), (CS, selCS3), (SS, selDS3)
              ,(RFLAGS, (1 << 9) || bit 1)]"

defs sanitiseRegister_def:
"sanitiseRegister x0 v\<equiv> (case x0 of
    RFLAGS \<Rightarrow>   
    v || (1 << 1) && (complement (bit 3)) && (complement (bit 5))  || bit 9
    && ((1 << 12) - 1)
  | FS \<Rightarrow>    if v \<noteq> selTLS \<and> v \<noteq> selIPCBUF then 0 else v
  | GS \<Rightarrow>    if v \<noteq> selTLS \<and> v \<noteq> selIPCBUF then 0 else v
  | _ \<Rightarrow>    v
  )"


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
                         machine_state_rest = undefined \<rparr>"

datatype vmpage_size =
    X64SmallPage
  | X64LargePage
  | X64HugePage

datatype vmfault_type =
    X64DataFault
  | X64InstructionFault

definition
pageBits :: "nat"
where
"pageBits \<equiv> 12"

definition
ptTranslationBits :: "nat"
where
"ptTranslationBits \<equiv> 9"

definition
pageBitsForSize :: "vmpage_size \<Rightarrow> nat"
where
"pageBitsForSize x0\<equiv> (case x0 of
    X64SmallPage \<Rightarrow>    pageBits
  | X64LargePage \<Rightarrow>    pageBits + ptTranslationBits
  | X64HugePage \<Rightarrow>    pageBits + ptTranslationBits + ptTranslationBits
  )"


end

context begin interpretation Arch .
requalify_types vmpage_size
end

context Arch begin global_naming X64

end
qualify X64 (in Arch) 
(* vmpage_size instance proofs *)
(*<*)
instantiation vmpage_size :: enum begin
interpretation Arch .
definition
  enum_vmpage_size: "enum_class.enum \<equiv> 
    [ 
      X64SmallPage,
      X64LargePage,
      X64HugePage
    ]"


definition
  "enum_class.enum_all (P :: vmpage_size \<Rightarrow> bool) \<longleftrightarrow> Ball UNIV P"

definition
  "enum_class.enum_ex (P :: vmpage_size \<Rightarrow> bool) \<longleftrightarrow> Bex UNIV P"

  instance
  apply intro_classes
   apply (safe, simp)
   apply (case_tac x)
  apply (simp_all add: enum_vmpage_size enum_all_vmpage_size_def enum_ex_vmpage_size_def)
  by fast+
end

instantiation vmpage_size :: enum_alt
begin
interpretation Arch .
definition
  enum_alt_vmpage_size: "enum_alt \<equiv> 
    alt_from_ord (enum :: vmpage_size list)"
instance ..
end

instantiation vmpage_size :: enumeration_both
begin
interpretation Arch .
instance by (intro_classes, simp add: enum_alt_vmpage_size)
end

(*>*)
end_qualify
context Arch begin global_naming X64


end
end
