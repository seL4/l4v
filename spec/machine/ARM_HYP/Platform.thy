(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "Platform Definitions"

theory Platform
imports
  "../../../lib/Defs"
  "../../../lib/Lib"
  "../../../lib/ARM_HYP/WordSetup"
  "../Setup_Locale"
begin

context Arch begin global_naming ARM_HYP

text {*
  This theory lists platform-specific types and basic constants, in particular
  the types of interrupts and physical addresses, constants for the
  kernel location, the offsets between physical and virtual kernel
  addresses, as well as the range of IRQs on the platform.
*}

type_synonym irq = "10 word"
type_synonym paddr = word32

abbreviation (input) "toPAddr \<equiv> id"
abbreviation (input) "fromPAddr \<equiv> id"

definition
  pageColourBits :: nat where
  "pageColourBits \<equiv> 2"

definition
  cacheLineBits :: nat where
  "cacheLineBits = 6"

definition
  cacheLine :: nat where
  "cacheLine = 2^cacheLineBits"

definition
  kernelBase_addr :: word32 where
  "kernelBase_addr \<equiv> 0xe0000000"

(* Arch specific kernel base address used for haskell spec *)
definition
  kernelBase :: word32 where
  "kernelBase \<equiv> 0xe0000000"

definition
  physBase :: word32 where
  "physBase \<equiv> 0x10000000"

definition
  physMappingOffset :: word32 where
  "physMappingOffset \<equiv> kernelBase_addr - physBase"

definition
  ptrFromPAddr :: "paddr \<Rightarrow> word32" where
  "ptrFromPAddr paddr \<equiv> paddr + physMappingOffset"

definition
  addrFromPPtr :: "word32 \<Rightarrow> paddr" where
  "addrFromPPtr pptr \<equiv> pptr - physMappingOffset"

definition
  minIRQ :: "irq" where
  "minIRQ \<equiv> 0"

definition
  maxIRQ :: "irq" where
  "maxIRQ \<equiv> 0x9F"

definition irqVGICMaintenance :: "irq"
  where "irqVGICMaintenance \<equiv> 25"

end

end
