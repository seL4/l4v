(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Platform Definitions"

theory Platform
imports
  "Lib.Defs"
  "Lib.Lib"
  "Word_Lib.WordSetup"
  Setup_Locale
begin

context Arch begin global_naming ARM

text \<open>
  This theory lists platform-specific types and basic constants, in particular
  the types of interrupts and physical addresses, constants for the
  kernel location, the offsets between physical and virtual kernel
  addresses, as well as the range of IRQs on the platform.
\<close>

type_synonym irq = "10 word"
type_synonym paddr = word32

abbreviation (input) "toPAddr \<equiv> id"
abbreviation (input) "fromPAddr \<equiv> id"

definition pageColourBits :: nat where
  "pageColourBits \<equiv> 2"

definition cacheLineBits :: nat where
  "cacheLineBits = 5"

definition cacheLine :: nat where
  "cacheLine = 2^cacheLineBits"

(* Arch specific kernel base address used for haskell spec *)
definition pptrBase :: word32 where
  "pptrBase \<equiv> 0xe0000000"

definition physBase :: word32 where
  "physBase \<equiv> 0x10000000"

definition pptrBaseOffset :: word32 where
  "pptrBaseOffset \<equiv> pptrBase - physBase"

definition kernelELFBase :: word32 where
  "kernelELFBase \<equiv> pptrBase + (physBase && mask 22)"

definition kernelELFPAddrBase :: word32 where
  "kernelELFPAddrBase \<equiv> 0x10000000"

definition kernelELFBaseOffset :: word32 where
  "kernelELFBaseOffset \<equiv> kernelELFBase - kernelELFPAddrBase"

definition ptrFromPAddr :: "paddr \<Rightarrow> word32" where
  "ptrFromPAddr paddr \<equiv> paddr + pptrBaseOffset"

definition addrFromPPtr :: "word32 \<Rightarrow> paddr" where
  "addrFromPPtr pptr \<equiv> pptr - pptrBaseOffset"

definition addrFromKPPtr :: "word32 \<Rightarrow> paddr" where
  "addrFromKPPtr kpptr \<equiv> kpptr - kernelELFBaseOffset"

definition minIRQ :: "irq" where
  "minIRQ \<equiv> 0"

definition maxIRQ :: "irq" where
  "maxIRQ \<equiv> 0x9F"

end

end
