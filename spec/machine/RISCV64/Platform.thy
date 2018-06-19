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
  "../../../lib/Lib"
  "../../../lib/Word_Lib/Word_Enum"
  "../../../lib/Defs"
  "../Setup_Locale"
begin

context Arch begin global_naming RISCV64

type_synonym irq = word32
type_synonym paddr = word64


abbreviation (input) "toPAddr \<equiv> id"
abbreviation (input) "fromPAddr \<equiv> id"

definition
  kernelBase :: word64 where
  "kernelBase = 0xFFFFFFFF80000000"

definition
  paddrLoad :: word64 where
  "paddrLoad = 0xC0000000"

definition
  kernelBaseOffset :: word64 where
  "kernelBaseOffset = kernelBase - paddrLoad"

definition
  pptrBase :: word64 where
  "pptrBase = 0xFFFFFFC000000000"

definition
  baseOffset :: word64 where
  "baseOffset = pptrBase - 0x80000000 (* PADDR_BASE *)"

definition
  ptrFromPAddr :: "paddr \<Rightarrow> word64" where
  "ptrFromPAddr paddr \<equiv> paddr + baseOffset"

definition
  addrFromPPtr :: "word64 \<Rightarrow> paddr" where
  "addrFromPPtr pptr \<equiv> pptr - baseOffset"

definition
  addrFromKPPtr :: "word64 \<Rightarrow> paddr" where
  "addrFromKPPtr pptr \<equiv> pptr - kernelBaseOffset"

definition
  minIRQ :: "irq" where
  "minIRQ \<equiv> 0"

definition
  maxIRQ :: "irq" where
  "maxIRQ \<equiv> 5"

end
end
