(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Platform Definitions"

theory Platform
imports
  "Lib.Lib"
  "Word_Lib.WordSetup"
  "Lib.Defs"
  Setup_Locale
  Kernel_Config
begin

context Arch begin global_naming X64

type_synonym irq = word8
type_synonym paddr = word64


abbreviation (input) "toPAddr \<equiv> id"
abbreviation (input) "fromPAddr \<equiv> id"

definition
  pptrBase :: word64 where
  "pptrBase = 0xffffff8000000000"

definition
  kernelELFBaseOffset :: word64 where
  "kernelELFBaseOffset = 0xffffffff80000000"

definition
  pptrUserTop :: word64 where
  "pptrUserTop = 0x00007fffffffffff"

definition
  cacheLineBits :: nat where
  "cacheLineBits = 5"

definition
  cacheLine :: nat where
  "cacheLine = 2^cacheLineBits"

definition
  ptrFromPAddr :: "paddr \<Rightarrow> word64" where
  "ptrFromPAddr paddr \<equiv> paddr + pptrBase"

definition
  addrFromPPtr :: "word64 \<Rightarrow> paddr" where
  "addrFromPPtr pptr \<equiv> pptr - pptrBase"

definition
  addrFromKPPtr :: "word64 \<Rightarrow> paddr" where
  "addrFromKPPtr pptr \<equiv> pptr - kernelELFBaseOffset"

definition
  pageColourBits :: "nat" where
  "pageColourBits \<equiv> undefined"

definition
  minIRQ :: "irq" where
  "minIRQ \<equiv> 0"

definition
  maxIRQ :: "irq" where
  "maxIRQ \<equiv> 125"

definition
  minUserIRQ :: "irq" where
  "minUserIRQ \<equiv> 16"

definition
  maxUserIRQ :: "irq" where
  "maxUserIRQ \<equiv> 123"

datatype cr3 = X64CR3 (CR3BaseAddress: word64) (cr3pcid: word64)

primrec cr3BaseAddress_update :: "(word64 \<Rightarrow> word64) \<Rightarrow> cr3 \<Rightarrow> cr3"
where
  "cr3BaseAddress_update f (X64CR3 v0 v1) = (X64CR3 (f v0) v1)"

primrec cr3pcid_update :: "(word64 \<Rightarrow> word64) \<Rightarrow> cr3 \<Rightarrow> cr3"
where
  "cr3pcid_update f (X64CR3 v0 v1) = (X64CR3 v0 (f v1))"


end
end
