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
(* FIXME X64: Missing lots of stuff *)

context Arch begin global_naming X64

type_synonym irq = word8
type_synonym paddr = word64


abbreviation (input) "toPAddr \<equiv> id"
abbreviation (input) "fromPAddr \<equiv> id"

definition
  pptrBase :: word64 where
  "pptrBase = 0xffffff8000000000"

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
  "addrFromKPPtr pptr \<equiv> undefined"

definition
  pageColourBits :: "nat" where
  "pageColourBits \<equiv> undefined"

definition
  minIRQ :: "irq" where
  "minIRQ \<equiv> 0"

definition
  maxIRQ :: "irq" where
  "maxIRQ \<equiv> 125"

datatype cr3 = X64CR3 word64 (*pml4*) word64 (*asid*)

primrec CR3BaseAddress where
"CR3BaseAddress (X64CR3 v0 _) = v0"

primrec cr3BaseAddress_update where
"cr3BaseAddress_update f (X64CR3 v0 v1) = (X64CR3 (f v0) v1)"

primrec cr3pcid where
"cr3pcid (X64CR3 _ v1) = v1"

primrec cr3pcid_update where
"cr3pcid_update f (X64CR3 v0 v1) = (X64CR3 v0 (f v1))"



end
end
