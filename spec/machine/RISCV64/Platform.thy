(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Platform Definitions"

theory Platform
imports
  "Lib.Lib"
  "Word_Lib.Word_Enum"
  "Lib.Defs"
  "../Setup_Locale"
begin

context Arch begin global_naming RISCV64

type_synonym irq = "3 word" (* maxIRQ currently 5; increase for real h/w *)
type_synonym paddr = word64

abbreviation (input) "toPAddr \<equiv> id"
abbreviation (input) "fromPAddr \<equiv> id"

(* Address space layout:
The top half of the address space is reserved for the kernel. This means that 256 top level
entries are for the user, and 256 are for the kernel. This will be further split into the
'regular' kernel window, which contains mappings to physical memory, a small (1GiB) higher
kernel image window that we use for running the actual kernel from and a top 1GiB window for
kernel device mappings. This means that between PPTR_BASE and
KERNEL_BASE there are 254 entries remaining, which represents how much physical memory
can be used.

Almost all of the top 256 kernel entries will contain 1GiB page mappings. The only 2 entries
that contain a 2nd level PageTable consisting of 2MiB page entries is the entry
for the 1GiB Kernel ELF region and the 1GiB region corresponding to the physical memory
of the kernel ELF in the kernel window.  The same 2nd level PageTable is used and so both
entries refer to the same 1GiB of physical memory.
This means that the 1GiB kernel ELF mapping will correspond to physical memory with a 1GiB
alignment.

                  +-----------------------------+ 2^64
                  |        Kernel Devices       |
               -> +-------------------KDEV_BASE-+ 2^64 - 1GiB
               |  |         Kernel ELF          |
           ----|  +-------------KERNEL_ELF_BASE-+ --+ 2^64 - 2GiB + (PADDR_LOAD % 1GiB)
           |   |  |                             |
           |   -> +-----------------KERNEL_BASE-+ --+ 2^64 - 2GiB
Shared 1GiB|      |                             |   |
table entry|      |           PSpace            |   |
           |      |  (direct kernel mappings)   |   +----+
           ------>|                             |   |    |
                  |                             |   |    |
                  +-------------------PPTR_BASE-+ --+ 2^64 - 2^c
                  |                             |        |         +-------------------------+
                  |                             |        |         |                         |
                  |                             |        |         |                         |
                  |          Invalid            |        |         |                         |
                  |                             |        |         |           not           |
                  |                             |        |         |         kernel          |
                  |                             |        |         |       addressable       |
                  +-----------------------------+  2^c   |         |                         |
                  |                             |        |         |                         |
                  |                             |        |         |                         |
                  |                             |        |      +- --------------------------+  PADDR_TOP =
                  |                             |        |      |  |                         |    KERNEL_BASE - PPTR_BASE
                  |                             |        |      |  |                         |
                  |                             |        |      |  |                         |
                  |            User             |        |      |  |                         |
                  |                             |        |      |  |                         |
                  |                             |        +------+  +-------------------------+  PADDR_HIGH_TOP =
                  |                             |     kernel    |  |        Kernel ELF       |    (KDEV_BASE - KERNEL_ELF_BASE + PADDR_LOAD)
                  |                             |   addressable |  +-------------------------+  PADDR_LOAD
                  |                             |               |  |                         |
                  |                             |               |  |                         |
                  +-----------------------------+  0            +- +-------------------------+  0 PADDR_BASE

                     virtual address space                          physical address space


c = one less than number of bits the page tables can translate
  = sign extension bit for canonical addresses
  (= 47 on x64, 38 on RISCV64 sv39, 47 on RISCV64 sv48)

*)

definition canonical_bit :: nat
  where
  "canonical_bit = 38"

definition kdevBase :: word64
  where
  "kdevBase = - (1 << 30)" (* 2^64 - 1 GiB *)

lemma "kdevBase = 0xFFFFFFFFC0000000" (* Sanity check with C *)
  by (simp add: kdevBase_def)

definition kernelELFBase :: word64
  where
  "kernelELFBase = - (1 << 31) + 0x4000000" (* 2^64 - 2 GiB + 2^26 *)

lemma "kernelELFBase = 0xFFFFFFFF84000000" (* Sanity check with C *)
  by (simp add: kernelELFBase_def)

definition paddrLoad :: word64
  where
  "paddrLoad = 0x84000000"

definition kernelBaseOffset :: word64
  where
  "kernelBaseOffset = kernelELFBase - paddrLoad"

definition pptrBase :: word64
  where
  "pptrBase = - (1 << canonical_bit)"

lemma "pptrBase = 0xFFFFFFC000000000" (* Sanity check with C *)
  by (simp add: pptrBase_def canonical_bit_def)

definition pptrUserTop :: word64
  where
  "pptrUserTop \<equiv> mask canonical_bit && ~~mask 12" (* for page boundary alignment *)

lemma "pptrUserTop = 0x0000003ffffff000" (* Sanity check with C *)
  by (simp add: pptrUserTop_def canonical_bit_def mask_def)

definition pAddr_base :: word64
  where
  "pAddr_base \<equiv> 0"

definition baseOffset :: word64
  where
  "baseOffset = pptrBase - pAddr_base"

definition ptrFromPAddr :: "paddr \<Rightarrow> word64"
  where
  "ptrFromPAddr paddr \<equiv> paddr + baseOffset"

definition addrFromPPtr :: "word64 \<Rightarrow> paddr"
  where
  "addrFromPPtr pptr \<equiv> pptr - baseOffset"

definition addrFromKPPtr :: "word64 \<Rightarrow> paddr"
  where
  "addrFromKPPtr pptr \<equiv> pptr - kernelBaseOffset"

definition minIRQ :: "irq"
  where
  "minIRQ \<equiv> 0"

definition maxIRQ :: "irq"
  where
  "maxIRQ \<equiv> 53"

(* Reserved by C to represent "not an IRQ" *)
definition irqInvalid :: "irq"
  where
  "irqInvalid \<equiv> 0"

definition pageColourBits :: nat
  where
  "pageColourBits \<equiv> undefined" \<comment> \<open>not implemented on this platform\<close>

end
end
