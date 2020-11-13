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
  Setup_Locale
begin

context Arch begin global_naming RISCV64

type_synonym irq = "6 word" (* match IRQ_CNODE_SLOT_BITS in seL4 config *)
type_synonym paddr = word64

abbreviation (input) "toPAddr \<equiv> id"
abbreviation (input) "fromPAddr \<equiv> id"

(* Address space layout (from seL4/include/arch/riscv/arch/64/mode/hardware.h):

The top half of the address space is reserved for the kernel. This means that 256 top level
entries are for the user, and 256 are for the kernel. This will be further split into the
'regular' kernel window, which contains mappings to physical memory, a small (1GiB) higher
kernel image window that we use for running the actual kernel from and a top 1GiB window for
kernel device mappings. This means that between PPTR_BASE and
KERNEL_ELF_BASE there are 254 entries remaining, which represents how much physical memory
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
           ----|  +-------------KERNEL_ELF_BASE-+ --+ 2^64 - 2GiB + (KERNEL_ELF_PADDR_BASE % 1GiB)
           |   |  |                             |
           |   -> +-----------------------------+ --+ 2^64 - 2GiB = (KERNEL_ELF_BASE % 1GiB)
Shared 1GiB|      |                             |   |
table entry|      |           PSpace            |   |
           |      |  (direct kernel mappings)   |   +----+
           ------>|                             |   |    |
                  |                             |   |    |
                  +-------------------PPTR_BASE-+ --+ 2^64 - 2^b
                  |                             |        |         +-------------------------+
                  |                             |        |         |                         |
                  |                             |        |         |                         |
                  |          Invalid            |        |         |                         |
                  |                             |        |         |           not           |
                  |                             |        |         |         kernel          |
                  |                             |        |         |       addressable       |
                  +--------------------USER_TOP-+  2^c   |         |                         |
                  |                             |        |         |                         |
                  |                             |        |         |                         |
                  |                             |        |      +- --------------------------+  PADDR_TOP =
                  |                             |        |      |  |                         |    PPTR_TOP - PPTR_BASE
                  |                             |        |      |  |                         |
                  |                             |        |      |  |                         |
                  |            User             |        |      |  |                         |
                  |                             |        |      |  |                         |
                  |                             |        +------+  +-------------------------+  KDEV_BASE - KERNEL_ELF_BASE + PADDR_LOAD
                  |                             |     kernel    |  |        Kernel ELF       |
                  |                             |   addressable |  +-------------------------+  KERNEL_ELF_PADDR_BASE
                  |                             |               |  |                         |
                  |                             |               |  |                         |
                  +-----------------------------+  0            +- +-------------------------+  0 PADDR_BASE

                     virtual address space                          physical address space

 c = one less than number of bits the page tables can translate
   = sign extension bit for canonical addresses
   (= 47 on x64, 38 on RISCV64 sv39, 47 on RISCV64 sv48)
 b = The number of bits used by kernel mapping.
   = 38 (half of the 1 level page table) on RISCV64 sc39
   = 39 (entire second level page table) on aarch64 / X64 / sv48
*)

(* NOTE: a number of these constants appear in the Haskell, but are shadowed
   here due to more convenient formulation.
   Examples: kernelELFBase, kernelELFBaseOffset, kernelELFAddressBase, pptrBase
   Ideally and in future, we should converge on a single authoritative source
   of these constants.
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

definition kernelELFPAddrBase :: word64
  where
  "kernelELFPAddrBase = 0x84000000"

definition kernelELFBaseOffset :: word64
  where
  "kernelELFBaseOffset = kernelELFBase - kernelELFPAddrBase"

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

schematic_goal pptrUserTop_def': (* direct constant definition *)
  "RISCV64.pptrUserTop = numeral ?x"
  by (simp add: RISCV64.pptrUserTop_def canonical_bit_def mask_def del: word_eq_numeral_iff_iszero)

definition paddrBase :: word64
  where
  "paddrBase \<equiv> 0"

definition pptrBaseOffset :: word64
  where
  "pptrBaseOffset = pptrBase - paddrBase"

definition ptrFromPAddr :: "paddr \<Rightarrow> word64"
  where
  "ptrFromPAddr paddr \<equiv> paddr + pptrBaseOffset"

definition addrFromPPtr :: "word64 \<Rightarrow> paddr"
  where
  "addrFromPPtr pptr \<equiv> pptr - pptrBaseOffset"

definition addrFromKPPtr :: "word64 \<Rightarrow> paddr"
  where
  "addrFromKPPtr pptr \<equiv> pptr - kernelELFBaseOffset"

definition minIRQ :: "irq"
  where
  "minIRQ \<equiv> 0"

definition maxIRQ :: "irq"
  where
  "maxIRQ \<equiv> 54"

(* Reserved by C to represent "not an IRQ" *)
definition irqInvalid :: "irq"
  where
  "irqInvalid \<equiv> 0"

definition pageColourBits :: nat
  where
  "pageColourBits \<equiv> undefined" \<comment> \<open>not implemented on this platform\<close>

end
end
