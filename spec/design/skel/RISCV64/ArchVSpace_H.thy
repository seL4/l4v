(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
  VSpace lookup code.
*)

theory ArchVSpace_H
imports
  CNode_H
  Untyped_H
  KI_Decls_H
  ArchVSpaceDecls_H
begin

context Arch begin arch_global_naming (H)

#INCLUDE_HASKELL SEL4/Kernel/VSpace/RISCV64.hs CONTEXT RISCV64_H bodies_only ArchInv=ArchRetypeDecls_H ONLY pteAtIndex getPPtrFromHWPTE isPageTablePTE ptBitsLeft

fun
  lookupPTSlotFromLevel :: "nat => machine_word => machine_word => (nat * machine_word) kernel"
where
  "lookupPTSlotFromLevel 0 ptPtr vPtr =
     return (ptBitsLeft 0, ptSlotIndex 0 ptPtr vPtr)"
| "lookupPTSlotFromLevel level ptPtr vPtr = do
     pte <- pteAtIndex level ptPtr vPtr;
     if isPageTablePTE pte
     then do
       checkPTAt (getPPtrFromHWPTE pte);
       lookupPTSlotFromLevel (level - 1) (getPPtrFromHWPTE pte) vPtr
     od
     else return (ptBitsLeft level, ptSlotIndex level ptPtr vPtr)
   od"

fun
  lookupPTFromLevel :: "nat => machine_word => machine_word => machine_word =>
    (lookup_failure, machine_word) kernel_f"
where
  "lookupPTFromLevel level ptPtr vPtr targetPtPtr = doE
    assertE (ptPtr \<noteq> targetPtPtr);
    unlessE (0 < level) $ throw InvalidRoot;
    slot <- returnOk $ ptSlotIndex level ptPtr vPtr;
    pte <- withoutFailure $ getObject slot;
    unlessE (isPageTablePTE pte) $ throw InvalidRoot;
    ptr <- returnOk (getPPtrFromHWPTE pte);
    if ptr = targetPtPtr
        then returnOk slot
        else doE
          liftE $ checkPTAt ptr;
          lookupPTFromLevel (level - 1) ptr vPtr targetPtPtr
        odE
  odE"

#INCLUDE_HASKELL SEL4/Kernel/VSpace/RISCV64.hs CONTEXT RISCV64_H bodies_only ArchInv=ArchRetypeDecls_H NOT lookupPTSlotFromLevel lookupPTFromLevel pteAtIndex getPPtrFromHWPTE isPageTablePTE ptBitsLeft checkPTAt

end

end
