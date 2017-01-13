(* THIS FILE WAS AUTOMATICALLY GENERATED. DO NOT EDIT. *)
(* instead, see the skeleton file CSpace_H.thy *)
(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "CSpace"

theory CSpace_H
imports CSpaceDecls_H Object_H
begin

defs lookupCap_def:
"lookupCap thread cPtr \<equiv> liftME fst $ lookupCapAndSlot thread cPtr"

defs lookupCapAndSlot_def:
"lookupCapAndSlot thread cPtr\<equiv> (doE
        slot \<leftarrow> lookupSlotForThread thread cPtr;
        cap \<leftarrow> withoutFailure $ getSlotCap slot;
        returnOk (cap, slot)
odE)"

defs lookupSlotForThread_def:
"lookupSlotForThread thread capptr\<equiv> (doE
        threadRootSlot \<leftarrow> withoutFailure $ getThreadCSpaceRoot thread;
        threadRoot \<leftarrow> withoutFailure $ getSlotCap threadRootSlot;
        bits \<leftarrow> returnOk ( finiteBitSize $ fromCPtr capptr);
        (s, _) \<leftarrow> resolveAddressBits threadRoot capptr bits;
        returnOk s
odE)"

defs lookupSlotForCNodeOp_def:
"lookupSlotForCNodeOp isSource x1 capptr depth\<equiv> (let root = x1 in
  if isCNodeCap root
  then   (doE
    rangeCheck depth 1 $ finiteBitSize capptr;
    lookupErrorOnFailure isSource $ (doE
        result \<leftarrow> resolveAddressBits root capptr depth;
        (let (slot, bitsLeft) = result in
            if bitsLeft = 0
            then  returnOk slot
            else  throw $ DepthMismatch_ \<lparr>
                depthMismatchBitsLeft= bitsLeft,
                depthMismatchBitsFound= 0 \<rparr>
            )
    odE)
  odE)
  else  
    throw $ FailedLookup isSource InvalidRoot
  )"

defs lookupSourceSlot_def:
"lookupSourceSlot \<equiv> lookupSlotForCNodeOp True"

defs lookupTargetSlot_def:
"lookupTargetSlot \<equiv> lookupSlotForCNodeOp False"

defs lookupPivotSlot_def:
"lookupPivotSlot \<equiv> lookupSlotForCNodeOp True"



function 
  resolveAddressBits :: 
  "capability \<Rightarrow> cptr \<Rightarrow> nat \<Rightarrow> 
   (lookup_failure, (machine_word * nat)) kernel_f"
where
 "resolveAddressBits a b c =
(\<lambda>x0 capptr bits.  (let nodeCap = x0 in
  if isCNodeCap nodeCap
  then   (doE
        radixBits \<leftarrow> returnOk ( capCNodeBits nodeCap);
        guardBits \<leftarrow> returnOk ( capCNodeGuardSize nodeCap);
        levelBits \<leftarrow> returnOk ( radixBits + guardBits);
        haskell_assertE (levelBits \<noteq> 0) [];
        offset \<leftarrow> returnOk ( (fromCPtr capptr `~shiftR~` (bits-levelBits)) &&
                   (mask radixBits));
        slot \<leftarrow> withoutFailure $ locateSlotCap nodeCap offset;
        guard \<leftarrow> returnOk ( (fromCPtr capptr `~shiftR~` (bits-guardBits)) &&
                   (mask guardBits));
        unlessE (guardBits \<le> bits \<and> guard = capCNodeGuard nodeCap)
            $ throw $ GuardMismatch_ \<lparr>
                guardMismatchBitsLeft= bits,
                guardMismatchGuardFound= capCNodeGuard nodeCap,
                guardMismatchGuardSize= guardBits \<rparr>;
        whenE (levelBits > bits) $ throw $ DepthMismatch_ \<lparr>
            depthMismatchBitsLeft= bits,
            depthMismatchBitsFound= levelBits \<rparr>;
        bitsLeft \<leftarrow> returnOk ( bits - levelBits);
        if (bitsLeft = 0)
          then returnOk (slot, 0)
          else (doE
            nextCap \<leftarrow> withoutFailure $ getSlotCap slot;
            (case nextCap of
                  CNodeCap _ _ _ _ \<Rightarrow>   (
                    resolveAddressBits nextCap capptr bitsLeft
                  )
                | _ \<Rightarrow>   returnOk (slot, bitsLeft)
                )
          odE)
  odE)
  else   throw InvalidRoot
  ))

a b c"
  by auto

termination
  apply (relation "measure (snd o snd)")
  apply (auto simp add: in_monad split: if_split_asm)
  done

defs
  resolveAddressBits_decl_def [simp]:
  "CSpaceDecls_H.resolveAddressBits \<equiv> resolveAddressBits"

end
