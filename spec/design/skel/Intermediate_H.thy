(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Intermediate"

theory Intermediate_H
imports "API_H"
begin

(*
 * Intermediate function bodies that were once in the Haskell spec, but are
 * now no longer.
 *
 * The idea is that these "Old Haskell" specs allow us to have refinement as
 * follows:
 *
 *  C <---> Haskell <---> Old Haskell <---> Abstract
 *
 * This provides a stepping stone for refactoring the Haskell without breaking
 * the upper proofs until a later time.
 *)

consts
insertNewCaps :: "object_type \<Rightarrow> machine_word \<Rightarrow> machine_word list \<Rightarrow> machine_word \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> unit kernel"

consts
createObjects :: "machine_word \<Rightarrow> nat \<Rightarrow> Structures_H.kernel_object \<Rightarrow> nat \<Rightarrow> machine_word list kernel"

consts
createObjects' :: "machine_word \<Rightarrow> nat \<Rightarrow> kernel_object \<Rightarrow> nat \<Rightarrow> unit kernel"

consts
createNewCaps :: "object_type \<Rightarrow> machine_word \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> capability list kernel"

consts
Arch_createNewCaps :: "object_type \<Rightarrow> machine_word \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> arch_capability list kernel"

defs insertNewCaps_def:
"insertNewCaps newType srcSlot destSlots regionBase magnitudeBits dev \<equiv> (do
    caps \<leftarrow> createNewCaps newType regionBase (length destSlots) magnitudeBits dev;
    zipWithM_x (insertNewCap srcSlot) destSlots caps
  od)"

defs createNewCaps_def:
"createNewCaps t regionBase numObjects userSize dev \<equiv>
    (case toAPIType t of
          Some TCBObject \<Rightarrow> (do
            curdom \<leftarrow> curDomain;
            addrs \<leftarrow> createObjects regionBase numObjects (injectKO ((makeObject ::tcb)\<lparr>tcbDomain := curdom\<rparr>)) 0;
            return $ map (\<lambda> addr. ThreadCap addr) addrs
          od)
        | Some EndpointObject \<Rightarrow> (do
            addrs \<leftarrow> createObjects regionBase numObjects (injectKO (makeObject ::endpoint)) 0;
            return $ map (\<lambda> addr. EndpointCap addr 0 True True True True) addrs
          od)
        | Some NotificationObject \<Rightarrow> (do
            addrs \<leftarrow> createObjects regionBase numObjects (injectKO (makeObject ::notification)) 0;
            return $ map (\<lambda> addr. NotificationCap addr 0 True True) addrs
          od)
        | Some SchedContextObject \<Rightarrow> (do
            scp \<leftarrow> return (PPtr $ fromPPtr regionBase);
            newCap \<leftarrow> return (SchedContextCap scp userSize);
            addrs \<leftarrow> createObjects regionBase numObjects
              (injectKO ((makeObject ::sched_context)\<lparr>scRefills := replicate (refillAbsoluteMax newCap) emptyRefill, scSize := userSize - minSchedContextBits\<rparr>)) 0;
            return $ map (\<lambda> addr. SchedContextCap addr userSize) addrs
          od)
        | Some ReplyObject \<Rightarrow> (do
            addrs \<leftarrow> createObjects regionBase numObjects (injectKO (makeObject ::reply)) 0;
            return $ map (\<lambda> addr. ReplyCap addr True) addrs
          od)
        | Some ArchTypes_H.CapTableObject \<Rightarrow> (do
            addrs \<leftarrow> createObjects regionBase numObjects (injectKO (makeObject ::cte)) userSize;
            modify (\<lambda> ks. ks \<lparr> gsCNodes := (\<lambda> addr.
              if addr `~elem~` map fromPPtr addrs then Just userSize
              else gsCNodes ks addr)\<rparr>);
            return $ map (\<lambda> addr. CNodeCap addr userSize 0 0) addrs
          od)
        | Some ArchTypes_H.Untyped \<Rightarrow>
            return $ map
                (\<lambda> n. UntypedCap dev (regionBase + n * 2 ^ (fromIntegral userSize)) userSize 0)
                [0  .e.  (fromIntegral numObjects) - 1]
        | None \<Rightarrow>   (do
            archCaps \<leftarrow> Arch_createNewCaps t regionBase numObjects userSize dev;
            return $ map ArchObjectCap archCaps
          od)
        )"

defs createObjects_def:
"createObjects ptr numObjects val gSize \<equiv> (do
        oBits \<leftarrow> return ( objBitsKO val);
        gBits \<leftarrow> return ( oBits + gSize);
        createObjects' ptr numObjects val gSize;
        return (map (\<lambda> n. (ptr + n `~shiftL~` gBits))
                [0  .e.  (of_nat numObjects) - 1])
  od)"

defs createObjects'_def:
"createObjects' ptr numObjects val gSize\<equiv> (do
        oBits \<leftarrow> return ( objBitsKO val);
        gBits \<leftarrow> return ( oBits + gSize);
        unless (fromPPtr ptr && mask gBits = 0) $
            alignError gBits;
        ps \<leftarrow> gets ksPSpace;
        end \<leftarrow> return ( fromPPtr ptr + fromIntegral ((numObjects `~shiftL~` gBits) - 1));
        (before, _) \<leftarrow> return ( lookupAround2 end (psMap ps));
        (case before of
              None \<Rightarrow>   return ()
            | Some (x, _) \<Rightarrow>   haskell_assert (x < fromPPtr ptr)
                []
            );
        addresses \<leftarrow> return ( map
                (\<lambda> n. fromPPtr ptr + n `~shiftL~` oBits)
                [0  .e.  (fromIntegral numObjects `~shiftL~` gSize) - 1]);
        map' \<leftarrow> return ( foldR
               (\<lambda> addr map. data_map_insert addr val map)
               (psMap ps) addresses);
        ps' \<leftarrow> return ( ps \<lparr> psMap := map' \<rparr>);
        modify (\<lambda> ks. ks \<lparr> ksPSpace := ps'\<rparr>)
od)"


end
