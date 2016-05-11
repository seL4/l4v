(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "Intermediate"

theory Intermediate_H
imports "../API_H"
begin
context begin interpretation Arch .
requalify_consts
  clearMemory
end
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
insertNewCaps :: "object_type \<Rightarrow> machine_word \<Rightarrow> machine_word list \<Rightarrow> machine_word \<Rightarrow> nat \<Rightarrow> unit kernel"

consts
createObjects :: "machine_word \<Rightarrow> nat \<Rightarrow> ('a :: pspace_storable) \<Rightarrow> nat \<Rightarrow> machine_word list kernel"

consts
createObjects' :: "machine_word \<Rightarrow> nat \<Rightarrow> kernel_object \<Rightarrow> nat \<Rightarrow> unit kernel"

consts
createNewCaps :: "object_type \<Rightarrow> machine_word \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> capability list kernel"

consts
Arch_createNewCaps :: "object_type \<Rightarrow> machine_word \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> arch_capability list kernel"

definition
"createWordObjects ptr numObjects gs\<equiv> (do
    gbits \<leftarrow> return ( objBitsKO (injectKO UserData) + gs);
    addrs \<leftarrow> createObjects ptr numObjects UserData gs;
    doMachineOp $ mapM_x (\<lambda>x. clearMemory (PPtr $ fromPPtr x) ((1::nat) `~shiftL~` gbits)) addrs;
    return addrs
od)"

defs insertNewCaps_def:
"insertNewCaps newType srcSlot destSlots regionBase magnitudeBits\<equiv> (do
    caps \<leftarrow> createNewCaps newType regionBase (length destSlots) magnitudeBits;
    zipWithM_x (insertNewCap srcSlot) destSlots caps
od)"

defs (in Arch) Arch_createNewCaps_def:
"Arch_createNewCaps t regionBase numObjects arg4 \<equiv>
    let pointerCast = PPtr \<circ> fromPPtr
    in (case t of 
        APIObjectType v5 \<Rightarrow> 
            haskell_fail []
        | SmallPageObject \<Rightarrow>  (do
            addrs \<leftarrow> createWordObjects regionBase numObjects 0;
            modify (\<lambda> ks. ks \<lparr> gsUserPages := (\<lambda> addr.
              if addr `~elem~` map fromPPtr addrs then Just ARMSmallPage
              else gsUserPages ks addr)\<rparr>);
            return $ map (\<lambda> n. PageCap (pointerCast n) VMReadWrite
                    ARMSmallPage Nothing) addrs
        od)
        | LargePageObject \<Rightarrow>  (do
            addrs \<leftarrow> createWordObjects regionBase numObjects 4;
            modify (\<lambda> ks. ks \<lparr> gsUserPages := (\<lambda> addr.
              if addr `~elem~` map fromPPtr addrs then Just ARMLargePage
              else gsUserPages ks addr)\<rparr>);
            return $ map (\<lambda> n. PageCap (pointerCast n) VMReadWrite
                    ARMLargePage Nothing) addrs
        od)
        | SectionObject \<Rightarrow>  (do
            addrs \<leftarrow> createWordObjects regionBase numObjects 8;
            modify (\<lambda> ks. ks \<lparr> gsUserPages := (\<lambda> addr.
              if addr `~elem~` map fromPPtr addrs then Just ARMSection
              else gsUserPages ks addr)\<rparr>);
            return $ map (\<lambda> n. PageCap (pointerCast n) VMReadWrite
                    ARMSection Nothing) addrs
        od)
        | SuperSectionObject \<Rightarrow>  (do
            addrs \<leftarrow> createWordObjects regionBase numObjects 12;
            modify (\<lambda> ks. ks \<lparr> gsUserPages := (\<lambda> addr.
              if addr `~elem~` map fromPPtr addrs then Just ARMSuperSection
              else gsUserPages ks addr)\<rparr>);
            return $ map (\<lambda> n. PageCap (pointerCast n) VMReadWrite
                    ARMSuperSection Nothing) addrs
        od)
        | PageTableObject \<Rightarrow>  (do
            ptSize \<leftarrow> return ( ptBits - objBits (makeObject ::pte));
            addrs \<leftarrow> createObjects regionBase numObjects (makeObject ::pte) ptSize;
            objSize \<leftarrow> return (((1::nat) `~shiftL~` ptBits));
            pts \<leftarrow> return ( map pointerCast addrs);
            doMachineOp $ mapM_x (flip clearMemoryVM ptBits) pts;
            doMachineOp $ mapM_x (\<lambda>x. cleanCacheRange_PoU x (x + (fromIntegral objSize) - 1)
                                                          (addrFromPPtr x)) pts;
            return $ map (\<lambda> pt. PageTableCap pt Nothing) pts
        od)
        | PageDirectoryObject \<Rightarrow>  (do
            pdSize \<leftarrow> return ( pdBits - objBits (makeObject ::pde));
            addrs \<leftarrow> createObjects regionBase numObjects (makeObject ::pde) pdSize;
            objSize \<leftarrow> return ( ((1::nat) `~shiftL~` pdBits));
            pds \<leftarrow> return ( map pointerCast addrs);
            doMachineOp $ mapM_x (flip clearMemoryVM pdBits) pds;
            mapM_x copyGlobalMappings pds;
            doMachineOp $ mapM_x (\<lambda>x. cleanCacheRange_PoU x (x + (fromIntegral objSize) - 1)
                                                          (addrFromPPtr x)) pds;
            return $ map (\<lambda> pd. PageDirectoryCap pd Nothing) pds
        od)
        )"

defs createNewCaps_def:
"createNewCaps t regionBase numObjects userSize \<equiv>
    (case toAPIType t of
          Some TCBObject \<Rightarrow>   (do
            addrs \<leftarrow> createObjects regionBase numObjects (makeObject ::tcb) 0;
            curdom \<leftarrow> curDomain;
            mapM_x (\<lambda>tptr. threadSet (tcbDomain_update (\<lambda>_. curdom)) tptr) addrs;
            return $ map (\<lambda> addr. ThreadCap addr) addrs
          od)
        | Some EndpointObject \<Rightarrow>   (do
            addrs \<leftarrow> createObjects regionBase numObjects (makeObject ::endpoint) 0;
            return $ map (\<lambda> addr. EndpointCap addr 0 True True True) addrs
        od)
        | Some NotificationObject \<Rightarrow>   (do
            addrs \<leftarrow> createObjects regionBase numObjects (makeObject ::notification) 0;
            return $ map (\<lambda> addr. NotificationCap addr 0 True True) addrs
        od)
        | Some ArchTypes_H.CapTableObject \<Rightarrow>   (do
            addrs \<leftarrow> createObjects regionBase numObjects (makeObject ::cte) userSize;
            modify (\<lambda> ks. ks \<lparr> gsCNodes := (\<lambda> addr.
              if addr `~elem~` map fromPPtr addrs then Just userSize
              else gsCNodes ks addr)\<rparr>);
            return $ map (\<lambda> addr. CNodeCap addr userSize 0 0) addrs
        od)
        | Some ArchTypes_H.Untyped \<Rightarrow>  
            return $ map
                (\<lambda> n. UntypedCap (regionBase + n * 2 ^ (fromIntegral userSize)) userSize 0)
                [0  .e.  (fromIntegral numObjects) - 1]
        | None \<Rightarrow>   (do
            archCaps \<leftarrow> Arch_createNewCaps t regionBase numObjects userSize;
            return $ map ArchObjectCap archCaps
        od)
        )"

defs createObjects_def:
"createObjects ptr numObjects val gSize \<equiv> (do
        oBits \<leftarrow> return ( objBitsKO (injectKO val));
        gBits \<leftarrow> return ( oBits + gSize);
        createObjects' ptr numObjects (injectKO val) gSize;
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
