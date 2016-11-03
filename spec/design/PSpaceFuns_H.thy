(* THIS FILE WAS AUTOMATICALLY GENERATED. DO NOT EDIT. *)
(* instead, see the skeleton file PSpaceFuns_H.thy *)
(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "Physical Memory Functions"

theory PSpaceFuns_H
imports
  ObjectInstances_H
  FaultMonad_H
  "../../lib/DataMap"
begin

context begin interpretation Arch .
requalify_consts
  fromPPtr
  PPtr
  freeMemory
  storeWord
  loadWord
end

definition deleteRange :: "( machine_word , 'a ) DataMap.map \<Rightarrow> machine_word \<Rightarrow> nat \<Rightarrow> ( machine_word , 'a ) DataMap.map"
where "deleteRange m ptr bits \<equiv> 
        let inRange = (\<lambda> x. x && ((- mask bits) - 1) = fromPPtr ptr) in
        data_map_filterWithKey (\<lambda> x _. Not (inRange x)) m"

consts'
newPSpace :: "pspace"

consts'
initPSpace :: "(machine_word * machine_word) list \<Rightarrow> unit kernel"

consts'
getObject :: "machine_word \<Rightarrow> ('a :: pspace_storable) kernel"

consts'
setObject :: "machine_word \<Rightarrow> ('a :: pspace_storable) \<Rightarrow> unit kernel"

consts'
placeNewObject :: "machine_word \<Rightarrow> ('a :: pspace_storable) \<Rightarrow> nat \<Rightarrow> unit kernel"

consts'
placeNewObject' :: "machine_word \<Rightarrow> kernel_object \<Rightarrow> nat \<Rightarrow> unit kernel"

consts'
deleteObjects :: "machine_word \<Rightarrow> nat \<Rightarrow> unit kernel"

consts'
deletionIsSafe :: "machine_word \<Rightarrow> nat \<Rightarrow> kernel_state \<Rightarrow> bool"

consts'
cNodePartialOverlap :: "(machine_word \<Rightarrow> nat option) \<Rightarrow> (machine_word \<Rightarrow> bool) \<Rightarrow> bool"

consts'
ksASIDMapSafe :: "kernel_state \<Rightarrow> bool"

consts'
reserveFrame :: "machine_word \<Rightarrow> bool \<Rightarrow> unit kernel"

consts'
loadWordUser :: "machine_word \<Rightarrow> machine_word kernel"

consts'
storeWordUser :: "machine_word \<Rightarrow> machine_word \<Rightarrow> unit kernel"

consts'
pointerInUserData :: "machine_word \<Rightarrow> kernel_state \<Rightarrow> bool"


consts
lookupAround2 :: "('k :: {linorder,finite}) \<Rightarrow> ( 'k , 'a ) DataMap.map \<Rightarrow> (('k * 'a) option * 'k option)"

defs newPSpace_def:
"newPSpace \<equiv> PSpace_ \<lparr> psMap= data_map_empty \<rparr>"

defs initPSpace_def:
"initPSpace arg1 \<equiv> return ()"

defs getObject_def:
"getObject ptr\<equiv> (do
        map \<leftarrow> gets $ psMap \<circ> ksPSpace;
        (before, after) \<leftarrow> return ( lookupAround2 (fromPPtr ptr) map);
        (ptr', val) \<leftarrow> maybeToMonad before;
        loadObject (fromPPtr ptr) ptr' after val
od)"

defs setObject_def:
"setObject ptr val\<equiv> (do
        ps \<leftarrow> gets ksPSpace;
        map \<leftarrow> return ( psMap ps);
        (before, after) \<leftarrow> return ( lookupAround2 (fromPPtr ptr) map);
        (ptr', obj) \<leftarrow> maybeToMonad before;
        obj' \<leftarrow> updateObject val obj (fromPPtr ptr) ptr' after;
        map' \<leftarrow> return ( data_map_insert ptr' obj' map);
        ps' \<leftarrow> return ( ps \<lparr> psMap := map' \<rparr>);
        modify (\<lambda> ks. ks \<lparr> ksPSpace := ps'\<rparr>)
od)"

defs lookupAround2_def:
"lookupAround2 ptr mp \<equiv>
    let
        (before, middle, after) = lookupAround ptr mp;
        after' = maybe Nothing (Just \<circ> fst) after
    in
                              (case middle of
                              Some v \<Rightarrow>   (Just (ptr, v), after')
                            | None \<Rightarrow>   (before, after')
                            )"

defs placeNewObject_def:
"placeNewObject ptr val groupSizeBits \<equiv>
        placeNewObject' ptr (injectKO val) groupSizeBits"

defs placeNewObject'_def:
"placeNewObject' ptr val groupSizeBits\<equiv> (do
        objSizeBits \<leftarrow> return ( objBitsKO val);
        totalBits \<leftarrow> return ( objSizeBits + groupSizeBits);
        unless (fromPPtr ptr && mask totalBits = 0) $
            alignError totalBits;
        ps \<leftarrow> gets ksPSpace;
        end \<leftarrow> return ( fromPPtr ptr + ((1 `~shiftL~` totalBits) - 1));
        (before, _) \<leftarrow> return ( lookupAround2 end (psMap ps));
        (case before of
              None \<Rightarrow>   return ()
            | Some (x, _) \<Rightarrow>   haskell_assert (x < fromPPtr ptr)
                []
            );
        addresses \<leftarrow> return ( map
                (\<lambda> n. fromPPtr ptr + n `~shiftL~` objSizeBits)
                [0  .e.  (1 `~shiftL~` groupSizeBits) - 1]);
        map' \<leftarrow> return ( foldR
               (\<lambda> addr map. data_map_insert addr val map)
               (psMap ps) addresses);
        ps' \<leftarrow> return ( ps \<lparr> psMap := map' \<rparr>);
        modify (\<lambda> ks. ks \<lparr> ksPSpace := ps'\<rparr>)
od)"

defs deleteObjects_def:
"deleteObjects ptr bits\<equiv> (do
        unless (fromPPtr ptr && mask bits = 0) $
            alignError bits;
        stateAssert (deletionIsSafe ptr bits)
            [];
        doMachineOp $ freeMemory (PPtr (fromPPtr ptr)) bits;
        ps \<leftarrow> gets ksPSpace;
        inRange \<leftarrow> return ( (\<lambda> x. x && ((- mask bits) - 1) = fromPPtr ptr));
        map' \<leftarrow> return ( deleteRange (psMap ps) (fromPPtr ptr) bits);
        ps' \<leftarrow> return ( ps \<lparr> psMap := map' \<rparr>);
        modify (\<lambda> ks. ks \<lparr> ksPSpace := ps'\<rparr>);
        modify (\<lambda> ks. ks \<lparr> gsUserPages := (\<lambda> x. if inRange x
                                   then Nothing else gsUserPages ks x) \<rparr>);
        stateAssert (\<lambda> x. Not (cNodePartialOverlap (gsCNodes x) inRange))
            [];
        modify (\<lambda> ks. ks \<lparr> gsCNodes := (\<lambda> x. if inRange x
                                   then Nothing else gsCNodes ks x) \<rparr>);
        stateAssert ksASIDMapSafe []
od)"

defs reserveFrame_def:
"reserveFrame ptr isKernel\<equiv> (do
        val \<leftarrow> return ( if isKernel then KOKernelData else KOUserData);
        placeNewObject' (PPtr (fromPPtr ptr)) val 0;
        return ()
od)"

defs loadWordUser_def:
"loadWordUser p\<equiv> (do
    stateAssert (pointerInUserData p)
        [];
    doMachineOp $ loadWord p
od)"

defs storeWordUser_def:
"storeWordUser p w\<equiv> (do
    stateAssert (pointerInUserData p)
        [];
    doMachineOp $ storeWord p w
od)"


end
