(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

(* 
   Types visible in the API. 
*)

header "Types visible in the API"

theory Types_H
imports
  State_H
  "../../lib/Lib"
  ArchTypes_H
begin

type_synonym object_type = "ArchTypes_H.object_type"

datatype cap_rights =
    CapRights bool bool bool

primrec
  capAllowWrite :: "cap_rights \<Rightarrow> bool"
where
  "capAllowWrite (CapRights v0 v1 v2) = v0"

primrec
  capAllowGrant :: "cap_rights \<Rightarrow> bool"
where
  "capAllowGrant (CapRights v0 v1 v2) = v2"

primrec
  capAllowRead :: "cap_rights \<Rightarrow> bool"
where
  "capAllowRead (CapRights v0 v1 v2) = v1"

primrec
  capAllowWrite_update :: "(bool \<Rightarrow> bool) \<Rightarrow> cap_rights \<Rightarrow> cap_rights"
where
  "capAllowWrite_update f (CapRights v0 v1 v2) = CapRights (f v0) v1 v2"

primrec
  capAllowGrant_update :: "(bool \<Rightarrow> bool) \<Rightarrow> cap_rights \<Rightarrow> cap_rights"
where
  "capAllowGrant_update f (CapRights v0 v1 v2) = CapRights v0 v1 (f v2)"

primrec
  capAllowRead_update :: "(bool \<Rightarrow> bool) \<Rightarrow> cap_rights \<Rightarrow> cap_rights"
where
  "capAllowRead_update f (CapRights v0 v1 v2) = CapRights v0 (f v1) v2"

abbreviation (input)
  CapRights_trans :: "(bool) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> cap_rights" ("CapRights'_ \<lparr> capAllowWrite= _, capAllowRead= _, capAllowGrant= _ \<rparr>")
where
  "CapRights_ \<lparr> capAllowWrite= v0, capAllowRead= v1, capAllowGrant= v2 \<rparr> == CapRights v0 v1 v2"

lemma capAllowWrite_capAllowWrite_update [simp]:
  "capAllowWrite (capAllowWrite_update f v) = f (capAllowWrite v)"
  by (cases v) simp

lemma capAllowWrite_capAllowGrant_update [simp]:
  "capAllowWrite (capAllowGrant_update f v) = capAllowWrite v"
  by (cases v) simp

lemma capAllowWrite_capAllowRead_update [simp]:
  "capAllowWrite (capAllowRead_update f v) = capAllowWrite v"
  by (cases v) simp

lemma capAllowGrant_capAllowWrite_update [simp]:
  "capAllowGrant (capAllowWrite_update f v) = capAllowGrant v"
  by (cases v) simp

lemma capAllowGrant_capAllowGrant_update [simp]:
  "capAllowGrant (capAllowGrant_update f v) = f (capAllowGrant v)"
  by (cases v) simp

lemma capAllowGrant_capAllowRead_update [simp]:
  "capAllowGrant (capAllowRead_update f v) = capAllowGrant v"
  by (cases v) simp

lemma capAllowRead_capAllowWrite_update [simp]:
  "capAllowRead (capAllowWrite_update f v) = capAllowRead v"
  by (cases v) simp

lemma capAllowRead_capAllowGrant_update [simp]:
  "capAllowRead (capAllowGrant_update f v) = capAllowRead v"
  by (cases v) simp

lemma capAllowRead_capAllowRead_update [simp]:
  "capAllowRead (capAllowRead_update f v) = f (capAllowRead v)"
  by (cases v) simp

type_synonym domain = "word8"

type_synonym priority = "word8"

type_synonym cptr = "machine_word"

definition
  CPtr :: "cptr \<Rightarrow> cptr"
where CPtr_def[simp]:
 "CPtr \<equiv> id"

definition
  fromCPtr :: "cptr \<Rightarrow> cptr"
where
  fromCPtr_def[simp]:
 "fromCPtr \<equiv> id"

definition  fromCPtr_update :: "(cptr \<Rightarrow> cptr) \<Rightarrow> cptr \<Rightarrow> cptr"
where
  fromCPtr_update_def[simp]:
 "fromCPtr_update f y \<equiv> f y"

abbreviation (input)
  CPtr_trans :: "(machine_word) \<Rightarrow> cptr" ("CPtr'_ \<lparr> fromCPtr= _ \<rparr>")
where
  "CPtr_ \<lparr> fromCPtr= v0 \<rparr> == CPtr v0"

datatype message_info =
    MI machine_word machine_word machine_word machine_word

primrec
  msgCapsUnwrapped :: "message_info \<Rightarrow> machine_word"
where
  "msgCapsUnwrapped (MI v0 v1 v2 v3) = v2"

primrec
  msgLength :: "message_info \<Rightarrow> machine_word"
where
  "msgLength (MI v0 v1 v2 v3) = v0"

primrec
  msgLabel :: "message_info \<Rightarrow> machine_word"
where
  "msgLabel (MI v0 v1 v2 v3) = v3"

primrec
  msgExtraCaps :: "message_info \<Rightarrow> machine_word"
where
  "msgExtraCaps (MI v0 v1 v2 v3) = v1"

primrec
  msgCapsUnwrapped_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> message_info \<Rightarrow> message_info"
where
  "msgCapsUnwrapped_update f (MI v0 v1 v2 v3) = MI v0 v1 (f v2) v3"

primrec
  msgLength_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> message_info \<Rightarrow> message_info"
where
  "msgLength_update f (MI v0 v1 v2 v3) = MI (f v0) v1 v2 v3"

primrec
  msgLabel_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> message_info \<Rightarrow> message_info"
where
  "msgLabel_update f (MI v0 v1 v2 v3) = MI v0 v1 v2 (f v3)"

primrec
  msgExtraCaps_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> message_info \<Rightarrow> message_info"
where
  "msgExtraCaps_update f (MI v0 v1 v2 v3) = MI v0 (f v1) v2 v3"

abbreviation (input)
  MI_trans :: "(machine_word) \<Rightarrow> (machine_word) \<Rightarrow> (machine_word) \<Rightarrow> (machine_word) \<Rightarrow> message_info" ("MI'_ \<lparr> msgLength= _, msgExtraCaps= _, msgCapsUnwrapped= _, msgLabel= _ \<rparr>")
where
  "MI_ \<lparr> msgLength= v0, msgExtraCaps= v1, msgCapsUnwrapped= v2, msgLabel= v3 \<rparr> == MI v0 v1 v2 v3"

lemma msgCapsUnwrapped_msgCapsUnwrapped_update [simp]:
  "msgCapsUnwrapped (msgCapsUnwrapped_update f v) = f (msgCapsUnwrapped v)"
  by (cases v) simp

lemma msgCapsUnwrapped_msgLength_update [simp]:
  "msgCapsUnwrapped (msgLength_update f v) = msgCapsUnwrapped v"
  by (cases v) simp

lemma msgCapsUnwrapped_msgLabel_update [simp]:
  "msgCapsUnwrapped (msgLabel_update f v) = msgCapsUnwrapped v"
  by (cases v) simp

lemma msgCapsUnwrapped_msgExtraCaps_update [simp]:
  "msgCapsUnwrapped (msgExtraCaps_update f v) = msgCapsUnwrapped v"
  by (cases v) simp

lemma msgLength_msgCapsUnwrapped_update [simp]:
  "msgLength (msgCapsUnwrapped_update f v) = msgLength v"
  by (cases v) simp

lemma msgLength_msgLength_update [simp]:
  "msgLength (msgLength_update f v) = f (msgLength v)"
  by (cases v) simp

lemma msgLength_msgLabel_update [simp]:
  "msgLength (msgLabel_update f v) = msgLength v"
  by (cases v) simp

lemma msgLength_msgExtraCaps_update [simp]:
  "msgLength (msgExtraCaps_update f v) = msgLength v"
  by (cases v) simp

lemma msgLabel_msgCapsUnwrapped_update [simp]:
  "msgLabel (msgCapsUnwrapped_update f v) = msgLabel v"
  by (cases v) simp

lemma msgLabel_msgLength_update [simp]:
  "msgLabel (msgLength_update f v) = msgLabel v"
  by (cases v) simp

lemma msgLabel_msgLabel_update [simp]:
  "msgLabel (msgLabel_update f v) = f (msgLabel v)"
  by (cases v) simp

lemma msgLabel_msgExtraCaps_update [simp]:
  "msgLabel (msgExtraCaps_update f v) = msgLabel v"
  by (cases v) simp

lemma msgExtraCaps_msgCapsUnwrapped_update [simp]:
  "msgExtraCaps (msgCapsUnwrapped_update f v) = msgExtraCaps v"
  by (cases v) simp

lemma msgExtraCaps_msgLength_update [simp]:
  "msgExtraCaps (msgLength_update f v) = msgExtraCaps v"
  by (cases v) simp

lemma msgExtraCaps_msgLabel_update [simp]:
  "msgExtraCaps (msgLabel_update f v) = msgExtraCaps v"
  by (cases v) simp

lemma msgExtraCaps_msgExtraCaps_update [simp]:
  "msgExtraCaps (msgExtraCaps_update f v) = f (msgExtraCaps v)"
  by (cases v) simp

datatype cap_transfer =
    CT cptr cptr nat

primrec
  ctReceiveRoot :: "cap_transfer \<Rightarrow> cptr"
where
  "ctReceiveRoot (CT v0 v1 v2) = v0"

primrec
  ctReceiveDepth :: "cap_transfer \<Rightarrow> nat"
where
  "ctReceiveDepth (CT v0 v1 v2) = v2"

primrec
  ctReceiveIndex :: "cap_transfer \<Rightarrow> cptr"
where
  "ctReceiveIndex (CT v0 v1 v2) = v1"

primrec
  ctReceiveRoot_update :: "(cptr \<Rightarrow> cptr) \<Rightarrow> cap_transfer \<Rightarrow> cap_transfer"
where
  "ctReceiveRoot_update f (CT v0 v1 v2) = CT (f v0) v1 v2"

primrec
  ctReceiveDepth_update :: "(nat \<Rightarrow> nat) \<Rightarrow> cap_transfer \<Rightarrow> cap_transfer"
where
  "ctReceiveDepth_update f (CT v0 v1 v2) = CT v0 v1 (f v2)"

primrec
  ctReceiveIndex_update :: "(cptr \<Rightarrow> cptr) \<Rightarrow> cap_transfer \<Rightarrow> cap_transfer"
where
  "ctReceiveIndex_update f (CT v0 v1 v2) = CT v0 (f v1) v2"

abbreviation (input)
  CT_trans :: "(cptr) \<Rightarrow> (cptr) \<Rightarrow> (nat) \<Rightarrow> cap_transfer" ("CT'_ \<lparr> ctReceiveRoot= _, ctReceiveIndex= _, ctReceiveDepth= _ \<rparr>")
where
  "CT_ \<lparr> ctReceiveRoot= v0, ctReceiveIndex= v1, ctReceiveDepth= v2 \<rparr> == CT v0 v1 v2"

lemma ctReceiveRoot_ctReceiveRoot_update [simp]:
  "ctReceiveRoot (ctReceiveRoot_update f v) = f (ctReceiveRoot v)"
  by (cases v) simp

lemma ctReceiveRoot_ctReceiveDepth_update [simp]:
  "ctReceiveRoot (ctReceiveDepth_update f v) = ctReceiveRoot v"
  by (cases v) simp

lemma ctReceiveRoot_ctReceiveIndex_update [simp]:
  "ctReceiveRoot (ctReceiveIndex_update f v) = ctReceiveRoot v"
  by (cases v) simp

lemma ctReceiveDepth_ctReceiveRoot_update [simp]:
  "ctReceiveDepth (ctReceiveRoot_update f v) = ctReceiveDepth v"
  by (cases v) simp

lemma ctReceiveDepth_ctReceiveDepth_update [simp]:
  "ctReceiveDepth (ctReceiveDepth_update f v) = f (ctReceiveDepth v)"
  by (cases v) simp

lemma ctReceiveDepth_ctReceiveIndex_update [simp]:
  "ctReceiveDepth (ctReceiveIndex_update f v) = ctReceiveDepth v"
  by (cases v) simp

lemma ctReceiveIndex_ctReceiveRoot_update [simp]:
  "ctReceiveIndex (ctReceiveRoot_update f v) = ctReceiveIndex v"
  by (cases v) simp

lemma ctReceiveIndex_ctReceiveDepth_update [simp]:
  "ctReceiveIndex (ctReceiveDepth_update f v) = ctReceiveIndex v"
  by (cases v) simp

lemma ctReceiveIndex_ctReceiveIndex_update [simp]:
  "ctReceiveIndex (ctReceiveIndex_update f v) = f (ctReceiveIndex v)"
  by (cases v) simp

datatype boot_region_type =
    BREmpty
  | BRRootTask
  | BRCapsOnly
  | BRNodeL1
  | BRNodeL2
  | BRFreeSlots
  | BRInitCaps
  | BRSmallBlocks
  | BRLargeBlocks
  | BRDeviceCaps
(* boot_region_type instance proofs *)
(*<*)
instantiation boot_region_type :: enum begin
definition
  enum_boot_region_type: "enum_class.enum \<equiv> 
    [ 
      BREmpty,
      BRRootTask,
      BRCapsOnly,
      BRNodeL1,
      BRNodeL2,
      BRFreeSlots,
      BRInitCaps,
      BRSmallBlocks,
      BRLargeBlocks,
      BRDeviceCaps
    ]"

definition
  "enum_class.enum_all (P :: boot_region_type \<Rightarrow> bool) \<longleftrightarrow> Ball UNIV P"

definition
  "enum_class.enum_ex (P :: boot_region_type \<Rightarrow> bool) \<longleftrightarrow> Bex UNIV P"

  instance
  apply intro_classes
   apply (safe, simp)
   apply (case_tac x)
  apply (simp_all add: enum_boot_region_type enum_all_boot_region_type_def enum_ex_boot_region_type_def)
  apply fast
  done
end

instantiation boot_region_type :: enum_alt
begin
definition
  enum_alt_boot_region_type: "enum_alt \<equiv> 
    alt_from_ord (enum :: boot_region_type list)"
instance ..
end

instantiation boot_region_type :: enumeration_both
begin
instance by (intro_classes, simp add: enum_alt_boot_region_type)
end

(*>*)


datatype boot_region =
    BootRegion cptr cptr boot_region_type machine_word

primrec
  brData :: "boot_region \<Rightarrow> machine_word"
where
  "brData (BootRegion v0 v1 v2 v3) = v3"

primrec
  brType :: "boot_region \<Rightarrow> boot_region_type"
where
  "brType (BootRegion v0 v1 v2 v3) = v2"

primrec
  brBase :: "boot_region \<Rightarrow> cptr"
where
  "brBase (BootRegion v0 v1 v2 v3) = v0"

primrec
  brEnd :: "boot_region \<Rightarrow> cptr"
where
  "brEnd (BootRegion v0 v1 v2 v3) = v1"

primrec
  brData_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> boot_region \<Rightarrow> boot_region"
where
  "brData_update f (BootRegion v0 v1 v2 v3) = BootRegion v0 v1 v2 (f v3)"

primrec
  brType_update :: "(boot_region_type \<Rightarrow> boot_region_type) \<Rightarrow> boot_region \<Rightarrow> boot_region"
where
  "brType_update f (BootRegion v0 v1 v2 v3) = BootRegion v0 v1 (f v2) v3"

primrec
  brBase_update :: "(cptr \<Rightarrow> cptr) \<Rightarrow> boot_region \<Rightarrow> boot_region"
where
  "brBase_update f (BootRegion v0 v1 v2 v3) = BootRegion (f v0) v1 v2 v3"

primrec
  brEnd_update :: "(cptr \<Rightarrow> cptr) \<Rightarrow> boot_region \<Rightarrow> boot_region"
where
  "brEnd_update f (BootRegion v0 v1 v2 v3) = BootRegion v0 (f v1) v2 v3"

abbreviation (input)
  BootRegion_trans :: "(cptr) \<Rightarrow> (cptr) \<Rightarrow> (boot_region_type) \<Rightarrow> (machine_word) \<Rightarrow> boot_region" ("BootRegion'_ \<lparr> brBase= _, brEnd= _, brType= _, brData= _ \<rparr>")
where
  "BootRegion_ \<lparr> brBase= v0, brEnd= v1, brType= v2, brData= v3 \<rparr> == BootRegion v0 v1 v2 v3"

lemma brData_brData_update [simp]:
  "brData (brData_update f v) = f (brData v)"
  by (cases v) simp

lemma brData_brType_update [simp]:
  "brData (brType_update f v) = brData v"
  by (cases v) simp

lemma brData_brBase_update [simp]:
  "brData (brBase_update f v) = brData v"
  by (cases v) simp

lemma brData_brEnd_update [simp]:
  "brData (brEnd_update f v) = brData v"
  by (cases v) simp

lemma brType_brData_update [simp]:
  "brType (brData_update f v) = brType v"
  by (cases v) simp

lemma brType_brType_update [simp]:
  "brType (brType_update f v) = f (brType v)"
  by (cases v) simp

lemma brType_brBase_update [simp]:
  "brType (brBase_update f v) = brType v"
  by (cases v) simp

lemma brType_brEnd_update [simp]:
  "brType (brEnd_update f v) = brType v"
  by (cases v) simp

lemma brBase_brData_update [simp]:
  "brBase (brData_update f v) = brBase v"
  by (cases v) simp

lemma brBase_brType_update [simp]:
  "brBase (brType_update f v) = brBase v"
  by (cases v) simp

lemma brBase_brBase_update [simp]:
  "brBase (brBase_update f v) = f (brBase v)"
  by (cases v) simp

lemma brBase_brEnd_update [simp]:
  "brBase (brEnd_update f v) = brBase v"
  by (cases v) simp

lemma brEnd_brData_update [simp]:
  "brEnd (brData_update f v) = brEnd v"
  by (cases v) simp

lemma brEnd_brType_update [simp]:
  "brEnd (brType_update f v) = brEnd v"
  by (cases v) simp

lemma brEnd_brBase_update [simp]:
  "brEnd (brBase_update f v) = brEnd v"
  by (cases v) simp

lemma brEnd_brEnd_update [simp]:
  "brEnd (brEnd_update f v) = f (brEnd v)"
  by (cases v) simp

datatype boot_info =
    BootInfo vptr "boot_region list"

primrec
  biIPCBuffer :: "boot_info \<Rightarrow> vptr"
where
  "biIPCBuffer (BootInfo v0 v1) = v0"

primrec
  biRegions :: "boot_info \<Rightarrow> boot_region list"
where
  "biRegions (BootInfo v0 v1) = v1"

primrec
  biIPCBuffer_update :: "(vptr \<Rightarrow> vptr) \<Rightarrow> boot_info \<Rightarrow> boot_info"
where
  "biIPCBuffer_update f (BootInfo v0 v1) = BootInfo (f v0) v1"

primrec
  biRegions_update :: "((boot_region list) \<Rightarrow> (boot_region list)) \<Rightarrow> boot_info \<Rightarrow> boot_info"
where
  "biRegions_update f (BootInfo v0 v1) = BootInfo v0 (f v1)"

abbreviation (input)
  BootInfo_trans :: "(vptr) \<Rightarrow> (boot_region list) \<Rightarrow> boot_info" ("BootInfo'_ \<lparr> biIPCBuffer= _, biRegions= _ \<rparr>")
where
  "BootInfo_ \<lparr> biIPCBuffer= v0, biRegions= v1 \<rparr> == BootInfo v0 v1"

lemma biIPCBuffer_biIPCBuffer_update [simp]:
  "biIPCBuffer (biIPCBuffer_update f v) = f (biIPCBuffer v)"
  by (cases v) simp

lemma biIPCBuffer_biRegions_update [simp]:
  "biIPCBuffer (biRegions_update f v) = biIPCBuffer v"
  by (cases v) simp

lemma biRegions_biIPCBuffer_update [simp]:
  "biRegions (biIPCBuffer_update f v) = biRegions v"
  by (cases v) simp

lemma biRegions_biRegions_update [simp]:
  "biRegions (biRegions_update f v) = f (biRegions v)"
  by (cases v) simp

definition
getObjectSize :: "object_type \<Rightarrow> nat \<Rightarrow> nat"
where
"getObjectSize \<equiv> ArchTypes_H.getObjectSize"

definition
fromAPIType :: "apiobject_type \<Rightarrow> object_type"
where
"fromAPIType \<equiv> ArchTypes_H.fromAPIType"

definition
toAPIType :: "object_type \<Rightarrow> apiobject_type option"
where
"toAPIType \<equiv> ArchTypes_H.toAPIType"

definition
pageType :: "object_type"
where
"pageType \<equiv> ArchTypes_H.pageType"

definition
allRights :: "cap_rights"
where
"allRights \<equiv> CapRights True True True"

definition
noRights :: "cap_rights"
where
"noRights \<equiv> CapRights False False False"

definition
andCapRights :: "cap_rights \<Rightarrow> cap_rights \<Rightarrow> cap_rights"
where
"andCapRights x0 x1\<equiv> (case (x0, x1) of
    ((CapRights a1 a2 a3), (CapRights b1 b2 b3)) \<Rightarrow>   
        CapRights (a1\<and>b1) (a2\<and>b2) (a3\<and>b3)
  )"

definition
rightsFromWord :: "machine_word \<Rightarrow> cap_rights"
where
"rightsFromWord p \<equiv>
         CapRights (p !! 0) (p !! 1) (p !! 2)"

definition
wordFromRights :: "cap_rights \<Rightarrow> machine_word"
where
"wordFromRights x0\<equiv> (case x0 of
    (CapRights r1 r2 r3) \<Rightarrow>  
        let
         bitIf = (\<lambda>  b n. if b then bit n else 0)
        in
        
        (bitIf r1 0) || (bitIf r2 1) || (bitIf r3 2)
  )"

definition
msgLengthBits :: "nat"
where
"msgLengthBits \<equiv> 7"

definition
msgMaxLength :: "('a :: {minus, one, zero, plus, numeral, HS_bit})"
where
"msgMaxLength \<equiv> 120"

definition
msgExtraCapBits :: "nat"
where
"msgExtraCapBits \<equiv> 2"

definition
msgMaxExtraCaps :: "('a :: {minus, one, zero, plus, numeral, HS_bit})"
where
"msgMaxExtraCaps \<equiv> bit msgExtraCapBits - 1"

definition
msgAlignBits :: "nat"
where
"msgAlignBits \<equiv> 9"

definition
capTransferDataSize :: "machine_word"
where
"capTransferDataSize \<equiv> 3"

definition
wordsFromBootRegion :: "boot_region \<Rightarrow> machine_word list"
where
"wordsFromBootRegion br \<equiv> [
        fromCPtr $ brBase br,
        fromCPtr $ brEnd br,
        fromIntegral $ fromEnum $ brType br,
        brData br ]"

definition
messageInfoFromWord :: "machine_word \<Rightarrow> message_info"
where
"messageInfoFromWord w \<equiv>
        let
         otherBits = msgLengthBits + msgExtraCapBits + msgMaxExtraCaps;
              msgLen    = w && (bit msgLengthBits - 1)
        in
                               MI_ \<lparr>
        msgLength= if msgLen > msgMaxLength then msgMaxLength else msgLen,
        msgExtraCaps= (w `~shiftR~` msgLengthBits) &&
            (bit msgExtraCapBits - 1),
        msgCapsUnwrapped= w `~shiftR~` (msgLengthBits + msgExtraCapBits) &&
            (bit msgMaxExtraCaps - 1),
        msgLabel= w `~shiftR~` otherBits \<rparr>"

definition
wordFromMessageInfo :: "message_info \<Rightarrow> machine_word"
where
"wordFromMessageInfo mi \<equiv>
    let
        len = msgLength mi;
        extra = msgExtraCaps mi `~shiftL~` msgLengthBits;
        un = msgCapsUnwrapped mi `~shiftL~` (msgLengthBits + msgExtraCapBits);
        otherBits = msgLengthBits + msgExtraCapBits + msgMaxExtraCaps;
        label = msgLabel mi `~shiftL~` otherBits
    in
                                label || extra || un || len"

definition
wordsFromBootInfo :: "boot_info \<Rightarrow> machine_word list"
where
"wordsFromBootInfo bi \<equiv> [
        fromVPtr $ biIPCBuffer bi,
        fromIntegral $ length $ biRegions bi ]
        @ (concat $ map wordsFromBootRegion $ biRegions bi)"


end
