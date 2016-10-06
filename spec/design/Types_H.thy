(* THIS FILE WAS AUTOMATICALLY GENERATED. DO NOT EDIT. *)
(* instead, see the skeleton file Types_H.thy *)
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

chapter "Types visible in the API"

theory Types_H
imports
  "./$L4V_ARCH/State_H"
  "../../lib/Lib"
  "./$L4V_ARCH/ArchTypes_H"
begin

context begin interpretation Arch .
requalify_types
  object_type
  machine_word
  paddr
  vptr

requalify_consts
  getObjectSize
  fromAPIType
  toAPIType
  isFrameType
  pageType
  ptrFromPAddr
end

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

type_synonym region = "(machine_word * machine_word)"

definition
  Region :: "region \<Rightarrow> region"
where Region_def[simp]:
 "Region \<equiv> id"

definition
  fromRegion :: "region \<Rightarrow> region"
where
  fromRegion_def[simp]:
 "fromRegion \<equiv> id"

definition  fromRegion_update :: "(region \<Rightarrow> region) \<Rightarrow> region \<Rightarrow> region"
where
  fromRegion_update_def[simp]:
 "fromRegion_update f y \<equiv> f y"

abbreviation (input)
  Region_trans :: "((machine_word * machine_word)) \<Rightarrow> region" ("Region'_ \<lparr> fromRegion= _ \<rparr>")
where
  "Region_ \<lparr> fromRegion= v0 \<rparr> == Region v0"

type_synonym slot_region = "machine_word * machine_word"

definition
  SlotRegion :: "slot_region \<Rightarrow> slot_region"
where SlotRegion_def[simp]:
 "SlotRegion \<equiv> id"

datatype bidevice_region =
    BIDeviceRegion paddr word32 slot_region

primrec
  bidrFrameCaps :: "bidevice_region \<Rightarrow> slot_region"
where
  "bidrFrameCaps (BIDeviceRegion v0 v1 v2) = v2"

primrec
  bidrFrameSizeBits :: "bidevice_region \<Rightarrow> word32"
where
  "bidrFrameSizeBits (BIDeviceRegion v0 v1 v2) = v1"

primrec
  bidrBasePAddr :: "bidevice_region \<Rightarrow> paddr"
where
  "bidrBasePAddr (BIDeviceRegion v0 v1 v2) = v0"

primrec
  bidrFrameCaps_update :: "(slot_region \<Rightarrow> slot_region) \<Rightarrow> bidevice_region \<Rightarrow> bidevice_region"
where
  "bidrFrameCaps_update f (BIDeviceRegion v0 v1 v2) = BIDeviceRegion v0 v1 (f v2)"

primrec
  bidrFrameSizeBits_update :: "(word32 \<Rightarrow> word32) \<Rightarrow> bidevice_region \<Rightarrow> bidevice_region"
where
  "bidrFrameSizeBits_update f (BIDeviceRegion v0 v1 v2) = BIDeviceRegion v0 (f v1) v2"

primrec
  bidrBasePAddr_update :: "(paddr \<Rightarrow> paddr) \<Rightarrow> bidevice_region \<Rightarrow> bidevice_region"
where
  "bidrBasePAddr_update f (BIDeviceRegion v0 v1 v2) = BIDeviceRegion (f v0) v1 v2"

abbreviation (input)
  BIDeviceRegion_trans :: "(paddr) \<Rightarrow> (word32) \<Rightarrow> (slot_region) \<Rightarrow> bidevice_region" ("BIDeviceRegion'_ \<lparr> bidrBasePAddr= _, bidrFrameSizeBits= _, bidrFrameCaps= _ \<rparr>")
where
  "BIDeviceRegion_ \<lparr> bidrBasePAddr= v0, bidrFrameSizeBits= v1, bidrFrameCaps= v2 \<rparr> == BIDeviceRegion v0 v1 v2"

lemma bidrFrameCaps_bidrFrameCaps_update [simp]:
  "bidrFrameCaps (bidrFrameCaps_update f v) = f (bidrFrameCaps v)"
  by (cases v) simp

lemma bidrFrameCaps_bidrFrameSizeBits_update [simp]:
  "bidrFrameCaps (bidrFrameSizeBits_update f v) = bidrFrameCaps v"
  by (cases v) simp

lemma bidrFrameCaps_bidrBasePAddr_update [simp]:
  "bidrFrameCaps (bidrBasePAddr_update f v) = bidrFrameCaps v"
  by (cases v) simp

lemma bidrFrameSizeBits_bidrFrameCaps_update [simp]:
  "bidrFrameSizeBits (bidrFrameCaps_update f v) = bidrFrameSizeBits v"
  by (cases v) simp

lemma bidrFrameSizeBits_bidrFrameSizeBits_update [simp]:
  "bidrFrameSizeBits (bidrFrameSizeBits_update f v) = f (bidrFrameSizeBits v)"
  by (cases v) simp

lemma bidrFrameSizeBits_bidrBasePAddr_update [simp]:
  "bidrFrameSizeBits (bidrBasePAddr_update f v) = bidrFrameSizeBits v"
  by (cases v) simp

lemma bidrBasePAddr_bidrFrameCaps_update [simp]:
  "bidrBasePAddr (bidrFrameCaps_update f v) = bidrBasePAddr v"
  by (cases v) simp

lemma bidrBasePAddr_bidrFrameSizeBits_update [simp]:
  "bidrBasePAddr (bidrFrameSizeBits_update f v) = bidrBasePAddr v"
  by (cases v) simp

lemma bidrBasePAddr_bidrBasePAddr_update [simp]:
  "bidrBasePAddr (bidrBasePAddr_update f v) = f (bidrBasePAddr v)"
  by (cases v) simp

datatype biframe_data =
    BIFrameData word32 word32 word32 vptr "machine_word list" "machine_word list" "machine_word list" "machine_word list" "machine_word list" "machine_word list" "paddr list" "word8 list" "bool list" word8 word32 "bidevice_region list"

primrec
  bifNumIOPTLevels :: "biframe_data \<Rightarrow> word32"
where
  "bifNumIOPTLevels (BIFrameData v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15) = v2"

primrec
  bifNullCaps :: "biframe_data \<Rightarrow> machine_word list"
where
  "bifNullCaps (BIFrameData v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15) = v4"

primrec
  bifIPCBufVPtr :: "biframe_data \<Rightarrow> vptr"
where
  "bifIPCBufVPtr (BIFrameData v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15) = v3"

primrec
  bifUIPTCaps :: "biframe_data \<Rightarrow> machine_word list"
where
  "bifUIPTCaps (BIFrameData v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15) = v8"

primrec
  bifUIFrameCaps :: "biframe_data \<Rightarrow> machine_word list"
where
  "bifUIFrameCaps (BIFrameData v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15) = v6"

primrec
  bifUntypedObjSizeBits :: "biframe_data \<Rightarrow> word8 list"
where
  "bifUntypedObjSizeBits (BIFrameData v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15) = v11"

primrec
  bifNodeID :: "biframe_data \<Rightarrow> word32"
where
  "bifNodeID (BIFrameData v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15) = v0"

primrec
  bifNumDeviceRegions :: "biframe_data \<Rightarrow> word32"
where
  "bifNumDeviceRegions (BIFrameData v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15) = v14"

primrec
  bifSharedFrameCaps :: "biframe_data \<Rightarrow> machine_word list"
where
  "bifSharedFrameCaps (BIFrameData v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15) = v5"

primrec
  bifDeviceRegions :: "biframe_data \<Rightarrow> bidevice_region list"
where
  "bifDeviceRegions (BIFrameData v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15) = v15"

primrec
  bifUntypedObjPAddrs :: "biframe_data \<Rightarrow> paddr list"
where
  "bifUntypedObjPAddrs (BIFrameData v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15) = v10"

primrec
  bifNumNodes :: "biframe_data \<Rightarrow> word32"
where
  "bifNumNodes (BIFrameData v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15) = v1"

primrec
  bifUIPDCaps :: "biframe_data \<Rightarrow> machine_word list"
where
  "bifUIPDCaps (BIFrameData v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15) = v7"

primrec
  bifUntypedObjIsDeviceList :: "biframe_data \<Rightarrow> bool list"
where
  "bifUntypedObjIsDeviceList (BIFrameData v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15) = v12"

primrec
  bifUntypedObjCaps :: "biframe_data \<Rightarrow> machine_word list"
where
  "bifUntypedObjCaps (BIFrameData v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15) = v9"

primrec
  bifITCNodeSizeBits :: "biframe_data \<Rightarrow> word8"
where
  "bifITCNodeSizeBits (BIFrameData v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15) = v13"

primrec
  bifNumIOPTLevels_update :: "(word32 \<Rightarrow> word32) \<Rightarrow> biframe_data \<Rightarrow> biframe_data"
where
  "bifNumIOPTLevels_update f (BIFrameData v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15) = BIFrameData v0 v1 (f v2) v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15"

primrec
  bifNullCaps_update :: "((machine_word list) \<Rightarrow> (machine_word list)) \<Rightarrow> biframe_data \<Rightarrow> biframe_data"
where
  "bifNullCaps_update f (BIFrameData v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15) = BIFrameData v0 v1 v2 v3 (f v4) v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15"

primrec
  bifIPCBufVPtr_update :: "(vptr \<Rightarrow> vptr) \<Rightarrow> biframe_data \<Rightarrow> biframe_data"
where
  "bifIPCBufVPtr_update f (BIFrameData v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15) = BIFrameData v0 v1 v2 (f v3) v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15"

primrec
  bifUIPTCaps_update :: "((machine_word list) \<Rightarrow> (machine_word list)) \<Rightarrow> biframe_data \<Rightarrow> biframe_data"
where
  "bifUIPTCaps_update f (BIFrameData v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15) = BIFrameData v0 v1 v2 v3 v4 v5 v6 v7 (f v8) v9 v10 v11 v12 v13 v14 v15"

primrec
  bifUIFrameCaps_update :: "((machine_word list) \<Rightarrow> (machine_word list)) \<Rightarrow> biframe_data \<Rightarrow> biframe_data"
where
  "bifUIFrameCaps_update f (BIFrameData v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15) = BIFrameData v0 v1 v2 v3 v4 v5 (f v6) v7 v8 v9 v10 v11 v12 v13 v14 v15"

primrec
  bifUntypedObjSizeBits_update :: "((word8 list) \<Rightarrow> (word8 list)) \<Rightarrow> biframe_data \<Rightarrow> biframe_data"
where
  "bifUntypedObjSizeBits_update f (BIFrameData v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15) = BIFrameData v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 (f v11) v12 v13 v14 v15"

primrec
  bifNodeID_update :: "(word32 \<Rightarrow> word32) \<Rightarrow> biframe_data \<Rightarrow> biframe_data"
where
  "bifNodeID_update f (BIFrameData v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15) = BIFrameData (f v0) v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15"

primrec
  bifNumDeviceRegions_update :: "(word32 \<Rightarrow> word32) \<Rightarrow> biframe_data \<Rightarrow> biframe_data"
where
  "bifNumDeviceRegions_update f (BIFrameData v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15) = BIFrameData v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 (f v14) v15"

primrec
  bifSharedFrameCaps_update :: "((machine_word list) \<Rightarrow> (machine_word list)) \<Rightarrow> biframe_data \<Rightarrow> biframe_data"
where
  "bifSharedFrameCaps_update f (BIFrameData v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15) = BIFrameData v0 v1 v2 v3 v4 (f v5) v6 v7 v8 v9 v10 v11 v12 v13 v14 v15"

primrec
  bifDeviceRegions_update :: "((bidevice_region list) \<Rightarrow> (bidevice_region list)) \<Rightarrow> biframe_data \<Rightarrow> biframe_data"
where
  "bifDeviceRegions_update f (BIFrameData v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15) = BIFrameData v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 (f v15)"

primrec
  bifUntypedObjPAddrs_update :: "((paddr list) \<Rightarrow> (paddr list)) \<Rightarrow> biframe_data \<Rightarrow> biframe_data"
where
  "bifUntypedObjPAddrs_update f (BIFrameData v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15) = BIFrameData v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 (f v10) v11 v12 v13 v14 v15"

primrec
  bifNumNodes_update :: "(word32 \<Rightarrow> word32) \<Rightarrow> biframe_data \<Rightarrow> biframe_data"
where
  "bifNumNodes_update f (BIFrameData v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15) = BIFrameData v0 (f v1) v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15"

primrec
  bifUIPDCaps_update :: "((machine_word list) \<Rightarrow> (machine_word list)) \<Rightarrow> biframe_data \<Rightarrow> biframe_data"
where
  "bifUIPDCaps_update f (BIFrameData v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15) = BIFrameData v0 v1 v2 v3 v4 v5 v6 (f v7) v8 v9 v10 v11 v12 v13 v14 v15"

primrec
  bifUntypedObjIsDeviceList_update :: "((bool list) \<Rightarrow> (bool list)) \<Rightarrow> biframe_data \<Rightarrow> biframe_data"
where
  "bifUntypedObjIsDeviceList_update f (BIFrameData v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15) = BIFrameData v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 (f v12) v13 v14 v15"

primrec
  bifUntypedObjCaps_update :: "((machine_word list) \<Rightarrow> (machine_word list)) \<Rightarrow> biframe_data \<Rightarrow> biframe_data"
where
  "bifUntypedObjCaps_update f (BIFrameData v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15) = BIFrameData v0 v1 v2 v3 v4 v5 v6 v7 v8 (f v9) v10 v11 v12 v13 v14 v15"

primrec
  bifITCNodeSizeBits_update :: "(word8 \<Rightarrow> word8) \<Rightarrow> biframe_data \<Rightarrow> biframe_data"
where
  "bifITCNodeSizeBits_update f (BIFrameData v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15) = BIFrameData v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 (f v13) v14 v15"

abbreviation (input)
  BIFrameData_trans :: "(word32) \<Rightarrow> (word32) \<Rightarrow> (word32) \<Rightarrow> (vptr) \<Rightarrow> (machine_word list) \<Rightarrow> (machine_word list) \<Rightarrow> (machine_word list) \<Rightarrow> (machine_word list) \<Rightarrow> (machine_word list) \<Rightarrow> (machine_word list) \<Rightarrow> (paddr list) \<Rightarrow> (word8 list) \<Rightarrow> (bool list) \<Rightarrow> (word8) \<Rightarrow> (word32) \<Rightarrow> (bidevice_region list) \<Rightarrow> biframe_data" ("BIFrameData'_ \<lparr> bifNodeID= _, bifNumNodes= _, bifNumIOPTLevels= _, bifIPCBufVPtr= _, bifNullCaps= _, bifSharedFrameCaps= _, bifUIFrameCaps= _, bifUIPDCaps= _, bifUIPTCaps= _, bifUntypedObjCaps= _, bifUntypedObjPAddrs= _, bifUntypedObjSizeBits= _, bifUntypedObjIsDeviceList= _, bifITCNodeSizeBits= _, bifNumDeviceRegions= _, bifDeviceRegions= _ \<rparr>")
where
  "BIFrameData_ \<lparr> bifNodeID= v0, bifNumNodes= v1, bifNumIOPTLevels= v2, bifIPCBufVPtr= v3, bifNullCaps= v4, bifSharedFrameCaps= v5, bifUIFrameCaps= v6, bifUIPDCaps= v7, bifUIPTCaps= v8, bifUntypedObjCaps= v9, bifUntypedObjPAddrs= v10, bifUntypedObjSizeBits= v11, bifUntypedObjIsDeviceList= v12, bifITCNodeSizeBits= v13, bifNumDeviceRegions= v14, bifDeviceRegions= v15 \<rparr> == BIFrameData v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15"

lemma bifNumIOPTLevels_bifNumIOPTLevels_update [simp]:
  "bifNumIOPTLevels (bifNumIOPTLevels_update f v) = f (bifNumIOPTLevels v)"
  by (cases v) simp

lemma bifNumIOPTLevels_bifNullCaps_update [simp]:
  "bifNumIOPTLevels (bifNullCaps_update f v) = bifNumIOPTLevels v"
  by (cases v) simp

lemma bifNumIOPTLevels_bifIPCBufVPtr_update [simp]:
  "bifNumIOPTLevels (bifIPCBufVPtr_update f v) = bifNumIOPTLevels v"
  by (cases v) simp

lemma bifNumIOPTLevels_bifUIPTCaps_update [simp]:
  "bifNumIOPTLevels (bifUIPTCaps_update f v) = bifNumIOPTLevels v"
  by (cases v) simp

lemma bifNumIOPTLevels_bifUIFrameCaps_update [simp]:
  "bifNumIOPTLevels (bifUIFrameCaps_update f v) = bifNumIOPTLevels v"
  by (cases v) simp

lemma bifNumIOPTLevels_bifUntypedObjSizeBits_update [simp]:
  "bifNumIOPTLevels (bifUntypedObjSizeBits_update f v) = bifNumIOPTLevels v"
  by (cases v) simp

lemma bifNumIOPTLevels_bifNodeID_update [simp]:
  "bifNumIOPTLevels (bifNodeID_update f v) = bifNumIOPTLevels v"
  by (cases v) simp

lemma bifNumIOPTLevels_bifNumDeviceRegions_update [simp]:
  "bifNumIOPTLevels (bifNumDeviceRegions_update f v) = bifNumIOPTLevels v"
  by (cases v) simp

lemma bifNumIOPTLevels_bifSharedFrameCaps_update [simp]:
  "bifNumIOPTLevels (bifSharedFrameCaps_update f v) = bifNumIOPTLevels v"
  by (cases v) simp

lemma bifNumIOPTLevels_bifDeviceRegions_update [simp]:
  "bifNumIOPTLevels (bifDeviceRegions_update f v) = bifNumIOPTLevels v"
  by (cases v) simp

lemma bifNumIOPTLevels_bifUntypedObjPAddrs_update [simp]:
  "bifNumIOPTLevels (bifUntypedObjPAddrs_update f v) = bifNumIOPTLevels v"
  by (cases v) simp

lemma bifNumIOPTLevels_bifNumNodes_update [simp]:
  "bifNumIOPTLevels (bifNumNodes_update f v) = bifNumIOPTLevels v"
  by (cases v) simp

lemma bifNumIOPTLevels_bifUIPDCaps_update [simp]:
  "bifNumIOPTLevels (bifUIPDCaps_update f v) = bifNumIOPTLevels v"
  by (cases v) simp

lemma bifNumIOPTLevels_bifUntypedObjIsDeviceList_update [simp]:
  "bifNumIOPTLevels (bifUntypedObjIsDeviceList_update f v) = bifNumIOPTLevels v"
  by (cases v) simp

lemma bifNumIOPTLevels_bifUntypedObjCaps_update [simp]:
  "bifNumIOPTLevels (bifUntypedObjCaps_update f v) = bifNumIOPTLevels v"
  by (cases v) simp

lemma bifNumIOPTLevels_bifITCNodeSizeBits_update [simp]:
  "bifNumIOPTLevels (bifITCNodeSizeBits_update f v) = bifNumIOPTLevels v"
  by (cases v) simp

lemma bifNullCaps_bifNumIOPTLevels_update [simp]:
  "bifNullCaps (bifNumIOPTLevels_update f v) = bifNullCaps v"
  by (cases v) simp

lemma bifNullCaps_bifNullCaps_update [simp]:
  "bifNullCaps (bifNullCaps_update f v) = f (bifNullCaps v)"
  by (cases v) simp

lemma bifNullCaps_bifIPCBufVPtr_update [simp]:
  "bifNullCaps (bifIPCBufVPtr_update f v) = bifNullCaps v"
  by (cases v) simp

lemma bifNullCaps_bifUIPTCaps_update [simp]:
  "bifNullCaps (bifUIPTCaps_update f v) = bifNullCaps v"
  by (cases v) simp

lemma bifNullCaps_bifUIFrameCaps_update [simp]:
  "bifNullCaps (bifUIFrameCaps_update f v) = bifNullCaps v"
  by (cases v) simp

lemma bifNullCaps_bifUntypedObjSizeBits_update [simp]:
  "bifNullCaps (bifUntypedObjSizeBits_update f v) = bifNullCaps v"
  by (cases v) simp

lemma bifNullCaps_bifNodeID_update [simp]:
  "bifNullCaps (bifNodeID_update f v) = bifNullCaps v"
  by (cases v) simp

lemma bifNullCaps_bifNumDeviceRegions_update [simp]:
  "bifNullCaps (bifNumDeviceRegions_update f v) = bifNullCaps v"
  by (cases v) simp

lemma bifNullCaps_bifSharedFrameCaps_update [simp]:
  "bifNullCaps (bifSharedFrameCaps_update f v) = bifNullCaps v"
  by (cases v) simp

lemma bifNullCaps_bifDeviceRegions_update [simp]:
  "bifNullCaps (bifDeviceRegions_update f v) = bifNullCaps v"
  by (cases v) simp

lemma bifNullCaps_bifUntypedObjPAddrs_update [simp]:
  "bifNullCaps (bifUntypedObjPAddrs_update f v) = bifNullCaps v"
  by (cases v) simp

lemma bifNullCaps_bifNumNodes_update [simp]:
  "bifNullCaps (bifNumNodes_update f v) = bifNullCaps v"
  by (cases v) simp

lemma bifNullCaps_bifUIPDCaps_update [simp]:
  "bifNullCaps (bifUIPDCaps_update f v) = bifNullCaps v"
  by (cases v) simp

lemma bifNullCaps_bifUntypedObjIsDeviceList_update [simp]:
  "bifNullCaps (bifUntypedObjIsDeviceList_update f v) = bifNullCaps v"
  by (cases v) simp

lemma bifNullCaps_bifUntypedObjCaps_update [simp]:
  "bifNullCaps (bifUntypedObjCaps_update f v) = bifNullCaps v"
  by (cases v) simp

lemma bifNullCaps_bifITCNodeSizeBits_update [simp]:
  "bifNullCaps (bifITCNodeSizeBits_update f v) = bifNullCaps v"
  by (cases v) simp

lemma bifIPCBufVPtr_bifNumIOPTLevels_update [simp]:
  "bifIPCBufVPtr (bifNumIOPTLevels_update f v) = bifIPCBufVPtr v"
  by (cases v) simp

lemma bifIPCBufVPtr_bifNullCaps_update [simp]:
  "bifIPCBufVPtr (bifNullCaps_update f v) = bifIPCBufVPtr v"
  by (cases v) simp

lemma bifIPCBufVPtr_bifIPCBufVPtr_update [simp]:
  "bifIPCBufVPtr (bifIPCBufVPtr_update f v) = f (bifIPCBufVPtr v)"
  by (cases v) simp

lemma bifIPCBufVPtr_bifUIPTCaps_update [simp]:
  "bifIPCBufVPtr (bifUIPTCaps_update f v) = bifIPCBufVPtr v"
  by (cases v) simp

lemma bifIPCBufVPtr_bifUIFrameCaps_update [simp]:
  "bifIPCBufVPtr (bifUIFrameCaps_update f v) = bifIPCBufVPtr v"
  by (cases v) simp

lemma bifIPCBufVPtr_bifUntypedObjSizeBits_update [simp]:
  "bifIPCBufVPtr (bifUntypedObjSizeBits_update f v) = bifIPCBufVPtr v"
  by (cases v) simp

lemma bifIPCBufVPtr_bifNodeID_update [simp]:
  "bifIPCBufVPtr (bifNodeID_update f v) = bifIPCBufVPtr v"
  by (cases v) simp

lemma bifIPCBufVPtr_bifNumDeviceRegions_update [simp]:
  "bifIPCBufVPtr (bifNumDeviceRegions_update f v) = bifIPCBufVPtr v"
  by (cases v) simp

lemma bifIPCBufVPtr_bifSharedFrameCaps_update [simp]:
  "bifIPCBufVPtr (bifSharedFrameCaps_update f v) = bifIPCBufVPtr v"
  by (cases v) simp

lemma bifIPCBufVPtr_bifDeviceRegions_update [simp]:
  "bifIPCBufVPtr (bifDeviceRegions_update f v) = bifIPCBufVPtr v"
  by (cases v) simp

lemma bifIPCBufVPtr_bifUntypedObjPAddrs_update [simp]:
  "bifIPCBufVPtr (bifUntypedObjPAddrs_update f v) = bifIPCBufVPtr v"
  by (cases v) simp

lemma bifIPCBufVPtr_bifNumNodes_update [simp]:
  "bifIPCBufVPtr (bifNumNodes_update f v) = bifIPCBufVPtr v"
  by (cases v) simp

lemma bifIPCBufVPtr_bifUIPDCaps_update [simp]:
  "bifIPCBufVPtr (bifUIPDCaps_update f v) = bifIPCBufVPtr v"
  by (cases v) simp

lemma bifIPCBufVPtr_bifUntypedObjIsDeviceList_update [simp]:
  "bifIPCBufVPtr (bifUntypedObjIsDeviceList_update f v) = bifIPCBufVPtr v"
  by (cases v) simp

lemma bifIPCBufVPtr_bifUntypedObjCaps_update [simp]:
  "bifIPCBufVPtr (bifUntypedObjCaps_update f v) = bifIPCBufVPtr v"
  by (cases v) simp

lemma bifIPCBufVPtr_bifITCNodeSizeBits_update [simp]:
  "bifIPCBufVPtr (bifITCNodeSizeBits_update f v) = bifIPCBufVPtr v"
  by (cases v) simp

lemma bifUIPTCaps_bifNumIOPTLevels_update [simp]:
  "bifUIPTCaps (bifNumIOPTLevels_update f v) = bifUIPTCaps v"
  by (cases v) simp

lemma bifUIPTCaps_bifNullCaps_update [simp]:
  "bifUIPTCaps (bifNullCaps_update f v) = bifUIPTCaps v"
  by (cases v) simp

lemma bifUIPTCaps_bifIPCBufVPtr_update [simp]:
  "bifUIPTCaps (bifIPCBufVPtr_update f v) = bifUIPTCaps v"
  by (cases v) simp

lemma bifUIPTCaps_bifUIPTCaps_update [simp]:
  "bifUIPTCaps (bifUIPTCaps_update f v) = f (bifUIPTCaps v)"
  by (cases v) simp

lemma bifUIPTCaps_bifUIFrameCaps_update [simp]:
  "bifUIPTCaps (bifUIFrameCaps_update f v) = bifUIPTCaps v"
  by (cases v) simp

lemma bifUIPTCaps_bifUntypedObjSizeBits_update [simp]:
  "bifUIPTCaps (bifUntypedObjSizeBits_update f v) = bifUIPTCaps v"
  by (cases v) simp

lemma bifUIPTCaps_bifNodeID_update [simp]:
  "bifUIPTCaps (bifNodeID_update f v) = bifUIPTCaps v"
  by (cases v) simp

lemma bifUIPTCaps_bifNumDeviceRegions_update [simp]:
  "bifUIPTCaps (bifNumDeviceRegions_update f v) = bifUIPTCaps v"
  by (cases v) simp

lemma bifUIPTCaps_bifSharedFrameCaps_update [simp]:
  "bifUIPTCaps (bifSharedFrameCaps_update f v) = bifUIPTCaps v"
  by (cases v) simp

lemma bifUIPTCaps_bifDeviceRegions_update [simp]:
  "bifUIPTCaps (bifDeviceRegions_update f v) = bifUIPTCaps v"
  by (cases v) simp

lemma bifUIPTCaps_bifUntypedObjPAddrs_update [simp]:
  "bifUIPTCaps (bifUntypedObjPAddrs_update f v) = bifUIPTCaps v"
  by (cases v) simp

lemma bifUIPTCaps_bifNumNodes_update [simp]:
  "bifUIPTCaps (bifNumNodes_update f v) = bifUIPTCaps v"
  by (cases v) simp

lemma bifUIPTCaps_bifUIPDCaps_update [simp]:
  "bifUIPTCaps (bifUIPDCaps_update f v) = bifUIPTCaps v"
  by (cases v) simp

lemma bifUIPTCaps_bifUntypedObjIsDeviceList_update [simp]:
  "bifUIPTCaps (bifUntypedObjIsDeviceList_update f v) = bifUIPTCaps v"
  by (cases v) simp

lemma bifUIPTCaps_bifUntypedObjCaps_update [simp]:
  "bifUIPTCaps (bifUntypedObjCaps_update f v) = bifUIPTCaps v"
  by (cases v) simp

lemma bifUIPTCaps_bifITCNodeSizeBits_update [simp]:
  "bifUIPTCaps (bifITCNodeSizeBits_update f v) = bifUIPTCaps v"
  by (cases v) simp

lemma bifUIFrameCaps_bifNumIOPTLevels_update [simp]:
  "bifUIFrameCaps (bifNumIOPTLevels_update f v) = bifUIFrameCaps v"
  by (cases v) simp

lemma bifUIFrameCaps_bifNullCaps_update [simp]:
  "bifUIFrameCaps (bifNullCaps_update f v) = bifUIFrameCaps v"
  by (cases v) simp

lemma bifUIFrameCaps_bifIPCBufVPtr_update [simp]:
  "bifUIFrameCaps (bifIPCBufVPtr_update f v) = bifUIFrameCaps v"
  by (cases v) simp

lemma bifUIFrameCaps_bifUIPTCaps_update [simp]:
  "bifUIFrameCaps (bifUIPTCaps_update f v) = bifUIFrameCaps v"
  by (cases v) simp

lemma bifUIFrameCaps_bifUIFrameCaps_update [simp]:
  "bifUIFrameCaps (bifUIFrameCaps_update f v) = f (bifUIFrameCaps v)"
  by (cases v) simp

lemma bifUIFrameCaps_bifUntypedObjSizeBits_update [simp]:
  "bifUIFrameCaps (bifUntypedObjSizeBits_update f v) = bifUIFrameCaps v"
  by (cases v) simp

lemma bifUIFrameCaps_bifNodeID_update [simp]:
  "bifUIFrameCaps (bifNodeID_update f v) = bifUIFrameCaps v"
  by (cases v) simp

lemma bifUIFrameCaps_bifNumDeviceRegions_update [simp]:
  "bifUIFrameCaps (bifNumDeviceRegions_update f v) = bifUIFrameCaps v"
  by (cases v) simp

lemma bifUIFrameCaps_bifSharedFrameCaps_update [simp]:
  "bifUIFrameCaps (bifSharedFrameCaps_update f v) = bifUIFrameCaps v"
  by (cases v) simp

lemma bifUIFrameCaps_bifDeviceRegions_update [simp]:
  "bifUIFrameCaps (bifDeviceRegions_update f v) = bifUIFrameCaps v"
  by (cases v) simp

lemma bifUIFrameCaps_bifUntypedObjPAddrs_update [simp]:
  "bifUIFrameCaps (bifUntypedObjPAddrs_update f v) = bifUIFrameCaps v"
  by (cases v) simp

lemma bifUIFrameCaps_bifNumNodes_update [simp]:
  "bifUIFrameCaps (bifNumNodes_update f v) = bifUIFrameCaps v"
  by (cases v) simp

lemma bifUIFrameCaps_bifUIPDCaps_update [simp]:
  "bifUIFrameCaps (bifUIPDCaps_update f v) = bifUIFrameCaps v"
  by (cases v) simp

lemma bifUIFrameCaps_bifUntypedObjIsDeviceList_update [simp]:
  "bifUIFrameCaps (bifUntypedObjIsDeviceList_update f v) = bifUIFrameCaps v"
  by (cases v) simp

lemma bifUIFrameCaps_bifUntypedObjCaps_update [simp]:
  "bifUIFrameCaps (bifUntypedObjCaps_update f v) = bifUIFrameCaps v"
  by (cases v) simp

lemma bifUIFrameCaps_bifITCNodeSizeBits_update [simp]:
  "bifUIFrameCaps (bifITCNodeSizeBits_update f v) = bifUIFrameCaps v"
  by (cases v) simp

lemma bifUntypedObjSizeBits_bifNumIOPTLevels_update [simp]:
  "bifUntypedObjSizeBits (bifNumIOPTLevels_update f v) = bifUntypedObjSizeBits v"
  by (cases v) simp

lemma bifUntypedObjSizeBits_bifNullCaps_update [simp]:
  "bifUntypedObjSizeBits (bifNullCaps_update f v) = bifUntypedObjSizeBits v"
  by (cases v) simp

lemma bifUntypedObjSizeBits_bifIPCBufVPtr_update [simp]:
  "bifUntypedObjSizeBits (bifIPCBufVPtr_update f v) = bifUntypedObjSizeBits v"
  by (cases v) simp

lemma bifUntypedObjSizeBits_bifUIPTCaps_update [simp]:
  "bifUntypedObjSizeBits (bifUIPTCaps_update f v) = bifUntypedObjSizeBits v"
  by (cases v) simp

lemma bifUntypedObjSizeBits_bifUIFrameCaps_update [simp]:
  "bifUntypedObjSizeBits (bifUIFrameCaps_update f v) = bifUntypedObjSizeBits v"
  by (cases v) simp

lemma bifUntypedObjSizeBits_bifUntypedObjSizeBits_update [simp]:
  "bifUntypedObjSizeBits (bifUntypedObjSizeBits_update f v) = f (bifUntypedObjSizeBits v)"
  by (cases v) simp

lemma bifUntypedObjSizeBits_bifNodeID_update [simp]:
  "bifUntypedObjSizeBits (bifNodeID_update f v) = bifUntypedObjSizeBits v"
  by (cases v) simp

lemma bifUntypedObjSizeBits_bifNumDeviceRegions_update [simp]:
  "bifUntypedObjSizeBits (bifNumDeviceRegions_update f v) = bifUntypedObjSizeBits v"
  by (cases v) simp

lemma bifUntypedObjSizeBits_bifSharedFrameCaps_update [simp]:
  "bifUntypedObjSizeBits (bifSharedFrameCaps_update f v) = bifUntypedObjSizeBits v"
  by (cases v) simp

lemma bifUntypedObjSizeBits_bifDeviceRegions_update [simp]:
  "bifUntypedObjSizeBits (bifDeviceRegions_update f v) = bifUntypedObjSizeBits v"
  by (cases v) simp

lemma bifUntypedObjSizeBits_bifUntypedObjPAddrs_update [simp]:
  "bifUntypedObjSizeBits (bifUntypedObjPAddrs_update f v) = bifUntypedObjSizeBits v"
  by (cases v) simp

lemma bifUntypedObjSizeBits_bifNumNodes_update [simp]:
  "bifUntypedObjSizeBits (bifNumNodes_update f v) = bifUntypedObjSizeBits v"
  by (cases v) simp

lemma bifUntypedObjSizeBits_bifUIPDCaps_update [simp]:
  "bifUntypedObjSizeBits (bifUIPDCaps_update f v) = bifUntypedObjSizeBits v"
  by (cases v) simp

lemma bifUntypedObjSizeBits_bifUntypedObjIsDeviceList_update [simp]:
  "bifUntypedObjSizeBits (bifUntypedObjIsDeviceList_update f v) = bifUntypedObjSizeBits v"
  by (cases v) simp

lemma bifUntypedObjSizeBits_bifUntypedObjCaps_update [simp]:
  "bifUntypedObjSizeBits (bifUntypedObjCaps_update f v) = bifUntypedObjSizeBits v"
  by (cases v) simp

lemma bifUntypedObjSizeBits_bifITCNodeSizeBits_update [simp]:
  "bifUntypedObjSizeBits (bifITCNodeSizeBits_update f v) = bifUntypedObjSizeBits v"
  by (cases v) simp

lemma bifNodeID_bifNumIOPTLevels_update [simp]:
  "bifNodeID (bifNumIOPTLevels_update f v) = bifNodeID v"
  by (cases v) simp

lemma bifNodeID_bifNullCaps_update [simp]:
  "bifNodeID (bifNullCaps_update f v) = bifNodeID v"
  by (cases v) simp

lemma bifNodeID_bifIPCBufVPtr_update [simp]:
  "bifNodeID (bifIPCBufVPtr_update f v) = bifNodeID v"
  by (cases v) simp

lemma bifNodeID_bifUIPTCaps_update [simp]:
  "bifNodeID (bifUIPTCaps_update f v) = bifNodeID v"
  by (cases v) simp

lemma bifNodeID_bifUIFrameCaps_update [simp]:
  "bifNodeID (bifUIFrameCaps_update f v) = bifNodeID v"
  by (cases v) simp

lemma bifNodeID_bifUntypedObjSizeBits_update [simp]:
  "bifNodeID (bifUntypedObjSizeBits_update f v) = bifNodeID v"
  by (cases v) simp

lemma bifNodeID_bifNodeID_update [simp]:
  "bifNodeID (bifNodeID_update f v) = f (bifNodeID v)"
  by (cases v) simp

lemma bifNodeID_bifNumDeviceRegions_update [simp]:
  "bifNodeID (bifNumDeviceRegions_update f v) = bifNodeID v"
  by (cases v) simp

lemma bifNodeID_bifSharedFrameCaps_update [simp]:
  "bifNodeID (bifSharedFrameCaps_update f v) = bifNodeID v"
  by (cases v) simp

lemma bifNodeID_bifDeviceRegions_update [simp]:
  "bifNodeID (bifDeviceRegions_update f v) = bifNodeID v"
  by (cases v) simp

lemma bifNodeID_bifUntypedObjPAddrs_update [simp]:
  "bifNodeID (bifUntypedObjPAddrs_update f v) = bifNodeID v"
  by (cases v) simp

lemma bifNodeID_bifNumNodes_update [simp]:
  "bifNodeID (bifNumNodes_update f v) = bifNodeID v"
  by (cases v) simp

lemma bifNodeID_bifUIPDCaps_update [simp]:
  "bifNodeID (bifUIPDCaps_update f v) = bifNodeID v"
  by (cases v) simp

lemma bifNodeID_bifUntypedObjIsDeviceList_update [simp]:
  "bifNodeID (bifUntypedObjIsDeviceList_update f v) = bifNodeID v"
  by (cases v) simp

lemma bifNodeID_bifUntypedObjCaps_update [simp]:
  "bifNodeID (bifUntypedObjCaps_update f v) = bifNodeID v"
  by (cases v) simp

lemma bifNodeID_bifITCNodeSizeBits_update [simp]:
  "bifNodeID (bifITCNodeSizeBits_update f v) = bifNodeID v"
  by (cases v) simp

lemma bifNumDeviceRegions_bifNumIOPTLevels_update [simp]:
  "bifNumDeviceRegions (bifNumIOPTLevels_update f v) = bifNumDeviceRegions v"
  by (cases v) simp

lemma bifNumDeviceRegions_bifNullCaps_update [simp]:
  "bifNumDeviceRegions (bifNullCaps_update f v) = bifNumDeviceRegions v"
  by (cases v) simp

lemma bifNumDeviceRegions_bifIPCBufVPtr_update [simp]:
  "bifNumDeviceRegions (bifIPCBufVPtr_update f v) = bifNumDeviceRegions v"
  by (cases v) simp

lemma bifNumDeviceRegions_bifUIPTCaps_update [simp]:
  "bifNumDeviceRegions (bifUIPTCaps_update f v) = bifNumDeviceRegions v"
  by (cases v) simp

lemma bifNumDeviceRegions_bifUIFrameCaps_update [simp]:
  "bifNumDeviceRegions (bifUIFrameCaps_update f v) = bifNumDeviceRegions v"
  by (cases v) simp

lemma bifNumDeviceRegions_bifUntypedObjSizeBits_update [simp]:
  "bifNumDeviceRegions (bifUntypedObjSizeBits_update f v) = bifNumDeviceRegions v"
  by (cases v) simp

lemma bifNumDeviceRegions_bifNodeID_update [simp]:
  "bifNumDeviceRegions (bifNodeID_update f v) = bifNumDeviceRegions v"
  by (cases v) simp

lemma bifNumDeviceRegions_bifNumDeviceRegions_update [simp]:
  "bifNumDeviceRegions (bifNumDeviceRegions_update f v) = f (bifNumDeviceRegions v)"
  by (cases v) simp

lemma bifNumDeviceRegions_bifSharedFrameCaps_update [simp]:
  "bifNumDeviceRegions (bifSharedFrameCaps_update f v) = bifNumDeviceRegions v"
  by (cases v) simp

lemma bifNumDeviceRegions_bifDeviceRegions_update [simp]:
  "bifNumDeviceRegions (bifDeviceRegions_update f v) = bifNumDeviceRegions v"
  by (cases v) simp

lemma bifNumDeviceRegions_bifUntypedObjPAddrs_update [simp]:
  "bifNumDeviceRegions (bifUntypedObjPAddrs_update f v) = bifNumDeviceRegions v"
  by (cases v) simp

lemma bifNumDeviceRegions_bifNumNodes_update [simp]:
  "bifNumDeviceRegions (bifNumNodes_update f v) = bifNumDeviceRegions v"
  by (cases v) simp

lemma bifNumDeviceRegions_bifUIPDCaps_update [simp]:
  "bifNumDeviceRegions (bifUIPDCaps_update f v) = bifNumDeviceRegions v"
  by (cases v) simp

lemma bifNumDeviceRegions_bifUntypedObjIsDeviceList_update [simp]:
  "bifNumDeviceRegions (bifUntypedObjIsDeviceList_update f v) = bifNumDeviceRegions v"
  by (cases v) simp

lemma bifNumDeviceRegions_bifUntypedObjCaps_update [simp]:
  "bifNumDeviceRegions (bifUntypedObjCaps_update f v) = bifNumDeviceRegions v"
  by (cases v) simp

lemma bifNumDeviceRegions_bifITCNodeSizeBits_update [simp]:
  "bifNumDeviceRegions (bifITCNodeSizeBits_update f v) = bifNumDeviceRegions v"
  by (cases v) simp

lemma bifSharedFrameCaps_bifNumIOPTLevels_update [simp]:
  "bifSharedFrameCaps (bifNumIOPTLevels_update f v) = bifSharedFrameCaps v"
  by (cases v) simp

lemma bifSharedFrameCaps_bifNullCaps_update [simp]:
  "bifSharedFrameCaps (bifNullCaps_update f v) = bifSharedFrameCaps v"
  by (cases v) simp

lemma bifSharedFrameCaps_bifIPCBufVPtr_update [simp]:
  "bifSharedFrameCaps (bifIPCBufVPtr_update f v) = bifSharedFrameCaps v"
  by (cases v) simp

lemma bifSharedFrameCaps_bifUIPTCaps_update [simp]:
  "bifSharedFrameCaps (bifUIPTCaps_update f v) = bifSharedFrameCaps v"
  by (cases v) simp

lemma bifSharedFrameCaps_bifUIFrameCaps_update [simp]:
  "bifSharedFrameCaps (bifUIFrameCaps_update f v) = bifSharedFrameCaps v"
  by (cases v) simp

lemma bifSharedFrameCaps_bifUntypedObjSizeBits_update [simp]:
  "bifSharedFrameCaps (bifUntypedObjSizeBits_update f v) = bifSharedFrameCaps v"
  by (cases v) simp

lemma bifSharedFrameCaps_bifNodeID_update [simp]:
  "bifSharedFrameCaps (bifNodeID_update f v) = bifSharedFrameCaps v"
  by (cases v) simp

lemma bifSharedFrameCaps_bifNumDeviceRegions_update [simp]:
  "bifSharedFrameCaps (bifNumDeviceRegions_update f v) = bifSharedFrameCaps v"
  by (cases v) simp

lemma bifSharedFrameCaps_bifSharedFrameCaps_update [simp]:
  "bifSharedFrameCaps (bifSharedFrameCaps_update f v) = f (bifSharedFrameCaps v)"
  by (cases v) simp

lemma bifSharedFrameCaps_bifDeviceRegions_update [simp]:
  "bifSharedFrameCaps (bifDeviceRegions_update f v) = bifSharedFrameCaps v"
  by (cases v) simp

lemma bifSharedFrameCaps_bifUntypedObjPAddrs_update [simp]:
  "bifSharedFrameCaps (bifUntypedObjPAddrs_update f v) = bifSharedFrameCaps v"
  by (cases v) simp

lemma bifSharedFrameCaps_bifNumNodes_update [simp]:
  "bifSharedFrameCaps (bifNumNodes_update f v) = bifSharedFrameCaps v"
  by (cases v) simp

lemma bifSharedFrameCaps_bifUIPDCaps_update [simp]:
  "bifSharedFrameCaps (bifUIPDCaps_update f v) = bifSharedFrameCaps v"
  by (cases v) simp

lemma bifSharedFrameCaps_bifUntypedObjIsDeviceList_update [simp]:
  "bifSharedFrameCaps (bifUntypedObjIsDeviceList_update f v) = bifSharedFrameCaps v"
  by (cases v) simp

lemma bifSharedFrameCaps_bifUntypedObjCaps_update [simp]:
  "bifSharedFrameCaps (bifUntypedObjCaps_update f v) = bifSharedFrameCaps v"
  by (cases v) simp

lemma bifSharedFrameCaps_bifITCNodeSizeBits_update [simp]:
  "bifSharedFrameCaps (bifITCNodeSizeBits_update f v) = bifSharedFrameCaps v"
  by (cases v) simp

lemma bifDeviceRegions_bifNumIOPTLevels_update [simp]:
  "bifDeviceRegions (bifNumIOPTLevels_update f v) = bifDeviceRegions v"
  by (cases v) simp

lemma bifDeviceRegions_bifNullCaps_update [simp]:
  "bifDeviceRegions (bifNullCaps_update f v) = bifDeviceRegions v"
  by (cases v) simp

lemma bifDeviceRegions_bifIPCBufVPtr_update [simp]:
  "bifDeviceRegions (bifIPCBufVPtr_update f v) = bifDeviceRegions v"
  by (cases v) simp

lemma bifDeviceRegions_bifUIPTCaps_update [simp]:
  "bifDeviceRegions (bifUIPTCaps_update f v) = bifDeviceRegions v"
  by (cases v) simp

lemma bifDeviceRegions_bifUIFrameCaps_update [simp]:
  "bifDeviceRegions (bifUIFrameCaps_update f v) = bifDeviceRegions v"
  by (cases v) simp

lemma bifDeviceRegions_bifUntypedObjSizeBits_update [simp]:
  "bifDeviceRegions (bifUntypedObjSizeBits_update f v) = bifDeviceRegions v"
  by (cases v) simp

lemma bifDeviceRegions_bifNodeID_update [simp]:
  "bifDeviceRegions (bifNodeID_update f v) = bifDeviceRegions v"
  by (cases v) simp

lemma bifDeviceRegions_bifNumDeviceRegions_update [simp]:
  "bifDeviceRegions (bifNumDeviceRegions_update f v) = bifDeviceRegions v"
  by (cases v) simp

lemma bifDeviceRegions_bifSharedFrameCaps_update [simp]:
  "bifDeviceRegions (bifSharedFrameCaps_update f v) = bifDeviceRegions v"
  by (cases v) simp

lemma bifDeviceRegions_bifDeviceRegions_update [simp]:
  "bifDeviceRegions (bifDeviceRegions_update f v) = f (bifDeviceRegions v)"
  by (cases v) simp

lemma bifDeviceRegions_bifUntypedObjPAddrs_update [simp]:
  "bifDeviceRegions (bifUntypedObjPAddrs_update f v) = bifDeviceRegions v"
  by (cases v) simp

lemma bifDeviceRegions_bifNumNodes_update [simp]:
  "bifDeviceRegions (bifNumNodes_update f v) = bifDeviceRegions v"
  by (cases v) simp

lemma bifDeviceRegions_bifUIPDCaps_update [simp]:
  "bifDeviceRegions (bifUIPDCaps_update f v) = bifDeviceRegions v"
  by (cases v) simp

lemma bifDeviceRegions_bifUntypedObjIsDeviceList_update [simp]:
  "bifDeviceRegions (bifUntypedObjIsDeviceList_update f v) = bifDeviceRegions v"
  by (cases v) simp

lemma bifDeviceRegions_bifUntypedObjCaps_update [simp]:
  "bifDeviceRegions (bifUntypedObjCaps_update f v) = bifDeviceRegions v"
  by (cases v) simp

lemma bifDeviceRegions_bifITCNodeSizeBits_update [simp]:
  "bifDeviceRegions (bifITCNodeSizeBits_update f v) = bifDeviceRegions v"
  by (cases v) simp

lemma bifUntypedObjPAddrs_bifNumIOPTLevels_update [simp]:
  "bifUntypedObjPAddrs (bifNumIOPTLevels_update f v) = bifUntypedObjPAddrs v"
  by (cases v) simp

lemma bifUntypedObjPAddrs_bifNullCaps_update [simp]:
  "bifUntypedObjPAddrs (bifNullCaps_update f v) = bifUntypedObjPAddrs v"
  by (cases v) simp

lemma bifUntypedObjPAddrs_bifIPCBufVPtr_update [simp]:
  "bifUntypedObjPAddrs (bifIPCBufVPtr_update f v) = bifUntypedObjPAddrs v"
  by (cases v) simp

lemma bifUntypedObjPAddrs_bifUIPTCaps_update [simp]:
  "bifUntypedObjPAddrs (bifUIPTCaps_update f v) = bifUntypedObjPAddrs v"
  by (cases v) simp

lemma bifUntypedObjPAddrs_bifUIFrameCaps_update [simp]:
  "bifUntypedObjPAddrs (bifUIFrameCaps_update f v) = bifUntypedObjPAddrs v"
  by (cases v) simp

lemma bifUntypedObjPAddrs_bifUntypedObjSizeBits_update [simp]:
  "bifUntypedObjPAddrs (bifUntypedObjSizeBits_update f v) = bifUntypedObjPAddrs v"
  by (cases v) simp

lemma bifUntypedObjPAddrs_bifNodeID_update [simp]:
  "bifUntypedObjPAddrs (bifNodeID_update f v) = bifUntypedObjPAddrs v"
  by (cases v) simp

lemma bifUntypedObjPAddrs_bifNumDeviceRegions_update [simp]:
  "bifUntypedObjPAddrs (bifNumDeviceRegions_update f v) = bifUntypedObjPAddrs v"
  by (cases v) simp

lemma bifUntypedObjPAddrs_bifSharedFrameCaps_update [simp]:
  "bifUntypedObjPAddrs (bifSharedFrameCaps_update f v) = bifUntypedObjPAddrs v"
  by (cases v) simp

lemma bifUntypedObjPAddrs_bifDeviceRegions_update [simp]:
  "bifUntypedObjPAddrs (bifDeviceRegions_update f v) = bifUntypedObjPAddrs v"
  by (cases v) simp

lemma bifUntypedObjPAddrs_bifUntypedObjPAddrs_update [simp]:
  "bifUntypedObjPAddrs (bifUntypedObjPAddrs_update f v) = f (bifUntypedObjPAddrs v)"
  by (cases v) simp

lemma bifUntypedObjPAddrs_bifNumNodes_update [simp]:
  "bifUntypedObjPAddrs (bifNumNodes_update f v) = bifUntypedObjPAddrs v"
  by (cases v) simp

lemma bifUntypedObjPAddrs_bifUIPDCaps_update [simp]:
  "bifUntypedObjPAddrs (bifUIPDCaps_update f v) = bifUntypedObjPAddrs v"
  by (cases v) simp

lemma bifUntypedObjPAddrs_bifUntypedObjIsDeviceList_update [simp]:
  "bifUntypedObjPAddrs (bifUntypedObjIsDeviceList_update f v) = bifUntypedObjPAddrs v"
  by (cases v) simp

lemma bifUntypedObjPAddrs_bifUntypedObjCaps_update [simp]:
  "bifUntypedObjPAddrs (bifUntypedObjCaps_update f v) = bifUntypedObjPAddrs v"
  by (cases v) simp

lemma bifUntypedObjPAddrs_bifITCNodeSizeBits_update [simp]:
  "bifUntypedObjPAddrs (bifITCNodeSizeBits_update f v) = bifUntypedObjPAddrs v"
  by (cases v) simp

lemma bifNumNodes_bifNumIOPTLevels_update [simp]:
  "bifNumNodes (bifNumIOPTLevels_update f v) = bifNumNodes v"
  by (cases v) simp

lemma bifNumNodes_bifNullCaps_update [simp]:
  "bifNumNodes (bifNullCaps_update f v) = bifNumNodes v"
  by (cases v) simp

lemma bifNumNodes_bifIPCBufVPtr_update [simp]:
  "bifNumNodes (bifIPCBufVPtr_update f v) = bifNumNodes v"
  by (cases v) simp

lemma bifNumNodes_bifUIPTCaps_update [simp]:
  "bifNumNodes (bifUIPTCaps_update f v) = bifNumNodes v"
  by (cases v) simp

lemma bifNumNodes_bifUIFrameCaps_update [simp]:
  "bifNumNodes (bifUIFrameCaps_update f v) = bifNumNodes v"
  by (cases v) simp

lemma bifNumNodes_bifUntypedObjSizeBits_update [simp]:
  "bifNumNodes (bifUntypedObjSizeBits_update f v) = bifNumNodes v"
  by (cases v) simp

lemma bifNumNodes_bifNodeID_update [simp]:
  "bifNumNodes (bifNodeID_update f v) = bifNumNodes v"
  by (cases v) simp

lemma bifNumNodes_bifNumDeviceRegions_update [simp]:
  "bifNumNodes (bifNumDeviceRegions_update f v) = bifNumNodes v"
  by (cases v) simp

lemma bifNumNodes_bifSharedFrameCaps_update [simp]:
  "bifNumNodes (bifSharedFrameCaps_update f v) = bifNumNodes v"
  by (cases v) simp

lemma bifNumNodes_bifDeviceRegions_update [simp]:
  "bifNumNodes (bifDeviceRegions_update f v) = bifNumNodes v"
  by (cases v) simp

lemma bifNumNodes_bifUntypedObjPAddrs_update [simp]:
  "bifNumNodes (bifUntypedObjPAddrs_update f v) = bifNumNodes v"
  by (cases v) simp

lemma bifNumNodes_bifNumNodes_update [simp]:
  "bifNumNodes (bifNumNodes_update f v) = f (bifNumNodes v)"
  by (cases v) simp

lemma bifNumNodes_bifUIPDCaps_update [simp]:
  "bifNumNodes (bifUIPDCaps_update f v) = bifNumNodes v"
  by (cases v) simp

lemma bifNumNodes_bifUntypedObjIsDeviceList_update [simp]:
  "bifNumNodes (bifUntypedObjIsDeviceList_update f v) = bifNumNodes v"
  by (cases v) simp

lemma bifNumNodes_bifUntypedObjCaps_update [simp]:
  "bifNumNodes (bifUntypedObjCaps_update f v) = bifNumNodes v"
  by (cases v) simp

lemma bifNumNodes_bifITCNodeSizeBits_update [simp]:
  "bifNumNodes (bifITCNodeSizeBits_update f v) = bifNumNodes v"
  by (cases v) simp

lemma bifUIPDCaps_bifNumIOPTLevels_update [simp]:
  "bifUIPDCaps (bifNumIOPTLevels_update f v) = bifUIPDCaps v"
  by (cases v) simp

lemma bifUIPDCaps_bifNullCaps_update [simp]:
  "bifUIPDCaps (bifNullCaps_update f v) = bifUIPDCaps v"
  by (cases v) simp

lemma bifUIPDCaps_bifIPCBufVPtr_update [simp]:
  "bifUIPDCaps (bifIPCBufVPtr_update f v) = bifUIPDCaps v"
  by (cases v) simp

lemma bifUIPDCaps_bifUIPTCaps_update [simp]:
  "bifUIPDCaps (bifUIPTCaps_update f v) = bifUIPDCaps v"
  by (cases v) simp

lemma bifUIPDCaps_bifUIFrameCaps_update [simp]:
  "bifUIPDCaps (bifUIFrameCaps_update f v) = bifUIPDCaps v"
  by (cases v) simp

lemma bifUIPDCaps_bifUntypedObjSizeBits_update [simp]:
  "bifUIPDCaps (bifUntypedObjSizeBits_update f v) = bifUIPDCaps v"
  by (cases v) simp

lemma bifUIPDCaps_bifNodeID_update [simp]:
  "bifUIPDCaps (bifNodeID_update f v) = bifUIPDCaps v"
  by (cases v) simp

lemma bifUIPDCaps_bifNumDeviceRegions_update [simp]:
  "bifUIPDCaps (bifNumDeviceRegions_update f v) = bifUIPDCaps v"
  by (cases v) simp

lemma bifUIPDCaps_bifSharedFrameCaps_update [simp]:
  "bifUIPDCaps (bifSharedFrameCaps_update f v) = bifUIPDCaps v"
  by (cases v) simp

lemma bifUIPDCaps_bifDeviceRegions_update [simp]:
  "bifUIPDCaps (bifDeviceRegions_update f v) = bifUIPDCaps v"
  by (cases v) simp

lemma bifUIPDCaps_bifUntypedObjPAddrs_update [simp]:
  "bifUIPDCaps (bifUntypedObjPAddrs_update f v) = bifUIPDCaps v"
  by (cases v) simp

lemma bifUIPDCaps_bifNumNodes_update [simp]:
  "bifUIPDCaps (bifNumNodes_update f v) = bifUIPDCaps v"
  by (cases v) simp

lemma bifUIPDCaps_bifUIPDCaps_update [simp]:
  "bifUIPDCaps (bifUIPDCaps_update f v) = f (bifUIPDCaps v)"
  by (cases v) simp

lemma bifUIPDCaps_bifUntypedObjIsDeviceList_update [simp]:
  "bifUIPDCaps (bifUntypedObjIsDeviceList_update f v) = bifUIPDCaps v"
  by (cases v) simp

lemma bifUIPDCaps_bifUntypedObjCaps_update [simp]:
  "bifUIPDCaps (bifUntypedObjCaps_update f v) = bifUIPDCaps v"
  by (cases v) simp

lemma bifUIPDCaps_bifITCNodeSizeBits_update [simp]:
  "bifUIPDCaps (bifITCNodeSizeBits_update f v) = bifUIPDCaps v"
  by (cases v) simp

lemma bifUntypedObjIsDeviceList_bifNumIOPTLevels_update [simp]:
  "bifUntypedObjIsDeviceList (bifNumIOPTLevels_update f v) = bifUntypedObjIsDeviceList v"
  by (cases v) simp

lemma bifUntypedObjIsDeviceList_bifNullCaps_update [simp]:
  "bifUntypedObjIsDeviceList (bifNullCaps_update f v) = bifUntypedObjIsDeviceList v"
  by (cases v) simp

lemma bifUntypedObjIsDeviceList_bifIPCBufVPtr_update [simp]:
  "bifUntypedObjIsDeviceList (bifIPCBufVPtr_update f v) = bifUntypedObjIsDeviceList v"
  by (cases v) simp

lemma bifUntypedObjIsDeviceList_bifUIPTCaps_update [simp]:
  "bifUntypedObjIsDeviceList (bifUIPTCaps_update f v) = bifUntypedObjIsDeviceList v"
  by (cases v) simp

lemma bifUntypedObjIsDeviceList_bifUIFrameCaps_update [simp]:
  "bifUntypedObjIsDeviceList (bifUIFrameCaps_update f v) = bifUntypedObjIsDeviceList v"
  by (cases v) simp

lemma bifUntypedObjIsDeviceList_bifUntypedObjSizeBits_update [simp]:
  "bifUntypedObjIsDeviceList (bifUntypedObjSizeBits_update f v) = bifUntypedObjIsDeviceList v"
  by (cases v) simp

lemma bifUntypedObjIsDeviceList_bifNodeID_update [simp]:
  "bifUntypedObjIsDeviceList (bifNodeID_update f v) = bifUntypedObjIsDeviceList v"
  by (cases v) simp

lemma bifUntypedObjIsDeviceList_bifNumDeviceRegions_update [simp]:
  "bifUntypedObjIsDeviceList (bifNumDeviceRegions_update f v) = bifUntypedObjIsDeviceList v"
  by (cases v) simp

lemma bifUntypedObjIsDeviceList_bifSharedFrameCaps_update [simp]:
  "bifUntypedObjIsDeviceList (bifSharedFrameCaps_update f v) = bifUntypedObjIsDeviceList v"
  by (cases v) simp

lemma bifUntypedObjIsDeviceList_bifDeviceRegions_update [simp]:
  "bifUntypedObjIsDeviceList (bifDeviceRegions_update f v) = bifUntypedObjIsDeviceList v"
  by (cases v) simp

lemma bifUntypedObjIsDeviceList_bifUntypedObjPAddrs_update [simp]:
  "bifUntypedObjIsDeviceList (bifUntypedObjPAddrs_update f v) = bifUntypedObjIsDeviceList v"
  by (cases v) simp

lemma bifUntypedObjIsDeviceList_bifNumNodes_update [simp]:
  "bifUntypedObjIsDeviceList (bifNumNodes_update f v) = bifUntypedObjIsDeviceList v"
  by (cases v) simp

lemma bifUntypedObjIsDeviceList_bifUIPDCaps_update [simp]:
  "bifUntypedObjIsDeviceList (bifUIPDCaps_update f v) = bifUntypedObjIsDeviceList v"
  by (cases v) simp

lemma bifUntypedObjIsDeviceList_bifUntypedObjIsDeviceList_update [simp]:
  "bifUntypedObjIsDeviceList (bifUntypedObjIsDeviceList_update f v) = f (bifUntypedObjIsDeviceList v)"
  by (cases v) simp

lemma bifUntypedObjIsDeviceList_bifUntypedObjCaps_update [simp]:
  "bifUntypedObjIsDeviceList (bifUntypedObjCaps_update f v) = bifUntypedObjIsDeviceList v"
  by (cases v) simp

lemma bifUntypedObjIsDeviceList_bifITCNodeSizeBits_update [simp]:
  "bifUntypedObjIsDeviceList (bifITCNodeSizeBits_update f v) = bifUntypedObjIsDeviceList v"
  by (cases v) simp

lemma bifUntypedObjCaps_bifNumIOPTLevels_update [simp]:
  "bifUntypedObjCaps (bifNumIOPTLevels_update f v) = bifUntypedObjCaps v"
  by (cases v) simp

lemma bifUntypedObjCaps_bifNullCaps_update [simp]:
  "bifUntypedObjCaps (bifNullCaps_update f v) = bifUntypedObjCaps v"
  by (cases v) simp

lemma bifUntypedObjCaps_bifIPCBufVPtr_update [simp]:
  "bifUntypedObjCaps (bifIPCBufVPtr_update f v) = bifUntypedObjCaps v"
  by (cases v) simp

lemma bifUntypedObjCaps_bifUIPTCaps_update [simp]:
  "bifUntypedObjCaps (bifUIPTCaps_update f v) = bifUntypedObjCaps v"
  by (cases v) simp

lemma bifUntypedObjCaps_bifUIFrameCaps_update [simp]:
  "bifUntypedObjCaps (bifUIFrameCaps_update f v) = bifUntypedObjCaps v"
  by (cases v) simp

lemma bifUntypedObjCaps_bifUntypedObjSizeBits_update [simp]:
  "bifUntypedObjCaps (bifUntypedObjSizeBits_update f v) = bifUntypedObjCaps v"
  by (cases v) simp

lemma bifUntypedObjCaps_bifNodeID_update [simp]:
  "bifUntypedObjCaps (bifNodeID_update f v) = bifUntypedObjCaps v"
  by (cases v) simp

lemma bifUntypedObjCaps_bifNumDeviceRegions_update [simp]:
  "bifUntypedObjCaps (bifNumDeviceRegions_update f v) = bifUntypedObjCaps v"
  by (cases v) simp

lemma bifUntypedObjCaps_bifSharedFrameCaps_update [simp]:
  "bifUntypedObjCaps (bifSharedFrameCaps_update f v) = bifUntypedObjCaps v"
  by (cases v) simp

lemma bifUntypedObjCaps_bifDeviceRegions_update [simp]:
  "bifUntypedObjCaps (bifDeviceRegions_update f v) = bifUntypedObjCaps v"
  by (cases v) simp

lemma bifUntypedObjCaps_bifUntypedObjPAddrs_update [simp]:
  "bifUntypedObjCaps (bifUntypedObjPAddrs_update f v) = bifUntypedObjCaps v"
  by (cases v) simp

lemma bifUntypedObjCaps_bifNumNodes_update [simp]:
  "bifUntypedObjCaps (bifNumNodes_update f v) = bifUntypedObjCaps v"
  by (cases v) simp

lemma bifUntypedObjCaps_bifUIPDCaps_update [simp]:
  "bifUntypedObjCaps (bifUIPDCaps_update f v) = bifUntypedObjCaps v"
  by (cases v) simp

lemma bifUntypedObjCaps_bifUntypedObjIsDeviceList_update [simp]:
  "bifUntypedObjCaps (bifUntypedObjIsDeviceList_update f v) = bifUntypedObjCaps v"
  by (cases v) simp

lemma bifUntypedObjCaps_bifUntypedObjCaps_update [simp]:
  "bifUntypedObjCaps (bifUntypedObjCaps_update f v) = f (bifUntypedObjCaps v)"
  by (cases v) simp

lemma bifUntypedObjCaps_bifITCNodeSizeBits_update [simp]:
  "bifUntypedObjCaps (bifITCNodeSizeBits_update f v) = bifUntypedObjCaps v"
  by (cases v) simp

lemma bifITCNodeSizeBits_bifNumIOPTLevels_update [simp]:
  "bifITCNodeSizeBits (bifNumIOPTLevels_update f v) = bifITCNodeSizeBits v"
  by (cases v) simp

lemma bifITCNodeSizeBits_bifNullCaps_update [simp]:
  "bifITCNodeSizeBits (bifNullCaps_update f v) = bifITCNodeSizeBits v"
  by (cases v) simp

lemma bifITCNodeSizeBits_bifIPCBufVPtr_update [simp]:
  "bifITCNodeSizeBits (bifIPCBufVPtr_update f v) = bifITCNodeSizeBits v"
  by (cases v) simp

lemma bifITCNodeSizeBits_bifUIPTCaps_update [simp]:
  "bifITCNodeSizeBits (bifUIPTCaps_update f v) = bifITCNodeSizeBits v"
  by (cases v) simp

lemma bifITCNodeSizeBits_bifUIFrameCaps_update [simp]:
  "bifITCNodeSizeBits (bifUIFrameCaps_update f v) = bifITCNodeSizeBits v"
  by (cases v) simp

lemma bifITCNodeSizeBits_bifUntypedObjSizeBits_update [simp]:
  "bifITCNodeSizeBits (bifUntypedObjSizeBits_update f v) = bifITCNodeSizeBits v"
  by (cases v) simp

lemma bifITCNodeSizeBits_bifNodeID_update [simp]:
  "bifITCNodeSizeBits (bifNodeID_update f v) = bifITCNodeSizeBits v"
  by (cases v) simp

lemma bifITCNodeSizeBits_bifNumDeviceRegions_update [simp]:
  "bifITCNodeSizeBits (bifNumDeviceRegions_update f v) = bifITCNodeSizeBits v"
  by (cases v) simp

lemma bifITCNodeSizeBits_bifSharedFrameCaps_update [simp]:
  "bifITCNodeSizeBits (bifSharedFrameCaps_update f v) = bifITCNodeSizeBits v"
  by (cases v) simp

lemma bifITCNodeSizeBits_bifDeviceRegions_update [simp]:
  "bifITCNodeSizeBits (bifDeviceRegions_update f v) = bifITCNodeSizeBits v"
  by (cases v) simp

lemma bifITCNodeSizeBits_bifUntypedObjPAddrs_update [simp]:
  "bifITCNodeSizeBits (bifUntypedObjPAddrs_update f v) = bifITCNodeSizeBits v"
  by (cases v) simp

lemma bifITCNodeSizeBits_bifNumNodes_update [simp]:
  "bifITCNodeSizeBits (bifNumNodes_update f v) = bifITCNodeSizeBits v"
  by (cases v) simp

lemma bifITCNodeSizeBits_bifUIPDCaps_update [simp]:
  "bifITCNodeSizeBits (bifUIPDCaps_update f v) = bifITCNodeSizeBits v"
  by (cases v) simp

lemma bifITCNodeSizeBits_bifUntypedObjIsDeviceList_update [simp]:
  "bifITCNodeSizeBits (bifUntypedObjIsDeviceList_update f v) = bifITCNodeSizeBits v"
  by (cases v) simp

lemma bifITCNodeSizeBits_bifUntypedObjCaps_update [simp]:
  "bifITCNodeSizeBits (bifUntypedObjCaps_update f v) = bifITCNodeSizeBits v"
  by (cases v) simp

lemma bifITCNodeSizeBits_bifITCNodeSizeBits_update [simp]:
  "bifITCNodeSizeBits (bifITCNodeSizeBits_update f v) = f (bifITCNodeSizeBits v)"
  by (cases v) simp

datatype init_data =
    InitData "region list" machine_word machine_word biframe_data vptr paddr

primrec
  initSlotPosMax :: "init_data \<Rightarrow> machine_word"
where
  "initSlotPosMax (InitData v0 v1 v2 v3 v4 v5) = v2"

primrec
  initSlotPosCur :: "init_data \<Rightarrow> machine_word"
where
  "initSlotPosCur (InitData v0 v1 v2 v3 v4 v5) = v1"

primrec
  initFreeMemory :: "init_data \<Rightarrow> region list"
where
  "initFreeMemory (InitData v0 v1 v2 v3 v4 v5) = v0"

primrec
  initVPtrOffset :: "init_data \<Rightarrow> vptr"
where
  "initVPtrOffset (InitData v0 v1 v2 v3 v4 v5) = v4"

primrec
  initBootInfoFrame :: "init_data \<Rightarrow> paddr"
where
  "initBootInfoFrame (InitData v0 v1 v2 v3 v4 v5) = v5"

primrec
  initBootInfo :: "init_data \<Rightarrow> biframe_data"
where
  "initBootInfo (InitData v0 v1 v2 v3 v4 v5) = v3"

primrec
  initSlotPosMax_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> init_data \<Rightarrow> init_data"
where
  "initSlotPosMax_update f (InitData v0 v1 v2 v3 v4 v5) = InitData v0 v1 (f v2) v3 v4 v5"

primrec
  initSlotPosCur_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> init_data \<Rightarrow> init_data"
where
  "initSlotPosCur_update f (InitData v0 v1 v2 v3 v4 v5) = InitData v0 (f v1) v2 v3 v4 v5"

primrec
  initFreeMemory_update :: "((region list) \<Rightarrow> (region list)) \<Rightarrow> init_data \<Rightarrow> init_data"
where
  "initFreeMemory_update f (InitData v0 v1 v2 v3 v4 v5) = InitData (f v0) v1 v2 v3 v4 v5"

primrec
  initVPtrOffset_update :: "(vptr \<Rightarrow> vptr) \<Rightarrow> init_data \<Rightarrow> init_data"
where
  "initVPtrOffset_update f (InitData v0 v1 v2 v3 v4 v5) = InitData v0 v1 v2 v3 (f v4) v5"

primrec
  initBootInfoFrame_update :: "(paddr \<Rightarrow> paddr) \<Rightarrow> init_data \<Rightarrow> init_data"
where
  "initBootInfoFrame_update f (InitData v0 v1 v2 v3 v4 v5) = InitData v0 v1 v2 v3 v4 (f v5)"

primrec
  initBootInfo_update :: "(biframe_data \<Rightarrow> biframe_data) \<Rightarrow> init_data \<Rightarrow> init_data"
where
  "initBootInfo_update f (InitData v0 v1 v2 v3 v4 v5) = InitData v0 v1 v2 (f v3) v4 v5"

abbreviation (input)
  InitData_trans :: "(region list) \<Rightarrow> (machine_word) \<Rightarrow> (machine_word) \<Rightarrow> (biframe_data) \<Rightarrow> (vptr) \<Rightarrow> (paddr) \<Rightarrow> init_data" ("InitData'_ \<lparr> initFreeMemory= _, initSlotPosCur= _, initSlotPosMax= _, initBootInfo= _, initVPtrOffset= _, initBootInfoFrame= _ \<rparr>")
where
  "InitData_ \<lparr> initFreeMemory= v0, initSlotPosCur= v1, initSlotPosMax= v2, initBootInfo= v3, initVPtrOffset= v4, initBootInfoFrame= v5 \<rparr> == InitData v0 v1 v2 v3 v4 v5"

lemma initSlotPosMax_initSlotPosMax_update [simp]:
  "initSlotPosMax (initSlotPosMax_update f v) = f (initSlotPosMax v)"
  by (cases v) simp

lemma initSlotPosMax_initSlotPosCur_update [simp]:
  "initSlotPosMax (initSlotPosCur_update f v) = initSlotPosMax v"
  by (cases v) simp

lemma initSlotPosMax_initFreeMemory_update [simp]:
  "initSlotPosMax (initFreeMemory_update f v) = initSlotPosMax v"
  by (cases v) simp

lemma initSlotPosMax_initVPtrOffset_update [simp]:
  "initSlotPosMax (initVPtrOffset_update f v) = initSlotPosMax v"
  by (cases v) simp

lemma initSlotPosMax_initBootInfoFrame_update [simp]:
  "initSlotPosMax (initBootInfoFrame_update f v) = initSlotPosMax v"
  by (cases v) simp

lemma initSlotPosMax_initBootInfo_update [simp]:
  "initSlotPosMax (initBootInfo_update f v) = initSlotPosMax v"
  by (cases v) simp

lemma initSlotPosCur_initSlotPosMax_update [simp]:
  "initSlotPosCur (initSlotPosMax_update f v) = initSlotPosCur v"
  by (cases v) simp

lemma initSlotPosCur_initSlotPosCur_update [simp]:
  "initSlotPosCur (initSlotPosCur_update f v) = f (initSlotPosCur v)"
  by (cases v) simp

lemma initSlotPosCur_initFreeMemory_update [simp]:
  "initSlotPosCur (initFreeMemory_update f v) = initSlotPosCur v"
  by (cases v) simp

lemma initSlotPosCur_initVPtrOffset_update [simp]:
  "initSlotPosCur (initVPtrOffset_update f v) = initSlotPosCur v"
  by (cases v) simp

lemma initSlotPosCur_initBootInfoFrame_update [simp]:
  "initSlotPosCur (initBootInfoFrame_update f v) = initSlotPosCur v"
  by (cases v) simp

lemma initSlotPosCur_initBootInfo_update [simp]:
  "initSlotPosCur (initBootInfo_update f v) = initSlotPosCur v"
  by (cases v) simp

lemma initFreeMemory_initSlotPosMax_update [simp]:
  "initFreeMemory (initSlotPosMax_update f v) = initFreeMemory v"
  by (cases v) simp

lemma initFreeMemory_initSlotPosCur_update [simp]:
  "initFreeMemory (initSlotPosCur_update f v) = initFreeMemory v"
  by (cases v) simp

lemma initFreeMemory_initFreeMemory_update [simp]:
  "initFreeMemory (initFreeMemory_update f v) = f (initFreeMemory v)"
  by (cases v) simp

lemma initFreeMemory_initVPtrOffset_update [simp]:
  "initFreeMemory (initVPtrOffset_update f v) = initFreeMemory v"
  by (cases v) simp

lemma initFreeMemory_initBootInfoFrame_update [simp]:
  "initFreeMemory (initBootInfoFrame_update f v) = initFreeMemory v"
  by (cases v) simp

lemma initFreeMemory_initBootInfo_update [simp]:
  "initFreeMemory (initBootInfo_update f v) = initFreeMemory v"
  by (cases v) simp

lemma initVPtrOffset_initSlotPosMax_update [simp]:
  "initVPtrOffset (initSlotPosMax_update f v) = initVPtrOffset v"
  by (cases v) simp

lemma initVPtrOffset_initSlotPosCur_update [simp]:
  "initVPtrOffset (initSlotPosCur_update f v) = initVPtrOffset v"
  by (cases v) simp

lemma initVPtrOffset_initFreeMemory_update [simp]:
  "initVPtrOffset (initFreeMemory_update f v) = initVPtrOffset v"
  by (cases v) simp

lemma initVPtrOffset_initVPtrOffset_update [simp]:
  "initVPtrOffset (initVPtrOffset_update f v) = f (initVPtrOffset v)"
  by (cases v) simp

lemma initVPtrOffset_initBootInfoFrame_update [simp]:
  "initVPtrOffset (initBootInfoFrame_update f v) = initVPtrOffset v"
  by (cases v) simp

lemma initVPtrOffset_initBootInfo_update [simp]:
  "initVPtrOffset (initBootInfo_update f v) = initVPtrOffset v"
  by (cases v) simp

lemma initBootInfoFrame_initSlotPosMax_update [simp]:
  "initBootInfoFrame (initSlotPosMax_update f v) = initBootInfoFrame v"
  by (cases v) simp

lemma initBootInfoFrame_initSlotPosCur_update [simp]:
  "initBootInfoFrame (initSlotPosCur_update f v) = initBootInfoFrame v"
  by (cases v) simp

lemma initBootInfoFrame_initFreeMemory_update [simp]:
  "initBootInfoFrame (initFreeMemory_update f v) = initBootInfoFrame v"
  by (cases v) simp

lemma initBootInfoFrame_initVPtrOffset_update [simp]:
  "initBootInfoFrame (initVPtrOffset_update f v) = initBootInfoFrame v"
  by (cases v) simp

lemma initBootInfoFrame_initBootInfoFrame_update [simp]:
  "initBootInfoFrame (initBootInfoFrame_update f v) = f (initBootInfoFrame v)"
  by (cases v) simp

lemma initBootInfoFrame_initBootInfo_update [simp]:
  "initBootInfoFrame (initBootInfo_update f v) = initBootInfoFrame v"
  by (cases v) simp

lemma initBootInfo_initSlotPosMax_update [simp]:
  "initBootInfo (initSlotPosMax_update f v) = initBootInfo v"
  by (cases v) simp

lemma initBootInfo_initSlotPosCur_update [simp]:
  "initBootInfo (initSlotPosCur_update f v) = initBootInfo v"
  by (cases v) simp

lemma initBootInfo_initFreeMemory_update [simp]:
  "initBootInfo (initFreeMemory_update f v) = initBootInfo v"
  by (cases v) simp

lemma initBootInfo_initVPtrOffset_update [simp]:
  "initBootInfo (initVPtrOffset_update f v) = initBootInfo v"
  by (cases v) simp

lemma initBootInfo_initBootInfoFrame_update [simp]:
  "initBootInfo (initBootInfoFrame_update f v) = initBootInfo v"
  by (cases v) simp

lemma initBootInfo_initBootInfo_update [simp]:
  "initBootInfo (initBootInfo_update f v) = f (initBootInfo v)"
  by (cases v) simp

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
priorityBits :: "nat"
where
"priorityBits \<equiv> 8"

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
ptrFromPAddrRegion :: "(paddr * paddr) \<Rightarrow> region"
where
"ptrFromPAddrRegion x0\<equiv> (case x0 of
    (start, end) \<Rightarrow>    Region (ptrFromPAddr start, ptrFromPAddr end)
  )"

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


end
