(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
 * CapDL Types
 *
 * This file introduces many of the high-level types used in this
 * specification.
 *)

theory Types_D
imports
  "ASpec.VMRights_A"
  Intents_D
  "Lib.Lib"
  "Lib.SplitRule"
  "HOL-Combinatorics.Transposition" (* for Fun.swap *)
  "ExecSpec.Arch_Kernel_Config_Lemmas"
begin

arch_requalify_types irq sgi_irq sgi_target
arch_requalify_consts numSGIs gicNumTargets

(* A hardware IRQ number. *)
type_synonym cdl_irq = irq

(*
 * How objects are named within the kernel.
 *
 * Objects are named by 32 bit words.
 * This name may correspond to the memory address of the object.
 *)
type_synonym cdl_object_id = word32

type_synonym cdl_object_set = "(cdl_object_id set)"

(* The badge of an endpoint *)
type_synonym cdl_badge = word32

(* The guard of a CNode cap, and the number of bits the guard uses. *)
type_synonym cdl_cap_guard = word32
type_synonym cdl_cap_guard_size = nat

(* The type we use to represent object sizes. *)
type_synonym cdl_size_bits = nat

(* A single IA32 IO port. *)
type_synonym cdl_io_port = nat

(* The depth of a particular IA32 pagetable. *)
type_synonym cdl_io_pagetable_level = nat

(* An index into a CNode, TCB, or other kernel object that contains caps. *)
type_synonym cdl_cnode_index = nat

(* A reference to a capability slot. *)
type_synonym cdl_cap_ref = "cdl_object_id \<times> cdl_cnode_index"

(* A virtual ASID. *)
type_synonym cdl_asid = "cdl_cnode_index \<times> cdl_cnode_index"

(* mapped address  *)
type_synonym cdl_mapped_addr = "(cdl_asid \<times> word32)"

(* Number of bits of a badge we can use. *)
definition
  badge_bits :: nat
where
  "badge_bits \<equiv> 28"

(* FrameCaps, PageTableCaps and PageDirectoryCaps can either be
 * "real" cap or "fake" cap. Real caps are installed in CNodes,
 * and fake caps represent a page table mapping.
 *)
datatype cdl_frame_cap_type = Real | Fake

(*
 * Kernel capabilities.
 *
 * Such capabilities (or "caps") give the holder particular rights to
 * a kernel object or system hardware.
 *
 * Caps have attributes such as the object they point to, the rights
 * they give the holder, or how the holder is allowed to interact with
 * the target object.
 *)

datatype cdl_cap =
    NullCap

  (* Kernel object capabilities *)
  | UntypedCap bool cdl_object_set cdl_object_set
  | EndpointCap cdl_object_id cdl_badge "cdl_right set"
  | NotificationCap cdl_object_id cdl_badge "cdl_right set"
  | ReplyCap cdl_object_id "cdl_right set" (* The id of the tcb of the target thread *)
  | MasterReplyCap cdl_object_id
  | CNodeCap cdl_object_id cdl_cap_guard cdl_cap_guard_size cdl_size_bits
  | TcbCap cdl_object_id
  | DomainCap

  (*
   * Capabilities representing threads waiting in endpoint queues.
   *)
  (* thread, badge, is call, can grant, can grant reply, is fault ipc *)
  | PendingSyncSendCap cdl_object_id cdl_badge bool bool bool bool
  (* thread, is waiting for reply, can grant *)
  | PendingSyncRecvCap cdl_object_id bool bool
  | PendingNtfnRecvCap cdl_object_id

  (* Indicate that the thread is ready for Reschedule *)
  | RestartCap
  | RunningCap

  (* Interrupt capabilities *)
  | IrqControlCap
  | IrqHandlerCap cdl_irq

  (* Arm specific IRQ/SGI caps *)
  | SGISignalCap sgi_irq sgi_target

  (* Virtual memory capabilties *)
  | FrameCap bool cdl_object_id "cdl_right set" nat cdl_frame_cap_type "cdl_mapped_addr option"
  | PageTableCap cdl_object_id cdl_frame_cap_type "cdl_mapped_addr option"
  | PageDirectoryCap cdl_object_id cdl_frame_cap_type "cdl_asid option"
  | AsidControlCap
  | AsidPoolCap cdl_object_id "cdl_cnode_index"

  (* x86-specific capabilities *)
  | IOPortsCap cdl_object_id "cdl_io_port set"
  | IOSpaceMasterCap
  | IOSpaceCap cdl_object_id
  | IOPageTableCap cdl_object_id

  (* Zombie caps (representing objects mid-deletion) *)
  | ZombieCap cdl_object_id

  (* Bound NTFN caps signifying when a tcb is bound to an NTFN *)
  | BoundNotificationCap cdl_object_id

(* A mapping from capability identifiers to capabilities. *)

type_synonym cdl_cap_map = "cdl_cnode_index \<Rightarrow> cdl_cap option"

(*
 * The cap derivation tree (CDT).
 *
 * This tree records how certain caps are derived from others. This
 * information is important because it affects how caps are revoked; if an
 * entity revokes a particular cap, all of the cap's children (as
 * recorded in the CDT) are also revoked.
 *
 * At this point in time, we leave the definition of the CDT quite
 * abstract. This may be made more concrete in the future allowing us to
 * reason about revocation.
 *)
type_synonym cdl_cdt = "cdl_cap_ref \<Rightarrow> cdl_cap_ref option"

translations
  (type) "cdl_cap_map" <=(type) "nat \<Rightarrow> cdl_cap option"
  (type) "cdl_cap_ref" <=(type) "cdl_object_id \<times> nat"
  (type) "cdl_cap_ref" <=(type) "word32 \<times> nat"
  (type) "cdl_cdt"     <=(type) "cdl_cap_ref \<Rightarrow> cdl_cap_ref option"


(* Kernel objects *)
record cdl_tcb =
  cdl_tcb_caps           :: cdl_cap_map
  cdl_tcb_fault_endpoint :: cdl_cptr
  cdl_tcb_intent         :: cdl_full_intent
  cdl_tcb_has_fault      :: bool
  cdl_tcb_domain         :: word8

record cdl_cnode =
  cdl_cnode_caps :: cdl_cap_map
  cdl_cnode_size_bits :: cdl_size_bits

record cdl_asid_pool =
  cdl_asid_pool_caps :: cdl_cap_map

record cdl_page_table =
  cdl_page_table_caps :: cdl_cap_map

record cdl_page_directory =
  cdl_page_directory_caps :: cdl_cap_map

record cdl_frame =
  cdl_frame_size_bits :: cdl_size_bits

record cdl_irq_node =
  cdl_irq_node_caps :: cdl_cap_map

(*
 * Kernel objects.
 *
 * These are in-memory objects that may, over the course of the system
 * execution, be created or deleted by users.
 *)
datatype cdl_object =
    Endpoint
  | Notification
  | Tcb cdl_tcb
  | CNode cdl_cnode
  | AsidPool cdl_asid_pool
  | PageTable cdl_page_table
  | PageDirectory cdl_page_directory
  | Frame cdl_frame
  | Untyped
  | IRQNode cdl_irq_node

(* The architecture that we are modelling. *)
datatype cdl_arch = IA32 | ARM11

(* The map of objects that are in the system. *)
type_synonym cdl_heap = "cdl_object_id \<Rightarrow> cdl_object option"

translations
  (type) "cdl_heap" <=(type) "32 word \<Rightarrow> cdl_object option"

(*
 * The current state of the system.
 *
 * The state record contains the following primary pieces of information:
 *
 * arch:
 *   The architecture of the system. This affects what capabilities and
 *   kernel objects could possibly be present. In the current kernel
 *   arch will not change at runtime.
 *
 * objects:
 *   The objects that currently exist in the system.
 *
 * cdt:
 *   The cap derivation tree of the system.
 *
 * current_thread:
 *   The currently running thread. Operations will always be performed
 *   on behalf of this thread.
 *
 * irq_node:
 *   Which IRQs are mapped to which notifications.
 *
 * asid_table:
 *   The first level of the asid table, containing capabilities to all
 *   of the ASIDPools.
 *
 * current_domain:
 *   The currently running domain.
 *)
record cdl_state =
  cdl_arch           :: cdl_arch
  cdl_objects        :: cdl_heap
  cdl_cdt            :: cdl_cdt
  cdl_current_thread :: "cdl_object_id option"
  cdl_irq_node       :: "cdl_irq \<Rightarrow> cdl_object_id"
  cdl_asid_table     :: cdl_cap_map
  cdl_current_domain :: word8

(* Return the type of an object. *)
definition
  object_type :: "cdl_object \<Rightarrow> cdl_object_type"
where
  "object_type x \<equiv>
    case x of
        Untyped \<Rightarrow> UntypedType
      | Endpoint \<Rightarrow> EndpointType
      | Notification \<Rightarrow> NotificationType
      | Tcb _ \<Rightarrow> TcbType
      | CNode _ \<Rightarrow> CNodeType
      | IRQNode _ \<Rightarrow> IRQNodeType
      | AsidPool _ \<Rightarrow> AsidPoolType
      | PageTable _ \<Rightarrow> PageTableType
      | PageDirectory _ \<Rightarrow> PageDirectoryType
      | Frame f \<Rightarrow> FrameType (cdl_frame_size_bits f)"

lemmas object_type_simps = object_type_def[split_simps cdl_object.split]

definition
  asid_high_bits :: nat where
  "asid_high_bits \<equiv> 7"
definition
  asid_low_bits :: nat where
  "asid_low_bits \<equiv> 10 :: nat"
definition
  asid_bits :: nat where
  "asid_bits \<equiv> 17 :: nat"

(*
 * Each TCB contains a number of cap slots, each with a specific
 * purpose. These constants define the purpose of each slot.
 *
 * The specific list of slots is chosen to be consistent with the output
 * of the CapDL-tool.
 *)
definition "tcb_cspace_slot     = (0 :: cdl_cnode_index)"
definition "tcb_vspace_slot     = (1 :: cdl_cnode_index)"
definition "tcb_replycap_slot   = (2 :: cdl_cnode_index)"
definition "tcb_caller_slot     = (3 :: cdl_cnode_index)"
definition "tcb_ipcbuffer_slot  = (4 :: cdl_cnode_index)"
definition "tcb_pending_op_slot = (5 :: cdl_cnode_index)"
definition "tcb_boundntfn_slot  = (8 :: cdl_cnode_index)"

definition "tcb_slots_list \<equiv> [0..<tcb_pending_op_slot + 1] @ [tcb_boundntfn_slot]"
abbreviation "tcb_slots \<equiv> set tcb_slots_list"
lemmas tcb_slots_def = tcb_slots_list_def

lemmas tcb_slot_defs =
  tcb_cspace_slot_def
  tcb_vspace_slot_def
  tcb_replycap_slot_def
  tcb_caller_slot_def
  tcb_ipcbuffer_slot_def
  tcb_pending_op_slot_def
  tcb_boundntfn_slot_def
  tcb_slots_list_def

(*
 * Getters and setters for various data types.
 *)

(* Capability getters / setters *)

fun
  cap_objects :: "cdl_cap \<Rightarrow> cdl_object_id set"
where
    "cap_objects (IOPageTableCap x) = {x}"
  | "cap_objects (IOSpaceCap x) = {x}"
  | "cap_objects (IOPortsCap x _) = {x}"
  | "cap_objects (AsidPoolCap x _) = {x}"
  | "cap_objects (PageDirectoryCap x _ _) = {x}"
  | "cap_objects (PageTableCap x _ _) = {x}"
  | "cap_objects (FrameCap _ x _ _ _ _) = {x}"
  | "cap_objects (TcbCap x) = {x}"
  | "cap_objects (CNodeCap x _ _ _) = {x}"
  | "cap_objects (MasterReplyCap x) = {x}"
  | "cap_objects (ReplyCap x _) = {x}"
  | "cap_objects (NotificationCap x _ _) = {x}"
  | "cap_objects (EndpointCap x _ _) = {x}"
  | "cap_objects (UntypedCap _ x a) = x"
  | "cap_objects (ZombieCap x) = {x}"
  | "cap_objects (PendingSyncSendCap x _ _ _ _ _) = {x}"
  | "cap_objects (PendingSyncRecvCap x _ _) = {x}"
  | "cap_objects (PendingNtfnRecvCap x) = {x}"
  | "cap_objects (BoundNotificationCap x) = {x}"
  | "cap_objects _ = {}"

definition
  cap_has_object :: "cdl_cap \<Rightarrow> bool"
where
  "cap_has_object cap \<equiv> case cap of
     NullCap          \<Rightarrow> False
  | IrqControlCap     \<Rightarrow> False
  | IrqHandlerCap _   \<Rightarrow> False
  | SGISignalCap _ _  \<Rightarrow> False
  | AsidControlCap    \<Rightarrow> False
  | IOSpaceMasterCap  \<Rightarrow> False
  | RestartCap        \<Rightarrow> False
  | RunningCap        \<Rightarrow> False
  | DomainCap         \<Rightarrow> False
  | _                 \<Rightarrow> True"

definition
  cap_object :: "cdl_cap \<Rightarrow> cdl_object_id"
where
  "cap_object cap \<equiv>
     if cap_has_object cap
     then (THE c. c \<in> cap_objects cap)
     else undefined"

lemma cap_object_simps[simp]:
  "cap_object (IOPageTableCap x) = x"
  "cap_object (IOSpaceCap x) = x"
  "cap_object (IOPortsCap x a) = x"
  "cap_object (AsidPoolCap x b) = x"
  "cap_object (PageDirectoryCap x c d) = x"
  "cap_object (PageTableCap x e f) = x"
  "cap_object (FrameCap dev x g h i j) = x"
  "cap_object (TcbCap x) = x"
  "cap_object (CNodeCap x k l sz) = x"
  "cap_object (MasterReplyCap x) = x"
  "cap_object (ReplyCap x q) = x"
  "cap_object (NotificationCap x m n) = x"
  "cap_object (EndpointCap x p q) = x"
  "cap_object (ZombieCap x) = x"
  "cap_object (PendingSyncSendCap x s t u v w) = x"
  "cap_object (PendingSyncRecvCap x t u) = x"
  "cap_object (PendingNtfnRecvCap x) = x"
  "cap_object (BoundNotificationCap x) = x"
  by (simp_all add:cap_object_def Nitpick.The_psimp cap_has_object_def)

primrec (nonexhaustive) cap_badge :: "cdl_cap \<Rightarrow> cdl_badge"
where
    "cap_badge (NotificationCap _ x _) = x"
  | "cap_badge (EndpointCap _ x _) = x"

definition
  update_cap_badge :: "cdl_badge \<Rightarrow> cdl_cap \<Rightarrow> cdl_cap"
where
  "update_cap_badge x c \<equiv> case c of
      NotificationCap f1 _ f3 \<Rightarrow> NotificationCap f1 x f3
    | EndpointCap f1 _ f3      \<Rightarrow> EndpointCap f1 x f3
    | _ \<Rightarrow> c"

definition all_cdl_rights :: "cdl_right set" where
  "all_cdl_rights = {Read, Write, Grant, GrantReply}"

definition
  cap_rights :: "cdl_cap \<Rightarrow> cdl_right set"
where
  "cap_rights c \<equiv> case c of
      FrameCap _ _ x _ _ _ \<Rightarrow> x
    | NotificationCap _ _ x \<Rightarrow> x
    | EndpointCap _ _ x \<Rightarrow> x
    | ReplyCap _ x \<Rightarrow> x
    | _ \<Rightarrow> all_cdl_rights"

definition
  update_cap_rights :: "cdl_right set \<Rightarrow> cdl_cap \<Rightarrow> cdl_cap"
where
  "update_cap_rights r c \<equiv> case c of
      FrameCap dev f1 _ f2 f3 f4 \<Rightarrow> FrameCap dev f1 (validate_vm_rights r) f2 f3 f4
    | NotificationCap f1 f2 _ \<Rightarrow> NotificationCap f1 f2 (r - {Grant, GrantReply})
    | EndpointCap f1 f2 _ \<Rightarrow> EndpointCap f1 f2 r
    | ReplyCap f1 _ \<Rightarrow> ReplyCap f1 (r - {Read, GrantReply} \<union> {Write})
    | _ \<Rightarrow> c"

definition
  update_mapping_cap_status :: "cdl_frame_cap_type \<Rightarrow> cdl_cap \<Rightarrow> cdl_cap"
where
 "update_mapping_cap_status r c \<equiv> case c of
      FrameCap dev f1 f2 f3 _ f4 \<Rightarrow> FrameCap dev f1 f2 f3 r f4
    | PageTableCap pt1 _ pt2 \<Rightarrow> PageTableCap pt1 r pt2
    | _ \<Rightarrow> c"

primrec (nonexhaustive) cap_guard :: "cdl_cap \<Rightarrow> cdl_cap_guard"
where
  "cap_guard (CNodeCap _ x _ _) = x"

definition
  update_cap_guard :: "cdl_cap_guard \<Rightarrow> cdl_cap \<Rightarrow> cdl_cap"
where
  "update_cap_guard x c \<equiv> case c of
      CNodeCap f1 _ f3 f4 \<Rightarrow> CNodeCap f1 x f3 f4
    | _ \<Rightarrow> c"

primrec (nonexhaustive) cap_guard_size :: "cdl_cap \<Rightarrow> cdl_cap_guard_size"
where
  "cap_guard_size (CNodeCap _ _ x _ ) = x"

definition
  cnode_cap_size :: "cdl_cap \<Rightarrow> cdl_size_bits"
where
  "cnode_cap_size cap \<equiv> case cap of
      CNodeCap _ _ _ x \<Rightarrow> x
    | _ \<Rightarrow> 0"

definition
  update_cap_guard_size :: "cdl_cap_guard_size \<Rightarrow> cdl_cap \<Rightarrow> cdl_cap"
where
  "update_cap_guard_size x c \<equiv> case c of
      CNodeCap f1 f2 _ f3 \<Rightarrow> CNodeCap f1 f2 x f3
    | _ \<Rightarrow> c"

(* Kernel object getters / setters *)
definition
  object_slots :: "cdl_object \<Rightarrow> cdl_cap_map"
where
  "object_slots obj \<equiv> case obj of
    PageDirectory x \<Rightarrow> cdl_page_directory_caps x
  | PageTable x \<Rightarrow> cdl_page_table_caps x
  | AsidPool x \<Rightarrow> cdl_asid_pool_caps x
  | CNode x \<Rightarrow> cdl_cnode_caps x
  | Tcb x \<Rightarrow> cdl_tcb_caps x
  | IRQNode x \<Rightarrow> cdl_irq_node_caps x
  | _ \<Rightarrow> Map.empty"

definition
  update_slots :: "cdl_cap_map \<Rightarrow> cdl_object \<Rightarrow> cdl_object"
where
  "update_slots new_val obj \<equiv> case obj of
    PageDirectory x \<Rightarrow> PageDirectory (x\<lparr>cdl_page_directory_caps := new_val\<rparr>)
  | PageTable x \<Rightarrow> PageTable (x\<lparr>cdl_page_table_caps := new_val\<rparr>)
  | AsidPool x \<Rightarrow> AsidPool (x\<lparr>cdl_asid_pool_caps := new_val\<rparr>)
  | CNode x \<Rightarrow> CNode (x\<lparr>cdl_cnode_caps := new_val\<rparr>)
  | Tcb x \<Rightarrow> Tcb (x\<lparr>cdl_tcb_caps := new_val\<rparr>)
  | IRQNode x \<Rightarrow> IRQNode (x\<lparr>cdl_irq_node_caps := new_val\<rparr>)
  | _ \<Rightarrow> obj"

definition
  has_slots :: "cdl_object \<Rightarrow> bool"
where
  "has_slots obj \<equiv> case obj of
    PageDirectory _ \<Rightarrow> True
  | PageTable _ \<Rightarrow> True
  | AsidPool _ \<Rightarrow> True
  | CNode _ \<Rightarrow> True
  | Tcb _ \<Rightarrow> True
  | IRQNode _ \<Rightarrow> True
  | _ \<Rightarrow> False"


definition
  cap_free_ids :: "cdl_cap \<Rightarrow> cdl_object_id set"
where
  "cap_free_ids cap \<equiv> (case cap of
     UntypedCap _ _ free_ids \<Rightarrow> free_ids
   | _ \<Rightarrow> {})"

definition
  remove_free_ids :: "cdl_cap \<Rightarrow> cdl_object_id set \<Rightarrow> cdl_cap"
where
  "remove_free_ids cap obj_ids \<equiv> case cap of
     UntypedCap dev c a \<Rightarrow> UntypedCap dev c (a - obj_ids)
   | _ \<Rightarrow> cap"

definition cap_irq :: "cdl_cap \<Rightarrow> cdl_irq"
where
  "cap_irq cap \<equiv> case cap of
      IrqHandlerCap x \<Rightarrow> x
    | _ \<Rightarrow> undefined"

(*************
 * Cap types *
 *************)




definition cap_type :: "cdl_cap \<Rightarrow> cdl_object_type option"
where
  "cap_type x \<equiv> case x of
    UntypedCap _ _ _         \<Rightarrow> Some UntypedType
  | EndpointCap _ _ _      \<Rightarrow> Some EndpointType
  | NotificationCap _ _ _ \<Rightarrow> Some NotificationType
  | TcbCap _               \<Rightarrow> Some TcbType
  | CNodeCap _ _ _ _       \<Rightarrow> Some CNodeType
  | AsidPoolCap _ _        \<Rightarrow> Some AsidPoolType
  | PageTableCap _ _ _     \<Rightarrow> Some PageTableType
  | PageDirectoryCap _ _ _ \<Rightarrow> Some PageDirectoryType
  | FrameCap _ _ _ f _ _     \<Rightarrow> Some (FrameType f)
  | IrqHandlerCap _        \<Rightarrow> Some IRQNodeType
  | _                      \<Rightarrow> None "

abbreviation "is_untyped_cap cap    \<equiv> (cap_type cap = Some UntypedType)"
abbreviation "is_ep_cap cap         \<equiv> (cap_type cap = Some EndpointType)"
abbreviation "is_ntfn_cap cap        \<equiv> (cap_type cap = Some NotificationType)"
abbreviation "is_tcb_cap cap        \<equiv> (cap_type cap = Some TcbType)"
abbreviation "is_cnode_cap cap      \<equiv> (cap_type cap = Some CNodeType)"
abbreviation "is_asidpool_cap cap   \<equiv> (cap_type cap = Some AsidPoolType)"
abbreviation "is_pt_cap cap         \<equiv> (cap_type cap = Some PageTableType)"
abbreviation "is_pd_cap cap         \<equiv> (cap_type cap = Some PageDirectoryType)"
abbreviation "is_frame_cap cap      \<equiv> (\<exists>sz. cap_type cap = Some (FrameType sz))"
abbreviation "is_irqhandler_cap cap \<equiv> (cap_type cap = Some IRQNodeType)"
definition   "is_irqcontrol_cap cap \<equiv> (cap = IrqControlCap)"

lemma cap_type_simps [simp]:
  "is_untyped_cap    (UntypedCap dev a a')"
  "is_ep_cap         (EndpointCap b c d)"
  "is_ntfn_cap        (NotificationCap e f g)"
  "is_tcb_cap        (TcbCap h)"
  "is_cnode_cap      (CNodeCap j k l m)"
  "is_asidpool_cap   (AsidPoolCap n p)"
  "is_pd_cap         (PageDirectoryCap r s t)"
  "is_pt_cap         (PageTableCap u v w)"
  "is_frame_cap      (FrameCap dev a1 a2 a3 a4 a5)"
  "is_irqhandler_cap (IrqHandlerCap a6)"
  "cap_type (FrameCap dev obj_id rights sz rs asid) = Some (FrameType sz)"
  by (clarsimp simp: cap_type_def)+

abbreviation "cap_has_type cap \<equiv> (\<exists>type. cap_type cap = Some type)"

lemma cap_type_update_cap_badge [simp]:
  "cap_type (update_cap_badge x cap) = cap_type cap"
  by (clarsimp simp: update_cap_badge_def cap_type_def split: cdl_cap.splits)

lemma cap_type_update_cap_rights [simp]:
  "cap_type (update_cap_rights x cap) = cap_type cap"
  by (clarsimp simp: update_cap_rights_def cap_type_def split: cdl_cap.splits)

lemma cap_type_update_mapping_cap_status [simp]:
  "cap_type (update_mapping_cap_status x cap) = cap_type cap"
  by (clarsimp simp: update_mapping_cap_status_def cap_type_def split: cdl_cap.splits)

lemma cap_type_update_cap_guard [simp]:
  "cap_type (update_cap_guard x cap) = cap_type cap"
  by (clarsimp simp: update_cap_guard_def cap_type_def split: cdl_cap.splits)

lemma update_cap_guard_size [simp]:
  "cap_type (update_cap_guard_size x cap) = cap_type cap"
  by (clarsimp simp: update_cap_guard_size_def cap_type_def split: cdl_cap.splits)



definition is_pending_cap :: "cdl_cap \<Rightarrow> bool"
where "is_pending_cap c \<equiv> case c of
  PendingSyncRecvCap _ _ _ \<Rightarrow> True
  | PendingNtfnRecvCap _ \<Rightarrow> True
  | PendingSyncSendCap _ _ _ _ _ _ \<Rightarrow> True
  | _ \<Rightarrow> False"


(*
 * Object constructors.
 *)

(* Create a capability map that contains no caps. *)
definition
  empty_cap_map :: "nat \<Rightarrow> cdl_cap_map"
where
  "empty_cap_map sz \<equiv> (\<lambda>a. if a < 2^sz then (Some NullCap) else None)"

(* Create an empty CNode. *)
definition
  empty_cnode :: "nat \<Rightarrow> cdl_cnode"
where
  "empty_cnode sz = \<lparr> cdl_cnode_caps = empty_cap_map sz, cdl_cnode_size_bits = sz \<rparr>"

definition
  empty_irq_node :: cdl_irq_node
where
  "empty_irq_node \<equiv> \<lparr> cdl_irq_node_caps = empty_cap_map 0 \<rparr>"

(* Standard empty TCB object. *)
definition
  default_tcb :: "word8 \<Rightarrow> cdl_tcb"
where
  "default_tcb current_domain = \<lparr>
    cdl_tcb_caps = \<lambda>n. if n \<in> tcb_slots then Some NullCap else None,
    cdl_tcb_fault_endpoint = 0,
    cdl_tcb_intent = \<lparr>
      cdl_intent_op = None,
      cdl_intent_error = False,
      cdl_intent_cap = 0,
      cdl_intent_extras = [],
      cdl_intent_recv_slot = None
      \<rparr>,
    cdl_tcb_has_fault = False,
    cdl_tcb_domain = current_domain
    \<rparr>"

(* Return a newly constructed object of the given type. *)
definition
  default_object :: "cdl_object_type \<Rightarrow> nat \<Rightarrow> word8 \<Rightarrow> cdl_object option"
where
  "default_object x y current_domain \<equiv>
    case x of
        UntypedType \<Rightarrow> Some Untyped
      | EndpointType \<Rightarrow> Some Endpoint
      | NotificationType \<Rightarrow> Some Notification
      | TcbType \<Rightarrow> Some (Tcb (default_tcb current_domain))
      | CNodeType \<Rightarrow> Some (CNode (empty_cnode y))
      | AsidPoolType \<Rightarrow> Some (AsidPool \<lparr> cdl_asid_pool_caps = empty_cap_map asid_low_bits \<rparr>)
      | PageTableType \<Rightarrow> Some (PageTable \<lparr> cdl_page_table_caps = empty_cap_map 8 \<rparr>)
      | PageDirectoryType \<Rightarrow> Some (PageDirectory \<lparr> cdl_page_directory_caps = empty_cap_map 12 \<rparr>)
      | FrameType sz \<Rightarrow> Some (Frame \<lparr> cdl_frame_size_bits = sz \<rparr>)
      | IRQNodeType \<Rightarrow> Some (IRQNode empty_irq_node)"

abbreviation "pick a \<equiv> SOME x. x\<in> a"

(* Construct a cap for a new object. *)
definition
  default_cap :: "cdl_object_type \<Rightarrow> cdl_object_id set \<Rightarrow> cdl_size_bits \<Rightarrow> bool \<Rightarrow> cdl_cap"
where
  "default_cap t id_set sz dev \<equiv>
    case t of
        EndpointType \<Rightarrow> EndpointCap (pick id_set) 0 UNIV
      | NotificationType \<Rightarrow> NotificationCap (THE i. i \<in> id_set) 0 {Read,Write}
      | TcbType \<Rightarrow> TcbCap (pick id_set)
      | CNodeType \<Rightarrow> CNodeCap (pick id_set) 0 0 sz
      | IRQNodeType \<Rightarrow> IrqHandlerCap undefined
      | UntypedType \<Rightarrow> UntypedCap dev id_set id_set
      | AsidPoolType \<Rightarrow> AsidPoolCap (pick id_set) 0
      | PageTableType \<Rightarrow> PageTableCap (pick id_set) Real None
      | PageDirectoryType \<Rightarrow> PageDirectoryCap (pick id_set) Real None
      | FrameType frame_size \<Rightarrow> FrameCap dev (pick id_set) {Read, Write} frame_size Real None"

end
