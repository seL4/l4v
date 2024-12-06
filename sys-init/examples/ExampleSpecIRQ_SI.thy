(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
 * This file contains an example spec, and shows it obeys the well_formed constraints
 *
 * This file contains the invariants of the user-space initialiser,
 * the well-formed conditions of the input capDL specification,
 * and the predicates describing the initial state.
 *)

theory ExampleSpecIRQ_SI
imports SysInit.WellFormed_SI
begin

context begin interpretation Arch . (*FIXME: arch-split*)

(****************************************************
 * Definitions of all the objects and capabilities. *
 ***************************************************)

definition small_section_size :: nat
where
  "small_section_size = 20"

definition "guard = 0"
definition "guard_size = 1"
definition "cnode_a1_size = 7"
definition "cnode_a2_size = 7"
definition "cnode_b_size = 8"
definition "cnode_extra_size = 2"
lemmas constants [simp] = guard_def guard_size_def cnode_a1_size_def cnode_a2_size_def
                          cnode_b_size_def cnode_extra_size_def


definition "tcb_a_id = 9"
definition "tcb_b_id = 10"
definition "cnode_a1_id = 6"
definition "cnode_a2_id = 7"
definition "cnode_b_id = 5"
definition "cnode_extra_id = 11"
definition "ep_id = 12"
definition "ntfn_id = 13"
definition "pd_a_id = 1"
definition "pt_a_id = 8"
definition "pd_b_id = 2"
definition "frame_a1_id = 3"
definition "frame_a2_id = 4"
definition "frame_b_id = 0"
lemmas ids [simp] = tcb_a_id_def tcb_b_id_def cnode_a1_id_def
                    cnode_a2_id_def cnode_b_id_def cnode_extra_id_def
                    ep_id_def ntfn_id_def pd_a_id_def pt_a_id_def pd_b_id_def
                    frame_a1_id_def frame_a2_id_def frame_b_id_def

definition
  "tcb_a =
  \<lparr>cdl_tcb_caps = [tcb_cspace_slot \<mapsto> CNodeCap cnode_a1_id guard guard_size cnode_a1_size,
                   tcb_vspace_slot \<mapsto> PageDirectoryCap pd_a_id Real None,
                   tcb_replycap_slot \<mapsto> NullCap,
                   tcb_caller_slot \<mapsto> NullCap,
                   tcb_ipcbuffer_slot \<mapsto> FrameCap False frame_a1_id {AllowRead, AllowWrite} small_frame_size Real None,
                   tcb_pending_op_slot \<mapsto> NullCap,
                   tcb_boundntfn_slot \<mapsto> NullCap],
   cdl_tcb_fault_endpoint = 0,
   cdl_tcb_intent = \<lparr>cdl_intent_op = None, cdl_intent_error = False, cdl_intent_cap = 0,
                     cdl_intent_extras = [], cdl_intent_recv_slot = None\<rparr>,
   cdl_tcb_has_fault = False,
   cdl_tcb_domain = minBound\<rparr>"

definition
  "tcb_b =
  \<lparr>cdl_tcb_caps = [tcb_cspace_slot \<mapsto> CNodeCap cnode_b_id guard guard_size cnode_b_size,
                   tcb_vspace_slot \<mapsto> PageDirectoryCap pd_b_id Real None,
                   tcb_replycap_slot \<mapsto> NullCap,
                   tcb_caller_slot \<mapsto> NullCap,
                   tcb_ipcbuffer_slot \<mapsto> FrameCap False frame_b_id {AllowRead, AllowWrite} small_section_size Real None,
                   tcb_pending_op_slot \<mapsto> NullCap,
                   tcb_boundntfn_slot \<mapsto> NullCap],
   cdl_tcb_fault_endpoint = 0,
   cdl_tcb_intent = \<lparr>cdl_intent_op = None, cdl_intent_error = False, cdl_intent_cap = 0,
                     cdl_intent_extras = [], cdl_intent_recv_slot = None\<rparr>,
   cdl_tcb_has_fault = False,
   cdl_tcb_domain = minBound\<rparr>"

definition
  "new_cap_map sz caps \<equiv> empty_cap_map sz ++ caps"

definition
  "new_cnode sz caps \<equiv> \<lparr>cdl_cnode_caps = new_cap_map sz caps,
                        cdl_cnode_size_bits = sz\<rparr>"

definition
  "cnode_a1 \<equiv>
   new_cnode cnode_a1_size
             [0 \<mapsto> TcbCap tcb_a_id,
              1 \<mapsto> CNodeCap cnode_a2_id guard guard_size cnode_a2_size]"


definition
  "cnode_a2 \<equiv>
   new_cnode cnode_a2_size
             [0 \<mapsto> EndpointCap ep_id 0 {Write},
              2 \<mapsto> CNodeCap cnode_a1_id guard guard_size cnode_a1_size,
              3 \<mapsto> PageDirectoryCap pd_a_id Real None,
              4 \<mapsto> PageTableCap pt_a_id Real None,
              8 \<mapsto> FrameCap False frame_a1_id {AllowRead, AllowWrite} small_frame_size Real None,
              10 \<mapsto> NotificationCap ntfn_id 0 {Read},
              11 \<mapsto> FrameCap False frame_a2_id {AllowRead, AllowWrite} small_frame_size Real None,
              12 \<mapsto> IrqHandlerCap 4]"

definition
  "cnode_b \<equiv>
   new_cnode cnode_b_size
             [0 \<mapsto> TcbCap tcb_b_id,
              2 \<mapsto> CNodeCap cnode_b_id guard guard_size cnode_b_size,
              4 \<mapsto> EndpointCap ep_id 0 {Read},
              7 \<mapsto> PageDirectoryCap pd_b_id Real None,
              8 \<mapsto> FrameCap False frame_b_id {AllowRead, AllowWrite} small_section_size Real None,
              0x3F \<mapsto> IrqHandlerCap 0x3F]"

definition
  "cnode_extra \<equiv>
   new_cnode cnode_extra_size
             [0 \<mapsto> CNodeCap cnode_extra_id guard guard_size cnode_extra_size,
              1 \<mapsto> EndpointCap ep_id 0 UNIV,
              2 \<mapsto> NotificationCap ntfn_id 0 {Read, Write}]"

definition
  "pd_a \<equiv> \<lparr>cdl_page_directory_caps = new_cap_map pd_size [0 \<mapsto> PageTableCap pt_a_id Fake None]\<rparr>"

definition
  "pd_b \<equiv> \<lparr>cdl_page_directory_caps = new_cap_map pd_size
           [2 \<mapsto> FrameCap False frame_b_id {AllowRead, AllowWrite} small_section_size Fake None]\<rparr>"

definition
  "pt_a \<equiv> \<lparr>cdl_page_table_caps = new_cap_map pt_size
           [0 \<mapsto> FrameCap False frame_a1_id {AllowRead, AllowWrite} small_frame_size Fake None,
            255 \<mapsto> FrameCap False frame_a2_id {AllowRead, AllowWrite} small_frame_size Fake None]\<rparr>"

definition
  "empty_frame \<equiv> \<lparr>cdl_frame_size_bits = small_frame_size\<rparr>"
definition
  "empty_section \<equiv> \<lparr>cdl_frame_size_bits = small_section_size\<rparr>"

definition
  example_irq_node :: "cdl_irq \<Rightarrow> cdl_object_id"
where
  "example_irq_node = (\<lambda>irq. ucast irq + 0x100)"

definition
  "new_irq_node obj_id \<equiv>
    \<lparr> cdl_irq_node_caps = (\<lambda>slot. if slot = 0
                                    then Some (NotificationCap obj_id 0 {Read, Write})
                                    else None)\<rparr>"

definition
  irq_objects :: cdl_heap
where
  "irq_objects \<equiv>
  \<lambda>obj_id. if obj_id = 0x104
           then Some (IRQNode (new_irq_node ntfn_id))
           else if 0x100 \<le> obj_id \<and> obj_id \<le> 0x100 + mask LENGTH(irq_len)
           then (Some (IRQNode empty_irq_node))
           else None"


lemma
  "irq_objects =
  (\<lambda>obj_id. if 0x100 \<le> obj_id \<and> obj_id \<le> 0x100 + mask LENGTH(irq_len)
            then (Some (IRQNode empty_irq_node))
            else None) ++
  (\<lambda>obj_id. if obj_id = 0x104 then Some (IRQNode (new_irq_node ntfn_id))
           else None)"
  apply (rule ext)
  apply (clarsimp simp: irq_objects_def map_add_def)
  done


definition
  "example_spec =
  \<lparr>cdl_arch = ARM11,
   cdl_objects = [tcb_a_id    \<mapsto> Tcb tcb_a,
                  tcb_b_id    \<mapsto> Tcb tcb_b,
                  pd_a_id     \<mapsto> PageDirectory pd_a,
                  pt_a_id     \<mapsto> PageTable pt_a,
                  pd_b_id     \<mapsto> PageDirectory pd_b,
                  cnode_a1_id \<mapsto> CNode cnode_a1,
                  cnode_a2_id \<mapsto> CNode cnode_a2,
                  cnode_b_id  \<mapsto> CNode cnode_b,
                  cnode_extra_id \<mapsto> CNode cnode_extra,
                  frame_a1_id \<mapsto> Frame empty_frame,
                  frame_a2_id \<mapsto> Frame empty_frame,
                  frame_b_id  \<mapsto> Frame empty_section,
                  ep_id       \<mapsto> Endpoint,
                  ntfn_id     \<mapsto> Notification,
                  0x104       \<mapsto> IRQNode (new_irq_node ntfn_id),
                  0x13F       \<mapsto> IRQNode empty_irq_node],
   cdl_cdt = [(cnode_a2_id, 0)  \<mapsto> (cnode_extra_id, 1),
              (cnode_b_id,  4)  \<mapsto> (cnode_extra_id, 1),
              (cnode_a2_id, 10) \<mapsto> (cnode_extra_id, 2)], \<comment> \<open>All caps are orig caps,
                                                            except endpoints and notifications.\<close>
   cdl_current_thread = undefined,
   cdl_irq_node = example_irq_node,
   cdl_asid_table = undefined,
   cdl_current_domain = minBound\<rparr>"


lemmas cnode_defs = cnode_a1_def cnode_a2_def cnode_b_def cnode_extra_def
lemmas obj_defs   = cnode_defs tcb_a_def tcb_b_def pd_a_def pd_b_def pt_a_def

lemmas example_spec_def_expanded = example_spec_def
  [unfolded obj_defs tcb_slot_defs tcb_pending_op_slot_def
             new_cnode_def new_cap_map_def empty_cap_map_def]

(*************************
 *     Helper lemmas.    *
 *************************)
lemma cap_has_object_IrqHandlerCap [simp]:
  "\<not>cap_has_object (IrqHandlerCap irq)"
  by (clarsimp simp: cap_has_object_def)+

lemma badge_bits_2p [simp]:
  "(0::word32) < 2 ^ badge_bits"
  by (clarsimp simp: p2_gt_0 badge_bits_def)

lemma cdl_cnode_size_bits_new_cnode [simp]:
  "cdl_cnode_size_bits (new_cnode sz caps) = sz"
  by (clarsimp simp: new_cnode_def)

lemma cnode_cap_size_simps [simp]:
  "cnode_cap_size (CNodeCap a b c sz) = sz"
  by (clarsimp simp: cnode_cap_size_def)

lemma object_size_bits_new_cnode [simp]:
  "object_size_bits (CNode (new_cnode sz caps)) = sz"
  by (clarsimp simp: object_size_bits_def)

lemma object_slots_Endpoint [simp]:
  "object_slots Endpoint = Map.empty"
  by (simp add: object_slots_def)

lemma cdl_frame_size_bits_empty_frame [simp]:
  "cdl_frame_size_bits empty_frame = small_frame_size"
  by (simp add: empty_frame_def)

lemma cdl_frame_size_bits_empty_section [simp]:
  "cdl_frame_size_bits empty_section = small_section_size"
  by (simp add: empty_section_def)

lemma object_slots_empty_objects [simp]:
  "object_slots (Frame f) slot = None"
  by (clarsimp simp: object_slots_def)+

lemma is_fake_pt_cap_simps:
  "\<not> is_fake_pt_cap (PageTableCap obj_id Real asid)"
  "is_fake_pt_cap (PageTableCap obj_id Fake asid)"
  by (clarsimp simp: is_fake_pt_cap_def)+

lemma frame_cap_not_cnode:
  "\<not>is_cnode_cap (FrameCap dev a b c d e)"
  by (clarsimp simp: cap_type_def)

lemma empty_cap_map_NullCap [simp]:
  "empty_cap_map sz slot = Some cap \<Longrightarrow> cap = NullCap"
  by (clarsimp simp: empty_cap_map_def split: if_split_asm)

lemma new_cap_map_empty_NullCap [simp]:
  "new_cap_map sz Map.empty slot = Some cap \<Longrightarrow> cap = NullCap"
  by (clarsimp simp: new_cap_map_def)


lemma new_cap_map_slot:
  "\<lbrakk>new_cap_map sz caps slot = Some cap; cap \<noteq> NullCap\<rbrakk> \<Longrightarrow> caps slot = Some cap"
  by (clarsimp simp: new_cap_map_def empty_cap_map_def split: option.splits if_split_asm)

lemma cdl_cnode_caps_new_cnode:
  "\<lbrakk>cdl_cnode_caps (new_cnode sz caps) slot = Some cap; cap \<noteq> NullCap\<rbrakk> \<Longrightarrow> caps slot = Some cap"
  by (clarsimp simp: new_cnode_def, erule (1) new_cap_map_slot)

lemma new_cap_map_caps_D:
  "new_cap_map sz caps slot = Some cap \<Longrightarrow> caps slot = Some cap \<or> cap = NullCap"
  by (clarsimp simp: new_cap_map_def)

lemma cdl_cnode_caps_new_cnode_D:
  "\<lbrakk>cdl_cnode_caps (new_cnode sz caps) slot = Some cap\<rbrakk>
  \<Longrightarrow> caps slot = Some cap \<or> cap = NullCap"
  by (clarsimp simp: new_cnode_def, erule (1) new_cap_map_slot)

lemma cdl_irq_node_caps_empty_irq_node_D:
  "\<lbrakk>cdl_irq_node_caps (empty_irq_node) slot = Some cap\<rbrakk>
  \<Longrightarrow> cap = NullCap"
  by (clarsimp simp: empty_irq_node_def)

lemma object_slots_new_cnode_D:
  "object_slots (CNode (new_cnode sz caps)) slot = Some cap
  \<Longrightarrow> caps slot = Some cap \<or> cap = NullCap"
  by (clarsimp simp: object_slots_def dest!: cdl_cnode_caps_new_cnode_D)

lemma object_slots_new_cnode_cap_has_object [dest!]:
  "\<lbrakk>object_slots (CNode (new_cnode sz caps)) slot = Some cap; cap_has_object cap\<rbrakk>
  \<Longrightarrow> caps slot = Some cap"
  by (clarsimp simp: object_slots_def dest!: cdl_cnode_caps_new_cnode_D)

lemma cdl_cnode_caps_empty_cnode [dest!]:
  "cdl_cnode_caps (empty_cnode sz) slot = Some cap \<Longrightarrow> cap = NullCap"
  by (clarsimp simp: empty_cnode_def)

lemma cdl_cnode_caps_new_cnode_cnode_cap:
  "\<lbrakk>cdl_cnode_caps (new_cnode sz caps) slot = Some cap; is_cnode_cap cap\<rbrakk>
  \<Longrightarrow> caps slot = Some cap"
  by (erule cdl_cnode_caps_new_cnode, clarsimp)

lemma object_slots_new_cnode_cnode_cap:
  "\<lbrakk>object_slots (CNode (new_cnode sz caps)) slot = Some cap; is_cnode_cap cap\<rbrakk>
  \<Longrightarrow> caps slot = Some cap"
  by (clarsimp simp: object_slots_def, erule cdl_cnode_caps_new_cnode, clarsimp)

lemma object_slots_empty_irq_node [simp, dest!]:
  "object_slots (IRQNode empty_irq_node) slot = Some cap \<Longrightarrow> cap = NullCap"
  by (clarsimp simp: object_slots_def empty_irq_node_def)

lemma tcb_domain_simp [simp]:
  "tcb_domain (Tcb \<lparr>cdl_tcb_caps = caps,
                    cdl_tcb_fault_endpoint = 0,
                    cdl_tcb_intent = intent,
                    cdl_tcb_has_fault = fault,
                    cdl_tcb_domain = domain\<rparr>) = domain"
  by (simp add: tcb_domain_def)


lemma cdl_irq_node_example_spec [simp]:
  "cdl_irq_node example_spec = example_irq_node"
  by (clarsimp simp: example_spec_def)

lemma range_example_irq_node_helper:
  "range example_irq_node = (\<lambda>irq. irq + 0x100) ` range (ucast :: irq \<Rightarrow> 32 word)"
  by (auto simp: example_irq_node_def image_def)

lemma range_example_irq_node:
  "range example_irq_node =  {x. 0x100 \<le> x \<and> x < 0x100 + 2^irq_len}"
  apply (clarsimp simp: range_example_irq_node_helper ucast_range_less irq_len_val)
  apply (clarsimp simp: image_def)
  apply rule
   apply (clarsimp simp:  word_le_nat_alt  word_less_nat_alt unat_plus_if')
  apply clarsimp
  apply (rule_tac x="x - 0x100" in exI)
  apply unat_arith
  done

lemma irq_nodes_example_spec:
  "irq_nodes example_spec = {obj_id. obj_id = 0x104 \<or> obj_id = 0x13F}"
  by (auto simp: irq_nodes_def example_spec_def object_at_def is_irq_node_def)

(*************************
 * End of helper lemmas. *
 *************************)


(************************
Helpers on the specific state.

***************************)




lemma onehundred_not_le_one:
  "\<not>(0x100 \<le> (1::32 word))"
  by unat_arith

lemma object_type_simps [simp]:
  "object_type (Tcb t) = TcbType"
  "object_type (CNode c) = CNodeType"
  "object_type (Endpoint) = EndpointType"
  "object_type (Notification) = NotificationType"
  "object_type (PageDirectory pd) = PageDirectoryType"
  "object_type (PageTable pt) = PageTableType"
  "object_type (Frame f) = FrameType (cdl_frame_size_bits f)"
  "object_type (IRQNode empty_irq_node) = IRQNodeType"
  by (clarsimp simp: object_type_def)+

lemma cap_irq_simp [simp]:
  "cap_irq (IrqHandlerCap irq) = irq"
  by (simp add: cap_irq_def)

lemma example_irq_node_simps [simp]:
  "example_irq_node 4 = 0x104"
  "example_irq_node 0x3F = 0x13F"
  by (simp add: example_irq_node_def)+

lemma irq_objects_simps [simp]:
  "irq_objects 0 = None"
  "irq_objects 1 = None"
  "irq_objects 2 = None"
  "irq_objects 3 = None"
  "irq_objects 4 = None"
  "irq_objects 5 = None"
  "irq_objects 6 = None"
  "irq_objects 7 = None"
  "irq_objects 8 = None"
  "irq_objects 9 = None"
  "irq_objects 0xA = None"
  "irq_objects 0xB = None"
  "irq_objects 0xC = None"
  "irq_objects 0xD = None"
  by (clarsimp simp: irq_objects_def onehundred_not_le_one)+


lemma opt_cap_example_spec [simp]:
  "opt_cap (4, slot) example_spec = object_slots (Frame empty_frame) slot"
  "opt_cap (5, slot) example_spec = object_slots (CNode cnode_b) slot"
  "opt_cap (6, slot) example_spec = object_slots (CNode cnode_a1) slot"
  "opt_cap (7, slot) example_spec = object_slots (CNode cnode_a2) slot"
  "opt_cap (0xB, slot) example_spec = object_slots (CNode cnode_extra) slot"
  by (auto simp: example_spec_def opt_cap_def slots_of_def
                 map_add_def  irq_objects_def
          split: if_split_asm)

lemma irq_objects_some_object:
  "irq_objects obj_id = Some obj \<Longrightarrow>
  (obj_id = 0x104 \<and> obj = IRQNode (new_irq_node ntfn_id)) \<or> obj = IRQNode empty_irq_node"
  by (clarsimp simp: irq_objects_def split: if_split_asm)

(*
lemma real_cnode_at_example_spec:
  "real_cnode_at obj_id example_spec
  \<Longrightarrow> obj_id = cnode_a1_id \<or> obj_id = cnode_a2_id \<or> obj_id = cnode_b_id \<or> obj_id = cnode_extra_id"
  apply (clarsimp simp: real_cnode_at_def object_at_def is_cnode_def irq_cnodes_example_spec)
  by (auto simp: example_spec_def object_at_def is_cnode_def irq_objects_def
          split: if_split_asm cdl_object.splits)
*)

lemma cnode_at_example_spec:
  "cnode_at obj_id example_spec =
  (obj_id = cnode_a1_id \<or> obj_id = cnode_a2_id \<or> obj_id = cnode_b_id \<or> obj_id = cnode_extra_id)"
  apply (clarsimp simp: object_at_def is_cnode_def)
  apply (auto simp: example_spec_def irq_objects_def map_add_def
             split: if_split_asm cdl_object.splits)
  done

lemma pt_at_example_spec:
  "pt_at obj_id example_spec = (obj_id = pt_a_id)"
  apply (clarsimp simp: object_at_def is_cnode_def)
  apply (auto simp: example_spec_def object_at_def is_pt_def irq_objects_def
                    new_irq_node_def empty_irq_node_def
             split: if_split_asm cdl_object.splits)
  done

lemma pd_at_example_spec:
  "pd_at obj_id example_spec = (obj_id = pd_a_id \<or> obj_id = pd_b_id)"
  apply (clarsimp simp: object_at_def is_cnode_def)
  apply (auto simp: example_spec_def object_at_def is_pd_def irq_objects_def
                    new_irq_node_def empty_irq_node_def
             split: if_split_asm cdl_object.splits)
  done

lemma slots_of_example_spec_obj_ids:
  "\<lbrakk>slots_of obj_id example_spec 0 = Some cap; cap \<noteq> NullCap\<rbrakk>\<Longrightarrow>
  ((obj_id = tcb_a_id) \<or>
  (obj_id = tcb_b_id) \<or>
  (obj_id = cnode_a1_id) \<or>
  (obj_id = cnode_a2_id) \<or>
  (obj_id = cnode_b_id) \<or>
  (obj_id = cnode_extra_id) \<or>
  (obj_id = pd_a_id) \<or>
  (obj_id = pt_a_id) \<or>
  (obj_id = pd_b_id) \<or>
  (obj_id = 0x104))"
  by (clarsimp simp: example_spec_def slots_of_def object_slots_def
              split: if_split_asm)

lemma irq_handler_cap_example_spec:
  "\<lbrakk>is_irqhandler_cap cap; opt_cap (obj_id, slot) example_spec = Some cap\<rbrakk>
  \<Longrightarrow> (obj_id = cnode_a2_id \<and> slot = 12) \<or>
      (obj_id = cnode_b_id \<and> slot = 0x3F)"
  by (clarsimp simp: example_spec_def opt_cap_def slots_of_def
                     object_slots_def empty_irq_node_def new_irq_node_def new_cnode_def
                     obj_defs new_cap_map_def empty_cap_map_def
              split: if_split_asm)


lemma irqhandler_cap_at_example_spec:
  "irqhandler_cap_at (obj_id, slot) example_spec
  = ((obj_id = cnode_a2_id \<and> slot = 12) \<or>
     (obj_id = cnode_b_id \<and> slot = 0x3F))"
  apply (clarsimp simp: cap_at_def)
  apply (rule iffI)
   apply clarsimp
   apply (drule (1) irq_handler_cap_example_spec)
   apply clarsimp
  apply (erule disjE)
   apply (clarsimp simp: cnode_a2_def object_slots_def new_cnode_def new_cap_map_def)
  apply (clarsimp simp: cnode_b_def object_slots_def new_cnode_def new_cap_map_def)
  done

lemma cap_at_has_no_parents_in_cdt_example_spec:
  "cap_at_has_no_parents_in_cdt (obj_id, slot) example_spec
  = ((obj_id \<noteq> cnode_a2_id \<or> slot \<noteq> 0) \<and>
     (obj_id \<noteq> cnode_a2_id \<or> slot \<noteq> 10) \<and>
     (obj_id \<noteq> cnode_b_id \<or> slot \<noteq> 4))"
  by (auto simp: cap_at_has_no_parents_in_cdt_def opt_parent_def example_spec_def)

lemma is_orig_cap_example_spec:
  "original_cap_at (obj_id, slot) example_spec
  = ((obj_id \<noteq> cnode_a2_id \<or> slot \<noteq> 0) \<and>
     (obj_id \<noteq> cnode_a2_id \<or> slot \<noteq> 10) \<and>
     (obj_id \<noteq> cnode_b_id \<or> slot \<noteq> 4))"
  by (fastforce simp: original_cap_at_def cap_at_has_no_parents_in_cdt_example_spec irqhandler_cap_at_example_spec)


(****************************************
 * Proof that the state is well formed. *
 ****************************************)

lemma well_formed_tcb_a:
  "well_formed_tcb example_spec obj_id (Tcb tcb_a)"
  by (auto simp: well_formed_tcb_def object_slots_def tcb_a_def tcb_slot_defs tcb_has_fault_def
                 is_default_cap_def default_cap_def cap_type_def irq_nodes_example_spec)

lemma well_formed_tcb_b:
  "well_formed_tcb example_spec obj_id (Tcb tcb_b)"
  by (auto simp: well_formed_tcb_def object_slots_def tcb_b_def tcb_slot_defs tcb_has_fault_def
                 is_default_cap_def default_cap_def cap_type_def irq_nodes_example_spec)

lemma well_formed_orig_caps_unique_example:
  "well_formed_orig_caps_unique example_spec"
  apply (clarsimp simp: well_formed_orig_caps_unique_def)
  apply (clarsimp simp: cnode_at_example_spec is_orig_cap_example_spec)
  by (elim disjE, (clarsimp simp: cnode_defs split: if_split_asm)+)

lemma well_formed_fake_pt_caps_unique_example:
  "well_formed_fake_pt_caps_unique example_spec"
   apply (clarsimp simp: well_formed_fake_pt_caps_unique_def
                         pd_at_example_spec)
   apply (fastforce simp: example_spec_def opt_cap_def slots_of_def
                          object_slots_def is_fake_pt_cap_simps
                          pd_a_def pd_b_def new_cap_map_def irq_objects_def
                   split: if_split_asm option.splits)
  done

lemma well_formed_orig_cap_tcb [simp]:
  "well_formed_orig_cap (TcbCap obj_id)"
  by (clarsimp simp: well_formed_orig_cap_def default_cap_def cap_type_def
                     cap_rights_def ep_related_cap_def)

lemma well_formed_cap_ex [simp]:
  "well_formed_cap (CNodeCap a 0 0 2)"
  "well_formed_cap (TcbCap 0)"
  by (clarsimp simp: well_formed_cap_def guard_bits_def)+

lemma well_formed_cap_example [simp]:
  "\<lbrakk>cdl_objects example_spec obj_id = Some obj;
    object_slots obj slot = Some cap; cap \<noteq> NullCap\<rbrakk>
  \<Longrightarrow> well_formed_cap cap"
  apply (clarsimp simp: well_formed_cap_def)
  by (clarsimp simp: well_formed_cap_def example_spec_def
                     obj_defs new_cap_map_def new_irq_node_def new_cnode_def
                     object_slots_def empty_cap_map_def guard_bits_def
                     tcb_slot_defs vm_read_write_def
              split: cdl_cap.splits if_split_asm)

lemma well_formed_cdt_example [simp]:
  "\<lbrakk>cdl_objects example_spec obj_id = Some obj;
    object_slots obj slot = Some cap; cap \<noteq> NullCap\<rbrakk>
  \<Longrightarrow> well_formed_cdt example_spec (obj_id, slot) cap"
  apply (clarsimp simp: well_formed_cdt_def)
  apply (clarsimp simp: cnode_at_example_spec)
  apply (case_tac "(obj_id = cnode_a2_id \<and> slot = 0) \<or>
                   (obj_id = cnode_b_id \<and> slot = 4)")
   apply (rule_tac x=cnode_extra_id in exI, clarsimp, rule conjI)
    subgoal by (fastforce simp: example_spec_def cnode_defs
                    split: if_split_asm)
   apply (rule_tac x=1 in exI)
   apply (clarsimp simp: is_orig_cap_example_spec)
   apply (clarsimp simp: example_spec_def opt_cap_def slots_of_def
                         cnode_defs object_slots_def new_cnode_def new_cap_map_def
                         irq_objects_def map_add_def empty_irq_node_def
                  split: if_split_asm)
  apply (case_tac "(obj_id = cnode_a2_id \<and> slot = 10)")
   apply (rule_tac x=cnode_extra_id in exI, clarsimp, rule conjI)
    apply (fastforce simp: example_spec_def cnode_defs
                    split: if_split_asm)
   apply (rule_tac x=2 in exI)
   apply (clarsimp simp: is_orig_cap_example_spec)
   apply (clarsimp simp: example_spec_def opt_cap_def slots_of_def
                         cnode_defs object_slots_def new_cnode_def new_cap_map_def
                         irq_objects_def map_add_def empty_irq_node_def
                  split: if_split_asm)
  apply clarsimp
  apply (rule_tac x=obj_id in exI, clarsimp, rule conjI)
   apply (clarsimp simp: example_spec_def cnode_defs
                  dest!: object_slots_new_cnode_D
                  split: if_split_asm)
  apply (fastforce simp: is_orig_cap_example_spec opt_cap_def slots_of_def)
  done

lemma well_formed_orig_cap_example [simp]:
  "\<lbrakk>cdl_objects example_spec obj_id = Some obj;
    object_slots obj slot = Some cap; cap \<noteq> NullCap;
    original_cap_at (obj_id, slot) example_spec \<rbrakk>
   \<Longrightarrow> well_formed_orig_cap cap"
  apply (clarsimp simp: is_orig_cap_example_spec well_formed_orig_cap_def)
  by (clarsimp simp: example_spec_def object_slots_def obj_defs new_cnode_def new_cap_map_def
                        new_irq_node_def ep_related_cap_def cap_type_def default_cap_def cap_rights_def
                split: if_split_asm)

lemma well_formed_caps_example:
  "cdl_objects example_spec obj_id = Some obj \<Longrightarrow>
   well_formed_caps example_spec obj_id obj"
   apply (clarsimp simp: well_formed_caps_def, rule conjI)
   apply (clarsimp simp: is_orig_cap_example_spec)
   apply (clarsimp simp: example_spec_def obj_defs object_type_def cap_type_def object_slots_def
                         is_copyable_cap_def
                  dest!: cdl_cnode_caps_new_cnode_D new_cap_map_caps_D
                  split: if_split_asm)
   apply (rule conjI)
    apply (clarsimp simp: well_formed_cap_to_real_object_def real_object_at_def irq_nodes_example_spec)
    apply (clarsimp simp: example_spec_def obj_defs object_slots_def onehundred_not_le_one
                   dest!: cdl_cnode_caps_new_cnode_D new_cap_map_caps_D
                          irq_objects_some_object cdl_irq_node_caps_empty_irq_node_D
                   split: if_split_asm)
    apply (fastforce simp: new_irq_node_def empty_irq_node_def split: if_split_asm)
   apply (rule conjI)
    apply (clarsimp simp: well_formed_cap_types_match_def)
    apply (rule conjI)
     apply (clarsimp simp: example_spec_def object_slots_def obj_defs
                           irq_objects_def map_add_def new_irq_node_def
                           onehundred_not_le_one
                    dest!: cdl_cnode_caps_new_cnode_D new_cap_map_caps_D
                           cdl_irq_node_caps_empty_irq_node_D
                    split: if_split_asm)
   apply (clarsimp simp: example_spec_def object_slots_def obj_defs
                         irq_objects_def map_add_def new_irq_node_def
                         onehundred_not_le_one object_type_def
                  dest!: cdl_cnode_caps_new_cnode_D new_cap_map_caps_D cdl_irq_node_caps_empty_irq_node_D
                  split: if_split_asm)
   by (clarsimp simp: example_spec_def obj_defs is_cnode_def is_tcb_def is_fake_vm_cap_def
                         object_slots_def object_type_def cap_type_def new_irq_node_def
                         empty_irq_node_def empty_cnode_def
                  dest!: cdl_cnode_caps_new_cnode_D irq_objects_some_object cdl_irq_node_caps_empty_irq_node_D
                  split: if_split_asm cdl_object.splits)

lemma real_object_at_example_spec:
  "real_object_at obj_id example_spec =
  ((obj_id = tcb_a_id) \<or>
  (obj_id = tcb_b_id) \<or>
  (obj_id = cnode_a1_id) \<or>
  (obj_id = cnode_a2_id) \<or>
  (obj_id = cnode_b_id) \<or>
  (obj_id = cnode_extra_id) \<or>
  (obj_id = ep_id) \<or>
  (obj_id = ntfn_id) \<or>
  (obj_id = pd_a_id) \<or>
  (obj_id = pt_a_id) \<or>
  (obj_id = pd_b_id) \<or>
  (obj_id = frame_a1_id) \<or>
  (obj_id = frame_a2_id) \<or>
  (obj_id = frame_b_id))"
  apply (clarsimp simp: real_object_at_def irq_nodes_example_spec)
  apply (clarsimp simp: example_spec_def irq_objects_def dom_def onehundred_not_le_one
                 split: if_split_asm)
  done

lemma real_object_at_example_spec_simp [simp]:
  "real_object_at 0 example_spec"
  "real_object_at 1 example_spec = True"
  "real_object_at 2 example_spec"
  "real_object_at 3 example_spec"
  "real_object_at 4 example_spec"
  "real_object_at 5 example_spec"
  "real_object_at 6 example_spec"
  "real_object_at 7 example_spec"
  "real_object_at 8 example_spec"
  "real_object_at 9 example_spec"
  "real_object_at 0xA example_spec"
  "real_object_at 0xB example_spec"
  "real_object_at 0xC example_spec"
  "real_object_at 0xD example_spec"
  "\<not>real_object_at 0x104 example_spec"
  "\<not>real_object_at 0x13F example_spec"
  by (clarsimp simp: real_object_at_example_spec)+

lemma cdl_objects_example_spec_simps [simp]:
  "cdl_objects example_spec 4 = Some (Frame empty_frame)"
  "cdl_objects example_spec 0xD = Some Notification"
  "cdl_objects example_spec 0x13F = Some (IRQNode empty_irq_node)"
  by (clarsimp simp: example_spec_def map_add_def)+

lemma well_formed_cap_to_object_example:
  "cdl_objects example_spec obj_id = Some obj
   \<Longrightarrow> well_formed_cap_to_object example_spec obj_id obj"
  apply (clarsimp simp: well_formed_cap_to_object_def is_orig_cap_example_spec)
  apply (intro conjI)
   apply (case_tac "obj_id = ep_id \<or>
                    obj_id = ntfn_id \<or>
                    obj_id = cnode_extra_id")
    apply (rule_tac x=cnode_extra_id in exI)
    apply (fastforce simp: cnode_at_example_spec cnode_extra_def
                           object_slots_def new_cnode_def new_cap_map_def)
   apply (case_tac "obj_id = tcb_b_id \<or>
                    obj_id = cnode_b_id \<or>
                    obj_id = pd_b_id \<or>
                    obj_id = frame_b_id")
    apply (rule_tac x=cnode_b_id in exI)
    apply (fastforce simp: cnode_at_example_spec cnode_b_def
                          object_slots_def new_cnode_def new_cap_map_def)
   apply (case_tac "obj_id = tcb_a_id \<or>
                    obj_id = cnode_a2_id")
    apply (rule_tac x=cnode_a1_id in exI)
    apply (fastforce simp: cnode_at_example_spec cnode_a1_def
                          object_slots_def new_cnode_def new_cap_map_def)
   apply (case_tac "obj_id = cnode_a1_id \<or>
                    obj_id = pd_a_id \<or>
                    obj_id = pt_a_id \<or>
                    obj_id = frame_a1_id \<or>
                    obj_id = ep_id")
    apply (rule_tac x=cnode_a2_id in exI)
    apply (fastforce simp: cnode_at_example_spec cnode_a2_def
                           object_slots_def new_cnode_def new_cap_map_def)
   apply (case_tac "obj_id = frame_a2_id")
    apply (rule_tac x=cnode_a2_id in exI)
    apply (rule_tac x=11 in exI) (* Not sure why fastforce gives up here. *)
    apply (fastforce simp: cnode_at_example_spec cnode_a2_def
                           object_slots_def new_cnode_def new_cap_map_def)
   apply (case_tac "obj_id = 0x104")
    apply (rule_tac x=cnode_a2_id in exI)
    apply (rule_tac x=12 in exI) (* Not sure why fastforce gives up here. *)
    apply (fastforce simp: cnode_at_example_spec cnode_a2_def
                           object_slots_def new_cnode_def new_cap_map_def)
   apply (case_tac "obj_id = 0x13F")
    apply (rule_tac x=cnode_b_id in exI)
    apply (fastforce simp: cnode_at_example_spec cnode_b_def
                           object_slots_def new_cnode_def new_cap_map_def)
   apply (clarsimp simp: example_spec_def)
  apply clarsimp
  apply (clarsimp simp: example_spec_def)
  by (clarsimp simp: opt_cap_def slots_of_def obj_defs
                        object_slots_def object_size_bits_def
                        new_cap_map_def empty_cap_map_def frame_cap_not_cnode
                        empty_irq_node_def new_irq_node_def
                 split: if_split_asm
       | drule (1) cdl_cnode_caps_new_cnode_cnode_cap)+ (* Takes 20 seconds. *)

lemma well_formed_cap_to_non_empty_pt_example:
  "cdl_objects example_spec obj_id = Some obj \<Longrightarrow>
    well_formed_cap_to_non_empty_pt example_spec obj_id obj"
  apply (clarsimp simp: well_formed_cap_to_non_empty_pt_def pt_at_example_spec)
  apply (rule exI [where x=pd_a_id])
  apply (clarsimp simp: well_formed_cap_to_non_empty_pt_def example_spec_def is_pt_def
                        object_at_def opt_cap_def slots_of_def object_slots_def
                        obj_defs new_cap_map_def is_pd_def empty_cap_map_def
              split: if_split_asm)
  done

lemma well_formed_vspace_example:
  "cdl_objects example_spec obj_id = Some obj
  \<Longrightarrow> well_formed_vspace example_spec obj_id obj"
  apply (clarsimp simp: well_formed_vspace_def well_formed_cap_to_non_empty_pt_example)
  apply (clarsimp simp: example_spec_def is_pt_def is_pd_def object_slots_def empty_cap_map_def
                        new_irq_node_def
                 split: if_split_asm)
    apply (fastforce simp: cap_type_def is_fake_vm_cap_def obj_defs new_cap_map_def small_section_size_def
                    split: if_split_asm)
   apply (clarsimp simp: obj_defs new_cap_map_def cap_type_def small_frame_size_def
                         is_fake_vm_cap_def is_fake_pt_cap_simps small_section_size_def
                  split: if_split_asm)
  apply (clarsimp simp: obj_defs new_cap_map_def cap_type_def small_frame_size_def
                        is_fake_vm_cap_def is_fake_pt_cap_simps small_section_size_def
                 split: if_split_asm)
  done


lemma well_formed_irqhandler_caps_unique_example_spec:
  "well_formed_irqhandler_caps_unique example_spec"
  apply (clarsimp simp: well_formed_irqhandler_caps_unique_def)
  apply (drule (1) irq_handler_cap_example_spec)+
  by (clarsimp simp: example_spec_def opt_cap_def slots_of_def
                        object_slots_def obj_defs
                        new_cnode_def new_cap_map_def
                 split: if_split_asm)

lemma ucast_0xFE:
  "(ucast :: 8 word \<Rightarrow> 32 word) irq = 0xFE \<Longrightarrow> irq = 0xFE"
  by (rule ucast_up_inj, simp+)

lemma ucast_4:
  "(ucast :: irq \<Rightarrow> 32 word) irq = 4 \<Longrightarrow> irq = 4"
  by (rule ucast_up_inj, simp+)

lemma rangeD:
  "\<lbrakk>range f = A; f x = y\<rbrakk> \<Longrightarrow> y \<in> A"
  by (fastforce simp: image_def)

lemma slots_of_example_irq_node:
  "\<lbrakk>slots_of (example_irq_node irq) example_spec 0 = Some cap;
    cap \<noteq> NullCap\<rbrakk>
  \<Longrightarrow> (irq = 4)"
  apply (frule (1) slots_of_example_spec_obj_ids)
  apply (insert range_example_irq_node)
  apply (erule disjE, drule (1) rangeD, simp add: onehundred_not_le_one)+
  apply (clarsimp simp: example_irq_node_def ucast_4)
  done

lemma bound_irqs_example_spec [simp]:
  "bound_irqs example_spec = {4}"
  apply (clarsimp simp: bound_irqs_def)
  apply rule
   apply clarsimp
   apply (erule (1) slots_of_example_irq_node)
  apply (clarsimp simp: example_spec_def slots_of_def
                        object_slots_def new_irq_node_def)
  done

lemma well_formed_irqhandler_caps_example_spec:
  "well_formed_irqhandler_caps example_spec"
  apply (clarsimp simp: well_formed_irqhandler_caps_def)
  apply (rule exI [where x=cnode_a2_id])
  apply (rule exI [where x=12])
  apply (rule exI [where x="IrqHandlerCap 4"])
  apply (clarsimp simp: object_slots_def cnode_a2_def new_cnode_def new_cap_map_def)
  done

lemma rangeI:
  "f x = a \<Longrightarrow> a \<in> range f"
  by auto

lemma well_formed_irq_table_example_spec:
  "well_formed_irq_table example_spec"
  apply (clarsimp simp: well_formed_irq_table_def)
  apply (rule conjI)
   apply (clarsimp simp: example_irq_node_def)
   apply (clarsimp simp: inj_on_def ucast_up_inj)
  apply (clarsimp simp: irq_nodes_example_spec)
  apply (rule subset_antisym)
   apply (clarsimp simp: example_spec_def)
   apply (metis example_irq_node_simps)
  apply clarsimp
  apply (clarsimp simp: example_spec_def split: if_split_asm,
         (drule rangeI [where f=example_irq_node],
          simp add: range_example_irq_node onehundred_not_le_one)+)
  done

lemma well_formed_tcb_example_spec:
  "cdl_objects example_spec obj_id = Some obj \<Longrightarrow>
   well_formed_tcb example_spec obj_id obj"
   apply (case_tac "obj_id = tcb_a_id")
    apply (cut_tac obj_id = tcb_a_id in well_formed_tcb_a)
    apply (clarsimp simp: example_spec_def split: if_split_asm)
   apply (case_tac "obj_id = tcb_b_id")
    apply (cut_tac obj_id = tcb_b_id in well_formed_tcb_b)
    apply (clarsimp simp: example_spec_def split: if_split_asm)
   by (clarsimp simp: example_spec_def well_formed_tcb_def is_tcb_def
                         empty_irq_node_def new_irq_node_def
                  split: if_split_asm)

lemma well_formed_irq_node_example_spec:
  "cdl_objects example_spec obj_id = Some obj \<Longrightarrow>
   well_formed_irq_node example_spec obj_id obj"
  apply (clarsimp simp: well_formed_irq_node_def irq_nodes_example_spec)
  apply (clarsimp simp: example_spec_def object_slots_def empty_irq_node_def new_irq_node_def
                        empty_cnode_def empty_cap_map_def dom_def
                        is_default_cap_def default_cap_def onehundred_not_le_one
                        split: if_split_asm)
  done

lemma well_formed_example:
  "well_formed example_spec"
  apply (clarsimp simp: well_formed_def)
  apply (intro conjI)
       apply (rule well_formed_orig_caps_unique_example)
      apply (rule well_formed_irqhandler_caps_unique_example_spec)
     apply (rule well_formed_fake_pt_caps_unique_example)
    apply (rule well_formed_irqhandler_caps_example_spec)
   apply (rule well_formed_irq_table_example_spec)
  apply (clarsimp split: option.splits, rename_tac obj)
  apply (clarsimp simp: well_formed_caps_example well_formed_cap_to_object_example
                        well_formed_orig_caps_unique_example)
  apply (rule conjI)
   apply (fact well_formed_tcb_example_spec)
  apply (rule conjI)
   apply (fact well_formed_vspace_example)
  apply (rule conjI)
   apply (fact well_formed_irq_node_example_spec)
  apply (clarsimp simp: cnode_at_example_spec)
  by (auto simp: example_spec_def object_size_bits_def object_default_state_def2
                    pd_size_def word_bits_def empty_cnode_def is_cnode_def
                    object_slots_def empty_cap_map_def tcb_slot_defs slots_of_def
                    default_tcb_def obj_defs cap_at_def opt_cap_def
                    small_frame_size_def small_section_size_def pt_size_def
                    new_cnode_def new_cap_map_def empty_irq_node_def
                    new_irq_node_def
             split: if_split_asm)

end

end

