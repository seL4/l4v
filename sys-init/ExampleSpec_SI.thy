(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

(*
 * This file contains an example spec, and shows it obeys the well_formed constraints
 *
 * This file contains the invariants of the user-space initialiser,
 * the well-formed conditions of the input capDL specification,
 * and the predicates describing the initial state.
 *)

theory ExampleSpec_SI
imports WellFormed_SI
begin

declare cap_object_simps [simp]

lemma object_slots_empty_object [simp]:
  "object_slots (Frame \<lparr>cdl_frame_size_bits = small_frame_size\<rparr>) slot = Some cap \<Longrightarrow> cap = NullCap"
  "object_slots (PageDirectory \<lparr>cdl_page_directory_caps = empty_cap_map pd_size\<rparr>) slot = Some cap \<Longrightarrow> cap = NullCap"
  "empty_cap_map obj_id slot = Some cap \<Longrightarrow> cap = NullCap"
  by (clarsimp simp: object_slots_def empty_cap_map_def
              split: split_if_asm)+

lemma object_type_simps [simp]:
  "object_type (Tcb t) = TcbType"
  "object_type (CNode c) = CNodeType"
  "object_type (PageDirectory pd) = PageDirectoryType"
  "object_type (PageTable pt) = PageTableType"
  "object_type (Frame f) = FrameType (cdl_frame_size_bits f)"
  by (clarsimp simp: object_type_def)+

lemma cap_type'_simps [simp]:
  "cap_type' (TcbCap obj_id) = Some TcbType"
  "cap_type' (CNodeCap obj_id g gs sz) = Some CNodeType"
  "cap_type' (PageDirectoryCap obj_id r asid) = Some PageDirectoryType"
  "cap_type' (PageTableCap obj_id r asid) = Some PageTableType"
  "cap_type' (FrameCap obj_id rights sz r asid) = Some (FrameType sz)"
  by (clarsimp simp: cap_type'_def cap_type_def)+

lemma is_irqhandler_cap_simps [simp]:
  "\<not> is_irqhandler_cap (TcbCap obj_id)"
  "\<not> is_irqhandler_cap (CNodeCap obj_id g gs sz)"
  "\<not> is_irqhandler_cap (PageDirectoryCap obj_id r asid)"
  "\<not> is_irqhandler_cap (PageTableCap obj_id r asid)"
  "\<not> is_irqhandler_cap (FrameCap obj_id rights sz r asid)"
  by (clarsimp simp: is_irqhandler_cap_def)+

lemma well_formed_empty:
  "well_formed \<lparr>
  cdl_arch = undefined,
  cdl_objects = empty,
  cdl_cdt = undefined,
  cdl_current_thread = undefined,
  cdl_irq_node = ucast,
  cdl_asid_table = undefined,
  cdl_current_domain = undefined
\<rparr>"
  by (clarsimp simp: well_formed_def well_formed_orig_caps_unique_def
                     well_formed_irqhandler_caps_unique_def well_formed_irqhandler_caps_def
                     well_formed_irq_table_def ucast_8_32_inj
                     well_formed_fake_pt_caps_unique_def object_at_def
                     opt_cap_def slots_of_def opt_object_def bound_irqs_def)


definition "tcb_id = 1000"
definition "cnode_id = 1001"
definition "pd_id = 1002"
definition "frame_id = 1003"
lemmas object_id_defs = tcb_id_def cnode_id_def pd_id_def frame_id_def

definition
  "example_tcb =
  \<lparr>cdl_tcb_caps = [tcb_cspace_slot \<mapsto> CNodeCap cnode_id 0 1 2,
                   tcb_vspace_slot \<mapsto> PageDirectoryCap pd_id Real None,
                   tcb_replycap_slot \<mapsto> NullCap,
                   tcb_caller_slot \<mapsto> NullCap,
                   tcb_ipcbuffer_slot \<mapsto> FrameCap frame_id {AllowRead, AllowWrite} small_frame_size Real None,
                   tcb_pending_op_slot \<mapsto> NullCap],
   cdl_tcb_fault_endpoint = 0,
   cdl_tcb_intent = \<lparr>cdl_intent_op = None,
                     cdl_intent_error = False,
                     cdl_intent_cap = 0,
                     cdl_intent_extras = [],
                     cdl_intent_recv_slot = None\<rparr>,
   cdl_tcb_has_fault = False,
   cdl_tcb_domain = minBound\<rparr>"

definition
  example_irq_node :: "cdl_irq \<Rightarrow> cdl_object_id"
where
  "example_irq_node = ucast"

definition
  example_irq_node2 :: "cdl_irq \<Rightarrow> cdl_object_id"
where
  "example_irq_node2 = (\<lambda>irq. ucast irq + 100)"

lemma example_irq_node_def2:
  "example_irq_node2 = (\<lambda>irq. word_of_int (uint irq + 100))"
  unfolding example_irq_node2_def
  by (metis (hide_lams) ucast_def wi_hom_add word_of_int_numeral)

definition
  "example_spec =
  \<lparr>cdl_arch = undefined,
   cdl_objects = [tcb_id \<mapsto> Tcb example_tcb,
                  cnode_id \<mapsto> CNode (\<lparr>cdl_cnode_caps = (empty_cap_map 2) ++
                       [0 \<mapsto> TcbCap tcb_id,
                        1 \<mapsto> CNodeCap cnode_id 0 0 2,
                        2 \<mapsto> PageDirectoryCap pd_id Real None,
                        3 \<mapsto> FrameCap frame_id {AllowRead, AllowWrite} small_frame_size Real None],
                               cdl_cnode_size_bits = 2\<rparr>),
                  pd_id \<mapsto> PageDirectory \<lparr>cdl_page_directory_caps = empty_cap_map pd_size\<rparr>,
                  frame_id \<mapsto> Frame \<lparr>cdl_frame_size_bits = small_frame_size\<rparr>],
   cdl_cdt = empty, (* All caps are orig caps. *)
   cdl_current_thread = undefined,
   cdl_irq_node = example_irq_node,
   cdl_asid_table = undefined,
   cdl_current_domain = undefined\<rparr>"

lemma cdl_irq_node_example_spec [simp]:
  "cdl_irq_node example_spec = example_irq_node"
  by (clarsimp simp: example_spec_def)

lemma cnode_id_not_in_irq_cnodes:
  "cnode_id \<notin> irq_cnodes example_spec"
  apply (clarsimp simp: irq_cnodes_def example_spec_def)
  apply (subgoal_tac "cnode_id \<notin> range example_irq_node", simp)
  apply (unfold example_irq_node_def)
  apply (subst ucast_range_less, simp)
  apply (clarsimp simp: cnode_id_def)
  done

lemma well_formed_tcb_example:
  "well_formed_tcb example_spec minBound (Tcb example_tcb)"
  by (auto simp: well_formed_tcb_def object_slots_def example_tcb_def tcb_slot_defs
                 tcb_domain_def tcb_pending_op_slot_def tcb_has_fault_def is_default_cap_def
                 default_cap_def cap_type_def cnode_id_not_in_irq_cnodes)

lemma well_formed_orig_caps_unique_example:
  "well_formed_orig_caps_unique example_spec"
   by (auto simp: well_formed_orig_caps_unique_def example_spec_def
                  object_at_def is_cnode_def opt_cap_def
                  slots_of_def object_slots_def opt_object_def
                  empty_cap_map_def cap_object_def cap_has_object_def
                  update_slots_def object_id_defs
                  real_cnode_at_def
           split: split_if_asm option.splits)

lemma well_formed_irqhandler_caps_unique_example:
  "well_formed_irqhandler_caps_unique example_spec"
  apply (clarsimp simp: well_formed_irqhandler_caps_unique_def is_irqhandler_cap_def cap_irq_def
                 split: cdl_cap.splits)
  apply (clarsimp simp: example_spec_def opt_cap_def slots_of_def opt_object_def
                        object_slots_def empty_cap_map_def example_tcb_def
                 split: split_if_asm option.splits)
  done

lemma well_formed_fake_pt_caps_unique_example:
  "well_formed_fake_pt_caps_unique example_spec"
   by (auto simp: well_formed_fake_pt_caps_unique_def example_spec_def
                  object_at_def opt_cap_def
                  slots_of_def object_slots_def opt_object_def
                  empty_cap_map_def is_pd_def
           split: split_if_asm option.splits)

lemma well_formed_orig_cap_tcb [simp]:
  "well_formed_orig_cap (TcbCap obj_id)"
  by (clarsimp simp: well_formed_orig_cap_def default_cap_def cap_type_def
                     cap_rights_def ep_related_cap_def)

lemma well_formed_cap_ex [simp]:
  "well_formed_cap (CNodeCap a 0 0 2)"
  "well_formed_cap (TcbCap 0)"
  by (clarsimp simp: well_formed_cap_def guard_bits_def)+

lemma cap_at_has_no_parents_in_cdt_example_spec [simp]:
  "cap_at_has_no_parents_in_cdt cap_ref example_spec"
  by (clarsimp simp: cap_at_has_no_parents_in_cdt_def example_spec_def opt_parent_def)

lemma irqhandler_cap_at_example_spec [simp]:
  "\<not> irqhandler_cap_at cap_ref example_spec"
  by (clarsimp simp: example_spec_def cap_at_def object_id_defs split_beta'
                        opt_cap_def slots_of_def opt_object_def object_slots_def
                        example_tcb_def tcb_slot_defs tcb_pending_op_slot_def empty_cap_map_def
                 split: split_if_asm)

lemma original_cap_at_example_spec [simp]:
  "original_cap_at cap_ref example_spec"
  by (clarsimp simp: original_cap_at_def)

lemma well_formed_cap_example [simp]:
  "\<lbrakk>cdl_objects example_spec obj_id = Some obj;
    object_slots obj slot = Some cap; cap \<noteq> NullCap\<rbrakk>
  \<Longrightarrow> well_formed_cap cap"
  by (clarsimp simp: well_formed_cap_def example_spec_def example_tcb_def
                     object_slots_def empty_cap_map_def guard_bits_def
                     tcb_slot_defs tcb_pending_op_slot_def vm_read_write_def
              split: cdl_cap.splits split_if_asm)

lemma range_example_irq_node:
  "range example_irq_node = {x. x \<le> 0xFF}"
  apply (clarsimp simp: irq_cnodes_def example_spec_def example_irq_node_def)
  apply (subst ucast_range_less, simp+)
  apply (subst word_less_sub_le [where 'a = 32 and n=8, simplified])
  apply simp
  done

lemma irq_cnodes_example_spec [simp]:
  "irq_cnodes example_spec = set [0 .e. 255]"
  by (clarsimp simp: irq_cnodes_def range_example_irq_node)


lemma example_irq_node_less_255:
  "example_irq_node irq = obj_id \<Longrightarrow> obj_id \<le> 255"
  apply (insert range_example_irq_node)
  apply (auto simp: image_def)
  done

lemma well_formed_irqhandler_caps_example:
  "well_formed_irqhandler_caps example_spec"
  apply (clarsimp simp: well_formed_irqhandler_caps_def bound_irqs_def)
  apply (clarsimp simp: example_spec_def object_id_defs object_slots_def
                        empty_cap_map_def opt_cap_def slots_of_def opt_object_def
                        example_tcb_def is_irqhandler_cap_def
                 split: split_if_asm)
  apply (drule example_irq_node_less_255, simp)+
  done

lemma well_formed_cdt_example [simp]:
  "\<lbrakk>cdl_objects example_spec obj_id = Some obj;
    object_slots obj slot = Some cap; cap \<noteq> NullCap\<rbrakk>
  \<Longrightarrow> well_formed_cdt example_spec (obj_id, slot) cap"
  apply (clarsimp simp: well_formed_cdt_def real_cnode_at_def)
  apply (rule_tac x=cnode_id in exI)
  apply (fastforce simp: well_formed_cdt_def example_spec_def object_id_defs
                         object_slots_def object_at_def is_cnode_def
                         opt_cap_def slots_of_def opt_object_def
                         empty_cap_map_def real_cnode_at_def
                  split: split_if_asm)
  done

lemma well_formed_orig_cap_example [simp]:
  "\<lbrakk>cdl_objects example_spec obj_id = Some obj;
    object_slots obj slot = Some cap; cap \<noteq> NullCap\<rbrakk>
  \<Longrightarrow> well_formed_orig_cap cap"
  by (clarsimp simp: well_formed_orig_cap_def example_spec_def
                     object_slots_def example_tcb_def empty_cap_map_def
                     cap_type_def default_cap_def cap_rights_def
                     tcb_slot_defs tcb_pending_op_slot_def ep_related_cap_def
              split: split_if_asm)

lemma well_formed_cap_to_real_object_example [simp]:
  "\<lbrakk>cdl_objects example_spec obj_id = Some obj; object_slots obj slot = Some cap\<rbrakk>
   \<Longrightarrow> well_formed_cap_to_real_object example_spec cap"
  apply (clarsimp simp: well_formed_cap_to_real_object_def real_object_at_def)
  apply (clarsimp simp: example_spec_def object_id_defs empty_cap_map_def
                        object_slots_def example_tcb_def
                 split: split_if_asm)
  done

lemma well_formed_cap_types_match_example [simp]:
  "\<lbrakk>cdl_objects example_spec obj_id = Some obj; object_slots obj slot = Some cap; cap \<noteq> NullCap\<rbrakk>
  \<Longrightarrow> well_formed_cap_types_match example_spec cap"
  apply (clarsimp simp: well_formed_cap_types_match_def example_spec_def object_id_defs
              split: split_if_asm)
   apply (clarsimp simp: object_slots_def example_tcb_def object_id_defs
                  split: split_if_asm)
  apply (clarsimp simp: object_slots_def example_tcb_def object_id_defs
                 split: split_if_asm)
  done

lemma well_formed_caps_example [simp]:
  "cdl_objects example_spec obj_id = Some obj \<Longrightarrow>
   well_formed_caps example_spec obj_id obj"
   apply (clarsimp simp: well_formed_caps_def)
   apply (clarsimp simp: example_spec_def empty_cap_map_def object_slots_def example_tcb_def is_fake_vm_cap_def
                  split: split_if_asm)
  done

lemma well_formed_cap_to_object_example:
  "cdl_objects example_spec obj_id = Some obj
   \<Longrightarrow> well_formed_cap_to_object example_spec obj_id obj"
  apply (clarsimp simp: well_formed_cap_to_object_def real_cnode_at_def)
  apply (clarsimp simp: example_spec_def example_tcb_def)
  apply (intro conjI)
   apply (rule_tac x=cnode_id in exI)
  apply (fastforce simp: example_spec_def example_tcb_def object_id_defs
                         opt_cap_def slots_of_def object_slots_def
                         opt_parent_def object_at_def opt_object_def
                         is_cnode_def cap_object_def cap_has_object_def
                         real_object_at_def irq_cnodes_def
                         range_example_irq_node
                  split: split_if_asm)
  apply (clarsimp simp: cap_type_def split:cdl_cap.splits)
  apply (clarsimp simp: example_spec_def example_tcb_def object_id_defs
                        opt_cap_def slots_of_def object_slots_def
                        opt_parent_def object_at_def opt_object_def
                        is_cnode_def cap_object_def cap_has_object_def
                        cap_type_def cnode_cap_size_def
                        empty_cap_map_def object_size_bits_def
                 split: split_if_asm)
  done

lemma well_formed_cap_to_non_empty_pt_example:
  "cdl_objects example_spec obj_id = Some obj \<Longrightarrow>
    well_formed_cap_to_non_empty_pt example_spec obj_id obj"
  by (clarsimp simp: well_formed_cap_to_non_empty_pt_def example_spec_def
                     object_at_def is_pt_def
              split: split_if_asm)

lemma well_formed_vspace_example:
  "cdl_objects example_spec obj_id = Some obj
  \<Longrightarrow> well_formed_vspace example_spec obj_id obj"
  apply (clarsimp simp: well_formed_vspace_def well_formed_cap_to_non_empty_pt_example)
  apply (clarsimp simp: example_spec_def is_pt_def is_pd_def object_slots_def empty_cap_map_def
                 split: split_if_asm)
  done

lemma well_formed_irq_node_example:
  "cdl_objects example_spec obj_id = Some obj
  \<Longrightarrow> well_formed_irq_node example_spec obj_id obj"
  apply (clarsimp simp: well_formed_irq_node_def)
  apply (clarsimp simp: example_spec_def object_id_defs split: split_if_asm)
  done

lemma well_formed_irq_table_example [simp]:
  "well_formed_irq_table example_spec"
  by (clarsimp simp: well_formed_irq_table_def example_irq_node_def ucast_8_32_inj)

lemma well_formed_example:
  "well_formed example_spec"
  apply (clarsimp simp: well_formed_def)
  apply (intro conjI)
      apply (rule well_formed_orig_caps_unique_example)
     apply (rule well_formed_irqhandler_caps_unique_example)
    apply (rule well_formed_fake_pt_caps_unique_example)
   apply (rule well_formed_irqhandler_caps_example)
  apply (clarsimp split: option.splits, rename_tac obj)
  apply (clarsimp simp: well_formed_caps_example well_formed_cap_to_object_example
                        well_formed_orig_caps_unique_example)
  apply (rule conjI)
   apply (case_tac "obj_id = tcb_id")
    apply (cut_tac well_formed_tcb_example)
    apply (clarsimp simp: example_spec_def object_id_defs well_formed_tcb_def split: split_if_asm)
   apply (clarsimp simp: example_spec_def well_formed_tcb_def is_tcb_def split: split_if_asm)
  apply (rule conjI)
   apply (fact well_formed_vspace_example)
  apply (rule conjI)
   apply (fact well_formed_irq_node_example)
  apply (fastforce simp: example_spec_def object_size_bits_def object_default_state_def2
                         pd_size_def word_bits_def empty_cnode_def is_cnode_def
                         object_slots_def empty_cap_map_def tcb_slot_defs
                         default_tcb_def example_tcb_def tcb_pending_op_slot_def
                         small_frame_size_def object_at_def
                         real_cnode_at_def irq_cnodes_def range_example_irq_node
                  split: split_if_asm)
  done

end

