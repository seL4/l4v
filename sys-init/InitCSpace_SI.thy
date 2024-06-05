(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory InitCSpace_SI
imports
  "DSpecProofs.CNode_DP"
  ObjectInitialised_SI
  RootTask_SI
  SysInit_SI
  Mapped_Separating_Conjunction
begin

(****************************
 * Move me
 *****************************)

lemma sum_less:
  "\<lbrakk>(a::nat) \<le> a';  a' + b \<le> c\<rbrakk> \<Longrightarrow> a + b \<le> c"
  by auto

lemma mask_smaller:
   "((x::word32) && mask n) \<le> x"
   by (metis word_and_le2)

(* Not used by might be useful someday *)
lemma map_of_zip_is_Some2:
  "\<lbrakk>length xs = length ys; distinct xs\<rbrakk>
  \<Longrightarrow> (y \<in> set ys) = (\<exists>x. map_of (zip xs ys) x = Some y)"
  apply (subst ran_map_of_zip [symmetric, where xs=xs and ys=ys], simp+)
  apply (rule)
   apply (metis map_of_SomeD ranE)
  apply (clarsimp simp: ran_def)
  done

(* Not used by might be useful someday *)
lemma map_of_zip_is_Some2':
  "\<lbrakk>length xs \<le> length ys; distinct xs; map_of (zip xs ys) x = Some y\<rbrakk> \<Longrightarrow> y \<in> set ys"
  apply (subst (asm) zip_take_length[symmetric])
  apply (drule iffD2 [OF map_of_zip_is_Some2, rotated], fast)
  apply (clarsimp simp: min_def)
  by (rule in_set_takeD)

(*********************
 Moved to capDL somewhere.
 *)

lemma object_slot_spec2s:
  "object_slots obj slot = object_slots obj' slot
  \<Longrightarrow> object_slots (spec2s t obj) slot =
      object_slots (spec2s t obj') slot"
  apply (case_tac "has_slots obj")
   apply (case_tac "has_slots obj'")
   apply (clarsimp simp: spec2s_def)+
  apply (case_tac obj')
   apply (simp_all add:object_slots_def update_slots_def)
  done

lemma irqhandler_cap_cap_irq [simp]:
  "is_irqhandler_cap cap \<Longrightarrow> IrqHandlerCap (cap_irq cap) = cap"
  by (clarsimp simp: cap_type_def cap_irq_def split: cdl_cap.splits)

lemma InitThreadCNode_guard_equal[simp]:
  "guard_equal si_cspace_cap seL4_CapInitThreadCNode word_bits"
  apply (clarsimp simp:seL4_CapInitThreadCNode_def word_bits_def)
  apply (rule guard_equal_si_cspace_cap)
  apply (simp add:si_cnode_size_def)
  done

lemma default_cap_has_type:
  "cap_type cap = Some type
    \<Longrightarrow> cap_has_type (default_cap type ids sz dev)"
  by (fastforce simp: default_cap_def cap_type_def
              split: cdl_cap.splits)

lemma cap_has_type_update_cap_object[simp]:
  "cap_has_type (update_cap_object client_object_id spec_cap)
  = cap_has_type spec_cap"
  apply (case_tac spec_cap,
         (fastforce simp: cap_type_def update_cap_object_def)+)
  done

lemma ep_related_cap_badge_of_default:
  "\<lbrakk>ep_related_cap spec_cap; cap_type spec_cap = Some type\<rbrakk>
  \<Longrightarrow> cap_badge (default_cap type {client_object_id} sz dev) = 0"
  by (clarsimp simp: ep_related_cap_def cap_type_def
                     default_cap_def cap_badge_def safe_for_derive_def
              split: cdl_cap.splits)


lemma valid_src_cap_cnode_cap_size_le_32:
  "valid_src_cap spec_cap (cap_data spec_cap) \<Longrightarrow>
    cnode_cap_size spec_cap \<le> 32"
  apply (case_tac "is_cnode_cap spec_cap")
   apply (clarsimp simp: valid_src_cap_def word_bits_def)
  apply (clarsimp simp: cnode_cap_size_def split: cdl_cap.splits)
  done

lemma si_spec_irq_null_cap_at_si_spec_irq_cap_at_has_type:
  "\<lbrakk>opt_cap (obj_id, slot) spec = Some spec_cap; cap_type spec_cap = Some type; type \<noteq> IRQNodeType\<rbrakk>
  \<Longrightarrow> si_spec_irq_null_cap_at irq_caps spec obj_id slot
         = si_spec_irq_cap_at irq_caps spec obj_id slot"
  by (clarsimp simp: si_spec_irq_cap_at_def si_spec_irq_null_cap_at_def cap_at_def)

lemma cnode_at_not_tcb_at:
  "\<lbrakk>cnode_at obj_id spec \<rbrakk>\<Longrightarrow> \<not>tcb_at obj_id spec"
  apply (clarsimp simp: object_at_def is_cnode_def is_tcb_def)
  apply (case_tac object, simp_all)
  done

lemma guard_size_well_formed:
  "\<lbrakk>guard_size < guard_bits; (g::word32) < 2 ^ guard_size\<rbrakk> \<Longrightarrow>
    g < 2 ^ (size g - 8)"
  apply (frule (1) guard_less_guard_bits)
  apply (erule less_le_trans)
  apply (rule two_power_increasing)
   apply (clarsimp simp: word_bits_size word_bits_def guard_bits_def)
  apply (clarsimp simp: word_bits_size word_bits_def)
  done

lemma well_formed_cap_valid_src_cap:
  "well_formed_cap cap \<Longrightarrow> valid_src_cap cap (cap_data cap)"
  apply (clarsimp simp: valid_src_cap_def)
  apply (clarsimp simp: cap_data_def cnode_cap_size_def)
  apply (clarsimp simp: well_formed_cap_def cap_type_def guard_as_rawdata_def split: cdl_cap.splits)
  apply (rename_tac guard guard_size size_bits)
  apply (subst is_aligned_add_or [where n=8])
    apply (rule is_aligned_shift)
   apply (rule shiftl_less_t2n)
    apply (rule word_of_nat_less)
    apply (clarsimp simp: guard_bits_def)
   apply clarsimp
  apply (clarsimp simp: shiftr_over_or_dist)
  apply (subst shiftl_shiftr_id, simp+)
   apply (rule word_of_nat_less)
   apply (clarsimp simp: guard_bits_def)
  apply (subst shiftl_shiftr1, simp)
  apply clarsimp
  apply (subst less_mask_eq, erule (1) guard_size_well_formed)
  apply (subst word_ao_dist)
  apply (subst shiftl_mask_is_0, simp)
  apply (clarsimp simp: word_bits_size word_bits_def)
  apply (rule_tac a'="guard_size" in sum_less)
   apply (cut_tac x="of_nat guard_size" and n=5 in mask_smaller)
   apply (erule word_unat_less_le)
  apply simp
  done

lemma well_formed_cap_has_object_has_type [simp]:
  "\<lbrakk>well_formed_cap cap; cap_has_object cap\<rbrakk> \<Longrightarrow> cap_has_type cap"
  by (clarsimp simp: cap_has_object_def well_formed_cap_def cap_type_def
              split: cdl_cap.splits)

(* Needed? *)
lemma si_spec_irq_cap_at_empty_cap_has_object:
  "cap_at cap_has_object (obj_id, slot) spec
  \<Longrightarrow> si_spec_irq_cap_at irq_caps spec obj_id slot = \<box>"
  by (clarsimp simp: si_spec_irq_cap_at_def cap_at_def)

(* Needed? *)
lemma si_obj_cap_at_empty_cap_has_object:
  "irqhandler_cap_at (obj_id, slot) spec
  \<Longrightarrow> si_obj_cap_at t orig_caps spec False obj_id slot = \<box>"
  by (clarsimp simp: si_obj_cap_at_def cap_at_def)

(* MOVEME *)
lemma well_formed_cap_no_object_irqhandler_cap:
  "\<lbrakk>well_formed spec; opt_cap (obj_id, slot) spec = Some cap; cap \<noteq> NullCap;
    \<not> cap_at cap_has_object (obj_id, slot) spec\<rbrakk>
   \<Longrightarrow> cap_at is_irqhandler_cap (obj_id, slot) spec"
  apply (clarsimp simp: cap_at_def)
  apply (frule opt_cap_cdl_objects, clarsimp)
  apply (frule (1) object_slots_opt_capI)
  apply (drule (3) well_formed_well_formed_cap)
  apply (clarsimp simp: well_formed_cap_def cap_has_object_def
                 split: cdl_cap.splits)
  done

(**********************************************************************
 * Helper lemmas about CNodes, and when they are halfway initialised. *
 **********************************************************************)

lemma valid_src_cap_if_cnode:
  "\<lbrakk>cap_type spec_cap = Some type;
    is_cnode_cap spec_cap \<longrightarrow> sz = cnode_cap_size spec_cap;
    valid_src_cap spec_cap data\<rbrakk>
  \<Longrightarrow> valid_src_cap (default_cap type {client_object_id} sz dev) data"
  apply (clarsimp simp: valid_src_cap_def)
  apply (clarsimp simp: cnode_cap_size_def cap_type_def default_cap_def)
  done

lemma default_cap_data_if_cnode:
  "\<lbrakk>cap_type spec_cap = Some type;
    is_cnode_cap spec_cap \<longrightarrow> sz = cnode_cap_size spec_cap\<rbrakk>
  \<Longrightarrow> (default_cap type m sz dev)
   =  (default_cap type m (cnode_cap_size spec_cap) dev)"
  by (case_tac spec_cap,
      (clarsimp simp: default_cap_def cap_type_def is_cnode_cap_simps)+)


(************************************************************
 * A CNode slot that is half done is either done, or empty. *
 ************************************************************)



lemma object_slots_cnode_half:
  "\<lbrakk>\<not>original_cap_at (obj_id, slot) spec\<rbrakk>
  \<Longrightarrow> object_slots (cnode_half spec obj_id obj) slot =
      object_slots obj slot"
  apply (case_tac "has_slots obj")
   apply (clarsimp simp: cnode_half_def restrict_map_def)
  apply (clarsimp simp: cnode_half_def)
  done

lemma cnode_slot_half_initialised_not_original_slot:
  "\<not>original_cap_at (obj_id, slot) spec
  \<Longrightarrow> cnode_slot_half_initialised spec t obj_id slot
    = object_slot_initialised spec t obj_id slot"
  apply (clarsimp simp: cnode_slot_half_initialised_def object_slot_initialised_def)
  apply (clarsimp simp: object_initialised_general_def)
  apply (rule ext, rule iffI)
   apply (clarsimp simp: sep_map_s_def sep_map_general_def)
   apply (rule ext)
   apply (clarsimp simp: object_to_sep_state_def object_project_def
                         object_slots_object_clean
                  split: option.splits)
   apply (cut_tac obj = "cnode_half spec obj_id spec_object" and
                 obj' = spec_object and slot=slot and t=t in object_slot_spec2s)
    apply (erule object_slots_cnode_half)
   apply clarsimp
  apply (clarsimp simp: sep_map_s_def sep_map_general_def)
  apply (rule ext)
  apply (clarsimp simp: object_to_sep_state_def object_project_def
                        object_slots_object_clean
                 split: option.splits)
  apply (cut_tac obj = "cnode_half spec obj_id spec_object" and
                obj' = spec_object and slot=slot and t=t in object_slot_spec2s)
   apply (erule object_slots_cnode_half)
  apply clarsimp
  done

lemma slots_empty_cnode1:
  "slot < 2 ^ sz
  \<Longrightarrow> object_slots (CNode (empty_cnode sz)) slot = Some NullCap"
  by (fastforce simp: object_slots_def empty_cnode_def empty_cap_map_def
                      restrict_map_def cdl_cnode.splits)

lemma slots_empty_cnode2:
  "\<not> slot < 2 ^ sz
  \<Longrightarrow> object_slots (CNode (empty_cnode sz)) slot = None"
  by (fastforce simp: object_slots_def empty_cnode_def empty_cap_map_def
                      restrict_map_def cdl_cnode.splits)

lemma slots_spec2s_cnode_half1:
  "\<lbrakk>slot < 2 ^ sz; original_cap_at (obj_id, slot) spec; (cdl_cnode_caps cnode slot) \<noteq> None\<rbrakk>
  \<Longrightarrow> object_slots (spec2s t (cnode_half spec obj_id (CNode cnode))) slot
      = Some NullCap"
  by (fastforce simp: object_slots_def cnode_half_def spec2s_def update_slots_def)

lemma slots_spec2s_cnode_half2:
  "\<lbrakk>\<not> slot < 2 ^ sz; original_cap_at (obj_id, slot) spec; (cdl_cnode_caps cnode slot) = None\<rbrakk>
  \<Longrightarrow> object_slots (spec2s t (cnode_half spec obj_id (CNode cnode))) slot
      = None"
  by (fastforce simp: object_slots_def cnode_half_def spec2s_def update_slots_def
                      restrict_map_def)

lemma object_slots_spec2s_cnode_half_object_default_state:
  "\<lbrakk>well_formed spec; original_cap_at (obj_id, slot) spec;
    cdl_objects spec obj_id = Some spec_object; is_cnode spec_object\<rbrakk>
  \<Longrightarrow> object_slots (spec2s t (cnode_half spec obj_id spec_object)) slot =
      object_slots (object_default_state spec_object) slot"
  apply (clarsimp simp: well_formed_def)
  apply (erule_tac x=obj_id in allE)
  apply (clarsimp split: option.splits)
  apply (clarsimp simp: object_default_state_def2 is_cnode_def
                 split: cdl_object.splits)
  apply (rename_tac cnode)
  apply (case_tac "slot < 2 ^ cdl_cnode_size_bits cnode")
   apply (frule slots_empty_cnode1)
   apply (frule_tac cnode=cnode and t=t in slots_spec2s_cnode_half1, assumption)
    apply (clarsimp simp: object_slots_def dom_def empty_cnode_def empty_cap_map_def)
    apply fastforce
   apply (clarsimp simp: update_slots_def empty_cnode_def spec2s_def cnode_half_def)
  apply (frule slots_empty_cnode2)
  apply (frule_tac cnode=cnode and t=t in slots_spec2s_cnode_half2, assumption)
   apply (fastforce simp: object_slots_def dom_def empty_cnode_def empty_cap_map_def)
  apply clarsimp
  done

lemma cnode_slot_half_initialised_original_slot:
  "\<lbrakk>well_formed spec; original_cap_at (obj_id, slot) spec; cnode_at obj_id spec\<rbrakk>
  \<Longrightarrow> cnode_slot_half_initialised spec t obj_id slot
    = object_slot_empty spec t obj_id slot"
  apply (clarsimp simp: object_at_def)
  apply (frule (1) well_formed_object_slots)
  apply (clarsimp simp: cnode_slot_half_initialised_def object_slot_empty_def)
  apply (clarsimp simp: object_initialised_general_def)
  apply (rule ext, rule iffI)
   apply (clarsimp simp: sep_map_s_def sep_map_general_def)
   apply (rule ext, clarsimp simp:object_to_sep_state_def
     object_project_def object_slots_object_clean)
   apply (subst object_slots_spec2s_cnode_half_object_default_state)
    apply simp+
    apply (clarsimp simp: object_at_def)+
  apply (clarsimp simp: sep_map_s_def sep_map_general_def)
  apply (rule ext)
  apply (clarsimp simp:object_to_sep_state_def object_project_def object_slots_object_clean)
  apply (subst object_slots_spec2s_cnode_half_object_default_state, simp+)
  apply (clarsimp split: option.splits)
  done

(**************************
 **************************
 * init_cspace proof  *
 **************************
 **************************)

lemma default_cap_cnode_dev:
  "default_cap CNodeType a b dev = CNodeCap (pick a) 0 0 b"
  by (simp add:default_cap_def)

lemma mint_pre:
  "\<lbrakk>well_formed spec; cnode_at obj_id spec;
    cdl_objects spec obj_id = Some spec_obj;
    opt_cap (obj_id, slot) spec = Some spec_cap;
    spec_cap \<noteq> NullCap;
    cap_has_object spec_cap;
    cap_type spec_cap = Some type;
    is_device_cap spec_cap = dev;
    data = cap_badge spec_cap;

   Some dest_root = dup_caps obj_id;
   dest_index = of_nat slot;
   (dest_depth::word32) = of_nat (object_size_bits spec_obj);

   src_root = seL4_CapInitThreadCNode;
   Some src_index = orig_caps (cap_object spec_cap);
   src_index < 2 ^ si_cnode_size;
   src_depth = (32::word32);

   rights = cap_rights spec_cap;

   \<guillemotleft>object_slot_empty spec t obj_id slot \<and>*
    si_cap_at t orig_caps spec dev (cap_object spec_cap) \<and>*
    si_cap_at t dup_caps spec dev obj_id \<and>*
    object_fields_empty spec t obj_id \<and>* si_objects \<and>* R\<guillemotright> s;

   cdl_objects spec (cap_object spec_cap) = Some spec_cap_object;

   dest_root_slot = offset dest_root si_cnode_size;
   cnode_cap_slot = offset src_root si_cnode_size;
   src_slot = offset src_index si_cnode_size;
   t obj_id = Some dest_id;
   default_cap CNodeType {dest_id} dest_size False = dest_root_cap;

   object_size_bits spec_obj = dest_size;
   dest_slot = offset dest_index dest_size;
   t (cap_object spec_cap) = Some client_object_id;
   default_cap type {client_object_id} (object_size_bits spec_cap_object)  = src_cap\<rbrakk>
 \<Longrightarrow>
    \<guillemotleft>si_tcb_id \<mapsto>f root_tcb \<and>*
     (si_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*

     \<comment> \<open>Root CNode.\<close>
     si_cnode_id \<mapsto>f CNode (empty_cnode si_cnode_size) \<and>*
     \<comment> \<open>Client cnode.\<close>
     dest_id \<mapsto>f CNode (empty_cnode dest_size) \<and>*

     \<comment> \<open>Cap to the root CNode.\<close>
     (si_tcb_id, tcb_cspace_slot) \<mapsto>c si_cspace_cap \<and>*
     \<comment> \<open>Cap to the client CNode.\<close>
     (si_cnode_id, dest_root_slot) \<mapsto>c dest_root_cap \<and>*
     \<comment> \<open>Cap that the root task has to its own CNode.\<close>
     (si_cnode_id, cnode_cap_slot) \<mapsto>c si_cnode_cap \<and>*
     \<comment> \<open>Cap to be copied, in the root CNode.\<close>
     (si_cnode_id, src_slot) \<mapsto>c src_cap dev \<and>*
     \<comment> \<open>Where to copy the cap (in the client CNode).\<close>
     (dest_id, dest_slot) \<mapsto>c NullCap \<and>*
     \<comment> \<open>IRQ control cap\<close>
     (si_cnode_id, unat seL4_CapIRQControl) \<mapsto>c IrqControlCap \<and>*
     \<comment> \<open>ASID caps.\<close>
     si_asid \<and>*
      R\<guillemotright> s \<and>

     \<comment> \<open>Cap slots match their cptrs.\<close>
     one_lvl_lookup si_cspace_cap 32 si_cnode_size \<and>
     one_lvl_lookup si_cspace_cap 32 si_cnode_size \<and>
     one_lvl_lookup si_cspace_cap (unat src_depth) si_cnode_size \<and>
     one_lvl_lookup dest_root_cap (unat dest_depth) dest_size \<and>

     unat src_depth \<le> word_bits \<and>
     0 < unat src_depth \<and>
     unat dest_depth \<le> word_bits \<and>
     0 < unat dest_depth \<and>
     is_tcb root_tcb \<and>
     is_cnode_cap dest_root_cap \<and>
     is_cnode_cap si_cspace_cap \<and>
     guard_equal si_cspace_cap src_index (unat src_depth) \<and>
     guard_equal dest_root_cap dest_index (unat dest_depth) \<and>

     Some dest_root = dup_caps obj_id \<and>
     Some src_index = orig_caps (cap_object spec_cap)"
  apply clarsimp
  apply (frule (3) well_formed_types_match)
  apply (frule (3) well_formed_slot_object_size_bits)
  apply (frule (2) well_formed_cnode_object_size_bits)
  apply (clarsimp simp: object_slot_empty_def object_fields_empty_def object_initialised_general_def)
  apply (clarsimp simp: si_objects_def)
  apply (clarsimp simp: sep_conj_exists sep_conj_assoc)
  apply (clarsimp simp: si_cap_at_def sep_conj_assoc sep_conj_exists)
  apply (clarsimp simp: object_at_def)
  apply (clarsimp simp: object_type_is_object)
  apply (rule conjI)
   apply (sep_drule sep_map_c_sep_map_s)
    apply (erule object_slots_object_default_state_NullCap [where obj_id=obj_id])
      apply (fastforce simp: object_at_def object_type_is_object)
     apply assumption
    apply assumption
   apply (subst offset_slot, assumption, simp)
   apply (subst offset_slot', assumption)
   apply (subst offset_slot', assumption)
   apply (subst empty_cnode_object_size_bits, simp add: object_type_is_object)
   apply (frule (1) well_formed_object_size_bits)
   apply (cut_tac obj_id=dest_id and obj'=spec_obj in
                  sep_map_f_object_size_bits_cnode, (simp add: object_type_is_object)+)
   apply (simp add: default_cap_cnode_dev)
   apply (sep_solve add: sep_any_imp )
  apply (clarsimp simp: one_lvl_lookup_def)
  apply (drule guard_equal_si_cspace_cap)
  apply (clarsimp simp: default_cap_def object_type_is_object)
  apply (cut_tac x="object_size_bits spec_obj" in unat_of_nat32)
   apply (insert n_less_equal_power_2 [where n=word_bits])
   apply (frule (1) well_formed_object_size_bits_word_bits)
   apply (metis lt_word_bits_lt_pow)
  apply (frule (1) well_formed_object_size_bits_word_bits)
  apply (drule guard_equal_si_cspace_cap)+
  apply clarsimp
  apply (clarsimp simp: word_bits_def guard_equal_def Let_unfold)
  apply (drule (1) well_formed_object_size_bits_word_bits)
  apply (simp add: word_bits_def)
  done



lemma move_pre_irq_handler:
  "\<lbrakk>well_formed spec; cnode_at obj_id spec;
   cdl_objects spec obj_id = Some spec_obj;
   opt_cap (obj_id, slot) spec = Some spec_cap;
   is_irqhandler_cap spec_cap;

   Some dest_root = dup_caps obj_id;
   dest_index = of_nat slot;
   (dest_depth::word32) = of_nat (object_size_bits spec_obj);

   src_root = seL4_CapInitThreadCNode;
   Some src_index = irq_caps (cap_irq spec_cap);
   src_index < 2 ^ si_cnode_size;
   src_depth = (32::word32);

   rights = cap_rights spec_cap;

   \<guillemotleft>object_slot_empty spec t obj_id slot \<and>*
    si_irq_cap_at irq_caps spec (cap_irq spec_cap) \<and>*
    si_cap_at t dup_caps spec False obj_id \<and>*
    object_fields_empty spec t obj_id \<and>* si_objects \<and>* R\<guillemotright> s;

   dest_root_slot = offset dest_root si_cnode_size;
   cnode_cap_slot = offset src_root si_cnode_size;
   src_slot = offset src_index si_cnode_size;
   t obj_id = Some dest_id;
   default_cap CNodeType {dest_id} dest_size False = dest_root_cap;

   object_size_bits spec_obj = dest_size;
   dest_slot = offset dest_index dest_size\<rbrakk>
 \<Longrightarrow>
    \<guillemotleft>si_tcb_id \<mapsto>f root_tcb \<and>*
     (si_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*

     \<comment> \<open>Root CNode.\<close>
     si_cnode_id \<mapsto>f CNode (empty_cnode si_cnode_size) \<and>*
     \<comment> \<open>Client cnode.\<close>
     dest_id \<mapsto>f CNode (empty_cnode dest_size) \<and>*

     \<comment> \<open>Cap to the root CNode.\<close>
     (si_tcb_id, tcb_cspace_slot) \<mapsto>c si_cspace_cap \<and>*
     \<comment> \<open>Cap to the client CNode.\<close>
     (si_cnode_id, dest_root_slot) \<mapsto>c dest_root_cap \<and>*
     \<comment> \<open>Cap that the root task has to its own CNode.\<close>
     (si_cnode_id, cnode_cap_slot) \<mapsto>c si_cnode_cap \<and>*
     \<comment> \<open>Cap to be copied, in the root CNode.\<close>
     (si_cnode_id, src_slot) \<mapsto>c spec_cap \<and>*
     \<comment> \<open>Where to copy the cap (in the client CNode).\<close>
     (dest_id, dest_slot) \<mapsto>c NullCap \<and>*
     \<comment> \<open>IRQ control cap\<close>
     (si_cnode_id, unat seL4_CapIRQControl) \<mapsto>c IrqControlCap \<and>*
     \<comment> \<open>ASID caps.\<close>
     si_asid \<and>*
      R\<guillemotright> s \<and>

     \<comment> \<open>Cap slots match their cptrs.\<close>
     one_lvl_lookup si_cspace_cap 32 si_cnode_size \<and>
     one_lvl_lookup si_cspace_cap 32 si_cnode_size \<and>
     one_lvl_lookup si_cspace_cap (unat src_depth) si_cnode_size \<and>
     one_lvl_lookup dest_root_cap (unat dest_depth) dest_size \<and>

     unat src_depth \<le> word_bits \<and>
     0 < unat src_depth \<and>
     unat dest_depth \<le> word_bits \<and>
     0 < unat dest_depth \<and>
     is_tcb root_tcb \<and>
     is_cnode_cap dest_root_cap \<and>
     is_cnode_cap si_cspace_cap \<and>
     guard_equal si_cspace_cap src_index (unat src_depth) \<and>
     guard_equal dest_root_cap dest_index (unat dest_depth) \<and>

     Some dest_root = dup_caps obj_id \<and>
     Some src_index = irq_caps (cap_irq spec_cap)"
  apply clarsimp
  apply (frule (3) well_formed_slot_object_size_bits)
  apply (frule (2) well_formed_cnode_object_size_bits)
  apply (clarsimp simp: object_slot_empty_def object_fields_empty_def object_initialised_general_def)
  apply (clarsimp simp: si_objects_def)
  apply (clarsimp simp: sep_conj_exists sep_conj_assoc)
  apply (clarsimp simp: si_cap_at_def si_irq_cap_at_def sep_conj_assoc sep_conj_exists)
  apply (clarsimp simp: object_at_def)
  apply (clarsimp simp: object_type_is_object)
  apply (rule conjI)
   apply (sep_drule sep_map_c_sep_map_s)
    apply (erule object_slots_object_default_state_NullCap [where obj_id=obj_id])
      apply (fastforce simp: object_at_def object_type_is_object)
     apply assumption
    apply assumption
   apply (simp add:default_cap_cnode_dev)
   apply (subst offset_slot, assumption, simp)
   apply (subst offset_slot', assumption)
   apply (subst offset_slot', assumption)
   apply (subst empty_cnode_object_size_bits, simp add: object_type_is_object)
   apply (frule (1) well_formed_object_size_bits)
   apply (cut_tac obj_id=dest_id and obj'=spec_obj in
                  sep_map_f_object_size_bits_cnode, (simp add: object_type_is_object)+)
   apply sep_solve
  apply (clarsimp simp: one_lvl_lookup_def)
  apply (drule guard_equal_si_cspace_cap)
  apply (clarsimp simp: default_cap_def object_type_is_object)
  apply (cut_tac x="object_size_bits spec_obj" in unat_of_nat32)
   apply (insert n_less_equal_power_2 [where n=word_bits])
   apply (frule (1) well_formed_object_size_bits_word_bits)
   apply (metis lt_word_bits_lt_pow)
  apply (frule (1) well_formed_object_size_bits_word_bits)
  apply (drule guard_equal_si_cspace_cap)+
  apply clarsimp
  apply (clarsimp simp: word_bits_def guard_equal_def Let_unfold)
  apply (drule (1) well_formed_object_size_bits_word_bits)
  apply (simp add: word_bits_def)
  done

lemma mint_post:
  "\<lbrakk>well_formed spec;
    t obj_id = Some dest_id;
    cdl_objects spec obj_id = Some spec_obj;
    opt_cap (obj_id, slot) spec = Some spec_cap;
    cap_has_object spec_cap;
    cap_type spec_cap = Some type;
    is_device_cap spec_cap = dev;
    dup_caps obj_id = Some dest_root;
    orig_caps (cap_object spec_cap) = Some src_index;
    cdl_objects spec (cap_object spec_cap) = Some spec_cap_object;
    t (cap_object spec_cap) = Some client_object_id;
    data = cap_data spec_cap;
    cnode_at obj_id spec;
    src_index < 2 ^ si_cnode_size;
    dest_root < 2 ^ si_cnode_size;

    \<comment> \<open>Remove me.\<close>
    \<not> is_untyped_cap spec_cap;
    spec_cap \<noteq> NullCap;

   \<guillemotleft>si_tcb_id \<mapsto>f root_tcb \<and>*
    si_cnode_id \<mapsto>f CNode (empty_cnode si_cnode_size) \<and>*
    dest_id \<mapsto>f CNode (empty_cnode (object_size_bits spec_obj)) \<and>*
   (si_tcb_id, tcb_cspace_slot) \<mapsto>c si_cspace_cap \<and>*
   (si_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
   (si_cnode_id, offset dest_root si_cnode_size) \<mapsto>c default_cap CNodeType {dest_id} (object_size_bits spec_obj) False \<and>*
   (si_cnode_id, offset seL4_CapInitThreadCNode si_cnode_size) \<mapsto>c si_cnode_cap \<and>*
   (si_cnode_id, offset src_index si_cnode_size) \<mapsto>c default_cap type {client_object_id} (object_size_bits spec_cap_object) dev \<and>*
   (dest_id, offset (of_nat slot) (object_size_bits spec_obj)) \<mapsto>c
       derived_cap (update_cap_data_det data
                   (update_cap_rights (cap_rights (default_cap type {client_object_id} (object_size_bits spec_cap_object) dev) \<inter> cap_rights spec_cap)
                   (default_cap type {client_object_id} (cnode_cap_size spec_cap) (is_device_cap spec_cap)))) \<and>*
   (si_cnode_id, unat seL4_CapIRQControl) \<mapsto>c IrqControlCap \<and>*
    si_asid \<and>* R\<guillemotright> s\<rbrakk>
   \<Longrightarrow>
   \<guillemotleft>object_slot_initialised spec t obj_id slot \<and>*
    si_cap_at t orig_caps spec dev (cap_object spec_cap) \<and>*
    si_cap_at t dup_caps spec dev obj_id \<and>*
    object_fields_empty spec t obj_id \<and>* si_objects \<and>* R\<guillemotright> s"
  apply (frule (3) well_formed_types_match)
  apply (frule (3) well_formed_slot_object_size_bits)
  apply (frule (1) well_formed_object_slots, simp)
  apply (clarsimp simp: object_slot_initialised_def object_fields_empty_def object_initialised_general_def)
  apply (clarsimp simp: si_objects_def)
  apply (clarsimp simp: sep_conj_exists sep_conj_assoc)
  apply (clarsimp simp: si_cap_at_def sep_conj_assoc sep_conj_exists)
  apply (clarsimp simp: object_at_def object_type_is_object)
  apply (frule_tac obj_id=dest_id in empty_cnode_object_size_bits, clarsimp)
  apply (cut_tac slot=slot in offset_slot, assumption, simp, simp)
  apply (subst sep_map_s_sep_map_c_eq [where cap="update_cap_object client_object_id spec_cap"])
   apply (rule object_slots_spec2s, (clarsimp simp: opt_cap_def slots_of_def)+)
  apply (frule (2) well_formed_well_formed_cap, clarsimp simp: cap_has_object_def)
  apply (frule (2) well_formed_vm_cap_has_asid)
  apply (frule (1) well_formed_is_fake_vm_cap,
         (assumption|simp add: object_type_is_object)+)
  apply (clarsimp simp: cap_rights_inter_default_cap_rights)
  apply (subst (asm) update_cap_rights_and_data,(assumption|clarsimp)+)
  apply (subst (asm) offset_slot', assumption)+
  apply (clarsimp simp: default_cap_cnode_dev)
  apply sep_solve
  done

lemma mutate_post:
  "\<lbrakk>well_formed spec; original_cap_at (obj_id, slot) spec;
    t obj_id = Some dest_id;
    cdl_objects spec obj_id = Some spec_obj;
    opt_cap (obj_id, slot) spec = Some spec_cap;
    cap_has_object spec_cap;
    cap_type spec_cap = Some type;
    is_device_cap spec_cap = dev;
    dup_caps obj_id = Some dest_root;
    orig_caps (cap_object spec_cap) = Some src_index;
    cdl_objects spec (cap_object spec_cap) = Some spec_cap_object;
    t (cap_object spec_cap) = Some client_object_id;
    data = cap_data spec_cap;
    cnode_at obj_id spec;
    src_index < 2 ^ si_cnode_size;
    dest_root < 2 ^ si_cnode_size;

    \<not> is_untyped_cap spec_cap;
    spec_cap \<noteq> NullCap;
   \<guillemotleft>si_tcb_id \<mapsto>f root_tcb \<and>*
    si_cnode_id \<mapsto>f CNode (empty_cnode si_cnode_size) \<and>*
    dest_id \<mapsto>f CNode (empty_cnode (object_size_bits spec_obj)) \<and>*
   (si_tcb_id, tcb_cspace_slot) \<mapsto>c si_cspace_cap \<and>*
   (si_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
   (si_cnode_id, offset dest_root si_cnode_size) \<mapsto>c default_cap CNodeType {dest_id} (object_size_bits spec_obj) False \<and>*
   (si_cnode_id, offset seL4_CapInitThreadCNode si_cnode_size) \<mapsto>c si_cnode_cap \<and>*
   (si_cnode_id, offset src_index si_cnode_size) \<mapsto>c NullCap \<and>*
   (dest_id, offset (of_nat slot) (object_size_bits spec_obj)) \<mapsto>c
     update_cap_data_det data (default_cap type {client_object_id} (cnode_cap_size spec_cap) dev) \<and>*
   (si_cnode_id, unat seL4_CapIRQControl) \<mapsto>c IrqControlCap \<and>*
    si_asid \<and>* R\<guillemotright> s\<rbrakk>
   \<Longrightarrow>
   \<guillemotleft>object_slot_initialised spec t obj_id slot \<and>*
    si_null_cap_at t orig_caps spec (cap_object spec_cap) \<and>*
    si_cap_at t dup_caps spec dev obj_id \<and>*
    object_fields_empty spec t obj_id \<and>* si_objects \<and>* R\<guillemotright> s"
  apply (frule (3) well_formed_types_match)
  apply (frule (3) well_formed_slot_object_size_bits)
  apply (frule (1) well_formed_object_slots, simp)
  apply (clarsimp simp: object_slot_initialised_def object_fields_empty_def object_initialised_general_def)
  apply (clarsimp simp: si_objects_def)
  apply (clarsimp simp: sep_conj_exists sep_conj_assoc)
  apply (clarsimp simp: si_null_cap_at_def si_cap_at_def sep_conj_assoc sep_conj_exists)
  apply (clarsimp simp: object_at_def object_type_is_object)
  apply (frule_tac obj_id=dest_id in empty_cnode_object_size_bits, clarsimp)
  apply (cut_tac slot=slot in offset_slot, assumption, simp, simp)
  apply (subst sep_map_s_sep_map_c_eq [where cap="update_cap_object client_object_id spec_cap"])
   apply (rule object_slots_spec2s, (clarsimp simp: opt_cap_def slots_of_def)+)
  apply (frule (2) well_formed_well_formed_cap, clarsimp simp: cap_has_object_def)
  apply (frule (2) well_formed_vm_cap_has_asid)
  apply (frule (1) well_formed_is_fake_vm_cap,
         (assumption|simp add: object_type_is_object)+)
  apply (subst update_cap_data [symmetric], simp+)
    apply (clarsimp simp: cap_has_object_not_irqhandler_cap)
   apply (erule well_formed_orig_caps, (simp add: slots_of_def)+)
  apply (subst (asm) offset_slot', assumption)+
  apply (clarsimp simp: default_cap_cnode_dev)
  apply sep_solve
  done

lemma move_post:
  "\<lbrakk>well_formed spec; original_cap_at (obj_id, slot) spec;
    t obj_id = Some dest_id;
    cdl_objects spec obj_id = Some spec_obj;
    opt_cap (obj_id, slot) spec = Some spec_cap;
    dup_caps obj_id = Some dest_root;
    orig_caps (cap_object spec_cap) = Some src_index;
    cdl_objects spec (cap_object spec_cap) = Some spec_cap_object;
    t (cap_object spec_cap) = Some client_object_id;
    cap_has_object spec_cap;
    data = cap_data spec_cap;
    spec_cap \<noteq> NullCap;
    cnode_at obj_id spec;
    src_index < 2 ^ si_cnode_size;
    dest_root < 2 ^ si_cnode_size;
    \<not> is_untyped_cap spec_cap;
   \<guillemotleft>si_tcb_id \<mapsto>f root_tcb \<and>*
    si_cnode_id \<mapsto>f CNode (empty_cnode si_cnode_size) \<and>*
    dest_id \<mapsto>f CNode (empty_cnode (object_size_bits spec_obj)) \<and>*
   (si_tcb_id, tcb_cspace_slot) \<mapsto>c si_cspace_cap \<and>*
   (si_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
   (si_cnode_id, offset dest_root si_cnode_size) \<mapsto>c default_cap CNodeType {dest_id} (object_size_bits spec_obj) False \<and>*
   (si_cnode_id, offset seL4_CapInitThreadCNode si_cnode_size) \<mapsto>c si_cnode_cap \<and>*
   (si_cnode_id, offset src_index si_cnode_size) \<mapsto>c NullCap \<and>*
   (dest_id, offset (of_nat slot) (object_size_bits spec_obj)) \<mapsto>c
     update_cap_object client_object_id spec_cap \<and>*
   (si_cnode_id, unat seL4_CapIRQControl) \<mapsto>c IrqControlCap \<and>*
    si_asid \<and>* R\<guillemotright> s\<rbrakk>
   \<Longrightarrow>
   \<guillemotleft>object_slot_initialised spec t obj_id slot \<and>*
    si_null_cap_at t orig_caps spec (cap_object spec_cap) \<and>*
    si_cap_at t dup_caps spec dev obj_id \<and>*
    object_fields_empty spec t obj_id \<and>* si_objects \<and>* R\<guillemotright> s"
  apply (frule (3) well_formed_types_match)
  apply (frule (3) well_formed_slot_object_size_bits)
  apply (frule (1) well_formed_object_slots, simp)
  apply (clarsimp simp: object_slot_initialised_def object_fields_empty_def object_initialised_general_def)
  apply (clarsimp simp: si_objects_def)
  apply (clarsimp simp: sep_conj_exists sep_conj_assoc)
  apply (clarsimp simp: si_null_cap_at_def si_cap_at_def sep_conj_assoc sep_conj_exists)
  apply (clarsimp simp: object_at_def object_type_is_object)
  apply (frule_tac obj_id=dest_id in empty_cnode_object_size_bits, clarsimp)
  apply (cut_tac slot=slot in offset_slot, assumption, simp, simp)
  apply (subst sep_map_s_sep_map_c_eq [where cap="update_cap_object client_object_id spec_cap"])
   apply (rule object_slots_spec2s, (clarsimp simp: opt_cap_def slots_of_def)+)
  apply (subst (asm) offset_slot', assumption)+
  apply (clarsimp simp: default_cap_cnode_dev)
  apply sep_solve
  done

lemma move_post_irq_handler:
  "\<lbrakk>well_formed spec;
    t obj_id = Some dest_id;
    cdl_objects spec obj_id = Some spec_obj;
    opt_cap (obj_id, slot) spec = Some spec_cap;
    dup_caps obj_id = Some dest_root;
    irq_caps (cap_irq spec_cap) = Some src_index;
    is_irqhandler_cap spec_cap;
    cnode_at obj_id spec;
    src_index < 2 ^ si_cnode_size;
    dest_root < 2 ^ si_cnode_size;

   \<guillemotleft>si_tcb_id \<mapsto>f root_tcb \<and>*
    si_cnode_id \<mapsto>f CNode (empty_cnode si_cnode_size) \<and>*
    dest_id \<mapsto>f CNode (empty_cnode (object_size_bits spec_obj)) \<and>*
   (si_tcb_id, tcb_cspace_slot) \<mapsto>c si_cspace_cap \<and>*
   (si_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
   (si_cnode_id, offset dest_root si_cnode_size) \<mapsto>c default_cap CNodeType {dest_id} (object_size_bits spec_obj) False \<and>*
   (si_cnode_id, offset seL4_CapInitThreadCNode si_cnode_size) \<mapsto>c si_cnode_cap \<and>*
   (si_cnode_id, offset src_index si_cnode_size) \<mapsto>c NullCap \<and>*
   (dest_id, offset (of_nat slot) (object_size_bits spec_obj)) \<mapsto>c spec_cap \<and>*
   (si_cnode_id, unat seL4_CapIRQControl) \<mapsto>c IrqControlCap \<and>*
    si_asid \<and>* R\<guillemotright> s\<rbrakk>
   \<Longrightarrow>
   \<guillemotleft>object_slot_initialised spec t obj_id slot \<and>*
    si_null_irq_cap_at irq_caps spec (cap_irq spec_cap) \<and>*
    si_cap_at t dup_caps spec dev obj_id \<and>*
    object_fields_empty spec t obj_id \<and>* si_objects \<and>* R\<guillemotright> s"
  apply (frule (3) well_formed_slot_object_size_bits)
  apply (frule (1) well_formed_object_slots, simp)
  apply (clarsimp simp: object_slot_initialised_def object_fields_empty_def object_initialised_general_def)
  apply (clarsimp simp: si_objects_def)
  apply (clarsimp simp: sep_conj_exists sep_conj_assoc)
  apply (clarsimp simp: si_null_cap_at_def si_cap_at_def si_null_irq_cap_at_def
                        sep_conj_assoc sep_conj_exists)
  apply (clarsimp simp: object_at_def object_type_is_object)
  apply (frule_tac obj_id=dest_id in empty_cnode_object_size_bits, clarsimp)
  apply (cut_tac slot=slot in offset_slot, assumption, simp, simp)
  apply (subst sep_map_s_sep_map_c_eq [where cap=spec_cap],
         (clarsimp simp: opt_cap_def slots_of_def)+)
  apply (subst (asm) offset_slot', assumption)+
  apply (clarsimp simp: default_cap_cnode_dev)
  apply sep_solve
  done

lemma seL4_CNode_Mutate_object_slot_initialised_sep_helper:
  "\<lbrakk>well_formed spec;
    cdl_objects spec obj_id = Some spec_obj;
    cnode_at obj_id spec;
    opt_cap (obj_id, slot) spec = Some spec_cap;
    spec_cap \<noteq> NullCap;
    original_cap_at (obj_id, slot) spec;
    valid_src_cap spec_cap data;
    cap_has_object spec_cap;
    cap_type spec_cap = Some type;
    is_device_cap spec_cap = dev;
    \<not> ep_related_cap spec_cap;
    \<not> is_untyped_cap spec_cap;
    data = cap_data spec_cap;
    cdl_objects spec (cap_object spec_cap) = Some spec_cap_obj;
    is_cnode_cap spec_cap \<longrightarrow> object_size_bits spec_cap_obj = cnode_cap_size spec_cap;
    t obj_id = Some dest_id;
    t (cap_object spec_cap) = Some client_object_id;
    src_index < 2 ^ si_cnode_size;
    dest_root < 2 ^ si_cnode_size;
    Some dest_root = dup_caps obj_id;
    Some src_index = orig_caps (cap_object spec_cap)\<rbrakk> \<Longrightarrow>
   \<lbrace>\<guillemotleft>object_slot_empty spec t obj_id slot \<and>*
     si_cap_at t orig_caps spec dev (cap_object spec_cap) \<and>*
     si_cap_at t dup_caps spec dev obj_id \<and>*
     object_fields_empty spec t obj_id \<and>* si_objects \<and>* R\<guillemotright> \<rbrace>
   seL4_CNode_Mutate dest_root (of_nat slot) (of_nat (object_size_bits spec_obj))
                     seL4_CapInitThreadCNode src_index 32 data
   \<lbrace>\<lambda>_.\<guillemotleft>object_slot_initialised spec t obj_id slot \<and>*
        si_null_cap_at t orig_caps spec (cap_object spec_cap) \<and>*
        si_cap_at t dup_caps spec dev obj_id \<and>*
        object_fields_empty spec t obj_id \<and>* si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_chain)
    apply (rule_tac cnode_cap = si_cspace_cap
                and cnode_cap' = si_cnode_cap
                and dest_root_cap = "default_cap CNodeType {dest_id} (object_size_bits spec_obj) False"
                and root_size=si_cnode_size
                and src_root=seL4_CapInitThreadCNode
                and src_depth=32
                and tcb=root_tcb
                and src_cap = "default_cap type {client_object_id} (object_size_bits spec_cap_obj) dev"
                in seL4_CNode_Mutate_sep[where
                R = "(si_cnode_id, unat seL4_CapIRQControl) \<mapsto>c IrqControlCap \<and>* si_asid \<and>* R"])
    apply (assumption|simp add: ep_related_cap_default_cap
                 default_cap_has_type valid_src_cap_if_cnode
                 get_index_def)+
   apply (frule_tac s=s and dup_caps=dup_caps and
                    t=t and orig_caps=orig_caps
                 in mint_pre,(assumption|rule refl|simp)+)
   apply (elim conjE)
   apply clarsimp
   apply (intro conjI,
          simp_all add: has_type_default_not_non ep_related_cap_default_cap)
      apply (thin_tac "\<guillemotleft>P \<and>* Q \<guillemotright>s" for P Q)
      apply sep_solve
     apply ((clarsimp simp: si_cnode_cap_def word_bits_def si_cspace_cap_def
                       dest!: guard_equal_si_cspace_cap |
               rule is_cnode_cap_si_cnode_cap)+)[2]
         (* it works because si_cnode_cap = si_cspace_cap *)
  apply (drule_tac s=s and dest_root=dest_root and src_index=src_index and R=R
                in mutate_post, (assumption|simp|fastforce)+)[1]
   apply (subst(asm) default_cap_data_if_cnode, fastforce+)
  done

lemma seL4_CNode_Move_object_slot_initialised_cap_has_object_sep_helper:
  "\<lbrakk>well_formed spec;
    cdl_objects spec obj_id = Some spec_obj;
    cnode_at obj_id spec;
    opt_cap (obj_id, slot) spec = Some spec_cap;
    spec_cap \<noteq> NullCap;
    original_cap_at (obj_id, slot) spec;
    is_default_cap spec_cap;
    valid_src_cap spec_cap data;
    cap_has_object spec_cap;
    cap_type spec_cap = Some type;
    is_device_cap spec_cap = dev;
    \<not> is_untyped_cap spec_cap;
    \<not> is_asidpool_cap spec_cap;
    data = cap_data spec_cap;
    cdl_objects spec (cap_object spec_cap) = Some spec_cap_obj;
    is_cnode_cap spec_cap \<longrightarrow> object_size_bits spec_cap_obj = cnode_cap_size spec_cap;
    t obj_id = Some dest_id;
    t (cap_object spec_cap) = Some client_object_id;
    src_index < 2 ^ si_cnode_size;
    dest_root < 2 ^ si_cnode_size;
    Some dest_root = dup_caps obj_id;
    Some src_index = orig_caps (cap_object spec_cap)\<rbrakk> \<Longrightarrow>
   \<lbrace>\<guillemotleft>object_slot_empty spec t obj_id slot \<and>*
     si_cap_at t orig_caps spec dev (cap_object spec_cap) \<and>*
     si_cap_at t dup_caps spec dev obj_id \<and>*
     object_fields_empty spec t obj_id \<and>* si_objects \<and>* R\<guillemotright> \<rbrace>
   seL4_CNode_Move dest_root (of_nat slot) (of_nat (object_size_bits spec_obj))
                     seL4_CapInitThreadCNode src_index 32
   \<lbrace>\<lambda>_.\<guillemotleft>object_slot_initialised spec t obj_id slot \<and>*
        si_null_cap_at t orig_caps spec (cap_object spec_cap) \<and>*
        si_cap_at t dup_caps spec dev obj_id \<and>*
        object_fields_empty spec t obj_id \<and>* si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_chain)
   apply (rule_tac cnode_cap = si_cspace_cap
              and cnode_cap' = si_cnode_cap
              and dest_root_cap = "default_cap CNodeType {dest_id} (object_size_bits spec_obj) False"
              and root_size=si_cnode_size
              and src_root=seL4_CapInitThreadCNode
              and src_depth=32
              and tcb=root_tcb
              and src_cap = "default_cap type {client_object_id} (object_size_bits spec_cap_obj) dev"
               in seL4_CNode_Move_sep[where
                R = "(si_cnode_id, unat seL4_CapIRQControl) \<mapsto>c IrqControlCap \<and>* si_asid \<and>* R"],
               (assumption|simp add: ep_related_cap_default_cap
                 default_cap_has_type
                 get_index_def)+)
    apply (frule_tac s=s and t=t and dup_caps=dup_caps and orig_caps=orig_caps
                 in mint_pre,(assumption|rule refl|simp)+)
   apply (elim conjE)
   apply clarsimp
   apply (intro conjI,
     simp_all add:has_type_default_not_non ep_related_cap_default_cap)
      apply (thin_tac "\<guillemotleft>P \<and>* Q \<guillemotright>s" for P Q)
      apply sep_solve
     apply ((clarsimp simp: si_cnode_cap_def word_bits_def si_cspace_cap_def
                       dest!: guard_equal_si_cspace_cap |
               rule is_cnode_cap_si_cnode_cap)+)[2]
         (* it works because si_cnode_cap = si_cspace_cap *)
  apply (drule_tac s=s and dest_root=dest_root and src_index=src_index and R=R
                in move_post, (assumption|simp)+)
   apply sep_cancel+
   apply (drule cap_has_object_not_irqhandler_cap)
   apply (subst(asm) default_cap_data_if_cnode,simp+)
   apply clarsimp
   apply (subst(asm) default_cap_update_cap_object,
          (simp add: valid_src_cap_cnode_cap_size_le_32)+)
  done

lemma seL4_CNode_Move_object_slot_initialised_irqhandler_cap_sep_helper:
  "\<lbrakk>well_formed spec;
    cdl_objects spec obj_id = Some spec_obj;
    cnode_at obj_id spec;
    opt_cap (obj_id, slot) spec = Some spec_cap;
    is_irqhandler_cap spec_cap;
    t obj_id = Some dest_id;
    src_index < 2 ^ si_cnode_size;
    dest_root < 2 ^ si_cnode_size;
    Some dest_root = dup_caps obj_id;
    Some src_index = irq_caps (cap_irq spec_cap)\<rbrakk> \<Longrightarrow>
   \<lbrace>\<guillemotleft>object_slot_empty spec t obj_id slot \<and>*
     si_irq_cap_at irq_caps spec (cap_irq spec_cap) \<and>*
     si_cap_at t dup_caps spec False obj_id \<and>*
     object_fields_empty spec t obj_id \<and>* si_objects \<and>* R\<guillemotright> \<rbrace>
   seL4_CNode_Move dest_root (of_nat slot) (of_nat (object_size_bits spec_obj))
                     seL4_CapInitThreadCNode src_index 32
   \<lbrace>\<lambda>_.\<guillemotleft>object_slot_initialised spec t obj_id slot \<and>*
        si_null_irq_cap_at irq_caps spec (cap_irq spec_cap) \<and>*
        si_cap_at t dup_caps spec dev obj_id \<and>*
        object_fields_empty spec t obj_id \<and>* si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_chain)
   apply (rule_tac cnode_cap = si_cspace_cap
              and cnode_cap' = si_cnode_cap
              and dest_root_cap = "default_cap CNodeType {dest_id} (object_size_bits spec_obj) False"
              and root_size=si_cnode_size
              and src_root=seL4_CapInitThreadCNode
              and src_depth=32
              and tcb=root_tcb
              and src_cap = " IrqHandlerCap (cap_irq spec_cap)"
               in seL4_CNode_Move_sep[where
                R = "(si_cnode_id, unat seL4_CapIRQControl) \<mapsto>c IrqControlCap \<and>* si_asid \<and>* R"],
               (assumption|simp add: ep_related_cap_default_cap
                 default_cap_has_type
                 get_index_def)+)
    apply (frule_tac s=s and t=t and dup_caps=dup_caps and irq_caps=irq_caps
                 in move_pre_irq_handler,(assumption|rule refl|simp)+)
   apply (elim conjE)
   apply (intro conjI,
          simp_all add:has_type_default_not_non ep_related_cap_default_cap)
      apply (thin_tac "\<guillemotleft>P \<and>* Q \<guillemotright>s" for P Q)
      apply (sep_solve add: sep_any_imp)
     apply ((clarsimp simp: si_cnode_cap_def word_bits_def si_cspace_cap_def
                     dest!: guard_equal_si_cspace_cap |
               rule is_cnode_cap_si_cnode_cap)+)[2]
         (* it works because si_cnode_cap = si_cspace_cap *)
  apply (drule_tac s=s and dest_root=dest_root and src_index=src_index and R=R
                in move_post_irq_handler, (assumption|simp)+)
  done

lemma seL4_CNode_Move_object_slot_initialised_cap_has_object_sep:
  "\<lbrace>\<lambda>s. well_formed spec \<and> original_cap_at (obj_id, slot) spec \<and>
        data = cap_data spec_cap \<and>
        cap_has_object spec_cap \<and>
        cnode_at obj_id spec \<and> cdl_objects spec obj_id = Some spec_obj \<and>
        opt_cap (obj_id, slot) spec = Some spec_cap \<and> spec_cap \<noteq> NullCap \<and>
        cap_has_type spec_cap \<and> valid_src_cap spec_cap data \<and> (is_device_cap spec_cap = dev) \<and>
        \<not>is_untyped_cap spec_cap \<and> is_default_cap spec_cap \<and> \<not> is_asidpool_cap spec_cap \<and>
        cdl_objects spec (cap_object spec_cap) = Some spec_cap_obj \<and>
        (is_cnode_cap spec_cap \<longrightarrow> object_size_bits spec_cap_obj = cnode_cap_size spec_cap) \<and>
        Some dest_root = dup_caps obj_id \<and>
        Some src_index = orig_caps (cap_object spec_cap) \<and>
        \<guillemotleft>object_slot_empty spec t obj_id slot \<and>*
         si_cap_at t orig_caps spec dev (cap_object spec_cap) \<and>*
         si_cap_at t dup_caps spec dev obj_id \<and>*
         object_fields_empty spec t obj_id \<and>* si_objects \<and>* R\<guillemotright> s\<rbrace>
     seL4_CNode_Move dest_root (of_nat slot) (of_nat (object_size_bits spec_obj))
                     seL4_CapInitThreadCNode src_index 32
   \<lbrace>\<lambda>_.\<guillemotleft>object_slot_initialised spec t obj_id slot \<and>*
        si_null_cap_at t orig_caps spec (cap_object spec_cap) \<and>*
        si_cap_at t dup_caps spec dev obj_id \<and>*
        object_fields_empty spec t obj_id \<and>* si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_assume_pre)
  apply (elim conjE)
  apply (rule hoare_weaken_pre)
   apply clarsimp
   apply (rule_tac dest_id="the(t obj_id)" and client_object_id="the(t (cap_object spec_cap))"
                in seL4_CNode_Move_object_slot_initialised_cap_has_object_sep_helper, (assumption|simp)+)
       apply (clarsimp simp: si_cap_at_def sep_conj_exists)
      apply (clarsimp simp: si_cap_at_def sep_conj_exists)
    apply (sep_drule (direct) si_cap_at_less_si_cnode_size [where cap_ptr = src_index
                 and R="object_slot_empty spec t obj_id slot \<and>* si_cap_at t dup_caps spec (is_device_cap spec_cap) obj_id \<and>* object_fields_empty spec t obj_id \<and>* si_objects \<and>* R"])
       apply (fastforce simp: sep_conj_ac)
   apply clarsimp
     apply (sep_drule (direct) si_cap_at_less_si_cnode_size [where cap_ptr = dest_root and t=t and spec=spec
                   and R="object_slot_empty spec t obj_id slot \<and>* si_cap_at t orig_caps spec (is_device_cap spec_cap) (cap_object spec_cap) \<and>* object_fields_empty spec t obj_id \<and>* si_objects \<and>* R"])
      apply (fastforce simp: sep_conj_ac)
     apply clarsimp+
  done


lemma seL4_CNode_Move_object_slot_initialised_irqhandler_cap_sep:
  "\<lbrace>\<lambda>s. well_formed spec \<and>
        cnode_at obj_id spec \<and>
        cdl_objects spec obj_id = Some spec_obj \<and>
        opt_cap (obj_id, slot) spec = Some spec_cap \<and>
        is_irqhandler_cap spec_cap \<and>
        Some dest_root = dup_caps obj_id \<and>
        Some src_index = irq_caps (cap_irq spec_cap) \<and>
        \<guillemotleft>object_slot_empty spec t obj_id slot \<and>*
         si_irq_cap_at irq_caps spec (cap_irq spec_cap) \<and>*
         si_cap_at t dup_caps spec False obj_id \<and>*
         object_fields_empty spec t obj_id \<and>* si_objects \<and>* R\<guillemotright> s\<rbrace>
     seL4_CNode_Move dest_root (of_nat slot) (of_nat (object_size_bits spec_obj))
                     seL4_CapInitThreadCNode src_index 32
   \<lbrace>\<lambda>_.\<guillemotleft>object_slot_initialised spec t obj_id slot \<and>*
        si_null_irq_cap_at irq_caps spec (cap_irq spec_cap) \<and>*
        si_cap_at t dup_caps spec False obj_id \<and>*
        object_fields_empty spec t obj_id \<and>* si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_assume_pre)
  apply (elim conjE)
  apply (rule hoare_weaken_pre)
   apply (rule_tac dest_id="the (t obj_id)"
                in seL4_CNode_Move_object_slot_initialised_irqhandler_cap_sep_helper, (assumption|simp)+)
       apply (clarsimp simp: si_cap_at_def sep_conj_exists)
      apply (sep_drule (direct) si_irq_cap_at_less_si_cnode_size, assumption+)
     apply (sep_drule (direct) si_cap_at_less_si_cnode_size, assumption+)
  apply clarsimp
  done

lemma seL4_CNode_Move_object_slot_initialised_irqhandler_cap_sep_new:
  "\<lbrace>\<guillemotleft>object_slot_empty spec t obj_id slot \<and>*
         si_irq_cap_at irq_caps spec (cap_irq spec_cap) \<and>*
         si_cap_at t dup_caps spec False obj_id \<and>*
         object_fields_empty spec t obj_id \<and>* si_objects \<and>* R\<guillemotright>
     and K( well_formed spec \<and>
        cnode_at obj_id spec \<and>
        cdl_objects spec obj_id = Some spec_obj \<and>
        opt_cap (obj_id, slot) spec = Some spec_cap \<and>
        is_irqhandler_cap spec_cap \<and>
        Some dest_root = dup_caps obj_id \<and>
        Some src_index = irq_caps (cap_irq spec_cap))\<rbrace>
     seL4_CNode_Move dest_root (of_nat slot) (of_nat (object_size_bits spec_obj))
                     seL4_CapInitThreadCNode src_index 32
   \<lbrace>\<lambda>_.\<guillemotleft>object_slot_initialised spec t obj_id slot \<and>*
        si_null_irq_cap_at irq_caps spec (cap_irq spec_cap) \<and>*
        si_cap_at t dup_caps spec False obj_id \<and>*
        object_fields_empty spec t obj_id \<and>* si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_assume_pre)
  apply (clarsimp)
  apply (wp sep_wp: seL4_CNode_Move_object_slot_initialised_irqhandler_cap_sep_helper
                    [where dest_id="the(t obj_id)" and t=t and obj_id=obj_id], (assumption|simp)+)
       apply (clarsimp simp: si_cap_at_def sep_conj_exists)
       apply (sep_drule (direct) si_irq_cap_at_less_si_cnode_size, assumption+)
      apply (sep_drule (direct) si_cap_at_less_si_cnode_size, assumption+)
  apply (sep_safe+, sep_solve)
  done

lemma seL4_CNode_Mutate_object_slot_initialised_sep:
  "\<lbrace>\<lambda>s. well_formed spec \<and> original_cap_at (obj_id, slot) spec \<and>
        data = cap_data spec_cap \<and>
        cnode_at obj_id spec \<and> cdl_objects spec obj_id = Some spec_obj \<and>
        opt_cap (obj_id, slot) spec = Some spec_cap \<and> spec_cap \<noteq> NullCap \<and>
        cap_has_type spec_cap \<and> valid_src_cap spec_cap data \<and> is_device_cap spec_cap = dev \<and>
        cap_has_object spec_cap \<and>
        \<not> is_untyped_cap spec_cap \<and> \<not> ep_related_cap spec_cap \<and>
        cdl_objects spec (cap_object spec_cap) = Some spec_cap_obj \<and>
        (is_cnode_cap spec_cap \<longrightarrow> object_size_bits spec_cap_obj = cnode_cap_size spec_cap) \<and>
        Some dest_root = dup_caps obj_id \<and>
        Some src_index = orig_caps (cap_object spec_cap) \<and>
        \<guillemotleft>object_slot_empty spec t obj_id slot \<and>*
         si_cap_at t orig_caps spec dev (cap_object spec_cap) \<and>*
         si_cap_at t dup_caps spec dev obj_id \<and>*
         object_fields_empty spec t obj_id \<and>* si_objects \<and>* R\<guillemotright> s \<rbrace>
      seL4_CNode_Mutate dest_root (of_nat slot) (of_nat (object_size_bits spec_obj))
                     seL4_CapInitThreadCNode src_index 32 data
   \<lbrace>\<lambda>_.\<guillemotleft>object_slot_initialised spec t obj_id slot \<and>*
        si_null_cap_at t orig_caps spec (cap_object spec_cap) \<and>*
        si_cap_at t dup_caps spec dev obj_id \<and>*
        object_fields_empty spec t obj_id \<and>* si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_assume_pre)
  apply (elim conjE)
  apply (rule hoare_weaken_pre)
   apply clarsimp
   apply (rule_tac dest_id="the(t obj_id)" and client_object_id="the(t (cap_object spec_cap))"
                in seL4_CNode_Mutate_object_slot_initialised_sep_helper, (assumption|simp)+)
       apply (clarsimp simp: si_cap_at_def sep_conj_exists)
      apply (clarsimp simp: si_cap_at_def sep_conj_exists)
    apply (sep_drule (direct) si_cap_at_less_si_cnode_size [where cap_ptr = src_index
                 and R="object_slot_empty spec t obj_id slot \<and>* si_cap_at t dup_caps spec (is_device_cap spec_cap) obj_id \<and>* object_fields_empty spec t obj_id \<and>* si_objects \<and>* R"])
       apply (fastforce simp: sep_conj_ac)
   apply clarsimp
     apply (sep_drule (direct) si_cap_at_less_si_cnode_size [where cap_ptr = dest_root and t=t and spec=spec
                   and R="object_slot_empty spec t obj_id slot \<and>* si_cap_at t orig_caps spec (is_device_cap spec_cap) (cap_object spec_cap) \<and>* object_fields_empty spec t obj_id \<and>* si_objects \<and>* R"] )
      apply (fastforce simp: sep_conj_ac)
     apply clarsimp+
  done

lemma irq_handler_cap_not_device[simp]:
 "is_irqhandler_cap y \<Longrightarrow> is_device_cap y = False"
 by (auto simp:is_device_cap_def split:cdl_cap.splits)

lemma init_cnode_slot_move_original_sep:
  "\<lbrakk>well_formed spec; cnode_at obj_id spec;
    original_cap_at (obj_id, slot) spec;
    cap_at (\<lambda>c. is_device_cap c = dev) (obj_id, slot)  spec\<rbrakk> \<Longrightarrow>
   \<lbrace>\<guillemotleft>cnode_slot_half_initialised spec t obj_id slot \<and>*
     si_obj_cap_at t orig_caps spec dev obj_id slot \<and>*
     si_spec_irq_cap_at irq_caps spec obj_id slot \<and>*
     si_cap_at t dup_caps spec dev obj_id \<and>*
     object_fields_empty spec t obj_id \<and>* si_objects \<and>* R\<guillemotright> \<rbrace>
   init_cnode_slot spec orig_caps dup_caps irq_caps Move obj_id slot
   \<lbrace>\<lambda>_.\<guillemotleft>object_slot_initialised spec t obj_id slot \<and>*
        si_spec_obj_null_cap_at t orig_caps spec obj_id slot \<and>*
        si_spec_irq_null_cap_at irq_caps spec obj_id slot \<and>*
        si_cap_at t dup_caps spec dev obj_id \<and>*
        object_fields_empty spec t obj_id \<and>* si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (subst cnode_slot_half_initialised_original_slot, assumption+)
  apply (frule cnode_at_not_tcb_at)

  (* Case: opt_cap (obj_id, slot) spec = Some NullCap *)
  apply (case_tac "opt_cap (obj_id, slot) spec = Some NullCap")
   apply (clarsimp simp: init_cnode_slot_def sep_conj_exists cap_at_def
                         si_obj_cap_at_def si_spec_irq_cap_at_def
                         si_spec_obj_null_cap_at_def si_spec_irq_null_cap_at_def)
   apply (frule opt_cap_cdl_objects)
   apply (wp | clarsimp)+
   apply (subst (asm) object_slot_empty_initialised_NullCap, assumption+)

  (* Case: opt_cap (obj_id, slot) spec = None *)
  apply (case_tac "opt_cap (obj_id, slot) spec = None")
   apply (clarsimp simp: init_cnode_slot_def assert_opt_def)
  apply clarsimp

  (* Case: cap_at cap_has_object (obj_id, slot) spec *)
  apply (case_tac "cap_at cap_has_object (obj_id, slot) spec")
   apply (clarsimp simp: cap_at_def)
   apply (rename_tac cap)
   apply (frule (2) well_formed_cap_object)
   apply (frule (2) well_formed_is_untyped_cap)
   apply (clarsimp simp: init_cnode_slot_def)
   apply (clarsimp simp: si_obj_cap_at_def si_obj_cap_at'_def cap_at_def
                         si_spec_obj_null_cap_at_def si_spec_obj_null_cap_at'_def
                         si_spec_irq_cap_at_def si_spec_irq_cap_at'_def
                         si_spec_irq_null_cap_at_def si_spec_irq_null_cap_at'_def)
   apply (wp seL4_CNode_Mutate_object_slot_initialised_sep seL4_CNode_Move_object_slot_initialised_cap_has_object_sep |
          clarsimp)+
   apply (intro impI conjI,simp_all add:)
          apply (drule(1) well_formed_well_formed_cap[where obj_id = obj_id])
            apply (simp add:opt_cap_def slots_of_def)
           apply (simp add:cap_type_null)
          apply simp
         apply (metis cap_has_object_not_NullCap well_formed_cap_valid_src_cap well_formed_well_formed_cap')
        apply (metis cap_has_object_not_NullCap well_formed_orig_ep_cap_is_default)
       apply (simp add: ep_related_cap_def cap_type_def split:cdl_cap.splits)
      apply (erule (3) well_formed_cnode_object_size_bits_eq)
     apply (metis cap_has_object_NullCap well_formed_cap_has_object_has_type well_formed_well_formed_cap')
    apply (metis cap_has_object_NullCap well_formed_cap_valid_src_cap well_formed_well_formed_cap')
   apply (erule (3) well_formed_cnode_object_size_bits_eq)

  (* Case: cap_at is_irqhandler_cap (obj_id, slot) spec *)
  apply (frule (3) well_formed_cap_no_object_irqhandler_cap)
  apply (clarsimp simp: cap_at_def)
  apply (rename_tac cap)
  apply (clarsimp simp: init_cnode_slot_def)
  apply (clarsimp simp: si_obj_cap_at_def si_obj_cap_at'_def cap_at_def
                        si_spec_obj_null_cap_at_def si_spec_obj_null_cap_at'_def
                        si_spec_irq_cap_at_def si_spec_irq_cap_at'_def
                        si_spec_irq_null_cap_at_def si_spec_irq_null_cap_at'_def)
  apply (wp seL4_CNode_Move_object_slot_initialised_irqhandler_cap_sep | clarsimp)+
  done

lemma init_cnode_slot_move_not_original_inv:
  "\<lbrakk>\<not>original_cap_at (obj_id, slot) spec\<rbrakk>
  \<Longrightarrow> \<lbrace>P\<rbrace> init_cnode_slot spec orig_caps dup_caps irq_caps Move obj_id slot \<lbrace>\<lambda>_. P\<rbrace>"
  apply (clarsimp simp: init_cnode_slot_def cap_at_def)
  apply wp
         apply (rule hoare_pre_cont)
        apply (rule hoare_pre_cont)
       apply clarsimp
       apply wp+
  apply clarsimp
  done

lemma si_obj_cap_at_si_spec_obj_null_cap_at_not_original:
  "\<lbrakk>\<not> original_cap_at (obj_id, slot) spec\<rbrakk>
  \<Longrightarrow> si_obj_cap_at t si_caps spec dev obj_id slot =
      si_spec_obj_null_cap_at t si_caps spec obj_id slot"
  by (clarsimp simp: si_obj_cap_at_def si_spec_obj_null_cap_at_def)

lemma init_cnode_slot_move_not_original_sep:
  "\<lbrakk>well_formed spec; cnode_at obj_id spec;
    \<not> original_cap_at (obj_id, slot) spec\<rbrakk> \<Longrightarrow>
   \<lbrace>\<guillemotleft>cnode_slot_half_initialised spec t obj_id slot \<and>*
     si_obj_cap_at t orig_caps spec dev obj_id slot \<and>*
     si_spec_irq_cap_at irq_caps spec obj_id slot \<and>*
     si_cap_at t dup_caps spec dev obj_id \<and>*
     object_fields_empty spec t obj_id \<and>* si_objects \<and>* R\<guillemotright> \<rbrace>
   init_cnode_slot spec orig_caps dup_caps irq_caps Move obj_id slot
   \<lbrace>\<lambda>_.\<guillemotleft>object_slot_initialised spec t obj_id slot \<and>*
        si_spec_obj_null_cap_at t orig_caps spec obj_id slot \<and>*
        si_spec_irq_null_cap_at irq_caps spec obj_id slot \<and>*
        si_cap_at t dup_caps spec dev obj_id \<and>*
        object_fields_empty spec t obj_id \<and>* si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (wp init_cnode_slot_move_not_original_inv)
  apply (subst (asm) cnode_slot_half_initialised_not_original_slot, assumption+)
  apply (subst (asm) si_obj_cap_at_si_spec_obj_null_cap_at_not_original, assumption)
  apply (clarsimp simp: si_spec_irq_cap_at_def si_spec_irq_null_cap_at_def original_cap_at_def)
  done

lemma init_cnode_slot_move_sep:
  "\<lbrakk>well_formed spec; cnode_at obj_id spec;cap_at (\<lambda>c. is_device_cap c = dev) (obj_id, slot) spec\<rbrakk> \<Longrightarrow>
   \<lbrace>\<guillemotleft>cnode_slot_half_initialised spec t obj_id slot \<and>*
     si_obj_cap_at t orig_caps spec dev obj_id slot \<and>*
     si_spec_irq_cap_at irq_caps spec obj_id slot \<and>*
     si_cap_at t dup_caps spec dev obj_id \<and>*
     object_fields_empty spec t obj_id \<and>* si_objects \<and>* R\<guillemotright> \<rbrace>
   init_cnode_slot spec orig_caps dup_caps irq_caps Move obj_id slot
   \<lbrace>\<lambda>_.\<guillemotleft>object_slot_initialised spec t obj_id slot \<and>*
        si_spec_obj_null_cap_at t orig_caps spec obj_id slot \<and>*
        si_spec_irq_null_cap_at irq_caps spec obj_id slot \<and>*
        si_cap_at t dup_caps spec dev obj_id \<and>*
        object_fields_empty spec t obj_id \<and>* si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (case_tac "original_cap_at (obj_id, slot) spec")
   apply (wp init_cnode_slot_move_original_sep)
  apply (wp init_cnode_slot_move_not_original_sep)
  done

lemma init_cnode_slots_move_sep:
  "\<lbrakk>well_formed spec; cnode_at obj_id spec;
    \<forall>slot\<in> dom (slots_of obj_id spec). cap_at (\<lambda>c. is_device_cap c = dev) (obj_id,slot) spec\<rbrakk> \<Longrightarrow>
   \<lbrace>\<guillemotleft>cnode_slots_half_initialised spec t obj_id \<and>*
     si_obj_caps_at t orig_caps spec dev obj_id \<and>*
     si_spec_irq_caps_at irq_caps spec obj_id \<and>*
     si_cap_at t dup_caps spec dev obj_id \<and>*
     object_fields_empty spec t obj_id \<and>* si_objects \<and>* R\<guillemotright>\<rbrace>
   init_cnode spec orig_caps dup_caps irq_caps Move obj_id
   \<lbrace>\<lambda>_.\<guillemotleft>object_slots_initialised spec t obj_id \<and>*
        si_spec_obj_null_caps_at t orig_caps spec obj_id \<and>*
        si_spec_irq_null_caps_at irq_caps spec obj_id \<and>*
        si_cap_at t dup_caps spec dev obj_id \<and>*
        object_fields_empty spec t obj_id \<and>* si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_assume_pre)
  apply (simp add: init_cnode_def si_obj_caps_at_def si_spec_obj_null_caps_at_def
                   si_spec_irq_caps_at_def si_spec_irq_null_caps_at_def)
  apply (frule_tac obj_id=obj_id and t=t in cnode_slots_half_initialised_decomp, fastforce+)
  apply (cut_tac obj_id=obj_id and t=t in object_slots_initialised_decomp, fastforce+)
  apply simp
  apply (subst cnode_empty_slots_half_initialised_object_empty_slots_initialised)
  apply (simp add: sep_conj_assoc)
  apply (rule hoare_chain)
    apply (rule_tac mapM_x_set_sep [where
               P="\<lambda>slot. cnode_slot_half_initialised spec t obj_id slot \<and>*
                  si_obj_cap_at t orig_caps spec dev obj_id slot \<and>*
                  si_spec_irq_cap_at irq_caps spec obj_id slot" and
               Q="\<lambda>slot. object_slot_initialised spec t obj_id slot \<and>*
                  si_spec_obj_null_cap_at t orig_caps spec obj_id slot \<and>*
                  si_spec_irq_null_cap_at irq_caps spec obj_id slot" and
               I="si_cap_at t dup_caps spec dev obj_id \<and>*
                  object_fields_empty spec t obj_id \<and>*
                  si_objects \<and>* object_empty_slots_initialised spec t obj_id" and
               xs="slots_of_list spec obj_id",
               simplified sep_conj_assoc], clarsimp+)
     apply (wpsimp wp: init_cnode_slot_move_sep)
     apply fastforce
    apply simp
   apply (subst sep.prod.distrib)+
   apply (clarsimp simp: sep_conj_assoc fun_eq_iff)
   apply sep_solve
  apply clarsimp
  apply (subst (asm) sep.prod.distrib)+
  apply (clarsimp simp: sep_conj_assoc fun_eq_iff)
  apply sep_solve
  done

lemma init_cnode_move_sep:
  "\<lbrakk>well_formed spec; cnode_at obj_id spec;
   \<forall>slot\<in>dom (slots_of obj_id spec). cap_at (\<lambda>c. is_device_cap c = dev) (obj_id, slot) spec\<rbrakk> \<Longrightarrow>
   \<lbrace>\<guillemotleft>cnode_half_initialised spec t obj_id \<and>*
     si_obj_caps_at t orig_caps spec dev obj_id \<and>*
     si_spec_irq_caps_at irq_caps spec obj_id \<and>*
     si_cap_at t dup_caps spec dev obj_id \<and>*
     si_objects \<and>* R\<guillemotright>\<rbrace>
   init_cnode spec orig_caps dup_caps irq_caps Move obj_id
   \<lbrace>\<lambda>_.\<guillemotleft>object_initialised spec t obj_id \<and>*
        si_spec_obj_null_caps_at t orig_caps spec obj_id \<and>*
        si_spec_irq_null_caps_at irq_caps spec obj_id \<and>*
        si_cap_at t dup_caps spec dev obj_id \<and>*
        si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_assume_pre)
  apply (subst object_initialised_decomp, subst cnode_half_initialised_decomp)
  apply (subst object_fields_empty_half_initialised, simp)
  apply (rule hoare_chain)
    apply (rule_tac R=R and t=t in init_cnode_slots_move_sep, simp+)
   apply sep_solve
  apply (subst (asm) cnode_fields_empty_initialised, assumption+, sep_solve)
  done

lemma init_cspace_move_sep:
  "\<lbrace>\<guillemotleft>cnodes_half_initialised spec t cnode_set \<and>*
    si_objs_caps_at t orig_caps spec dev cnode_set \<and>*
    si_spec_irqs_caps_at irq_caps spec cnode_set \<and>*
    si_caps_at t dup_caps spec dev cnode_set \<and>*
    si_objects \<and>* R\<guillemotright> and K(
    well_formed spec \<and>
    (\<forall>obj_id \<in> set cnode_list.
     (cnode_at obj_id spec \<and>
     (\<forall>slot\<in>dom (slots_of obj_id spec). cap_at (\<lambda>c. is_device_cap c = dev) (obj_id, slot) spec)))
    \<and> distinct cnode_list \<and> cnode_set = set cnode_list)\<rbrace>
     mapM_x (init_cnode spec orig_caps dup_caps irq_caps Move) cnode_list
   \<lbrace>\<lambda>_. \<guillemotleft>objects_initialised spec t cnode_set \<and>*
         si_spec_objs_null_caps_at t orig_caps spec cnode_set \<and>*
         si_spec_irqs_null_caps_at irq_caps spec cnode_set \<and>*
         si_caps_at t dup_caps spec dev cnode_set \<and>*
         si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (clarsimp simp: cnodes_half_initialised_def objects_initialised_def si_caps_at_def
                        si_objs_caps_at_def si_spec_objs_null_caps_at_def
                        si_spec_irqs_caps_at_def si_spec_irqs_null_caps_at_def)
  apply (rule hoare_name_pre_state)
  apply (rule hoare_chain)
    apply (rule_tac R=R in mapM_x_set_sep [where
                    P="\<lambda>obj_id. cnode_half_initialised spec t obj_id \<and>*
                       si_obj_caps_at t orig_caps spec dev obj_id \<and>*
                       si_spec_irq_caps_at irq_caps spec obj_id \<and>*
                       si_cap_at t dup_caps spec dev obj_id" and
                    Q="\<lambda>obj_id. object_initialised spec t obj_id \<and>*
                       si_spec_obj_null_caps_at t orig_caps spec obj_id \<and>*
                       si_spec_irq_null_caps_at irq_caps spec obj_id \<and>*
                       si_cap_at t dup_caps spec dev obj_id" and
                    I="si_objects" and
                    xs="cnode_list", simplified sep_conj_assoc], simp)
     apply (wp init_cnode_move_sep, simp+)
   apply clarsimp
   apply (subst sep.prod.distrib)+
   apply sep_solve
  apply (subst (asm) sep.prod.distrib)+
  apply sep_solve
  done

lemma init_cnode_slot_copy_original_sep:
  "\<lbrakk>original_cap_at (obj_id, slot) spec\<rbrakk>
  \<Longrightarrow> \<lbrace>P\<rbrace> init_cnode_slot spec orig_caps dup_caps irq_caps Copy obj_id slot \<lbrace>\<lambda>_. P\<rbrace>"
  apply (clarsimp simp: init_cnode_slot_def)
  apply (wp|clarsimp)+
  done

lemma ep_cap_default_cap:
 "cap_type cap = Some type \<Longrightarrow>
  is_ep_cap (default_cap type ids sz dev) = is_ep_cap cap"
  by (fastforce simp: cap_type_def default_cap_def
               split: cdl_cap.splits cdl_object_type.splits)

lemma ntfn_cap_default_cap:
 "cap_type cap = Some type \<Longrightarrow>
  is_ntfn_cap (default_cap type ids sz dev) = is_ntfn_cap cap"
  by (fastforce simp: cap_type_def default_cap_def
               split: cdl_cap.splits cdl_object_type.splits)

lemma seL4_CNode_Mint_object_slot_initialised_sep_helper:
  "\<lbrakk>well_formed spec;
    cnode_at obj_id spec;
    \<not> original_cap_at (obj_id, slot) spec; \<not> is_untyped_cap spec_cap;
    valid_src_cap spec_cap data;
    cap_has_object spec_cap;
    cap_type spec_cap = Some type;
    is_device_cap spec_cap = dev;
    data = cap_data spec_cap; rights = cap_rights spec_cap;
    well_formed spec; cnode_at obj_id spec;
    cdl_objects spec obj_id = Some spec_obj;
    opt_cap (obj_id, slot) spec = Some spec_cap; spec_cap \<noteq> NullCap;
    cdl_objects spec (cap_object spec_cap) = Some spec_cap_obj;
    is_cnode_cap spec_cap \<longrightarrow>object_size_bits spec_cap_obj = cnode_cap_size spec_cap;
    t obj_id = Some dest_id;
    t (cap_object spec_cap) = Some client_object_id;
    src_index < 2 ^ si_cnode_size;
    dest_root < 2 ^ si_cnode_size;
    Some dest_root = dup_caps obj_id;
    Some src_index = orig_caps (cap_object spec_cap)\<rbrakk> \<Longrightarrow>
   \<lbrace>\<guillemotleft>object_slot_empty spec t obj_id slot \<and>*
     si_cap_at t orig_caps spec dev (cap_object spec_cap) \<and>*
     si_cap_at t dup_caps spec dev obj_id \<and>*
     object_fields_empty spec t obj_id \<and>* si_objects \<and>* R\<guillemotright> \<rbrace>
   seL4_CNode_Mint dest_root (of_nat slot) (of_nat (object_size_bits spec_obj))
                   seL4_CapInitThreadCNode src_index 32 rights data
   \<lbrace>\<lambda>_.\<guillemotleft>object_slot_initialised spec t obj_id slot \<and>*
        si_cap_at t orig_caps spec dev (cap_object spec_cap) \<and>*
        si_cap_at t dup_caps spec dev obj_id \<and>*
        object_fields_empty spec t obj_id \<and>* si_objects \<and>* R\<guillemotright>\<rbrace>"
  supply ep_related_capI[intro, dest]
  apply (rule hoare_chain)
   apply (cut_tac cnode_cap = si_cspace_cap
              and cnode_cap' = si_cnode_cap
              and dest_root_cap = "default_cap CNodeType {dest_id} (object_size_bits spec_obj) False"
              and root_size=si_cnode_size
              and src_root=seL4_CapInitThreadCNode
              and src_depth=32
              and tcb=root_tcb
              and src_cap = "default_cap type {client_object_id} (object_size_bits spec_cap_obj) dev"
               in seL4_CNode_Mint_sep,
               (assumption|simp add: ep_cap_default_cap ntfn_cap_default_cap get_index_def
                 default_cap_has_type
                 ep_related_cap_badge_of_default[OF ep_related_capI(1)]
                 ep_related_cap_badge_of_default[OF ep_related_capI(2)])+)
    apply (frule_tac s=s and t=t and dup_caps=dup_caps and orig_caps=orig_caps
                 in mint_pre,(assumption|rule refl|simp)+)
   apply (elim conjE)
   (* FIXME: need to refactor ep_related_cap rules. For now, discharge these manually *)
   apply (subgoal_tac
            "(type = EndpointType \<longrightarrow>
                cap_badge (default_cap EndpointType {client_object_id}
                                       (object_size_bits spec_cap_obj) dev) = 0)
             \<and> (type = NotificationType \<longrightarrow>
                cap_badge (default_cap NotificationType {client_object_id}
                                       (object_size_bits spec_cap_obj) dev) = 0)")
    prefer 2
    apply (blast intro: ep_related_cap_badge_of_default)
   apply clarsimp
   apply (intro conjI,
     simp_all add:has_type_default_not_non ep_related_cap_default_cap
     valid_src_cap_if_cnode)
      apply ((clarsimp simp: si_cnode_cap_def word_bits_def si_cspace_cap_def
                      dest!: guard_equal_si_cspace_cap |
              rule is_cnode_cap_si_cnode_cap | sep_cancel)+)[2]
    apply (drule_tac s=s and dest_root=dest_root and src_index=src_index and R=R
                 in mint_post, (assumption|simp)+)
   apply sep_cancel+
   apply (subst default_cap_data_if_cnode[symmetric],simp+)
  done

lemma seL4_CNode_Mint_object_slot_initialised_sep:
  "\<lbrace>\<lambda>s. well_formed spec \<and> \<not> original_cap_at (obj_id, slot) spec \<and>
        rights = cap_rights spec_cap \<and> data = cap_data spec_cap \<and>
        cnode_at obj_id spec \<and> cdl_objects spec obj_id = Some spec_obj \<and>
        opt_cap (obj_id, slot) spec = Some spec_cap \<and> spec_cap \<noteq> NullCap \<and>
        \<not>is_untyped_cap spec_cap \<and>
        valid_src_cap spec_cap data \<and>
        cap_has_object spec_cap \<and>
        cap_has_type spec_cap \<and>
        is_device_cap spec_cap = dev \<and>
        cdl_objects spec (cap_object spec_cap) = Some spec_cap_obj \<and>
        (is_cnode_cap spec_cap \<longrightarrow> object_size_bits spec_cap_obj = cnode_cap_size spec_cap) \<and>
        Some dest_root = dup_caps obj_id \<and>
        Some src_index = orig_caps (cap_object spec_cap) \<and>
        \<guillemotleft>object_slot_empty spec t obj_id slot \<and>*
         si_cap_at t orig_caps spec dev (cap_object spec_cap) \<and>*
         si_cap_at t dup_caps spec dev obj_id \<and>*
         object_fields_empty spec t obj_id \<and>* si_objects \<and>* R\<guillemotright> s \<rbrace>
     seL4_CNode_Mint dest_root (of_nat slot) (of_nat (object_size_bits spec_obj))
                     seL4_CapInitThreadCNode src_index 32 rights data
   \<lbrace>\<lambda>_ s. \<guillemotleft>object_slot_initialised spec t obj_id slot \<and>*
           si_cap_at t orig_caps spec dev (cap_object spec_cap) \<and>*
           si_cap_at t dup_caps spec dev obj_id \<and>*
           object_fields_empty spec t obj_id \<and>* si_objects \<and>* R\<guillemotright> s\<rbrace>"
  apply (rule hoare_assume_pre)
  apply (elim conjE)
  apply (rule hoare_weaken_pre)
   apply clarsimp
   apply (rule_tac dest_id="the(t obj_id)" and client_object_id="the(t (cap_object spec_cap))"
                in seL4_CNode_Mint_object_slot_initialised_sep_helper, (assumption|simp)+)
      apply (clarsimp simp: si_cap_at_def sep_conj_exists)
     apply (clarsimp simp: si_cap_at_def sep_conj_exists)
(* Why doesn't sep_drule work when you don't mention s? *)
    apply (sep_drule (direct) si_cap_at_less_si_cnode_size [where cap_ptr = src_index
                 and R="object_slot_empty spec t obj_id slot \<and>* si_cap_at t dup_caps spec (is_device_cap spec_cap) obj_id \<and>* object_fields_empty spec t obj_id \<and>* si_objects \<and>* R"])
       apply (fastforce simp: sep_conj_ac)
      apply clarsimp
     apply (sep_drule (direct) si_cap_at_less_si_cnode_size [where cap_ptr = dest_root and t=t and spec=spec
                   and R="object_slot_empty spec t obj_id slot \<and>* si_cap_at t orig_caps spec (is_device_cap spec_cap) (cap_object spec_cap) \<and>* object_fields_empty spec t obj_id \<and>* si_objects \<and>* R"])
      apply (fastforce simp: sep_conj_ac)
     apply clarsimp+
  done

lemma init_cnode_slot_copy_not_original_sep_helper:
  "\<lbrakk>well_formed spec; cnode_at obj_id spec; \<not> original_cap_at (obj_id, slot) spec;
    original_cap_at (orig_obj_id, orig_slot) spec;
    opt_cap (obj_id, slot) spec = Some cap; cap \<noteq> NullCap;
    opt_cap (orig_obj_id, orig_slot) spec = Some orig_cap; orig_cap \<noteq> NullCap;
    cap_has_object cap; cap_has_object orig_cap; is_device_cap cap = dev;
    cap_object orig_cap = cap_object cap\<rbrakk> \<Longrightarrow>
   \<lbrace>\<guillemotleft>object_slot_empty spec t obj_id slot \<and>*
     si_obj_cap_at t orig_caps spec dev orig_obj_id orig_slot \<and>*
     si_cap_at t dup_caps spec dev obj_id \<and>*
     object_fields_empty spec t obj_id \<and>* si_objects \<and>* R\<guillemotright> \<rbrace>
   init_cnode_slot spec orig_caps dup_caps irq_caps Copy obj_id slot
   \<lbrace>\<lambda>_.\<guillemotleft>object_slot_initialised spec t obj_id slot \<and>*
        si_obj_cap_at t orig_caps spec dev orig_obj_id orig_slot \<and>*
        si_cap_at t dup_caps spec dev obj_id \<and>*
        object_fields_empty spec t obj_id \<and>* si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_assume_pre)
  apply (clarsimp simp: si_obj_cap_at_def si_obj_cap_at'_def)
  apply (frule well_formed_cap_object, assumption+)
  apply (clarsimp simp: init_cnode_slot_def cap_at_def)
  apply (wp seL4_CNode_Mint_object_slot_initialised_sep)+
  apply (wp seL4_CNode_Mint_object_slot_initialised_sep | clarsimp)+
  apply (intro impI conjI, simp_all)
     apply (erule (2) well_formed_is_untyped_cap)
    apply (metis cap_has_object_NullCap well_formed_cap_valid_src_cap well_formed_well_formed_cap')
   apply (metis well_formed_types_match)
  apply (erule well_formed_cnode_object_size_bits_eq)
   apply simp+
  done

lemma init_cnode_slot_copy_not_original_sep:
  "\<lbrakk>well_formed spec; obj_id \<in> cnodes; \<not> original_cap_at (obj_id, slot) spec;
    cnodes = {obj_id. cnode_at obj_id spec}; cap_at (\<lambda>c. is_device_cap c = dev) (obj_id, slot) spec\<rbrakk> \<Longrightarrow>
   \<lbrace>\<guillemotleft>object_slot_empty spec t obj_id slot \<and>*
     si_objs_caps_at t orig_caps spec dev cnodes \<and>*
     si_cap_at t dup_caps spec dev obj_id \<and>*
     object_fields_empty spec t obj_id \<and>* si_objects \<and>* R\<guillemotright>\<rbrace>
     init_cnode_slot spec orig_caps dup_caps irq_caps Copy obj_id slot
   \<lbrace>\<lambda>_. \<guillemotleft>object_slot_initialised spec t obj_id slot \<and>*
         si_objs_caps_at t orig_caps spec dev cnodes \<and>*
         si_cap_at t dup_caps spec dev obj_id \<and>*
         object_fields_empty spec t obj_id \<and>* si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_assume_pre)
  apply (clarsimp, rename_tac spec_obj)

  (* Case: opt_cap (obj_id, slot) spec = Some NullCap *)
  apply (case_tac "opt_cap (obj_id, slot) spec = Some NullCap")
   apply (clarsimp simp: init_cnode_slot_def si_obj_cap_at_def
                         si_obj_cap_at'_def sep_conj_exists)
   apply (frule opt_cap_cdl_objects)
   apply (wp | clarsimp)+
   apply (frule cnode_at_not_tcb_at)
   apply (subst (asm) object_slot_empty_initialised_NullCap, assumption+)
   apply (subst (asm) object_slot_empty_initialised_NullCap, assumption+)

  (* Case: opt_cap (obj_id, slot) spec = None *)
  apply (case_tac "opt_cap (obj_id, slot) spec = None")
   apply (clarsimp simp: init_cnode_slot_def)
   apply (wp|clarsimp)+
         apply (rule hoare_pre_cont)
        apply (wp|clarsimp)+

  (* Case: cap_at cap_has_object (obj_id, slot) spec *)
  apply (case_tac "cap_at cap_has_object (obj_id, slot) spec")
   apply (clarsimp simp: cap_at_def)
   apply (rename_tac cap)
   (* Rearrange to work with the sep_list_conj_map_singleton_wp rule. *)
   apply (rule hoare_chain[where P'="\<guillemotleft>(object_slot_empty spec t obj_id slot \<and>*
                                       si_cap_at t dup_caps spec dev obj_id \<and>*
                                       object_fields_empty spec t obj_id \<and>*
                                       si_objects) \<and>*
                                      si_objs_caps_at t orig_caps spec dev {obj_id. cnode_at obj_id spec} \<and>* R\<guillemotright>"
                          and Q="\<lambda>_. \<guillemotleft>(object_slot_initialised spec t obj_id slot \<and>*
                                       si_cap_at t dup_caps spec dev obj_id \<and>*
                                       object_fields_empty spec t obj_id \<and>*
                                       si_objects) \<and>*
                                      si_objs_caps_at t orig_caps spec dev {obj_id. cnode_at obj_id spec} \<and>* R\<guillemotright>"])
     apply (frule (3) well_formed_cdt)
     apply (clarsimp simp: si_objs_caps_at_def)
     apply (rule_tac x=orig_obj_id in sep_set_conj_map_singleton_wp, simp)
       apply (clarsimp simp: object_at_def)
     apply (clarsimp simp: si_obj_caps_at_def)
     apply (rule_tac x=orig_slot in sep_set_conj_map_singleton_wp, clarsimp+)
      apply (clarsimp simp: opt_cap_def)
      apply clarsimp
     apply (rule hoare_chain)
       apply (rule_tac orig_cap=orig_cap and cap=cap and R=Ra
              in init_cnode_slot_copy_not_original_sep_helper, (simp|sep_solve)+)
  (* Case: cap_at is_irqhandler_cap (obj_id, slot) spec *)
  apply (frule (3) well_formed_cap_no_object_irqhandler_cap)
  apply (clarsimp simp: original_cap_at_def)
  done

lemma init_cnode_slot_copy_sep:
  "\<lbrakk>well_formed spec; obj_id \<in> cnodes;cap_at (\<lambda>c. is_device_cap c = dev) (obj_id, slot) spec;
    cnodes = {obj_id. cnode_at obj_id spec}\<rbrakk> \<Longrightarrow>
   \<lbrace>\<guillemotleft>object_slot_empty spec t obj_id slot \<and>*
     si_objs_caps_at t orig_caps spec dev cnodes \<and>*
     si_cap_at t dup_caps spec dev obj_id \<and>*
     object_fields_empty spec t obj_id \<and>* si_objects \<and>* R\<guillemotright>\<rbrace>
   init_cnode_slot spec orig_caps dup_caps irq_caps Copy obj_id slot
   \<lbrace>\<lambda>_.\<guillemotleft>cnode_slot_half_initialised spec t obj_id slot \<and>*
        si_objs_caps_at t orig_caps spec dev cnodes \<and>*
        si_cap_at t dup_caps spec dev obj_id \<and>*
        object_fields_empty spec t obj_id \<and>* si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (case_tac "original_cap_at (obj_id, slot) spec")
   apply (wp init_cnode_slot_copy_original_sep, simp+)
   apply (subst cnode_slot_half_initialised_original_slot, simp+)
  apply (subst cnode_slot_half_initialised_not_original_slot, assumption+)
  apply (wp init_cnode_slot_copy_not_original_sep, simp+)
  done

lemma init_cnode_slots_copy_sep:
  "\<lbrakk>well_formed spec; obj_id \<in> cnodes;
    \<forall>slot\<in> dom (slots_of obj_id spec). cap_at (\<lambda>c. is_device_cap c = dev) (obj_id,slot) spec;
    cnodes = {obj_id. cnode_at obj_id spec}\<rbrakk> \<Longrightarrow>
   \<lbrace>\<guillemotleft>object_slots_empty spec t obj_id \<and>*
     si_objs_caps_at t orig_caps spec dev cnodes \<and>*
     si_cap_at t dup_caps spec dev obj_id \<and>*
     object_fields_empty spec t obj_id \<and>* si_objects \<and>* R\<guillemotright>\<rbrace>
   init_cnode spec orig_caps dup_caps irq_caps Copy obj_id
   \<lbrace>\<lambda>_.\<guillemotleft>cnode_slots_half_initialised spec t obj_id \<and>*
        si_objs_caps_at t orig_caps spec dev cnodes \<and>*
        si_cap_at t dup_caps spec dev obj_id \<and>*
        object_fields_empty spec t obj_id \<and>* si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_assume_pre)
  apply (simp add: init_cnode_def si_obj_caps_at_def)
  apply (frule_tac obj_id=obj_id and t=t in object_slots_empty_decomp)
  apply (frule_tac obj_id=obj_id and t=t in cnode_slots_half_initialised_decomp, fastforce+)
  apply simp
  apply (subst cnode_empty_slots_half_initialised_object_empty_slots_initialised)
  apply (subst object_empty_slots_empty_initialised, simp)
  apply (simp add: sep_conj_assoc)
  apply (rule hoare_chain)
    apply (rule_tac mapM_x_set_sep [where
               P="\<lambda>slot. object_slot_empty spec t obj_id slot" and
               Q="\<lambda>slot. cnode_slot_half_initialised spec t obj_id slot" and
               I="si_objs_caps_at t orig_caps spec dev cnodes \<and>*
                  si_cap_at t dup_caps spec dev obj_id \<and>*
                  object_fields_empty spec t obj_id \<and>*
                  si_objects \<and>* object_empty_slots_initialised spec t obj_id" and
               xs="slots_of_list spec obj_id",
               simplified sep_conj_assoc])
    apply (clarsimp simp: sep_conj_assoc)
    apply (wp init_cnode_slot_copy_sep, (simp add: dom_def | sep_solve)+)
  done

lemma init_cnode_copy_sep:
  "\<lbrakk>well_formed spec; obj_id \<in> cnodes;
    \<forall>slot\<in> dom (slots_of obj_id spec). cap_at (\<lambda>c. is_device_cap c = dev) (obj_id,slot) spec;
    cnodes = {obj_id. cnode_at obj_id spec}\<rbrakk> \<Longrightarrow>
   \<lbrace>\<guillemotleft>object_empty spec t obj_id \<and>*
     si_objs_caps_at t orig_caps spec dev cnodes \<and>*
     si_cap_at t dup_caps spec dev obj_id \<and>*
     si_objects \<and>* R\<guillemotright>\<rbrace>
   init_cnode spec orig_caps dup_caps irq_caps Copy obj_id
   \<lbrace>\<lambda>_.\<guillemotleft>cnode_half_initialised spec t obj_id \<and>*
        si_objs_caps_at t orig_caps spec dev cnodes \<and>*
        si_cap_at t dup_caps spec dev obj_id \<and>*
        si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_assume_pre)
  apply (subst object_empty_decomp, subst cnode_half_initialised_decomp)
  apply (subst object_fields_empty_half_initialised, simp+)
  apply (rule hoare_chain)
    apply (rule_tac R=R and t=t and cnodes=cnodes in init_cnode_slots_copy_sep, (simp|sep_solve)+)
  done

lemma init_cspace_copy_sep:
  "\<lbrace>\<guillemotleft>objects_empty spec t cnode_set \<and>*
     si_objs_caps_at t orig_caps spec dev cnode_set \<and>*
     si_spec_irqs_caps_at irq_caps spec cnode_set \<and>*
     si_caps_at t dup_caps spec dev cnode_set \<and>*
     si_objects \<and>* R\<guillemotright> and K(
    well_formed spec \<and>
    distinct cnode_list \<and> cnode_set = set cnode_list \<and>
    set cnode_list = {obj_id. cnode_at obj_id spec}
    \<and> (\<forall>obj_id\<in>cnode_set. \<forall>slot\<in> dom (slots_of obj_id spec). cap_at (\<lambda>c. is_device_cap c = dev) (obj_id,slot) spec))\<rbrace>
   mapM_x (init_cnode spec orig_caps dup_caps irq_caps Copy) cnode_list
   \<lbrace>\<lambda>_.\<guillemotleft>cnodes_half_initialised spec t cnode_set \<and>*
        si_objs_caps_at t orig_caps spec dev cnode_set \<and>*
        si_spec_irqs_caps_at irq_caps spec cnode_set \<and>*
        si_caps_at t dup_caps spec dev cnode_set \<and>*
        si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (clarsimp simp: cnodes_half_initialised_def objects_empty_def
                        si_caps_at_def)
  apply (rule hoare_name_pre_state)
  apply (rule hoare_chain)
    apply (rule_tac R=R in
               mapM_x_set_sep [where
               P="\<lambda>obj_id. object_empty spec t obj_id \<and>*
                  si_cap_at t dup_caps spec dev obj_id" and
               Q="\<lambda>obj_id. cnode_half_initialised spec t obj_id \<and>*
                  si_cap_at t dup_caps spec dev obj_id" and
               I="si_spec_irqs_caps_at irq_caps spec (set cnode_list) \<and>*
                  si_objs_caps_at t orig_caps spec dev (set cnode_list) \<and>*
                  si_objects"  and
               xs="cnode_list",
               simplified sep_conj_assoc], simp+)
    apply (rule hoare_chain)
    apply (rule init_cnode_copy_sep [where t=t and cnodes="set cnode_list" and dev = dev],simp+)
    apply sep_solve
   apply clarsimp
   apply sep_solve
   apply (subst sep.prod.distrib)+
   apply clarsimp
   apply sep_solve
  apply (subst (asm) sep.prod.distrib)+
  apply clarsimp
  apply sep_solve
  done

lemma init_cspace_sep':
  "\<lbrace>\<guillemotleft>objects_empty spec t cnodes \<and>*
     si_objs_caps_at t orig_caps spec dev cnodes \<and>*
     si_spec_irqs_caps_at irq_caps spec cnodes \<and>*
     si_caps_at t dup_caps spec dev cnodes \<and>*
     si_objects \<and>* R\<guillemotright> and K(
     well_formed spec \<and>
     set obj_ids = dom (cdl_objects spec) \<and>
     distinct obj_ids \<and>
     cnodes = {obj_id. cnode_at obj_id spec} \<and>
     (\<forall>obj_id\<in> cnodes. \<forall>slot\<in> dom (slots_of obj_id spec). cap_at (\<lambda>c. is_device_cap c = dev) (obj_id,slot) spec))\<rbrace>
   init_cspace spec orig_caps dup_caps irq_caps obj_ids
   \<lbrace>\<lambda>_.\<guillemotleft>objects_initialised spec t cnodes \<and>*
        si_spec_objs_null_caps_at t orig_caps spec cnodes \<and>*
        si_spec_irqs_null_caps_at irq_caps spec cnodes \<and>*
        si_caps_at t dup_caps spec dev cnodes \<and>*
        si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (unfold init_cspace_def)
  apply (wp init_cspace_move_sep)
    apply (wp init_cspace_copy_sep)+
  apply simp
  done

lemma hoare_subst:
  "\<lbrakk>\<lbrace>A\<rbrace> f \<lbrace>C\<rbrace>; A = B; C = D\<rbrakk> \<Longrightarrow> \<lbrace>B\<rbrace> f \<lbrace>D\<rbrace>"
  by simp


lemma si_caps_at_filter:
  "si_caps_at t si_caps spec dev (set xs) =
  (si_caps_at t si_caps spec dev (set [x\<leftarrow>xs. P x]) \<and>* si_caps_at t si_caps spec dev (set [x\<leftarrow>xs. \<not>P x]))"
  apply (clarsimp simp: si_caps_at_def)
  apply (subst sep.prod.union_disjoint [symmetric], (fastforce simp: union_filter)+)
  done

lemma si_caps_at_restrict:
  "si_caps_at t si_caps spec dev xs =
  (si_caps_at t si_caps spec dev {x \<in> xs. P x} \<and>* si_caps_at t si_caps spec dev {x \<in> xs. \<not>P x})"
  by (clarsimp simp: si_caps_at_def sep_map_set_conj_restrict)

lemma length_Un_disjoint:
  "\<lbrakk>distinct zs; distinct xs; distinct ys;
   set xs \<union> set ys = set zs; set xs \<inter> set ys = {}\<rbrakk>
  \<Longrightarrow> length xs + length ys = length zs"
  by (metis List.finite_set card_Un_disjoint distinct_card)

lemma set_take_add:
  "\<lbrakk>i+j \<le> length zs; i + j = k\<rbrakk> \<Longrightarrow>
   set (take i zs) \<union> set (take j (drop i zs)) = set (take k zs)"
  by (metis set_append take_add)

lemma wellformed_no_dev:
  "well_formed spec \<Longrightarrow>(\<forall>obj_id. cnode_at obj_id spec \<longrightarrow>
                       (\<forall>slot\<in>dom (slots_of obj_id spec). cap_at (\<lambda>c. is_device_cap c = False) (obj_id, slot) spec))"
   apply (simp add: well_formed_def cap_at_def del:split_paired_All)
   apply (intro allI impI ballI)
   apply  (clarsimp simp: dom_def slots_of_def opt_cap_def)
   done

lemma init_cspace_sep:
  "\<lbrace>\<guillemotleft>objects_empty spec t {obj_id. cnode_at obj_id spec} \<and>*
     si_caps_at t orig_caps spec False {obj_id. real_object_at obj_id spec} \<and>*
     si_irq_caps_at irq_caps spec (used_irqs spec) \<and>*
     si_caps_at t dup_caps spec False {obj_id. cnode_or_tcb_at obj_id spec} \<and>*
     si_objects \<and>* R\<guillemotright> and K(
     well_formed spec \<and>
     set obj_ids = dom (cdl_objects spec) \<and>
     distinct obj_ids \<and>
     distinct free_cptrs \<and>
     orig_caps = map_of (zip [obj\<leftarrow>obj_ids. real_object_at obj spec] free_cptrs) \<and>
     irq_caps = map_of (zip (used_irq_list spec) (drop (card {obj_id. real_object_at obj_id spec}) free_cptrs)) \<and>
     length obj_ids \<le> length free_cptrs
     )\<rbrace>
   init_cspace spec orig_caps dup_caps irq_caps obj_ids
   \<lbrace>\<lambda>_. \<guillemotleft>objects_initialised spec t {obj_id. cnode_at obj_id spec} \<and>*
        (\<And>* cptr \<in> set (take (card (dom (cdl_objects spec))) free_cptrs). (si_cnode_id, unat cptr) \<mapsto>c NullCap) \<and>*
         si_caps_at t dup_caps spec False {obj_id. cnode_or_tcb_at obj_id spec} \<and>*
         si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_gen_asm, clarsimp)
  apply (frule well_formed_inj_cdl_irq_node)
  apply (frule well_formed_objects_real_or_irq)
  apply (frule well_formed_objects_only_real_or_irq)
  apply (frule well_formed_objects_card)
  apply (insert distinct_card [where xs = obj_ids], clarsimp)
  apply (insert distinct_card [where xs = "[obj\<leftarrow>obj_ids . real_object_at obj spec]", symmetric], clarsimp)
  apply (subst si_caps_at_conversion [where
               real_ids  = "{obj_id. real_object_at obj_id spec}" and
               cnode_ids = "{obj_id. cnode_at obj_id spec}", symmetric], simp+)
  apply (subst si_irq_caps_at_conversion [where
               irqs = "used_irqs spec" and
               cnode_ids = "{obj_id. cnode_at obj_id spec}", symmetric], simp+)
  apply (subst si_caps_at_restrict [where P="\<lambda>ref. cnode_at ref spec" and
                                           xs="{obj_id. cnode_or_tcb_at obj_id spec}"])+
  apply (wp sep_wp: init_cspace_sep'[where t=t and dev=False and cnodes="set [obj\<leftarrow>obj_ids. cnode_at obj spec]"])
  apply (clarsimp simp: cnode_or_tcb_at_simps wellformed_no_dev)
  apply (frule wellformed_no_dev)
   apply simp
  apply sep_cancel+
  apply (sep_drule si_null_caps_at_simplified [where
                       obj_ids = "[obj\<leftarrow>obj_ids. real_object_at obj spec]"
                   and real_ids = "{obj_id. real_object_at obj_id spec}"
                   and free_cptrs = free_cptrs], simp+)
  apply (sep_drule si_irq_null_caps_at_simplified [where
                       free_cptrs="drop (card {obj_id. real_object_at obj_id spec}) free_cptrs"
                   and irqs="used_irq_list spec"], simp+)
  apply (subst (asm) sep.prod.union_disjoint [symmetric], simp+)
   apply (metis (no_types) distinct_append distinct_take_strg inf_sup_aci(1) take_add)
  apply (erule sep_map_set_conj_set_cong[THEN fun_cong, THEN iffD1, rotated])
  apply clarsimp
  apply (subst Un_commute, subst set_take_add, (simp add: add.commute)+)
  done

end

