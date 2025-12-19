(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
 * Well formed constraints of what capDL specifications the system-initialiser can initialise.
 *
 * There are two types of constraints:
 *   - fundamental ones (such as that specs must be finite),
 *     and other seL4 limitations (such as that page tables can't be shared).
 *   - limitations of the initialiser.
 *
 * The latter are commented with LIMITATION.
 *)

theory WellFormed_SI
imports
  "DSpecProofs.Kernel_DP"
  "SepDSpec.Separation_SD"
  "Lib.SimpStrategy"
  "AInvs.Rights_AI"
begin

context begin interpretation Arch . (*FIXME: arch-split*)

lemma cap_has_object_NullCap [simp]:
  "\<not>cap_has_object NullCap"
  by (clarsimp simp: cap_has_object_def)

lemma cap_has_object_not_NullCap:
  "cap_has_object cap \<Longrightarrow> cap \<noteq> NullCap"
  by clarsimp

lemma is_irqhandler_cap_not_NullCap:
  "is_irqhandler_cap cap \<Longrightarrow> cap \<noteq> NullCap"
  by clarsimp

lemma cap_has_object_not_irqhandler_cap:
  "cap_has_object cap \<Longrightarrow> \<not> is_irqhandler_cap cap"
   by (clarsimp simp: cap_has_object_def cap_type_def
               split: cdl_cap.splits)

lemmas cap_has_object_not_irqhandler_cap_simp[simp] = cap_has_object_not_irqhandler_cap[OF ByAssum]
lemmas cap_has_object_not_NullCap_simp[simp] = cap_has_object_not_NullCap[OF ByAssum]
lemmas is_irqhandler_cap_not_NullCap_simp[simp] = is_irqhandler_cap_not_NullCap[OF ByAssum]







definition
  cap_ref_object :: "cdl_cap_ref \<Rightarrow> cdl_state \<Rightarrow> cdl_object_id"
where
  "cap_ref_object cap_ref s \<equiv> cap_object (the (opt_cap cap_ref s))"

definition
  cap_ref_irq :: "cdl_cap_ref \<Rightarrow> cdl_state \<Rightarrow> cdl_irq"
where
  "cap_ref_irq cap_ref s \<equiv> cap_irq (the (opt_cap cap_ref s))"

definition real_cap_ref :: "cdl_cap_ref \<Rightarrow> cdl_state \<Rightarrow> bool"
where
  "real_cap_ref cap_ref s \<equiv> \<exists>cap. opt_cap cap_ref s = Some cap \<and> cap \<noteq> NullCap \<and>
                                  cnode_at (fst cap_ref) s"

definition object_cap_ref :: "cdl_cap_ref \<Rightarrow> cdl_state \<Rightarrow> bool"
where
  "object_cap_ref cap_ref s \<equiv> \<exists>cap. opt_cap cap_ref s = Some cap \<and>
                                     cap_has_object cap \<and>
                                     cnode_at (fst cap_ref) s"

(* MOVE ME *)
definition "guard_bits = (18::nat)"

lemma guard_less_guard_bits:
  "\<lbrakk>guard_size < guard_bits; (g::word32) < 2 ^ guard_size\<rbrakk> \<Longrightarrow>
   g < 2 ^ guard_bits"
  apply (erule less_le_trans)
  apply (rule two_power_increasing, simp)
  apply (clarsimp simp: guard_bits_def)
  done

lemma guard_size_shiftl_non_zero:
  "\<lbrakk>guard_size < guard_bits; guard_size \<noteq> 0\<rbrakk> \<Longrightarrow>
  ((of_nat guard_size)::word32) << 3 \<noteq> 0"
  apply (rule word_shift_nonzero [where m=guard_bits])
    apply clarsimp
    apply (rule order_less_imp_le)
    apply (rule guard_less_guard_bits, assumption)
    apply (insert n_less_equal_power_2 [where n=guard_size])
    apply clarsimp
    apply (rule of_nat_n_less_equal_power_2)
    apply (clarsimp simp: guard_bits_def)
   apply (clarsimp simp: guard_bits_def)
  apply (clarsimp simp: of_nat_0 simp del: word_of_nat_eq_0_iff)
  apply (drule of_nat_0)
   apply (erule less_le_trans)
   apply (clarsimp simp: guard_bits_def word_bits_def)
  apply clarsimp
  done

(* End of MOVE ME
 *)
definition well_formed_cap :: "cdl_cap \<Rightarrow> bool"
where
  "well_formed_cap cap \<equiv> (case cap of
      EndpointCap _ b _       \<Rightarrow> b < 2 ^ badge_bits
    | NotificationCap _ b r  \<Rightarrow> (b < 2 ^ badge_bits) \<and> (r \<subseteq> {AllowRead, AllowWrite})
    | CNodeCap _ g gs sz      \<Rightarrow> (gs < guard_bits) \<and> (g < 2 ^ gs) \<and> (sz + gs \<le> 32)
    | TcbCap _                \<Rightarrow> True
    | FrameCap _ _ r _ _ ad     \<Rightarrow> r \<in> {vm_read_write, vm_read_only} \<and> ad = None
    | PageTableCap  _ _ ad    \<Rightarrow> ad = None
    | PageDirectoryCap _ _ ad \<Rightarrow> ad = None
    | IrqHandlerCap _         \<Rightarrow> True
\<comment> \<open>LIMITATION: The following should probably eventually be true.\<close>
    | IrqControlCap           \<Rightarrow> False
    | UntypedCap _ _ _          \<Rightarrow> False
    | AsidControlCap          \<Rightarrow> False
    | AsidPoolCap _ _         \<Rightarrow> False
    | SGISignalCap _ _        \<Rightarrow> False \<comment> \<open>FIXME SGI: eventually allow this\<close>
    | _                       \<Rightarrow> False)"

(* LIMITATION: The specification cannot contain ASID numbers. *)
definition vm_cap_has_asid :: "cdl_cap \<Rightarrow> bool"
where
  "vm_cap_has_asid cap \<equiv>
       (case cap of
           FrameCap _ _ _ _ _ ad     \<Rightarrow> ad \<noteq> None
         | PageTableCap _ _ ad     \<Rightarrow> ad \<noteq> None
         | PageDirectoryCap _ _ ad \<Rightarrow> ad \<noteq> None
         | _                       \<Rightarrow> False)"

(* Original caps must have default rights,
 * and original endpoint + notification caps must not be badged.
 *)
definition
  is_copyable_cap :: "cdl_cap \<Rightarrow> bool"
where
  "is_copyable_cap cap \<equiv> \<not> is_irqhandler_cap cap"

definition
   well_formed_orig_cap :: "cdl_cap \<Rightarrow> bool"
where
  "well_formed_orig_cap cap \<equiv>
  (cap_has_type cap \<longrightarrow> cap_rights (default_cap (the (cap_type cap)) undefined undefined undefined)
                      = cap_rights cap) \<and>
  (ep_related_cap cap \<longrightarrow> cap_badge cap = 0)"

definition
  well_formed_cdt :: "cdl_state \<Rightarrow> cdl_cap_ref \<Rightarrow> cdl_cap \<Rightarrow> bool"
where
  "well_formed_cdt spec cap_ref cap \<equiv>
    cnode_at (fst cap_ref) spec \<longrightarrow>
    cap_has_object cap \<longrightarrow>
    (\<exists>orig_obj_id orig_slot orig_cap.
    cnode_at orig_obj_id spec \<and>
    (\<exists>obj. cdl_objects spec (cap_object cap) = Some obj) \<and>
    original_cap_at (orig_obj_id, orig_slot) spec \<and>
    opt_cap (orig_obj_id, orig_slot) spec = Some orig_cap \<and>
    cap_has_object orig_cap \<and> cap_object orig_cap = cap_object cap)"

(* MOVEME *)
lemma well_formed_cdt_irqhandler_cap:
  "is_irqhandler_cap cap \<Longrightarrow> well_formed_cdt spec cap_ref cap"
  by (clarsimp simp: well_formed_cdt_def split: cdl_cap.splits)


(* The only thing that points to IRQ objects is the IRQ table (not a cap). *)
definition
  well_formed_cap_to_real_object :: "cdl_state \<Rightarrow> cdl_cap \<Rightarrow> bool"
where
  "well_formed_cap_to_real_object spec cap \<equiv>
    cap_has_object cap \<longrightarrow> real_object_at (cap_object cap) spec"

definition
  well_formed_cap_types_match :: "cdl_state \<Rightarrow> cdl_cap \<Rightarrow> bool"
where
  "well_formed_cap_types_match spec cap \<equiv>
    (cap_has_object cap \<longrightarrow>
    (\<exists>cap_obj. cdl_objects spec (cap_object cap) = Some cap_obj \<and>
               cap_type cap = Some (object_type cap_obj))) \<and>
    (is_irqhandler_cap cap \<longrightarrow>
    (\<exists>cap_obj. cdl_objects spec (cdl_irq_node spec (cap_irq cap)) = Some cap_obj \<and>
               cap_type cap = Some (object_type cap_obj)))"

definition well_formed_caps :: "cdl_state \<Rightarrow> cdl_object_id \<Rightarrow> cdl_object \<Rightarrow> bool"
where
  "well_formed_caps spec obj_id obj \<equiv> \<forall>slot cap.
     object_slots obj slot = Some cap \<longrightarrow>
     cap \<noteq> NullCap \<longrightarrow>
        (well_formed_cap cap \<and>
        (original_cap_at (obj_id, slot) spec \<longrightarrow> well_formed_orig_cap cap) \<and>
        (\<not>original_cap_at (obj_id, slot) spec \<longrightarrow> is_copyable_cap cap) \<and>
         well_formed_cdt spec (obj_id, slot) cap \<and>
         well_formed_cap_to_real_object spec cap \<and>
         well_formed_cap_types_match spec cap \<and>
        ((is_cnode obj \<or> is_tcb obj) \<longrightarrow> (\<not> is_fake_vm_cap cap)))"

definition
  well_formed_cap_to_object :: "cdl_state \<Rightarrow> cdl_object_id \<Rightarrow> cdl_object \<Rightarrow> bool"
where
  "well_formed_cap_to_object spec obj_id obj \<equiv> (\<exists>cnode_id slot cap.
    opt_cap (cnode_id, slot) spec = Some cap \<and>
    original_cap_at (cnode_id, slot) spec \<and>
    cnode_at cnode_id spec \<and>
    (real_object_at obj_id spec \<longrightarrow> cap_object cap = obj_id \<and> cap_has_object cap) \<and>
    (\<not>real_object_at obj_id spec \<longrightarrow> is_irqhandler_cap cap \<and> cdl_irq_node spec (cap_irq cap) = obj_id)) \<and>

    (\<forall>slot cap. (opt_cap slot spec = Some cap \<and> is_cnode_cap cap \<and> cap_object cap = obj_id)
     \<longrightarrow> object_size_bits obj = cnode_cap_size cap)"

(* For every IRQ object that has a cap in it,
 * there should be an IRQ handler cap to that object.
 * There can be more IRQ handler caps than this,
 * but every object must have a cap to it.
 *)
definition
  well_formed_irqhandler_caps :: "cdl_state \<Rightarrow> bool"
where
  "well_formed_irqhandler_caps spec \<equiv> (\<forall>irq. irq \<in> bound_irqs spec \<longrightarrow>
    (\<exists>cnode_id slot cap. opt_cap (cnode_id, slot) spec = Some cap \<and>
                         is_irqhandler_cap cap \<and>
                         cap_irq cap = irq))"

definition
  well_formed_orig_caps_unique :: "cdl_state \<Rightarrow> bool"
where
  "well_formed_orig_caps_unique spec \<equiv> \<forall>obj_id obj_id' slot slot' cap cap'.
      cnode_at obj_id spec \<longrightarrow>
      cnode_at obj_id' spec \<longrightarrow>
      cap_has_object cap \<longrightarrow>
      cap_has_object cap' \<longrightarrow>
      opt_cap (obj_id, slot) spec = Some cap \<longrightarrow>
      opt_cap (obj_id', slot') spec = Some cap' \<longrightarrow>
      cap \<noteq> NullCap \<longrightarrow> original_cap_at (obj_id, slot) spec \<longrightarrow>
      cap' \<noteq> NullCap \<longrightarrow> original_cap_at (obj_id', slot') spec \<longrightarrow>
      cap_object cap = cap_object cap' \<longrightarrow>
      (obj_id = obj_id' \<and> slot = slot')"

definition
  well_formed_irqhandler_caps_unique :: "cdl_state \<Rightarrow> bool"
where
  "well_formed_irqhandler_caps_unique spec \<equiv> \<forall>obj_id obj_id' slot slot' cap cap'.
      opt_cap (obj_id, slot) spec = Some cap \<longrightarrow>
      opt_cap (obj_id', slot') spec = Some cap' \<longrightarrow>
      is_irqhandler_cap cap \<longrightarrow>
      is_irqhandler_cap cap' \<longrightarrow>
      cap_irq cap = cap_irq cap' \<longrightarrow>
      (obj_id = obj_id' \<and> slot = slot')"

definition well_formed_tcb :: "cdl_state \<Rightarrow> cdl_object_id \<Rightarrow> cdl_object \<Rightarrow> bool"
where
  "well_formed_tcb spec obj_id obj \<equiv>
     is_tcb obj \<longrightarrow>
     \<not> tcb_has_fault obj \<and>
     tcb_domain obj = minBound \<and>
     (\<forall>slot cap. object_slots obj slot = Some cap \<longrightarrow>
     ((slot = tcb_cspace_slot \<longrightarrow> is_cnode_cap cap \<and>
                                  cap_guard_size cap \<noteq> 0 \<and>
                                  cap_object cap \<notin> irq_nodes spec) \<and>
      (slot = tcb_vspace_slot \<longrightarrow> is_pd_cap cap) \<and>
      (slot = tcb_ipcbuffer_slot \<longrightarrow> is_frame_cap cap \<and> is_default_cap cap) \<and>
      (slot = tcb_replycap_slot \<longrightarrow> cap = NullCap \<or> cap = MasterReplyCap obj_id) \<and>
      (slot = tcb_caller_slot \<longrightarrow> cap = NullCap) \<and>
      (slot = tcb_pending_op_slot \<longrightarrow> cap = NullCap \<or> cap = RestartCap) \<and>
      (slot = tcb_boundntfn_slot \<longrightarrow> cap = NullCap) )) \<and>
     ((object_slots obj tcb_replycap_slot = Some (MasterReplyCap obj_id)) =
      (object_slots obj tcb_pending_op_slot = Some RestartCap))"

definition
  well_formed_fake_pt_caps_unique :: "cdl_state \<Rightarrow> bool"
where
  "well_formed_fake_pt_caps_unique spec \<equiv> \<forall>obj_id obj_id' slot slot' cap cap'.
      pd_at obj_id spec \<longrightarrow>
      pd_at obj_id' spec \<longrightarrow>
      opt_cap (obj_id, slot) spec = Some cap \<longrightarrow>
      opt_cap (obj_id', slot') spec = Some cap' \<longrightarrow>
      cap \<noteq> NullCap \<longrightarrow> is_fake_pt_cap cap \<longrightarrow>
      cap' \<noteq> NullCap \<longrightarrow> is_fake_pt_cap cap' \<longrightarrow>
      cap_object cap = cap_object cap' \<longrightarrow> (obj_id = obj_id' \<and> slot = slot')"

definition
  well_formed_cap_to_non_empty_pt :: "cdl_state \<Rightarrow> cdl_object_id \<Rightarrow> cdl_object \<Rightarrow> bool"
where
  "well_formed_cap_to_non_empty_pt spec obj_id obj \<equiv>
   pt_at obj_id spec \<longrightarrow>
   object_default_state obj \<noteq> obj \<longrightarrow>
   (\<exists>pd_id slot cap.
     opt_cap (pd_id, slot) spec = Some cap \<and>
     pd_at pd_id spec \<and>
     cap_object cap = obj_id \<and>
     cap_has_object cap)"

definition well_formed_vspace :: "cdl_state \<Rightarrow> cdl_object_id \<Rightarrow> cdl_object \<Rightarrow> bool"
where
  "well_formed_vspace spec obj_id obj \<equiv>
   well_formed_cap_to_non_empty_pt spec obj_id obj \<and>
   (\<forall>slot cap.
     (is_pt obj \<longrightarrow>
      object_slots obj slot = Some cap \<longrightarrow>
      cap \<noteq> NullCap \<longrightarrow> (\<exists>sz. cap_type cap = Some (FrameType sz) \<and> (sz = 12 \<or> sz = 16) \<and> is_fake_vm_cap cap)
      ) \<and>
     (is_pd obj \<longrightarrow>
      object_slots obj slot = Some cap \<longrightarrow>
      cap \<noteq> NullCap \<longrightarrow>
      (is_fake_pt_cap cap \<or>
         (\<exists>sz. cap_type cap = Some (FrameType sz) \<and> (sz = 20 \<or> sz = 24) \<and> is_fake_vm_cap cap) )))"

(* LIMITATION: The caps in a IRQ Node must have full permissions and be unbadged. *)
definition well_formed_irq_node :: "cdl_state \<Rightarrow> cdl_object_id \<Rightarrow> cdl_object \<Rightarrow> bool"
where
  "well_formed_irq_node spec obj_id obj \<equiv> \<forall>slot cap.
     obj_id \<in> irq_nodes spec \<longrightarrow>
     dom (object_slots obj) = {0} \<and>
     (object_slots obj slot = Some cap \<longrightarrow>
     (cap \<noteq> NullCap \<longrightarrow> (is_ntfn_cap cap \<and> is_default_cap cap)))"

definition well_formed_irq_table :: "cdl_state \<Rightarrow> bool"
where
  "well_formed_irq_table spec \<equiv> inj (cdl_irq_node spec) \<and>
                                irq_nodes spec = {obj_id. \<exists>irq. cdl_irq_node spec irq = obj_id \<and>
                                                                obj_id \<in> dom (cdl_objects spec)}"

definition
  well_formed :: "cdl_state \<Rightarrow> bool"
where
  "well_formed spec \<equiv> well_formed_orig_caps_unique spec \<and>
                      well_formed_irqhandler_caps_unique spec \<and>
                      well_formed_fake_pt_caps_unique spec \<and>
                      well_formed_irqhandler_caps spec \<and>
                      well_formed_irq_table spec \<and>
  (\<forall>obj_id.
    case cdl_objects spec obj_id of
        Some obj \<Rightarrow> well_formed_caps spec obj_id obj \<and>
                    well_formed_cap_to_object spec obj_id obj \<and>
                    well_formed_tcb spec obj_id obj \<and>
                    well_formed_vspace spec obj_id obj \<and>
                    well_formed_irq_node spec obj_id obj \<and>
                    object_size_bits obj < word_bits \<and>
                    object_size_bits (object_default_state obj) = object_size_bits obj \<and>
                    dom (object_slots (object_default_state obj)) = dom (object_slots obj) \<and>
                    (cnode_at obj_id spec \<longrightarrow> 0 < object_size_bits obj)
      | None \<Rightarrow> True)
  \<and> (\<forall>slot. \<not> cap_at (\<lambda>c. is_device_cap c = True) slot spec)"

lemma dom_cap_map [simp]:
  "dom (\<lambda>n. if n \<le> N then Some a else None) = {0::nat .. N}"
  by (rule, clarsimp simp: dom_def)+

lemma dom_cap_map' [simp]:
  "dom (\<lambda>n. if n < N then Some a else None) = {0::nat ..< N}"
  by (rule, clarsimp simp: dom_def)+

(*******************************
 * Rules about well_formed_cap. *
 *******************************)

lemma well_formed_cap_cap_has_object_eq:
  "\<lbrakk>well_formed_cap cap; cap_has_object cap; cap_type cap = cap_type cap'\<rbrakk> \<Longrightarrow> cap_has_object cap'"
  by (clarsimp simp: well_formed_cap_def cap_type_def cap_has_object_def split: cdl_cap.splits)+

lemma well_formed_cap_update_cap_objects [simp]:
  "is_untyped_cap cap
   \<Longrightarrow> well_formed_cap (update_cap_objects x cap) = well_formed_cap cap"
  apply (clarsimp simp: update_cap_object_def
                        update_cap_objects_def well_formed_cap_def)
  apply (cases cap, simp_all)
  done

lemma well_formed_cap_update_cap_object [simp]:
  "well_formed_cap (update_cap_object x cap) = well_formed_cap cap"
  apply (clarsimp simp: update_cap_object_def well_formed_cap_def)
  apply (cases cap, simp_all add:is_default_cap_def cap_type_def cap_badge_def default_cap_def)
  done

lemma cap_rights_inter_default_cap_rights:
  "\<lbrakk>well_formed_cap cap; cap_type cap = Some type\<rbrakk>
   \<Longrightarrow> cap_rights (default_cap type ids sz dev) \<inter> cap_rights cap = cap_rights cap"
  by (fastforce simp: well_formed_cap_def default_cap_def cap_type_def cap_rights_def
                      validate_vm_rights_def vm_read_write_def
                      vm_kernel_only_def vm_read_only_def
               split: cdl_cap.splits cdl_object_type.splits)

lemma well_formed_cap_derived_cap [simp]:
  "\<lbrakk>well_formed_cap cap; \<not> vm_cap_has_asid cap\<rbrakk> \<Longrightarrow> derived_cap cap = cap"
  by (clarsimp simp: well_formed_cap_def vm_cap_has_asid_def derived_cap_def not_Some_eq_tuple
              split: cdl_cap.splits)

(*********************************
 * Rules about well_formed spec. *
 *********************************)
lemma dom_if_0 [simp]:
  "dom (\<lambda>a. if a = 0 then Some b else None) = {0}"
  by (auto split: if_split_asm)

lemma well_formed_finite [elim!]:
  "well_formed spec \<Longrightarrow> finite (dom (slots_of obj_id spec))"
  apply (clarsimp simp: well_formed_def)
  apply (erule_tac x=obj_id in allE)
  apply (clarsimp simp: slots_of_def split: option.splits)
  apply (rename_tac obj)
  apply (drule_tac t="dom (object_slots obj)" in sym) (* Makes rewriting work. *)
  apply (clarsimp simp: object_default_state_def2 object_slots_def dom_expand
                        default_tcb_def tcb_pending_op_slot_def
                        empty_cnode_def empty_irq_node_def empty_cap_map_def
                 split: cdl_object.splits)
  done

lemma well_formed_finite_object_slots:
  "\<lbrakk>well_formed spec; cdl_objects spec obj_id = Some obj\<rbrakk> \<Longrightarrow> finite (dom (object_slots obj))"
  apply (drule well_formed_finite [where obj_id=obj_id])
  apply (clarsimp simp: slots_of_def)
  done

lemma well_formed_distinct_slots_of_list [elim!]:
  "well_formed spec \<Longrightarrow> distinct (slots_of_list spec obj_id)"
  by (clarsimp simp: slots_of_list_def object_slots_list_def tcb_slot_defs
               split: option.splits cdl_object.splits)

lemma well_formed_object_size_bits:
  "\<lbrakk>well_formed spec; cdl_objects spec obj_id = Some obj\<rbrakk>
   \<Longrightarrow> object_size_bits (object_default_state obj) = object_size_bits obj"
  apply (clarsimp simp: well_formed_def)
  apply (erule_tac x=obj_id in allE)
  apply (clarsimp)
  done

lemma well_formed_well_formed_caps:
  "\<lbrakk>well_formed spec; cdl_objects spec obj_id = Some obj\<rbrakk>
   \<Longrightarrow> well_formed_caps spec obj_id obj"
  by (clarsimp simp: well_formed_def split: option.splits)

lemma well_formed_well_formed_cap:
  "\<lbrakk>well_formed spec; cdl_objects spec obj_id = Some obj;
    object_slots obj slot = Some cap; cap \<noteq> NullCap\<rbrakk>
   \<Longrightarrow> well_formed_cap cap"
  apply (clarsimp simp: well_formed_def)
  apply (erule_tac x=obj_id in allE)
  apply (clarsimp simp: well_formed_caps_def)
  done

lemma well_formed_well_formed_cap':
  "\<lbrakk>well_formed spec; opt_cap (obj_id, slot) spec = Some cap; cap \<noteq> NullCap\<rbrakk> \<Longrightarrow>
  well_formed_cap cap"
  apply (frule opt_cap_dom_cdl_objects)
  apply clarsimp
  apply (frule (1) object_slots_opt_cap, simp)
  apply (erule (3) well_formed_well_formed_cap)
  done

lemma well_formed_well_formed_cap_to_object:
  "\<lbrakk>well_formed spec; cdl_objects spec obj_id = Some obj\<rbrakk>
   \<Longrightarrow> well_formed_cap_to_object spec obj_id obj"
  by (clarsimp simp: well_formed_def split: option.splits)

lemma well_formed_well_formed_cap_to_real_object:
  "\<lbrakk>well_formed spec; cdl_objects spec obj_id = Some obj;
    object_slots obj slot = Some cap; cap \<noteq> NullCap\<rbrakk>
   \<Longrightarrow> well_formed_cap_to_real_object spec cap"
  apply (clarsimp simp: well_formed_def)
  apply (erule_tac x=obj_id in allE)
  apply (clarsimp simp: well_formed_caps_def)
  done

lemma well_formed_well_formed_cap_to_real_object':
  "\<lbrakk>well_formed spec; opt_cap cap_ref spec = Some cap; cap \<noteq> NullCap\<rbrakk> \<Longrightarrow>
    well_formed_cap_to_real_object spec cap"
  apply (frule opt_cap_dom_cdl_objects)
  apply (clarsimp split: prod.splits)
  apply (frule (1) object_slots_opt_capD)
  apply (erule (3) well_formed_well_formed_cap_to_real_object)
  done

lemma well_formed_well_formed_cap_types_match:
  "\<lbrakk>well_formed spec; cdl_objects spec obj_id = Some obj;
    object_slots obj slot = Some cap; cap \<noteq> NullCap\<rbrakk>
   \<Longrightarrow> well_formed_cap_types_match spec cap"
  apply (clarsimp simp: well_formed_def)
  apply (erule_tac x=obj_id in allE)
  apply (clarsimp simp: well_formed_caps_def)
  done

lemma well_formed_well_formed_cap_types_match':
  "\<lbrakk>well_formed spec; opt_cap cap_ref spec = Some cap; cap \<noteq> NullCap\<rbrakk> \<Longrightarrow>
  well_formed_cap_types_match spec cap"
  apply (frule opt_cap_dom_cdl_objects)
  apply (clarsimp)
  apply (frule (1) object_slots_opt_capD)
  apply (erule (3) well_formed_well_formed_cap_types_match)
  done

lemma well_formed_cap_object_is_real:
  "\<lbrakk>well_formed spec; opt_cap slot spec = Some cap; cap_has_object cap\<rbrakk>
   \<Longrightarrow> real_object_at (cap_object cap) spec"
  apply (drule (1) well_formed_well_formed_cap_to_real_object', simp)
  apply (clarsimp simp: well_formed_cap_to_real_object_def)
  done

lemma well_formed_types_match:
  "\<lbrakk>well_formed spec; opt_cap (obj_id, slot) spec = Some cap;
    cdl_objects spec (cap_object cap) = Some cap_obj; cap_has_object cap\<rbrakk>
   \<Longrightarrow> Some (object_type cap_obj) = cap_type cap"
  apply (frule cap_has_object_not_NullCap)
  apply (clarsimp simp: well_formed_def)
  apply (erule_tac x=obj_id in allE)
  apply (clarsimp simp: opt_cap_def slots_of_def)
  apply (clarsimp split: option.splits)
  apply (rename_tac obj)
  apply (clarsimp simp: well_formed_caps_def well_formed_cap_types_match_def)
  apply (erule_tac x=slot in allE)
  apply (clarsimp)
  done

lemma well_formed_object_slots:
  "\<lbrakk>well_formed spec; cdl_objects spec obj_id = Some obj\<rbrakk>
   \<Longrightarrow> dom (object_slots obj) = dom (object_slots (object_default_state obj))"
  apply (clarsimp simp: well_formed_def)
  apply (erule allE [where x=obj_id])
  apply simp
  done

lemma well_formed_slot_object_size_bits:
  "\<lbrakk>well_formed spec; opt_cap (obj_id, slot) spec = Some cap;
    cdl_objects spec obj_id = Some obj; cnode_at obj_id spec\<rbrakk>
   \<Longrightarrow> slot < 2 ^ object_size_bits obj"
  apply (clarsimp simp: well_formed_def object_at_def is_cnode_def)
  apply (erule_tac x=obj_id in allE)
  apply clarsimp
  apply (clarsimp simp: opt_cap_def)
  apply (subgoal_tac "slot \<in> dom (object_slots (object_default_state obj))")
   apply (thin_tac "dom P = dom Q" for P Q)
   apply (clarsimp simp: well_formed_caps_def)
   apply (erule_tac x=slot in allE)
   apply (clarsimp simp: object_default_state_def2 object_type_def has_slots_def
                         default_tcb_def object_size_bits_def object_slots_def
                         empty_cnode_def empty_cap_map_def pt_size_def pd_size_def
                  split: cdl_object.splits if_split_asm)
  apply (clarsimp simp: object_slots_slots_of)
  done

lemma well_formed_slot_object_size_bits_pt:
  "\<lbrakk>well_formed spec; opt_cap (obj_id, slot) spec = Some cap;
    pt_at obj_id spec; cdl_objects spec obj_id = Some obj\<rbrakk>
   \<Longrightarrow> slot < 2 ^ object_size_bits obj"
  apply (clarsimp simp: well_formed_def object_at_def is_pt_def)
  apply (erule_tac x=obj_id in allE)
  apply clarsimp
  apply (subgoal_tac "slot \<in> dom (object_slots (object_default_state obj))")
   apply (thin_tac "dom P = dom Q" for P Q)
   apply (clarsimp simp: well_formed_caps_def)
   apply (erule_tac x=slot in allE)
   apply (clarsimp simp: object_default_state_def2 object_type_def has_slots_def
                         default_tcb_def object_size_bits_def object_slots_def
                         empty_cnode_def empty_cap_map_def pt_size_def pd_size_def
                   split: cdl_object.splits if_split_asm)
  by (fastforce intro: object_slots_opt_capI)

lemma well_formed_cnode_object_size_bits:
  "\<lbrakk>well_formed spec; cnode_at obj_id spec; cdl_objects spec obj_id = Some obj\<rbrakk>
   \<Longrightarrow> 0 < object_size_bits obj"
  apply (clarsimp simp: well_formed_def)
  apply (erule_tac x=obj_id in allE)
  apply (clarsimp simp: is_cnode_def object_at_def)
  done

lemma well_formed_cnode_object_size_bits_eq:
  "\<lbrakk>well_formed spec; opt_cap slot spec = Some cap;
    cdl_objects spec (cap_object cap) = Some obj; is_cnode_cap cap\<rbrakk>
   \<Longrightarrow> object_size_bits obj = cnode_cap_size cap"
  apply (frule (1) well_formed_cap_object_is_real)
   apply (clarsimp simp: cap_has_object_def cap_type_def split: cdl_cap.splits)
  apply (clarsimp simp: well_formed_def split_def split:option.splits)
  apply (erule_tac x="cap_object cap" in allE)
  apply (case_tac slot)
  apply (clarsimp simp: is_cnode_def  well_formed_cap_to_object_def)
  done

lemma dom_cdl_tcb_caps_default_tcb:
 "dom (cdl_tcb_caps (default_tcb domain)) = tcb_slots"
  by (auto simp: object_slots_def default_tcb_def dom_expand tcb_slots_def)

lemma slots_of_set [simp]:
  "well_formed spec \<Longrightarrow> set (slots_of_list spec obj_id) = dom (slots_of obj_id spec)"
  apply (clarsimp simp: slots_of_list_def slots_of_def  well_formed_def
                  split: option.splits)
  apply (rename_tac obj)
  apply (erule_tac x=obj_id in allE)
  apply (erule_tac x=obj in allE)
  apply (intro set_eqI iffI)
  by (fastforce simp: object_default_state_def2 object_slots_def object_slots_list_def
                      dom_cdl_tcb_caps_default_tcb empty_cnode_def empty_irq_node_def empty_cap_map_def
                      pt_size_def pd_size_def
                split: cdl_object.splits)+

lemma well_formed_well_formed_tcb:
  "\<lbrakk>well_formed spec; cdl_objects spec obj_id = Some obj\<rbrakk>
   \<Longrightarrow> well_formed_tcb spec obj_id obj"
  apply (clarsimp simp: well_formed_def)
  apply (erule_tac x=obj_id in allE)
  apply clarsimp
  done

lemma well_formed_well_formed_vspace:
  "\<lbrakk>well_formed spec; cdl_objects spec obj_id = Some obj\<rbrakk>
   \<Longrightarrow> well_formed_vspace spec obj_id obj"
  apply (clarsimp simp: well_formed_def)
  apply (erule_tac x=obj_id in allE)
  apply clarsimp
  done

lemma well_formed_well_formed_irq_node:
  "\<lbrakk>well_formed spec; cdl_objects spec obj_id = Some obj\<rbrakk>
   \<Longrightarrow> well_formed_irq_node spec obj_id obj"
  apply (clarsimp simp: well_formed_def)
  apply (erule_tac x=obj_id in allE)
  apply clarsimp
  done

lemma well_formed_well_formed_irqhandler_caps:
  "well_formed spec \<Longrightarrow> well_formed_irqhandler_caps spec"
  by (clarsimp simp: well_formed_def)

lemma well_formed_well_formed_irq_table:
  "well_formed spec \<Longrightarrow> well_formed_irq_table spec"
  by (clarsimp simp: well_formed_def)

lemma well_formed_inj_cdl_irq_node:
  "well_formed spec \<Longrightarrow> inj (cdl_irq_node spec)"
  by (clarsimp simp: well_formed_def well_formed_irq_table_def)

lemma well_formed_vm_cap_has_asid:
  "\<lbrakk>well_formed spec; cdl_objects spec obj_id = Some obj;
    object_slots obj slot = Some cap\<rbrakk>
   \<Longrightarrow> \<not>vm_cap_has_asid cap"
  apply (case_tac "cap = NullCap")
   apply (clarsimp simp: vm_cap_has_asid_def)
  apply (drule (3) well_formed_well_formed_cap)
  apply (clarsimp simp: well_formed_cap_def vm_cap_has_asid_def
                 split: cdl_cap.splits)
  done

lemma is_fake_vm_cap_cap_type:
  "is_fake_vm_cap cap \<Longrightarrow> (\<exists>sz. cap_type cap = Some (FrameType sz)) \<or>
                         (cap_type cap = Some PageTableType) \<or>
                         (cap_type cap = Some PageDirectoryType)"
  by (clarsimp simp: is_fake_vm_cap_def cap_type_def
              split: cdl_cap.splits)

lemma is_fake_vm_cap_cap_has_object[simp]:
  "is_fake_vm_cap cap \<Longrightarrow> cap_has_object cap"
  by (clarsimp simp: cap_has_object_def is_fake_vm_cap_def split: cdl_cap.splits)

lemma well_formed_is_fake_vm_cap:
  "\<lbrakk>well_formed spec; cdl_objects spec obj_id = Some obj; is_cnode obj \<or> is_tcb obj \<or> is_irq_node obj;
    object_slots obj slot = Some cap\<rbrakk>
   \<Longrightarrow> \<not>is_fake_vm_cap cap"
  apply (case_tac "is_irq_node obj")
   apply (frule (1) well_formed_well_formed_irq_node)
   apply (clarsimp simp: well_formed_irq_node_def object_at_def irq_nodes_def)
   apply (drule is_fake_vm_cap_cap_type)
   apply (cases "cap = NullCap", simp_all)
  apply (clarsimp simp: well_formed_def)
  apply (erule_tac x=obj_id in allE)
  apply (clarsimp simp: well_formed_caps_def)
  apply (erule_tac x=slot in allE)
  apply (clarsimp simp: domI is_fake_vm_cap_def)
  done

lemma vm_cap_has_asid_update_cap_object [simp]:
  "vm_cap_has_asid (update_cap_object obj_id cap) = vm_cap_has_asid cap"
  by (clarsimp simp: cap_has_object_def update_cap_object_def
                     vm_cap_has_asid_def
              split: cdl_cap.splits)

lemma well_formed_object_size_bits_word_bits [simp]:
  "\<lbrakk>well_formed spec; cdl_objects spec obj_id = Some spec_obj\<rbrakk>
   \<Longrightarrow> object_size_bits spec_obj < word_bits"
  apply (clarsimp simp: well_formed_def)
  apply (erule_tac x=obj_id in allE)
  apply clarsimp
  done

lemma well_formed_is_untyped_cap:
  "\<lbrakk>well_formed spec; cnode_at obj_id spec;
    opt_cap (obj_id, slot) spec = Some cap\<rbrakk>
   \<Longrightarrow> \<not> is_untyped_cap cap"
  apply (frule opt_cap_cdl_objects)
  apply (clarsimp simp: well_formed_def)
  apply (erule_tac x=obj_id in allE)
  apply (clarsimp simp: opt_cap_def well_formed_caps_def)
  apply (erule_tac x=slot in allE)
  apply (clarsimp simp: slots_of_def well_formed_cap_def
                        cap_type_def
                 split: cdl_cap.splits)
  done

lemma well_formed_cap_has_object:
  "\<lbrakk>well_formed spec; opt_cap (obj_id, slot) spec = Some spec_cap;
   spec_cap \<noteq> NullCap; \<not> is_untyped_cap spec_cap; \<not> is_irqhandler_cap spec_cap\<rbrakk>
   \<Longrightarrow> cap_has_object spec_cap"
  apply (clarsimp simp: opt_cap_def slots_of_def)
  apply (clarsimp simp: well_formed_def)
  apply (clarsimp split: option.splits)
  apply (rename_tac obj)
  apply (erule_tac x=obj_id in allE)
  apply (erule_tac x=obj in allE)
  apply (clarsimp simp: well_formed_caps_def)
  apply (erule_tac x=slot in allE)
  apply (clarsimp simp: domI)
  by (clarsimp simp: cap_has_object_def well_formed_cap_def
               split: cdl_cap.splits)

lemma well_formed_cap_object:
  "\<lbrakk>well_formed spec; opt_cap (obj_id, slot) spec = Some spec_cap;
    cap_has_object spec_cap\<rbrakk>
   \<Longrightarrow> \<exists>obj. cdl_objects spec (cap_object spec_cap) = Some obj"
  apply (frule (1) well_formed_well_formed_cap', clarsimp)
  apply (frule (1) well_formed_cap_has_object)
    apply clarsimp
   apply (clarsimp simp: well_formed_cap_def cap_type_def split: cdl_cap.splits)
  apply simp
  apply (clarsimp simp: opt_cap_def slots_of_def split: option.splits)
  apply (frule (1) well_formed_well_formed_caps)
  apply (clarsimp simp: well_formed_caps_def well_formed_cap_types_match_def)
  apply (erule allE [where x=slot])
  apply (erule allE [where x=spec_cap])
  apply clarsimp
  done

lemma well_formed_cap_object_in_dom:
  "\<lbrakk>well_formed spec; opt_cap (obj_id, slot) spec = Some spec_cap;
    cap_has_object spec_cap\<rbrakk>
   \<Longrightarrow> cap_object spec_cap \<in> dom (cdl_objects spec)"
  by (drule (2) well_formed_cap_object, clarsimp)

lemma well_formed_all_caps_cap_object:
  "\<lbrakk>well_formed spec; cap \<in> all_caps spec; cap_has_object cap\<rbrakk>
   \<Longrightarrow>\<exists>obj. cdl_objects spec (cap_object cap) = Some obj"
  apply (clarsimp simp: all_caps_def)
  apply (erule (2) well_formed_cap_object)
  done

lemma well_formed_all_caps_cap_irq:
  "\<lbrakk>well_formed spec; cap \<in> all_caps spec; is_irqhandler_cap cap\<rbrakk>
   \<Longrightarrow>\<exists>obj. cdl_objects spec (cdl_irq_node spec (cap_irq cap)) = Some obj"
  apply (clarsimp simp: all_caps_def)
  apply (frule (1) well_formed_well_formed_cap_types_match', simp)
  apply (clarsimp simp: well_formed_cap_types_match_def)
  done

lemma well_formed_update_cap_rights_idem:
  "\<lbrakk>well_formed_cap cap; rights = cap_rights cap\<rbrakk>
   \<Longrightarrow> update_cap_rights rights cap = cap"
  by (auto simp: update_cap_rights_def cap_rights_def well_formed_cap_def
               validate_vm_rights_def vm_kernel_only_def vm_read_write_def
               vm_read_only_def split: cdl_cap.splits)

lemma default_ep_cap[simp]:
  "is_default_cap (EndpointCap a 0 UNIV)"
  by (simp add:is_default_cap_def default_cap_def
    cap_type_def)

lemma default_ntfn_cap[simp]:
  "is_default_cap (NotificationCap a 0 {AllowRead, AllowWrite})"
  by (simp add:is_default_cap_def default_cap_def cap_type_def)

lemma default_cap_well_formed_cap:
  "\<lbrakk>well_formed_cap cap; cap_type cap = Some type; cnode_cap_size cap = sz\<rbrakk>
   \<Longrightarrow> well_formed_cap (default_cap type obj_ids sz dev)"
  by (auto simp: well_formed_cap_def default_cap_def cap_type_def
                 word_gt_a_gt_0 vm_read_write_def cnode_cap_size_def
          split: cdl_cap.splits)

lemma default_cap_well_formed_cap2:
  "\<lbrakk>is_default_cap cap; cap_type cap = Some type; sz \<le> 32;
    \<not> is_untyped_cap cap; \<not> is_asidpool_cap cap\<rbrakk>
   \<Longrightarrow> well_formed_cap (default_cap type obj_ids sz dev )"
  apply (clarsimp simp: is_default_cap_def)
  apply (clarsimp simp: default_cap_def well_formed_cap_def
                        word_gt_a_gt_0 badge_bits_def guard_bits_def
                        vm_read_write_def cnode_cap_size_def
                 split: cdl_object_type.splits cdl_cap.splits)
  done

lemma well_formed_well_formed_orig_cap:
  "\<lbrakk>well_formed spec;
    opt_cap (obj_id, slot) spec = Some cap; cap \<noteq> NullCap;
    original_cap_at (obj_id, slot) spec\<rbrakk>
   \<Longrightarrow> well_formed_orig_cap cap"
  apply (frule opt_cap_dom_cdl_objects)
  apply (clarsimp simp: dom_def, rename_tac obj)
  apply (frule (1) object_slots_opt_cap, simp)
  apply (clarsimp simp: well_formed_def well_formed_caps_def)
  apply (erule allE [where x=obj_id])
  apply (clarsimp simp: well_formed_caps_def)
  done

lemma well_formed_orig_ep_cap_is_default_helper:
  "\<lbrakk>well_formed_orig_cap cap; ep_related_cap cap; cap_has_type cap\<rbrakk> \<Longrightarrow> is_default_cap cap"
  by (clarsimp simp: well_formed_orig_cap_def is_default_cap_def cap_rights_def
                     ep_related_cap_def default_cap_def cap_type_def
              split: cdl_cap.splits)

lemma well_formed_orig_ep_cap_is_default:
  "\<lbrakk>well_formed spec; original_cap_at (obj_id, slot) spec;
    opt_cap (obj_id, slot) spec = Some cap;
    ep_related_cap cap; cap \<noteq> NullCap\<rbrakk>
   \<Longrightarrow> is_default_cap cap"
  apply (case_tac "\<exists>obj_id R. cap = ReplyCap obj_id R")
   apply (frule (1) well_formed_well_formed_cap', simp)
   apply (clarsimp simp: well_formed_cap_def)
  apply (case_tac "\<exists>irq target. cap = SGISignalCap irq target")
   apply (frule (1) well_formed_well_formed_cap', simp)
   apply (clarsimp simp: well_formed_cap_def)
  apply (frule (3) well_formed_well_formed_orig_cap)
  apply (erule (1) well_formed_orig_ep_cap_is_default_helper)
  apply (fastforce simp: ep_related_cap_def split: cdl_cap.splits)
  done

lemma cap_rights_default_cap_eq:
  "cap_rights (default_cap type obj_ids sz dev) =
   cap_rights (default_cap type obj_ids' sz' dev')"
  apply (clarsimp simp: cap_rights_def default_cap_def)
  apply (case_tac type, simp_all)
  done

lemma well_formed_orig_caps:
  "\<lbrakk>well_formed spec; original_cap_at (obj_id, slot) spec;
    slots_of obj_id spec slot = Some cap; cap \<noteq> NullCap; cap_type cap = Some type\<rbrakk>
   \<Longrightarrow> cap_rights (default_cap type obj_ids sz dev) = cap_rights cap"
  apply (frule well_formed_well_formed_orig_cap, simp add: opt_cap_def, assumption+)
  apply (clarsimp simp: well_formed_orig_cap_def)
  apply (subst (asm) cap_rights_default_cap_eq, fast)
  done

lemma well_formed_cdt:
  "\<lbrakk>well_formed spec; opt_cap (obj_id, slot) spec = Some cap; cap_has_object cap;
    cnode_at obj_id spec\<rbrakk> \<Longrightarrow>
    \<exists>orig_obj_id orig_slot orig_cap.
    cnode_at orig_obj_id spec \<and>
    original_cap_at (orig_obj_id, orig_slot) spec \<and>
    opt_cap (orig_obj_id, orig_slot) spec = Some orig_cap \<and>
    cap_has_object orig_cap \<and> cap_object orig_cap = cap_object cap"
  apply (clarsimp simp: well_formed_def)
  apply (erule_tac x=obj_id in allE)
  apply (clarsimp simp: split: option.splits)
   apply (clarsimp simp: object_at_def)
  apply (clarsimp simp: well_formed_caps_def)
  apply (erule_tac x=slot in allE)
  apply (clarsimp simp: well_formed_cdt_def object_slots_opt_cap)
  by blast

lemma well_formed_cap_to_real_object:
  "\<lbrakk>well_formed spec; real_object_at obj_id spec\<rbrakk>
   \<Longrightarrow> \<exists>cnode_id slot cap.
       opt_cap (cnode_id, slot) spec = Some cap \<and>
       original_cap_at (cnode_id, slot) spec \<and>
       cnode_at cnode_id spec \<and>
       cap_object cap = obj_id \<and>
       cap_has_object cap"
  apply (clarsimp simp: well_formed_def)
  apply (erule_tac x=obj_id in allE)
  apply (clarsimp simp: well_formed_cap_to_object_def real_object_at_def split: option.splits)
  done

lemma well_formed_cap_to_irq_object:
  "\<lbrakk>well_formed spec; cdl_objects spec obj_id = Some obj; obj_id \<in> irq_nodes spec\<rbrakk>
   \<Longrightarrow> \<exists>cnode_id slot cap.
       opt_cap (cnode_id, slot) spec = Some cap \<and>
       original_cap_at (cnode_id, slot) spec \<and>
       cnode_at cnode_id spec \<and>
       is_irqhandler_cap cap \<and>
       cdl_irq_node spec (cap_irq cap) = obj_id"
  apply (frule (1) well_formed_well_formed_cap_to_object)
  apply (clarsimp simp: well_formed_cap_to_object_def real_object_at_def split: option.splits)
  done

lemma well_formed_cap_to_non_empty_pt:
  "\<lbrakk>well_formed spec; pt_at obj_id spec;
    object_at (\<lambda>obj. object_default_state obj \<noteq> obj) obj_id spec\<rbrakk>
   \<Longrightarrow> \<exists>pd_id slot cap.
       opt_cap (pd_id, slot) spec = Some cap \<and>
       pd_at pd_id spec \<and>
       cap_object cap = obj_id \<and>
       cap_has_object cap"
  apply (clarsimp simp: well_formed_def)
  apply (erule_tac x=obj_id in allE)
  apply (clarsimp simp: object_at_def)
  apply (clarsimp simp: well_formed_vspace_def well_formed_cap_to_non_empty_pt_def object_at_def)
  done

lemma dom_object_slots_default_tcb:
  "dom (object_slots (Tcb (default_tcb domain))) = tcb_slots"
  by (clarsimp simp: object_slots_def dom_cdl_tcb_caps_default_tcb)

lemma well_formed_tcb_has_fault:
  "\<lbrakk>well_formed spec; cdl_objects spec obj_id = Some (Tcb tcb)\<rbrakk>
   \<Longrightarrow> \<not> cdl_tcb_has_fault tcb"
  apply (drule (1) well_formed_well_formed_tcb)
  apply (clarsimp simp: well_formed_tcb_def tcb_has_fault_def)
  done

lemma well_formed_tcb_domain:
  "\<lbrakk>well_formed spec; cdl_objects spec obj_id = Some (Tcb tcb)\<rbrakk>
   \<Longrightarrow> cdl_tcb_domain tcb = minBound"
  apply (drule (1) well_formed_well_formed_tcb)
  apply (clarsimp simp: well_formed_tcb_def tcb_domain_def)
  done

lemma well_formed_object_domain:
  "\<lbrakk>well_formed spec; cdl_objects spec obj_id = Some obj\<rbrakk>
   \<Longrightarrow> object_domain obj = minBound"
  apply (case_tac "\<exists>tcb. obj = Tcb tcb")
   apply clarsimp
   apply (drule (1) well_formed_tcb_domain)
   apply (clarsimp simp: object_domain_def)
  apply (clarsimp simp: object_domain_def minBound_word
                 split: cdl_object.splits)
  done

lemma well_formed_tcb_object_slots:
  "\<lbrakk>well_formed spec; cdl_objects spec obj_id = Some tcb; is_tcb tcb\<rbrakk>
   \<Longrightarrow> dom (object_slots tcb) = tcb_slots"
  apply (frule (1) well_formed_object_slots)
  apply (clarsimp simp: object_default_state_def2 is_tcb_def split: cdl_object.splits)
  apply (rule dom_object_slots_default_tcb)
  done

lemma well_formed_tcb_cspace_cap:
  "\<lbrakk>well_formed spec;
    tcb_at obj_id spec\<rbrakk>
   \<Longrightarrow> \<exists>cspace_cap. opt_cap (obj_id, tcb_cspace_slot) spec = Some cspace_cap \<and>
                   is_cnode_cap cspace_cap \<and> cap_guard_size cspace_cap \<noteq> 0 \<and>
                   real_object_at (cap_object cspace_cap) spec"
  apply (clarsimp simp: object_at_def)
  apply (frule (1) well_formed_well_formed_caps)
  apply (frule (1) well_formed_well_formed_tcb)
  apply (frule (2) well_formed_tcb_object_slots)
  apply (clarsimp simp: well_formed_caps_def)
  apply (clarsimp simp: well_formed_tcb_def)
  apply (erule_tac x=tcb_cspace_slot in allE)+
  apply (clarsimp simp: is_tcb_def object_default_state_def2 split: cdl_object.splits)
  apply (rename_tac cdl_tcb)
  apply (clarsimp simp: opt_cap_def slots_of_def split: option.splits)
  apply (subgoal_tac "\<exists>cspace_cap. object_slots (Tcb cdl_tcb) tcb_cspace_slot =
                                   Some cspace_cap")
   apply (clarsimp simp: dom_def well_formed_tcb_def real_object_at_def)
   apply (erule well_formed_cap_object [where obj_id=obj_id and slot=tcb_cspace_slot])
    apply (simp add: opt_cap_def slots_of_def)
   apply (clarsimp simp: cap_has_object_def cap_type_def split: cdl_cap.splits)
  apply (auto simp: dom_def tcb_slot_defs)
  done

lemma cap_data_cap_guard_size_0:
  "\<lbrakk>well_formed_cap cap; is_cnode_cap cap; cap_data cap = 0\<rbrakk>
   \<Longrightarrow> cap_guard_size cap = 0"
  apply (clarsimp simp: cap_type_def cap_data_def guard_as_rawdata_def
                        well_formed_cap_def
                 split: cdl_cap.splits)
    apply (subst (asm) is_aligned_add_or [where n=8])
    apply (rule is_aligned_shift)
   apply (rule shiftl_less_t2n)
    apply (rule word_of_nat_less)
    apply (clarsimp simp: guard_bits_def)
   apply clarsimp
  apply (clarsimp simp: word_or_zero)
  apply (rule ccontr)
  apply (drule (1) guard_size_shiftl_non_zero)
  apply simp
  done

lemma well_formed_tcb_cspace_cap_cap_data:
  "\<lbrakk>well_formed spec; tcb_at obj_id spec;
    cdl_objects spec obj_id = Some (Tcb tcb);
    opt_cap (obj_id, tcb_cspace_slot) spec = Some spec_cspace_cap\<rbrakk>
   \<Longrightarrow> cap_data spec_cspace_cap \<noteq> 0"
  apply (frule (1) well_formed_tcb_cspace_cap, clarsimp)
  apply (frule (1) well_formed_well_formed_cap', clarsimp)
  apply (drule (2) cap_data_cap_guard_size_0, simp)
  done

lemma well_formed_tcb_opt_cap:
  "\<lbrakk>well_formed spec; tcb_at obj_id spec; slot \<in> tcb_slots\<rbrakk>
   \<Longrightarrow> \<exists>cap. opt_cap (obj_id, slot) spec = Some cap"
  apply (clarsimp simp: object_at_def)
  apply (drule (1) well_formed_object_slots)
  apply (fastforce simp: object_default_state_def2 is_tcb_def
                         opt_cap_def slots_of_def object_slots_def
                         default_tcb_def dom_def
                  split: cdl_object.splits if_split_asm)
  done


lemma well_formed_tcb_vspace_cap:
  "\<lbrakk>well_formed spec;
    tcb_at obj_id spec\<rbrakk>
   \<Longrightarrow> \<exists>vspace_cap.
    opt_cap (obj_id, tcb_vspace_slot) spec = Some vspace_cap \<and> is_pd_cap vspace_cap"
  apply (frule (1) well_formed_tcb_opt_cap [where slot=tcb_vspace_slot], simp add: tcb_slot_defs)
  apply (clarsimp simp: object_at_def)
  apply (frule (1) well_formed_well_formed_tcb)
  apply (auto simp: well_formed_tcb_def opt_cap_def slots_of_def)
  done

lemma well_formed_tcb_ipcbuffer_cap:
  "\<lbrakk>well_formed spec;
    tcb_at obj_id spec\<rbrakk>
   \<Longrightarrow> \<exists>tcb_ipcbuffer_cap.
    opt_cap (obj_id, tcb_ipcbuffer_slot) spec = Some tcb_ipcbuffer_cap \<and>
    is_default_cap tcb_ipcbuffer_cap \<and> is_frame_cap tcb_ipcbuffer_cap"
  apply (frule (1) well_formed_tcb_opt_cap [where slot=tcb_ipcbuffer_slot], simp add: tcb_slot_defs)
  apply (clarsimp simp: object_at_def)
  apply (frule (1) well_formed_well_formed_tcb)
  apply (auto simp: well_formed_tcb_def opt_cap_def slots_of_def)
  done

lemma well_formed_tcb_caller_cap:
  "\<lbrakk>well_formed spec; tcb_at obj_id spec\<rbrakk>
   \<Longrightarrow> opt_cap (obj_id, tcb_caller_slot) spec = Some NullCap"
  apply (frule (1) well_formed_tcb_opt_cap [where slot=tcb_caller_slot], simp add: tcb_slot_defs)
  apply (clarsimp simp: object_at_def)
  apply (frule (1) well_formed_well_formed_tcb)
  apply (auto simp: well_formed_tcb_def opt_cap_def slots_of_def)
  done

lemma well_formed_tcb_replycap_cap:
  "\<lbrakk>well_formed spec; tcb_at obj_id spec\<rbrakk>
   \<Longrightarrow> opt_cap (obj_id, tcb_replycap_slot) spec = Some NullCap \<or>
      opt_cap (obj_id, tcb_replycap_slot) spec = Some (MasterReplyCap obj_id)"
  apply (frule (1) well_formed_tcb_opt_cap [where slot=tcb_replycap_slot], simp add: tcb_slot_defs)
  apply (clarsimp simp: object_at_def)
  apply (frule (1) well_formed_well_formed_tcb)
  apply (auto simp: well_formed_tcb_def opt_cap_def slots_of_def)
  done


lemma well_formed_tcb_pending_op_cap:
  "\<lbrakk>well_formed spec; tcb_at obj_id spec\<rbrakk>
   \<Longrightarrow> opt_cap (obj_id, tcb_pending_op_slot) spec = Some NullCap \<or>
      opt_cap (obj_id, tcb_pending_op_slot) spec = Some RestartCap"
  apply (frule (1) well_formed_tcb_opt_cap [where slot=tcb_pending_op_slot], simp add: tcb_slot_defs)
  apply (clarsimp simp: object_at_def)
  apply (frule (1) well_formed_well_formed_tcb)
  apply (auto simp: well_formed_tcb_def opt_cap_def slots_of_def)
  done

lemma well_formed_tcb_pending_op_replycap:
  "\<lbrakk>well_formed spec; tcb_at obj_id spec\<rbrakk>
   \<Longrightarrow> (opt_cap (obj_id, tcb_replycap_slot) spec = Some (MasterReplyCap obj_id))
    = (opt_cap (obj_id, tcb_pending_op_slot) spec = Some RestartCap)"
  apply (clarsimp simp: object_at_def)
  apply (drule (1) well_formed_well_formed_tcb)
  apply (clarsimp simp: well_formed_tcb_def opt_cap_def slots_of_def)
  done

lemma well_formed_tcb_boundntfn_cap:
  "\<lbrakk>well_formed spec; tcb_at obj_id spec\<rbrakk>
   \<Longrightarrow> opt_cap (obj_id, tcb_boundntfn_slot) spec = Some NullCap"
  apply (frule (1) well_formed_tcb_opt_cap [where slot=tcb_boundntfn_slot], simp add: tcb_slot_defs)
  apply (elim exE)
  apply (clarsimp simp: object_at_def)
  apply (drule (1) well_formed_well_formed_tcb)
  by (auto simp: well_formed_tcb_def opt_cap_def slots_of_def)

lemma well_formed_orig_caps_unique:
  "\<lbrakk>well_formed spec; original_cap_at (obj_id, slot) spec; original_cap_at (obj_id', slot') spec;
    cnode_at obj_id spec; cnode_at obj_id' spec; cap_has_object cap; cap_has_object cap';
    opt_cap (obj_id, slot) spec = Some cap; opt_cap (obj_id', slot') spec = Some cap';
    cap_object cap = cap_object cap'\<rbrakk>
   \<Longrightarrow> obj_id = obj_id' \<and> slot = slot'"
  by (clarsimp simp: well_formed_def well_formed_orig_caps_unique_def)

lemma well_formed_orig_caps_unique':
  "\<lbrakk>well_formed spec; original_cap_at (obj_id, slot) spec; original_cap_at (obj_id', slot') spec;
    real_cap_ref (obj_id, slot) spec; real_cap_ref (obj_id', slot') spec;
    opt_cap (obj_id, slot) spec = Some cap; opt_cap (obj_id', slot') spec = Some cap';
    cap_has_object cap; cap_has_object cap';
    cap_object cap = cap_object cap'\<rbrakk>
   \<Longrightarrow> obj_id = obj_id' \<and> slot = slot'"
  by (clarsimp simp: well_formed_def well_formed_orig_caps_unique_def real_cap_ref_def)

lemma well_formed_irqhandler_caps_unique:
  "\<lbrakk>well_formed s; is_irqhandler_cap cap; is_irqhandler_cap cap';
    opt_cap (obj_id, slot) s = Some cap; opt_cap (obj_id', slot') s = Some cap';
    cap_irq cap = cap_irq cap'\<rbrakk>
   \<Longrightarrow> obj_id = obj_id' \<and> slot = slot'"
  by (clarsimp simp: well_formed_def well_formed_irqhandler_caps_unique_def)

lemma object_cap_ref_cap_irq:
  "\<lbrakk>object_cap_ref (obj_id, slot) spec; opt_cap (obj_id, slot) spec = Some cap\<rbrakk>
   \<Longrightarrow> cap_irq cap = undefined"
  by (auto simp: object_cap_ref_def cap_has_object_def cap_irq_def
          split: cdl_cap.splits)

lemma object_cap_ref_real_cap_ref:
  "object_cap_ref (obj_id, slot) spec \<Longrightarrow> real_cap_ref (obj_id, slot) spec"
  by (clarsimp simp: object_cap_ref_def real_cap_ref_def)

lemma well_formed_orig_caps_unique_object_cap:
  "\<lbrakk>well_formed spec; original_cap_at (obj_id, slot) spec; original_cap_at (obj_id', slot') spec;
    object_cap_ref (obj_id, slot) spec; object_cap_ref (obj_id', slot') spec;
    opt_cap (obj_id, slot) spec = Some cap; opt_cap (obj_id', slot') spec = Some cap';
    cap_has_object cap; cap_has_object cap';
    cap_object cap = cap_object cap'\<rbrakk>
   \<Longrightarrow> obj_id = obj_id' \<and> slot = slot'"
  apply (frule object_cap_ref_real_cap_ref, drule (1) object_cap_ref_cap_irq)+
  apply (erule (8) well_formed_orig_caps_unique', simp)
  done

lemma well_formed_child_cap_not_copyable:
  "\<lbrakk>well_formed spec; \<not> original_cap_at (obj_id, slot) spec;
    opt_cap (obj_id, slot) spec = Some cap; cap \<noteq> NullCap\<rbrakk>
   \<Longrightarrow> is_copyable_cap cap"
  apply (clarsimp simp: well_formed_def)
  apply (erule_tac x=obj_id in allE)
  apply (clarsimp simp: opt_cap_def slots_of_def)
  apply (clarsimp split: option.splits)
  apply (rename_tac obj)
  apply (clarsimp simp: well_formed_caps_def)
  done

lemma well_formed_child_cap_not_copyable':
  "\<lbrakk>well_formed spec;
    opt_cap (obj_id, slot) spec = Some cap; cap \<noteq> NullCap\<rbrakk>
   \<Longrightarrow> \<not>original_cap_at (obj_id, slot) spec \<longrightarrow> is_copyable_cap cap"
  by (rule impI, erule (3) well_formed_child_cap_not_copyable)

lemma well_formed_pd:
  "\<lbrakk>well_formed spec; opt_cap (obj_id, slot) spec = Some cap;
    pd_at obj_id spec; cap \<noteq> NullCap\<rbrakk>
   \<Longrightarrow> is_frame_cap cap \<or> is_fake_pt_cap cap"
  apply (clarsimp simp: object_at_def)
  apply (frule (1) well_formed_well_formed_vspace)
  apply (clarsimp simp: well_formed_vspace_def)
  apply (erule allE [where x=slot])
  apply (erule allE [where x=cap])
  apply (clarsimp simp: opt_cap_def slots_of_def split: option.splits)
  done

lemma well_formed_pt:
  "\<lbrakk>well_formed spec; opt_cap (obj_id, slot) spec = Some cap;
    pt_at obj_id spec; cap \<noteq> NullCap\<rbrakk>
   \<Longrightarrow> is_frame_cap cap"
  apply (clarsimp simp: object_at_def)
  apply (frule (1) well_formed_well_formed_vspace)
  apply (clarsimp simp: well_formed_vspace_def)
  apply (erule allE [where x=slot])
  apply (erule allE [where x=cap])
  apply (clarsimp simp: opt_cap_def slots_of_def split: option.splits)
  done

lemma well_formed_pt_cap_is_fake_pt_cap:
  "\<lbrakk>well_formed spec; opt_cap (obj_id, slot) spec = Some cap;
    pd_at obj_id spec; is_pt_cap cap\<rbrakk>
   \<Longrightarrow> is_fake_pt_cap cap"
  by (frule (2) well_formed_pd, clarsimp+)

lemma wf_cap_pt_cap[simp]: "well_formed_cap (PageTableCap pt_id ty addr) \<longleftrightarrow> addr = None"
  by (clarsimp simp: well_formed_cap_def)

lemma wf_frame_cap_frame_size_bits:
  "\<lbrakk>well_formed spec;
    opt_cap (pt_ptr, slot) spec = Some (FrameCap dev frame_ptr rights n Fake None);
    cdl_objects spec frame_ptr = Some (Frame frame)\<rbrakk>
   \<Longrightarrow> cdl_frame_size_bits frame = n"
  apply (clarsimp simp: opt_cap_def slots_of_def split: option.splits)
  apply (frule (2) well_formed_well_formed_cap_types_match, fastforce)
  apply (fastforce simp: well_formed_cap_types_match_def cap_object_def object_type_def)
  done

lemma wf_pd_cap_has_object:
  "\<lbrakk>well_formed spec;
    pd_at spec_pd_ptr spec;
    opt_cap (spec_pd_ptr, slot) spec = Some cap;
    cap \<noteq> NullCap\<rbrakk> \<Longrightarrow> cap_has_object cap"
  by (fastforce simp: cap_has_object_def cap_type_def is_fake_pt_cap_def
                dest: well_formed_pd split: cdl_cap.splits)


(****************************************
 * Rules about IRQ caps and IRQ CNodes. *
 ****************************************)

lemma well_formed_irq_nodes_object_type:
  "\<lbrakk>well_formed spec; obj_id \<in> irq_nodes spec;
    cdl_objects spec obj_id = Some object\<rbrakk>
   \<Longrightarrow> object_type object = IRQNodeType"
  apply (frule (1) well_formed_well_formed_irq_node)
  apply (frule (2) well_formed_cap_to_irq_object)
  apply (clarsimp simp: opt_cap_def slots_of_def split: option.splits)
  apply (frule (2) well_formed_well_formed_cap_types_match, simp)
  apply (clarsimp simp: well_formed_cap_types_match_def)
  done

lemma well_formed_object_at_irq_node_irq_node_at:
  "\<lbrakk>well_formed spec; object_at P obj_id spec; obj_id \<in> irq_nodes spec\<rbrakk> \<Longrightarrow> irq_node_at obj_id spec"
  apply (clarsimp simp: object_at_def)
  apply (frule (2) well_formed_irq_nodes_object_type)
  apply (simp add: object_type_is_object)
  done

lemma real_object_not_irq_node:
  "well_formed spec \<Longrightarrow> (real_object_at obj_id spec \<and> cnode_at obj_id spec) = cnode_at obj_id spec"
  "well_formed spec \<Longrightarrow> (real_object_at obj_id spec \<and> tcb_at obj_id spec) = tcb_at obj_id spec"
  "well_formed spec \<Longrightarrow> (real_object_at obj_id spec \<and> table_at obj_id spec) = table_at obj_id spec"
  "well_formed spec \<Longrightarrow> (real_object_at obj_id spec \<and> capless_at obj_id spec) = capless_at obj_id spec"
  apply (insert well_formed_object_at_irq_node_irq_node_at [where spec=spec and obj_id=obj_id])
  apply (fastforce simp: real_object_at_def object_at_def object_type_is_object)+
  done

lemma object_at_real_object_at:
  "\<lbrakk>well_formed spec; cnode_at obj_id spec\<rbrakk> \<Longrightarrow> real_object_at obj_id spec"
  "\<lbrakk>well_formed spec; tcb_at obj_id spec\<rbrakk> \<Longrightarrow> real_object_at obj_id spec"
  "\<lbrakk>well_formed spec; ep_at obj_id spec\<rbrakk> \<Longrightarrow> real_object_at obj_id spec"
  "\<lbrakk>well_formed spec; ntfn_at obj_id spec\<rbrakk> \<Longrightarrow> real_object_at obj_id spec"
  "\<lbrakk>well_formed spec; table_at obj_id spec\<rbrakk> \<Longrightarrow> real_object_at obj_id spec"
  "\<lbrakk>well_formed spec; pd_at obj_id spec\<rbrakk> \<Longrightarrow> real_object_at obj_id spec"
  "\<lbrakk>well_formed spec; pt_at obj_id spec\<rbrakk> \<Longrightarrow> real_object_at obj_id spec"
  "\<lbrakk>well_formed spec; frame_at obj_id spec\<rbrakk> \<Longrightarrow> real_object_at obj_id spec"
  apply (insert well_formed_object_at_irq_node_irq_node_at [where spec=spec and obj_id=obj_id])
  apply (fastforce simp: real_object_at_def object_at_def object_type_is_object)+
  done

lemma well_formed_irq_node_slot_0:
  "\<lbrakk>well_formed spec; irq_id \<in> irq_nodes spec;
    opt_cap (irq_id, slot) spec = Some cap\<rbrakk> \<Longrightarrow>
    slot = 0"
  apply (frule opt_cap_cdl_objects, clarsimp)
  apply (frule (1) well_formed_well_formed_irq_node)
  apply (frule (1) object_slots_opt_cap, simp)
  apply (simp add: well_formed_irq_node_def dom_def, blast)
  done

lemma well_formed_irq_nodes_cdl_irq_node:
  "cdl_irq_node spec irq \<in> irq_nodes spec \<Longrightarrow> irq_node_at (cdl_irq_node spec irq) spec"
  by (simp add: irq_nodes_def)

lemma well_formed_cdl_irq_node_irq_nodes:
  "\<lbrakk>well_formed spec; cdl_objects spec (cdl_irq_node spec irq) = Some irq_node\<rbrakk>
   \<Longrightarrow> cdl_irq_node spec irq \<in> irq_nodes spec"
  apply (drule well_formed_well_formed_irq_table)
  apply (clarsimp simp: well_formed_irq_table_def)
  apply (fastforce simp: object_at_def)
  done

lemma well_formed_irq_is_irq_node:
  "\<lbrakk>well_formed spec; cdl_objects spec (cdl_irq_node spec irq) = Some irq_node\<rbrakk>
   \<Longrightarrow> is_irq_node irq_node"
  apply (frule (1) well_formed_cdl_irq_node_irq_nodes)
  apply (clarsimp simp: irq_nodes_def object_at_def)
  done

lemma well_formed_object_slots_irq_node:
  "\<lbrakk>well_formed spec; cdl_objects spec (cdl_irq_node spec irq) = Some irq_node\<rbrakk>
   \<Longrightarrow> dom (object_slots irq_node) = {0}"
  apply (frule (1) well_formed_cdl_irq_node_irq_nodes)
  apply (frule (1) well_formed_well_formed_irq_node)
  apply (clarsimp simp: well_formed_irq_node_def)
  done

lemma well_formed_irq_ntfn_cap:
  "\<lbrakk>well_formed spec;
    irq \<in> bound_irqs spec;
    opt_cap (cdl_irq_node spec irq, 0) spec = Some ntfn_cap\<rbrakk>
   \<Longrightarrow> ntfn_cap = NotificationCap (cap_object ntfn_cap) 0 {AllowRead, AllowWrite}"
  apply (frule opt_cap_cdl_objects, clarsimp)
  apply (frule (1) well_formed_object_slots_irq_node [where irq=irq])
  apply (frule (1) well_formed_well_formed_irq_node)
  apply (frule (1) well_formed_cdl_irq_node_irq_nodes)
  apply (clarsimp simp: well_formed_irq_node_def)
  apply (erule allE [where x=0])
  apply (erule allE [where x=ntfn_cap])
  apply (fastforce simp: bound_irqs_def opt_cap_def slots_of_def
                         is_default_cap_def default_cap_def cap_object_def
                         cap_has_object_def
                  split: cdl_cap.splits)
  done

lemma well_formed_bound_irqs_are_used_irqs:
  "well_formed spec \<Longrightarrow> bound_irqs spec \<subseteq> used_irqs spec"
  apply (frule well_formed_well_formed_irqhandler_caps)
  apply (fastforce simp: well_formed_irqhandler_caps_def used_irqs_def bound_irqs_def all_caps_def)
  done

lemma well_formed_slots_of_used_irq_node:
  "\<lbrakk>well_formed spec; irq \<in> used_irqs spec\<rbrakk>
   \<Longrightarrow> dom (slots_of (cdl_irq_node spec irq) spec) = {0}"
  apply (clarsimp simp: used_irqs_def slots_of_def split: option.splits)
  apply (frule (2) well_formed_all_caps_cap_irq, clarsimp)
  apply (erule (1) well_formed_object_slots_irq_node)
  done

lemma well_formed_slot_0_of_used_irq_node:
  "\<lbrakk>well_formed spec; irq \<in> used_irqs spec\<rbrakk>
   \<Longrightarrow> \<exists>ntfn_cap. slots_of (cdl_irq_node spec irq) spec 0 = Some ntfn_cap"
  apply (frule (1) well_formed_slots_of_used_irq_node)
  apply (clarsimp simp: dom_eq_singleton_conv)
  done

lemma well_formed_object_slots_default_irq_node:
  "\<lbrakk>well_formed spec; cdl_objects spec (cdl_irq_node spec irq) = Some irq_node\<rbrakk>
   \<Longrightarrow> dom (object_slots (object_default_state irq_node)) = {0}"
  by (metis well_formed_object_slots well_formed_object_slots_irq_node)

lemma object_slots_empty_cnode:
  "object_slots (CNode (empty_cnode sz)) = empty_cap_map sz"
  by (clarsimp simp: object_slots_def empty_cnode_def)

lemma dom_empty_cap_map_singleton:
  "dom (empty_cap_map (sz)) = {0} \<Longrightarrow> sz = 0"
  apply (clarsimp simp: empty_cap_map_def)
  apply (subst (asm) atLeastLessThan_singleton [symmetric])
  apply (drule atLeastLessThan_inj(2), simp+)
  done

lemma well_formed_size_irq_node:
  "\<lbrakk>well_formed spec; cdl_objects spec (cdl_irq_node spec irq) = Some irq_node\<rbrakk>
   \<Longrightarrow> object_size_bits irq_node = 0"
  apply (frule (1) well_formed_irq_is_irq_node)
  apply (frule (1) well_formed_object_slots)
  apply (drule (1) well_formed_object_slots_default_irq_node)
  apply (clarsimp simp: object_default_state_def2 is_cnode_def object_slots_empty_cnode
                        object_size_bits_def dom_empty_cap_map_singleton is_irq_node_def
                 split: cdl_object.splits)
  done

lemma well_formed_used_irqs_have_irq_node:
  "\<lbrakk>well_formed spec; irq \<in> used_irqs spec\<rbrakk>
   \<Longrightarrow> \<exists>irq_node. cdl_objects spec (cdl_irq_node spec irq) = Some irq_node"
  apply (clarsimp simp: used_irqs_def)
  apply (erule (2) well_formed_all_caps_cap_irq)
  done

lemma well_formed_bound_irqs_have_irq_node:
  "\<lbrakk>well_formed spec; irq \<in> bound_irqs spec\<rbrakk>
   \<Longrightarrow> \<exists>irq_node. cdl_objects spec (cdl_irq_node spec irq) = Some irq_node"
  apply (frule well_formed_well_formed_irqhandler_caps)
  apply (clarsimp simp: well_formed_irqhandler_caps_def used_irqs_def bound_irqs_def all_caps_def)
  done

lemma well_formed_irq_node_is_bound:
  "\<lbrakk>well_formed spec; cdl_objects spec (cdl_irq_node spec irq) = Some irq_node;
    object_slots irq_node 0 \<noteq> Some NullCap\<rbrakk>
   \<Longrightarrow> irq \<in> bound_irqs spec"
  apply (frule well_formed_well_formed_irqhandler_caps)
  apply (frule (1) well_formed_object_slots_default_irq_node)
  apply (frule (1) well_formed_object_slots)
  apply (clarsimp simp: well_formed_irqhandler_caps_def bound_irqs_def
                        dom_eq_singleton_conv slots_of_def)
  done

lemma well_formed_cap_object_cdl_irq_node:
  "\<lbrakk>well_formed spec; irq \<in> bound_irqs spec\<rbrakk>
    \<Longrightarrow> \<exists>obj. is_ntfn obj \<and>
              cdl_objects spec (cap_object (the (opt_cap (cdl_irq_node spec irq, 0) spec))) = Some obj"
  apply (frule well_formed_bound_irqs_are_used_irqs)
  apply (frule (1) well_formed_bound_irqs_have_irq_node, clarsimp)
  apply (frule well_formed_slot_0_of_used_irq_node [where irq=irq], fast)
  apply (clarsimp simp: opt_cap_def)
  apply (rename_tac cap)
  apply (frule (1) well_formed_irq_ntfn_cap, simp add: opt_cap_def)
  apply (frule well_formed_cap_object, simp add: opt_cap_def)
   apply (metis cap_has_object_simps(12))
  apply clarsimp
  apply (frule well_formed_types_match [where obj_id = "cdl_irq_node spec irq" and slot = 0])
    apply (simp add: opt_cap_def)
   apply simp
   apply (metis cap_has_object_simps(12))
  apply (clarsimp simp: object_type_is_object cap_type_def split: cdl_cap.splits)
  done





(* There are no untyped objects (as there are no untyped caps). *)
lemma well_formed_object_untyped:
 "\<lbrakk>well_formed spec; cdl_objects spec obj_id = Some object\<rbrakk>
   \<Longrightarrow> object_type object \<noteq> UntypedType"
  apply (case_tac "real_object_at obj_id spec")
   apply (frule (1) well_formed_cap_to_real_object)
   apply clarsimp
   apply (frule (1) well_formed_types_match, simp add: cap_has_object_def)
    apply (clarsimp simp: cap_has_object_def)
   apply (clarsimp simp: cap_type_def cap_has_object_def
                  split: cdl_cap.splits)
   apply (frule (2) well_formed_is_untyped_cap)
   apply (clarsimp simp: cap_type_def)
  apply (clarsimp simp: real_object_at_def dom_def)
  apply (drule (2) well_formed_irq_nodes_object_type)
  apply simp
  done

lemma well_formed_asidpool_at:
  "well_formed spec \<Longrightarrow> \<not> asidpool_at obj_id spec"
  apply (clarsimp simp: object_at_def object_type_is_object)
  apply (frule well_formed_cap_to_real_object [where obj_id=obj_id])
   apply (clarsimp simp: real_object_at_def dom_def)
   apply (drule (2) well_formed_irq_nodes_object_type, simp)
  apply clarsimp
  apply (frule (2) well_formed_types_match [symmetric], clarsimp+)
  apply (frule (1) well_formed_well_formed_cap', clarsimp)
  apply (clarsimp simp: well_formed_cap_def cap_type_def
                 split: cdl_cap.splits)
  done

lemma well_formed_no_asidpools:
  "well_formed spec \<Longrightarrow> [obj \<leftarrow> obj_ids. asidpool_at obj spec] = []"
  by (clarsimp simp: filter_empty_conv well_formed_asidpool_at)


lemma well_formed_fake_pt_cap_in_pd:
  "\<lbrakk>well_formed spec; slots_of obj_id spec slot = Some cap; is_fake_pt_cap cap\<rbrakk>
   \<Longrightarrow> pd_at obj_id spec"
  apply (clarsimp simp: slots_of_def split: option.splits)
  apply (rename_tac obj)
  apply (frule well_formed_asidpool_at [where obj_id=obj_id])
  apply (frule (1) well_formed_well_formed_vspace)
  apply (case_tac "is_cnode obj \<or> is_tcb obj \<or> is_irq_node obj")
   apply (frule (3) well_formed_is_fake_vm_cap)
   apply (clarsimp simp: is_fake_vm_cap_def is_fake_pt_cap_def split: cdl_cap.splits)
  apply clarsimp
  apply (clarsimp simp: object_at_def object_type_is_object)
  apply (case_tac obj, simp_all add: object_slots_def object_at_def object_type_is_object object_type_def)
  apply (clarsimp simp: well_formed_vspace_def)
  apply (erule allE [where x=slot])
  apply (erule allE [where x=cap])
  apply (clarsimp simp: is_fake_pt_cap_is_pt_cap object_slots_def)
  done

lemma well_formed_pt_cap_pt_at:
  "\<lbrakk>well_formed spec; opt_cap cap_ref spec = Some cap; is_fake_pt_cap cap\<rbrakk>
   \<Longrightarrow> pt_at (cap_object cap) spec"
  apply (case_tac cap_ref, clarsimp)
  apply (frule (1) well_formed_cap_object)
   apply (fastforce intro: is_fake_pt_cap_cap_has_object)
  apply clarsimp
  apply (frule (2) well_formed_types_match)
   apply (fastforce intro: is_fake_pt_cap_cap_has_object)
  apply (clarsimp simp: is_fake_pt_cap_is_pt_cap object_at_def object_type_is_object)
  done

lemma cap_has_object_cap_irq [simp]:
  "cap_has_object cap \<Longrightarrow> cap_irq cap = undefined"
  by (auto simp: cap_has_object_def cap_irq_def split: cdl_cap.splits)

definition
  cap_at_to_real_object :: "cdl_cap_ref \<Rightarrow> cdl_state \<Rightarrow> bool"
where
  "cap_at_to_real_object cap_ref s =
   cap_at (\<lambda>cap. cap_has_object cap \<and> cap_object cap \<notin> irq_nodes s) cap_ref s"
(* FIXME: Why doesn't every cap pointing to an object not point to an IRQ Node? *)

(* There is a bijection between objects and orig caps. *)
lemma well_formed_bij:
  "well_formed s \<Longrightarrow>
     bij_betw
       (\<lambda>cap_ref. cap_ref_object cap_ref s)
       {cap_ref. original_cap_at cap_ref s \<and>
                 cap_at_to_real_object cap_ref s \<and>
                 cnode_at (fst cap_ref) s}
       ((real_objects s))"
  apply (clarsimp simp: bij_betw_def)
  apply (rule conjI)
  apply (clarsimp simp: inj_on_def real_cap_ref_def cap_ref_object_def
                        object_cap_ref_def cap_at_to_real_object_def cap_at_def)
   apply (erule_tac cap=cap and cap'=capa in well_formed_orig_caps_unique,
          (assumption|fastforce)+)
  apply (clarsimp simp: image_def)
  apply rule
   apply (clarsimp simp: real_cap_ref_def cap_ref_object_def object_cap_ref_def
                         cap_at_to_real_object_def cap_at_def
                         real_objects_def real_object_at_def)
   apply (erule (1) well_formed_cap_object, clarsimp)
  apply clarsimp
  apply (clarsimp simp: real_cap_ref_def cap_ref_object_def
                        real_objects_def real_object_at_def)
  apply (frule_tac well_formed_cap_to_real_object, fastforce simp: real_object_at_def)
  apply (fastforce simp: cap_at_to_real_object_def cap_at_def)
  done

lemma well_formed_irqhandler_bij:
  "well_formed s \<Longrightarrow>
     bij_betw (\<lambda>cap_ref. cap_ref_irq cap_ref s)
              {cap_ref. irqhandler_cap_at cap_ref s}
              (used_irqs s)"
  apply (clarsimp simp: bij_betw_def)
  apply (rule conjI)
   apply (clarsimp simp: inj_on_def real_cap_ref_def cap_ref_object_def
                         object_cap_ref_def cap_at_to_real_object_def cap_at_def)
   apply (erule_tac cap=cap and cap'=capa in well_formed_irqhandler_caps_unique,
          (assumption|clarsimp simp: cap_ref_irq_def)+)
  apply (fastforce simp: image_def used_irqs_def cap_ref_irq_def cap_at_def all_caps_def)
  done

lemma fake_cap_rewrite:
  "well_formed spec \<Longrightarrow>
   Set.filter (\<lambda>cap_ref. fake_pt_cap_at cap_ref spec)
              (SIGMA obj_id:{obj_id. pd_at obj_id spec}.
                     dom (slots_of obj_id spec))
   = {cap_ref. fake_pt_cap_at cap_ref spec}"
  apply (clarsimp simp: cap_at_def opt_cap_def
                 split: option.splits)
  apply (rule)
   apply clarsimp
  apply clarsimp
  apply (frule (2) well_formed_fake_pt_cap_in_pd)
  apply (fastforce)
  done

lemma well_formed_fake_pt_caps_unique:
  "\<lbrakk>well_formed spec; pd_at obj_id spec; pd_at obj_id' spec;
    opt_cap (obj_id, slot) spec = Some cap; opt_cap (obj_id', slot') spec = Some cap';
    is_fake_pt_cap cap; is_fake_pt_cap cap';
    cap_object cap = cap_object cap'\<rbrakk>
   \<Longrightarrow> obj_id = obj_id' \<and> slot = slot'"
  by (fastforce simp: well_formed_def well_formed_fake_pt_caps_unique_def)

lemma well_formed_fake_pt_caps_unique':
  "\<lbrakk>well_formed spec; pd_at obj_id spec; pd_at obj_id' spec;
    fake_pt_cap_at (obj_id, slot) spec; fake_pt_cap_at (obj_id', slot') spec;
    cap_ref_object (obj_id, slot) spec = cap_ref_object (obj_id', slot') spec\<rbrakk>
   \<Longrightarrow> obj_id = obj_id' \<and> slot = slot'"
  by (erule well_formed_fake_pt_caps_unique
                [where cap="the (opt_cap (obj_id, slot) spec)" and
                       cap'="the (opt_cap (obj_id', slot') spec)"],
      (clarsimp simp: cap_ref_object_def cap_at_def)+)

(* There is a bijection between pts and pts in pds. *)
lemma well_formed_pt_cap_bij:
  "well_formed spec \<Longrightarrow>
     bij_betw
       (\<lambda>cap_ref. cap_ref_object cap_ref spec)
       {(obj_id, slot). pd_at obj_id spec \<and> fake_pt_cap_at (obj_id, slot) spec}
       {obj_id. \<exists>cap. cap \<in> all_caps spec \<and> obj_id = cap_object cap \<and> is_fake_pt_cap cap}"
  apply (clarsimp simp: bij_betw_def)
  apply (rule conjI)
   apply (clarsimp simp: inj_on_def)
   apply (erule (5) well_formed_fake_pt_caps_unique')
  apply (rule)
   apply (clarsimp simp: cap_at_def)
   apply (rule_tac x=cap in exI)
   apply (rule conjI, clarsimp)
   apply (clarsimp simp: cap_ref_object_def cap_at_def)
  apply (clarsimp simp: image_def all_caps_def)
  apply (rename_tac obj_id slot)
  apply (rule_tac x=obj_id in exI)
  apply (rule conjI)
   apply (clarsimp simp: opt_cap_def)
   apply (erule (2) well_formed_fake_pt_cap_in_pd)
  apply (rule_tac x=slot in exI)
  apply (clarsimp simp: cap_ref_object_def cap_at_def)
  done

lemma well_formed_objects_real_or_irq:
  "well_formed spec \<Longrightarrow>
  {obj_id. real_object_at obj_id spec} \<union> (cdl_irq_node spec ` used_irqs spec) =
  dom (cdl_objects spec)"
  apply (frule well_formed_well_formed_irqhandler_caps)
  apply (frule well_formed_inj_cdl_irq_node)
  apply (rule)
   apply clarsimp
   apply (rule conjI)
    apply (clarsimp simp: real_object_at_def object_at_def)
   apply (clarsimp simp: used_irqs_def all_caps_def opt_cap_def slots_of_def
                  split: option.splits)
   apply (frule (2) well_formed_well_formed_cap_types_match, simp)
   apply (clarsimp simp: well_formed_cap_types_match_def)
  apply (clarsimp simp: real_object_at_def)
  apply (rule conjI)
   apply clarsimp
  apply clarsimp
  apply (frule (1) well_formed_cap_to_irq_object, simp add: irq_nodes_def)
  apply (fastforce simp: used_irqs_def all_caps_def dest!: injD)
  done

lemma well_formed_objects_only_real_or_irq:
  "well_formed spec \<Longrightarrow>
  {obj_id. real_object_at obj_id spec} \<inter> (cdl_irq_node spec ` used_irqs spec) = {}"
  apply (subst disjoint_iff_not_equal, clarsimp)
  apply (frule (1) well_formed_used_irqs_have_irq_node, clarsimp)
  apply (frule (1) well_formed_cdl_irq_node_irq_nodes)
  apply (auto simp: real_object_at_def)
  done

lemma well_formed_objects_card:
  "\<lbrakk>well_formed spec \<rbrakk>
   \<Longrightarrow> card (used_irqs spec) + card {x. real_object_at x spec} = card (dom (cdl_objects spec))"
  apply (frule well_formed_inj_cdl_irq_node)
  apply (frule well_formed_objects_real_or_irq)
  apply (frule well_formed_objects_only_real_or_irq)
  apply (subgoal_tac " card (used_irqs spec) =  card (used_irq_nodes spec)", simp)
   apply (subst card_Un_Int, simp+)
   apply (simp add: Int_commute Un_commute used_irq_nodes_def)
  by (metis card_image inj_inj_on used_irq_nodes_def)

(****************************************
 * Packing data into a well_formed cap. *
 ****************************************)

lemma update_cap_rights_and_data:
  "\<lbrakk>t (cap_object spec_cap) = Some client_object_id; \<not> is_untyped_cap spec_cap;
    well_formed_cap spec_cap; \<not> vm_cap_has_asid spec_cap; \<not> is_fake_vm_cap spec_cap;
    \<not> is_irqhandler_cap spec_cap; cap_type spec_cap = Some type\<rbrakk>
 \<Longrightarrow> update_cap_data_det
     (cap_data spec_cap)
     (update_cap_rights (cap_rights spec_cap)
                        (default_cap type {client_object_id} (cnode_cap_size spec_cap) (is_device_cap spec_cap))) =
  update_cap_object client_object_id spec_cap"
  apply (case_tac "\<not>is_cnode_cap spec_cap")
   apply (case_tac spec_cap, simp_all add: cap_type_def,
          (fastforce simp: cap_data_def cap_rights_def default_cap_def
                           update_cap_rights_def badge_update_def update_cap_badge_def
                           update_cap_object_def update_cap_data_det_def
                           well_formed_cap_def Word.less_mask_eq
                           is_fake_vm_cap_def validate_vm_rights_def
                           vm_read_write_def vm_read_only_def
                   split:  cdl_frame_cap_type.splits)+)
  apply (case_tac spec_cap, simp_all add: cap_type_def)
  apply (rename_tac word1 word2 nat1 nat2)
  apply (clarsimp simp: update_cap_data_det_def update_cap_rights_def
                        default_cap_def well_formed_cap_def update_cap_object_def
                        cap_rights_def cap_data_def cnode_cap_size_def)
  apply (case_tac "guard_as_rawdata (CNodeCap word1 word2 nat1 nat2) = 0")
   apply (clarsimp simp: guard_update_def guard_as_rawdata_def)
   apply (cut_tac p="word2 << 8" and d="of_nat nat1 << 3" and n=8 in is_aligned_add_or)
     apply (simp add: is_aligned_shiftl)
    apply (rule shiftl_less_t2n)
     apply (clarsimp simp: guard_bits_def word_of_nat_less)
    apply simp
   apply (clarsimp simp: word_or_zero)
   apply (drule word_shift_zero, erule less_imp_le)
    apply (clarsimp simp: guard_bits_def)
   apply (drule_tac m=8 in word_shift_zero, rule less_imp_le)
     apply (clarsimp simp: guard_bits_def word_of_nat_less)
    apply simp
   apply (clarsimp simp: of_nat_0 guard_bits_def word_bits_def)
   apply (clarsimp simp: badge_update_def cap_rights_def cap_data_def
                         guard_update_def guard_as_rawdata_def)
  apply (cut_tac p="word2 << 8" and d="of_nat nat1 << 3" and n=8 in is_aligned_add_or)
    apply (simp add: is_aligned_shiftl)
   apply (rule shiftl_less_t2n)
    apply (clarsimp simp: guard_bits_def word_of_nat_less)
   apply simp
  apply (simp add: word_ao_dist shiftr_over_or_dist shiftl_shiftr1 word_size
                   word_bw_assocs mask_and_mask guard_as_rawdata_def guard_update_def)
  apply (subst le_mask_iff[THEN iffD1])
   apply (rule plus_one_helper)
   apply (unfold mask_plus_1)
   apply (rule shiftl_less_t2n)
    apply (clarsimp simp: guard_bits_def word_of_nat_less)
   apply simp
  apply (subst less_mask_eq)
   apply (subst less_mask_eq)
    apply (clarsimp simp: guard_bits_def word_of_nat_less)
   apply (subst unat_of_nat32)
    apply (clarsimp simp: guard_bits_def word_bits_def)
   apply (clarsimp simp: min_def guard_bits_def)
  apply simp
  apply (subst less_mask_eq)
   apply (clarsimp simp: guard_bits_def word_of_nat_less)
  apply (clarsimp simp: guard_bits_def word_of_nat_less word_bits_def unat_of_nat32)
  done

lemma update_cap_data:
  "\<lbrakk>t (cap_object spec_cap) = Some client_object_id;
    cap_type spec_cap = Some type; cap_data spec_cap = data;
    well_formed_cap spec_cap; \<not> is_untyped_cap spec_cap;
    \<not> vm_cap_has_asid spec_cap; \<not> is_fake_vm_cap spec_cap; \<not> is_irqhandler_cap spec_cap;
    cap_rights (default_cap type {obj_id} sz (is_device_cap spec_cap)) = cap_rights spec_cap;
    dev = is_device_cap spec_cap\<rbrakk>
 \<Longrightarrow> update_cap_data_det data (default_cap type {client_object_id} (cnode_cap_size spec_cap) dev) =
     update_cap_object client_object_id spec_cap"
  apply (frule (6) update_cap_rights_and_data)
  apply clarsimp
  apply (subgoal_tac "\<And>dev. update_cap_rights
                      (cap_rights spec_cap)
                      (default_cap type {client_object_id} (cnode_cap_size spec_cap) dev)
                     = default_cap type {client_object_id} (cnode_cap_size spec_cap) dev")
   apply clarsimp
  apply (subst well_formed_update_cap_rights_idem)
    apply (erule (1) default_cap_well_formed_cap, simp)
   apply (subst cap_rights_default_cap_eq, fast)
  apply simp
  done

lemma well_formed_frame_in_pt:
  "\<lbrakk>well_formed spec;
    opt_cap (pt, pt_slot) spec = Some frame_cap;
    frame_cap \<noteq> NullCap;
    pt_at pt spec\<rbrakk>
   \<Longrightarrow> \<exists>sz. cap_type frame_cap = Some (FrameType sz) \<and>
           (sz = 12 \<or> sz = 16) \<and>
           is_fake_vm_cap frame_cap"
  apply (clarsimp simp: well_formed_def object_at_def)
  apply (drule_tac x = pt in spec)
  apply (clarsimp simp: well_formed_vspace_def opt_cap_def slots_of_def
                 split: option.split_asm)
  done

lemma well_formed_frame_in_pd:
  "\<lbrakk>well_formed spec;
    opt_cap (pd, pt_slot) spec = Some frame_cap;
    pd_at pd spec;
    is_frame_cap frame_cap\<rbrakk>
   \<Longrightarrow> (\<exists>sz. cap_type frame_cap = Some (FrameType sz) \<and> (sz = 20 \<or> sz = 24)) \<and>
      is_fake_vm_cap frame_cap \<and>
      \<not> is_device_cap frame_cap"
  apply (clarsimp simp: well_formed_def object_at_def)
  apply (drule_tac x = pd in spec)
  apply (clarsimp simp: well_formed_vspace_def opt_cap_def slots_of_def
                 split: option.split_asm)
  apply (drule_tac x = pt_slot in spec)
  apply (drule_tac x = frame_cap in spec)
  apply (clarsimp simp: is_fake_pt_cap_def cap_type_def
                 split: cdl_cap.splits)
  apply (clarsimp simp: cap_at_def opt_cap_def slots_of_def
              simp del: split_paired_All)
  apply (drule_tac x = pd in spec)
  apply (drule_tac x = pt_slot in spec)
  apply fastforce
  done

lemma well_formed_no_dev: "well_formed spec \<Longrightarrow> \<forall>slot. \<not> cap_at is_device_cap slot spec"
  by (clarsimp simp: well_formed_def)

lemma well_formed_frame_cap[simp]:
  "well_formed_cap (FrameCap x y rights a b R) \<longleftrightarrow>
     R = None \<and> (rights = vm_read_write \<or> rights = vm_read_only)"
  apply (clarsimp simp: well_formed_cap_def split: cdl_frame_cap_type.splits)
  apply (rule iffI; clarsimp?)
  done

lemma wf_cap_in_pt_is_frame:
  "well_formed spec \<Longrightarrow>
   page_cap \<noteq> NullCap \<Longrightarrow>
   pt_at pt_id spec \<Longrightarrow>
   opt_cap (pt_id, slot) spec = Some page_cap \<Longrightarrow>
   page_cap = fake_frame_cap False (cap_object page_cap)
                                   (validate_vm_rights (cap_rights page_cap))
                                   (cap_size_bits page_cap) \<and>
  (cap_size_bits page_cap = 12 \<or> cap_size_bits page_cap = 16)"
  apply (frule well_formed_frame_in_pt, fastforce+)
  apply (clarsimp simp: cap_type_def cap_rights_def cap_size_bits_def split: cdl_cap.splits)
  apply (frule well_formed_well_formed_cap[where obj_id=pt_id])
     apply (fastforce intro: object_slots_opt_capI)+
  apply clarsimp
  apply (drule well_formed_no_dev, clarsimp simp: cap_at_def)
  apply (fastforce simp: fake_vm_cap_simp)
  done

lemma wf_frame_cap_in_pd:
  "well_formed spec \<Longrightarrow>
   page_cap \<noteq> NullCap \<Longrightarrow>
   pd_at pd_id spec \<Longrightarrow>
   opt_cap (pd_id, slot) spec = Some page_cap \<Longrightarrow>
   frame_at (cap_object page_cap) spec \<Longrightarrow>
   page_cap = fake_frame_cap False (cap_object page_cap)
                                   (validate_vm_rights (cap_rights page_cap))
                                   (cap_size_bits page_cap) \<and>
   (cap_size_bits page_cap = 20 \<or> cap_size_bits page_cap = 24)"
  apply (frule well_formed_frame_in_pd, fastforce+)
   apply (frule well_formed_types_match, fastforce+)
    using object_type_is_object(9) object_type_object_at(9) wf_pd_cap_has_object apply blast
   apply (frule object_at_object_type(10)[rotated], rule classical, fastforce)
   apply (fastforce simp: cap_type_def split: cdl_cap.splits)
  apply (clarsimp simp: cap_type_def cap_rights_def cap_size_bits_def split: cdl_cap.splits)
  apply (frule well_formed_well_formed_cap[where obj_id=pd_id])
     apply fastforce
    apply (fastforce intro: object_slots_opt_capI)
   apply (fastforce simp: fake_vm_cap_simp)+
  done

lemma wf_pt_in_pd_fake_and_none:
  "well_formed spec \<Longrightarrow>
   page_cap \<noteq> NullCap \<Longrightarrow>
   pd_at pd_id spec \<Longrightarrow>
   opt_cap (pd_id, slot) spec = Some page_cap \<Longrightarrow>
   pt_at (cap_object page_cap) spec \<Longrightarrow>
   page_cap = PageTableCap (cap_object page_cap) Fake None"
  apply (clarsimp simp: object_at_def)
  apply (frule well_formed_types_match[where obj_id=pd_id and slot=slot])
     apply fastforce+
     using object_at_def wf_pd_cap_has_object
   apply blast
  apply (clarsimp simp: object_type_is_object)
  apply (frule well_formed_pt_cap_is_fake_pt_cap[where obj_id=pd_id and slot=slot])
     apply fastforce
    apply (clarsimp simp: object_at_def)
    apply (clarsimp simp: object_type_is_object)
   apply (frule (1) well_formed_well_formed_cap[where obj_id=pd_id and slot=slot])
     apply (clarsimp simp: opt_cap_def slots_of_def split: option.splits)
     apply fastforce+
  apply (clarsimp simp: cap_type_def is_fake_pt_cap_pt_cap split: cdl_cap.splits)
  using well_formed_well_formed_cap' wf_cap_pt_cap by blast

lemma well_formed_pd_slots_have_objects:
  "\<lbrakk>well_formed spec; pd_at pd_id spec; slot \<in> dom (slots_of pd_id spec);
    slots_of pd_id spec slot = Some cap; cap \<noteq> NullCap\<rbrakk>
   \<Longrightarrow> cap_has_object cap"
  apply (drule (1) wf_pd_cap_has_object[where cap=cap and slot=slot])
    apply (clarsimp simp: opt_cap_def)+
  done

lemma well_formed_pd_slot_limited:
  "\<lbrakk>well_formed spec; pd_at obj_id spec; slots_of obj_id spec slot = Some cap\<rbrakk>
   \<Longrightarrow> slot < 4096"
  apply (clarsimp simp:well_formed_def object_at_def)
  apply (drule_tac x = obj_id in spec)
  apply (clarsimp simp: is_pd_def object_type_simps object_default_state_def slots_of_def,
              simp add: default_object_def object_type_simps object_slots_def empty_cap_map_def
                 split: cdl_object.split_asm option.split_asm)
  apply fastforce
  done

lemma well_formed_pd_frame_or_pt:
  "well_formed spec \<Longrightarrow>
   pd_at pd_ptr spec \<Longrightarrow>
   opt_cap (pd_ptr,slot) spec = Some slot_cap \<Longrightarrow>
   cap_object slot_cap = ptr \<Longrightarrow>
   slot_cap \<noteq> NullCap \<Longrightarrow>
   frame_at ptr spec \<noteq> pt_at ptr spec"
  apply (frule (3) well_formed_pd[where obj_id=pd_ptr and slot=slot])
  apply clarsimp
  apply (frule (3) wf_pd_cap_has_object)
  apply (frule (2) well_formed_cap_object)
  apply clarsimp
  apply (safe; (fastforce simp: object_at_def dest: not_frame_and_pt)?)
   apply (frule well_formed_types_match[where obj_id=pd_ptr and slot=slot], fastforce+)
   apply (fastforce simp: object_type_is_object(10) intro: object_at_cdl_objects)
  apply (frule well_formed_types_match[where obj_id=pd_ptr and slot=slot], fastforce+)
  using is_fake_pt_cap_is_pt_cap object_type_is_object(8) by (fastforce intro: object_at_cdl_objects)

end

end
