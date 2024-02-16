(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
 * The layout of the capability space and other parts of the system-initialiser.
 *)
theory RootTask_SI
imports WellFormed_SI SysInit_SI
begin

(******************************************************************
 * Definition of the CSpace of the root task.                     *
 * This requires a default cap to all of the objects created,     *
 * and a copy of caps to all of the CNodes (for installing caps). *
 ******************************************************************)

consts
  si_cnode_id      :: cdl_object_id
  si_asidpool_id   :: cdl_object_id
  si_asidpool_base :: nat

definition
  si_cnode_size :: cdl_size_bits
where
  "si_cnode_size = 12"

(* If we axioimise this size, we need it to be smaller than the word size.
 * We need this to prove that:
   - word_bits - si_cnode_size + si_cnode_size = word_bits.
   - offset (of_nat slot) si_cnode_size = slot
 *)
lemma si_cnode_size_less_than_word_size [simp]:
  "si_cnode_size < word_bits"
  by (clarsimp simp: si_cnode_size_def word_bits_def)

lemma si_cnode_size_less_than_eq_word_size [simp]:
  "si_cnode_size \<le> word_bits"
  by (rule less_imp_le_nat, simp)

lemma si_cnode_size_greater_than_1 [simp]:
  "1 < si_cnode_size"
  by (clarsimp simp: si_cnode_size_def)

lemma si_cnode_size_greater_than_2 [simp]:
  "2 < si_cnode_size"
  by (clarsimp simp: si_cnode_size_def)

lemma unat_less_2_si_cnode_size:
  "unat (cptr::32 word) < 2 ^ si_cnode_size
  \<Longrightarrow> cptr < 2 ^ si_cnode_size"
  by (metis si_cnode_size_less_than_word_size unat_power_lower32 word_less_nat_alt)

lemma unat_less_2_si_cnode_size':
  "(cptr::32 word) < 2 ^ si_cnode_size
  \<Longrightarrow> unat cptr < 2 ^ si_cnode_size"
  by (metis unat_less_helper word_unat_power)

(* This is stored in the root TCB. *)
definition
  si_cspace_cap :: cdl_cap
where
  "si_cspace_cap = CNodeCap si_cnode_id 0 (word_bits - si_cnode_size) si_cnode_size"

(* This is the cap the root TCB has to its own root cnode (stored in its root CNode). *)
definition
  si_cnode_cap :: cdl_cap
where
  "si_cnode_cap = CNodeCap si_cnode_id 0 (word_bits - si_cnode_size) si_cnode_size"

definition
  root_tcb :: cdl_object
where
  "root_tcb = update_slots [tcb_cspace_slot \<mapsto> si_cspace_cap,
                            tcb_vspace_slot \<mapsto> undefined,
                            tcb_replycap_slot \<mapsto> undefined,
                            tcb_caller_slot \<mapsto> undefined,
                            tcb_ipcbuffer_slot \<mapsto> undefined,
                            tcb_pending_op_slot \<mapsto> undefined] (Tcb (default_tcb minBound))"

definition
  empty_asid :: cdl_asid_pool
where
  "empty_asid = \<lparr>cdl_asid_pool_caps = empty_cap_map asid_low_bits\<rparr>"

definition
  si_asid :: "sep_state \<Rightarrow> bool"
where
  "si_asid \<equiv>
  (si_cnode_id, unat seL4_CapInitThreadASIDPool) \<mapsto>c AsidPoolCap si_asidpool_id si_asidpool_base \<and>*
    si_asidpool_id \<mapsto>f AsidPool empty_asid \<and>*
   (\<And>* offset\<in>{offset. offset < 2 ^ asid_low_bits}.
               (si_asidpool_id, offset) \<mapsto>c -)"

abbreviation "si_tcb_id \<equiv> root_tcb_id"

definition si_objects :: "sep_state \<Rightarrow> bool"
where
  "si_objects \<equiv>
   si_tcb_id \<mapsto>f root_tcb \<and>*
   si_cnode_id \<mapsto>f CNode (empty_cnode si_cnode_size) \<and>*
  (si_tcb_id, tcb_cspace_slot) \<mapsto>c si_cspace_cap \<and>*
  (si_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
  (si_cnode_id, unat seL4_CapInitThreadCNode) \<mapsto>c si_cnode_cap \<and>*
  (si_cnode_id, unat seL4_CapIRQControl) \<mapsto>c IrqControlCap \<and>*
   si_asid"

definition
  si_objects_extra_caps' :: "cdl_object_id set \<Rightarrow> cdl_cptr list \<Rightarrow> cdl_cptr list \<Rightarrow> sep_state \<Rightarrow> bool"
where
  "si_objects_extra_caps' obj_ids free_cptrs untyped_cptrs \<equiv> \<lambda>s.
   \<exists>untyped_caps all_available_ids.
    ((\<And>* (cptr, cap) \<in> set (zip untyped_cptrs untyped_caps). (si_cnode_id, unat cptr) \<mapsto>c cap) \<and>*
     (\<And>* cptr \<in> set (drop (card obj_ids) free_cptrs). (si_cnode_id, unat cptr) \<mapsto>c NullCap) \<and>*
     (\<And>* obj_id\<in>all_available_ids. obj_id \<mapsto>o Untyped)) s"

definition
  si_objects_extra_caps :: "cdl_object_id set \<Rightarrow> cdl_cptr list \<Rightarrow> cdl_cptr list
                          \<Rightarrow> cdl_state \<Rightarrow> sep_state \<Rightarrow> bool"
where
  "si_objects_extra_caps obj_ids free_cptrs untyped_cptrs spec \<equiv> \<lambda>s.
   \<exists>untyped_caps all_available_ids.
    ((\<And>* (cptr, cap) \<in> set (zip untyped_cptrs untyped_caps). (si_cnode_id, unat cptr) \<mapsto>c cap) \<and>*
     (\<And>* cptr \<in> set (drop (card obj_ids + card {obj_id \<in> obj_ids. cnode_or_tcb_at obj_id spec}) free_cptrs).
         (si_cnode_id, unat cptr) \<mapsto>c NullCap) \<and>*
     (\<And>* obj_id\<in>all_available_ids. obj_id \<mapsto>o Untyped)) s"


lemma distinct_take_drop_append:
  "distinct xs \<Longrightarrow> set (take b (drop a xs)) \<inter> set (drop (a + b) xs) = {}"
  by (metis distinct_append distinct_drop take_drop_append)

lemma si_objects_extra_caps'_si_objects_extra_caps:
  "distinct free_slots \<Longrightarrow>
     si_objects_extra_caps' obj_ids free_slots untyped_cptrs =
    (si_objects_extra_caps obj_ids free_slots untyped_cptrs spec \<and>*
    (\<And>* cptr \<in> set (take (card {obj_id \<in> obj_ids. cnode_or_tcb_at obj_id spec})
                       (drop (card obj_ids) free_slots)).
           (si_cnode_id, unat cptr) \<mapsto>c NullCap))"
  apply (rule ext)
  apply (clarsimp simp: si_objects_extra_caps'_def si_objects_extra_caps_def sep_conj_exists)
  apply (rule ex_eqI)+
  apply (subst take_drop_append [where a="card obj_ids" and
               b="card {obj_id \<in> obj_ids. cnode_or_tcb_at obj_id spec}"])
  apply clarsimp
  apply (subst sep.prod.union_disjoint, (simp add: distinct_take_drop_append)+)+
  apply (clarsimp simp: sep_conj_ac)
  done

definition
  si_irq_nodes :: "cdl_state \<Rightarrow> sep_state \<Rightarrow> bool"
where
  "si_irq_nodes spec \<equiv>
     (\<lambda>s. \<exists>k_irq_table. (\<And>* irq\<in>used_irqs spec. irq \<mapsto>irq k_irq_table irq \<and>*
                                                 k_irq_table irq \<mapsto>o IRQNode empty_irq_node) s)"


(***************************************
 * Lemmas about the root task objects. *
 ***************************************)

lemma is_cnode_cap_si_cspace_cap [simp]:
  "is_cnode_cap si_cspace_cap"
  by (clarsimp simp: si_cspace_cap_def)

lemma is_cnode_cap_si_cnode_cap [simp]:
  "is_cnode_cap si_cnode_cap"
  by (clarsimp simp: si_cnode_cap_def)

lemma is_tcb_root_tcb [simp]:
  "is_tcb root_tcb"
  by (clarsimp simp: root_tcb_def)

lemma cap_guard_size_si_cnode_cap_plus_si_cnode_size [simp]:
  "cap_guard_size si_cnode_cap + si_cnode_size = word_bits"
  by (clarsimp simp: si_cnode_cap_def)

lemma cap_object_si_cspace_cap [simp]:
  "cap_object si_cspace_cap = si_cnode_id"
  by (clarsimp simp: cap_object_def cap_has_object_def si_cspace_cap_def)

lemma cap_object_si_cnode_cap [simp]:
  "cap_object si_cnode_cap = si_cnode_id"
  by (clarsimp simp: cap_object_def cap_has_object_def si_cnode_cap_def)


lemma offset_slot_si_cnode_size:
  "slot < 2^si_cnode_size \<Longrightarrow> offset (of_nat slot) si_cnode_size = slot"
  by (clarsimp simp: offset_slot)

lemma offset_slot_si_cnode_size':
  "slot < 2^si_cnode_size \<Longrightarrow> offset slot si_cnode_size = unat slot"
  by (clarsimp simp: offset_slot')

lemma guard_equal_si_cspace_cap:
  "src_index < 2 ^ si_cnode_size \<Longrightarrow> guard_equal si_cspace_cap src_index 32"
  apply (clarsimp simp: si_cspace_cap_def guard_equal_def Let_unfold)
  apply (subst and_mask_eq_iff_shiftr_0 [THEN iffD1])
   apply (clarsimp simp: word_bits_def)
   apply (erule less_mask_eq)
  apply (clarsimp simp: mask_def)
  done

lemma guard_equal_si_cspace_cap':
  "src_index < 2 ^ si_cnode_size \<Longrightarrow> guard_equal si_cspace_cap src_index word_bits"
  by (drule guard_equal_si_cspace_cap, simp add: word_bits_def)

lemma guard_equal_si_cnode_cap:
  "src_index < 2 ^ si_cnode_size \<Longrightarrow> guard_equal si_cnode_cap src_index 32"
  apply (clarsimp simp: si_cnode_cap_def guard_equal_def Let_unfold)
  apply (subst and_mask_eq_iff_shiftr_0 [THEN iffD1])
   apply (clarsimp simp: word_bits_def)
   apply (erule less_mask_eq)
  apply (clarsimp simp: mask_def)
  done

lemma seL4_CapInitThreadASIDPool_si_cnode_size [simp]:
  "seL4_CapInitThreadASIDPool < 2 ^ si_cnode_size"
  by (clarsimp simp: seL4_CapInitThreadASIDPool_def si_cnode_size_def)

lemma guard_equal_si_cspace_cap_seL4_CapInitThreadASIDPool [simp]:
  "guard_equal si_cspace_cap seL4_CapInitThreadASIDPool word_bits"
  by (rule guard_equal_si_cspace_cap', simp)

lemma si_cspace_cap_guard_equal:
  "guard_equal si_cnode_cap src_index 32 \<Longrightarrow> src_index < 2 ^ si_cnode_size"
  apply (clarsimp simp: si_cnode_cap_def guard_equal_def
                        Let_unfold si_cnode_size_def)
  apply (subst (asm) shiftr_mask_eq')
   apply (simp add: word_bits_size word_bits_def)
  apply (subst (asm) le_mask_iff [symmetric])
  apply (clarsimp simp: mask_def)
  apply (insert word32_less_sub_le [where x=src_index and n=12])
  apply (clarsimp simp: word_bits_def)
  done

lemma one_lvl_lookup_si_cspace_cap [simp]:
  "one_lvl_lookup si_cspace_cap word_bits si_cnode_size"
  by (clarsimp simp: one_lvl_lookup_def si_cspace_cap_def)

lemmas one_lvl_lookup_si_cspace_cap' [simp] =
       one_lvl_lookup_si_cspace_cap [simplified word_bits_def, simplified]

lemma one_lvl_lookup_si_cnode_cap [simp]:
  "one_lvl_lookup si_cnode_cap word_bits si_cnode_size"
  by (clarsimp simp: one_lvl_lookup_def si_cnode_cap_def)

lemmas one_lvl_lookup_si_cnode_cap' [simp] =
       one_lvl_lookup_si_cnode_cap [simplified word_bits_def, simplified]

lemma obj_tcb_root_tcb [simp]:
  "Tcb (obj_tcb root_tcb) = root_tcb"
  by (clarsimp simp: obj_tcb_def root_tcb_def update_slots_def)

(***************************
 * Lemmas about word size. *
 ***************************)
lemma seL4_CapInitThreadCNode_less_than_si_cnode_size [simp]:
  "seL4_CapInitThreadCNode < 2 ^ si_cnode_size"
  apply (insert si_cnode_size_greater_than_1)
  apply (insert power_strict_increasing [where n=1 and a="(2::nat)" and N=si_cnode_size, simplified])
  apply (clarsimp)
  apply (drule  of_nat_less_pow_32)
   apply (clarsimp simp: seL4_CapInitThreadCNode_def)+
  done

lemma offset_seL4_CapInitThreadCNode [simp]:
  "offset seL4_CapInitThreadCNode si_cnode_size = unat seL4_CapInitThreadCNode"
  by (rule offset_slot', simp)

lemma seL4_CapIRQControl_less_than_si_cnode_size [simp]:
  "seL4_CapIRQControl < 2 ^ si_cnode_size"
  apply (simp add: seL4_CapIRQControl_def)
  apply (insert si_cnode_size_greater_than_2)
  apply (insert power_strict_increasing [where n=2 and a="(2::nat)" and N=si_cnode_size, simplified])
  apply (drule  of_nat_less_pow_32, simp_all)
  done

lemma offset_seL4_CapIRQControl [simp]:
  "offset seL4_CapIRQControl si_cnode_size = unat seL4_CapIRQControl"
  by (rule offset_slot', simp)

(* There is a cap in the root cnode that points to the obj_id specified.
 * This cap should be the default cap to that object.
 *
 * This predicate can be used for spec objects, or the duplicated cnode caps.
 *)
definition si_cap_at :: "(cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow>
                           (cdl_object_id \<Rightarrow> cdl_cptr option) \<Rightarrow> cdl_state \<Rightarrow> bool \<Rightarrow>
                            cdl_object_id \<Rightarrow> sep_pred"
where
  "si_cap_at t si_caps spec dev obj_id \<equiv> \<lambda>s.
    \<exists>cap_ptr slot obj kobj_id.
     ((si_cnode_id, slot) \<mapsto>c default_cap (object_type obj) {kobj_id} (object_size_bits obj) dev) s \<and>
     si_caps obj_id = Some cap_ptr \<and>
     unat cap_ptr = slot \<and>
     cap_ptr < 2 ^ si_cnode_size \<and>
     cdl_objects spec obj_id = Some obj \<and>
     t obj_id = Some kobj_id"

definition si_irq_cap_at :: "(cdl_irq \<Rightarrow> cdl_cptr option) \<Rightarrow> cdl_state \<Rightarrow>
                                cdl_irq \<Rightarrow> sep_pred"
where
  "si_irq_cap_at si_irq_caps spec irq \<equiv> \<lambda>s.
    \<exists>cap_ptr slot.
     ((si_cnode_id, slot) \<mapsto>c IrqHandlerCap irq) s \<and>
     si_irq_caps irq = Some cap_ptr \<and>
     unat cap_ptr = slot \<and>
     cap_ptr < 2 ^ si_cnode_size"

definition si_caps_at :: "(cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow>
                           (cdl_object_id \<Rightarrow> cdl_cptr option) \<Rightarrow> cdl_state \<Rightarrow> bool \<Rightarrow>
                            cdl_object_id set \<Rightarrow> sep_pred"
where
  "si_caps_at t si_caps spec dev obj_ids \<equiv>
  \<And>* obj_id \<in> obj_ids. (si_cap_at t si_caps spec) dev obj_id"

definition si_irq_caps_at :: "(cdl_irq \<Rightarrow> cdl_cptr option) \<Rightarrow> cdl_state \<Rightarrow>
                                cdl_irq set \<Rightarrow> sep_pred"
where
  "si_irq_caps_at si_irq_caps spec irqs \<equiv>
  \<And>* irq \<in> irqs. si_irq_cap_at si_irq_caps spec irq"

definition
  si_obj_cap_at' :: " (cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow>
                        (cdl_object_id \<Rightarrow> cdl_cptr option) \<Rightarrow> cdl_state \<Rightarrow> bool \<Rightarrow>
                         cdl_object_id \<Rightarrow> cdl_cnode_index \<Rightarrow> sep_pred"
where
  "si_obj_cap_at' t si_caps spec dev obj_id slot \<equiv> \<lambda>s. \<exists> spec_cap.
   si_cap_at t si_caps spec dev (cap_object spec_cap) s \<and>
   opt_cap (obj_id, slot) spec = Some spec_cap"

definition si_obj_cap_at where
  "si_obj_cap_at t si_caps spec dev obj_id slot \<equiv>
     if original_cap_at (obj_id, slot) spec \<and> cap_at cap_has_object (obj_id, slot) spec
     then si_obj_cap_at' t si_caps spec dev obj_id slot
     else \<box>"

definition
  si_obj_caps_at :: "(cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow>
                            (cdl_object_id \<Rightarrow> cdl_cptr option) \<Rightarrow> cdl_state \<Rightarrow> bool \<Rightarrow>
                             cdl_object_id \<Rightarrow> sep_pred"
where
  "si_obj_caps_at t si_caps spec dev obj_id \<equiv>
   \<And>* slot \<in> dom (slots_of obj_id spec). si_obj_cap_at t si_caps spec dev obj_id slot"

definition
  si_objs_caps_at :: "(cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow>
                             (cdl_object_id \<Rightarrow> cdl_cptr option) \<Rightarrow> cdl_state \<Rightarrow> bool \<Rightarrow>
                              cdl_object_id set \<Rightarrow> sep_pred"
where
  "si_objs_caps_at t si_caps spec dev obj_ids \<equiv>
   \<And>* obj_id \<in> obj_ids. (si_obj_caps_at t si_caps spec) dev obj_id"

definition
  si_spec_irq_cap_at' :: "(cdl_irq \<Rightarrow> cdl_cptr option) \<Rightarrow> cdl_state \<Rightarrow>
                             cdl_object_id \<Rightarrow> cdl_cnode_index \<Rightarrow> sep_pred"
where
  "si_spec_irq_cap_at' si_irq_caps spec obj_id slot \<equiv> \<lambda>s. \<exists> spec_cap.
   si_irq_cap_at si_irq_caps spec (cap_irq spec_cap) s \<and>
   opt_cap (obj_id, slot) spec = Some spec_cap"

definition si_spec_irq_cap_at where
  "si_spec_irq_cap_at si_irq_caps spec obj_id slot \<equiv>
     if irqhandler_cap_at (obj_id, slot) spec
     then si_spec_irq_cap_at' si_irq_caps spec obj_id slot
     else \<box>"

definition
  si_spec_irq_caps_at :: "(cdl_irq \<Rightarrow> cdl_cptr option) \<Rightarrow> cdl_state \<Rightarrow>
                             cdl_object_id \<Rightarrow> sep_pred"
where
  "si_spec_irq_caps_at si_irq_caps spec obj_id \<equiv>
   \<And>* slot \<in> dom (slots_of obj_id spec). si_spec_irq_cap_at si_irq_caps spec obj_id slot"

definition
  si_spec_irqs_caps_at :: "(cdl_irq \<Rightarrow> cdl_cptr option) \<Rightarrow> cdl_state \<Rightarrow>
                              cdl_object_id set \<Rightarrow> sep_pred"
where
  "si_spec_irqs_caps_at si_irq_caps spec obj_ids \<equiv>
   \<And>* obj_id \<in> obj_ids. si_spec_irq_caps_at si_irq_caps spec obj_id"

definition
  "si_null_cap_at t si_irq_caps spec obj_id \<equiv>
    \<lambda>s. \<exists>cap_ptr slot obj kobj_id.
       ((si_cnode_id, slot) \<mapsto>c NullCap) s \<and>
       si_irq_caps obj_id = Some cap_ptr \<and>
       unat cap_ptr = slot \<and>
       cap_ptr < 2 ^ si_cnode_size \<and>
       cdl_objects spec obj_id = Some obj \<and> t obj_id = Some kobj_id"

definition
  "si_null_irq_cap_at si_irq_caps spec irq \<equiv>
    \<lambda>s. \<exists>cap_ptr slot.
       ((si_cnode_id, slot) \<mapsto>c NullCap) s \<and>
       si_irq_caps irq = Some cap_ptr \<and>
       unat cap_ptr = slot \<and>
       cap_ptr < 2 ^ si_cnode_size"

definition
  si_spec_obj_null_cap_at' :: " (cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow>
                                  (cdl_object_id \<Rightarrow> cdl_cptr option) \<Rightarrow> cdl_state \<Rightarrow>
                                   cdl_object_id \<Rightarrow> cdl_cnode_index \<Rightarrow> sep_pred"
where
  "si_spec_obj_null_cap_at' t si_irq_caps spec obj_id slot \<equiv> \<lambda>s. \<exists> spec_cap.
   si_null_cap_at t si_irq_caps spec (cap_object spec_cap) s \<and>
   opt_cap (obj_id, slot) spec = Some spec_cap"

definition si_spec_obj_null_cap_at where
  "si_spec_obj_null_cap_at t si_irq_caps spec obj_id slot \<equiv>
     if original_cap_at (obj_id, slot) spec \<and> cap_at cap_has_object (obj_id, slot) spec
     then si_spec_obj_null_cap_at' t si_irq_caps spec obj_id slot
     else \<box>"

definition
  si_spec_obj_null_caps_at :: "(cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow>
                                 (cdl_object_id \<Rightarrow> cdl_cptr option) \<Rightarrow> cdl_state \<Rightarrow>
                                  cdl_object_id \<Rightarrow> sep_pred"
where
  "si_spec_obj_null_caps_at t si_irq_caps spec obj_id \<equiv>
   \<And>* slot \<in> dom (slots_of obj_id spec). si_spec_obj_null_cap_at t si_irq_caps spec obj_id slot"

definition
  si_spec_objs_null_caps_at :: "(cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow>
                                  (cdl_object_id \<Rightarrow> cdl_cptr option) \<Rightarrow> cdl_state \<Rightarrow>
                                   cdl_object_id set \<Rightarrow> sep_pred"
where
  "si_spec_objs_null_caps_at t si_irq_caps spec obj_ids \<equiv>
   \<And>* obj_id \<in> obj_ids. si_spec_obj_null_caps_at t si_irq_caps spec obj_id"

definition
  si_spec_irq_null_cap_at' :: "(cdl_irq \<Rightarrow> cdl_cptr option) \<Rightarrow> cdl_state \<Rightarrow>
                                  cdl_object_id \<Rightarrow> cdl_cnode_index \<Rightarrow> sep_pred"
where
  "si_spec_irq_null_cap_at' si_irq_caps spec obj_id slot \<equiv> \<lambda>s. \<exists> spec_cap.
   si_null_irq_cap_at si_irq_caps spec (cap_irq spec_cap) s \<and>
   opt_cap (obj_id, slot) spec = Some spec_cap \<and> \<not>is_untyped_cap spec_cap"

definition si_spec_irq_null_cap_at where
  "si_spec_irq_null_cap_at si_irq_caps spec obj_id slot \<equiv>
     if irqhandler_cap_at (obj_id, slot) spec
     then si_spec_irq_null_cap_at' si_irq_caps spec obj_id slot
     else \<box>"

definition
  si_spec_irq_null_caps_at :: "(cdl_irq \<Rightarrow> cdl_cptr option) \<Rightarrow> cdl_state \<Rightarrow>
                                  cdl_object_id \<Rightarrow> sep_pred"
where
  "si_spec_irq_null_caps_at si_irq_caps spec obj_id \<equiv>
   \<And>* slot \<in> dom (slots_of obj_id spec). si_spec_irq_null_cap_at si_irq_caps spec obj_id slot"

definition
  si_spec_irqs_null_caps_at :: "(cdl_irq \<Rightarrow> cdl_cptr option) \<Rightarrow> cdl_state \<Rightarrow>
                                   cdl_object_id set \<Rightarrow> sep_pred"
where
  "si_spec_irqs_null_caps_at si_irq_caps spec obj_ids \<equiv>
   \<And>* obj_id \<in> obj_ids. si_spec_irq_null_caps_at si_irq_caps spec obj_id"

definition si_null_caps_at :: "(cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow>
                           (cdl_object_id \<Rightarrow> cdl_cptr option) \<Rightarrow> cdl_state \<Rightarrow>
                            cdl_object_id set \<Rightarrow> sep_pred"
where
  "si_null_caps_at t si_caps spec obj_ids \<equiv>
  \<And>* obj_id \<in> obj_ids. si_null_cap_at t si_caps spec obj_id"


lemma si_cap_at_less_si_cnode_size:
  "\<lbrakk>\<guillemotleft>si_cap_at t opt_sel4_cap spec dev obj_id \<and>* R\<guillemotright> s;
    Some cap_ptr = opt_sel4_cap obj_id\<rbrakk>
  \<Longrightarrow> cap_ptr < 2 ^ si_cnode_size"
  by (clarsimp simp: si_cap_at_def sep_conj_exists)

lemma si_irq_cap_at_less_si_cnode_size:
  "\<lbrakk>\<guillemotleft>si_irq_cap_at opt_sel4_cap spec obj_id \<and>* R\<guillemotright> s;
    Some cap_ptr = opt_sel4_cap obj_id\<rbrakk>
  \<Longrightarrow> cap_ptr < 2 ^ si_cnode_size"
  by (clarsimp simp: si_irq_cap_at_def sep_conj_exists)

lemma si_cap_at_has_k_obj_id:
  "\<lbrakk>\<guillemotleft>si_cap_at t opt_sel4_cap spec dev obj_id \<and>* R\<guillemotright> s\<rbrakk>
  \<Longrightarrow> \<exists>cap_object_id. t obj_id = Some cap_object_id"
  by (clarsimp simp: si_cap_at_def sep_conj_exists)

(******************************************************
 * Using just si_cap_at when you have si_caps_at. *
 ******************************************************)

lemma valid_si_caps_at_si_cap_at:
  "\<lbrakk>finite obj_ids; obj_id \<in> obj_ids;
   (\<And>R. \<lbrace>\<guillemotleft>si_cap_at t orig_caps spec dev obj_id \<and>* P \<and>* R\<guillemotright>\<rbrace>
   f
   \<lbrace>\<lambda>_.\<guillemotleft>si_cap_at t orig_caps spec dev obj_id \<and>* Q \<and>* R\<guillemotright>\<rbrace>)\<rbrakk>
   \<Longrightarrow>
   \<lbrace>\<guillemotleft>si_caps_at t orig_caps spec dev obj_ids \<and>* P \<and>* R\<guillemotright>\<rbrace>
   f
   \<lbrace>\<lambda>_.\<guillemotleft>si_caps_at t orig_caps spec dev obj_ids \<and>* Q \<and>* R\<guillemotright>\<rbrace>"
  apply (clarsimp simp: si_caps_at_def)
  apply (drule sep_set_conj_map_singleton_wp [where f=f and
                   I="si_cap_at t orig_caps spec dev" and  P=P and Q=Q and R=R, rotated])
    apply (clarsimp simp: sep_conj_ac)+
  done

(*******************************************************
 * Frames have been duplicated. *
 *******************************************************)

abbreviation (input)
  "cap_object_from_slot obj_id slot P s \<equiv> \<exists>cap. opt_cap (obj_id, slot) s = Some cap
                                      \<and> cap \<noteq> NullCap
                                      \<and> P (cap_object cap) s"
abbreviation "get_obj obj_id slot spec \<equiv> (cap_object o the) (opt_cap (obj_id, slot) spec)"
abbreviation "ref_obj spec obj_id slot \<equiv> cap_ref_object (obj_id, slot) spec"
abbreviation "real_frame_cap_of dev ptr rights n t \<equiv> FrameCap dev ((the o t) ptr) rights n Real None"
abbreviation (input) "the_cap spec pt_id pt_slot \<equiv> the (opt_cap (pt_id, pt_slot) spec)"

definition conjure_real_frame_cap ::
  "cdl_cap \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow> cdl_cap"
  where
  "conjure_real_frame_cap cap t \<equiv>
    case cap of FrameCap _ ptr _ n _ _ \<Rightarrow> real_frame_cap_of False ptr vm_read_write n t | _ \<Rightarrow> cap"

definition frame_duplicates_empty ::
  "(cdl_object_id \<times> nat \<Rightarrow> word32) \<Rightarrow> cdl_object_id \<Rightarrow> cdl_state \<Rightarrow> (sep_state \<Rightarrow> bool)"
  where
  "frame_duplicates_empty cptr_map pd_id spec \<equiv>
   sep_map_set_conj
    (\<lambda>x. let pt_id = get_obj pd_id x spec in
         sep_map_set_conj (\<lambda>y. (si_cnode_id, unat $ cptr_map (pt_id, y)) \<mapsto>c NullCap)
         {slot \<in> dom (slots_of pt_id spec). cap_at ((\<noteq>) NullCap) (pt_id, slot) spec})
    {slot \<in> dom (slots_of pd_id spec). cap_at (\<lambda>cap. cap \<noteq> NullCap \<and> pt_at (cap_object cap) spec)
                                              (pd_id, slot) spec} \<and>*
   sep_map_set_conj
     (\<lambda>x. let frame_id = get_obj pd_id x spec in
          (si_cnode_id, unat $ cptr_map (pd_id, x)) \<mapsto>c NullCap)
     {slot \<in> dom (slots_of pd_id spec). cap_at (\<lambda>cap. cap \<noteq> NullCap \<and> frame_at (cap_object cap) spec)
                                               (pd_id, slot) spec}"

definition frame_duplicates_copied ::
  "(cdl_object_id \<times> nat \<Rightarrow> word32) \<Rightarrow> cdl_object_id \<Rightarrow> cdl_state
   \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow> (sep_state \<Rightarrow> bool)"
  where
  "frame_duplicates_copied cptr_map pd_id spec t \<equiv>
   sep_map_set_conj
    (\<lambda>x. let pt_id = get_obj pd_id x spec in
         sep_map_set_conj (\<lambda>y. (si_cnode_id, unat $ cptr_map (pt_id, y)) \<mapsto>c
                                 conjure_real_frame_cap (the_cap spec pt_id y) t)
         {slot \<in> dom (slots_of pt_id spec). cap_at ((\<noteq>) NullCap) (pt_id, slot) spec})
    {slot \<in> dom (slots_of pd_id spec). cap_at (\<lambda>cap. cap \<noteq> NullCap \<and> pt_at (cap_object cap) spec)
                                              (pd_id, slot) spec} \<and>*
   sep_map_set_conj
     (\<lambda>x. let frame_id = get_obj pd_id x spec in
          (si_cnode_id, unat $ cptr_map (pd_id, x)) \<mapsto>c
            conjure_real_frame_cap (the_cap spec pd_id x) t)
     {slot \<in> dom (slots_of pd_id spec). cap_at (\<lambda>cap. cap \<noteq> NullCap \<and> frame_at (cap_object cap) spec)
                                               (pd_id, slot) spec}"

(**********************************************************
 * The pre and post conditions of the system initialiser. *
 **********************************************************)

(* That the boot info is valid, and that there are enough free slots to initialise a system. *)
definition
  valid_boot_info
where
  "valid_boot_info bootinfo spec \<equiv> \<lambda>s.
  \<exists>untyped_caps fstart fend ustart uend obj_ids.
  ((\<And>*(cptr, cap) \<in> set (zip [ustart .e. uend - 1] untyped_caps). (si_cnode_id, unat cptr) \<mapsto>c cap)  \<and>*
   (\<And>* cptr \<in> set [fstart .e. fend - 1]. (si_cnode_id, unat cptr) \<mapsto>c NullCap) \<and>*
   (\<And>* obj_id\<in>(\<Union>cap\<in>set untyped_caps. cap_free_ids cap). obj_id \<mapsto>o Untyped) \<and>*
   (SETSEPCONJ pd_id | pd_at pd_id spec.
     frame_duplicates_empty (make_frame_cap_map obj_ids
                              (drop (card (dom (cdl_objects spec))) [fstart .e. fend - 1]) spec)
                            pd_id spec) \<and>*
   si_objects \<and>*
   si_irq_nodes spec) s \<and>
   obj_ids = sorted_list_of_set (dom (cdl_objects spec)) \<and>
   card (dom (cdl_objects spec)) +
   card {obj_id. cnode_or_tcb_at obj_id spec} +
   card (\<Union>(set ` get_frame_caps spec ` {obj. pd_at obj spec})) \<le> unat fend - unat fstart \<and>
   length untyped_caps = unat uend - unat ustart \<and>
   distinct_sets (map cap_free_ids untyped_caps) \<and>
   list_all is_full_untyped_cap untyped_caps \<and>
   list_all well_formed_untyped_cap untyped_caps \<and>
   list_all (\<lambda>c. \<not> is_device_cap c) untyped_caps \<and>
   bi_untypes bootinfo = (ustart, uend) \<and>
   bi_free_slots bootinfo = (fstart, fend) \<and>
   ustart < 2 ^ si_cnode_size \<and>
  (uend - 1) < 2 ^ si_cnode_size \<and>
   fstart < 2 ^ si_cnode_size \<and>
  (fend - 1) < 2 ^ si_cnode_size \<and>
   uend \<noteq> 0 \<and> fend \<noteq> 0"

definition
  si_final_objects :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow> sep_pred"
where
  "si_final_objects spec t \<equiv> \<lambda>s.
   \<exists>dup_caps (untyped_cptrs::32 word list) (free_cptrs::32 word list) untyped_caps all_available_ids.
    ((\<And>*  cptr \<in> set (take (card (dom (cdl_objects spec))) free_cptrs).
          (si_cnode_id, unat cptr) \<mapsto>c NullCap) \<and>*
     (\<And>*  cptr \<in> set (drop (card (dom (cdl_objects spec)) +
                             card ({obj_id. cnode_or_tcb_at obj_id spec})) free_cptrs).
          (si_cnode_id, unat cptr) \<mapsto>c NullCap) \<and>*
     (\<And>* (cptr, untyped_cap) \<in> set (zip untyped_cptrs untyped_caps).
          (si_cnode_id, unat cptr) \<mapsto>c untyped_cap) \<and>*
     (\<And>*  obj_id \<in> all_available_ids. obj_id \<mapsto>o Untyped) \<and>*
     (\<And>*  obj_id \<in> {obj_id. cnode_or_tcb_at obj_id spec}. (si_cap_at t dup_caps spec False obj_id)) \<and>*
      si_objects) s"

(********************************************************
 * Conversion of si_objs_caps_at to si_caps_at *
 ********************************************************)

lemma orig_cap_rewrite:
  "Set.filter (\<lambda>cap_ref. original_cap_at cap_ref spec \<and> cap_at cap_has_object cap_ref spec)
               (SIGMA obj_id:{obj_id. cnode_at obj_id spec}.
                      dom (slots_of obj_id spec)) =
   {cap_ref. original_cap_at cap_ref spec \<and> object_cap_ref cap_ref spec}"
  by (auto simp: object_cap_ref_def opt_cap_def object_at_def cap_at_def real_object_at_def
          split: option.splits)

lemma slots_tcb:
  "\<lbrakk>well_formed spec; opt_cap (obj_id, slot) spec = Some cap;
    cdl_objects spec obj_id = Some obj; obj = Tcb tcb\<rbrakk> \<Longrightarrow>
   slot = 0 \<or>
   slot = 1 \<or>
   slot = 2 \<or>
   slot = 3 \<or>
   slot = 4 \<or>
   slot = 5 \<or>
   slot = 8"
  apply (frule (1) well_formed_object_slots)
  apply (drule (1) well_formed_well_formed_tcb)
  apply (clarsimp simp: well_formed_tcb_def opt_cap_def slots_of_def)
  apply (drule (1) dom_eqD)
  apply (clarsimp simp: object_default_state_def2 dom_object_slots_default_tcb tcb_slot_defs)
  done

lemma object_at_dom_cdl_objects:
  "object_at P obj_id s \<Longrightarrow> obj_id \<in> dom (cdl_objects s)"
  by (clarsimp simp: object_at_def)

lemma foo:
  "\<lbrakk>well_formed spec; irq_node_at obj_id spec\<rbrakk>
  \<Longrightarrow> obj_id \<in> irq_nodes spec"
  by (metis irq_nodes_def mem_Collect_eq)

lemma well_formed_irqhandler_cap_in_cnode:
  "\<lbrakk>well_formed spec; opt_cap (obj_id, slot) spec = Some cap;
    is_irqhandler_cap cap; cdl_objects spec obj_id = Some obj\<rbrakk>
    \<Longrightarrow> is_cnode obj"
  apply (case_tac obj)
          apply (fastforce simp: opt_cap_def slots_of_def object_slots_def
                                 is_cnode_def object_at_def is_asidpool_def)+
        apply (frule (3) slots_tcb)
        apply (drule (1) well_formed_well_formed_tcb)
        apply (clarsimp simp: well_formed_tcb_def opt_cap_def slots_of_def)
        apply (erule allE [where x=slot])
        apply (simp add: tcb_slot_defs cap_type_def split: cdl_cap.splits)
       apply (fastforce simp: opt_cap_def slots_of_def object_slots_def
                              is_cnode_def object_at_def is_asidpool_def)
      apply (frule_tac obj_id=obj_id in well_formed_asidpool_at, simp add: object_at_def)
     apply (frule (1) well_formed_pt, simp add: object_at_def, simp+)
    apply (frule (1) well_formed_pd, simp add: object_at_def, simp+)
    apply (clarsimp simp: is_fake_pt_cap_def split: cdl_cap.splits)
   apply (fastforce simp: opt_cap_def slots_of_def object_slots_def
                         is_cnode_def object_at_def is_asidpool_def)+
   apply (frule (1) well_formed_well_formed_irq_node)
   apply (fastforce simp: well_formed_irq_node_def opt_cap_def slots_of_def
                          object_at_def irq_nodes_def is_irq_node_def)
  done

lemma well_formed_irqhandler_cap_in_cnode_at:
  "\<lbrakk>well_formed spec; opt_cap (obj_id, slot) spec = Some cap; is_irqhandler_cap cap\<rbrakk>
  \<Longrightarrow> cnode_at obj_id spec"
  apply (frule opt_cap_cdl_objects, clarsimp)
  apply (drule (3) well_formed_irqhandler_cap_in_cnode)
  apply (clarsimp simp: object_at_def)
  done

lemma irqhandler_cap_rewrite:
   "well_formed spec \<Longrightarrow>
    Set.filter (\<lambda>irq. irqhandler_cap_at irq spec)
                (SIGMA obj_id:{obj_id. cnode_at obj_id spec}.
                       dom (slots_of obj_id spec)) =
    {cap_ref. irqhandler_cap_at cap_ref spec}"
   apply (clarsimp simp: object_cap_ref_def object_at_def cap_at_def
          split: option.splits)
   apply rule
    apply clarsimp
   apply clarsimp
   apply (frule opt_cap_dom_cdl_objects)
   apply (frule opt_cap_dom_slots_of, clarsimp)
   apply (frule (3) well_formed_irqhandler_cap_in_cnode)
   apply (frule (1) well_formed_well_formed_irq_node)
   apply (clarsimp simp: well_formed_irq_node_def object_at_def
                         opt_cap_def slots_of_def dom_def)
   done

lemma well_formed_object_cap_real:
  "well_formed spec
  \<Longrightarrow> object_cap_ref cap_ref spec =
     (cap_at_to_real_object cap_ref spec \<and>
      cnode_at (fst cap_ref) spec)"
  apply (clarsimp simp: cap_at_def cap_at_to_real_object_def object_cap_ref_def)
  apply (rule iffI)
   apply clarsimp
   apply (drule (1) well_formed_well_formed_cap_to_real_object', simp)
   apply (clarsimp simp: well_formed_cap_to_real_object_def real_object_at_def)
  apply (clarsimp simp: real_object_at_def opt_cap_dom_cdl_objects)
  done

(* This lemma converts between the two represenatations of the fact that the
 * root task has orig caps to each of the objects.
 *
 * This can be specified either:
 * - on the objects themselves.
 * - on the cap slots of CNodes that have a orig cap in them.
 *
 * This relies on the bijection between orig capabilities and objects in the spec.
 *)

lemma si_caps_at_conversion:
  "\<lbrakk>well_formed spec;
    real_ids = {obj_id. real_object_at obj_id spec};
    cnode_ids = {obj_id. cnode_at obj_id spec}\<rbrakk>
  \<Longrightarrow> si_objs_caps_at t si_caps spec dev cnode_ids =
      si_caps_at t si_caps spec dev real_ids"
  apply (clarsimp simp: si_objs_caps_at_def si_obj_caps_at_def [abs_def]
                        si_obj_cap_at_def [abs_def] si_caps_at_def)
  apply (subst sep.prod.Sigma, clarsimp+)
  apply (clarsimp simp: split_def)
  apply (subst sep_map_set_conj_restrict_predicate)
   apply (rule finite_SigmaI, clarsimp+)
  apply (subst orig_cap_rewrite)
  apply (frule well_formed_bij)
  apply (clarsimp simp: bij_betw_def)
  apply (rule sep_map_set_conj_reindex_cong [where f="\<lambda>cap_ref. cap_ref_object cap_ref spec", symmetric])
    apply (subst well_formed_object_cap_real, simp+)
   apply (simp add: real_objects_def real_object_at_def)
   apply (subst well_formed_object_cap_real, simp+)
  apply (clarsimp simp: cap_ref_object_def object_cap_ref_def si_obj_cap_at'_def)
  done


lemma si_null_caps_at_conversion:
  "\<lbrakk>well_formed spec;
    real_ids = {obj_id. real_object_at obj_id spec};
    cnode_ids = {obj_id. cnode_at obj_id spec}\<rbrakk>
  \<Longrightarrow> si_spec_objs_null_caps_at t si_caps spec cnode_ids =
      si_null_caps_at t si_caps spec real_ids"
  apply (clarsimp simp: si_spec_objs_null_caps_at_def si_spec_obj_null_caps_at_def [abs_def]
                        si_spec_obj_null_cap_at_def [abs_def] si_null_caps_at_def)
  apply (subst sep.prod.Sigma, clarsimp+)
  apply (clarsimp simp: split_def)
  apply (subst sep_map_set_conj_restrict_predicate)
   apply (rule finite_SigmaI, clarsimp+)
  apply (subst orig_cap_rewrite)
  apply (frule well_formed_bij)
  apply (clarsimp simp: bij_betw_def)
  apply (rule sep_map_set_conj_reindex_cong [where f="\<lambda>cap_ref. cap_ref_object cap_ref spec"
    and h="(si_null_cap_at t si_caps spec)"
    and B="{obj_id. real_object_at obj_id spec}", symmetric])
    apply (subst well_formed_object_cap_real, simp+)
   apply (simp add: real_objects_def real_object_at_def)
   apply (subst well_formed_object_cap_real, simp+)
  apply (clarsimp simp: cap_ref_object_def object_cap_ref_def si_spec_obj_null_cap_at'_def)
  done

lemma si_null_caps_at_reindex:
  "\<lbrakk>distinct (obj_ids::32 word list); distinct (free_cptrs);
     orig_caps = map_of (zip obj_ids free_cptrs);
     length obj_ids \<le> length free_cptrs\<rbrakk>
  \<Longrightarrow> (\<And>* obj_id\<in>set obj_ids.
       (\<lambda>s. \<exists>cap_ptr. ((si_cnode_id, unat cap_ptr) \<mapsto>c NullCap) s \<and>
                       orig_caps obj_id = Some cap_ptr))
   = (\<And>* cptr\<in>set (take (length obj_ids) free_cptrs).
                   (si_cnode_id, unat cptr) \<mapsto>c NullCap)"
  apply (rule sep_map_set_conj_reindex_cong [symmetric, where
      f="\<lambda>obj_id. the (orig_caps obj_id)"
      and h="\<lambda>cptr. (si_cnode_id, unat cptr) \<mapsto>c NullCap"
      and B="set (take (length obj_ids) free_cptrs)"])
    apply clarsimp
    apply (erule (2) map_of_zip_inj')
   apply clarsimp
   apply (subst zip_take_length[symmetric])
   apply (subst map_of_zip_range)
     apply (clarsimp simp: min_def)
    apply assumption
   apply simp
  apply clarsimp
  apply (rule ext)
  apply rule
   apply clarsimp
  apply (rule_tac x="the (map_of (zip obj_ids free_cptrs) a)" in exI)
  apply clarsimp
  apply (frule_tac x=a in map_of_zip_is_Some', clarsimp)
  done

lemma si_null_caps_at_simplified_helper:
  "\<lbrakk>(si_null_caps_at t orig_caps spec obj_ids) s\<rbrakk> \<Longrightarrow>
     (\<And>* obj_id \<in> obj_ids. (\<lambda>s. \<exists>cap_ptr. ((si_cnode_id, unat cap_ptr) \<mapsto>c NullCap) s \<and>
                                   orig_caps obj_id = Some cap_ptr)) s"
  apply (clarsimp simp: si_null_caps_at_def si_null_cap_at_def [abs_def])
  apply (erule sep_map_set_conj_impl)
   apply blast
  apply clarsimp
  done

lemma si_null_caps_at_simplified:
  "\<lbrakk>(si_spec_objs_null_caps_at t si_caps spec cnode_ids) s;
    well_formed spec;
    cnode_ids = {obj_id. cnode_at obj_id spec};
    real_ids = {obj_id. real_object_at obj_id spec};
    real_ids = set obj_ids;
    distinct obj_ids; distinct free_cptrs;
    si_caps = map_of (zip obj_ids free_cptrs);
    length obj_ids \<le> length free_cptrs\<rbrakk> \<Longrightarrow>
   (\<And>* cptr \<in> set (take (length obj_ids) free_cptrs). ((si_cnode_id, unat cptr) \<mapsto>c NullCap)) s"
  apply (subst (asm) si_null_caps_at_conversion, assumption+)
  apply (drule si_null_caps_at_simplified_helper)
  apply (subst si_null_caps_at_reindex [symmetric], simp+)
  done

lemma map_of_zip_range':
  "\<lbrakk>length xs = length ys; distinct xs; set xs = X\<rbrakk>
  \<Longrightarrow> (\<lambda>x. (the (map_of (zip xs ys) x))) ` X = set ys"
  by (metis map_of_zip_range)




lemma si_irq_caps_at_conversion:
  "\<lbrakk>well_formed spec;
    cnode_ids = {obj_id. cnode_at obj_id spec};
    irqs = used_irqs spec\<rbrakk>
  \<Longrightarrow> si_spec_irqs_caps_at irq_caps spec cnode_ids =
      si_irq_caps_at irq_caps spec irqs"
  apply (clarsimp simp: si_spec_irqs_caps_at_def si_irq_caps_at_def
                        si_spec_irq_caps_at_def [abs_def]
                        si_spec_irq_cap_at_def [abs_def])
  apply (subst sep.prod.Sigma, clarsimp+)
  apply (clarsimp simp: split_def)
  apply (subst sep_map_set_conj_restrict_predicate)
   apply (rule finite_SigmaI, clarsimp+)
  apply (subst irqhandler_cap_rewrite, assumption)
  apply (frule well_formed_irqhandler_bij)
  apply (clarsimp simp: bij_betw_def)
  apply (rule sep_map_set_conj_reindex_cong [where f="\<lambda>cap_ref. cap_ref_irq cap_ref spec", symmetric], simp+)
  apply (clarsimp simp: si_spec_irq_cap_at'_def cap_ref_irq_def cap_at_def)
  done

definition si_null_irq_caps_at :: "(cdl_irq \<Rightarrow> cdl_cptr option) \<Rightarrow> cdl_state \<Rightarrow>
                                      cdl_irq set \<Rightarrow> sep_pred"
where
  "si_null_irq_caps_at si_irq_caps spec irqs \<equiv>
  \<And>* irq \<in> irqs. si_null_irq_cap_at si_irq_caps spec irq"

lemma si_null_irq_caps_at_simplified_helper:
  "\<lbrakk>(si_null_irq_caps_at si_irq_caps spec irqs) s\<rbrakk> \<Longrightarrow>
     (\<And>* irq \<in> irqs. (\<lambda>s. \<exists>cap_ptr. ((si_cnode_id, unat cap_ptr) \<mapsto>c NullCap) s \<and>
                                   si_irq_caps irq = Some cap_ptr)) s"
  apply (clarsimp simp: si_null_irq_caps_at_def si_null_irq_cap_at_def)
  apply (erule sep_map_set_conj_impl)
   apply blast
  apply clarsimp
  done

lemma map_of_zip_inj2:
  "\<lbrakk>distinct xs; distinct ys; length xs \<le> length ys; set xs = X\<rbrakk>
  \<Longrightarrow> inj_on (\<lambda>x. the (map_of (zip xs ys) x)) X"
  by (metis map_of_zip_inj')

lemma opt_cap_has_slots:
  "\<lbrakk>opt_cap (obj_id, slot) spec = Some cap\<rbrakk>
  \<Longrightarrow> object_at has_slots obj_id spec"
  by (auto simp: object_at_def has_slots_def opt_cap_def slots_of_def object_slots_def
          split: option.splits cdl_object.splits)

lemma well_formed_non_ntfn_in_real_object:
  "\<lbrakk>well_formed spec; opt_cap (obj_id, slot) spec = Some cap; \<not>is_ntfn_cap cap; cap \<noteq> NullCap\<rbrakk>
  \<Longrightarrow> real_object_at obj_id spec"
  apply (frule opt_cap_cdl_objects, clarsimp)
  apply (frule (1) well_formed_well_formed_irq_node)
  apply (clarsimp simp: well_formed_irq_node_def real_object_at_def
                         opt_cap_def slots_of_def opt_cap_dom_cdl_objects)
  done


lemma irqhandler_cap_at_simp:
  "well_formed spec \<Longrightarrow>
   {(obj_id, slot). cnode_at obj_id spec \<and> irqhandler_cap_at (obj_id, slot) spec} =
   {(obj_id, slot). irqhandler_cap_at (obj_id, slot) spec}"
  apply (safe)
  apply (clarsimp simp: cap_at_def)
  apply (frule (2) well_formed_irqhandler_cap_in_cnode_at)
  apply (frule (1) well_formed_non_ntfn_in_real_object, simp+)
  done

lemma orig_cap_rewrite_v2:
  "(SIGMA obj_id:{obj_id. cnode_at obj_id spec}. dom (slots_of obj_id spec)) =
   {(obj_id, slot). cnode_at obj_id spec \<and> slots_of obj_id spec slot \<noteq> None}"
  by auto

lemma rewrite_irqhandler_cap_at:
  "well_formed spec \<Longrightarrow>
  Set.filter (\<lambda>cap_ref. irqhandler_cap_at cap_ref spec)
             (SIGMA obj_id:{obj_id. cnode_at obj_id spec}. dom (slots_of obj_id spec)) =
  {(obj_id, slot). irqhandler_cap_at (obj_id, slot) spec}"
  apply (subst irqhandler_cap_at_simp [symmetric])
  by (auto simp: opt_cap_def cap_at_def)

lemma well_formed_used_irqs_rewrite:
  "well_formed spec \<Longrightarrow>
   (\<lambda>cap_ref. cap_ref_irq cap_ref spec) ` {(obj_id, slot). irqhandler_cap_at (obj_id, slot) spec} =
   used_irqs spec"
  apply (drule well_formed_irqhandler_bij)
  apply (auto simp: bij_betw_def)
  done


lemma si_irq_null_caps_at_simplified:
  "\<lbrakk>(si_spec_irqs_null_caps_at irq_caps spec {obj_id. cnode_at obj_id spec}) s;
    well_formed spec;
    distinct irqs; distinct free_cptrs;
    set irqs = used_irqs spec;
    irq_caps = map_of (zip irqs free_cptrs);
    length irqs \<le> length free_cptrs\<rbrakk> \<Longrightarrow>
   (\<And>* cptr \<in> set (take (length irqs) free_cptrs). ((si_cnode_id, unat cptr) \<mapsto>c NullCap)) s"
  apply (clarsimp simp: si_spec_irqs_null_caps_at_def si_spec_irq_null_caps_at_def
                        si_spec_irq_null_cap_at_def si_spec_irqs_caps_at_def)
  apply (subst (asm) sep.prod.Sigma, clarsimp+)
  apply (clarsimp simp: split_def)
  apply (subst (asm) sep_map_set_conj_restrict_predicate, rule finite_SigmaI, clarsimp+)
  apply (subst (asm) rewrite_irqhandler_cap_at, simp)
  apply (subst (asm) sep_map_set_conj_reindex_cong [where
                    f = "\<lambda>cap_ref. cap_ref_irq cap_ref spec"
                and h = "si_null_irq_cap_at (map_of (zip irqs free_cptrs)) spec", symmetric])
     apply (drule well_formed_irqhandler_bij)
     apply (clarsimp simp: bij_betw_def cond_case_prod_eta)
    apply simp
   apply (clarsimp simp: si_spec_irq_null_cap_at'_def cap_at_def cap_ref_irq_def)
  apply clarsimp
  apply (drule si_null_irq_caps_at_simplified_helper [simplified si_null_irq_caps_at_def])
  apply (subst (asm) sep_map_set_conj_reindex_cong [symmetric, where
                    f = "\<lambda>irq. the ( map_of (zip irqs free_cptrs) irq)"
                and h = "\<lambda>cptr. (si_cnode_id, unat cptr) \<mapsto>c NullCap"
                and B = "set (take (length irqs) free_cptrs)"])
     apply (subst well_formed_used_irqs_rewrite, assumption)
     apply (metis map_of_zip_inj')
    apply (subst well_formed_used_irqs_rewrite, assumption)
    apply (subst zip_take_length[symmetric], subst map_of_zip_range', simp+)
   apply (rule ext)
   apply rule
    apply clarsimp
   apply (rule_tac x="the (map_of (zip irqs free_cptrs) a)" in exI)
   apply clarsimp
   apply (frule_tac x1="(cap_irq (the (opt_cap (aa, b) spec)))" in map_of_zip_is_Some'[THEN iffD1], clarsimp)
    apply (fastforce simp: cap_at_def used_irqs_def all_caps_def)
   apply (clarsimp simp: cap_ref_irq_def)
  apply simp
  done

end
