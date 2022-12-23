(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory InitIRQ_SI
imports
  "DSpecProofs.IRQ_DP"
  ObjectInitialised_SI
  RootTask_SI
  SysInit_SI
begin

lemma seL4_IRQHandler_SetEndpoint_irq_initialised_helper_sep:
  "\<lbrace>\<guillemotleft>irq_empty spec t irq \<and>*
     si_cap_at t orig_caps spec dev ntfn_id \<and>*
     si_irq_cap_at irq_caps spec irq \<and>*
     si_objects \<and>* R\<guillemotright> and
   K(well_formed spec \<and>
     cdl_objects spec ntfn_id = Some ntfn \<and>
     is_ntfn ntfn \<and>
     irq \<in> bound_irqs spec \<and>

     opt_cap (cdl_irq_node spec irq, 0) spec = Some ntfn_cap \<and>
     ntfn_id = cap_object ntfn_cap \<and>

     t (cdl_irq_node spec irq) = Some kernel_irq_id \<and>
     t ntfn_id = Some kernel_ntfn_id \<and>
     cdl_objects spec (cdl_irq_node spec irq) = Some spec_irq \<and>

     irq_caps irq = Some irq_handler_cptr \<and>
     orig_caps ntfn_id = Some endpoint_cptr \<and>
     irq_handler_cptr < 2 ^ si_cnode_size \<and>
     endpoint_cptr < 2 ^ si_cnode_size)\<rbrace>
     seL4_IRQHandler_SetEndpoint irq_handler_cptr endpoint_cptr
   \<lbrace>\<lambda>_.
    \<guillemotleft>irq_initialised spec t irq \<and>*
     si_cap_at t orig_caps spec dev ntfn_id \<and>*
     si_irq_cap_at irq_caps spec irq \<and>*
     si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_gen_asm, clarsimp)
  apply (frule well_formed_bound_irqs_are_used_irqs)
  apply (subst irq_initialised_decomp_total, assumption+, fast)
  apply (subst irq_empty_decomp_total, assumption+, fast)
  apply (clarsimp simp: irq_slot_initialised_def irq_slot_empty_def irq_initialised_general_def
                        si_cap_at_def si_irq_cap_at_def si_objects_def
                        sep_conj_assoc sep_conj_exists)
  apply (frule (1) well_formed_irq_is_irq_node)
  apply (frule (1) well_formed_size_irq_node)
  apply (frule (2) well_formed_irq_ntfn_cap)
  apply (rule hoare_chain)
    apply (rule seL4_IRQHandler_SetEndpoint_wp [where
              root_tcb = root_tcb
           and cnode_cap = si_cspace_cap
           and cnode_id = si_cnode_id
           and root_size = si_cnode_size
           and irq = irq
           and irq_handler_slot = "unat (the (irq_caps irq))"
           and endpoint_slot    = "unat (the (orig_caps (cap_object ntfn_cap)))"
           and irq_id = "the (t (cdl_irq_node spec irq))"
           and old_cap = NullCap
           and endpoint_cap = "NotificationCap (the (t (cap_object ntfn_cap))) 0 {AllowRead, AllowWrite}"
           and R="object_empty_slots_initialised spec t (cdl_irq_node spec irq) \<and>*
                  object_fields_empty spec t     (cdl_irq_node spec irq) \<and>*
                 (si_cnode_id, unat seL4_CapInitThreadCNode) \<mapsto>c si_cnode_cap \<and>*
                 (si_cnode_id, unat seL4_CapIRQControl) \<mapsto>c IrqControlCap \<and>*
                  si_asid \<and>*  R"])
   apply (intro pred_conjI)
    apply (clarsimp simp: object_type_is_object default_cap_def)
    apply (sep_drule sep_map_c_sep_map_s [where cap=NullCap])
     apply (rule object_slots_object_default_state_NullCap', (simp add: object_type_has_slots)+)
    apply sep_solve
   apply simp
   apply (frule guard_equal_si_cspace_cap' [where src_index=irq_handler_cptr])
   apply (frule guard_equal_si_cspace_cap' [where src_index=endpoint_cptr])
   apply (clarsimp simp: ep_related_cap_def offset_slot')
  apply simp
  apply (clarsimp simp: object_type_is_object default_cap_def)
  apply (subst (asm) irq_node_fields_empty_initialised)
   apply (simp add: object_type_object_at)
  apply (simp add: object_fields_initialised_def object_initialised_general_def)
  apply (sep_drule sep_map_s_sep_map_c [where obj_id = kernel_irq_id
         and cap = "NotificationCap kernel_ntfn_id 0 {AllowRead, AllowWrite}"
         and obj = "spec2s t spec_irq"])
   apply simp
   apply (frule (1) object_slots_opt_capI)
   apply (subst object_slots_spec2s,
         (fastforce simp: object_type_has_slots cap_has_object_def
                          update_cap_object_def cap_type_def
                   split: cdl_cap.splits)+)
  apply sep_solve
  done

lemma seL4_IRQHandler_SetEndpoint_irq_initialised_sep:
  "\<lbrace>\<guillemotleft>irq_empty spec t irq \<and>*
     si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} \<and>*
     si_irq_caps_at irq_caps spec (bound_irqs spec) \<and>*
     si_objects \<and>* R\<guillemotright> and
   K(well_formed spec \<and>
     irq \<in> bound_irqs spec \<and>
     irq_caps irq = Some irq_handler_cptr \<and>
     orig_caps (cap_object (the (opt_cap (cdl_irq_node spec irq, 0) spec))) = Some endpoint_cptr)\<rbrace>
     seL4_IRQHandler_SetEndpoint irq_handler_cptr endpoint_cptr
   \<lbrace>\<lambda>_.
    \<guillemotleft>irq_initialised spec t irq \<and>*
     si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} \<and>*
     si_irq_caps_at irq_caps spec (bound_irqs spec) \<and>*
     si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (clarsimp simp: si_irq_caps_at_def)
  apply (frule well_formed_bound_irqs_are_used_irqs)
  apply (frule (1) well_formed_cap_object_cdl_irq_node, clarsimp)
  apply (frule object_at_real_object_at [where obj_id = "cap_object (the (opt_cap (cdl_irq_node spec irq, 0) spec))"],
         fastforce simp: object_at_def)
  apply (frule well_formed_slot_0_of_used_irq_node, fast, clarsimp)
  apply (frule slots_of_cdl_objects, clarsimp)
  apply (rule hoare_chain [OF sep_set_conj_map_singleton_wp
         [where P = "irq_empty spec t irq \<and>*
                     si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} \<and>*
                     si_objects"
            and Q = "irq_initialised spec t irq \<and>*
                     si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} \<and>*
                     si_objects"
            and I = "si_irq_cap_at irq_caps spec"
            and x = irq
            and xs = "bound_irqs spec"]], simp+)
    apply (clarsimp simp: si_irq_caps_at_def si_caps_at_def)
    apply (rule hoare_chain [OF sep_set_conj_map_singleton_wp
           [where P = "irq_empty spec t irq \<and>*
                       si_irq_cap_at irq_caps spec irq \<and>*
                       si_objects"
              and Q = "irq_initialised spec t irq \<and>*
                       si_irq_cap_at irq_caps spec irq \<and>*
                       si_objects"
              and I = "si_cap_at t orig_caps spec dev"
              and x = "cap_object (the (opt_cap (cdl_irq_node spec irq, 0) spec))"
              and xs = "{obj_id. real_object_at obj_id spec}"]], simp+)
       apply (wp sep_wp: seL4_IRQHandler_SetEndpoint_irq_initialised_helper_sep [where t=t and spec=spec and irq=irq
                and ntfn_cap = "the (opt_cap (cdl_irq_node spec irq, 0) spec)"
                and kernel_irq_id = "the (t (cdl_irq_node spec irq))"
                and kernel_ntfn_id = "the (t (cap_object (the (opt_cap (cdl_irq_node spec irq, 0) spec))))"], simp)
      apply (rule conjI)
       apply sep_solve
      apply (fastforce simp: opt_cap_def irq_empty_def irq_initialised_general_def
                             si_irq_cap_at_def si_cap_at_def sep_conj_exists)
     apply sep_solve
    apply sep_solve
   apply sep_solve
  apply sep_solve
  done

lemma init_irq_sep:
  "\<lbrace>\<guillemotleft>irq_empty spec t irq \<and>*
     si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} \<and>*
     si_irq_caps_at irq_caps spec (bound_irqs spec) \<and>*
     si_objects \<and>* R\<guillemotright> and
   K(well_formed spec \<and>
     irq \<in> bound_irqs spec)\<rbrace>
   init_irq spec orig_caps irq_caps irq
   \<lbrace>\<lambda>_. \<guillemotleft>irq_initialised spec t irq \<and>*
         si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} \<and>*
         si_irq_caps_at irq_caps spec (bound_irqs spec) \<and>*
         si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_gen_asm, clarsimp)
  apply (clarsimp simp: init_irq_def)
  apply (wp hoare_drop_imp seL4_IRQHandler_SetEndpoint_irq_initialised_sep | simp)+
  apply (frule (1) well_formed_cap_object_cdl_irq_node)
  apply (frule object_at_real_object_at [where obj_id = "cap_object (the (opt_cap (cdl_irq_node spec irq, 0) spec))"],
         fastforce simp: object_at_def)
  apply (clarsimp simp: si_caps_at_def get_irq_slot_def)
  apply (subst (asm) sep.prod.remove [where x="cap_object (the (opt_cap (cdl_irq_node spec irq, 0) spec))"], simp)
   apply clarsimp
  apply (clarsimp simp: si_cap_at_def sep_conj_exists)
  done

lemma init_irqs_bound_irqs_sep:
  "\<lbrace>\<guillemotleft>irqs_empty spec t (bound_irqs spec) \<and>*
     si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} \<and>*
     si_irq_caps_at irq_caps spec (bound_irqs spec) \<and>*
     si_objects \<and>* R\<guillemotright> and
   K(well_formed spec)\<rbrace>
   init_irqs spec orig_caps irq_caps
   \<lbrace>\<lambda>_.\<guillemotleft>irqs_initialised spec t (bound_irqs spec) \<and>*
        si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} \<and>*
        si_irq_caps_at irq_caps spec (bound_irqs spec) \<and>*
        si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (clarsimp simp: init_irqs_def)
  apply (clarsimp simp: irqs_empty_def irqs_initialised_def)
  apply (rule mapM_x_set_sep' [where
              P="irq_empty spec t" and
              Q="irq_initialised spec t" and
              I="si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} \<and>*
                 si_irq_caps_at irq_caps spec (bound_irqs spec) \<and>*
                 si_objects" and
              R=R, simplified sep_conj_assoc], fastforce+)
  apply (wp init_irq_sep, simp+)
  done

lemma irq_slot_empty_initialised_NullCap:
  "\<lbrakk>well_formed spec; slots_of (cdl_irq_node spec irq) spec slot = Some NullCap\<rbrakk>
  \<Longrightarrow> irq_slot_empty spec t irq slot = irq_slot_initialised spec t irq slot"
  apply (frule slots_of_cdl_objects, clarsimp)
  apply (frule (1) well_formed_irq_is_irq_node)
  apply (frule (1) well_formed_object_slots)
  apply (rule ext)
  apply (clarsimp simp: irq_slot_empty_def irq_slot_initialised_def irq_initialised_general_def slots_of_def
                 split: option.splits)
  apply (subgoal_tac "object_slots (object_default_state obj) slot = object_slots (spec2s t obj) slot")
   apply (subst sep_map_s_object_slots_equal, assumption, simp)
   apply clarsimp
  apply (frule object_slots_spec2s_NullCap [where t=t], simp)
  apply (erule object_slots_object_default_state_NullCap
          [where obj_id = "cdl_irq_node spec irq" and cap = NullCap])
    apply (clarsimp simp: object_at_def object_type_is_object)
   apply (clarsimp simp: opt_cap_def slots_of_def)
  apply simp
  done

lemma irq_slot_empty_initialised:
  "\<lbrakk>well_formed spec; irq \<notin> bound_irqs spec; irq \<in> used_irqs spec;
    cdl_objects spec (cdl_irq_node spec irq) = Some irq_node\<rbrakk>
   \<Longrightarrow> irq_slot_empty spec t irq 0 = irq_slot_initialised spec t irq 0"
  apply (frule (1) well_formed_slots_of_used_irq_node)
  apply (erule irq_slot_empty_initialised_NullCap)
  apply (clarsimp simp: bound_irqs_def)
  apply blast
  done



lemma irq_empty_initialised:
  "\<lbrakk>well_formed spec; irq \<notin> bound_irqs spec; irq \<in> used_irqs spec\<rbrakk>
  \<Longrightarrow> irq_empty spec t irq = irq_initialised spec t irq"
  apply (frule (1) well_formed_used_irqs_have_irq_node, clarsimp)
  apply (frule (1) well_formed_irq_is_irq_node)
  apply (subst irq_empty_decomp_total, assumption+)
  apply (subst irq_initialised_decomp_total, assumption+)
  apply (subst irq_node_fields_empty_initialised)
   apply (simp add: object_type_object_at object_at_def)
  apply (subst irq_slot_empty_initialised, assumption+)
  apply simp
  done

(* If all the bound IRQs are done, then all the used ones are too.
   To show this is true we note that:
    - by well_formed_bound_irqs_are_used_irqs:
        well_formed spec \<Longrightarrow> bound_irqs spec \<subseteq> used_irqs spec
    - empty (used and not bound) IRQs don't need any setting up
    - there's no problem having si_irq_caps_at to more IRQ caps.
*)
lemma init_irqs_sep:
  "\<lbrace>\<guillemotleft>irqs_empty spec t (used_irqs spec) \<and>*
     si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} \<and>*
     si_irq_caps_at irq_caps spec (used_irqs spec) \<and>*
     si_objects \<and>* R\<guillemotright> and
   K(well_formed spec)\<rbrace>
   init_irqs spec orig_caps irq_caps
   \<lbrace>\<lambda>_.\<guillemotleft>irqs_initialised spec t (used_irqs spec) \<and>*
        si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} \<and>*
        si_irq_caps_at irq_caps spec (used_irqs spec) \<and>*
        si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (clarsimp simp: si_irq_caps_at_def irqs_initialised_def irqs_empty_def)
  apply (frule well_formed_bound_irqs_are_used_irqs)
  apply (frule sep_set_conj_subset_wp
         [where P = "sep_map_set_conj (irq_empty spec t) (used_irqs spec) \<and>*
                     si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} \<and>* si_objects"
            and Q = "sep_map_set_conj (irq_initialised spec t) (used_irqs spec) \<and>*
                     si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} \<and>* si_objects"
            and f = "init_irqs spec orig_caps irq_caps"], simp+)
   apply (subst sep.prod.subset_diff, assumption, simp)+
   apply (rule hoare_pre, sep_wp init_irqs_bound_irqs_sep [where t=t])
   apply (simp add: si_irq_caps_at_def irqs_initialised_def irqs_empty_def sep_conj_assoc)
   apply(subgoal_tac "sep_map_set_conj (irq_empty spec t) (used_irqs spec - bound_irqs spec)
                    = sep_map_set_conj (irq_initialised spec t) (used_irqs spec - bound_irqs spec)", simp)
    apply sep_solve
   apply (rule sep.prod.cong, simp)
   apply (subst irq_empty_initialised, simp+)
  apply (erule hoare_chain, sep_solve, sep_solve)
  done

end
