(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory StartThreads_SI
imports
  InitTCB_SI
begin

lemma is_waiting_thread_is_tcb [simp]:
  "\<lbrakk>cdl_objects spec obj_id = Some obj; is_waiting_thread obj\<rbrakk>
  \<Longrightarrow> is_tcb obj"
  by (clarsimp simp: is_waiting_thread_def)

lemma is_waiting_thread_at_tcb_at [simp]:
  "is_waiting_thread_at obj_id spec \<Longrightarrow> tcb_at obj_id spec"
  by (clarsimp simp: object_at_def is_waiting_thread_def)

lemma is_waiting_thread_at_real_object_at [simp]:
  "\<lbrakk>well_formed spec; is_waiting_thread_at obj_id spec\<rbrakk> \<Longrightarrow> real_object_at obj_id spec"
  by (metis is_waiting_thread_at_tcb_at real_object_not_irq_node(2))

lemma is_waiting_thread_tcb_at [simp]:
  "(tcb_at obj_id spec \<and> object_at is_waiting_thread obj_id spec) = object_at is_waiting_thread obj_id spec"
  by fastforce

lemma is_waiting_thread_opt_cap_tcb_pending_op_slot [simp]:
  "\<lbrakk>cdl_objects spec obj_id = Some obj; is_waiting_thread obj\<rbrakk>
  \<Longrightarrow> opt_cap (obj_id, tcb_pending_op_slot) spec = Some RestartCap"
  by (clarsimp simp: is_waiting_thread_def opt_cap_def slots_of_def)


lemma is_waiting_thread_opt_cap_tcb_replycap_slot [simp]:
  "\<lbrakk>well_formed spec; cdl_objects spec obj_id = Some obj; is_waiting_thread obj\<rbrakk>
  \<Longrightarrow> opt_cap (obj_id, tcb_replycap_slot) spec = Some (MasterReplyCap obj_id)"
  apply (frule well_formed_tcb_pending_op_replycap [where obj_id=obj_id], simp add: object_at_def)
  apply (clarsimp simp: is_waiting_thread_def opt_cap_def slots_of_def)
  done

lemma is_waiting_thread_opt_cap_tcb_boundntfn_slot[simp]:
  "\<lbrakk>well_formed spec; cdl_objects spec obj_id = Some obj; is_waiting_thread obj\<rbrakk>
  \<Longrightarrow> opt_cap (obj_id, tcb_boundntfn_slot) spec = Some NullCap"
  apply (clarsimp simp: is_waiting_thread_def opt_cap_def slots_of_def)
  apply (frule well_formed_tcb_boundntfn_cap [where obj_id=obj_id], simp add: object_at_def)
  by (clarsimp simp: is_waiting_thread_def opt_cap_def slots_of_def)

lemma cap_transform_RestartCap [simp]:
  "cap_transform t RestartCap = RestartCap"
  by (clarsimp simp: cap_transform_def cap_type_def update_cap_object_def)

lemma cap_type_MasterReplyCap [simp]:
  "cap_type (MasterReplyCap obj_id) = None"
  by (simp add: cap_type_def)

lemma cap_transform_MasterReplyCap:
  "\<lbrakk>t obj_id = Some k_obj_id\<rbrakk>
  \<Longrightarrow> cap_transform t (MasterReplyCap obj_id) = MasterReplyCap k_obj_id"
  apply (frule cap_transform_update_cap_object [where cap="MasterReplyCap obj_id"], simp+)
  apply (clarsimp simp: cap_transform_def cap_object_def update_cap_object_def)
  done



lemma start_thread_sep:
  "\<lbrace>\<guillemotleft>tcb_half_initialised spec t obj_id \<and>*
     si_cap_at t dup_caps spec False obj_id \<and>*
     si_objects \<and>* R\<guillemotright> and
   K(well_formed spec \<and> obj_id \<in> {obj_id. is_waiting_thread_at obj_id spec})\<rbrace>
   start_thread spec dup_caps obj_id
   \<lbrace>\<lambda>_.\<guillemotleft>object_initialised spec t obj_id \<and>*
        si_cap_at t dup_caps spec False obj_id \<and>*
        si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (clarsimp simp: start_thread_def object_initialised_def tcb_half_initialised_def object_initialised_general_def
                        si_cap_at_def si_objects_def sep_conj_exists)
  apply (rule hoare_vcg_ex_lift | rule hoare_grab_asm | simp)+
  apply (subst tcb_half_decomp, (simp add: object_at_def)+)+
  apply (subst tcb_decomp, (simp add: object_at_def)+)+
  apply (wp add: hoare_drop_imps
         sep_wp: seL4_TCB_Resume_wp
         [where root_tcb = root_tcb
            and cnode_cap = si_cspace_cap
            and root_size = si_cnode_size
            and tcb_cap = "TcbCap (the (t obj_id))"] |
         simp add: guard_equal_si_cspace_cap' is_tcb_default_cap)+
  apply (subst offset_slot_si_cnode_size', assumption)+
  apply (clarsimp simp: cap_transform_MasterReplyCap)
  by sep_solve


lemma tcb_half_id:
  "\<lbrakk>well_formed spec; is_tcb object; \<not> is_waiting_thread object;
    cdl_objects spec obj_id = Some object\<rbrakk>
  \<Longrightarrow> tcb_half spec object = object"
  apply (frule well_formed_tcb_pending_op_cap [where obj_id=obj_id], simp add: object_at_def)
  apply (frule well_formed_tcb_replycap_cap [where obj_id=obj_id], simp add: object_at_def)
  apply (frule well_formed_tcb_pending_op_replycap [where obj_id=obj_id], simp add: object_at_def)
  apply (frule well_formed_tcb_boundntfn_cap [where obj_id=obj_id], simp add: object_at_def)
  apply (fastforce simp: tcb_half_def is_waiting_thread_def is_tcb_def
                         opt_cap_def slots_of_def object_slots_def update_slots_def
                         cdl_tcb.splits
                  split: cdl_object.splits)
  done

lemma tcb_half_initialised_object_initialised:
  "\<lbrakk>well_formed spec; tcb_at obj_id spec; \<not> object_at is_waiting_thread obj_id spec\<rbrakk>
  \<Longrightarrow> tcb_half_initialised spec t obj_id = object_initialised spec t obj_id"
  by (clarsimp simp: tcb_half_initialised_def object_initialised_def object_initialised_general_def
                     object_at_def tcb_half_id)

lemma tcb_half_initialised_object_initialised':
  "well_formed spec
  \<Longrightarrow> (\<And>*obj_id | tcb_at obj_id spec \<and> \<not> object_at is_waiting_thread obj_id spec.
                   tcb_half_initialised spec t obj_id)
    = (\<And>*obj_id | tcb_at obj_id spec \<and> \<not> object_at is_waiting_thread obj_id spec.
                   object_initialised spec t obj_id)"
  apply(rule sep.prod.cong, simp)
  apply (rule tcb_half_initialised_object_initialised, simp+)
  done

lemma start_threads_sep:
  "\<lbrace>\<guillemotleft>tcbs_half_initialised spec t {obj_id. tcb_at obj_id spec} \<and>*
     si_caps_at t dup_caps spec False {obj_id. cnode_or_tcb_at obj_id spec} \<and>*
     si_objects \<and>* R\<guillemotright> and
     K(well_formed spec \<and> set obj_ids = dom (cdl_objects spec) \<and> distinct obj_ids)\<rbrace>
   start_threads spec dup_caps obj_ids
   \<lbrace>\<lambda>_.\<guillemotleft>objects_initialised spec t {obj_id. tcb_at obj_id spec} \<and>*
        si_caps_at t dup_caps spec False {obj_id. cnode_or_tcb_at obj_id spec} \<and>*
        si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (clarsimp simp: start_threads_def tcbs_half_initialised_def objects_initialised_def)

  (* The threads that don't need to be started can be ignored. *)
  apply (subst sep_map_set_conj_restrict
         [where P="tcb_half_initialised spec t"
            and t="\<lambda>obj_id. object_at is_waiting_thread obj_id spec"], simp+)
  apply (subst sep_map_set_conj_restrict
         [where P="object_initialised spec t"
            and t="\<lambda>obj_id. object_at is_waiting_thread obj_id spec"], simp+)
  apply (subst tcb_half_initialised_object_initialised', assumption)

  (* Now apply the mapM_x rule to reason about a single thread. *)
  apply (clarsimp simp: sep_conj_ac)
  apply (rule mapM_x_set_sep' [where
               P="\<lambda>obj_id. tcb_half_initialised spec t obj_id" and
               Q="\<lambda>obj_id. object_initialised spec t obj_id" and
               I="si_caps_at t dup_caps spec False {obj_id. cnode_or_tcb_at obj_id spec} \<and>*
                  si_objects" and
               xs="[obj_id \<leftarrow> obj_ids. is_waiting_thread_at obj_id spec]" and
               X="{obj_id. object_at is_waiting_thread obj_id spec}" and
              R="R \<and>* (\<And>*obj_id | tcb_at obj_id spec \<and> \<not> object_at is_waiting_thread obj_id spec.
                                   object_initialised spec t obj_id)"
              , simplified sep_conj_ac], simp+)

  (* Now select only a single one of the "si_cap_at t dup_caps spec" predicates. *)
  apply (clarsimp simp: si_caps_at_def, rename_tac obj_id)
  apply (rule hoare_chain)
    apply (rule_tac x = obj_id
                and xs = "{obj_id. cnode_or_tcb_at obj_id spec}"
                and P = "tcb_half_initialised spec t obj_id \<and>* si_objects"
                and Q = "object_initialised spec t obj_id \<and>* si_objects"
                and I = "si_cap_at t dup_caps spec False"
                and R=R
                 in sep_set_conj_map_singleton_wp [simplified], simp_all add: object_at_real_object_at)

  (* Then apply the start_thread_sep rule and we are done. *)
    apply (wp sep_wp: start_thread_sep [where t=t], (simp|sep_solve)+)
  done

end
