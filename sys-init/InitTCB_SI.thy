(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory InitTCB_SI
imports
  "../proof/capDL-api/KHeap_DP"
  "../proof/capDL-api/TCB_DP"
  ObjectInitialised_SI
  RootTask_SI
  SysInit_SI
begin

lemma cap_has_type_cap_has_object [simp]:
  "cap_has_type cap \<Longrightarrow> cap_has_object cap"
  by (clarsimp simp: cap_type_def cap_has_object_def split: cdl_cap.splits)


lemma tcb_decomp:
  "is_tcb obj
  \<Longrightarrow>
   (obj_id \<mapsto>o object_default_state obj)
   =
   (obj_id \<mapsto>f Tcb (default_tcb (object_domain obj)) \<and>*
   (obj_id, tcb_cspace_slot) \<mapsto>c NullCap \<and>*
   (obj_id, tcb_vspace_slot) \<mapsto>c NullCap \<and>*
   (obj_id, tcb_ipcbuffer_slot) \<mapsto>c NullCap \<and>*
   (obj_id, tcb_replycap_slot) \<mapsto>c NullCap \<and>*
   (obj_id, tcb_caller_slot) \<mapsto>c NullCap \<and>*
   (obj_id, tcb_pending_op_slot) \<mapsto>c NullCap \<and>*
    obj_id \<mapsto>E Tcb (default_tcb (object_domain obj)))"
  apply (rule ext, rename_tac s)
  apply (clarsimp simp: is_tcb_def object_default_state_def2)
  apply (case_tac obj, simp_all)
  apply (subst sep_map_o_decomp)
  apply (subst sep_map_S_decomp_list [where slots = "[0 .e. tcb_pending_op_slot]"])
    apply (force simp: default_tcb_def object_slots_def)
   apply clarsimp
  apply clarsimp
  apply (clarsimp simp: sep_list_conj_def)
  apply (subst default_tcb_slots)
  apply (unfold map.simps)
  apply (clarsimp simp: tcb_slot_defs object_domain_def)
  apply (clarsimp simp: sep_conj_assoc)
  apply rule
   apply (sep_drule sep_map_c_sep_map_s,
          fastforce simp: default_tcb_def object_slots_def tcb_pending_op_slot_def)+
   apply sep_solve
  apply (sep_drule sep_map_s_sep_map_c',
         simp add: default_tcb_def object_slots_def tcb_pending_op_slot_def)+
  apply sep_solve
  done


lemma pred_subst: "P x = P y \<Longrightarrow> P y = P z \<Longrightarrow> P x = P z" by clarsimp

lemma tcb_decomp2:
  "\<lbrakk>well_formed spec; cdl_objects spec obj_id = Some obj;
    is_tcb obj;
    t obj_id = Some k_obj_id;
    t (cap_object cspace_cap) = Some cspace_kobj_id;

    opt_cap (obj_id, tcb_cspace_slot) spec = Some cspace_cap;
    opt_cap (obj_id, tcb_vspace_slot) spec = Some vspace_cap;
    opt_cap (obj_id, tcb_ipcbuffer_slot) spec = Some buffer_frame_cap;
    opt_cap (obj_id, tcb_replycap_slot) spec = Some NullCap;
    opt_cap (obj_id, tcb_caller_slot) spec = Some NullCap;
    opt_cap (obj_id, tcb_pending_op_slot) spec = Some NullCap\<rbrakk>
  \<Longrightarrow> (k_obj_id \<mapsto>o spec2s t obj) =
    (k_obj_id \<mapsto>f obj \<and>*
     (k_obj_id, tcb_cspace_slot)     \<mapsto>c cap_transform t cspace_cap \<and>*
     (k_obj_id, tcb_vspace_slot)     \<mapsto>c cap_transform t vspace_cap \<and>*
     (k_obj_id, tcb_ipcbuffer_slot)  \<mapsto>c cap_transform t buffer_frame_cap \<and>*
     (k_obj_id, tcb_replycap_slot)   \<mapsto>c NullCap \<and>*
     (k_obj_id, tcb_caller_slot)     \<mapsto>c NullCap \<and>*
     (k_obj_id, tcb_pending_op_slot) \<mapsto>c NullCap \<and>*
      k_obj_id \<mapsto>E Tcb (default_tcb minBound))"
  apply (frule (1) well_formed_object_slots)
  apply (frule (1) well_formed_object_domain)
  apply (clarsimp simp: is_tcb_def object_domain_def object_default_state_def2)
  apply (case_tac obj, simp_all)
  apply (subst sep_map_o_decomp)
  apply (subst sep_map_S_decomp_list [where slots = "[0 .e. tcb_pending_op_slot]"])
    apply (drule (1) well_formed_object_slots, simp)
    apply (force simp: object_default_state_def2 default_tcb_def object_slots_def split: cdl_object.splits)
   apply clarsimp
  apply (clarsimp simp: sep_list_conj_def)
  apply (subst default_tcb_slots)
  apply (clarsimp simp: tcb_slot_defs sep_conj_assoc)
  apply (rule ext, rule)
   apply (sep_drule sep_map_c_sep_map_s, rule object_slots_spec2s', fastforce simp: opt_cap_def slots_of_def opt_object_def)+
   apply (subst (asm) sep_map_E_eq [where obj'="Tcb (default_tcb minBound)"])
     apply (clarsimp simp: object_type_def)
    apply simp
   apply clarsimp
   apply sep_solve
  apply (subst sep_map_f_spec2s [where t=t, THEN sym])
  apply (subst (asm) sep_map_f_spec2s [where t=t, THEN sym])
  apply (sep_drule sep_map_s_sep_map_c',
         clarsimp simp: object_slots_def update_slots_def spec2s_def opt_object_def
                        opt_cap_def slots_of_def)+
  apply (subst sep_map_E_eq [where obj'="Tcb (default_tcb minBound)"])
    apply (clarsimp simp: object_type_def)
    apply (clarsimp simp:  object_slots_def update_slots_def spec2s_def
                        opt_object_def opt_cap_def slots_of_def)
  apply sep_solve
  done

lemma default_cap_size_0:
  "type \<noteq> CNodeType
 \<Longrightarrow> default_cap type obj_id sz = default_cap type obj_id 0"
  by (clarsimp simp: default_cap_def split: cdl_object_type.splits)

lemma tcb_configure_pre:
  "\<lbrakk>well_formed spec;
    tcb_at obj_id spec;

    opt_cap (obj_id, tcb_cspace_slot) spec = Some cspace_cap;
    opt_cap (obj_id, tcb_vspace_slot) spec = Some vspace_cap;
    opt_cap (obj_id, tcb_ipcbuffer_slot) spec = Some buffer_frame_cap;

    cap_object cspace_cap = cspace_id;
    cap_object vspace_cap = vspace_id;
    cap_object buffer_frame_cap = buffer_frame_id;

    cdl_objects spec cspace_id = Some spec_cnode;
    object_size_bits spec_cnode = cnode_size;
    cap_type buffer_frame_cap = Some buffer_frame_type;

    orig_caps obj_id    = Some tcb_index;
    orig_caps cspace_id = Some cspace_index;
    orig_caps vspace_id = Some vspace_index;
    orig_caps buffer_frame_id = Some buffer_frame_index;

    t obj_id    = Some k_obj_id;
    t cspace_id = Some cspace_kobj_id;
    t vspace_id = Some vspace_kobj_id;
    t buffer_frame_id = Some buffer_frame_kobj_id;

    tcb_slot    = offset tcb_index si_cnode_size;
    cspace_slot = offset cspace_index si_cnode_size;
    vspace_slot = offset vspace_index si_cnode_size;
    buffer_frame_slot = offset buffer_frame_index si_cnode_size;

    tcb_cap = default_cap TcbType {k_obj_id} 0;
    k_cspace_cap = default_cap CNodeType {cspace_kobj_id} cnode_size;
    k_vspace_cap = default_cap PageDirectoryType {vspace_kobj_id} 0;
    k_buffer_frame_cap = default_cap buffer_frame_type {buffer_frame_kobj_id} 0;

    \<guillemotleft>object_empty spec t obj_id \<and>*
     si_cap_at t orig_caps spec obj_id \<and>*
     si_cap_at t orig_caps spec cspace_id \<and>*
     si_cap_at t orig_caps spec vspace_id \<and>*
     si_cap_at t orig_caps spec buffer_frame_id \<and>*
     si_objects \<and>* R\<guillemotright> s\<rbrakk>
 \<Longrightarrow>
    \<guillemotleft>si_tcb_id \<mapsto>f root_tcb \<and>*
     (si_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*

     (* Root CNode. *)
     si_cnode_id \<mapsto>f CNode (empty_cnode si_cnode_size) \<and>*
     (* Cap to the root CNode. *)
     (si_tcb_id, tcb_cspace_slot) \<mapsto>c si_cspace_cap \<and>*
     (* Cap that the root task has to it's own CNode. *)
     (si_cnode_id, unat seL4_CapInitThreadCNode) \<mapsto>c si_cnode_cap \<and>*

     (* IRQ control cap *)
     (si_cnode_id, unat seL4_CapIRQControl) \<mapsto>c IrqControlCap \<and>*

     (* ASID caps. *)
      si_asid \<and>*

     (* Client TCB. *)
     k_obj_id \<mapsto>f Tcb (default_tcb minBound) \<and>*

     (* Cap to the client TCB. *)
     (si_cnode_id, tcb_slot) \<mapsto>c tcb_cap \<and>*

     (* Caps to install in the TCB *)
     (si_cnode_id, cspace_slot) \<mapsto>c k_cspace_cap \<and>*
     (si_cnode_id, vspace_slot) \<mapsto>c k_vspace_cap \<and>*
     (si_cnode_id, buffer_frame_slot) \<mapsto>c k_buffer_frame_cap \<and>*

     (* Caps slots in the TCB. *)
     (k_obj_id, tcb_cspace_slot) \<mapsto>c NullCap \<and>*
     (k_obj_id, tcb_vspace_slot) \<mapsto>c NullCap \<and>*
     (k_obj_id, tcb_ipcbuffer_slot) \<mapsto>c NullCap \<and>*

     (k_obj_id, tcb_replycap_slot) \<mapsto>c NullCap \<and>*
     (k_obj_id, tcb_caller_slot) \<mapsto>c NullCap \<and>*
     (k_obj_id, tcb_pending_op_slot) \<mapsto>c NullCap \<and>*
      k_obj_id \<mapsto>E Tcb (default_tcb minBound) \<and>*
      R\<guillemotright> s"
  apply clarsimp
  apply (frule (1) well_formed_tcb_cspace_cap)
  apply (frule (1) well_formed_tcb_vspace_cap)
  apply (frule (1) well_formed_tcb_ipcbuffer_cap)
  apply (clarsimp simp: object_empty_def object_initialised_general_def)
  apply (clarsimp simp: si_objects_def)
  apply (clarsimp simp: sep_conj_exists sep_conj_assoc)
  apply (clarsimp simp: si_cap_at_def sep_conj_assoc sep_conj_exists)
  apply (clarsimp simp: object_at_def)
  apply (subst (asm) tcb_decomp, assumption)
  apply (subst offset_slot', assumption)+
  apply (frule (1) well_formed_object_domain [where obj_id=obj_id])
  apply (frule (2) well_formed_types_match [where cap=cspace_cap], clarsimp)
  apply (frule (2) well_formed_types_match [where cap=vspace_cap], clarsimp)
  apply (frule (2) well_formed_types_match [where cap=buffer_frame_cap], clarsimp simp: cap_type_def)
  apply (clarsimp simp: object_type_is_object cap_has_type_cap_type')
  apply (subst (asm) default_cap_size_0 [where type=TcbType], simp)
  apply (subst (asm) default_cap_size_0 [where type=PageDirectoryType], simp)
  apply (cut_tac type="FrameType sz" and sz="(object_size_bits obja)" and
              obj_id="{buffer_frame_kobj_id}" in default_cap_size_0, simp+)
  apply sep_solve
done

(* Replace well_formed_cnode_object_size_bits_eq with this one. *)
lemma well_formed_cnode_object_size_bits_eq2:
  "\<lbrakk>well_formed spec; cdl_objects spec obj_id = Some spec_obj;
    cdl_objects spec (cap_object cap) = Some obj; cap_type cap = Some CNodeType;
    object_slots spec_obj slot = Some cap\<rbrakk>
  \<Longrightarrow> object_size_bits obj = cnode_cap_size cap"
  apply (erule well_formed_cnode_object_size_bits_eq [where slot="(obj_id,slot)"])
    apply (clarsimp simp: opt_cap_def slots_of_def opt_object_def split: option.splits)
   apply (clarsimp simp: opt_object_def split: option.splits)
  apply assumption
  done

lemma default_cap_update_cap_object_non_cnode:
  "\<lbrakk>cap_type cap = Some type; is_default_cap cap; cnode_cap_size cap \<le> 32;
    type \<noteq> UntypedType; type \<noteq> AsidPoolType; type \<noteq> CNodeType\<rbrakk>
  \<Longrightarrow> default_cap type {obj_id} sz =
      update_cap_object obj_id cap"
  apply (frule (4) default_cap_update_cap_object [where obj_id=obj_id])
  apply (subst default_cap_size_0, simp+)
  done

lemma sep_map_f_eq_tcb_fault_endpoint:
  "\<lbrakk>\<not> cdl_tcb_has_fault tcb; cdl_tcb_domain tcb = minBound\<rbrakk> \<Longrightarrow>
   obj_id \<mapsto>f Tcb (update_tcb_fault_endpoint (cdl_tcb_fault_endpoint tcb) (default_tcb minBound)) =
   obj_id \<mapsto>f Tcb tcb"
   apply (rule sep_map_f_eq_tcb)
     apply (clarsimp simp: update_tcb_fault_endpoint_def)
    apply (clarsimp simp: update_tcb_fault_endpoint_def default_tcb_def)
   apply (clarsimp simp: update_tcb_fault_endpoint_def default_tcb_def)
  done

lemma tcb_configure_post:
  "\<lbrakk>well_formed spec; tcb_at obj_id spec;
    cdl_objects spec obj_id = Some (Tcb spec_tcb);
    opt_cap (obj_id, tcb_cspace_slot) spec = Some spec_cspace_cap;
    opt_cap (obj_id, tcb_vspace_slot) spec = Some spec_vspace_cap;
    opt_cap (obj_id, tcb_ipcbuffer_slot) spec = Some spec_buffer_frame_cap;
    opt_cap (obj_id, tcb_replycap_slot) spec = Some NullCap;
    opt_cap (obj_id, tcb_caller_slot) spec = Some NullCap;
    opt_cap (obj_id, tcb_pending_op_slot) spec = Some NullCap;

    cap_object spec_cspace_cap = cspace_id;
    cap_object spec_vspace_cap = vspace_id;
    cap_object spec_buffer_frame_cap = buffer_frame_id;

    cdl_objects spec cspace_id = Some spec_cnode;
    object_size_bits spec_cnode = cnode_size;
    cap_type spec_buffer_frame_cap = Some buffer_frame_type;

    cap_data spec_cspace_cap = cspace_cap_data;
    cap_data spec_vspace_cap = vspace_cap_data;

    cspace_cap = default_cap CNodeType {cspace_kobj_id} cnode_size;
    vspace_cap = default_cap PageDirectoryType {vspace_kobj_id} 0;
    buffer_frame_cap = default_cap buffer_frame_type {buffer_frame_kobj_id} 0;

    orig_caps obj_id = Some tcb_index;
    orig_caps cspace_id = Some cspace_index;
    orig_caps vspace_id = Some vspace_index;
    orig_caps buffer_frame_id = Some buffer_frame_index;

    t obj_id = Some k_obj_id;
    t cspace_id = Some cspace_kobj_id;
    t vspace_id = Some vspace_kobj_id;
    t buffer_frame_id = Some buffer_frame_kobj_id;

    cdl_tcb_fault_endpoint new_tcb = cdl_tcb_fault_endpoint spec_tcb;
    cdl_tcb_has_fault new_tcb = cdl_tcb_has_fault spec_tcb;

    tcb_index < 2 ^ si_cnode_size;
    cspace_index < 2 ^ si_cnode_size;
    vspace_index < 2 ^ si_cnode_size;
    buffer_frame_index < 2 ^ si_cnode_size;
    \<guillemotleft>si_tcb_id \<mapsto>f root_tcb \<and>*
     (si_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
     (si_tcb_id, tcb_cspace_slot) \<mapsto>c si_cspace_cap \<and>*

      si_cnode_id \<mapsto>f CNode (empty_cnode si_cnode_size) \<and>*
     (si_cnode_id, unat seL4_CapInitThreadCNode) \<mapsto>c si_cnode_cap \<and>*
     (si_cnode_id, offset tcb_index si_cnode_size) \<mapsto>c
          default_cap TcbType {k_obj_id} 0 \<and>*
     (si_cnode_id, offset cspace_index si_cnode_size) \<mapsto>c
          default_cap CNodeType {cspace_kobj_id} cnode_size \<and>*
     (si_cnode_id, offset vspace_index si_cnode_size) \<mapsto>c
          default_cap PageDirectoryType {vspace_kobj_id} 0 \<and>*
     (si_cnode_id, offset buffer_frame_index si_cnode_size) \<mapsto>c buffer_frame_cap \<and>*
     (si_cnode_id, unat seL4_CapIRQControl) \<mapsto>c IrqControlCap \<and>*
      si_asid \<and>*

      k_obj_id \<mapsto>f Tcb (update_tcb_fault_endpoint (cdl_tcb_fault_endpoint spec_tcb)
                                                  (default_tcb minBound)) \<and>*
     (k_obj_id, tcb_cspace_slot) \<mapsto>c update_cap_data_det cspace_cap_data
                                    (default_cap CNodeType {cspace_kobj_id} cnode_size) \<and>*
     (k_obj_id, tcb_vspace_slot) \<mapsto>c default_cap PageDirectoryType {vspace_kobj_id} 0 \<and>*
     (k_obj_id, tcb_ipcbuffer_slot) \<mapsto>c buffer_frame_cap \<and>*
     (k_obj_id, tcb_replycap_slot) \<mapsto>c NullCap \<and>*
     (k_obj_id, tcb_caller_slot) \<mapsto>c NullCap \<and>*
     (k_obj_id, tcb_pending_op_slot) \<mapsto>c NullCap \<and>*
     k_obj_id \<mapsto>E Tcb (default_tcb minBound) \<and>* R\<guillemotright> s\<rbrakk>
  \<Longrightarrow> \<guillemotleft>object_initialised spec t obj_id \<and>*
       si_cap_at t orig_caps spec obj_id \<and>*
       si_cap_at t orig_caps spec cspace_id \<and>*
       si_cap_at t orig_caps spec vspace_id \<and>*
       si_cap_at t orig_caps spec buffer_frame_id \<and>*
       si_objects \<and>* R\<guillemotright> s"
  apply (frule (1) well_formed_tcb_cspace_cap)
  apply (frule (1) well_formed_tcb_vspace_cap)
  apply (frule (1) well_formed_tcb_ipcbuffer_cap)
  apply (frule (1) well_formed_tcb_replycap_cap)
  apply (frule (1) well_formed_tcb_caller_cap)
  apply (frule (1) well_formed_tcb_pending_op_cap)
  apply (frule (1) well_formed_tcb_has_fault)
  apply (frule (1) well_formed_tcb_domain)
  apply (frule (1) well_formed_cap_object [where slot=tcb_cspace_slot], clarsimp)
  apply (frule (1) well_formed_cap_object [where slot=tcb_vspace_slot], clarsimp)
  apply (frule (1) well_formed_cap_object [where slot=tcb_ipcbuffer_slot],
         clarsimp simp: cap_type_def)
  apply clarsimp
  apply (frule (1) well_formed_types_match [where slot=tcb_cspace_slot], fastforce+)
  apply (frule (1) well_formed_types_match [where slot=tcb_vspace_slot], fastforce+)
  apply (frule (1) well_formed_types_match [where slot=tcb_ipcbuffer_slot],
         (fastforce simp: cap_type_def)+)
  apply (clarsimp simp: object_initialised_def object_initialised_general_def)
  apply (clarsimp simp: si_objects_def)
  apply (clarsimp simp: sep_conj_exists sep_conj_assoc)
  apply (clarsimp simp: si_cap_at_def sep_conj_assoc sep_conj_exists)
  apply (clarsimp simp: object_at_def)
  apply (subst tcb_decomp2 [where obj_id=obj_id and k_obj_id=k_obj_id],
         (assumption|simp)+)
  apply (subst (asm) sep_map_f_eq_tcb_fault_endpoint, assumption+)
  apply (clarsimp simp: opt_cap_def slots_of_def opt_object_def)
  apply (frule (2) well_formed_well_formed_cap [where cap=spec_cspace_cap],
         simp add: cap_type_null)
  apply (frule (2) well_formed_well_formed_cap [where cap=spec_vspace_cap],
         simp add: cap_type_null)
  apply (frule (2) well_formed_vm_cap_has_asid [where cap=spec_cspace_cap])
  apply (frule (2) well_formed_vm_cap_has_asid [where cap=spec_vspace_cap])
  apply (frule (1) well_formed_is_fake_vm_cap
         [where cap=spec_vspace_cap], simp+)
  apply (subst (asm) cap_has_type_cap_type', simp)+

  apply (frule (4) well_formed_cnode_object_size_bits_eq2, simp)
  apply (subst (asm) update_cap_data [where spec_cap = spec_cspace_cap],
         (assumption|simp|fastforce dest: is_fake_vm_cap_cap_type)+)
  apply (subst cap_transform_update_cap_object
         [where obj_id="cap_object spec_cspace_cap"],
         (assumption|simp)+)
  apply (subst cap_transform_update_cap_object
         [where obj_id="cap_object spec_vspace_cap"],
         (assumption|simp)+)
  apply (subst cap_transform_update_cap_object
         [where obj_id="cap_object spec_buffer_frame_cap"],
         (assumption|simp)+)
  apply (subst (asm) default_cap_update_cap_object_non_cnode,
         assumption, assumption, simp+)
  apply (subst (asm) default_cap_update_cap_object_non_cnode,
         assumption, assumption, simp+)
  apply (subst default_cap_update_cap_object_non_cnode,
         assumption, assumption, simp+)
  apply (subst default_cap_update_cap_object_pd [THEN sym],
         assumption, assumption, simp+)
  apply (cut_tac type = "FrameType sz" in default_cap_update_cap_object_non_cnode,
          (assumption|simp|fastforce)+)
  apply (subst (asm) offset_slot', assumption)+
  apply (clarsimp simp: sep_conj_assoc)
  apply (clarsimp simp: object_type_simps)
  apply (subst default_cap_size_0 [where type=TcbType], simp)
  apply (cut_tac type=PageDirectoryType and sz="(object_size_bits obj)" and
              obj_id="{vspace_kobj_id}" in default_cap_size_0, simp+)
  apply (cut_tac type="FrameType sz" and sz="(object_size_bits obja)" and
              obj_id="{buffer_frame_kobj_id}" in default_cap_size_0, simp+)
by sep_solve

lemma tcb_cap_has_object [elim]:
  "is_tcb_cap tcb_cap \<Longrightarrow> cap_has_object tcb_cap"
  by (clarsimp simp: cap_type_def cap_has_object_def split: cdl_cap.splits)

lemma tcb_cap_not_ep_related_cap:
  "is_tcb_cap tcb_cap \<Longrightarrow> \<not> ep_related_cap tcb_cap"
  by (clarsimp simp: cap_type_def ep_related_cap_def split: cdl_cap.splits)

lemma tcb_cap_not_is_memory_cap:
  "is_tcb_cap tcb_cap \<Longrightarrow> \<not> is_memory_cap tcb_cap"
  by (clarsimp simp: cap_type_def is_memory_cap_def split: cdl_cap.splits)

lemma update_cap_data_det_cnode:
  "is_cnode_cap cap \<Longrightarrow> update_cap_data_det data cap = guard_update cap data"
  by (clarsimp simp: update_cap_data_det_def cap_type_def split: cdl_cap.splits)

lemma cdl_update_cnode_cap_data_non_zero:
  "\<lbrakk>is_cnode_cap cap; data \<noteq> 0\<rbrakk> \<Longrightarrow>
   cdl_update_cnode_cap_data cap data = guard_update cap data"
  by (clarsimp simp: cdl_update_cnode_cap_data_def guard_update_def cap_type_def
              split: cdl_cap.splits)

lemma seL4_TCB_Configure_sep:
  "\<lbrakk>(* Caps point to the right objects. *)
     cap_object cnode_cap = cnode_id;
     cap_object cnode_cap' = cnode_id;

     cap_object tcb_cap    = tcb_id;

     (* Caps are of the right type. *)
     is_tcb_cap tcb_cap;
     is_cnode_cap cnode_cap;
     is_cnode_cap cspace_cap;
     is_pd_cap vspace_cap;
     is_frame_cap buffer_frame_cap;

     (* Cap slots match their cptrs. *)
     cnode_cap_slot = offset src_root root_size;
     tcb_cap_slot = offset tcb_root root_size;
     cspace_slot = offset cspace_root root_size;
     vspace_slot = offset vspace_root root_size;
     buffer_frame_slot = offset buffer_frame_root root_size;

     one_lvl_lookup cnode_cap word_bits root_size;
     guard_equal cnode_cap tcb_root word_bits;
     guard_equal cnode_cap cspace_root word_bits;
     guard_equal cnode_cap vspace_root word_bits;
     guard_equal cnode_cap buffer_frame_root word_bits;

     is_tcb root_tcb;
     buffer_addr \<noteq> 0;
     cspace_root_data \<noteq> 0;
     cspace_cap' = update_cap_data_det cspace_root_data cspace_cap;
     new_tcb_fields = update_tcb_fault_endpoint fault_ep tcb\<rbrakk>
   \<Longrightarrow> \<lbrace>\<lambda>s. \<guillemotleft>
     si_tcb_id \<mapsto>f root_tcb \<and>*
     (si_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*

     (* Root CNode. *)
     cnode_id \<mapsto>f CNode (empty_cnode root_size) \<and>*
     (* Cap to the root CNode. *)
     (si_tcb_id, tcb_cspace_slot) \<mapsto>c cnode_cap \<and>*

     (* Cap that the root task has to it's own CNode. *)
     (cnode_id, cnode_cap_slot) \<mapsto>c cnode_cap' \<and>*

     (* IRQ control cap *)
     (si_cnode_id, unat seL4_CapIRQControl) \<mapsto>c IrqControlCap \<and>*

     (* ASID caps. *)
     si_asid \<and>*

     (* TCB's stuff *)
     tcb_id    \<mapsto>f Tcb tcb \<and>*

     (* Where to copy the cap from (in the client CNode). *)
     (cnode_id, tcb_cap_slot) \<mapsto>c tcb_cap \<and>*
     (cnode_id, cspace_slot)  \<mapsto>c cspace_cap \<and>*
     (cnode_id, vspace_slot)  \<mapsto>c vspace_cap \<and>*
     (cnode_id, buffer_frame_slot) \<mapsto>c buffer_frame_cap \<and>*

     (* Cap to the TCB. *)
     (tcb_id, tcb_cspace_slot) \<mapsto>c NullCap \<and>*
     (tcb_id, tcb_vspace_slot) \<mapsto>c NullCap \<and>*
     (tcb_id, tcb_ipcbuffer_slot) \<mapsto>c NullCap \<and>*
      R\<guillemotright> s\<rbrace>
  seL4_TCB_Configure tcb_root fault_ep priority
                     cspace_root cspace_root_data
                     vspace_root vspace_root_data
                     buffer_addr buffer_frame_root
  \<lbrace>\<lambda>_. \<guillemotleft>si_tcb_id \<mapsto>f root_tcb \<and>*
       (si_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*

       (* Root CNode. *)
       cnode_id \<mapsto>f CNode (empty_cnode root_size) \<and>*
       (* Cap to the root CNode. *)
       (si_tcb_id, tcb_cspace_slot) \<mapsto>c cnode_cap \<and>*
       (* Cap that the root task has to it's own CNode. *)
       (cnode_id, cnode_cap_slot) \<mapsto>c cnode_cap' \<and>*

       (* IRQ control cap *)
       (si_cnode_id, unat seL4_CapIRQControl) \<mapsto>c IrqControlCap \<and>*

       (* ASID caps. *)
       si_asid \<and>*

       (* TCB's stuff *)
       tcb_id    \<mapsto>f Tcb new_tcb_fields \<and>*

       (* Where to copy the cap from (in the client CNode). *)
       (cnode_id, tcb_cap_slot) \<mapsto>c tcb_cap \<and>*
       (cnode_id, cspace_slot)  \<mapsto>c cspace_cap \<and>*
       (cnode_id, vspace_slot)  \<mapsto>c vspace_cap \<and>*
       (cnode_id, buffer_frame_slot) \<mapsto>c buffer_frame_cap \<and>*

       (* Cap to the TCB. *)
       (tcb_id, tcb_cspace_slot) \<mapsto>c cspace_cap' \<and>*
       (tcb_id, tcb_vspace_slot) \<mapsto>c vspace_cap \<and>*
       (tcb_id, tcb_ipcbuffer_slot) \<mapsto>c buffer_frame_cap \<and>*
       R\<guillemotright>\<rbrace>"
  apply (subst (asm) update_cap_data_det_cnode, assumption)
  apply (rule hoare_chain)
    apply (wp TCB_Configure_wp [where
              cnode_id=cnode_id and
              cnode_cap=cnode_cap and
              tcb_id=tcb_id and
              tcb_cap=tcb_cap and
              cspace_root=cspace_root and
              vspace_root=vspace_root and
              tcb_cap_slot=tcb_cap_slot and
              cspace_slot=cspace_slot and
              vspace_slot=vspace_slot and
              buffer_frame_slot=buffer_frame_slot and
              root_size=root_size and
              cspace_cap=cspace_cap and
              vspace_cap=vspace_cap and
              buffer_frame_cap=buffer_frame_cap and
              tcb = tcb and
              R="(si_cnode_id, unat seL4_CapIRQControl) \<mapsto>c IrqControlCap \<and>* si_asid \<and>* R"],
           (fastforce simp: tcb_cap_not_ep_related_cap
                            tcb_cap_not_is_memory_cap
                            cdl_update_cnode_cap_data_non_zero
             | intro conjI | sep_cancel)+)
  done


lemma seL4_TCB_Configure_object_initialised_sep_helper:
  "\<lbrakk>well_formed spec; tcb_at obj_id spec;
    cdl_objects spec obj_id = Some (Tcb tcb);
    opt_cap (obj_id, tcb_cspace_slot) spec = Some spec_cspace_cap;
    opt_cap (obj_id, tcb_vspace_slot) spec = Some spec_vspace_cap;
    opt_cap (obj_id, tcb_ipcbuffer_slot) spec = Some spec_buffer_frame_cap;
    opt_cap (obj_id, tcb_replycap_slot) spec = Some NullCap;
    opt_cap (obj_id, tcb_caller_slot) spec = Some NullCap;
    opt_cap (obj_id, tcb_pending_op_slot) spec = Some NullCap;

    cap_object spec_cspace_cap = cspace_id;
    cap_object spec_vspace_cap = vspace_id;
    cap_object spec_buffer_frame_cap = buffer_frame_id;

    cdl_objects spec cspace_id = Some spec_cnode;
    object_size_bits spec_cnode = cnode_size;
    cap_type spec_buffer_frame_cap = Some buffer_frame_type;

    orig_caps obj_id    = Some tcb_index;
    orig_caps cspace_id = Some cspace_index;
    orig_caps vspace_id = Some vspace_index;
    orig_caps buffer_frame_id = Some buffer_frame_index;

    t obj_id    = Some k_obj_id;
    t cspace_id = Some cspace_kobj_id;
    t vspace_id = Some vspace_kobj_id;
    t buffer_frame_id = Some buffer_frame_kobj_id;

    tcb_index < 2 ^ si_cnode_size;
    cspace_index < 2 ^ si_cnode_size;
    vspace_index < 2 ^ si_cnode_size;
    buffer_frame_index < 2 ^ si_cnode_size;

(* Put this in later once we have priorities.
    priority = tcb_priority tcb;
    tcb_ipc_buffer_address tcb = buffer_addr; *)
    buffer_addr \<noteq> 0;
    cspace_root_data = cap_data spec_cspace_cap;
    fault_ep = cdl_tcb_fault_endpoint tcb\<rbrakk>
 \<Longrightarrow>
   \<lbrace>\<guillemotleft>object_empty spec t obj_id \<and>*
     si_cap_at t orig_caps spec obj_id \<and>*
     si_cap_at t orig_caps spec cspace_id \<and>*
     si_cap_at t orig_caps spec vspace_id \<and>*
     si_cap_at t orig_caps spec buffer_frame_id \<and>*
     si_objects \<and>* R\<guillemotright>\<rbrace>
  seL4_TCB_Configure tcb_index fault_ep priority
                     cspace_index cspace_root_data
                     vspace_index vspace_root_data
                     buffer_addr buffer_frame_index
   \<lbrace>\<lambda>_. \<guillemotleft>object_initialised spec t obj_id \<and>*
         si_cap_at t orig_caps spec obj_id \<and>*
         si_cap_at t orig_caps spec cspace_id \<and>*
         si_cap_at t orig_caps spec vspace_id \<and>*
         si_cap_at t orig_caps spec buffer_frame_id \<and>*
         si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (frule (1) well_formed_tcb_vspace_cap, elim exE conjE)
  apply (frule (1) well_formed_tcb_ipcbuffer_cap, clarsimp)
  apply (frule (3) well_formed_tcb_cspace_cap_cap_data)
  apply (frule guard_equal_si_cspace_cap' [where src_index=tcb_index])
  apply (frule guard_equal_si_cspace_cap' [where src_index=cspace_index])
  apply (frule guard_equal_si_cspace_cap' [where src_index=vspace_index])
  apply (frule guard_equal_si_cspace_cap' [where src_index=buffer_frame_index])
  apply (rule hoare_chain)
    prefer 2
    apply (rule_tac s=s  and t=t and orig_caps=orig_caps
                 in tcb_configure_pre, (assumption|rule refl|clarsimp)+)[1]
   apply (cut_tac tcb="default_tcb minBound" and
                  cnode_cap = si_cspace_cap and
                  cnode_cap' = si_cnode_cap and
                  tcb_cap = "default_cap TcbType {k_obj_id} 0" and
                  cspace_cap = "default_cap CNodeType {cspace_kobj_id} (object_size_bits spec_cnode)" and
                  vspace_cap = "default_cap PageDirectoryType {vspace_kobj_id} 0" and
                  buffer_frame_cap = "default_cap (FrameType sz) {buffer_frame_kobj_id} 0" and
                  cspace_root = cspace_index and
                  vspace_root = vspace_index and
                  buffer_frame_root = buffer_frame_index and
                  src_root = seL4_CapInitThreadCNode and
                  root_size = si_cnode_size and
                  cspace_root_data = "cap_data spec_cspace_cap" and
                  R="(k_obj_id, tcb_replycap_slot) \<mapsto>c NullCap \<and>*
                     (k_obj_id, tcb_caller_slot) \<mapsto>c NullCap \<and>*
                     (k_obj_id, tcb_pending_op_slot) \<mapsto>c NullCap \<and>*
                      k_obj_id \<mapsto>E Tcb (default_tcb minBound) \<and>* R"
               in seL4_TCB_Configure_sep,
               (assumption|simp|clarsimp)+)[1]
  apply (erule tcb_configure_post, (assumption|simp)+)
  apply (sep_solve)
  done


lemma seL4_TCB_Configure_object_initialised_sep:
  "\<lbrace>\<lambda>s. well_formed spec \<and> cdl_objects spec obj_id = Some (Tcb tcb) \<and>
        cdl_tcb_fault_endpoint tcb = fault_ep \<and>
        opt_cap (obj_id, tcb_cspace_slot) spec = Some spec_cspace_cap \<and>
        opt_cap (obj_id, tcb_vspace_slot) spec = Some spec_vspace_cap \<and>
        opt_cap (obj_id, tcb_ipcbuffer_slot) spec = Some spec_buffer_frame_cap \<and>
        opt_cap (obj_id, tcb_replycap_slot) spec = Some NullCap \<and>
        opt_cap (obj_id, tcb_caller_slot) spec = Some NullCap \<and>
        opt_cap (obj_id, tcb_pending_op_slot) spec = Some NullCap \<and>

        cap_object spec_cspace_cap = cspace_id \<and>
        cap_object spec_vspace_cap = vspace_id \<and>
        cap_object spec_buffer_frame_cap = buffer_frame_id \<and>

        cdl_objects spec cspace_id = Some spec_cnode \<and>
        object_size_bits spec_cnode = cnode_size \<and>
        cap_type spec_buffer_frame_cap = Some buffer_frame_type \<and>

        fault_ep = cdl_tcb_fault_endpoint tcb \<and>
        cspace_root_data = cap_data spec_cspace_cap \<and>
        buffer_addr \<noteq> 0 \<and>

        orig_caps obj_id    = Some tcb_index \<and>
        orig_caps cspace_id = Some cspace_index \<and>
        orig_caps vspace_id = Some vspace_index \<and>
        orig_caps buffer_frame_id = Some buffer_frame_index \<and>

        \<guillemotleft>object_empty spec t obj_id \<and>*
         si_cap_at t orig_caps spec obj_id \<and>*
         si_cap_at t orig_caps spec cspace_id \<and>*
         si_cap_at t orig_caps spec vspace_id \<and>*
         si_cap_at t orig_caps spec buffer_frame_id \<and>*
         si_objects \<and>* R\<guillemotright> s\<rbrace>
  seL4_TCB_Configure tcb_index fault_ep priority
                     cspace_index cspace_root_data
                     vspace_index vspace_root_data
                     buffer_addr buffer_frame_index
   \<lbrace>\<lambda>_. \<guillemotleft>object_initialised spec t obj_id \<and>*
         si_cap_at t orig_caps spec obj_id \<and>*
         si_cap_at t orig_caps spec cspace_id \<and>*
         si_cap_at t orig_caps spec vspace_id \<and>*
         si_cap_at t orig_caps spec buffer_frame_id \<and>*
        si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_assume_pre)
  apply (elim conjE)
  apply (rule hoare_weaken_pre)
   apply (rule_tac k_obj_id = "the (t obj_id)" and
                   cspace_kobj_id = "the (t cspace_id)" and
                   vspace_kobj_id = "the (t vspace_id)" and
                   buffer_frame_kobj_id = "the (t buffer_frame_id)"
                in seL4_TCB_Configure_object_initialised_sep_helper,
    (assumption|fastforce simp:  object_at_def si_cap_at_def sep_conj_exists)+)
  done

lemma init_tcb_sep':
  "\<lbrakk>well_formed spec; obj_id \<in> set tcbs; distinct tcbs;
    set tcbs = {obj_id. tcb_at obj_id spec};
    opt_cap (obj_id, tcb_cspace_slot) spec = Some cspace_cap;
    opt_cap (obj_id, tcb_vspace_slot) spec = Some vspace_cap;
    opt_cap (obj_id, tcb_ipcbuffer_slot) spec = Some tcb_ipcbuffer_cap;
    opt_cap (obj_id, tcb_replycap_slot) spec = Some NullCap;
    opt_cap (obj_id, tcb_caller_slot) spec = Some NullCap;
    opt_cap (obj_id, tcb_pending_op_slot) spec = Some NullCap;
    cap_object cspace_cap = cspace_id;
    cap_object vspace_cap = vspace_id;
    cdl_objects spec cspace_id = Some spec_cnode;
    object_size_bits spec_cnode = cnode_size;
    cap_type tcb_ipcbuffer_cap = Some buffer_frame_type;
    cap_object tcb_ipcbuffer_cap = buffer_frame_id\<rbrakk> \<Longrightarrow>
   \<lbrace>\<guillemotleft>object_empty spec t obj_id \<and>*
     si_cap_at t orig_caps spec obj_id \<and>*
     si_cap_at t orig_caps spec cspace_id \<and>*
     si_cap_at t orig_caps spec vspace_id \<and>*
     si_cap_at t orig_caps spec buffer_frame_id \<and>*
     si_objects \<and>* R\<guillemotright>\<rbrace>
   init_tcb spec orig_caps obj_id
   \<lbrace>\<lambda>_.\<guillemotleft>object_initialised spec t obj_id \<and>*
        si_cap_at t orig_caps spec obj_id \<and>*
        si_cap_at t orig_caps spec cspace_id \<and>*
        si_cap_at t orig_caps spec vspace_id \<and>*
        si_cap_at t orig_caps spec buffer_frame_id \<and>*
        si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (clarsimp)
  apply (subgoal_tac "\<exists>tcb. cdl_objects spec obj_id = Some (Tcb tcb)", clarsimp)
   apply (frule well_formed_tcb_cspace_cap, fastforce)
   apply (frule well_formed_tcb_vspace_cap, fastforce)
   apply (frule well_formed_tcb_ipcbuffer_cap, fastforce)
   apply (clarsimp simp: init_tcb_def)
   apply (wp hoare_drop_imps seL4_TCB_Configure_object_initialised_sep
                             [where spec_cspace_cap=cspace_cap and
                                    spec_vspace_cap=vspace_cap and
                                    spec_buffer_frame_cap=tcb_ipcbuffer_cap])
   apply (fastforce simp: opt_thread_def opt_object_def cap_data_def
                          tcb_ipc_buffer_address_non_zero
                          si_cap_at_def sep_conj_exists)
  apply (clarsimp simp: object_at_def is_tcb_def)
  apply (clarsimp split: cdl_object.splits)
  done

lemma init_tcb_sep:
  "\<lbrakk>well_formed spec; obj_id \<in> set tcbs; distinct tcbs;
    set tcbs = {obj_id. tcb_at obj_id spec}\<rbrakk> \<Longrightarrow>
   \<lbrace>\<guillemotleft>object_empty spec t obj_id \<and>*
     si_caps_at t orig_caps spec {obj_id. real_object_at obj_id spec} \<and>*
     si_objects \<and>* R\<guillemotright>\<rbrace>
   init_tcb spec orig_caps obj_id
   \<lbrace>\<lambda>_.\<guillemotleft>object_initialised spec t obj_id \<and>*
        si_caps_at t orig_caps spec {obj_id. real_object_at obj_id spec} \<and>*
        si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (frule well_formed_tcb_cspace_cap, fastforce)
  apply (frule well_formed_tcb_vspace_cap, fastforce)
  apply (frule well_formed_tcb_ipcbuffer_cap, fastforce)
  apply (frule well_formed_tcb_replycap_cap, fastforce)
  apply (frule well_formed_tcb_caller_cap, fastforce)
  apply (frule well_formed_tcb_pending_op_cap, fastforce)
  apply (clarsimp simp: si_caps_at_def)
  apply (frule (1) well_formed_cap_object [where slot=tcb_cspace_slot], clarsimp)
  apply (frule (1) well_formed_cap_object [where slot=tcb_vspace_slot], clarsimp)
  apply (frule (1) well_formed_cap_object [where slot=tcb_ipcbuffer_slot],
          clarsimp simp: cap_type_def)
  apply clarsimp
  apply (frule object_at_real_object_at, simp)
  apply (rule_tac xs="{obj_id, cap_object cspace_cap, cap_object vspace_cap,
                       cap_object tcb_ipcbuffer_cap}" in sep_set_conj_subset_wp')
     apply (frule (2) well_formed_real_types_match [where slot=tcb_vspace_slot], simp+)
     apply (frule (2) well_formed_real_types_match [where slot=tcb_ipcbuffer_slot], simp+)
     apply (rule conjI)
      apply (erule object_at_real_object_at, erule (1) object_type_object_at)
     apply (erule object_at_real_object_at, fastforce simp: object_at_def object_type_is_object)
    apply clarsimp
   apply clarsimp

  apply (wp sep_wp: init_tcb_sep' [where obj_id=obj_id and tcbs=tcbs and t=t],
        (assumption|fastforce simp: sep_conj_ac)+)

 (* We can break up the sep_map_set_conj if the object ids are distinct. *)
  apply (subgoal_tac "distinct [obj_id, cap_object cspace_cap,
                                        cap_object vspace_cap,
                                        cap_object tcb_ipcbuffer_cap]")
   apply (clarsimp simp: simp: sep_conj_assoc)
   apply (sep_safe+, sep_solve)

  (* The object_ids are all distinct because they point to different types of objects. *)
  apply (frule (2) well_formed_types_match [where slot=tcb_cspace_slot], clarsimp)
  apply (frule (2) well_formed_types_match [where slot=tcb_vspace_slot], clarsimp)
  apply (frule (2) well_formed_types_match [where slot=tcb_ipcbuffer_slot],
          clarsimp simp: cap_type_def)
  apply clarsimp
  apply (fastforce simp: object_type_def object_at_def is_tcb_def cap_has_object_cap_type'
                  split: cdl_object.splits)
  done

lemma init_tcbs_sep_helper:
  "\<lbrakk>well_formed spec; distinct tcbs;
    set tcbs = {obj_id \<in> dom (cdl_objects spec). tcb_at obj_id spec}\<rbrakk> \<Longrightarrow>
   \<lbrace>\<guillemotleft>objects_empty spec t (set tcbs) \<and>*
     si_caps_at t orig_caps spec {obj_id. real_object_at obj_id spec} \<and>*
     si_objects \<and>* R\<guillemotright>\<rbrace>
   mapM_x (init_tcb spec orig_caps) tcbs
   \<lbrace>\<lambda>_.\<guillemotleft>objects_initialised spec t (set tcbs) \<and>*
        si_caps_at t orig_caps spec {obj_id. real_object_at obj_id spec} \<and>*
        si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (clarsimp simp: objects_empty_def objects_initialised_def)
  apply (rule hoare_name_pre_state)
  apply (rule hoare_chain)
    apply (rule_tac R=R in
               mapM_x_set_sep [where
               P="\<lambda>obj_id. object_empty spec t obj_id" and
               Q="\<lambda>obj_id. object_initialised spec t obj_id" and
               I="si_caps_at t orig_caps spec {obj_id. real_object_at obj_id spec} \<and>*
                  si_objects" and
               xs="tcbs",
               simplified sep_conj_assoc], simp+)
    apply (wp init_tcb_sep [where t=t and tcbs=tcbs], (assumption|simp)+)
  done

lemma init_tcbs_sep:
  "\<lbrace>\<guillemotleft>objects_empty spec t {obj_id. tcb_at obj_id spec} \<and>*
     si_caps_at t orig_caps spec {obj_id. real_object_at obj_id spec} \<and>*
     si_objects \<and>* R\<guillemotright> and
     K(well_formed spec \<and> set obj_ids = dom (cdl_objects spec) \<and> distinct obj_ids)\<rbrace>
   init_tcbs spec orig_caps obj_ids
   \<lbrace>\<lambda>_.\<guillemotleft>objects_initialised spec t {obj_id. tcb_at obj_id spec} \<and>*
        si_caps_at t orig_caps spec {obj_id. real_object_at obj_id spec} \<and>*
        si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_gen_asm, clarsimp)
  apply (clarsimp simp: init_tcbs_def)
  apply (drule init_tcbs_sep_helper [where t=t
                                       and orig_caps=orig_caps
                                       and tcbs="[obj\<leftarrow>obj_ids . tcb_at obj spec]"
                                       and R=R],
         (assumption|clarsimp)+)
  done

end
