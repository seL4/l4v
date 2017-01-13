(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory
  InitVSpace_SI
imports
  "../proof/capDL-api/Invocation_DP"
  "../proof/capDL-api/Arch_DP"
  ObjectInitialised_SI
  RootTask_SI
  SysInit_SI
begin

context begin interpretation Arch . (*FIXME: arch_split*)

lemma all_fake_pd_caps_in_pd:
  "well_formed spec \<Longrightarrow>
   {(obj_id, slot). pd_at obj_id spec \<and> fake_pt_cap_at (obj_id, slot) spec} =
   {cap_ref. fake_pt_cap_at cap_ref spec}"
   apply rule
    apply clarsimp
   apply (clarsimp simp: cap_at_def opt_cap_def)
   apply (erule (2) well_formed_fake_pt_cap_in_pd)
   done

lemma is_fake_pt_cap_cap_has_object [simp]:
  "is_fake_pt_cap cap \<Longrightarrow> cap_has_object cap"
  by (clarsimp simp: cap_has_object_def is_fake_pt_cap_def split: cdl_cap.splits)

lemma is_fake_vm_cap_cap_has_object [simp]:
  "is_fake_vm_cap cap \<Longrightarrow> cap_has_object cap"
  by (clarsimp simp: cap_has_object_def is_fake_vm_cap_def split: cdl_cap.splits)

lemma cap_has_object_simps [simp]:
  "cap_has_object (EndpointCap obj_id badge rights)"
  "cap_has_object (NotificationCap obj_id badge rights)"
  "cap_has_object (ReplyCap obj_id)"
  "cap_has_object (MasterReplyCap obj_id)"
  "cap_has_object (CNodeCap obj_id guard gs sz)"
  "cap_has_object (TcbCap obj_id)"
  "cap_has_object (PendingSyncSendCap obj_id badge a b c)"
  "cap_has_object (PendingSyncRecvCap obj_id d)"
  "cap_has_object (PendingNtfnRecvCap obj_id)"
  "cap_has_object (FrameCap dev obj_id rights sz type maddr)"
  "cap_has_object (PageTableCap obj_id cdl_frame_cap_type maddr)"
  "cap_has_object (PageDirectoryCap obj_id cdl_frame_cap_type asid)"
  "cap_has_object (AsidPoolCap obj_id as)"
  "cap_has_object (IOPortsCap obj_id io)"
  "cap_has_object (IOSpaceCap obj_id)"
  "cap_has_object (IOPageTableCap obj_id)"
  "cap_has_object (ZombieCap obj_id)"
  by (clarsimp simp: cap_has_object_def)+

lemma fake_pt_cap_at_conversion:
  "well_formed spec
  \<Longrightarrow> (\<And>* obj_id \<in> {obj_id. pd_at obj_id spec}.
       \<And>* slot\<in>set (slots_of_list spec obj_id).
        if fake_pt_cap_at (obj_id, slot) spec then f (cap_ref_object (obj_id, slot) spec) else \<box>) =
      (\<And>* obj_id \<in> {obj_id. \<exists>cap. cap \<in> all_caps spec \<and> is_fake_pt_cap cap \<and> obj_id = cap_object cap}.
           f obj_id)"
  apply (subst sep.prod.Sigma, clarsimp+)
  apply (subst sep_map_set_conj_restrict_predicate)
   apply (rule finite_SigmaI, clarsimp+)
  apply (subst fake_cap_rewrite, assumption)
  apply (frule well_formed_pt_cap_bij)
  apply (clarsimp simp: bij_betw_def)
  apply (rule sep_map_set_conj_reindex_cong [where f="\<lambda>cap_ref. cap_ref_object cap_ref spec", symmetric])
    apply (subst (asm) all_fake_pd_caps_in_pd, simp+)
   apply (fastforce simp: image_def cap_ref_object_def cap_at_def all_caps_def)
  apply (clarsimp)
  done

lemma empty_cap_map_shiftr_NullCap:
  "empty_cap_map 12 (unat ((vaddr::word32) >> 20)) = Some NullCap"
  apply (clarsimp simp:empty_cap_map_def)
  apply (rule unat_less_helper)
  apply simp
  apply (subst word32_less_sub_le[where n= 12,simplified,symmetric])
   apply (simp add:word_bits_def)
  apply (simp add: shiftr_shiftr
    le_mask_iff[where n = 12,unfolded mask_def,simplified])
  apply (rule shiftr_eq_0)
  apply simp
  done

lemma object_slot_initialised_lookup:
  "\<lbrakk>t spec_ptr = Some ptr; opt_cap (spec_ptr,slot) spec = Some cap\<rbrakk>
  \<Longrightarrow> object_slot_initialised spec t spec_ptr slot = ((ptr,slot)\<mapsto>c (cap_transform t cap))"
  apply (clarsimp simp:object_slot_initialised_def opt_object_def
    object_initialised_general_def opt_cap_def slots_of_def
    split:option.splits)
  apply (intro ext iffI)
   apply (drule sep_map_c_sep_map_s[where cap = "cap_transform t cap"])
    apply (simp add:spec2s_def update_slots_def object_slots_def
      split:cdl_object.splits)
   apply simp
  apply (subst (asm) sep_map_c_def2)
  apply (clarsimp simp:spec2s_def)
  apply (clarsimp simp:sep_map_s_def
    sep_map_general_def object_to_sep_state_def)
  apply (rule ext)
  apply (clarsimp simp:object_project_def
    object_slots_object_clean)
  apply (clarsimp simp:update_slots_def
    object_slots_def split:cdl_object.splits)
  done

(*****************************
 * Mapping page directories. *
 *****************************)

lemma seL4_PageTable_Map_object_initialised_sep:
  "\<lbrace>\<guillemotleft>object_slot_empty spec t pd_id (unat (shiftr vaddr 20)) \<and>*
   (si_cnode_id, offset sel4_pt si_cnode_size) \<mapsto>c (PageTableCap pt_ptr Real None) \<and>*
   (si_cnode_id, offset sel4_pd si_cnode_size) \<mapsto>c (PageDirectoryCap pd_ptr Real None) \<and>*
    si_objects \<and>* R\<guillemotright> and K(
    well_formed spec \<and>
    pd_at pd_id spec \<and>
    opt_cap (pd_id, unat (shiftr vaddr 20)) spec = Some (PageTableCap pt_id Fake None) \<and>

    (* Some word assumption *)
    sel4_pt < 2 ^ si_cnode_size \<and>
    sel4_pd < 2 ^ si_cnode_size \<and>

    (* Following are some assumptions about t *)
    t pd_id = Some pd_ptr \<and>
    t pt_id = Some pt_ptr)\<rbrace>
     seL4_PageTable_Map sel4_pt sel4_pd vaddr vmattribs
  \<lbrace>\<lambda>rv. \<guillemotleft>object_slot_initialised spec t pd_id (unat (shiftr vaddr 20)) \<and>*
   (si_cnode_id, offset sel4_pt si_cnode_size) \<mapsto>c (PageTableCap pt_ptr Real None) \<and>*
   (si_cnode_id, offset sel4_pd si_cnode_size) \<mapsto>c (PageDirectoryCap pd_ptr Real None) \<and>*
    si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (clarsimp simp:object_slot_initialised_lookup cap_transform_def cap_object_simps update_cap_object_def)
  apply (clarsimp simp: object_at_def is_pd_def)
  apply (clarsimp split:cdl_object.split_asm)
  apply (rule hoare_chain)
    apply (rule seL4_Page_Table_Map[where cnode_cap = si_cspace_cap
      and root_size = si_cnode_size and ptr = pt_ptr and pd_ptr = pd_ptr])
          apply (simp add:word_bits_def guard_equal_si_cspace_cap)+
  prefer 2
   apply (clarsimp simp:si_objects_def sep_conj_assoc sep_state_projection2_def)
   apply (clarsimp simp: object_slot_initialised_def cdl_lookup_pd_slot_def
     object_fields_empty_def object_initialised_general_def)
    apply (clarsimp simp:root_tcb_def sep_conj_assoc update_slots_def)
    apply (sep_cancel)+
  apply (clarsimp simp: object_slot_empty_def object_fields_empty_def
                        object_initialised_general_def si_objects_def cdl_lookup_pd_slot_def
                        root_tcb_def update_slots_def)
  apply sep_cancel+
  apply (drule sep_map_c_sep_map_s)
  apply (simp add:object_default_state_def object_type_def default_object_def object_slots_def)
   apply (simp add:empty_cap_map_shiftr_NullCap)
   apply (erule sep_any_imp)
  done

lemma valid_vm_rights_rw:
 "validate_vm_rights ({AllowRead, AllowWrite} \<inter> rights) = validate_vm_rights rights"
  apply (rule set_eqI)
  apply (clarsimp simp:validate_vm_rights_def)
  done

lemma seL4_Section_Map_object_initialised_sep:
  "\<lbrace>\<guillemotleft>object_slot_empty spec t spec_pd_ptr (unat (vaddr >> 20)) \<and>*
    (si_cnode_id , offset sel4_section si_cnode_size) \<mapsto>c (FrameCap dev section_ptr {AllowRead, AllowWrite} n Real None) \<and>*
    (si_cnode_id , offset sel4_pd si_cnode_size) \<mapsto>c (PageDirectoryCap pd_ptr Real None) \<and>*
    si_objects \<and>* R\<guillemotright> and
  K(pd_at spec_pd_ptr spec \<and>
    opt_cap (spec_pd_ptr,unat (vaddr >> 20)) spec
      = Some (FrameCap False spec_section_ptr (validate_vm_rights rights) n Fake None) \<and>

    sel4_section < 2 ^ si_cnode_size \<and>
    sel4_pd < 2 ^ si_cnode_size \<and>
    (n = 20 \<or> n = 24) \<and>

 (* object ids mapping *)
    t spec_pd_ptr = Some pd_ptr \<and>
    t spec_section_ptr = Some section_ptr)\<rbrace>
     seL4_Page_Map sel4_section sel4_pd vaddr rights vmattribs
   \<lbrace>\<lambda>rv. \<guillemotleft>object_slot_initialised spec t spec_pd_ptr (unat (vaddr >> 20)) \<and>*
   (si_cnode_id , offset sel4_section si_cnode_size) \<mapsto>c (FrameCap dev section_ptr {AllowRead, AllowWrite} n Real None) \<and>*
   (si_cnode_id , offset sel4_pd si_cnode_size) \<mapsto>c (PageDirectoryCap pd_ptr Real None) \<and>*
   si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (clarsimp simp:object_slot_initialised_lookup cap_transform_def cap_object_simps
    update_cap_object_def update_cap_objects_def valid_vm_rights_rw)
  apply (clarsimp simp: object_at_def is_pd_def)
  apply (clarsimp simp: cap_type_def split:cdl_object.split_asm)
  apply (rule hoare_chain)
    apply (rule seL4_Section_Map_wp[where cnode_cap = si_cspace_cap
      and root_size = si_cnode_size and frame_ptr = section_ptr and rights = "{AllowRead, AllowWrite}"])
          apply (simp add:word_bits_def guard_equal_si_cspace_cap)+
  prefer 2
   apply (clarsimp simp: object_slot_initialised_def cdl_lookup_pd_slot_def
     object_fields_empty_def object_initialised_general_def)
   apply (clarsimp simp:si_objects_def sep_conj_assoc sep_state_projection2_def)
   apply (clarsimp simp:root_tcb_def sep_conj_assoc update_slots_def valid_vm_rights_rw)
   apply (sep_erule_concl refl_imp)+
   apply (assumption)
  apply (clarsimp simp: object_slot_empty_def object_fields_empty_def
    object_initialised_general_def si_objects_def cdl_lookup_pd_slot_def
    root_tcb_def update_slots_def)
  apply sep_cancel+
  apply (drule sep_map_c_sep_map_s)
  apply (simp add:object_default_state_def object_type_def
    default_object_def object_slots_def)
   apply (simp add:empty_cap_map_shiftr_NullCap)
  apply (erule sep_any_imp)
  done

lemma assert_opt_validI:
  assumes w: "\<And>a. r = Some a \<Longrightarrow> \<lbrace>P\<rbrace> f a \<lbrace>Q\<rbrace>"
  shows "\<lbrace>P\<rbrace> (assert_opt r) >>= f \<lbrace>Q\<rbrace>"
  using w
  by (clarsimp simp:assert_opt_def split:option.split)

lemma well_formed_cap_obj_match_frame:
  "\<lbrakk> well_formed spec;
     cdl_objects spec ptr = Some (Frame frame);
     opt_cap cap_ref spec = Some cap;
     cap_has_object cap;
     cap_object cap = ptr\<rbrakk>
  \<Longrightarrow> \<exists>is_real dev. cap = FrameCap dev ptr (validate_vm_rights (cap_rights cap)) (cdl_frame_size_bits frame) is_real None"
  apply (case_tac cap_ref, clarsimp)
  apply (frule (1) well_formed_well_formed_cap', simp)
  apply (frule (3) well_formed_types_match)
  apply (fastforce simp: well_formed_cap_def object_type_def cap_type_def cap_object_def cap_has_object_def
                         cap_rights_def validate_vm_rights_def vm_read_write_def  vm_read_only_def
                  split: cdl_cap.splits)
   done

lemma well_formed_cap_obj_match_pt:
  "\<lbrakk>well_formed spec; pt_at (cap_object cap) spec;
   opt_cap cap_ref spec = Some cap;
   cap_has_object cap\<rbrakk>
  \<Longrightarrow> \<exists>is_real. cap = PageTableCap (cap_object cap) is_real None"
  apply (case_tac cap_ref, clarsimp)
  apply (frule (1) well_formed_well_formed_cap', simp)
  apply (frule (2) well_formed_cap_object, clarsimp)
  apply (frule (3) well_formed_types_match)
  apply (clarsimp simp: well_formed_cap_def object_type_def cap_type_def cap_object_def
                        object_at_def is_pt_def
                 split: cdl_object.splits cdl_cap.splits)
  done

lemma sep_caps_at_split: "a \<in> A \<Longrightarrow>
  si_caps_at t orig_caps spec dev A = (
  si_cap_at t orig_caps spec dev a \<and>* si_caps_at t orig_caps spec dev (A - {a}))"
  apply (simp add:si_caps_at_def)
  apply (subst sep.prod.union_disjoint [where A = "{a}", simplified, symmetric])
   apply simp
  apply (simp add:insert_absorb)
  done

lemma map_page_in_pd_wp:
  "\<lbrakk>well_formed spec; pd_at spec_pd_ptr spec\<rbrakk>
    \<Longrightarrow>
    \<lbrace>\<guillemotleft>object_slot_empty spec t spec_pd_ptr (unat (shiftr vaddr 20)) \<and>*
      si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} \<and>*
      si_objects \<and>* R\<guillemotright> and
      K ((pt_at spec_pt_section_ptr spec \<longrightarrow>
          opt_cap (spec_pd_ptr, unat (shiftr vaddr 20)) spec = Some (PageTableCap spec_pt_section_ptr Fake None)) \<and>
         (frame_at spec_pt_section_ptr spec \<longrightarrow>
             (\<exists>n. (n = 20 \<or> n = 24) \<and>
                   opt_cap (spec_pd_ptr, unat (shiftr vaddr 20)) spec =
                   Some (FrameCap False spec_pt_section_ptr (validate_vm_rights rights) n Fake None))))\<rbrace>
    map_page spec orig_caps spec_pt_section_ptr spec_pd_ptr rights vaddr
    \<lbrace>\<lambda>_. \<guillemotleft>object_slot_initialised spec t spec_pd_ptr (unat (shiftr vaddr 20)) \<and>*
          si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} \<and>*
          si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (clarsimp simp: map_page_def dest!:domE)
  apply (frule (1) object_at_real_object_at)
  apply (intro assert_opt_validI)
  apply (subgoal_tac "spec_pd_ptr \<in> {obj_id. real_object_at obj_id spec}")
   apply (subst sep_caps_at_split [where t = t and orig_caps = orig_caps and spec = spec and
          a = spec_pd_ptr and A = "{obj_id. real_object_at obj_id spec}"], simp)+
   apply clarsimp
   apply (intro conjI impI)
    apply (clarsimp simp: object_at_def is_pt_def is_frame_def
                   split: cdl_object.split_asm)
    apply (frule (1) object_at_real_object_at [where obj_id=spec_pt_section_ptr])
    apply (subgoal_tac "spec_pt_section_ptr \<in> {obj_id. real_object_at obj_id spec} - {spec_pd_ptr}")
     apply (subst sep_caps_at_split [where t = t and orig_caps = orig_caps and spec = spec and
                  a = spec_pt_section_ptr and A = "{obj_id. real_object_at obj_id spec} - {spec_pd_ptr}"], assumption)+
     apply (rule hoare_name_pre_state)
     apply (clarsimp simp: si_cap_at_def sep_conj_exists)
     apply (rule hoare_pre)
      apply wp
      apply (rule hoare_strengthen_post [OF seL4_Section_Map_object_initialised_sep[where t = t]], simp+)
      apply (clarsimp simp:object_at_def is_frame_def is_pd_def)
      apply (simp split:cdl_object.split_asm add:object_type_def)
      apply (simp add:default_cap_def)
      apply (drule(2) well_formed_cap_obj_match_frame)
        apply (simp add: cap_has_object_def)
       apply (simp add: cap_object_simps)
      apply (clarsimp simp: offset_slot_si_cnode_size' sep_conj_assoc)
      apply sep_solve
     apply (clarsimp simp:object_at_def is_frame_def is_pd_def)
     apply (simp split:cdl_object.split_asm add:object_type_def)
     apply (simp add:default_cap_def)
     apply (drule(2) well_formed_cap_obj_match_frame)
       apply (simp add: cap_has_object_def)
      apply (simp add:cap_object_simps)
     apply (clarsimp simp:offset_slot_si_cnode_size')
     apply (rule conjI)
      apply sep_solve
     apply fastforce
    apply (clarsimp simp: object_at_def opt_object_def object_type_is_object)
   apply (frule (1) object_at_real_object_at [where obj_id=spec_pt_section_ptr])
   apply (subgoal_tac "spec_pt_section_ptr \<in> {obj_id. real_object_at obj_id spec} - {spec_pd_ptr}")
    apply (subst sep_caps_at_split [where t = t and orig_caps = orig_caps and spec = spec and
                 a = spec_pt_section_ptr], assumption)+
    apply (rule hoare_name_pre_state)
    apply (clarsimp simp:si_cap_at_def sep_conj_exists)
    apply (rule hoare_pre)
     apply wp
     apply (rule hoare_strengthen_post [OF seL4_PageTable_Map_object_initialised_sep [where t = t]], simp+)
     apply (clarsimp simp:object_at_def is_frame_def is_pd_def is_pt_def)
     apply (simp split:cdl_object.split_asm add:object_type_def)
     apply (simp add:default_cap_def offset_slot_si_cnode_size')
     apply (clarsimp simp:sep_conj_assoc)
     apply sep_solve
    apply (clarsimp simp:object_at_def is_frame_def is_pd_def is_pt_def)
    apply (simp split:cdl_object.split_asm add:object_type_def)
    apply (simp add:default_cap_def offset_slot_si_cnode_size')
    apply (rule conjI)
     apply sep_solve
    apply fastforce
   apply (clarsimp simp: object_at_def opt_object_def object_type_is_object)
  apply (clarsimp simp:object_at_def)
  done

lemma well_formed_frame_in_pt:
  "\<lbrakk>well_formed spec; opt_cap (pt, pt_slot) spec = Some frame_cap; frame_cap \<noteq> NullCap; pt_at pt spec\<rbrakk>
  \<Longrightarrow> \<exists>sz. cap_type frame_cap = Some (FrameType sz) \<and>
           (sz = 12 \<or> sz = 16) \<and>
           is_fake_vm_cap frame_cap"
  apply (clarsimp simp: well_formed_def object_at_def)
  apply (drule_tac x = pt in spec)
  apply (clarsimp simp: well_formed_vspace_def opt_cap_def slots_of_def opt_object_def
                 split: option.split_asm)
  done

lemma well_formed_frame_in_pd:
  "\<lbrakk>well_formed spec; opt_cap (pd, pt_slot) spec = Some frame_cap; pd_at pd spec; is_frame_cap frame_cap \<rbrakk> \<Longrightarrow>
  (\<exists>sz. cap_type frame_cap = Some (FrameType sz) \<and> (sz = 20 \<or> sz = 24)) \<and> is_fake_vm_cap frame_cap \<and> \<not> is_device_cap frame_cap"
  apply (clarsimp simp: well_formed_def object_at_def)
  apply (drule_tac x = pd in spec)
  apply (clarsimp simp: well_formed_vspace_def opt_cap_def slots_of_def opt_object_def
                 split: option.split_asm)
  apply (drule_tac x = pt_slot in spec)
  apply (drule_tac x = frame_cap in spec)
  apply (clarsimp simp: is_fake_pt_cap_def cap_type_def
                 split: cdl_cap.splits)
  apply (clarsimp simp: cap_at_def opt_cap_def slots_of_def opt_object_def
              simp del: split_paired_All)
  apply (drule_tac x = pd in spec)
  apply (drule_tac x = pt_slot in spec)
  apply fastforce
  done

lemma map_page_directory_slot_wp:
  "\<lbrace>\<guillemotleft>object_slot_empty spec t spec_pd_ptr slot \<and>*
     si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} \<and>*
     si_objects \<and>* R\<guillemotright> and K(
     well_formed spec \<and>
    slot < 0x1000 \<and>
    pd_at spec_pd_ptr spec)\<rbrace>
    map_page_directory_slot spec orig_caps spec_pd_ptr slot
    \<lbrace>\<lambda>_. \<guillemotleft>object_slot_initialised spec t spec_pd_ptr slot \<and>*
         si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} \<and>*
         si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (clarsimp simp: map_page_directory_slot_def)
  apply (rule assert_opt_validI)
  apply (rule hoare_name_pre_state)
  apply wp
   apply (rule hoare_strengthen_post[OF map_page_in_pd_wp[where t = t]], simp+)
   apply (simp add:pt_size_def small_frame_size_def)
   apply (subst (asm) shiftl_shiftr_id)
     apply simp+
    apply (rule word_of_nat_less)
    apply (clarsimp simp:si_cap_at_def sep_conj_exists si_cnode_size_def)
   apply (simp add: unat_of_nat_eq)
  apply (clarsimp simp:pt_size_def small_frame_size_def)
  apply (intro conjI impI)
     apply (simp add:shiftl_shiftr_id word_of_nat_less unat_of_nat_eq)
    apply (simp add:shiftl_shiftr_id word_of_nat_less unat_of_nat_eq si_cnode_size_def)
    apply (frule (2) well_formed_cap_obj_match_pt)
     apply (frule (3) well_formed_pd)
     apply (clarsimp simp: cap_has_object_def cap_type_def is_fake_pt_cap_def split: cdl_cap.splits)
    apply (frule well_formed_pt_cap_is_fake_pt_cap)
       apply simp+
     apply (case_tac "cap_object a",clarsimp)
    apply (clarsimp simp:is_fake_pt_cap_def split:cdl_cap.splits)
    apply (case_tac is_real,simp+)[1]
   apply (simp add:shiftl_shiftr_id word_of_nat_less unat_of_nat_eq si_cnode_size_def)
   apply (clarsimp simp: object_at_def is_frame_def)
   apply (clarsimp split: cdl_object.split_asm)
   apply (frule (2) well_formed_cap_obj_match_frame)
     apply (frule (1) well_formed_pd)
       apply (clarsimp simp: object_at_def)
      apply assumption
     apply (clarsimp simp: cap_has_object_def cap_type_def is_fake_pt_cap_def split: cdl_cap.splits)
    apply clarsimp
   apply (drule well_formed_frame_in_pd)
      apply simp+
     apply (simp add:object_at_def)
    apply (case_tac a,simp_all)
    apply clarsimp
   apply (clarsimp simp:is_fake_vm_cap_def split:cdl_cap.split_asm cdl_frame_cap_type.split_asm)
  apply (frule object_slot_empty_initialised_NullCap [where obj_id=spec_pd_ptr and slot=slot and t=t])
    apply (clarsimp simp: object_at_def object_type_is_object)
   apply simp
  apply simp
  done

lemma well_formed_pd_slot_limited:
  "\<lbrakk>well_formed spec;pd_at obj_id spec; slots_of obj_id spec slot = Some cap\<rbrakk>
   \<Longrightarrow> slot < 4096"
  apply (clarsimp simp:well_formed_def object_at_def)
  apply (drule_tac x = obj_id in spec)
  apply (clarsimp simp: is_pd_def object_type_simps object_default_state_def slots_of_def,
              simp add: default_object_def object_type_simps opt_object_def object_slots_def empty_cap_map_def
                 split: cdl_object.split_asm option.split_asm)
  apply fastforce
  done

lemma well_formed_pt_slot_limited:
  "\<lbrakk>well_formed spec;pt_at obj_id spec; slots_of obj_id spec slot = Some cap\<rbrakk>
   \<Longrightarrow> slot < 256"
  apply (clarsimp simp:well_formed_def object_at_def)
  apply (drule_tac x = obj_id in spec)
  apply (clarsimp simp: is_pt_def object_type_simps object_default_state_def slots_of_def,
              simp add: default_object_def object_type_simps opt_object_def object_slots_def empty_cap_map_def
                 split: cdl_object.split_asm option.split_asm)
  apply fastforce
  done


lemma map_map_page_directory_slot_wp':
  "\<lbrace>\<guillemotleft>object_slots_empty spec t obj_id \<and>*
     si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} \<and>*
     si_objects \<and>* R\<guillemotright> and K(
  well_formed spec \<and> pd_at obj_id spec)\<rbrace>
    mapM_x (map_page_directory_slot spec orig_caps obj_id)
           (slots_of_list spec obj_id)
    \<lbrace>\<lambda>_. \<guillemotleft>object_slots_initialised spec t obj_id \<and>*
          si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} \<and>*
          si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (subst object_slots_empty_decomp, simp+)
  apply (subst object_slots_initialised_decomp, simp+)
  apply (subst object_empty_slots_empty_initialised, simp)
  apply (simp add:sep_conj_assoc)
  apply (rule mapM_x_set_sep' [where I = "object_empty_slots_initialised spec t obj_id \<and>*
                                          si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} \<and>*
                                          si_objects"
                                and xs = "slots_of_list spec obj_id", unfolded sep_conj_assoc])
    apply clarsimp
   apply clarsimp
  apply (wp sep_wp: map_page_directory_slot_wp [where t=t])
  apply (clarsimp simp: well_formed_pd_slot_limited)
  apply sep_solve
  done

lemma object_fields_empty_initialised_pd:
  "\<lbrakk>well_formed spec; pd_at obj_id spec\<rbrakk> \<Longrightarrow>
   object_fields_empty spec t obj_id = object_fields_initialised spec t obj_id"
  apply (clarsimp simp: object_at_def object_type_is_object)
  apply (frule (1) well_formed_object_slots)
  apply (clarsimp simp: object_fields_empty_def object_fields_initialised_def
                        object_initialised_general_def object_at_def object_type_is_object)
  apply (subst sep_map_f_object_size_bits_pd, simp+)
  done

lemma object_fields_empty_initialised_pt:
  "\<lbrakk>well_formed spec; pt_at obj_id spec\<rbrakk> \<Longrightarrow>
   object_fields_empty spec t obj_id = object_fields_initialised spec t obj_id"
  apply (clarsimp simp: object_at_def object_type_is_object)
  apply (frule (1) well_formed_object_slots)
  apply (clarsimp simp: object_fields_empty_def object_fields_initialised_def
                        object_initialised_general_def object_at_def object_type_is_object)
  apply (subst sep_map_f_object_size_bits_pt, simp+)
  done

(* MoveMe *)
lemma object_default_state_frame [simp]:
  "is_frame object \<Longrightarrow> object_default_state object = object"
  by (clarsimp simp: object_default_state_def default_object_def
                     object_type_is_object object_type_def
              split: cdl_object.splits)

(* MoveMe *)
lemma spec2s_frame [simp]:
  "is_frame object \<Longrightarrow> spec2s t object = object"
  by (clarsimp simp: object_type_is_object object_type_def
              split: cdl_object.splits)

(* MoveMe *)
lemma object_empty_initialised_frame:
  "frame_at obj_id spec \<Longrightarrow>
   object_empty spec t obj_id = object_initialised spec t obj_id"
  by (clarsimp simp: object_empty_def object_initialised_def object_initialised_general_def object_at_def)


lemma map_object_empty_initialised_frame:
  "\<And>* map (object_empty spec t) [obj_id\<leftarrow>obj_ids . frame_at obj_id spec] =
   \<And>* map (object_initialised spec t) [obj_id\<leftarrow>obj_ids . frame_at obj_id spec]"
  apply (rule map_sep_list_conj_cong)
  apply (clarsimp simp: object_empty_initialised_frame)
  done

lemma map_map_page_directory_slot_wp:
  "\<lbrace>\<guillemotleft>object_empty spec t obj_id \<and>*
     si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} \<and>*
     si_objects \<and>* R\<guillemotright> and K(
     well_formed spec \<and> pd_at obj_id spec)\<rbrace>
    mapM_x (map_page_directory_slot spec orig_caps obj_id)
           (slots_of_list spec obj_id)
   \<lbrace>\<lambda>_.
    \<guillemotleft>object_initialised spec t obj_id \<and>*
     si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} \<and>*
     si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_gen_asm)
  apply clarsimp
  apply (subst object_empty_decomp)
  apply (subst object_initialised_decomp)
  apply (subst object_fields_empty_initialised_pd, assumption+)
  apply (simp add: sep_conj_assoc)
  apply (wp sep_wp: map_map_page_directory_slot_wp' [where t=t])
  apply clarsimp
  apply sep_solve
  done

lemma set_asid_rewrite:
  "\<lbrakk>pd_at obj_id spec;
    cdl_objects spec obj_id = Some pd;
    orig_caps obj_id = Some pd_offset;
    pd_offset < 2 ^ si_cnode_size;
    t obj_id = Some kobj_id\<rbrakk> \<Longrightarrow>
   ((si_cnode_id, unat pd_offset) \<mapsto>c default_cap (object_type pd) {kobj_id} (object_size_bits pd) dev \<and>*
    si_objects \<and>* R)
    =
   ((si_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
     si_tcb_id \<mapsto>f Tcb (obj_tcb root_tcb) \<and>*
    (si_cnode_id, unat seL4_CapInitThreadASIDPool) \<mapsto>c AsidPoolCap si_asidpool_id si_asidpool_base \<and>*
    (si_cnode_id, unat pd_offset) \<mapsto>c PageDirectoryCap kobj_id Real None \<and>*
     si_asidpool_id \<mapsto>f AsidPool empty_asid \<and>*
    (\<And>*off \<in> {off. off < 2 ^ asid_low_bits}. (si_asidpool_id, off) \<mapsto>c -) \<and>*
     si_cnode_id \<mapsto>f CNode (empty_cnode si_cnode_size) \<and>*
    (si_tcb_id, tcb_cspace_slot) \<mapsto>c si_cspace_cap \<and>*
    (si_cnode_id, unat seL4_CapInitThreadCNode) \<mapsto>c si_cnode_cap \<and>*
    (si_cnode_id, unat seL4_CapIRQControl) \<mapsto>c IrqControlCap \<and>* R)"
  apply (clarsimp simp: si_objects_def si_asid_def si_cap_at_def)
  apply (clarsimp simp: sep_conj_assoc sep_conj_exists object_at_object_type default_cap_def)
  apply (rule ext, rule)
   apply sep_solve
  apply sep_solve
  done

lemma set_asid_wp:
   "\<lbrace>\<guillemotleft>si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} \<and>*
      si_objects \<and>* R\<guillemotright> and K(
     well_formed spec \<and>
     pd_at obj_id spec)\<rbrace>
    set_asid spec orig_caps obj_id
    \<lbrace>\<lambda>rv. \<guillemotleft>si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} \<and>*
           si_objects \<and>* R\<guillemotright>\<rbrace>"
  including no_pre
  apply (rule hoare_gen_asm, clarsimp)
  apply (frule (1) object_at_real_object_at)
  apply (rule valid_si_caps_at_si_cap_at [where obj_id=obj_id], clarsimp+)
  apply (clarsimp simp: si_cap_at_def sep_conj_assoc sep_conj_exists)
  apply (subst ex_conj_increase)+
  apply (rule hoare_ex_wp)+
  apply (rename_tac kobj_id)
  apply (rule hoare_grab_asm)+
  apply (wp, simp_all)
  apply (clarsimp simp: set_asid_def)
  apply (subst set_asid_rewrite, assumption+)
  apply (clarsimp simp: sep_conj_assoc)
  apply (wp add: hoare_drop_imps
            sep_wp: seL4_ASIDPool_Assign_wp [where
                    cnode_cap = si_cspace_cap and
                    cnode_id = si_cnode_id and
                    root_size = si_cnode_size and
                    tcb = "obj_tcb root_tcb" and
                    p = si_asidpool_id and
                    base = si_asidpool_base and
                    pd = "the (t obj_id)"],
        (simp add: guard_equal_si_cspace_cap')+)
  apply (subst offset_slot_si_cnode_size', simp)+
  apply (simp add: si_objects_def si_asid_def default_cap_def object_at_object_type)
  apply sep_solve
  done

lemma map_map_page_directory_wp':
  "\<lbrace>\<guillemotleft>(\<And>* pd_id \<in> {pd_id. pd_at pd_id spec}. object_empty spec t pd_id) \<and>*
      si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} \<and>*
      si_objects \<and>* R\<guillemotright> and
    K(well_formed spec \<and> set obj_ids = dom (cdl_objects spec) \<and> distinct obj_ids)\<rbrace>
    mapM_x (map_page_directory spec orig_caps)
           [obj\<leftarrow>obj_ids. pd_at obj spec]
    \<lbrace>\<lambda>rv. \<guillemotleft>(\<And>* pd_id \<in> {pd_id. pd_at pd_id spec}. object_initialised spec t pd_id) \<and>*
          si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} \<and>*
          si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (rule mapM_x_set_sep' [where I = "si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} \<and>* si_objects",
         simplified sep_conj_assoc])
    apply simp
   apply (fastforce simp: object_at_def)
  apply (clarsimp simp: map_page_directory_def)
  apply (wp map_map_page_directory_slot_wp, simp)
  done

lemma map_map_page_directory_wp:
  "\<lbrace>\<guillemotleft>(\<And>* pt_id \<in> {pt_id. pt_at pt_id spec}. object_empty spec t pt_id) \<and>*
     (\<And>* pd_id \<in> {pd_id. pd_at pd_id spec}. object_empty spec t pd_id) \<and>*
      si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} \<and>*
      si_objects \<and>* R\<guillemotright> and K(
      well_formed spec \<and> set obj_ids = dom (cdl_objects spec) \<and> distinct obj_ids)\<rbrace>
    mapM_x (map_page_directory spec orig_caps)
           [obj\<leftarrow>obj_ids . pd_at obj spec]
    \<lbrace>\<lambda>_.
     \<guillemotleft>(\<And>* pt_id \<in> {pt_id. pt_at pt_id spec}. object_empty spec t pt_id) \<and>*
      (\<And>* pd_id \<in> {pd_id. pd_at pd_id spec}. object_initialised spec t pd_id) \<and>*
      si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} \<and>*
      si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (wp sep_wp: map_map_page_directory_wp' [where t=t], simp)
  apply sep_solve
  done

lemma fake_pt_cap_rewrite:
  "well_formed spec \<Longrightarrow>
   {obj_id. pt_at obj_id spec \<and>
           (\<exists>cap. cap \<in> all_caps spec \<and> is_fake_pt_cap cap \<and> obj_id = cap_object cap)} =
   {obj_id. \<exists>cap. cap \<in> all_caps spec \<and> is_fake_pt_cap cap \<and> obj_id = cap_object cap}"
  apply rule
   apply clarsimp
  apply (clarsimp simp: all_caps_def)
  apply (frule (1) well_formed_cap_object, simp)
  apply clarsimp
  apply (drule (2) well_formed_types_match, clarsimp)
  apply (fastforce simp: object_at_def object_type_is_object is_fake_pt_cap_is_pt_cap)
  done

lemma cap_transform_empty_cap_map [simp]:
  "cap_transform t \<circ>\<^sub>M empty_cap_map n = empty_cap_map n"
  apply (rule ext)
  apply (clarsimp simp: cap_transform_def empty_cap_map_def update_cap_object_def)
  done

lemma spec2s_default_tcb [simp]:
  "spec2s t (Tcb (default_tcb domain)) = Tcb (default_tcb domain)"
  apply (clarsimp simp: spec2s_def object_slots_def update_slots_def default_tcb_def cap_transform_def)
  apply (rule ext)
  apply clarsimp
  done

(* MoveMe *)
lemma object_default_state_spec2s:
  "object_default_state obj = obj \<Longrightarrow> spec2s t obj = obj"
  apply (clarsimp simp: object_default_state_def2 split: cdl_object.splits)
      apply (metis spec2s_default_tcb)
     apply (clarsimp simp: spec2s_def object_slots_def empty_cnode_def empty_irq_node_def
                           cdl_cnode.splits)+
  done

lemma object_empty_initialised_default_state:
  "object_at (\<lambda>obj. object_default_state obj = obj) obj_id spec \<Longrightarrow>
  object_empty spec t obj_id = object_initialised spec t obj_id"
  apply (clarsimp simp: object_empty_def object_initialised_def object_initialised_general_def object_at_def)
  apply (frule object_default_state_spec2s [where t=t])
  apply clarsimp
  done

lemma not_object_at:
  "\<exists>object. cdl_objects spec obj_id = Some object \<Longrightarrow>
  (\<not> object_at P obj_id spec) = object_at (\<lambda>obj. \<not>P obj) obj_id spec "
  apply (clarsimp simp: object_at_def)
  done

(* Each pt is either mapped in to a pd, or it is in a default state. *)
lemma well_formed_pt_default_or_mapped:
  "\<lbrakk>well_formed spec; pt_at obj_id spec;
    \<forall>cap. is_fake_pt_cap cap \<longrightarrow>
          cap \<in> all_caps spec \<longrightarrow> obj_id \<noteq> cap_object cap\<rbrakk> \<Longrightarrow>
   object_at (\<lambda>obj. object_default_state obj = obj) obj_id spec"
  apply (rule ccontr)
  apply (subst (asm) not_object_at)
   apply (clarsimp simp: object_at_def)
  apply (frule (2) well_formed_cap_to_non_empty_pt)
  apply clarsimp
  apply (clarsimp simp: object_at_def, rename_tac pt pd)
  apply (case_tac "cap \<noteq> NullCap")
   apply (frule (3) well_formed_types_match [symmetric])
   apply (clarsimp simp: object_type_is_object)
   apply (frule_tac obj_id=pd_id in well_formed_pt_cap_is_fake_pt_cap, assumption+)
     apply (clarsimp simp: object_at_def object_type_is_object)
    apply simp
   apply (erule_tac x=cap in allE)
   apply (fastforce simp: all_caps_def)
  apply (clarsimp)
  done

lemma object_empty_initialised_pt:
  "\<lbrakk>well_formed spec; pt_at obj_id spec;
   \<forall>cap. is_fake_pt_cap cap \<longrightarrow> cap \<in> all_caps spec \<longrightarrow> obj_id \<noteq> cap_object cap\<rbrakk>
   \<Longrightarrow>
   object_empty spec t obj_id = object_initialised spec t obj_id"
  apply (rule object_empty_initialised_default_state)
  apply (erule (2) well_formed_pt_default_or_mapped)
  done

lemma map_object_empty_initialised_pt:
  "well_formed spec \<Longrightarrow>
   (\<And>* obj_id \<in> {obj_id. pt_at obj_id spec \<and> (\<forall>cap. is_fake_pt_cap cap \<longrightarrow>
                                                cap \<in> all_caps spec \<longrightarrow>
                                                obj_id \<noteq> cap_object cap)}.
          (object_empty spec t) obj_id)
     =
   (\<And>* obj_id \<in> {obj_id. pt_at obj_id spec \<and> (\<forall>cap. is_fake_pt_cap cap \<longrightarrow>
                                                cap \<in> all_caps spec \<longrightarrow>
                                                obj_id \<noteq> cap_object cap)}.
           (object_initialised spec t) obj_id)"
  apply (rule sep.prod.cong, clarsimp)
  apply (clarsimp simp: object_empty_initialised_pt)
  done


lemma well_formed_pt_cap_pt_at:
  "\<lbrakk>well_formed spec; opt_cap cap_ref spec = Some cap; is_fake_pt_cap cap\<rbrakk>
  \<Longrightarrow> pt_at (cap_object cap) spec"
  apply (case_tac cap_ref, clarsimp)
  apply (frule (1) well_formed_cap_object, simp, clarsimp)
  apply (frule (2) well_formed_types_match, simp)
  apply (clarsimp simp: is_fake_pt_cap_is_pt_cap object_at_def object_type_is_object)
  done

lemma pt_slot_compute:
  "pt_slot < 2 ^ 8
  \<Longrightarrow> unat (((of_nat pd_slot << pt_size + small_frame_size) + (of_nat pt_slot << small_frame_size) >> 12) && (0xFF::word32))
  = pt_slot"
  apply (clarsimp simp:pt_size_def small_frame_size_def)
  apply (rule of_nat_inverse)
   apply (drule of_nat_mono_maybe[rotated,where 'a=32])
    apply simp
   apply word_bitwise
    apply simp
  apply simp
  done

lemma cdl_lookup_pd_slot_compute:
  "\<lbrakk>pd_slot < 2 ^ 12;pt_slot < 2 ^ 8\<rbrakk> \<Longrightarrow>
   cdl_lookup_pd_slot pd_ptr
   (((of_nat pd_slot::word32) << pt_size + small_frame_size) + (of_nat pt_slot << small_frame_size))
  = (pd_ptr ,(of_nat pd_slot))"
  apply (clarsimp simp: cdl_lookup_pd_slot_def pt_size_def small_frame_size_def)
  apply (rule of_nat_inverse)
   apply (drule of_nat_mono_maybe[rotated,where 'a=32],simp)+
   apply (subst is_aligned_add_or [where n=20])
     apply (rule is_aligned_shiftl, simp)
    apply (rule shiftl_less_t2n, simp+)
   apply (clarsimp simp: shiftr_over_or_dist)
   apply (subst shiftl_shiftr_id, simp+)
   apply (clarsimp simp: limited_and_simps)
   apply (subst le_mask_iff [THEN iffD1])
    apply (clarsimp simp: mask_def plus_one_helper)
   apply clarsimp
  apply (clarsimp simp: word_bits_len_of)
  done

lemma well_formed_frame_valid:
  "\<lbrakk>well_formed spec; opt_cap cap_ref spec = Some (FrameCap dev ptr seta sz real_type option)\<rbrakk>
   \<Longrightarrow> validate_vm_rights seta = seta"
  apply (case_tac cap_ref, clarsimp)
  apply (frule (1) well_formed_well_formed_cap', simp)
  apply (fastforce simp: well_formed_cap_def vm_read_write_def
                         vm_read_only_def validate_vm_rights_def)
  done

lemma empty_cap_map_NullCap:
  "pt_slot < 2 ^n \<Longrightarrow> empty_cap_map n pt_slot = Some NullCap"
  by (simp add:empty_cap_map_def)

(* FIXME: current cdl_init does not consider device caps *)
lemma well_formed_opt_cap_nondevice:
  "\<lbrakk>well_formed spec; opt_cap slot spec = Some cap\<rbrakk> \<Longrightarrow> \<not> is_device_cap cap"
  by (simp add: well_formed_def cap_at_def del: split_paired_All)

(***********************
 * Mapping page tables *
 ***********************)
lemma map_page_in_pt_sep:
  "\<lbrace>\<guillemotleft>object_slot_empty spec t (cap_object pt_cap) pt_slot \<and>*
     object_slot_initialised spec t obj_id pd_slot \<and>*
     si_caps_at t orig_caps spec False {obj_id. real_object_at obj_id spec} \<and>*
     si_objects \<and>* R\<guillemotright> and K(
    well_formed spec \<and>
    pd_at obj_id spec \<and>
    opt_cap (obj_id, pd_slot) spec = Some pt_cap \<and>
    is_fake_pt_cap pt_cap \<and>
    opt_cap (cap_object pt_cap, pt_slot) spec = Some frame_cap \<and>
    frame_cap \<noteq> NullCap \<and>
    pt_slot < 2 ^ 8 \<and>
    pd_slot < 2 ^ 12)\<rbrace>
     map_page spec orig_caps (cap_object frame_cap)
                obj_id (cap_rights frame_cap)
                ((of_nat pd_slot << pt_size + small_frame_size) +
                 (of_nat pt_slot << small_frame_size))
  \<lbrace>\<lambda>_. \<guillemotleft>object_slot_initialised spec t (cap_object pt_cap) pt_slot \<and>*
         object_slot_initialised spec t obj_id pd_slot \<and>*
         si_caps_at t orig_caps spec False {obj_id. real_object_at obj_id spec} \<and>*
         si_objects \<and>*
         R\<guillemotright>\<rbrace>"
  including no_pre
  apply (rule hoare_gen_asm, clarsimp)
  apply (simp add:map_page_def)
  apply (rule assert_opt_validI)+
  apply (frule (2) well_formed_pt_cap_pt_at[where cap = pt_cap])
  apply (frule well_formed_frame_in_pt[where pt = "(cap_object pt_cap)"])
    apply (simp+)[3]
  apply (case_tac "frame_at (cap_object frame_cap) spec")
   apply clarsimp

  apply (frule (1) object_at_real_object_at)
  apply (frule (1) object_at_real_object_at [where obj_id = "cap_object pt_cap"])
  apply (frule (1) object_at_real_object_at [where obj_id = "cap_object frame_cap"])
   apply (intro conjI)
    apply (clarsimp simp: object_at_def is_pt_def is_frame_def,
           simp split:cdl_object.splits)
   apply clarsimp
   apply wp
   apply (clarsimp simp: object_at_def)
   apply (subst sep_caps_at_split[where a = obj_id
                                    and A = "{obj_id. real_object_at obj_id spec}"], fastforce)+
   apply (subst sep_caps_at_split[where a = "cap_object pt_cap"
                                    and A = "{obj_id. real_object_at obj_id spec} - {obj_id}"],
          fastforce simp: object_type_is_object)+
   apply (subst sep_caps_at_split[where a = "cap_object frame_cap"
                                    and A = "{obj_id. real_object_at obj_id spec} - {obj_id} - {cap_object pt_cap}"],
          fastforce simp: object_type_is_object)+
   apply (rule hoare_name_pre_state)
   apply (clarsimp simp: si_cap_at_def sep_conj_exists is_pd_def is_pt_def is_frame_def
                  split: cdl_object.split_asm)
   apply (clarsimp simp: object_type_def default_cap_def)
   apply (clarsimp simp: object_slot_initialised_lookup)
   apply (clarsimp simp: cap_type_def is_fake_vm_cap_def cap_object_simps
                         cap_transform_def is_fake_pt_cap_def
                  split: cdl_cap.split_asm cdl_frame_cap_type.split_asm)
   apply (frule(1) well_formed_opt_cap_nondevice)
   apply (rule hoare_pre)
    apply (rule hoare_strengthen_post)
     apply (rule_tac pd_ptr = kobj_id in seL4_Page_Map_wp[where cnode_cap = si_cspace_cap
       and root_size = si_cnode_size and dev = False
       and rights = "{AllowRead, AllowWrite}"])
          apply (simp add:word_bits_def guard_equal_si_cspace_cap)+
    apply (simp add:si_objects_def sep_conj_assoc pt_slot_compute)
        apply (clarsimp simp: update_cap_object_def valid_vm_rights_rw cap_rights_def)
    apply (sep_select 9, sep_cancel)
    apply (sep_select 9,sep_cancel)
    apply (clarsimp simp: update_cap_object_def valid_vm_rights_rw cap_rights_def)
    apply (frule well_formed_frame_valid[rotated])
     apply simp+
    apply (subst sep_map_c_asid_simp)
    apply sep_cancel
    apply (simp add: cdl_lookup_pd_slot_compute)
    apply (subst sep_map_c_asid_simp(2))
    apply sep_cancel
    apply (simp add:offset_slot_si_cnode_size')
    apply sep_cancel
    apply (simp add:root_tcb_def update_slots_def)
    apply (sep_select 4,sep_cancel)
    apply (sep_select 4,sep_cancel)
    apply (drule (2)  well_formed_cap_obj_match_frame, simp)
     apply (simp add:cap_object_simps)
    apply clarsimp
    apply (sep_select 2,sep_solve)
   apply (clarsimp simp: si_objects_def root_tcb_def update_slots_def
                         offset_slot_si_cnode_size' pt_slot_compute cdl_lookup_pd_slot_compute)
   apply (drule (2) well_formed_cap_obj_match_frame, simp+)
    apply (simp add:cap_object_simps)
   apply (clarsimp simp:update_cap_object_def)
   apply (subst (asm) sep_map_c_asid_simp(2))
   apply (clarsimp simp: object_slot_empty_def object_fields_empty_def object_initialised_general_def)
   apply (sep_drule sep_map_c_sep_map_s)
    apply (simp add: object_default_state_def object_type_def
                     default_object_def object_slots_def empty_cap_map_NullCap)
   apply (simp add: fun_upd_def)
   apply sep_solve
  apply clarsimp
  apply (clarsimp simp: is_pt_def object_at_def
                 split: cdl_object.split_asm)
  apply (drule (2) well_formed_types_match [where cap = frame_cap])
   apply simp
  apply (simp add:object_type_simps)
  done

lemma map_page_table_slot_wp:
  "\<lbrace>\<guillemotleft>object_slot_empty spec t (cap_object page_cap) pt_slot \<and>*
     object_slot_initialised spec t obj_id pd_slot \<and>*
     si_caps_at t orig_caps spec False {obj_id. real_object_at obj_id spec} \<and>*
     si_objects \<and>* R\<guillemotright> and K(
    well_formed spec \<and>
    pd_at obj_id spec \<and>
    is_fake_pt_cap page_cap \<and>
    pt_slot < 256 \<and>
    pd_slot < 2 ^ 12 \<and>
    opt_cap (obj_id, pd_slot) spec = Some page_cap \<and>
    opt_cap (cap_object page_cap, pt_slot) spec = Some frame_cap)\<rbrace>
    map_page_table_slot spec orig_caps obj_id
                       (cap_object page_cap)
                       (of_nat pd_slot << pt_size + small_frame_size)
                        pt_slot
    \<lbrace>\<lambda>_. \<guillemotleft>object_slot_initialised spec t (cap_object page_cap) pt_slot \<and>*
         object_slot_initialised spec t obj_id pd_slot \<and>*
         si_caps_at t orig_caps spec False {obj_id. real_object_at obj_id spec} \<and>*
         si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (clarsimp simp: map_page_table_slot_def)
  apply (wp map_page_in_pt_sep)
  apply clarsimp
  apply (subst (asm) object_slot_empty_initialised_NullCap, simp_all)
  apply (clarsimp simp: object_at_def is_fake_pt_cap_def is_pd_def is_tcb_def)
  apply (simp split:cdl_object.splits cdl_cap.splits)
  apply (drule well_formed_types_match[where cap = page_cap],simp_all)
  apply (simp add:object_type_def)
  done

lemma map_page_table_slots_wp'':
  "\<lbrakk>well_formed spec;
    pd_at obj_id spec;
    fake_pt_cap_at (obj_id, pd_slot) spec;
    opt_cap (obj_id, pd_slot) spec = Some page_cap\<rbrakk> \<Longrightarrow>
   \<lbrace>\<guillemotleft>object_slots_empty spec t (cap_ref_object (obj_id, pd_slot) spec) \<and>*
     object_slot_initialised spec t obj_id pd_slot \<and>*
     si_caps_at t orig_caps spec False {obj_id. real_object_at obj_id spec} \<and>*
     si_objects \<and>* R\<guillemotright>\<rbrace>
   mapM_x (map_page_table_slot spec orig_caps obj_id
                              (cap_object page_cap)
                              (of_nat pd_slot << pt_size + small_frame_size))
          (slots_of_list spec (cap_object page_cap))
   \<lbrace>\<lambda>_. \<guillemotleft>object_slots_initialised spec t (cap_ref_object (obj_id, pd_slot) spec) \<and>*
         object_slot_initialised spec t obj_id pd_slot \<and>*
         si_caps_at t orig_caps spec False {obj_id. real_object_at obj_id spec} \<and>*
         si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (frule well_formed_distinct_slots_of_list [where obj_id="cap_ref_object (obj_id, pd_slot) spec"])
  apply (frule well_formed_finite [where obj_id="cap_ref_object (obj_id, pd_slot) spec"])
  apply (subst object_slots_empty_decomp, simp+)
  apply (subst object_slots_initialised_decomp, clarsimp+)
  apply (subst object_empty_slots_empty_initialised, simp)
  apply (clarsimp simp: sep_conj_assoc cap_ref_object_def cap_at_def)
  apply (rule mapM_x_set_sep' [where I = "object_empty_slots_initialised spec t (cap_object page_cap) \<and>*
                                          object_slot_initialised spec t obj_id pd_slot \<and>*
                                          si_caps_at t orig_caps spec False {obj_id. real_object_at obj_id spec} \<and>*
                                          si_objects", unfolded sep_conj_assoc], simp, clarsimp)
  apply (frule is_fake_pt_cap_is_pt_cap)
  apply (frule (1) well_formed_cap_object, clarsimp)
  apply clarsimp
  apply (frule (2) well_formed_types_match[where cap = page_cap], clarsimp)
  apply (clarsimp simp: opt_cap_def)
  apply (frule (2) well_formed_pd_slot_limited [where slot=pd_slot])
  apply (frule well_formed_pt_slot_limited [where obj_id="cap_object page_cap"],
         clarsimp simp: object_type_object_at, assumption)
  apply (wp sep_wp: map_page_table_slot_wp [where t=t])
  apply clarsimp
  apply (rule conjI)
   apply sep_solve
  apply (simp add: opt_cap_def)
  done

lemma map_page_table_slots_wp':
  "\<lbrace>\<guillemotleft>object_empty spec t (cap_ref_object (obj_id, pd_slot) spec) \<and>*
     object_slot_initialised spec t obj_id pd_slot \<and>*
     si_caps_at t orig_caps spec False {obj_id. real_object_at obj_id spec} \<and>*
     si_objects \<and>*
     R\<guillemotright> and K(
     well_formed spec \<and>
     pd_at obj_id spec \<and> fake_pt_cap_at (obj_id, pd_slot) spec \<and>
     opt_cap (obj_id, pd_slot) spec = Some page_cap)\<rbrace>
   mapM_x (map_page_table_slot spec orig_caps obj_id
                               (cap_object page_cap)
                               (of_nat pd_slot << pt_size + small_frame_size))
          (slots_of_list spec (cap_object page_cap))
   \<lbrace>\<lambda>_. \<guillemotleft>object_initialised spec t (cap_ref_object (obj_id, pd_slot) spec) \<and>*
         object_slot_initialised spec t obj_id pd_slot \<and>*
         si_caps_at t orig_caps spec False {obj_id. real_object_at obj_id spec} \<and>*
         si_objects \<and>*
   R\<guillemotright>\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (subst object_empty_decomp)
  apply (subst object_initialised_decomp)
  apply (subst object_fields_empty_initialised_pt, simp+)
   apply (clarsimp simp: cap_at_def)
   apply (frule (1) well_formed_cap_object, clarsimp+)
   apply (drule (2) well_formed_types_match, clarsimp)
   apply (drule is_fake_pt_cap_is_pt_cap)
   apply (clarsimp simp: object_at_def object_type_is_object cap_ref_object_def
                  split: cdl_cap.splits)
  apply (clarsimp simp: sep_conj_assoc)
  apply (wp sep_wp: map_page_table_slots_wp'' [where t=t])
  apply sep_solve
  done

lemma map_page_table_slots_wp:
  "\<lbrace>\<guillemotleft>object_empty spec t (cap_ref_object (obj_id, pd_slot) spec) \<and>*
         object_slot_initialised spec t obj_id pd_slot \<and>*
     si_caps_at t orig_caps spec False {obj_id. real_object_at obj_id spec} \<and>*
     si_objects \<and>* R\<guillemotright> and K(
    well_formed spec \<and>
    pd_at obj_id spec \<and>
    cdl_objects spec obj_id = Some obj \<and>
    fake_pt_cap_at (obj_id, pd_slot) spec)\<rbrace>
   map_page_table_slots spec orig_caps obj_id pd_slot
    \<lbrace>\<lambda>_. \<guillemotleft>object_initialised spec t (cap_ref_object (obj_id, pd_slot) spec) \<and>*
         object_slot_initialised spec t obj_id pd_slot \<and>*
         si_caps_at t orig_caps spec False {obj_id. real_object_at obj_id spec} \<and>*
         si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (clarsimp simp: map_page_table_slots_def)
  apply (wp map_page_table_slots_wp', simp+)
  done

lemma object_initialised_slot_initialised:
  "\<lbrakk> well_formed spec; slot \<in> dom (slots_of obj_id spec) \<rbrakk>
  \<Longrightarrow> \<exists>F. object_initialised spec t obj_id
       = (object_slot_initialised spec t obj_id slot \<and>* F)"
  apply (frule well_formed_finite [where obj_id=obj_id])
  apply (simp add: object_initialised_decomp_total)
  apply (subst sep.prod.remove, assumption+)
  by (metis sep_conj_assoc sep_conj_left_commute)

lemma map_page_directory_page_tables_wp:
  "\<lbrace>\<guillemotleft>(\<And>* slot\<in>set (slots_of_list spec obj_id).
                     if fake_pt_cap_at (obj_id, slot) spec
                     then (object_empty spec t (cap_ref_object (obj_id, slot) spec))
                     else \<box>)  \<and>*
     object_initialised spec t obj_id \<and>*
     si_caps_at t orig_caps spec False {obj_id. real_object_at obj_id spec} \<and>*
     si_objects \<and>* R\<guillemotright> and
    K(well_formed spec \<and> pd_at obj_id spec)\<rbrace>
   map_page_directory_page_tables spec orig_caps obj_id
   \<lbrace>\<lambda>_. \<guillemotleft>(\<And>* slot\<in>set (slots_of_list spec obj_id).
                     if fake_pt_cap_at (obj_id, slot) spec
                     then (object_initialised spec t (cap_ref_object (obj_id, slot) spec))
                     else \<box>) \<and>*
     object_initialised spec t obj_id \<and>*
     si_caps_at t orig_caps spec False {obj_id. real_object_at obj_id spec} \<and>*
     si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_gen_asm, clarsimp)
  apply (frule well_formed_distinct_slots_of_list [where obj_id=obj_id])
  apply (clarsimp simp: map_page_directory_page_tables_def)
  apply (rule mapM_x_set_sep'[where I="object_initialised spec t obj_id \<and>*
                                       si_caps_at t orig_caps spec False {obj_id. real_object_at obj_id spec} \<and>*
                                       si_objects",
                                    unfolded sep_conj_assoc,simplified], simp+)
  apply clarsimp
  apply (rule conjI)
   apply (clarsimp simp:sep_conj_assoc)
   apply (frule object_initialised_slot_initialised[where obj_id = obj_id and t = t])
    apply fastforce
   apply (clarsimp simp:sep_conj_assoc)
   apply (frule slots_of_cdl_objects, clarsimp)
   apply (wp sep_wp: map_page_table_slots_wp [where t=t], simp+)
   apply (rule conjI)
    apply sep_solve
   apply simp
  apply (clarsimp simp: map_page_table_slots_def)
  apply wp
  apply clarsimp
  done

lemma map_map_page_directory_page_tables_wp'':
  "\<lbrace>\<guillemotleft>(\<And>* obj_id \<in> {obj_id. pt_at obj_id spec \<and>
                           (\<exists>cap. cap \<in> all_caps spec \<and> is_fake_pt_cap cap \<and>
                                  obj_id = cap_object cap)}.
         object_empty spec t obj_id) \<and>*
      (\<And>* obj_id \<in> {obj_id. pd_at obj_id spec}. object_initialised spec t obj_id) \<and>*
      si_caps_at t orig_caps spec False {obj_id. real_object_at obj_id spec} \<and>*
      si_objects \<and>* R\<guillemotright> and
    K (well_formed spec \<and> set obj_ids = dom (cdl_objects spec) \<and> distinct obj_ids)\<rbrace>
   mapM_x (map_page_directory_page_tables spec orig_caps)
          [obj\<leftarrow>obj_ids . pd_at obj spec]
   \<lbrace>\<lambda>_. \<guillemotleft>(\<And>* obj_id \<in> {obj_id. pt_at obj_id spec \<and>
                           (\<exists>cap. cap \<in> all_caps spec \<and> is_fake_pt_cap cap \<and>
                                  obj_id = cap_object cap)}.
         object_initialised spec t obj_id) \<and>*
         (\<And>* obj_id \<in> {obj_id. pd_at obj_id spec}. object_initialised spec t obj_id) \<and>*
         si_caps_at t orig_caps spec False {obj_id. real_object_at obj_id spec} \<and>*
         si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_gen_asm, clarsimp)
  apply (subst fake_pt_cap_rewrite, assumption)+
  apply (subst fake_pt_cap_at_conversion [symmetric], assumption)+
  apply simp
  apply (rule mapM_x_set_sep'[where
              I = "(\<And>* obj_id \<in> {obj_id. pd_at obj_id spec}.
                        object_initialised spec t obj_id) \<and>*
                   si_caps_at t orig_caps spec False {obj_id. real_object_at obj_id spec} \<and>* si_objects",
              unfolded sep_conj_assoc,simplified])
    apply simp
   apply simp
  apply simp
  apply (wp sep_wp: map_page_directory_page_tables_wp [where t=t])
  apply simp
  apply (subst (asm) sep.prod.remove, simp, simp)
  apply (subst sep.prod.remove, simp, simp)
  apply clarsimp
  apply sep_solve
  done

lemma map_map_page_directory_page_tables_wp:
  "\<lbrace>\<guillemotleft>(\<And>* obj_id \<in> {obj_id. pt_at obj_id spec}. object_empty spec t obj_id) \<and>*
     (\<And>* obj_id \<in> {obj_id. pd_at obj_id spec}. object_initialised spec t obj_id) \<and>*
     si_caps_at t orig_caps spec False {obj_id. real_object_at obj_id spec} \<and>*
     si_objects \<and>* R\<guillemotright> and
     K(well_formed spec \<and> set obj_ids = dom (cdl_objects spec) \<and> distinct obj_ids)\<rbrace>
   mapM_x (map_page_directory_page_tables spec orig_caps)
          [obj\<leftarrow>obj_ids. pd_at obj spec]
   \<lbrace>\<lambda>_. \<guillemotleft>(\<And>* obj_id \<in> {obj_id. pt_at obj_id spec}. object_initialised spec t obj_id) \<and>*
         (\<And>* obj_id \<in> {obj_id. pd_at obj_id spec}. object_initialised spec t obj_id) \<and>*
         si_caps_at t orig_caps spec False {obj_id. real_object_at obj_id spec} \<and>*
         si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_gen_asm, clarsimp)
  apply (subst sep_map_set_conj_restrict [where xs="{obj_id. pt_at obj_id spec}" and
         t="\<lambda>obj_id. \<exists>cap. cap \<in> all_caps spec \<and> is_fake_pt_cap cap \<and> obj_id = cap_object cap"], simp)+
  apply (clarsimp simp: sep_conj_assoc)
  apply (subst map_object_empty_initialised_pt, assumption)
  apply (wp sep_wp: map_map_page_directory_page_tables_wp'' [where t=t], simp+)
  apply sep_solve
  done

lemma init_vspace_sep:
  "\<lbrace>\<guillemotleft>objects_empty spec t {obj_id. table_at obj_id spec} \<and>*
     si_caps_at t orig_caps spec False {obj_id. real_object_at obj_id spec} \<and>*
     si_objects \<and>* R\<guillemotright> and
     K(well_formed spec \<and> set obj_ids = dom (cdl_objects spec) \<and> distinct obj_ids)\<rbrace>
   init_vspace spec orig_caps obj_ids
   \<lbrace>\<lambda>_. \<guillemotleft>objects_initialised spec t {obj_id. table_at obj_id spec} \<and>*
         si_caps_at t orig_caps spec False {obj_id. real_object_at obj_id spec} \<and>*
         si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_gen_asm, clarsimp)
  apply (clarsimp simp: objects_empty_def objects_initialised_def)
  apply (subst sep_map_set_conj_set_disjoint, simp+,
         clarsimp simp: object_at_def object_type_is_object)+
  apply (clarsimp simp: init_vspace_def sep_conj_assoc)
  apply (wp sep_wp: map_map_page_directory_page_tables_wp [where t=t]
                    map_map_page_directory_wp [where t=t], simp+)
  apply (sep_safe+, sep_solve)
  done

lemma init_pd_asids_sep:
  "\<lbrace>\<guillemotleft>si_caps_at t orig_caps spec False {obj_id. real_object_at obj_id spec} \<and>*
     si_objects \<and>* R\<guillemotright> and K(well_formed spec)\<rbrace>
   init_pd_asids spec orig_caps obj_ids
   \<lbrace>\<lambda>_. \<guillemotleft>si_caps_at t orig_caps spec False {obj_id. real_object_at obj_id spec} \<and>*
         si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (clarsimp simp: init_pd_asids_def)
  apply (rule mapM_x_wp', clarsimp)
  apply (wp sep_wp: set_asid_wp [where t=t], simp+, sep_solve)
  done

end

end
