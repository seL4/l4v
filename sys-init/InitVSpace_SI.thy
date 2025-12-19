(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory
  InitVSpace_SI
imports
  "DSpecProofs.Invocation_DP"
  "DSpecProofs.Arch_DP"
  ObjectInitialised_SI
  RootTask_SI
  SysInit_SI
  DuplicateCaps_SI
  Sep_Algebra.Sep_Fold_Cancel
  Sep_Algebra.Sep_Util
  "HOL-Library.Multiset"
  Mapped_Separating_Conjunction
  AInvs.Rights_AI
  Lib.Guess_ExI
begin

context begin interpretation Arch . (*FIXME: arch-split*)

declare
  object_at_predicate_lift[simp]
  opt_cap_object_slot[simp]
  opt_cap_object_slotE[elim]
  slots_of_object_slot[simp]
  slots_of_object_slotE[elim]
  object_at_cdl_objects[simp]

(* Abbreviations for commonly appearing expressions involving virtual addresses and slots *)
(* TODO: use pd_size, pt_size, small_frame_size instead of magic numbers *)
abbreviation
  "pd_slot_of_pt_vaddr vaddr \<equiv> vaddr >> 20 :: machine_word"
abbreviation
  "pt_slot_of_vaddr vaddr \<equiv> (vaddr >> 12) && 0xFF :: machine_word"
abbreviation
  "pt_vaddr_of_pd_slot pd_slot \<equiv> of_nat pd_slot << 20 :: machine_word"
abbreviation
  "frame_vaddr_of_slots pd_slot pt_slot \<equiv>
    pt_vaddr_of_pd_slot pd_slot + (of_nat pt_slot << small_frame_size) :: machine_word"

(* FIXME: MOVE (Lib) *)
lemma singleton_eq[simp]: "(\<lambda>v. if v = x then Some y else None) = [x \<mapsto> y]"
  by (clarsimp simp: fun_upd_def)

lemma map_add_simp [simp]: "(\<lambda>p. if p = p' then Some v else f p) = f ++ [p' \<mapsto> v] "
  by (intro ext iffI; clarsimp simp: map_add_def split: option.splits)

lemma list_all_spec: "list_all P xs \<Longrightarrow> x \<in> set xs \<Longrightarrow> P x"
  by (simp add: list_all_iff)
(* /MOVE *)

lemma empty_cap_map_shiftr_NullCap:
  "empty_cap_map 12 (unat ((vaddr :: word32) >> 20)) = Some NullCap"
  apply (clarsimp simp:empty_cap_map_def)
  apply (rule unat_less_helper)
  apply simp
  apply (subst word32_less_sub_le[where n=12, simplified, symmetric])
   apply (simp add: word_bits_def)
  apply (simp add: shiftr_shiftr le_mask_iff[where n=12, unfolded mask_def, simplified])
  apply (rule shiftr_eq_0)
  apply simp
  done

lemma object_slot_initialised_lookup:
  "\<lbrakk>t spec_ptr = Some ptr; opt_cap (spec_ptr,slot) spec = Some cap\<rbrakk>
   \<Longrightarrow> object_slot_initialised spec t spec_ptr slot = (ptr, slot) \<mapsto>c cap_transform t cap"
  apply (clarsimp simp: object_slot_initialised_def
                        object_initialised_general_def opt_cap_def slots_of_def
                 split: option.splits)
  apply (intro ext iffI)
   apply (drule sep_map_c_sep_map_s[where cap = "cap_transform t cap"])
    apply (simp add: spec2s_def update_slots_def object_slots_def split: cdl_object.splits)
   apply simp
  apply (subst (asm) sep_map_c_def2)
  apply (clarsimp simp: spec2s_def sep_map_s_def sep_map_general_def object_to_sep_state_def)
  apply (rule ext)
  apply (clarsimp simp: object_project_def object_slots_object_clean)
  apply (clarsimp simp: update_slots_def object_slots_def split: cdl_object.splits)
  done

lemma seL4_Page_Map_object_initialised_sep:
  "\<lbrace>\<guillemotleft>object_slot_initialised spec t spec_pd_ptr (unat (vaddr >> 20)) \<and>*
    object_slot_empty spec t (cap_object pt_cap) (unat (pt_slot_of_vaddr vaddr)) \<and>*
    (si_cnode_id , offset sel4_page si_cnode_size) \<mapsto>c
      FrameCap dev page_ptr vm_read_write n Real None \<and>*
    (si_cnode_id , offset sel4_pd si_cnode_size) \<mapsto>c (PageDirectoryCap pd_ptr Real None) \<and>*
    si_objects \<and>* R\<guillemotright> and
  K(pd_at spec_pd_ptr spec \<and>
    opt_cap (spec_pd_ptr, unat (vaddr >> 20)) spec = Some pt_cap \<and>
    pt_cap = PageTableCap spec_pt_ptr Fake None \<and>
    opt_cap (spec_pt_ptr, unat (pt_slot_of_vaddr vaddr)) spec
      = Some (FrameCap False spec_page_ptr (validate_vm_rights rights) n Fake None) \<and>
    cdl_objects spec (cap_object pt_cap) = Some cap_obj \<and>
    sel4_page < 2 ^ si_cnode_size \<and>
    vaddr = frame_vaddr_of_slots (unat (pd_slot_of_pt_vaddr vaddr))
                                 (unat (pt_slot_of_vaddr vaddr)) \<and>
    sel4_pd < 2 ^ si_cnode_size \<and>
    object_slots (object_default_state cap_obj) (unat (pt_slot_of_vaddr vaddr)) = Some cap_slots \<and>
    (n = 12 \<or> n = 16) \<and>
    t (cap_object pt_cap) = Some pt_ptr \<and>
    t spec_pd_ptr = Some pd_ptr \<and>
    t spec_page_ptr = Some page_ptr)\<rbrace>
     seL4_Page_Map sel4_page sel4_pd vaddr rights vmattribs
   \<lbrace>\<lambda>rv. \<guillemotleft>object_slot_initialised spec t spec_pd_ptr (unat (vaddr >> 20)) \<and>*
   object_slot_initialised spec t (cap_object pt_cap) (unat (pt_slot_of_vaddr vaddr)) \<and>*
   (si_cnode_id , offset sel4_page si_cnode_size) \<mapsto>c
      FrameCap dev page_ptr vm_read_write n Real None \<and>*
   (si_cnode_id , offset sel4_pd si_cnode_size) \<mapsto>c (PageDirectoryCap pd_ptr Real None) \<and>*
   si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (wp sep_wp: seL4_Page_Map_wp[where n=n and cnode_cap= si_cspace_cap and
                                           root_size = si_cnode_size and pt_ptr = pt_ptr])
          apply fastforce+
     apply (simp add: word_bits_def guard_equal_si_cspace_cap)+
  apply clarsimp
  apply sep_cancel+
  apply (clarsimp simp: si_objects_def sep_conj_assoc sep_state_projection2_def root_tcb_def
                        update_slots_def)
  apply sep_cancel+
  apply (clarsimp simp: object_slot_empty_def object_fields_empty_def
                        object_initialised_general_def si_objects_def cdl_lookup_pd_slot_def
                        root_tcb_def update_slots_def validate_vm_rights_inter_rw)
  apply (sep_drule sep_map_c_sep_map_s)
   apply (clarsimp, fastforce)
  apply (clarsimp simp: object_slot_initialised_lookup shiftr_less cap_object_def)
  apply sep_solve
  done

lemma seL4_PageTable_Map_object_initialised_sep:
  "\<lbrace>\<guillemotleft>object_slot_empty spec t pd_id (unat (shiftr vaddr 20)) \<and>*
   (si_cnode_id, offset sel4_pt si_cnode_size) \<mapsto>c (PageTableCap pt_ptr Real None) \<and>*
   (si_cnode_id, offset sel4_pd si_cnode_size) \<mapsto>c (PageDirectoryCap pd_ptr Real None) \<and>*
    si_objects \<and>* R\<guillemotright> and K(
    well_formed spec \<and>
    pd_at pd_id spec \<and>
    opt_cap (pd_id, unat (shiftr vaddr 20)) spec = Some (PageTableCap pt_id Fake None) \<and>

    sel4_pt < 2 ^ si_cnode_size \<and>
    sel4_pd < 2 ^ si_cnode_size \<and>

    t pd_id = Some pd_ptr \<and>
    t pt_id = Some pt_ptr)\<rbrace>
     seL4_PageTable_Map sel4_pt sel4_pd vaddr vmattribs
  \<lbrace>\<lambda>rv. \<guillemotleft>object_slot_initialised spec t pd_id (unat (shiftr vaddr 20)) \<and>*
   (si_cnode_id, offset sel4_pt si_cnode_size) \<mapsto>c (PageTableCap pt_ptr Real None) \<and>*
   (si_cnode_id, offset sel4_pd si_cnode_size) \<mapsto>c (PageDirectoryCap pd_ptr Real None) \<and>*
    si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (clarsimp simp: object_slot_initialised_lookup cap_transform_def
                        update_cap_object_def object_at_def is_pd_def)
  apply (clarsimp split:cdl_object.split_asm)
  apply (wp add: seL4_Page_Table_Map[where cnode_cap = si_cspace_cap
                                       and root_size = si_cnode_size
                                       and ptr = pt_ptr
                                       and pd_ptr = pd_ptr,
                                     sep_wandise])
         apply (simp add: word_bits_def guard_equal_si_cspace_cap)+
  apply (clarsimp simp: si_objects_def  sep_state_projection2_def object_slot_empty_def
                        object_fields_empty_def object_initialised_general_def cdl_lookup_pd_slot_def
                        root_tcb_def update_slots_def)
  apply sep_cancel+
  apply (sep_drule sep_map_c_sep_map_s)
   apply (fastforce simp: object_default_state_def object_type_def default_object_def
                          object_slots_def empty_cap_map_shiftr_NullCap)
  by sep_solve

lemma assert_opt_validI:
  assumes w: "\<And>a. r = Some a \<Longrightarrow> \<lbrace>P\<rbrace> f a \<lbrace>Q\<rbrace>"
  shows "\<lbrace>P\<rbrace> (assert_opt r) >>= f \<lbrace>Q\<rbrace>"
  using w
  by (clarsimp simp:assert_opt_def split:option.split)

lemma sep_caps_at_split: "a \<in> A \<Longrightarrow>
  si_caps_at t orig_caps spec dev A = (
  si_cap_at t orig_caps spec dev a \<and>* si_caps_at t orig_caps spec dev (A - {a}))"
  apply (simp add:si_caps_at_def)
  apply (subst sep.prod.union_disjoint [where A = "{a}", simplified, symmetric])
   apply simp
  apply (simp add:insert_absorb)
  done

lemma duplicate_frame_cap_sep:
  "\<lbrace>\<guillemotleft>(si_cnode_id, unat free_cptr) \<mapsto>c NullCap \<and>*
    si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} \<and>* si_objects \<and>* R\<guillemotright> and K (
    well_formed spec \<and>
    unat free_cptr < 2 ^ si_cnode_size \<and>
    frame_at obj_id spec)\<rbrace>
      duplicate_cap spec orig_caps (obj_id, free_cptr)
  \<lbrace>\<lambda>_.
   \<guillemotleft>si_cap_at t (map_of [(obj_id, free_cptr)]) spec dev obj_id
    \<and>* si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec}
    \<and>* si_objects
    \<and>* R\<guillemotright>\<rbrace>"
  apply (wp sep_wp: duplicate_cap_sep_general[
        where free_cptr=free_cptr and
          free_cptrs="[free_cptr]" and
          obj_ids="obj_id # (sorted_list_of_set (dom (cdl_objects spec) - {obj_id}))" and
          spec=spec and
          obj_id=obj_id and
          obj_filter=frame_at])
  apply (clarsimp simp: object_at_def wf_obj_filter_frame_at, intro conjI)
   apply sep_solve
  apply fastforce
  done

lemma si_caps_at_take_2:
  "\<lbrakk>well_formed spec;
    pd_at spec_pd_ptr spec;
    frame_at spec_pt_section_ptr spec\<rbrakk>
   \<Longrightarrow> si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} =
           (si_cap_at t orig_caps spec dev spec_pd_ptr \<and>*
            si_cap_at t orig_caps spec dev spec_pt_section_ptr \<and>*
            si_caps_at t orig_caps spec dev ({obj_id. real_object_at obj_id spec} -
                                                      {spec_pd_ptr} - {spec_pt_section_ptr}))"
  apply (frule (1) object_at_real_object_at)
  apply (frule (1) object_at_real_object_at[where obj_id=spec_pt_section_ptr])
  apply (clarsimp simp: object_at_def is_pd_def is_frame_def is_pt_def split: cdl_object.split_asm)
  apply (rename_tac object obj_id, case_tac object; simp)
  by (metis cdl_object.distinct(79) insert_Diff insert_iff mem_Collect_eq option.inject
            sep_caps_at_split)

lemma si_caps_at_take_2_not_object_at:
  "\<lbrakk>well_formed spec;
    cdl_objects spec spec_pd_ptr = Some pd;
    is_pd pd;
    cdl_objects spec spec_pt_section_ptr = Some frame;
    is_frame frame\<rbrakk>
   \<Longrightarrow> si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} =
           (si_cap_at t orig_caps spec dev spec_pd_ptr \<and>*
            si_cap_at t orig_caps spec dev spec_pt_section_ptr \<and>*
            si_caps_at t orig_caps spec dev ({obj_id. real_object_at obj_id spec} -
                                                      {spec_pd_ptr} - {spec_pt_section_ptr}))"
  by (erule si_caps_at_take_2; fastforce simp: object_at_def)

lemma si_caps_at_take_2':
  "\<lbrakk>well_formed spec;
      pd_at spec_pd_ptr spec;
      pt_at spec_pt_section_ptr spec \<rbrakk>
   \<Longrightarrow> si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} =
           (si_cap_at t orig_caps spec dev spec_pd_ptr \<and>*
            si_cap_at t orig_caps spec dev spec_pt_section_ptr \<and>*
            si_caps_at t orig_caps spec dev ({obj_id. real_object_at obj_id spec} -
                                                      {spec_pd_ptr} - {spec_pt_section_ptr}))"
  apply (frule (1) object_at_real_object_at)
  apply (frule (1) object_at_real_object_at[where obj_id=spec_pt_section_ptr])
  apply (clarsimp simp: object_at_def is_pd_def is_frame_def is_pt_def split: cdl_object.split_asm)
  apply (rename_tac object obj_id, case_tac object; simp)
  by (metis cdl_object.distinct(71) insert_Diff insert_iff mem_Collect_eq option.inject
            sep_caps_at_split)

lemma frame_at_default_cap[simp]:
  "well_formed spec \<Longrightarrow>
   is_frame frame \<Longrightarrow>
   cdl_objects spec (cap_object frame_cap) = Some frame \<Longrightarrow>
   opt_cap (parent_id, slot) spec = Some frame_cap \<Longrightarrow>
   is_fake_frame_cap frame_cap \<Longrightarrow>
   t (cap_object frame_cap) = Some ptr' \<Longrightarrow>
   default_cap (object_type frame) {ptr'} (object_size_bits frame) False
     = conjure_real_frame_cap frame_cap t"
  apply (clarsimp simp: si_caps_at_take_2  si_cap_at_def object_type_is_object object_at_def
                        default_cap_def object_type_def wf_frame_cap_frame_size_bits
                        offset_slot_si_cnode_size' vm_read_write_def si_objects_def)
  apply (clarsimp simp: is_frame_def split: cdl_object.splits)
  apply (clarsimp split: cdl_cap.splits cdl_frame_cap_type.splits option.splits)
  apply (drule_tac frame=x8 in wf_frame_cap_frame_size_bits)
  by (fastforce simp: vm_read_write_def conjure_real_frame_cap_def dev_of_def)+

lemma is_frame_default_cap[simp]:
  "well_formed spec \<Longrightarrow>
   frame_at (cap_object frame_cap) spec \<Longrightarrow>
   cdl_objects spec (cap_object frame_cap) = Some obj \<Longrightarrow>
   opt_cap (parent_id, slot) spec = Some frame_cap \<Longrightarrow>
   is_fake_frame_cap frame_cap \<Longrightarrow>
   t (cap_object frame_cap) = Some ptr' \<Longrightarrow>
   default_cap (object_type obj) {ptr'} (object_size_bits obj) False
     = conjure_real_frame_cap frame_cap t"
  by (fastforce dest!: frame_at_default_cap simp: object_at_def)

lemma pt_slot_compute[simp]:
  "pt_slot < 2 ^ 8 \<Longrightarrow> unat (pt_slot_of_vaddr (frame_vaddr_of_slots pd_slot pt_slot)) = pt_slot"
  apply (clarsimp simp:pt_size_def small_frame_size_def)
  apply (rule of_nat_inverse)
   apply (drule of_nat_mono_maybe[rotated,where 'a=32])
    apply simp
   apply word_bitwise
   apply simp
  apply simp
  done

lemma pd_slot_compute_from_pt[simp]:
  "pd_slot < 2 ^ 12 \<Longrightarrow>
   pt_slot < 2 ^ 8 \<Longrightarrow>
   unat (pd_slot_of_pt_vaddr (frame_vaddr_of_slots pd_slot pt_slot)) = pd_slot"
  apply (clarsimp simp: cdl_lookup_pd_slot_def pt_size_def small_frame_size_def)
  apply (rule of_nat_inverse)
   apply (drule of_nat_mono_maybe[rotated,where 'a=32],simp)+
   apply (subst is_aligned_add_or [where n=20])
     apply (rule is_aligned_shiftl, simp)
    apply (rule shiftl_less_t2n, simp+)
   apply (clarsimp simp: shiftr_over_or_dist)
   apply (subst shiftl_shiftr_id, simp+)
   apply (clarsimp simp: shiftl_shiftr2)
   apply (subst le_mask_iff [THEN iffD1])
    apply (clarsimp simp: mask_def plus_one_helper)
   apply clarsimp
  apply (clarsimp simp: word_bits_len_of)
  done

lemma pd_slot_compute_inverse[simp]:
  "pd_slot < 2 ^ 12 \<Longrightarrow>
   unat (pd_slot_of_pt_vaddr (pt_vaddr_of_pd_slot pd_slot)) = pd_slot"
  apply (clarsimp simp: cdl_lookup_pd_slot_def pt_size_def small_frame_size_def)
  apply (rule of_nat_inverse)
   apply (drule of_nat_mono_maybe[rotated, where 'a=32], simp)+
   apply (word_bitwise, clarsimp, clarsimp)
  done

lemma object_slot_empty_translate_exists:
  "(object_slot_empty spec t pt_id pt_slot) s \<Longrightarrow>
   (object_slot_empty spec t pt_id pt_slot) s \<and> t pt_id \<noteq> None"
  by (clarsimp simp: object_slot_empty_def object_initialised_general_def)

lemma object_slot_initialised_translate_exists:
  "(object_slot_initialised spec t pt_id pt_slot) s \<Longrightarrow>
   (object_slot_initialised spec t pt_id pt_slot) s \<and> t pt_id \<noteq> None"
  by (clarsimp simp: object_slot_initialised_def object_initialised_general_def)

lemma si_cap_at_translate_exists:
 "si_cap_at t f spec dev page_id s \<Longrightarrow>
  si_cap_at t f spec dev page_id s \<and> t page_id \<noteq> None"
  by (clarsimp simp: si_cap_at_def)

lemmas translate_exists = si_cap_at_translate_exists object_slot_initialised_translate_exists
                          object_slot_empty_translate_exists

lemma si_caps_at_less_si_cnode_size:
  "(si_caps_at t orig_caps spec dev xs \<and>* R) s \<Longrightarrow>
   orig_caps ptr = Some v \<Longrightarrow>
   ptr \<in> xs \<Longrightarrow>
   v < 2 ^ si_cnode_size"
  by (clarsimp simp: sep_caps_at_split si_cap_at_def sep_conj_def)

lemma si_caps_at_less_translate_exists:
  "(si_caps_at t orig_caps spec dev xs \<and>* R) s \<Longrightarrow>
  ptr \<in> xs \<Longrightarrow>
  t ptr \<noteq> None"
  by (clarsimp simp: sep_caps_at_split si_cap_at_def sep_conj_def)

lemma map_page_wp:
  "\<lbrakk>well_formed spec; pd_at spec_pd_ptr spec\<rbrakk> \<Longrightarrow>
    \<lbrace>\<guillemotleft>object_slot_initialised spec t spec_pd_ptr (unat (vaddr >> 20)) \<and>*
      object_slot_empty spec t pt_id pt_slot \<and>*
      (si_cnode_id, unat free_cptr) \<mapsto>c NullCap \<and>*
      si_caps_at t orig_caps spec False {obj_id. real_object_at obj_id spec} \<and>*
      si_objects \<and>* R\<guillemotright> and
      K (page_cap = fake_frame_cap False page_id (validate_vm_rights rights) n \<and>
         (n = 12 \<or> n = (16 :: nat)) \<and>
         opt_cap (spec_pd_ptr, pd_slot) spec = Some pt_cap \<and>
         pt_cap = PageTableCap pt_id Fake None \<and>
         opt_cap (pt_id, pt_slot) spec = Some page_cap \<and>
         vaddr = frame_vaddr_of_slots pd_slot pt_slot \<and>
         pt_slot < 2 ^ 8 \<and>
         pd_slot < 2 ^ 12 \<and>
         the (orig_caps spec_pd_ptr) < 2 ^ si_cnode_size \<and>
         free_cptr < 2 ^ si_cnode_size)\<rbrace>
    map_page spec orig_caps page_id spec_pd_ptr rights vaddr free_cptr
    \<lbrace>\<lambda>_. \<guillemotleft>object_slot_initialised spec t spec_pd_ptr (unat (vaddr >> 20)) \<and>*
          object_slot_initialised spec t pt_id pt_slot \<and>*
          (si_cnode_id, unat free_cptr) \<mapsto>c conjure_real_frame_cap page_cap t \<and>*
          si_caps_at t orig_caps spec False {obj_id. real_object_at obj_id spec} \<and>*
          si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (frule well_formed_pt_cap_pt_at[where cap=pt_cap],
         fastforce, clarsimp simp: is_fake_pt_cap_def)
  apply (elim conjE)
  apply (clarsimp simp: map_page_def dest!: domE)
  apply (wp)
         apply (clarsimp simp: object_at_def)
         apply (wp sep_wp: seL4_Page_Map_object_initialised_sep
                             [where n=n and
                                    spec=spec and
                                    cap_obj="the (cdl_objects spec pt_id)" and
                                    spec_pd_ptr=spec_pd_ptr and
                                    pt_ptr="the (t pt_id)" and
                                    pt_cap=pt_cap and
                                    spec_page_ptr=page_id and
                                    page_ptr="the (t page_id)" and
                                    t=t and
                                    pd_ptr="the (t spec_pd_ptr)"]
                           duplicate_frame_cap_sep)+
  apply clarsimp
  apply (intro conjI, sep_cancel+, intro conjI)
          apply (sep_simp si_caps_at_take_2 si_cap_at_def)
          apply (clarsimp simp: offset_slot_si_cnode_size' vm_read_write_def
                                conjure_real_frame_cap_def dev_of_def
                                is_frame_default_cap[where frame_cap=page_cap])
          apply sep_solve
         apply (fastforce simp: object_at_def pt_size_def pt_has_slots
                         intro: object_slots_object_default_state_NullCap')+
  by (sep_map thms: translate_exists, fastforce simp: unat_less_2_si_cnode_size')+

(***********************************************************
         * Mapping a frame inside a page directory *
************************************************************)
lemma map_page_in_pd_wp:
  "\<lbrakk>well_formed spec; pd_at pd_id spec\<rbrakk> \<Longrightarrow>
    \<lbrace>\<guillemotleft>object_slot_empty spec t pd_id pd_slot \<and>*
      (si_cnode_id, unat free_cptr) \<mapsto>c NullCap \<and>*
      si_caps_at t orig_caps spec False {obj_id. real_object_at obj_id spec} \<and>*
      si_objects \<and>* R\<guillemotright> and
      K (    page_cap = fake_frame_cap False page_id (validate_vm_rights rights) n \<and>
             (n = 20 \<or> n = (24 :: nat)) \<and>
             pd_slot = unat (pd_slot_of_pt_vaddr vaddr) \<and>
             opt_cap (pd_id, pd_slot) spec = Some page_cap \<and>
             pd_slot < 2 ^ 12 \<and>
             the (orig_caps pd_id) < 2 ^ si_cnode_size \<and>
             free_cptr < 2 ^ si_cnode_size)\<rbrace>
    map_page spec orig_caps page_id pd_id rights vaddr free_cptr
    \<lbrace>\<lambda>_. \<guillemotleft>object_slot_initialised spec t pd_id pd_slot \<and>*
          (si_cnode_id, unat free_cptr) \<mapsto>c conjure_real_frame_cap page_cap t \<and>*
          si_caps_at t orig_caps spec False {obj_id. real_object_at obj_id spec} \<and>*
          si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (elim conjE)
  apply (clarsimp simp: map_page_def dest!: domE)
  apply (intro assert_opt_validI)
  apply wp
     apply (clarsimp simp: object_at_def)
     apply (wp sep_wp: seL4_Section_Map_wp[where pd_ptr="the (t pd_id)" and
                                                 frame_ptr="the (t page_id)" and
                                                 cnode_cap=si_cspace_cap and
                                                 root_size=si_cnode_size and
                                                 n=n];
            fastforce simp: word_bits_def intro!: guard_equal_si_cspace_cap)
    apply (wp sep_wp: duplicate_frame_cap_sep)+
  apply (clarsimp, intro conjI impI, clarsimp simp: si_objects_def cdl_lookup_pd_slot_def)
   apply sep_cancel+
   apply (sep_map thms: translate_exists)
   apply (sep_simp si_cap_at_def object_at_def object_slot_empty_eq)
   apply (sep_drule sep_map_c_sep_map_s)
    apply (clarsimp simp: opt_cap_def object_default_state_def is_pd_def object_type_def
                          default_object_def
                    split: cdl_object.splits)
    apply (clarsimp simp: object_slots_def empty_cap_map_def, fastforce)
   apply sep_cancel+
   apply (clarsimp simp: si_caps_at_take_2_not_object_at offset_slot_si_cnode_size' si_cap_at_def
                         frame_at_default_cap[where frame_cap=page_cap] cap_object_def
                         object_at_def conjure_real_frame_cap_def dev_of_def
                         root_tcb_def update_slots_def)
   apply sep_cancel+
   apply (fastforce simp: object_slot_initialised_lookup shiftr_less cap_object_def
                          validate_vm_rights_inter_rw)
  by (fastforce simp: unat_less_2_si_cnode_size')

(***********************************************************
      * Mapping a page table inside a page directory *
************************************************************)

lemma map_page_table_in_pd_wp:
  "\<lbrakk>well_formed spec; pd_at pd_id spec\<rbrakk> \<Longrightarrow>
    \<lbrace>\<guillemotleft>object_slot_empty spec t pd_id pd_slot \<and>*
      si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} \<and>*
      si_objects \<and>* R\<guillemotright> and
      K ((n = 20 \<or> n = 24) \<and>
         opt_cap (pd_id, pd_slot) spec = Some (PageTableCap spec_pt_section_ptr Fake None) \<and>
         pd_slot < 2 ^ 12 \<and>
         vaddr = pt_vaddr_of_pd_slot pd_slot)\<rbrace>
    map_page_table spec orig_caps spec_pt_section_ptr pd_id rights vaddr
    \<lbrace>\<lambda>_. \<guillemotleft>object_slot_initialised spec t pd_id pd_slot \<and>*
          si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} \<and>*
          si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (clarsimp simp: map_page_table_def dest!: domE)
  apply (intro assert_opt_validI)
  apply wp
    apply (clarsimp simp: object_at_def)
    apply (wp sep_wp:
              seL4_PageTable_Map_object_initialised_sep[where pt_ptr ="the (t spec_pt_section_ptr)"
                                                        and   pd_ptr ="the (t pd_id)"])+
  apply (clarsimp, intro conjI impI)
         apply sep_cancel+
         apply (sep_simp si_caps_at_take_2' si_cap_at_def offset_slot_si_cnode_size')
         apply sep_solve
        apply assumption+
  by (sep_simp si_caps_at_less_si_cnode_size[rotated 2, OF pt_at_is_real]
               si_caps_at_less_si_cnode_size[rotated 2, OF pd_at_is_real]
               si_caps_at_less_translate_exists[rotated, OF pt_at_is_real]
               si_caps_at_less_translate_exists[rotated, OF pd_at_is_real])+

(***********************************************************
              * Mapping a page table slot *
************************************************************)

lemma map_page_table_slot_wp:
  "\<lbrakk>well_formed spec; pd_at pd_id spec\<rbrakk> \<Longrightarrow>
   \<lbrace>\<guillemotleft>object_slot_initialised spec t pd_id pd_slot \<and>*
     object_slot_empty spec t (cap_object pt_cap) pt_slot \<and>*
     (si_cnode_id, unat free_cptr) \<mapsto>c NullCap \<and>*
     si_caps_at t orig_caps spec False {obj_id. real_object_at obj_id spec} \<and>*
     si_objects \<and>* R\<guillemotright> and K (
      opt_cap (pd_id, pd_slot) spec = Some pt_cap \<and>
      pt_at (cap_object pt_cap) spec \<and>
      opt_cap (pt_id, pt_slot) spec = Some page_cap \<and>
      cptr_map (pt_id, pt_slot) = free_cptr \<and>
      pt_cap = PageTableCap pt_id Fake None \<and>
      ((page_cap = fake_frame_cap False page_id (validate_vm_rights rights) n \<and> (n = 12 \<or> n = 16))
       \<or> page_cap = NullCap) \<and>
      free_cptr < 2 ^ si_cnode_size \<and>
      pd_slot < 2 ^ 12 \<and>
      pt_slot < 2 ^ 8 \<and>
      vaddr = pt_vaddr_of_pd_slot pd_slot)\<rbrace>
    map_page_table_slot spec orig_caps pd_id pt_id vaddr cptr_map pt_slot
    \<lbrace>\<lambda>_. \<guillemotleft>object_slot_initialised spec t pd_id pd_slot \<and>*
          object_slot_initialised spec t (cap_object pt_cap) pt_slot \<and>*
          si_caps_at t orig_caps spec False {obj_id. real_object_at obj_id spec} \<and>*
          si_objects \<and>* (si_cnode_id, unat free_cptr) \<mapsto>c conjure_real_frame_cap page_cap t \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (clarsimp simp: map_page_table_slot_def is_fake_pt_cap_def  dest!: domE split: cdl_cap.splits)
  apply (intro conjI impI)
   apply (wp sep_wp: map_page_wp[where n=n and page_cap=page_cap])
   apply (clarsimp, intro conjI; clarsimp?)
           apply sep_solve
          apply (clarsimp simp: cap_rights_def)
         apply fastforce+
   apply (subst (asm) sep_caps_at_split[where a=pd_id], clarsimp simp: object_at_real_object_at)
   apply (sep_simp si_cap_at_def)
  apply (wp, clarsimp simp: conjure_real_frame_cap_def)
  apply sep_cancel+
  by (fastforce simp: object_slot_empty_initialised_NullCap object_at_def is_tcb_def)

(***********************************************************
  * Mapping a page directory slot that contains a frame *
************************************************************)

lemma map_page_directory_slot_page_wp:
 "frame_at page_id spec \<Longrightarrow>
  \<lbrace>\<guillemotleft>(object_slot_empty spec t pd_id pd_slot \<and>* (si_cnode_id, unat free_cptr) \<mapsto>c NullCap \<and>*
    si_caps_at t orig_caps spec False {obj_id. real_object_at obj_id spec} \<and>* si_objects \<and>* R)\<guillemotright> and
   K (page_cap = fake_frame_cap False page_id (validate_vm_rights rights) n \<and> well_formed spec \<and>
      pd_at pd_id spec \<and> (n = 20 \<or> n = 24) \<and> cptr_map (pd_id, pd_slot) = free_cptr \<and>
      pd_slot = unat (pd_slot_of_pt_vaddr vaddr) \<and> opt_cap (pd_id, pd_slot) spec = Some page_cap \<and>
      pd_slot < 2 ^ 12 \<and> the (orig_caps pd_id) < 2 ^ si_cnode_size \<and>
      free_cptr < 2 ^ si_cnode_size)\<rbrace>
    map_page_directory_slot spec orig_caps pd_id cptr_map pd_slot
  \<lbrace>\<lambda>_. \<guillemotleft>(object_slot_initialised spec t pd_id pd_slot \<and>*
        (si_cnode_id, unat free_cptr) \<mapsto>c conjure_real_frame_cap page_cap t \<and>*
        si_caps_at t orig_caps spec False {obj_id. real_object_at obj_id spec} \<and>* si_objects \<and>* R)\<guillemotright>\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (clarsimp simp: map_page_directory_slot_def)
  apply (intro conjI impI)
   apply (fastforce simp: object_at_def dest: not_frame_and_pt)
  apply (wp sep_wp: map_page_in_pd_wp[where n=n])
  apply clarsimp
  apply (intro conjI)
      apply sep_solve
     apply (fastforce simp: cap_rights_def pt_size_def small_frame_size_def)+
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

lemma object_fields_empty_initialised_pd:
  "\<lbrakk>well_formed spec; pd_at obj_id spec\<rbrakk> \<Longrightarrow>
   object_fields_empty spec t obj_id = object_fields_initialised spec t obj_id"
  apply (clarsimp simp: object_at_def object_type_is_object)
  apply (frule (1) well_formed_object_slots)
  apply (clarsimp simp: object_fields_empty_def object_fields_initialised_def
                        object_initialised_general_def object_at_def object_type_is_object)
  apply (subst sep_map_f_object_size_bits_pd, simp+)
  done

lemma pt_NullCap_empty_init:
  "well_formed spec \<Longrightarrow>
   pt_at obj_id spec \<Longrightarrow>
   cap_at (\<lambda>x. x = NullCap) (obj_id, slot) spec \<Longrightarrow>
   object_slot_empty spec t obj_id slot = object_slot_initialised spec t obj_id slot"
  apply (rule object_slot_empty_initialised_NullCap)
    apply fastforce
   apply (clarsimp simp: object_at_def is_pt_def is_tcb_def  split: cdl_object.splits)
   apply (metis cdl_object.exhaust)
  apply (clarsimp simp: cap_at_def)
  done

lemma pd_NullCap_empty_init:
  "well_formed spec \<Longrightarrow>
   pd_at obj_id spec \<Longrightarrow>  cap_at (\<lambda>x. x = NullCap) (obj_id, slot) spec \<Longrightarrow>
   object_slot_empty spec t obj_id slot = object_slot_initialised spec t obj_id slot"
  apply (rule object_slot_empty_initialised_NullCap)
    apply clarsimp
   apply (clarsimp simp: object_at_def is_pd_def is_tcb_def  split: cdl_object.splits)
   apply (metis cdl_object.exhaust)
  apply (clarsimp simp: cap_at_def)
  done

(***********************************************************
* Mapping a page directory slot that contains a page table *
************************************************************)

lemma map_page_directory_slot_pt_wp:
  "pt_at pt_id spec \<Longrightarrow>
   \<lbrace>\<guillemotleft>object_slot_empty spec t pd_id slot \<and>*
     si_caps_at t orig_caps spec False {obj_id. real_object_at obj_id spec} \<and>*
     si_objects \<and>*
     sep_map_list_conj ((\<lambda>x. (si_cnode_id, unat x) \<mapsto>c NullCap) o cptr_map o (Pair pt_id))
                       [slot <- page_slots. cap_at ((\<noteq>) NullCap) (pt_id, slot) spec]  \<and>*
     object_empty spec t pt_id \<and>* R\<guillemotright> and K (
       (\<forall>n \<in> range cptr_map. n < 2 ^ si_cnode_size) \<and>
       pt_cap = PageTableCap pt_id Fake None  \<and>
       well_formed spec \<and>
       slot < 0x1000 \<and> (n = 12 \<or> n = (16 :: nat)) \<and>
       pd_at pd_id spec \<and>
       page_slots = slots_of_list spec pt_id \<and>
       opt_cap (pd_id, slot) spec = Some pt_cap)\<rbrace>
    map_page_directory_slot spec orig_caps pd_id  cptr_map slot
    \<lbrace>\<lambda>_. \<guillemotleft>sep_map_list_conj (\<lambda>x. (si_cnode_id, unat (cptr_map (pt_id, x)))
                                 \<mapsto>c conjure_real_frame_cap (the_cap spec pt_id x) t)
                            [slot <- page_slots. cap_at ((\<noteq>) NullCap) (pt_id, slot) spec] \<and>*
          object_initialised spec t pt_id  \<and>* object_slot_initialised spec t pd_id slot \<and>*
          si_caps_at t orig_caps spec False {obj_id. real_object_at obj_id spec} \<and>*
          si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (clarsimp simp: map_page_directory_slot_def)
  apply (rule hoare_name_pre_state)
  apply (wp map_page_table_slot_wp[where pt_cap=pt_cap,
                                   simplified sep_wp_simp, THEN sep_hoare_fold_mapM_x]
            map_page_table_in_pd_wp[sep_wandise])+
  apply (clarsimp, intro conjI impI)
      apply sep_cancel+
      apply (clarsimp simp: pt_size_def small_frame_size_def word_of_nat_less word_bits_def
                            unat_of_nat32)
      apply (sep_fold_cancel, rule sep_map_sep_foldI)
       apply (clarsimp simp: map_def comp_def object_empty_decomp object_initialised_decomp
                             object_empty_slots_empty_initialised object_fields_empty_initialised_pt
                             object_slots_initialised_decomp object_slots_empty_decomp sep_conj_ac)
       apply sep_cancel+
       apply (clarsimp simp: well_formed_finite sep.prod.union_diff2 sep_list_conj_sep_map_set_conj
                             well_formed_distinct_slots_of_list
                             sep_map_set_conj_set_cong
                               [OF split_filter_set
                                     [where xs="dom (slots_of pt_id spec)" and
                                            P="\<lambda>slot. cap_at ((\<noteq>) NullCap) (pt_id, slot) spec"]])
       apply sep_cancel+
       apply (fastforce elim: sep_map_set_conj_match
                        simp: pt_NullCap_empty_init not_cap_at_cap_not_at eq_commute)
      apply clarsimp
      apply (intro conjI)
        apply (clarsimp simp: object_at_def cap_at_def)
       apply clarsimp
       apply (erule wf_cap_in_pt_is_frame; fastforce simp: cap_at_def)
      apply (frule well_formed_slot_object_size_bits_pt[where obj_id=pt_id,
                                                        simplified is_pt_pt_size])
  by (fastforce simp: cap_at_def opt_cap_def pt_size_def small_frame_size_def)+

(***********************************************************
              * Mapping a page directory *
************************************************************)

lemma map_page_directory_wp_expanded:
  "\<lbrakk>well_formed spec; pd_at pd_id spec; pd_slots = slots_of_list spec pd_id;
    list_all (\<lambda>n. n < 2 ^ 12) pd_slots; \<forall>ptr. cptr_map ptr < 2 ^ si_cnode_size;
    the (orig_caps pd_id) < 2 ^ si_cnode_size\<rbrakk> \<Longrightarrow>
    \<lbrace>\<guillemotleft>si_objects \<and>*
      si_caps_at t orig_caps spec False {obj_id. real_object_at obj_id spec} \<and>*
      \<And>* map (\<lambda>x.
          let pt_id = get_obj pd_id x spec in
          object_slot_empty spec t pd_id x \<and>*
          object_empty spec t pt_id \<and>*
          sep_map_set_conj (\<lambda>y. (si_cnode_id, unat (cptr_map (pt_id, y))) \<mapsto>c NullCap)
                           {slot \<in> dom (slots_of pt_id spec).
                             cap_at ((\<noteq>) NullCap) (pt_id, slot) spec})
        [slot <- pd_slots. cap_object_from_slot pd_id slot pt_at spec] \<and>*
      \<And>* map (\<lambda>x.
          let frame_id = get_obj pd_id x spec in
          (si_cnode_id, unat (cptr_map (pd_id, x))) \<mapsto>c NullCap \<and>*
          object_slot_empty spec t pd_id x)
        [slot <- pd_slots. cap_object_from_slot pd_id slot frame_at spec] \<and>*
      R\<guillemotright>\<rbrace>
      map_page_directory spec orig_caps cptr_map pd_id
    \<lbrace>\<lambda>_. \<guillemotleft>si_objects \<and>*
          si_caps_at t orig_caps spec False {obj_id. real_object_at obj_id spec} \<and>*
          \<And>* map (\<lambda>x.
              let pt_id = get_obj pd_id x spec in
              object_slot_initialised spec t pd_id x \<and>*
              object_initialised spec t pt_id \<and>*
              sep_map_set_conj (\<lambda>y. (si_cnode_id, unat (cptr_map (pt_id, y)))
                                    \<mapsto>c conjure_real_frame_cap (the_cap spec pt_id y) t)
                               {slot \<in> dom (slots_of pt_id spec).
                                 cap_at ((\<noteq>) NullCap) (pt_id, slot) spec})
             [slot <- pd_slots. cap_object_from_slot pd_id slot pt_at spec] \<and>*
          \<And>* map (\<lambda>x.
              let frame_id = get_obj pd_id x spec in
              (si_cnode_id, unat (cptr_map (pd_id, x)))
                \<mapsto>c conjure_real_frame_cap (the_cap spec pd_id x) t \<and>*
              object_slot_initialised spec t pd_id x)
             [slot <- pd_slots. cap_object_from_slot pd_id slot frame_at spec] \<and>*
          R\<guillemotright>\<rbrace>"
  apply (clarsimp simp: map_page_directory_def Let_unfold)
  apply wp
    apply (rule sep_hoare_fold_mapM_x[OF map_page_directory_slot_pt_wp
                                          [where t=t and
                                                 page_slots="slots_of_list spec pt_id" and
                                                 pt_id="get_obj pd_id slot spec"
                                                 for pt_id slot,
                                           simplified sep_wp_simp],
                                          simplified fun_app_def])
    apply (clarsimp simp: opt_cap_def cap_at_def)
    apply (fastforce dest: Some_to_the)
   apply (rule sep_hoare_fold_mapM_x[OF map_page_directory_slot_page_wp
                                          [where t=t and
                                                 rights="cap_rights cap" and
                                                 n="cap_size_bits cap" and
                                                 page_id="get_obj pd_id slot spec"
                                                 for slot cap,
                                           simplified sep_wp_simp],
                                          simplified fun_app_def])
   apply (clarsimp simp: cap_at_def)
   apply (fastforce dest: Some_to_the)
  apply clarsimp
  apply (sep_fold_cancel, rule sep_map_sep_foldI)
   apply (clarsimp simp: cap_at_def)
   apply sep_cancel+
   apply (sep_fold_cancel, rule sep_map_sep_foldI)
    apply (clarsimp simp: sep_list_conj_sep_map_set_conj well_formed_distinct_slots_of_list
                          well_formed_finite)
    apply sep_solve
   apply (intro conjI)
       apply (fastforce dest: Some_to_the)
      apply (fastforce elim: list_all_spec)+
   apply clarsimp
   apply (erule wf_pt_in_pd_fake_and_none; fastforce)
  apply (clarsimp, intro conjI)
      apply (drule wf_frame_cap_in_pd; (fastforce simp: cap_at_def)?)
     apply (drule wf_frame_cap_in_pd; (fastforce simp: cap_at_def)?)
    apply (rule pd_slot_compute_inverse[symmetric], clarsimp)
  by (fastforce simp: cap_at_def elim: list_all_spec)+

lemma slots_of_pd_split:
  "\<lbrakk>well_formed spec; pd_at pd_id spec\<rbrakk> \<Longrightarrow>
   dom (slots_of pd_id spec) =
    {slot \<in> dom (slots_of pd_id spec). cap_at (\<lambda>c. c \<noteq> NullCap \<and> pt_at (cap_object c) spec)
                                              (pd_id, slot) spec} \<union>
    {slot \<in> dom (slots_of pd_id spec). cap_at (\<lambda>c. c \<noteq> NullCap \<and> frame_at (cap_object c) spec)
                                              (pd_id, slot) spec} \<union>
    {slot \<in> dom (slots_of pd_id spec). cap_at (\<lambda>c. c = NullCap) (pd_id, slot) spec}"
  apply (intro set_eqI iffI; clarsimp)
   apply (clarsimp simp: slots_of_def cap_at_def opt_cap_object_slot_simp
                   split: option.splits)
   apply (fastforce dest: well_formed_pd_frame_or_pt)+
  done

lemma wf_split_slots_of_pd:
  "\<lbrakk>well_formed spec; pd_at pd_id spec\<rbrakk> \<Longrightarrow>
   sep_map_set_conj P (dom (slots_of pd_id spec)) =
    (sep_map_set_conj P
      {slot \<in> dom (slots_of pd_id spec). cap_at (\<lambda>c. c \<noteq> NullCap \<and> pt_at (cap_object c) spec)
                                                (pd_id, slot) spec} \<and>*
     sep_map_set_conj P
      {slot \<in> dom (slots_of pd_id spec). cap_at (\<lambda>c. c \<noteq> NullCap \<and> frame_at (cap_object c) spec)
                                                (pd_id, slot) spec} \<and>*
     sep_map_set_conj P
      {slot \<in> dom (slots_of pd_id spec). cap_at (\<lambda>c. c = NullCap) (pd_id, slot) spec})"
  apply clarsimp
  apply (subst slots_of_pd_split)
    apply (clarsimp simp: sep.prod.union_disjoint well_formed_finite[where obj_id=pd_id]
                          cap_at_def)+
  apply (subst sep.prod.union_disjoint)
     apply (clarsimp simp: well_formed_finite[where obj_id=pd_id])+
   apply (intro set_eqI iffI; clarsimp)
  apply (subst sep.prod.union_disjoint)
     apply (clarsimp simp: well_formed_finite[where obj_id=pd_id])+
   apply (intro set_eqI iffI; clarsimp)
   apply (fastforce dest: well_formed_pd_frame_or_pt)
  apply (clarsimp simp: sep_conj_ac)
  done

lemma wf_pd_pt_obj_inj:
  "\<lbrakk>well_formed spec; pd_at pd_id spec\<rbrakk>
   \<Longrightarrow> inj_on (ref_obj spec pd_id)
             {slot \<in> dom (slots_of pd_id spec). cap_object_from_slot pd_id slot pt_at spec}"
  supply object_type_is_object[simp]
  apply (clarsimp simp: inj_on_def cap_ref_object_def object_at_def)
  apply (frule_tac obj_id=pd_id and slot=y in well_formed_types_match)
     apply fastforce+
  using object_type_is_object(9) object_type_object_at(9) wf_pd_cap_has_object apply blast
  apply clarsimp+
  apply (frule_tac obj_id=pd_id and slot=x in well_formed_types_match, fastforce+)
  using object_type_is_object(9) object_type_object_at(9) wf_pd_cap_has_object apply blast
  apply (clarsimp simp: cap_type_def split: cdl_cap.splits)
  apply (frule_tac obj_id=pd_id and obj_id'=pd_id and slot=x and slot'=y in
                   well_formed_fake_pt_caps_unique)
         apply fastforce+
     apply (erule well_formed_pt_cap_is_fake_pt_cap, fastforce+)
    apply (erule well_formed_pt_cap_is_fake_pt_cap, fastforce+)
  done

lemma sep_map_pd_slots_inj[simp]:
  "well_formed spec \<Longrightarrow>
   pd_at pd_id spec \<Longrightarrow>
   (SETSEPCONJ x | x \<in> dom (slots_of pd_id spec) \<and> cap_object_from_slot pd_id x pt_at spec.
      P (cap_object (the_cap spec pd_id x))) =
   sep_map_set_conj P
     {obj. \<exists>slot. slot \<in> dom (slots_of pd_id spec) \<and>
                  cap_object_from_slot pd_id slot pt_at spec \<and>
                  obj = cap_object (the_cap spec pd_id slot)}"
  apply (subgoal_tac "{obj. \<exists>slot. slot \<in> dom (slots_of pd_id spec) \<and>
                                   cap_object_from_slot pd_id slot pt_at spec \<and>
                                   obj = cap_object (the_cap spec pd_id slot)} =
                      ref_obj spec pd_id ` {slot \<in> dom (slots_of pd_id spec).
                                              cap_object_from_slot pd_id slot pt_at spec}")
   prefer 2
   apply (clarsimp simp: cap_ref_object_def)
   apply blast
  apply clarsimp
  apply (subst sep.prod.reindex)
   apply (erule (1) wf_pd_pt_obj_inj)
  apply (clarsimp simp: cap_ref_object_def)
  done

lemma opt_cap_cap_at_simp: "(opt_cap ref spec = Some cap) = cap_at (\<lambda>x. x = cap) ref spec"
  by (clarsimp simp: cap_at_def)

(***********************************************************
* Mapping a page directory, with cleaner pre/postcondition *
************************************************************)

lemma map_page_directory_wp:
  "\<lbrakk>well_formed spec; pd_at pd_id spec; pd_slots = slots_of_list spec pd_id;
    list_all (\<lambda>n. n < 2 ^ 12) pd_slots; \<forall>ptr. cptr_map ptr < 2 ^ si_cnode_size;
    the (orig_caps pd_id) < 2 ^ si_cnode_size\<rbrakk> \<Longrightarrow>
     \<lbrace>\<guillemotleft>si_objects \<and>*
       si_caps_at t orig_caps spec False {obj_id. real_object_at obj_id spec} \<and>*
       object_empty spec t pd_id \<and>*
       frame_duplicates_empty cptr_map pd_id spec \<and>*
       slots_in_object_empty (\<lambda>cap. cap \<noteq> NullCap \<and> pt_at (cap_object cap) spec) pd_id spec t \<and>*
       R\<guillemotright>\<rbrace>
     map_page_directory spec orig_caps cptr_map pd_id
     \<lbrace>\<lambda>_. \<guillemotleft>si_objects \<and>*
           si_caps_at t orig_caps spec False {obj_id. real_object_at obj_id spec} \<and>*
           object_initialised spec t pd_id \<and>*
           frame_duplicates_copied cptr_map pd_id spec t \<and>*
           slots_in_object_init (\<lambda>cap. cap \<noteq> NullCap \<and> pt_at (cap_object cap) spec) pd_id spec t \<and>*
           R\<guillemotright>\<rbrace>"
  apply (wp map_page_directory_wp_expanded[sep_wandise])
  apply sep_cancel+
  apply (clarsimp simp: Let_unfold cap_at_def wf_split_slots_of_pd object_slots_empty_decomp
                        object_empty_decomp[where spec_object_id=pd_id]
                        sep_list_conj_sep_map_set_conj slots_in_object_empty_def
                        frame_duplicates_empty_def cap_ref_object_def
                        well_formed_distinct_slots_of_list well_formed_finite
                        object_initialised_decomp[where spec_object_id=pd_id]
                        frame_duplicates_copied_def object_slots_initialised_decomp
                        object_fields_empty_initialised_pd object_empty_slots_empty_initialised)
  apply sep_cancel+
  apply (subst (asm) sep_map_set_conj_subst[OF pd_NullCap_empty_init];
         clarsimp simp: opt_cap_cap_at_simp)
  apply sep_cancel
  apply (clarsimp simp: slots_in_object_init_def)
  apply (fold cap_ref_object_def)
  apply (erule sep_map_set_elim)
   apply (clarsimp simp: image_def)
   apply (intro set_eqI iffI; clarsimp simp: cap_at_def)
  apply blast
  done

lemma set_asid_wp:
   "\<lbrace>\<guillemotleft>si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} \<and>*
      si_objects \<and>* R\<guillemotright> and K(
     well_formed spec \<and>
     pd_at obj_id spec)\<rbrace>
    set_asid spec orig_caps obj_id
    \<lbrace>\<lambda>rv. \<guillemotleft>si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} \<and>*
           si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_gen_asm, clarsimp)
  apply (frule (1) object_at_real_object_at)
  apply (rule valid_si_caps_at_si_cap_at [where obj_id=obj_id], clarsimp+)
  apply (clarsimp simp: si_cap_at_def sep_conj_assoc sep_conj_exists)
  apply (subst ex_conj_increase)+
  apply (rule hoare_vcg_ex_lift)+
  apply (rename_tac kobj_id)
  apply (rule hoare_grab_asm)+
  apply wpsimp
   apply (clarsimp simp: set_asid_def)
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
  "(\<not> object_at P obj_id spec) \<Longrightarrow> cdl_objects spec obj_id = Some object \<Longrightarrow>
   object_at (\<lambda>obj. \<not>P obj) obj_id spec "
  apply (clarsimp simp: object_at_def)
  done

definition parent_obj_of :: "cdl_object_id \<Rightarrow> cdl_object_id \<Rightarrow> cdl_state \<Rightarrow> bool" where
  "parent_obj_of parent_obj child_obj spec \<equiv>
      (\<exists>slot \<in> dom (slots_of parent_obj spec).
           cap_at (\<lambda>cap. cap_has_object cap \<and> cap_object cap = child_obj) (parent_obj, slot) spec)"

definition pd_equiv_class :: "cdl_state \<Rightarrow> (cdl_object_id \<times> cdl_object_id) set" where
  "pd_equiv_class spec \<equiv>
    {(x,y). pt_at x spec \<and> pt_at y spec \<and>
            (\<exists>obj. pd_at obj spec \<and> parent_obj_of obj x spec \<and> parent_obj_of obj y spec)}"

lemma pd_equiv_sym:
  "sym (pd_equiv_class spec)"
  apply (clarsimp simp: sym_def pd_equiv_class_def)
  by blast

lemma pt_parents_eq:
  "\<lbrakk>well_formed spec; pd_at obj_id spec; pd_at obj_id' spec; pt_at pt spec;
    parent_obj_of obj_id pt spec; parent_obj_of obj_id' pt spec\<rbrakk>
   \<Longrightarrow> obj_id = obj_id'"
  apply (clarsimp simp: parent_obj_of_def cap_at_def)
  apply (frule well_formed_fake_pt_caps_unique[where obj_id=obj_id and obj_id'=obj_id'])
         apply assumption+
     apply (metis (full_types) cap_has_object_not_NullCap cap_type_simps(8)
                               well_formed_pt_cap_is_fake_pt_cap wf_pt_in_pd_fake_and_none)
    apply (metis (full_types) cap_has_object_not_NullCap cap_type_simps(8)
                              well_formed_pt_cap_is_fake_pt_cap wf_pt_in_pd_fake_and_none)
   apply fastforce+
  done

lemma pd_equiv_trans:
  "well_formed spec \<Longrightarrow> trans (pd_equiv_class spec)"
  apply (clarsimp simp: trans_def pd_equiv_class_def)
  apply (rule_tac x=obj in exI)
  apply (clarsimp)
  using pt_parents_eq by blast

abbreviation (input)
  "object_in_cap P ref spec \<equiv> cap_at (\<lambda>cap. cap \<noteq> NullCap \<and> P (cap_object cap)) ref spec"

(* Looking up PTs of a PD is injective, except when both have none *)
lemma pd_pts_inj_or_empty:
  "\<lbrakk>well_formed spec; pd_at x spec; pd_at y spec;
    {obj. \<exists>slot. slot \<in> dom (slots_of x spec) \<and>
                 object_in_cap (\<lambda>obj. pt_at obj spec) (x, slot) spec \<and> obj = ref_obj spec x slot} =
    {obj. \<exists>slot. slot \<in> dom (slots_of y spec) \<and>
                object_in_cap (\<lambda>obj. pt_at obj spec) (y, slot) spec \<and> obj = ref_obj spec y slot};
    x \<noteq> y\<rbrakk> \<Longrightarrow>
  {obj. \<exists>slot. slot \<in> dom (slots_of x spec) \<and>
               object_in_cap (\<lambda>obj. pt_at obj spec) (x, slot) spec \<and> obj = ref_obj spec x slot} = {}"
  apply (clarsimp simp: cap_at_def cap_ref_object_def)
  apply (drule_tac x="cap_object cap" in eqset_imp_iff)
  apply (frule pt_parents_eq[where obj_id = x and obj_id' = y];
         fastforce simp: parent_obj_of_def cap_at_def wf_pd_cap_has_object)
  done

lemma wf_pd_equiv_parentD:
  "\<lbrakk>(pt, pt') \<in> pd_equiv_class spec; well_formed spec; pd_at pd spec; parent_obj_of pd pt spec\<rbrakk>
    \<Longrightarrow> parent_obj_of pd pt' spec"
  apply (clarsimp simp: pd_equiv_class_def)
  apply (frule_tac obj_id=obj and obj_id'=pd and pt=pt in pt_parents_eq; fastforce)
  done

lemma pd_equiv_ptsD: "pts \<in> pd_equiv_class spec \<Longrightarrow> pt_at (fst pts) spec \<and> pt_at (snd pts) spec"
  by (clarsimp simp: pd_equiv_class_def split: prod.splits)

(* Grouping PTs by their parent PD is the same as taking the PT children of each parent PD *)
lemma pd_quotient_eq_pts_of_pds:
  "well_formed spec \<Longrightarrow>
   image (\<lambda>pd.{ref_obj spec pd slot | slot. slot \<in> dom (slots_of pd spec) \<and>
                             object_in_cap (\<lambda>obj. pt_at obj spec) (pd, slot) spec})
                             {obj. pd_at obj spec} - {{}} =
   {x. pt_at x spec \<and> (\<exists>obj. pd_at obj spec \<and>
     (\<exists>slot\<in>dom (slots_of obj spec). cap_at cap_has_object (obj, slot) spec
                                    \<and> ref_obj spec obj slot = x))} // pd_equiv_class spec - {{}}"
  apply (clarsimp simp: image_def quotient_def Image_def cong: SUP_cong_simp)
  apply (intro set_eqI iffI; clarsimp simp: cap_at_def)
   apply (guess_exI)
   apply safe
     apply (fastforce simp: wf_pd_cap_has_object cap_ref_object_def)
    apply (clarsimp simp: pd_equiv_class_def cap_ref_object_def)
    apply (guess_exI, clarsimp)
    apply (intro conjI; fastforce simp: wf_pd_cap_has_object cap_ref_object_def
                                        cap_at_def parent_obj_of_def)
   apply (clarsimp simp: cap_ref_object_def)
   apply (frule_tac pd=xa in wf_pd_equiv_parentD; clarsimp?)
    apply (fastforce simp: wf_pd_cap_has_object cap_ref_object_def cap_at_def parent_obj_of_def)
   apply (drule pd_equiv_ptsD, clarsimp simp: parent_obj_of_def cap_at_def)
   apply (rule_tac x=slota in exI)
   apply (fastforce simp: wf_pd_cap_has_object cap_ref_object_def
                          pd_equiv_class_def cap_at_def parent_obj_of_def)
  apply (rule_tac x=obj in exI)
  apply (clarsimp simp: cap_ref_object_def)
  apply (intro set_eqI iffI; clarsimp)
   apply (frule_tac pd=obj and pt'=xa in wf_pd_equiv_parentD; clarsimp?)
    apply (fastforce simp: parent_obj_of_def cap_at_def)
   apply (drule pd_equiv_ptsD, clarsimp simp: parent_obj_of_def cap_at_def)
   apply (rule_tac x=slota in exI)
   apply (fastforce simp: wf_pd_cap_has_object cap_ref_object_def
      pd_equiv_class_def cap_at_def parent_obj_of_def)
  apply (clarsimp simp: pd_equiv_class_def)
  apply (rule_tac x=obj in exI)
  apply (clarsimp simp: parent_obj_of_def cap_at_def)
  apply (metis (full_types) domI wf_pd_cap_has_object)
  done

lemma well_formed_pd_slots:
  "\<lbrakk>well_formed spec; pd_at obj_id spec\<rbrakk> \<Longrightarrow>
   \<forall>slot \<in> dom (slots_of obj_id spec). slot < 2 ^ 12"
  by (fastforce simp: Ball_def elim: well_formed_pd_slot_limited)

lemma well_formed_pt_not_in_pd_empty_init:
 "\<lbrakk>well_formed spec; pt_at x spec;
   (\<forall>obj. pd_at obj spec \<longrightarrow> (\<forall>slot\<in>dom (slots_of obj spec). cap_at cap_has_object (obj, slot) spec
                         \<longrightarrow> ref_obj spec obj slot \<noteq> x))\<rbrakk>
   \<Longrightarrow> object_empty spec t x = object_initialised spec t x"
  apply (rule object_empty_initialised_default_state)
  apply (rule ccontr)
  apply (drule not_object_at, fastforce)
  apply (frule (2) well_formed_cap_to_non_empty_pt)
  apply clarsimp
  apply (erule_tac x=pd_id in allE, clarsimp)
  apply (clarsimp simp: object_at_def)
  apply (case_tac "cap \<noteq> NullCap")
   apply (frule well_formed_types_match[symmetric], fastforce+)
   apply (fastforce del: opt_cap_dom_slots_of
                    dest: opt_cap_dom_slots_of
                    simp: cap_at_def cap_ref_object_def object_at_def object_type_is_object)+
  done

lemma refl_on_pd_parent[simp]:
  "refl_on {pt_id. pt_at pt_id spec \<and>
                   (\<exists>obj. pd_at obj spec \<and> parent_obj_of obj pt_id spec)}
           (pd_equiv_class spec)"
  by (clarsimp simp: pd_equiv_class_def refl_on_def)

lemma pt_parents_pd_pts_empty:
  "well_formed spec \<Longrightarrow>
   (SETSEPCONJ pd_id | pd_at pd_id spec.
        slots_in_object_empty (\<lambda>cap. cap \<noteq> NullCap \<and> pt_at (cap_object cap) spec) pd_id spec t) =
   (SETSEPCONJ pt_id | pt_at pt_id spec \<and> (\<exists>obj. pd_at obj spec \<and> parent_obj_of obj pt_id spec).
        object_empty spec t pt_id)"
  apply (rule sym, subst sep_map_set_quotient_split[where R="pd_equiv_class spec"])
    apply fastforce
   apply (rule equivI; clarsimp simp: pd_equiv_sym[simplified fun_app_def] pd_equiv_trans)
   apply (fastforce simp: pd_equiv_class_def)
  apply (clarsimp simp: slots_in_object_empty_def, rule sym, subst sep_map_set_squash)
    apply clarsimp
    apply (drule_tac x=x and y=y in pd_pts_inj_or_empty, clarsimp+)
    apply blast
   apply fastforce
  apply (rule sym)
  apply (rule sep_map_set_conj_cong_empty_eq)
    apply clarsimp+
  apply (rule box_equals[OF pd_quotient_eq_pts_of_pds[symmetric]], assumption)
   apply (clarsimp simp: parent_obj_of_def, intro set_eqI iffI;
          clarsimp simp: quotient_def Image_def)
    apply (guess_exI, clarsimp)
    apply (guess_exI, clarsimp)
    apply (clarsimp simp: cap_ref_object_def)
    apply (metis (mono_tags, lifting) cap_at_def domI option.sel)
   apply (guess_exI, clarsimp)
   apply (guess_exI, clarsimp)
   apply (clarsimp simp: cap_ref_object_def)
   apply (metis (mono_tags, lifting) cap_at_def domI option.sel)
  apply blast
  done

lemma pt_parents_pd_pts_init:
  "well_formed spec \<Longrightarrow>
   (SETSEPCONJ pd_id | pd_at pd_id spec.
        slots_in_object_init (\<lambda>cap. cap \<noteq> NullCap \<and> pt_at (cap_object cap) spec) pd_id spec t) =
   (SETSEPCONJ pt_id | pt_at pt_id spec \<and> (\<exists>obj. pd_at obj spec \<and> parent_obj_of obj pt_id spec).
        object_initialised spec t pt_id)"
  apply (rule sym, subst sep_map_set_quotient_split[where R="pd_equiv_class spec"])
    apply (clarsimp)
   apply (rule equivI; clarsimp simp: pd_equiv_sym[simplified fun_app_def] pd_equiv_trans)
   apply (fastforce simp: pd_equiv_class_def)
  apply (clarsimp simp: slots_in_object_init_def, rule sym, subst sep_map_set_squash)
    apply clarsimp
    apply (drule_tac x=x and y=y in pd_pts_inj_or_empty, clarsimp+)
    apply blast
   apply clarsimp
  apply (rule sym)
  apply (rule sep_map_set_conj_cong_empty_eq)
    apply clarsimp+
  apply (rule box_equals [OF pd_quotient_eq_pts_of_pds[symmetric]], assumption)
   apply (clarsimp simp: parent_obj_of_def, intro set_eqI iffI;
          clarsimp simp: quotient_def Image_def)
    apply (guess_exI, clarsimp)
    apply (guess_exI, clarsimp)
    apply (clarsimp simp: cap_ref_object_def)
    apply (metis (mono_tags, lifting) cap_at_def domI option.sel)
   apply (guess_exI, clarsimp)
   apply (guess_exI, clarsimp)
   apply (clarsimp simp: cap_ref_object_def)
   apply (metis (mono_tags, lifting) cap_at_def domI option.sel)
  apply blast
  done

(***********************************************************
              * Initialising all page directories *
************************************************************)

lemma init_vspace_sep:
  "\<lbrace>\<guillemotleft>si_objects \<and>*
     si_caps_at t orig_caps spec False {obj_id. real_object_at obj_id spec} \<and>*
     objects_empty spec t {obj_id. table_at obj_id spec} \<and>*
     (SETSEPCONJ x | pd_at x spec.
        frame_duplicates_empty (make_frame_cap_map obj_ids free_cptrs spec) x spec) \<and>*
     R\<guillemotright> and K (
      well_formed spec \<and>
      set obj_ids = dom (cdl_objects spec) \<and>
      distinct obj_ids \<and>
      card (\<Union> (set ` get_frame_caps spec ` {obj. pd_at obj spec})) \<le> length free_cptrs \<and>
      list_all (\<lambda>n. n < 2 ^ si_cnode_size) free_cptrs \<and>
      (\<forall>p. p \<in> {obj_id. pd_at obj_id spec} \<longrightarrow> the (orig_caps p) < 2 ^ si_cnode_size))\<rbrace>
   init_vspace spec orig_caps obj_ids free_cptrs
   \<lbrace>\<lambda>_. \<guillemotleft>si_objects \<and>*
         si_caps_at t orig_caps spec False {obj_id. real_object_at obj_id spec} \<and>*
         objects_initialised spec t {obj_id. table_at obj_id spec} \<and>*
         (SETSEPCONJ x | pd_at x spec.
            frame_duplicates_copied (make_frame_cap_map obj_ids free_cptrs spec) x spec t) \<and>*
         R\<guillemotright>\<rbrace>"
  apply (rule hoare_gen_asm, clarsimp)
  apply (clarsimp simp: objects_empty_def objects_initialised_def)
  apply (subst sep_map_set_conj_set_disjoint, simp+,
         clarsimp simp: object_at_def object_type_is_object)+
  apply (clarsimp simp: init_vspace_def sep_conj_assoc)
  apply (wp sep_hoare_fold_mapM_x[OF map_page_directory_wp[simplified sep_wp_simp]], simp+)
     apply (frule_tac obj_id=x in well_formed_pd_slots; clarsimp)
     using Ball_set apply fastforce
    apply (clarsimp simp: make_frame_cap_map_def si_cnode_size_def split: option.splits)
    apply (meson list_all_spec map_of_SomeD set_zip_rightD)
   apply (fastforce elim: list_all_spec)
  apply sep_flatten
  apply sep_fold_cancel
  apply (rule sep_map_set_sep_foldI)
   apply (clarsimp simp: sep.prod.distrib)+
  apply sep_cancel+
    (* Split PTs into those which have a parent and those which do not *)
  apply (clarsimp simp: sep_map_set_conj_restrict
                          [where t="\<lambda>pt_id. (\<exists>obj. pd_at obj spec \<and> parent_obj_of obj pt_id spec)"
                             and xs="{obj_id. pt_at obj_id spec}"])
  apply (clarsimp simp: pt_parents_pd_pts_empty pt_parents_pd_pts_init, sep_cancel+)
  apply (subst (asm) sep_map_set_conj_subst[OF well_formed_pt_not_in_pd_empty_init])
     apply fastforce+
   apply (clarsimp simp: parent_obj_of_def)
   apply (erule_tac x=obj in allE, drule mp, assumption, clarsimp simp: cap_at_def)
   apply (fastforce simp: cap_ref_object_def)
  by sep_solve

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
