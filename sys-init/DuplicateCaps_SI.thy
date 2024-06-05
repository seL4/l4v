(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory DuplicateCaps_SI
imports
  "DSpecProofs.CNode_DP"
  ObjectInitialised_SI
  RootTask_SI
  SysInit_SI
begin

lemma sep_map_zip_fst:
  "\<lbrakk>distinct xs; length xs \<le> length ys\<rbrakk> \<Longrightarrow> (\<And>* (x, y) \<in> set (zip xs ys). f x) = (\<And>* x \<in> set xs. f x)"
  apply (subst sep_list_conj_sep_map_set_conj [symmetric], simp add: distinct_zipI1)+
  apply (subst map_zip_fst', assumption)
  apply simp
  done

lemma sep_map_zip_snd_take:
  "\<lbrakk>distinct xs; distinct ys\<rbrakk> \<Longrightarrow>
    (\<And>* (x, y) \<in> set (zip xs ys). f y) = (\<And>* x \<in> set (take (length xs) ys). f x)"
  apply (subst sep_list_conj_sep_map_set_conj [symmetric], simp add: distinct_zipI1)+
  apply (subst map_zip_snd_take)
  apply simp
  done

lemma wfdc_obj_not_untyped:
  "well_formed_cap (default_cap t oid sz dev) \<Longrightarrow> t \<noteq> UntypedType"
  by (clarsimp simp:default_cap_def well_formed_cap_def)

lemma derived_cap_default:
  "derived_cap (default_cap ty oid sz dev)
  = (default_cap ty oid sz dev)"
  by (case_tac ty,
    simp_all add:derived_cap_def default_cap_def)

lemma cnode_or_tcb_at_wfc:
  "\<lbrakk>cnode_or_tcb_at obj_id spec; cdl_objects spec obj_id = Some obj; sz \<le> 32\<rbrakk>
   \<Longrightarrow> well_formed_cap (default_cap (object_type obj) oid sz dev)"
  apply (elim disjE)
   apply (simp add: object_at_def is_tcb_def default_cap_def well_formed_cap_def
                    is_cnode_def object_type_def guard_bits_def
             split: cdl_object.splits)+
  done

lemma frame_at_wfc:
  "\<lbrakk>frame_at obj_id spec; cdl_objects spec obj_id = Some obj; sz \<le> 32\<rbrakk>
   \<Longrightarrow> well_formed_cap (default_cap (object_type obj) oid sz dev)"
   apply (simp add: object_at_def is_frame_def default_cap_def well_formed_cap_def
                    is_cnode_def object_type_def guard_bits_def vm_read_write_def
             split: cdl_object.splits)
  done

lemma seL4_CNode_Copy_sep_helper:
  "\<lbrakk>(free_cptr::32 word) < 2 ^ si_cnode_size;
    (cap_ptr::32 word) < 2 ^ si_cnode_size;
    well_formed_cap (default_cap (object_type obj) {kobj_id} (object_size_bits obj) dev)\<rbrakk>
  \<Longrightarrow>
  \<lbrace>\<lambda>s. \<guillemotleft>si_tcb_id \<mapsto>f root_tcb \<and>*
       (si_tcb_id, tcb_cspace_slot) \<mapsto>c si_cspace_cap \<and>*
       (si_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
        si_cnode_id \<mapsto>f CNode (empty_cnode si_cnode_size) \<and>*
       (si_cnode_id, unat seL4_CapInitThreadCNode) \<mapsto>c si_cnode_cap \<and>*
       (si_cnode_id, unat cap_ptr) \<mapsto>c default_cap (object_type obj) {kobj_id}
                                                     (object_size_bits obj) dev \<and>*
       (si_cnode_id, unat free_cptr) \<mapsto>c NullCap \<and>* R\<guillemotright> s\<rbrace>
    seL4_CNode_Copy seL4_CapInitThreadCNode free_cptr 32
                    seL4_CapInitThreadCNode cap_ptr 32 UNIV
  \<lbrace>\<lambda>rv.\<guillemotleft>si_tcb_id \<mapsto>f root_tcb \<and>*
       (si_tcb_id, tcb_cspace_slot) \<mapsto>c si_cspace_cap \<and>*
       (si_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
        si_cnode_id \<mapsto>f CNode (empty_cnode si_cnode_size) \<and>*
       (si_cnode_id, unat seL4_CapInitThreadCNode) \<mapsto>c si_cnode_cap \<and>*
       (si_cnode_id, unat cap_ptr) \<mapsto>c default_cap (object_type obj) {kobj_id}
                                                     (object_size_bits obj) dev \<and>*
       (si_cnode_id, unat free_cptr) \<mapsto>c default_cap (object_type obj) {kobj_id}
                                                       (object_size_bits obj) dev \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_chain)
    apply (rule_tac src_index=cap_ptr and
                    cnode_cap=si_cspace_cap and
                    cnode_cap'=si_cnode_cap and
                    root_size=si_cnode_size and
                    src_cap="default_cap (object_type obj) {kobj_id}
                                         (object_size_bits obj) dev" and
                    R=R in
           seL4_CNode_Copy_sep, (simp add: wfdc_obj_not_untyped offset_slot offset_slot'|clarsimp)+)
   apply (rule conjI)
    apply sep_solve
   apply (clarsimp simp: guard_equal_si_cspace_cap
                         guard_equal_si_cnode_cap word_bits_def)
  apply (simp add: well_formed_update_cap_rights_idem derived_cap_default)
  apply sep_solve
  done

(* This definition is a bit of a hack for the duplicate_cap_sep_helper_general lemma below.
   Originally it only supported CNodes and TCBs, but it has been extended with support for'
   duplicating frames *)
definition well_formed_obj_filter ::
  "(cdl_object_id \<Rightarrow> cdl_state \<Rightarrow> bool) \<Rightarrow> bool"
  where
  "well_formed_obj_filter obj_filter \<equiv>
     \<forall>spec obj_id obj.
        obj_filter obj_id spec \<and> cdl_objects spec obj_id = Some obj
        \<longrightarrow> (\<forall>oid sz dev. sz \<le> 32 \<longrightarrow> well_formed_cap (default_cap (object_type obj) oid sz dev))
            \<and> (well_formed spec \<longrightarrow> real_object_at obj_id spec)"

lemma wf_obj_filter_wfc:
  "\<lbrakk>well_formed_obj_filter obj_filter;
    obj_filter obj_id spec;
    cdl_objects spec obj_id = Some obj;
    sz \<le> 32\<rbrakk> \<Longrightarrow>
   well_formed_cap (default_cap (object_type obj) oid sz dev)"
  by (clarsimp simp: well_formed_obj_filter_def)

lemma wf_obj_filter_real_object_at:
  "\<lbrakk>well_formed_obj_filter obj_filter;
    well_formed spec;
    obj_filter obj_id spec;
    cdl_objects spec obj_id = Some obj\<rbrakk> \<Longrightarrow>
   real_object_at obj_id spec"
  by (clarsimp simp: well_formed_obj_filter_def)

lemma wf_obj_filter_cnode_or_tcb_at:
  "well_formed_obj_filter cnode_or_tcb_at"
  by (auto simp: well_formed_obj_filter_def object_at_real_object_at intro: cnode_or_tcb_at_wfc)

lemma wf_obj_filter_frame_at:
  "well_formed_obj_filter frame_at"
  by (auto simp: well_formed_obj_filter_def object_at_real_object_at intro: frame_at_wfc)

lemma duplicate_cap_sep_helper_general:
  "\<lbrakk>well_formed spec; distinct obj_ids;
   list_all (\<lambda>n. n < 2 ^ si_cnode_size) (map unat free_cptrs);
   well_formed_obj_filter obj_filter;
   (obj_id, free_cptr) \<in> set (zip [obj\<leftarrow>obj_ids. obj_filter obj spec] free_cptrs);
    set obj_ids = dom (cdl_objects spec)\<rbrakk>
  \<Longrightarrow>
  \<lbrace>\<guillemotleft>(si_cnode_id, unat free_cptr) \<mapsto>c NullCap \<and>*
     si_cap_at t orig_caps spec dev obj_id \<and>* si_objects \<and>* R\<guillemotright>\<rbrace>
    duplicate_cap spec orig_caps (obj_id, free_cptr)
  \<lbrace>\<lambda>_ s.
   \<guillemotleft>si_cap_at t (map_of (zip [obj\<leftarrow>obj_ids. obj_filter obj spec] free_cptrs))
                spec dev obj_id \<and>*
    si_cap_at t orig_caps spec dev obj_id \<and>* si_objects \<and>* R\<guillemotright> s\<rbrace>"
  apply (rule hoare_assume_pre)
  apply (clarsimp simp: duplicate_cap_def si_cap_at_def sep_conj_exists)
  apply (rule_tac x=free_cptr in hoare_exI)
  apply (frule map_of_zip_tuple_in, simp, simp)
  apply (frule in_set_zip1)
  apply (frule in_set_zip2)
  apply (subgoal_tac "\<exists>kobj_id. t obj_id = Some kobj_id \<and>
                       orig_caps obj_id = Some cap_ptr \<and>
                       cap_ptr < 2 ^ si_cnode_size")
   apply (clarsimp simp: si_objects_def Ball_set_list_all[symmetric])
   apply (wp hoare_drop_imps)
    apply (rule hoare_chain)
      apply (rule_tac free_cptr=free_cptr and cap_ptr=cap_ptr and dev = dev and
              R="(si_cnode_id, unat seL4_CapIRQControl) \<mapsto>c IrqControlCap \<and>* si_asid \<and>* R" in
              seL4_CNode_Copy_sep_helper)
        apply (rule unat_less_2_si_cnode_size, simp)
       apply simp
      apply (erule (2) wf_obj_filter_wfc)
      apply (frule (1) well_formed_object_size_bits_word_bits, simp add: word_bits_def)
     apply sep_solve
    apply sep_solve
   apply (rule conjI)
    apply (rule unat_less_2_si_cnode_size, simp)
   apply sep_solve
  apply clarsimp
  done

lemma duplicate_cap_sep_general:
  "\<lbrace>\<guillemotleft>(si_cnode_id, unat free_cptr) \<mapsto>c NullCap \<and>*
    si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} \<and>* si_objects \<and>* R\<guillemotright> and K (
    well_formed spec \<and> distinct obj_ids \<and>
    list_all (\<lambda>n. n < 2 ^ si_cnode_size) (map unat free_cptrs) \<and>
    well_formed_obj_filter obj_filter \<and>
    (obj_id, free_cptr) \<in> set (zip [obj\<leftarrow>obj_ids. obj_filter obj spec] free_cptrs) \<and>
    set obj_ids = dom (cdl_objects spec))\<rbrace>
      duplicate_cap spec orig_caps (obj_id, free_cptr)
  \<lbrace>\<lambda>_.
   \<guillemotleft>si_cap_at t (map_of (zip [obj\<leftarrow>obj_ids. obj_filter obj spec] free_cptrs))
                spec dev obj_id \<and>*
    si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} \<and>* si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_gen_asm)
  apply clarsimp
  apply (frule well_formed_finite [where obj_id=obj_id])
  apply (clarsimp simp: si_caps_at_def)
  apply (rule hoare_chain[where
   P'="\<guillemotleft>((si_cnode_id, unat free_cptr) \<mapsto>c NullCap \<and>* si_objects) \<and>*
        (\<And>* obj_id \<in> {obj_id. real_object_at obj_id spec}. si_cap_at t orig_caps spec dev obj_id) \<and>* R\<guillemotright>" and
   Q'="\<lambda>rv.\<guillemotleft>(si_cap_at t (map_of (zip [obj\<leftarrow>obj_ids. obj_filter obj spec]
            free_cptrs)) spec dev obj_id \<and>* si_objects) \<and>*
        (\<And>* obj_id \<in> {obj_id. real_object_at obj_id spec}. si_cap_at t orig_caps spec dev obj_id) \<and>* R\<guillemotright>"])
    apply (rule sep_set_conj_map_singleton_wp [where x=obj_id])
      apply simp
     apply (fastforce dest: in_set_zip1 simp: wf_obj_filter_real_object_at)
    apply (rule hoare_chain)
      apply (rule_tac t=t and R=R in duplicate_cap_sep_helper_general, fastforce+)
     apply sep_solve
    apply sep_solve
   apply sep_solve
  apply simp
  apply sep_solve
  done

lemmas duplicate_cap_sep = duplicate_cap_sep_general[where obj_filter=cnode_or_tcb_at]

lemma duplicate_caps_sep_helper:
  "\<lbrace>\<guillemotleft>si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} \<and>*
     (\<And>* (obj_id, free_cptr) \<in> set (zip [obj\<leftarrow>obj_ids. cnode_or_tcb_at obj spec] free_cptrs).
          (si_cnode_id, unat free_cptr) \<mapsto>c NullCap) \<and>*
        si_objects \<and>* R\<guillemotright> and K(
     well_formed spec \<and> distinct obj_ids \<and>
     list_all (\<lambda>n. n < 2 ^ si_cnode_size) (map unat free_cptrs) \<and>
     set obj_ids = dom (cdl_objects spec) \<and>
     length [obj\<leftarrow>obj_ids . cnode_or_tcb_at obj spec] \<le> length free_cptrs)\<rbrace>
    duplicate_caps spec orig_caps obj_ids free_cptrs
  \<lbrace>\<lambda>dup_caps.
    \<guillemotleft>si_caps_at t dup_caps spec dev {obj_id. cnode_or_tcb_at obj_id spec} \<and>*
    si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} \<and>* si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (clarsimp simp: duplicate_caps_def si_caps_at_def)
  apply (wp)
   apply (rule hoare_chain)
     apply (rule mapM_x_set_sep [where
           f="duplicate_cap spec orig_caps" and
           xs="zip [obj\<leftarrow>obj_ids . cnode_or_tcb_at obj spec] free_cptrs" and
           P="\<lambda>(obj_id,free_cptr). (si_cnode_id, unat free_cptr) \<mapsto>c NullCap" and
           Q="\<lambda>(obj_id,free_cptr). (si_cap_at t (map_of
                (zip [obj\<leftarrow>obj_ids. cnode_or_tcb_at obj spec] free_cptrs))
                spec dev obj_id)" and
           I="si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} \<and>* si_objects" and
           R=R])
      apply (rule distinct_zipI1, simp)
     apply (clarsimp simp: sep_conj_assoc)
     apply (rename_tac obj_id free_cptr)
     apply (wp sep_wp: duplicate_cap_sep [where obj_ids=obj_ids and free_cptrs=free_cptrs and t=t])
     apply (clarsimp simp: wf_obj_filter_cnode_or_tcb_at)
     apply sep_solve
    apply (clarsimp simp: sep_conj_assoc si_caps_at_def)
    apply sep_solve
   apply (subst (asm) sep_map_zip_fst, simp+)
   apply (clarsimp simp: sep_conj_assoc si_caps_at_def)
  apply sep_solve
  done

(* FIXME, move higher *)
lemma distinct_card':
  "\<lbrakk>distinct xs; set xs = A\<rbrakk> \<Longrightarrow> card (A) = length xs"
  by (clarsimp simp: distinct_card)

(* FIXME, move higher *)
lemma distinct_length_filter':
  "distinct xs \<Longrightarrow> length [x\<leftarrow>xs. P x] = card {x \<in> set xs. P x}"
  by (metis distinct_card' distinct_filter set_filter)

lemma duplicate_caps_sep_no_rv:
  "\<lbrace>\<guillemotleft>si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} \<and>*
     si_objects \<and>*
     si_objects_extra_caps' (set obj_ids) free_cptrs untyped_cptrs \<and>*
     R\<guillemotright> and K(well_formed spec \<and> distinct obj_ids \<and> distinct free_cptrs \<and>
    set obj_ids = dom (cdl_objects spec) \<and>
    list_all (\<lambda>n. n < 2 ^ si_cnode_size) (map unat free_cptrs) \<and>
    length obj_ids + card {obj_id. cnode_or_tcb_at obj_id spec} \<le> length free_cptrs \<and>
    free_cptrs' = drop (length obj_ids) free_cptrs)\<rbrace>
    duplicate_caps spec orig_caps obj_ids free_cptrs'
  \<lbrace>\<lambda>dup_caps s.
    \<guillemotleft>si_caps_at t dup_caps spec dev {obj_id. cnode_or_tcb_at obj_id spec} \<and>*
     si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} \<and>*
     si_objects \<and>*
     si_objects_extra_caps (set obj_ids) free_cptrs untyped_cptrs spec \<and>*
     R\<guillemotright> s\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (rule hoare_chain)
    apply (rule duplicate_caps_sep_helper[where t=t and
           free_cptrs=free_cptrs' and
           R="\<lambda>s. \<exists>untyped_caps all_available_ids.
             ((\<And>* (cptr, y) \<in> set (zip untyped_cptrs untyped_caps). (si_cnode_id, unat cptr) \<mapsto>c y) \<and>*
              (\<And>* obj_id\<in>all_available_ids. obj_id \<mapsto>o Untyped) \<and>*
              (\<And>* map (\<lambda>free_cptr. (si_cnode_id, unat free_cptr) \<mapsto>c NullCap)
                       (drop (card {obj_id. cnode_or_tcb_at obj_id spec})
                       (drop (length obj_ids) free_cptrs))) \<and>* R) s"], simp+)
   apply (clarsimp simp: Ball_set_list_all[symmetric] dest!: in_set_dropD)
   apply (rule conjI)
    apply (clarsimp simp: si_objects_extra_caps'_def sep_conj_exists sep_conj_assoc)
    apply (rule_tac x=untyped_caps in exI)
    apply (rule_tac x=all_available_ids in exI)
    apply (subst sep_map_zip_snd_take, simp+)
    apply (subst (asm) drop_take_drop[symmetric,
           where a="card (dom (cdl_objects spec))"
             and b="length [obj\<leftarrow>obj_ids. cnode_or_tcb_at obj spec]"])
    apply (subst take_drop)
    apply clarsimp
    apply (clarsimp simp: distinct_card' distinct_length_filter')
    apply (subst sep_list_conj_sep_map_set_conj, simp)
    apply (subst (asm) sep.prod.union_disjoint, simp+)
     apply (simp add: drop_take)
     apply (subst add.commute)
     apply (erule distinct_take_drop_append)
    apply sep_solve
   apply (subst (asm) distinct_card [symmetric], simp+)+
   apply (subst distinct_card [symmetric], simp+)+
   apply (fastforce dest!: in_set_dropD)
  apply (clarsimp simp: si_objects_extra_caps_def sep_conj_exists sep_conj_assoc)
  apply (rule_tac x=untyped_caps in exI)
  apply (rule_tac x=all_available_ids in exI)
  apply (subst add.commute)
  apply (subst (asm) distinct_card [symmetric], simp)+
   apply (clarsimp simp: distinct_card' distinct_length_filter')
  apply (subst (asm) sep_list_conj_sep_map_set_conj, simp)
  apply sep_solve
  done

lemma duplicate_caps_rv:
  "\<lbrace>\<guillemotleft>si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} \<and>*
      si_objects \<and>*
      si_objects_extra_caps' (set obj_ids) free_cptrs untyped_cptrs \<and>* R\<guillemotright>\<rbrace>
  duplicate_caps spec orig_caps obj_ids free_cptrs'
   \<lbrace>\<lambda>dup_caps _. dup_caps = map_of (zip [obj\<leftarrow>obj_ids. cnode_or_tcb_at obj spec] free_cptrs')\<rbrace>"
  apply (clarsimp simp: duplicate_caps_def)
  apply (wp, clarsimp)
  done

lemma duplicate_caps_sep:
  "\<lbrace>\<guillemotleft>(si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} \<and>*
     si_objects \<and>*
     si_objects_extra_caps' (dom (cdl_objects spec)) free_cptrs_orig untyped_cptrs \<and>* R) and
      K (well_formed spec \<and>
         distinct obj_ids \<and>
         set obj_ids = dom (cdl_objects spec) \<and>
         list_all (\<lambda>n. n < 2 ^ si_cnode_size) free_cptrs_orig \<and>
         free_cptrs = drop (length obj_ids) free_cptrs_orig \<and>
         distinct free_cptrs_orig \<and>
         length obj_ids + card {obj_id. cnode_or_tcb_at obj_id spec} \<le> length free_cptrs_orig)\<guillemotright>\<rbrace>
  duplicate_caps spec orig_caps obj_ids free_cptrs
   \<lbrace>\<lambda>dup_caps.
    \<guillemotleft>(si_caps_at t dup_caps spec dev {obj_id. cnode_or_tcb_at obj_id spec} \<and>*
      si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} \<and>*
      si_objects \<and>*
      si_objects_extra_caps (dom (cdl_objects spec)) free_cptrs_orig untyped_cptrs spec \<and>* R) and
      K (dup_caps = map_of (zip [obj\<leftarrow>obj_ids. cnode_or_tcb_at obj spec] free_cptrs))\<guillemotright> \<rbrace>"
  apply clarsimp
  apply (rule hoare_gen_asm_conj)
  apply (rule hoare_conjI, elim conjE)
   apply (rule hoare_chain[OF duplicate_caps_sep_no_rv], simp+)
   apply (simp add: list_all_iff unat_less_2_si_cnode_size' | rule conjI)+
  apply (wp duplicate_caps_rv, simp)
  done

end

