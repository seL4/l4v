(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory CreateIRQCaps_SI
  imports
    DSpecProofs.IRQ_DP
    ObjectInitialised_SI
    RootTask_SI
    SysInitSpec.SysInit_SI
    Mapped_Separating_Conjunction
    Sep_Algebra.Sep_Fold_Cancel
begin

(*****************
 * Helper lemmas *
 *****************)

lemma si_cnode_caps:
  "si_cnode_cap = si_cspace_cap"
  by (simp add: si_cnode_cap_def si_cspace_cap_def)

(*********************************************************************************
 * A new definition of si_irq_nodes that states that the mapping is injective. *
 *********************************************************************************)

lemma sep_map_o_distinct:
  "(obj_id \<mapsto>o obj \<and>* obj_id' \<mapsto>o obj') s \<Longrightarrow> obj_id \<noteq> obj_id'"
  by (fastforce simp: sep_map_o_def sep_map_general_def sep_conj_def object_to_sep_state_def
                      sep_disj_sep_state_def sep_state_disj_def
                      map_disj_def dom_def disjoint_iff_not_equal)

lemma sep_any_map_o_false_eq:
  "(obj_id \<mapsto>o - \<and>* obj_id \<mapsto>o -) = sep_false"
  by (fastforce simp: sep_any_def sep_map_o_def sep_map_general_def sep_conj_def
                      object_to_sep_state_def sep_disj_sep_state_def sep_state_disj_def
                      map_disj_def dom_def disjoint_iff_not_equal)

lemma sep_any_map_o_false:
  "(obj_id \<mapsto>o - \<and>* obj_id \<mapsto>o -) s \<Longrightarrow> False"
  by (simp add: sep_any_map_o_false_eq)

lemma sep_map_o_false:
  "(obj_id \<mapsto>o obj \<and>* obj_id \<mapsto>o obj') s \<Longrightarrow> False"
  by (metis sep_map_o_distinct)

lemma sep_map_o_any_distinct_list:
  "((f x) \<mapsto>o - \<and>* \<And>* map (\<lambda>x. (f x) \<mapsto>o -) xs) s
  \<Longrightarrow> x \<notin> set xs"
  apply clarsimp
  apply (subst (asm) sep_list_conj_map_remove1, assumption)
  apply (sep_drule sep_any_map_o_false)
  apply clarsimp
  done

lemma sep_any_map_o_inj_on:
  "(\<And>* map (\<lambda>x. (f x) \<mapsto>o -) xs) s
  \<Longrightarrow> inj_on f (set xs)"
  apply (induct xs arbitrary: s)
   apply clarsimp
  apply clarsimp
  apply (rule conjI)
   apply (clarsimp simp: sep_conj_def)
  apply clarsimp
  apply (frule sep_map_o_any_distinct_list)
  apply simp
  done

lemma sep_any_map_o_inj_on_set:
  "\<lbrakk>(\<And>* x \<in> A. (f x) \<mapsto>o -) s; finite A\<rbrakk>
  \<Longrightarrow> inj_on f A"
  apply (drule sep_map_set_conj_sep_list_conj [where P="\<lambda>x. (f x) \<mapsto>o -"])
  apply clarsimp
  apply (erule sep_any_map_o_inj_on)
  done

lemma sep_map_o_inj_on_set:
  "\<lbrakk>(\<And>* x \<in> A. (f x) \<mapsto>o obj) s; finite A\<rbrakk>
  \<Longrightarrow> inj_on f A"
  apply (rule sep_any_map_o_inj_on_set [rotated, where s=s], assumption)
  apply (erule sep_map_set_conj_impl)
   apply (fastforce simp: sep_any_def)
  apply simp
  done

lemma sep_conj_existL: (* FIXME: move to SepAlgebra *)
  "(P \<and>* Q) s \<Longrightarrow> \<exists>s. P s"
  by (auto simp: sep_conj_def)

lemma sep_conj_existR: (* FIXME: move to SepAlgebra *)
  "(P \<and>* Q) s \<Longrightarrow> \<exists>s. Q s"
  by (auto simp: sep_conj_def)

lemma si_irq_nodes_def2:
  "si_irq_nodes spec =
     (\<lambda>s. \<exists>k_irq_table. inj_on k_irq_table (used_irqs spec) \<and>
                        (\<And>* irq\<in>used_irqs spec. irq \<mapsto>irq k_irq_table irq \<and>*
                                                 k_irq_table irq \<mapsto>o IRQNode empty_irq_node) s)"
  apply (rule ext)
  apply (clarsimp simp: si_irq_nodes_def)
  apply (rule iffI)
   apply clarsimp
   apply (rule_tac x=k_irq_table in exI, simp)
   apply (subst (asm) sep.prod.distrib)
   apply (drule sep_conj_existR, clarsimp)
    apply (erule sep_map_o_inj_on_set) (* Why doesn't sep_rule work? *)
   apply simp
  apply blast
  done


(*******************************************
 * The actual proofs about create_irq_caps *
 *******************************************)

lemma well_formed_default_irq_node_empty:
  "\<lbrakk>well_formed spec; irq \<in> used_irqs spec\<rbrakk>
    \<Longrightarrow> object_at (\<lambda>obj. object_default_state obj = IRQNode empty_irq_node) (cdl_irq_node spec irq) spec"
  apply (frule (1) well_formed_used_irqs_have_irq_node, clarsimp)
  apply (frule (1) well_formed_irq_is_irq_node)
  apply (frule (1) well_formed_size_irq_node)
  apply (clarsimp simp: object_at_def empty_irq_node_def object_default_state_def2
                        is_irq_node_def object_size_bits_def
                 split: cdl_object.splits)
  done

lemma create_irq_cap_sep:
  "\<lbrace>\<guillemotleft>(si_cnode_id, unat free_cptr) \<mapsto>c NullCap \<and>*
      irq \<mapsto>irq kernel_irq_id \<and>*
      kernel_irq_id \<mapsto>o (IRQNode empty_irq_node) \<and>*
      si_objects \<and>* R\<guillemotright> and
    K(well_formed spec \<and>
      irq \<in> used_irqs spec \<and>
      t' (cdl_irq_node spec irq) = Some kernel_irq_id \<and>
      irq_caps irq = Some free_cptr \<and>
      free_cptr < 2 ^ si_cnode_size)\<rbrace>
   create_irq_cap spec (irq, free_cptr)
   \<lbrace>\<lambda>_.
    \<guillemotleft>irq_empty spec t' irq \<and>*
     si_irq_cap_at irq_caps spec irq \<and>*
     si_objects \<and>*
     R\<guillemotright>\<rbrace>"
  apply (rule hoare_gen_asm, clarsimp)
  apply (frule (1) well_formed_used_irqs_have_irq_node, clarsimp)
  apply (frule (1) well_formed_default_irq_node_empty, clarsimp simp: object_at_def)
  apply (clarsimp simp: create_irq_cap_def si_objects_def si_cnode_caps
                        irq_empty_def irq_initialised_general_def
                        si_irq_cap_at_def sep_conj_assoc)
  apply (wp add: hoare_drop_imp sep_wp: seL4_IRQHandler_IRQControl_Get, simp)
  apply (rule conjI)
   apply sep_solve
  apply (simp add: offset_slot_si_cnode_size' guard_equal_si_cspace_cap)
  done

lemma well_formed_spec_used_irqs_compute:
  assumes "well_formed spec"
  shows "used_irq_list_compute spec = used_irq_list spec"
  using assms
  unfolding used_irq_list_compute_def used_irq_list_def used_irqs_def
            sorted_list_of_set_eq_filter minBound_word
  apply (rule_tac filter_cong[OF refl, OF iffI])
   apply (clarsimp simp add: Option.is_none_def)
   apply (frule well_formed_cap_to_irq_object,assumption)
    apply (simp add: well_formed_cdl_irq_node_irq_nodes)
   apply (force dest: well_formed_inj_cdl_irq_node[THEN injD]
                      well_formed_cap_to_irq_object
                simp add: all_caps_def)
  apply (clarsimp simp add: Option.is_none_def well_formed_all_caps_cap_irq)
  done


lemma fun_on_prod: "f = (\<lambda>a. f (fst a, snd a))" (* FIXME: move to Lib *)
  by clarsimp

lemma map_snd_zip_take[simp]: (* FIXME: move to Lib *)
  "map (\<lambda>x. f (snd x)) (zip xs ys) = map f (take (length xs) ys) "
  apply (induct ys arbitrary: xs; clarsimp?)
  apply (case_tac xs; clarsimp)
  done

lemma map_fst_zip_take[simp]: (* FIXME: move to Lib *)
  "map (\<lambda>x. f (fst x)) (zip xs ys) = map f (take (length ys) xs) "
  apply (induct ys arbitrary: xs; clarsimp?)
  apply (case_tac xs; clarsimp)
  done


lemma irq_initialised_general_def3:
  "\<forall>irq\<in>used_irqs spec. t (cdl_irq_node spec irq) = Some (cdl_irq_node spec irq) \<Longrightarrow> irq \<in> used_irqs spec \<Longrightarrow>
    irq_initialised_general spec t obj_trans arrow irq  =
     (object_initialised_general spec t obj_trans arrow (cdl_irq_node spec irq) \<and>*
      irq \<mapsto>irq  (cdl_irq_node spec irq)) "
  apply (rule ext, clarsimp simp: irq_initialised_general_def object_initialised_general_def
                      sep_conj_exists sep_conj_ac)
  apply (drule (1) bspec)
  apply (rule iffI; clarsimp)
  done

definition si_irq_nodes :: "cdl_state \<Rightarrow> sep_state \<Rightarrow> bool" where
  "si_irq_nodes spec \<equiv> \<lambda>s.
     (\<And>* irq\<in>used_irqs spec. irq \<mapsto>irq (cdl_irq_node spec irq) \<and>*
                             (cdl_irq_node spec irq) \<mapsto>o IRQNode empty_irq_node) s"


lemma sep_fold_cong1: (* FIXME: move to SepAlgebra *)
  "(\<forall>x\<in>(set xs). P x = P' x) \<Longrightarrow> sep_fold P Q R xs = sep_fold P' Q R xs"
  apply (clarsimp simp: sep_fold_def)
  apply (smt (verit) foldr_cong)
  done

lemma sep_fold_cong2: (* FIXME: move to SepAlgebra *)
  "(\<forall>x\<in>(set xs). Q x = Q' x) \<Longrightarrow>  sep_fold P Q R xs = sep_fold P Q' R xs"
  apply (clarsimp simp: sep_fold_def)
  apply (smt (verit) foldr_cong)
  done

lemma create_irq_caps_sep:
  "\<forall>irq\<in>used_irqs spec. t (cdl_irq_node spec irq) = Some (cdl_irq_node spec irq) \<Longrightarrow>
    \<lbrace>\<guillemotleft>((\<And>* cptr \<in> set (list_take_region (card (used_irqs spec)) free_cptrs).
             ((si_cnode_id, unat cptr) \<mapsto>c NullCap)) \<and>*
        si_objects \<and>* si_irq_nodes spec \<and>* R)  and
     K (well_formed spec \<and> valid_slot_region free_cptrs \<and>
        card (used_irqs spec) \<le> length_region free_cptrs)\<guillemotright> \<rbrace>
    create_irq_caps spec free_cptrs
     \<lbrace>\<lambda>rv.
      \<guillemotleft>((irqs_empty spec t (used_irqs spec) and
         K ((map_of (zip_region (used_irq_list spec) free_cptrs),
             drop_region (card (used_irqs spec)) free_cptrs) = rv)) \<and>*
        si_irq_caps_at (fst rv) spec (used_irqs spec) \<and>*
        si_objects \<and>* R)\<guillemotright> \<rbrace>"
  apply clarsimp
  apply (rule hoare_gen_asm_conj)
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp: create_irq_caps_def well_formed_spec_used_irqs_compute)
  apply wpsimp
   apply (subst fun_on_prod)
   apply (rule sep_hoare_fold_mapM_x[
                 OF create_irq_cap_sep[
                      where irq_caps="map_of (zip_region (used_irq_list spec) free_cptrs)"
                        and kernel_irq_id="cdl_irq_node spec (fst irq)"
                        and t'=t for irq,
                      simplified sep_wp_simp]])
  apply clarsimp
  apply sep_flatten
  apply sep_fold_cancel+
   apply (clarsimp simp: irq_empty_def)
   apply (subst sep_fold_cong2)
    apply (intro ballI)
    apply (subst irq_initialised_general_def3)
      apply assumption
     apply (fastforce elim!: in_set_zipE)
    apply (rule refl)
   apply sep_flatten
   apply (rule sep_map_sep_foldI)
   apply (clarsimp simp: sep_list_conj_sep_map_set_conj sep.prod.distrib)
   apply sep_flatten
   apply clarsimp
   apply (subst map_snd_zip_take)
   apply clarsimp
   apply (clarsimp simp: sep_list_conj_sep_map_set_conj, sep_cancel)
   apply (clarsimp simp: si_irq_nodes_def sep_conj_exists)
   apply (subst map_fst_zip_take, clarsimp simp: sep_list_conj_sep_map_set_conj sep.prod.distrib)
   apply sep_cancel+
   apply (subst map_fst_zip_take, clarsimp simp: sep_list_conj_sep_map_set_conj sep.prod.distrib)
   apply sep_cancel+
   apply (subst (asm) map_fst_zip_take, clarsimp simp: sep_list_conj_sep_map_set_conj sep.prod.distrib)
   apply (subst (asm) map_fst_zip_take, clarsimp simp: sep_list_conj_sep_map_set_conj sep.prod.distrib)
   apply (clarsimp simp: irqs_empty_def si_irq_caps_at_def irq_empty_def
                         irq_initialised_general_def3 sep.prod.distrib)
   apply sep_cancel+
  apply (clarsimp simp: sep_conj_sep_true')
  apply (intro conjI; fastforce?)
    apply (fastforce elim: in_set_zipE)
   apply (fastforce elim: in_set_zipE)
  apply (frule valid_slot_region_leI, drule valid_slot_region_less_all)
  apply (clarsimp simp: list_all_def)
  apply (metis in_set_zipE length_used_irq_list zip_take_length)
  done

lemma create_irq_caps_sep':
  "\<forall>irq\<in>used_irqs spec. t (cdl_irq_node spec irq) = Some (cdl_irq_node spec irq) \<Longrightarrow>
  \<lbrace>\<guillemotleft>((\<And>* cptr \<in> set_region (free_cptrs).
           ((si_cnode_id, unat cptr) \<mapsto>c NullCap)) \<and>*
      si_objects \<and>* si_irq_nodes spec \<and>* R)  and
   K (well_formed spec \<and> valid_slot_region free_cptrs \<and>
      card (used_irqs spec) \<le> length_region free_cptrs)\<guillemotright> \<rbrace>
  create_irq_caps spec free_cptrs
   \<lbrace>\<lambda>_.
    \<guillemotleft>(irqs_empty spec t (used_irqs spec) \<and>*
      si_irq_caps_at (map_of (zip_region (used_irq_list spec) free_cptrs)) spec (used_irqs spec) \<and>*
     (\<And>* cptr \<in> set_region (drop_region (card (used_irqs spec)) free_cptrs).
           ((si_cnode_id, unat cptr) \<mapsto>c NullCap)) \<and>*
      si_objects \<and>* R)
    \<guillemotright> \<rbrace>"
  apply (erule hoare_chain[OF create_irq_caps_sep])
   apply (clarsimp simp: pred_conj_def)
   prefer 2 (* instantiate schematic *)
   apply (clarsimp simp: pred_conj_def cong del: prod.cong_simp)
   apply sep_solve
  apply sep_cancel+
  apply (sep_drule sep_map_set_conj_set_take_drop[where n="card (used_irqs spec)"])
   apply clarsimp
  apply sep_cancel+
  done


(*****************************************************************************
 * The above lemma has an injection on just the IRQs.                        *
 * We take the above proof, and join it with the result of CreateObjects     *
 * to produce an injection on all objects.                                   *
 *                                                                           *
 * The sum of the two injections "t_irqs" and "t_real" is injective because: *
 *  - Each individual relation is injective                                  *
 *  - The domains are separate                                               *
 *  - The ranges are separate                                                *
 *                                                                           *
 * The first two are easily true.                                            *
 * The last one is hard and only true because we have                        *
     obj_id \<mapsto>o Untyped \<and>* obj_id \<mapsto> IRQ, and so the obj_ids are distinct.   *
 *****************************************************************************)

lemma irq_empty_cong:
  "t (cdl_irq_node spec irq) = t' (cdl_irq_node spec irq)
  \<Longrightarrow> irq_empty spec t irq = irq_empty spec t' irq"
  by (clarsimp simp: irq_empty_def irq_initialised_general_def)

lemma object_empty_cong:
  "t obj_id = t' obj_id
  \<Longrightarrow> object_empty spec t obj_id = object_empty spec t' obj_id"
  by (clarsimp simp: object_empty_def object_initialised_general_def)

lemma si_cap_at_cong:
  "t obj_id = t' obj_id
  \<Longrightarrow> si_cap_at  t si_caps spec dev obj_id = si_cap_at  t' si_caps spec dev obj_id"
  by (clarsimp simp: si_cap_at_def)

lemma irq_empty_map_add:
  "\<lbrakk>dom t' = cdl_irq_node spec ` irqs\<rbrakk>
  \<Longrightarrow> irqs_empty spec t' irqs = irqs_empty spec (t++t') irqs"
  apply (clarsimp simp: irqs_empty_def)
  apply (rule sep.prod.cong, simp)
  apply (subst irq_empty_cong [where t'="t++t'" and t=t'], simp_all)
  apply (metis imageI map_add_eval_right)
  done

lemma object_empty_map_add:
  "\<lbrakk>dom t = obj_ids; map_disj t t'\<rbrakk>
  \<Longrightarrow> objects_empty spec t obj_ids = objects_empty spec (t++t') obj_ids"
  apply (clarsimp simp: objects_empty_def)
  apply (rule sep.prod.cong, simp)
  apply (subst object_empty_cong [where t'="t++t'" and t=t], simp_all)
  apply (metis map_add_eval_left)
  done

lemma si_caps_at_map_add:
  "\<lbrakk>dom t = obj_ids; map_disj t t'\<rbrakk>
  \<Longrightarrow> si_caps_at t si_caps spec dev obj_ids = si_caps_at (t++t') si_caps spec dev obj_ids"
  apply (clarsimp simp: si_caps_at_def)
  apply (rule sep.prod.cong, simp)
  apply (subst si_cap_at_cong [where t'="t++t'" and t=t], simp_all)
  apply (metis map_add_eval_left)
  done

lemma inj_on_map_add: (* FIXME: move to Lib or SepAlgebra *)
  "\<lbrakk>inj_on m (dom m); inj_on m' (dom m');
    dom m \<inter> dom m' = {}; ran m \<inter> ran m' = {}; A = dom m \<union> dom m'\<rbrakk>
  \<Longrightarrow> inj_on (m ++ m') A"
  apply (rule inj_onI)
  apply clarsimp
  apply (elim disjE)
     apply (metis inj_on_eq_iff inter_empty_not_both map_add_eval_left')
    apply (metis dom_ran map_add_comm map_add_eval_right orthD1)
   apply (metis dom_ran map_add_comm map_add_eval_right orthD1)
  apply (metis inj_on_def map_add_eval_right)
  done

lemma ran_inter_emptyI: (* FIXME: move to Lib *)
  "\<lbrakk>\<And>x a b. \<lbrakk>f a = Some x; g b = Some x\<rbrakk> \<Longrightarrow> False\<rbrakk> \<Longrightarrow> ran f \<inter> ran g = {}"
  by (meson disjoint_iff ranE)

lemma irq_empty_objects_empty_ran_distinct:
  "\<lbrakk>\<guillemotleft>irqs_empty spec t_irq (used_irqs spec) \<and>*
    objects_empty spec t_real {obj_id. real_object_at obj_id spec} \<and>* R\<guillemotright> s;
    well_formed spec;
    inj_on t_irq (cdl_irq_node spec ` used_irqs spec); dom t_irq = cdl_irq_node spec ` used_irqs spec;
    inj_on t_real {obj_id. real_object_at obj_id spec}; dom t_real = {obj_id. real_object_at obj_id spec}\<rbrakk>
  \<Longrightarrow> ran t_real \<inter> ran t_irq = {}"
  apply (frule well_formed_inj_cdl_irq_node)
  apply (clarsimp simp: irqs_empty_def irq_empty_def irq_initialised_general_def
                        objects_empty_def object_empty_def object_initialised_general_def)
  apply (rule ran_inter_emptyI)
  apply (frule domI [where m=t_real])
  apply (frule domI [where m=t_irq])
  apply clarsimp
  apply (rename_tac irq_obj_id obj_id irq)
  apply (subst (asm) sep.prod.remove, simp, assumption)
  apply (subst (asm) sep.prod.remove, simp, fast)
  apply (clarsimp simp: sep_conj_exists sep_conj_assoc)
  apply (sep_drule sep_map_o_false, simp)
  done

lemma si_objects_extra_caps'_split:
  "\<lbrakk>well_formed spec; distinct free_cptrs';
    free_cptrs = drop (card {obj_id. real_object_at obj_id spec}) free_cptrs'\<rbrakk> \<Longrightarrow>
   si_objects_extra_caps' {obj_id. real_object_at obj_id spec} free_cptrs' untyped_cptrs
   = ((\<And>*cptr \<in> set (take (card (used_irqs spec)) free_cptrs). (si_cnode_id, unat cptr) \<mapsto>c NullCap) \<and>*
      si_objects_extra_caps' (dom (cdl_objects spec)) free_cptrs' untyped_cptrs)"
  apply (frule well_formed_objects_card [symmetric])
  apply (subst (asm) add.commute)
  apply (clarsimp simp: si_objects_extra_caps'_def sep_conj_exists sep_conj_assoc)
  apply (subst take_drop_append [where a="card {obj_id. real_object_at obj_id spec}"
                                   and b="card (used_irqs spec)"])
  apply clarsimp
  apply (subst sep.prod.union_disjoint, (simp add: distinct_take_drop_append)+)
  apply (clarsimp simp: sep_conj_ac)
  done

end
