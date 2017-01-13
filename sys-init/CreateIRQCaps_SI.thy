(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory CreateIRQCaps_SI
imports
  "../proof/capDL-api/IRQ_DP"
  ObjectInitialised_SI
  RootTask_SI
  SysInit_SI
begin

(*****************
 * Helper lemmas *
 *****************)



lemma si_cnode_caps:
  "si_cnode_cap = si_cspace_cap"
  by (simp add: si_cnode_cap_def si_cspace_cap_def)

lemma hoare_grab_exs2:
  "(\<And>x. P x \<Longrightarrow> \<lbrace>P' x\<rbrace> f \<lbrace>Q\<rbrace>) \<Longrightarrow> \<lbrace>\<lambda>s. \<exists>x. P x \<and> P' x s\<rbrace> f \<lbrace>Q\<rbrace>"
  by (fastforce simp: valid_def)

lemma sep_map_irq_sep_irq_node:
  "(irq \<mapsto>irq k_irq_table irq \<and>* R) s
  \<Longrightarrow> sep_irq_node s irq = Some (k_irq_table irq)"
  by (fastforce simp: sep_map_irq_def sep_conj_def
                      sep_disj_sep_state_def sep_state_disj_def
                      plus_sep_state_def sep_state_add_def
                      map_disj_def map_add_Some_iff)

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

lemma sep_conj_existL:
  "(P \<and>* Q) s \<Longrightarrow> \<exists>s. P s"
  by (auto simp: sep_conj_def)

lemma sep_conj_existR:
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
  apply (simp add: offset_slot_si_cnode_size' guard_equal_si_cspace_cap word_bits_def)
  done

lemma create_irq_caps_sep_helper:
  "\<lbrace>\<guillemotleft>((\<And>* cptr \<in> set (take (card (used_irqs spec)) free_cptrs).
           ((si_cnode_id, unat cptr) \<mapsto>c NullCap)) \<and>*
      si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} \<and>*
      si_objects \<and>* si_irq_nodes spec \<and>* R)  and
   K (well_formed spec \<and>
      list_all (\<lambda>n. n < 2 ^ si_cnode_size) free_cptrs \<and>
      distinct free_cptrs \<and>
      card (used_irqs spec) \<le> length free_cptrs)\<guillemotright> \<rbrace>
  create_irq_caps spec free_cptrs
   \<lbrace>\<lambda>rv s. \<exists>(t'::32 word \<Rightarrow> 32 word option).
    \<guillemotleft>(irqs_empty spec t' (used_irqs spec) \<and>*
      si_irq_caps_at (fst rv) spec (used_irqs spec) \<and>*
      si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} \<and>*
      si_objects \<and>* R)
    and K ((map_of (zip (used_irq_list spec) free_cptrs), drop (card (used_irqs spec)) free_cptrs) = rv \<and>
    inj_on t' (used_irq_nodes spec) \<and>
    dom t' = used_irq_nodes spec)\<guillemotright> s\<rbrace>"
  including no_pre
  apply clarsimp
  apply (rule hoare_gen_asm_conj)
  apply (clarsimp simp: create_irq_caps_def si_irq_nodes_def2 sep_conj_exists)
  apply wp
  apply simp
  apply (rule hoare_grab_exs2)
  apply (rule_tac x="(\<lambda>obj_id. Some ((k_irq_table \<circ> inv (cdl_irq_node spec)) obj_id))
                     |` used_irq_nodes spec" in hoare_exI)

  apply (rule_tac P1 = "\<lambda>(irq,free_cptr). (si_cnode_id, unat free_cptr) \<mapsto>c NullCap \<and>*
                                           irq \<mapsto>irq k_irq_table irq \<and>*
                                           k_irq_table irq \<mapsto>o IRQNode empty_irq_node" and
                  Q1 = "\<lambda>(irq,free_cptr). irq_empty spec ((\<lambda>obj_id. Some ((k_irq_table \<circ> inv (cdl_irq_node spec)) obj_id))
                                                           |` used_irq_nodes spec) irq \<and>*
                                          si_irq_cap_at (map_of (zip (used_irq_list spec) free_cptrs)) spec irq" and
                  I1 = "si_objects" and
                  R1 = "si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} \<and>*
                        R" in hoare_chain [OF mapM_x_set_sep])
     apply (metis distinct_zipI2)
    apply (clarsimp split:prod.splits)
    apply (clarsimp simp: sep_conj_assoc)
    apply (wp sep_wp: create_irq_cap_sep, simp+)
    apply (rule conjI)
     apply (clarsimp simp: sep_conj_assoc sep_conj_exists)
     apply sep_solve
    apply (frule well_formed_inj_cdl_irq_node)
    apply (frule set_zip_leftD)
    apply (frule in_set_zip2)
    apply (simp add: map_of_zip_tuple_in list_all_iff unat_less_2_si_cnode_size
                     restrict_map_def used_irq_nodes_def)

   apply (subst sep_list_conj_sep_map_set_conj [symmetric], erule distinct_zipI2)
   apply (subst (asm) sep_list_conj_sep_map_set_conj [symmetric, where xs = "used_irq_list spec", simplified])
   apply (subst split_beta')
   apply (subst sep_list_conj_map_add)
   apply (subst zip_take_length [symmetric])
   apply (subst split_beta' [symmetric])+
   apply (subst map_zip_snd', simp)

   apply (subst (asm) (3) append_take_drop_id [where n="card (used_irqs spec)" and xs=free_cptrs, symmetric])
   apply (subst map_zip_fst', simp)
   apply (subst sep_list_conj_sep_map_set_conj, fastforce simp: used_irq_list_def)
   apply (simp add: comp_def)
   apply sep_solve

  apply simp
  apply (subst (asm) sep_list_conj_sep_map_set_conj [symmetric], erule distinct_zipI2)
  apply (subst (asm) map_zip_fst', simp)
  apply (subst (asm) sep_list_conj_map_add)
  apply (subst (asm) sep_list_conj_sep_map_set_conj,
         metis used_irq_list_def distinct_sorted_list_of_set)
  apply (subst (asm) sep_list_conj_sep_map_set_conj,
         metis used_irq_list_def distinct_sorted_list_of_set)
  apply (clarsimp simp: irqs_empty_def si_irq_caps_at_def)
  apply (rule conjI)
   apply sep_solve
  apply (frule well_formed_inj_cdl_irq_node)
  apply (fastforce simp: inj_on_def used_irq_nodes_def)
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
  by (metis imageI map_add_eval_right)

lemma object_empty_map_add:
  "\<lbrakk>dom t = obj_ids; map_disj t t'\<rbrakk>
  \<Longrightarrow> objects_empty spec t obj_ids = objects_empty spec (t++t') obj_ids"
  apply (clarsimp simp: objects_empty_def)
  apply (rule sep.prod.cong, simp)
  apply (subst object_empty_cong [where t'="t++t'" and t=t], simp_all)
  by (metis map_add_eval_left)

lemma si_caps_at_map_add:
  "\<lbrakk>dom t = obj_ids; map_disj t t'\<rbrakk>
  \<Longrightarrow> si_caps_at t si_caps spec dev obj_ids = si_caps_at (t++t') si_caps spec dev obj_ids"
  apply (clarsimp simp: si_caps_at_def)
  apply (rule sep.prod.cong, simp)
  apply (subst si_cap_at_cong [where t'="t++t'" and t=t], simp_all)
  by (metis map_add_eval_left)


lemma inj_on_map_add:
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

lemma inter_emptyI:
  "\<lbrakk>\<And>x. x \<in> A \<and> x \<in> B \<Longrightarrow> False\<rbrakk>  \<Longrightarrow> A \<inter> B = {}"
  by auto

lemma ran_inter_emptyI:
  "\<lbrakk>\<And>x a b. f a = Some x \<and> g b = Some x \<Longrightarrow> False\<rbrakk> \<Longrightarrow> ran f \<inter> ran g = {}"
  apply (rule inter_emptyI)
  apply (auto simp: ran_def)
  done

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
  apply clarsimp
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
    =
  ((\<And>* cptr \<in> set (take (card (used_irqs spec)) free_cptrs). (si_cnode_id, unat cptr) \<mapsto>c NullCap) \<and>*
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


lemma create_irq_caps_sep:
  "\<lbrace>\<lambda>s. \<exists>t_real.
    \<guillemotleft>(objects_empty spec t_real {obj_id. real_object_at obj_id spec} \<and>*
      si_caps_at t_real orig_caps spec dev {obj_id. real_object_at obj_id spec} \<and>*
      si_objects \<and>*
      si_objects_extra_caps' {obj_id. real_object_at obj_id spec} free_cptrs_orig untyped_cptrs \<and>*
      si_irq_nodes spec \<and>* R)  and
   K (well_formed spec \<and>
      distinct free_cptrs_orig \<and>
      list_all (\<lambda>n. n < 2 ^ si_cnode_size) free_cptrs \<and>
      card (used_irqs spec) \<le> length free_cptrs \<and>
      inj_on t_real {obj_id. real_object_at obj_id spec} \<and>
      dom t_real = {obj_id. real_object_at obj_id spec} \<and>
      dom orig_caps = {obj_id. real_object_at obj_id spec} \<and>
      free_cptrs = drop (card {obj_id. real_object_at obj_id spec}) free_cptrs_orig)\<guillemotright> s\<rbrace>
  create_irq_caps spec free_cptrs
   \<lbrace>\<lambda>rv s. \<exists>(t::32 word \<Rightarrow> 32 word option).
    \<guillemotleft>(objects_empty spec t {obj_id. real_object_at obj_id spec} \<and>*
      irqs_empty spec t (used_irqs spec) \<and>*
      si_caps_at t orig_caps spec dev {obj_id. real_object_at obj_id spec} \<and>*
      si_irq_caps_at (fst rv) spec (used_irqs spec) \<and>*
      si_objects \<and>*
      si_objects_extra_caps' (dom (cdl_objects spec)) free_cptrs_orig untyped_cptrs \<and>*
      R) and
    K ((map_of (zip (used_irq_list spec) free_cptrs), drop (card (used_irqs spec)) free_cptrs) = rv \<and>
       inj_on t (dom (cdl_objects spec)) \<and> dom t = dom (cdl_objects spec))\<guillemotright> s\<rbrace>"
  apply (rule hoare_ex_pre)
  apply (rule hoare_gen_lifted_asm)
  apply (elim conjE)
  apply (subst si_objects_extra_caps'_split, assumption+)
  apply (rule hoare_chain [OF create_irq_caps_sep_helper, where orig_caps1=orig_caps])
   apply (rule pred_andI)
    apply sep_solve
   apply clarsimp
  apply clarsimp
  apply (rule_tac x="t_real ++ t'" in exI)
  apply clarsimp
  apply (frule well_formed_objects_real_or_irq)
  apply (frule well_formed_objects_only_real_or_irq)
  apply (clarsimp simp: used_irq_nodes_def)
  apply (subgoal_tac "map_disj t_real t'")
   apply (rule conjI)
    apply (subst object_empty_map_add [symmetric], assumption+)
    apply (subst irq_empty_map_add [symmetric],simp add: used_irq_nodes_def)
    apply (subst si_caps_at_map_add [symmetric], assumption+)
    apply (clarsimp simp: si_objects_extra_caps'_def sep_conj_exists sep_conj_assoc)
    apply (rule_tac x=untyped_caps in exI)
    apply (rule_tac x=all_available_ids in exI)
    apply sep_solve
   apply (rule conjI)
    apply (rule inj_on_map_add, simp+)
     apply (rule irq_empty_objects_empty_ran_distinct, sep_solve, simp+)
   apply (metis sup_commute)
  apply (clarsimp simp: map_disjI)
  done

end
