(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright 2025, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
   Arch-specific lemmas related to a heap based approach to the state relation.
*)

theory ArchHeapStateRelationLemmas
imports HeapStateRelation
begin

context Arch begin arch_global_naming

named_theorems HeapStateRelation_R_assms

lemmas ko_relations =
  cte_relation_def pte_relation_def ep_relation_cut_def ntfn_relation_cut_def
  other_aobj_relation_def tcb_relation_cut_def asid_pool_relation_def

lemma pspace_relation_tcbs_relation:
  "pspace_relation (kheap s) (ksPSpace s') \<Longrightarrow> tcbs_relation s s'"
  apply (clarsimp simp: map_relation_def)
  apply (rule conjI)
   apply (rule dom_eqI)
    apply (clarsimp simp: opt_map_def tcbs_of_kh_def split: option.splits)
    apply (drule (1) pspace_relation_absD)
    apply clarsimp
    apply (rename_tac ko, case_tac ko; simp add: tcb_relation_cut_def)
   apply (clarsimp simp: opt_map_def tcbs_of_kh_def split: option.splits)
   apply (erule (1) pspace_dom_relatedE)
   apply (clarsimp simp: obj_relation_cuts_def2 ko_relations
                  split: Structures_A.kernel_object.split_asm if_split_asm arch_kernel_obj.split_asm)
  apply (clarsimp simp: pspace_relation_def opt_map_def tcbs_of_kh_def split: option.splits)
  apply (rename_tac p tcb tcb')
  apply (drule_tac x=p in bspec, fastforce)
  apply (clarsimp simp: tcb_relation_cut_def)
  done

lemma pspace_relation_scs_relation:
  "\<lbrakk>pspace_relation (kheap s) (ksPSpace s')\<rbrakk> \<Longrightarrow> scs_relation s s'"
  apply (clarsimp simp: scs_relation_def)
  apply (rule context_conjI)
   apply (simp add: set_eq_subset)
   apply (intro conjI impI)
    apply (clarsimp simp: opt_map_def scs_of_kh_def split: option.splits)
    apply (drule (1) pspace_relation_absD)
    apply (clarsimp split: if_splits)
    apply (rename_tac ko, case_tac ko; simp)
   apply (clarsimp simp: opt_map_def split: option.splits)
   apply (erule (1) pspace_dom_relatedE)
   apply (clarsimp simp: obj_relation_cuts_def2 ko_relations scs_of_kh_def opt_map_def
                  split: Structures_A.kernel_object.split_asm if_split_asm arch_kernel_obj.split_asm)
  apply (clarsimp simp: pspace_relation_def opt_map_def split: option.splits)
  apply (rename_tac p ko sc'' n sc sc')
  apply (drule_tac x=p in bspec, fastforce)
  apply (case_tac ko; clarsimp split: if_splits)
  apply (clarsimp simp: sc_relation_def scs_of_kh_def opt_map_def cte_relation_def)
  done

lemma pspace_relation_eps_relation:
  "pspace_relation (kheap s) (ksPSpace s') \<Longrightarrow> eps_relation s s'"
  apply (clarsimp simp: map_relation_def)
  apply (rule conjI)
   apply (rule dom_eqI)
    apply (clarsimp simp: opt_map_def eps_of_kh_def split: option.splits)
    apply (drule (1) pspace_relation_absD)
    apply (clarsimp split: if_splits)
    apply (rename_tac ko, case_tac ko; simp add: ko_relations)
   apply (clarsimp simp: opt_map_def split: option.splits)
   apply (erule (1) pspace_dom_relatedE)
   apply (clarsimp simp: obj_relation_cuts_def2 ko_relations eps_of_kh_def opt_map_def
                  split: Structures_A.kernel_object.split_asm if_split_asm arch_kernel_obj.split_asm)
  apply (clarsimp simp: pspace_relation_def opt_map_def eps_of_kh_def split: option.splits)
  apply (rename_tac p ep ep')
  apply (drule_tac x=p in bspec, fastforce)
  apply (fastforce simp: ko_relations)
  done

lemma pspace_relation_ntfns_relation:
  "pspace_relation (kheap s) (ksPSpace s') \<Longrightarrow> ntfns_relation s s'"
  apply (clarsimp simp: map_relation_def)
  apply (rule conjI)
   apply (rule dom_eqI)
    apply (clarsimp simp: opt_map_def split: option.splits)
    apply (drule (1) pspace_relation_absD)
    apply (clarsimp split: if_splits)
    apply (rename_tac ko, case_tac ko; simp add: ko_relations)
   apply (clarsimp simp: opt_map_def split: option.splits)
   apply (erule (1) pspace_dom_relatedE)
   apply (clarsimp simp: obj_relation_cuts_def2 ko_relations opt_map_def
                  split: Structures_A.kernel_object.split_asm if_split_asm arch_kernel_obj.split_asm)
  apply (clarsimp simp: pspace_relation_def opt_map_def split: option.splits)
  apply (rename_tac p ntfn ntfn')
  apply (drule_tac x=p in bspec, fastforce)
  apply (fastforce simp: ko_relations)
  done

lemma pspace_relation_replies_relation:
  "pspace_relation (kheap s) (ksPSpace s') \<Longrightarrow> replies_relation s s'"
  apply (clarsimp simp: map_relation_def)
  apply (rule conjI)
   apply (rule dom_eqI)
    apply (clarsimp simp: opt_map_def split: option.splits)
    apply (drule (1) pspace_relation_absD)
    apply (clarsimp split: if_splits)
    apply (rename_tac ko, case_tac ko; simp add: ko_relations)
   apply (clarsimp simp: opt_map_def split: option.splits)
   apply (erule (1) pspace_dom_relatedE)
   apply (clarsimp simp: obj_relation_cuts_def2 ko_relations opt_map_def
                  split: Structures_A.kernel_object.split_asm if_split_asm arch_kernel_obj.split_asm)
  apply (clarsimp simp: pspace_relation_def opt_map_def split: option.splits)
  apply (rename_tac p reply reply')
  apply (drule_tac x=p in bspec, fastforce)
  apply (fastforce simp: ko_relations)
  done

lemma pspace_relation_caps_relation:
  "pspace_relation (kheap s) (ksPSpace s') \<Longrightarrow> caps_relation s s'"
  apply (clarsimp simp: caps_relation_def)
  apply (rule context_conjI)
   apply (simp add: set_eq_subset)
   apply (intro conjI impI)
    apply clarsimp
    apply (clarsimp simp: opt_map_def cnode_to_cte_ptrs_def cnode_of_def split: option.splits)
    apply (drule (1) pspace_relation_absD)
    apply (clarsimp simp: is_cap_table well_formed_cnode_n_def)
    apply (rename_tac contents cref ko' cap, case_tac ko'; clarsimp split: if_splits)
    apply (prop_tac "\<exists>z. ksPSpace s' (cte_map ( p, cref)) = Some z
                         \<and> cte_relation (cref) (CNode (length (cref)) contents) z")
     apply (fastforce dest: wf_cs_nD intro: domI)
    apply (clarsimp split: kernel_object.split_asm simp: cte_relation_def)
   apply (clarsimp simp: opt_map_def cnode_to_cte_ptrs_def split: option.splits)
   apply (erule (1) pspace_dom_relatedE)
   apply (fastforce simp: obj_relation_cuts_def2 ko_relations
                   split: Structures_A.kernel_object.split_asm if_split_asm
                          arch_kernel_obj.split_asm)
  apply (clarsimp simp: pspace_relation_def opt_map_def cnode_of_def
                 split: option.splits)
  apply (drule_tac x=p in bspec, fastforce)
  apply (rename_tac ko cref, case_tac ko; clarsimp split: if_splits)
  apply (clarsimp simp: cte_relation_def)
  by (fastforce del: ext intro!: ext)

lemma pspace_relation_KOKernelData:
  "pspace_relation (kheap s) (ksPSpace s') \<Longrightarrow> \<forall>p. ksPSpace s' p \<noteq> Some KOKernelData"
  apply (clarsimp simp: opt_map_def cnode_to_cte_ptrs_def split: option.splits)
  apply (erule (1) pspace_dom_relatedE)
  apply (fastforce simp: obj_relation_cuts_def2 ko_relations
                  split: Structures_A.kernel_object.split_asm if_split_asm arch_kernel_obj.split_asm)
  done

lemma pspace_relation_data_pages_relation:
  "pspace_relation (kheap s) (ksPSpace s') \<Longrightarrow> data_pages_relation s s'"
  apply (clarsimp simp: data_pages_relation_def)
  apply (rule context_conjI)
   apply (simp add: set_eq_subset)
   apply (intro conjI impI)
     apply clarsimp
     apply (clarsimp simp: opt_map_def vmpage_size_to_ptrs_def
                    split: option.splits)
     apply (drule (1) pspace_relation_absD)
     apply (clarsimp simp: is_cap_table well_formed_cnode_n_def)
     apply (rename_tac ko n ako, case_tac ako; clarsimp split: if_splits)
      apply (fastforce intro: domI)
     apply (fastforce intro: domI)
    apply clarsimp
    apply (erule (1) pspace_dom_relatedE)
    apply (fastforce elim!: pspace_dom_relatedE
                    intro!: dom_eqD
                      simp: obj_relation_cuts_def2 ko_relations vmpage_size_to_ptrs_def opt_map_def
                     split: Structures_A.kernel_object.split_asm if_split_asm
                            arch_kernel_obj.split_asm)
   apply clarsimp
   apply (erule (1) pspace_dom_relatedE)
   apply (fastforce simp: obj_relation_cuts_def2 ko_relations vmpage_size_to_ptrs_def opt_map_def
                   split: Structures_A.kernel_object.split_asm if_split_asm
                          arch_kernel_obj.split_asm)
  apply (clarsimp simp: pspace_relation_def opt_map_red tcbs_of_kh_def vmpage_size_to_ptrs_def)
  apply (prop_tac "p + (n << pageBits)
                   \<in> {p + (n << pageBits)
                      |n. n < 2 ^ (pageBitsForSize (the (page_sizes_of s p)) - pageBits)}")
   apply fastforce
  apply (prop_tac "ksPSpace s' (p + (n << pageBits)) \<noteq> None")
   apply blast
  apply (drule_tac x=p in bspec)
   apply (clarsimp simp: opt_map_def split: option.splits)
  apply (clarsimp simp: opt_map_def page_of_def
                 split: arch_kernel_obj.split_asm option.splits)
  apply (fastforce intro: domI split: Structures_A.kernel_object.split_asm)
  done

lemma pspace_relation_ptes_relation:
  "pspace_relation (kheap s) (ksPSpace s') \<Longrightarrow> ptes_relation s s'"
  apply (clarsimp simp: ptes_relation_def)
  apply (rule context_conjI)
   apply (simp add: set_eq_subset)
   apply (intro conjI impI)
    apply clarsimp
    apply (clarsimp simp: opt_map_def ptr_to_pte_ptrs_def
                   split: option.splits)
    apply (drule (1) pspace_relation_absD)
    apply (clarsimp, rename_tac idx)
    apply (drule_tac x=idx in spec)
    apply clarsimp
    apply (clarsimp simp: pte_relation_def aobj_of'_def pte_of'_def)
   apply (clarsimp simp: opt_map_def ptr_to_pte_ptrs_def split: option.splits)
   apply (erule (1) pspace_dom_relatedE)
   apply (clarsimp simp: pte_relation_def aobj_of'_def pte_of'_def)
   apply (rename_tac ako ko ptr abs_ko P)
   apply (case_tac ko; clarsimp)
   apply (case_tac ako; clarsimp)
   apply (fastforce simp: obj_relation_cuts_def2 ko_relations
                   split: Structures_A.kernel_object.split_asm if_split_asm
                          arch_kernel_obj.split_asm)
  apply (clarsimp simp: pspace_relation_def)
  apply (rename_tac p pt pte pte')
  apply (drule_tac x=p in bspec)
   apply (clarsimp simp: opt_map_def split: option.splits)
  apply (clarsimp elim!: pspace_dom_relatedE
                   simp: obj_relation_cuts_def2 aobj_of'_def ko_relations opt_map_def
                  split: option.splits)
  apply (drule_tac x=pte in spec)
  apply (clarsimp simp: pte_of'_def)
  done

lemma pspace_relation_asid_pools_relation:
  "pspace_relation (kheap s) (ksPSpace s') \<Longrightarrow> asid_pools_relation s s'"
  apply (clarsimp simp: map_relation_def)
  apply (rule conjI)
   apply (rule dom_eqI)
    apply (clarsimp simp: opt_map_def split: option.splits)
    apply (drule (1) pspace_relation_absD)
    apply (clarsimp split: if_splits)
    apply (rename_tac ko, case_tac ko; simp add: ko_relations)
    apply (rename_tac ako, case_tac ako; simp add: ko_relations)
    apply (clarsimp simp: aobj_of'_def asid_pool_of'_def)
   apply (clarsimp simp: opt_map_def split: option.splits)
   apply (erule (1) pspace_dom_relatedE)
   apply (clarsimp simp: obj_relation_cuts_def2 ko_relations opt_map_def aobj_of'_def
                         asid_pool_of'_def
                  split: Structures_A.kernel_object.split_asm if_split_asm
                         arch_kernel_obj.split_asm kernel_object.splits)
  apply (clarsimp simp: pspace_relation_def opt_map_def split: option.splits)
  apply (rename_tac p ko ako ap ap')
  apply (drule_tac x=p in bspec, fastforce)
  apply (clarsimp simp: aobj_of'_def asid_pool_of'_def other_aobj_relation_def
                 split: kernel_object.splits arch_kernel_object.splits)
  done

lemma pspace_relation_heap_pspace_relation[HeapStateRelation_R_assms]:
  "pspace_relation (kheap s) (ksPSpace s') \<longleftrightarrow> heap_pspace_relation s s'"
  apply (intro iffI)
   apply (clarsimp simp: heap_pspace_relation_def aobjs_relation_def)
   apply (intro conjI impI allI iffI)
            apply (fastforce dest: pspace_relation_tcbs_relation)
           apply (fastforce dest: pspace_relation_caps_relation)
          apply (fastforce dest: pspace_relation_scs_relation)
         apply (fastforce dest: pspace_relation_eps_relation)
        apply (fastforce dest: pspace_relation_ntfns_relation)
       apply (fastforce dest: pspace_relation_replies_relation)
      apply (fastforce dest: pspace_relation_KOKernelData)
     apply (fastforce dest: pspace_relation_data_pages_relation)
    apply (fastforce dest: pspace_relation_ptes_relation)
   apply (fastforce dest: pspace_relation_asid_pools_relation)
  apply (clarsimp simp: pspace_relation_def)
  apply (rule conjI)
   apply (clarsimp simp: pspace_dom_def)
   apply (simp add: set_eq_subset)
   apply (intro conjI impI)
    apply clarsimp
    apply (rename_tac ptr x rel ako)
    apply (case_tac ako; clarsimp simp: ko_relations split: if_splits)
            apply (frule heap_pspace_relation_caps_relation)
            apply (clarsimp simp: caps_relation_def cnode_to_cte_ptrs_def)
            apply (subgoal_tac "cte_map (ptr, y) \<in> dom (ctes_of' s')")
             apply (force simp: opt_map_def projectKO_opts_defs split: option.splits)
            apply (fastforce simp: opt_map_def)
           apply (fastforce dest: heap_pspace_relation_caps_relation
                            simp: caps_relation_def opt_map_def split: option.splits)
          apply (frule heap_pspace_relation_tcbs_relation)
          apply (fastforce simp: map_relation_def tcbs_of_kh_def opt_map_def split: option.splits)
         apply (frule heap_pspace_relation_eps_relation)
         apply (fastforce simp: map_relation_def eps_of_kh_def opt_map_def split: option.splits)
        apply (frule heap_pspace_relation_ntfns_relation)
        apply (fastforce dest: dom_eq_All simp: map_relation_def opt_map_def split: option.splits)
       apply (frule heap_pspace_relation_scs_relation)
       apply (fastforce simp: scs_relation_def scs_of_kh_def opt_map_def split: option.splits)
      apply (frule heap_pspace_relation_scs_relation)
      apply (fastforce simp: scs_relation_def scs_of_kh_def opt_map_def split: option.splits)
     apply (frule heap_pspace_relation_replies_relation)
     apply (fastforce simp: map_relation_def opt_map_def split: option.splits)
    apply (frule heap_pspace_relation_aobjs_relation)
    apply (rename_tac ako, case_tac ako; clarsimp)
      apply (frule aobjs_relation_asid_pools_relation)
      apply (fastforce simp: map_relation_def opt_map_def split: option.splits)
     apply (frule aobjs_relation_ptes_relation)
     apply (clarsimp simp: ptes_relation_def ptr_to_pte_ptrs_def)
     apply (subgoal_tac "ptr + (UCAST(9 \<rightarrow> 64) y << pteBits) \<in> dom (ptes_of' s')")
      apply (force simp: opt_map_def projectKO_opts_defs split: option.splits)
     apply (fastforce simp: opt_map_def)
    apply (frule aobjs_relation_data_pages_relation)
    apply (clarsimp simp: data_pages_relation_def vmpage_size_to_ptrs_def)
    apply (subgoal_tac "ptr + (n << pageBits)
                        \<in> {p. userDataDevice_at s' p} \<union> {p. userData_at s' p}")
     apply (force simp: opt_map_def projectKO_opts_defs split: option.splits)
    apply (fastforce simp: page_of_def opt_map_def)
   apply clarsimp
   apply (rename_tac ptr ko)
   apply (case_tac ko; clarsimp)
            apply (frule heap_pspace_relation_eps_relation)
            apply (clarsimp simp: map_relation_def)
            apply (force dest!: dom_eq_All simp: eps_of_kh_def opt_map_def split: option.splits)
           apply (frule heap_pspace_relation_ntfns_relation)
           apply (clarsimp simp: map_relation_def)
           apply (force dest!: dom_eq_All simp: opt_map_def split: option.splits)
          apply (fastforce dest: heap_pspace_relation_KOKernelData)
         apply (frule heap_pspace_relation_aobjs_relation)
         apply (frule aobjs_relation_data_pages_relation)
         apply (clarsimp simp: data_pages_relation_def)
         apply (prop_tac "ptr \<in> (\<Union>p\<in>dom (page_sizes_of s).
                                  vmpage_size_to_ptrs p (the (page_sizes_of s p)))")
          apply fastforce
         apply (frule Union_iff[THEN iffD1])
         apply (clarsimp, rename_tac i sz)
         apply (rule_tac x=i in bexI)
          apply (force simp: opt_map_def image_def page_of_def vmpage_size_to_ptrs_def
                      split: arch_kernel_obj.split_asm option.splits)
         apply (fastforce simp: opt_map_def split: option.splits)
        apply (frule heap_pspace_relation_aobjs_relation)
        apply (frule aobjs_relation_data_pages_relation)
        apply (clarsimp simp: data_pages_relation_def)
        apply (prop_tac "ptr \<in> (\<Union>p\<in>dom (page_sizes_of s).
                                 vmpage_size_to_ptrs p (the (page_sizes_of s p)))")
         apply fastforce
        apply (frule Union_iff[THEN iffD1])
        apply (clarsimp, rename_tac i sz)
        apply (rule_tac x=i in bexI)
         apply (force simp: opt_map_def image_def page_of_def vmpage_size_to_ptrs_def
                     split: arch_kernel_obj.split_asm option.splits)
        apply (fastforce simp: opt_map_def split: option.splits)
       apply (frule heap_pspace_relation_tcbs_relation)
       apply (clarsimp simp: map_relation_def)
       apply (force dest!: dom_eq_All simp: tcbs_of_kh_def opt_map_def split: option.splits)
      apply (frule heap_pspace_relation_caps_relation)
      apply (clarsimp simp: caps_relation_def)
      apply (prop_tac "ptr \<in> (\<Union>p\<in>dom (cnode_contents_of s). cnode_to_cte_ptrs p (the (cnode_contents_of s p)))")
       apply (fastforce simp: cnode_of_def opt_map_red)
      apply (frule Union_iff[THEN iffD1])
      apply clarsimp
      apply (rename_tac i cte cnode_contents)
      apply (rule_tac x=i in bexI)
       apply (force simp: opt_map_def image_def cnode_to_cte_ptrs_def cnode_of_def
                   split: Structures_A.kernel_object.splits option.splits)
      apply (fastforce simp: opt_map_def split: option.splits)
     apply (drule heap_pspace_relation_aobjs_relation)
     apply (rename_tac ako, case_tac ako; clarsimp)
      apply (frule aobjs_relation_asid_pools_relation)
      apply (clarsimp simp: map_relation_def)
      apply (rule_tac x=ptr in bexI)
       apply (fastforce dest: dom_eq_All simp: asid_pool_of'_def opt_map_def aobj_of'_def
                       split: option.splits)
      apply (fastforce simp: asid_pool_of'_def opt_map_def aobj_of'_def split: option.splits)
     apply (frule aobjs_relation_ptes_relation)
     apply (clarsimp simp: ptes_relation_def)
     apply (prop_tac "ptr \<in> \<Union> (ptr_to_pte_ptrs ` dom (pts_of s))")
      apply (fastforce simp: aobj_of'_def pte_of'_def opt_map_def split: option.splits)
     apply (frule Union_iff[THEN iffD1])
     apply clarsimp
     apply (rename_tac i pte pt)
     apply (rule_tac x=i in bexI)
      apply (force simp: opt_map_def image_def ptr_to_pte_ptrs_def split: option.splits)
     apply (fastforce simp: opt_map_def split: option.splits)
    apply (frule heap_pspace_relation_scs_relation)
    apply (clarsimp simp: scs_relation_def)
    subgoal by (force dest!: dom_eq_All simp: scs_of_kh_def opt_map_def split: option.splits)
   apply (frule heap_pspace_relation_replies_relation)
   apply (clarsimp simp: map_relation_def)
   apply (force dest!: dom_eq_All simp: opt_map_def split: option.splits)
  apply clarsimp
  apply (rename_tac ptr x rel ko)
  apply (clarsimp simp: obj_relation_cuts_def2)
  apply (case_tac ko; clarsimp split: if_splits)
          apply (rename_tac sz cnode_contents cnode_index cap)
          apply (drule heap_pspace_relation_caps_relation)
          apply (clarsimp simp: caps_relation_def cte_relation_def)
          apply (drule_tac x=ptr in bspec, force simp: opt_map_red)
          apply (drule_tac x=cnode_contents in spec)
          apply (drule_tac x=sz in spec)
          apply clarsimp
          apply (elim impE)
           apply (force simp: opt_map_red)
          apply (drule_tac x=cnode_index in bspec, fastforce)
          apply (clarsimp simp: cnode_to_cte_ptrs_def)
          apply (fastforce simp: opt_map_def split: option.splits)
         apply (drule heap_pspace_relation_caps_relation)
         apply (clarsimp simp: caps_relation_def cte_relation_def)
         apply (fastforce simp: opt_map_def split: option.splits)
        apply (drule heap_pspace_relation_tcbs_relation)
        apply (fastforce simp: map_relation_def tcb_relation_cut_def opt_map_def tcbs_of_kh_def
                        split: option.splits)
       apply (drule heap_pspace_relation_eps_relation)
       apply (fastforce simp: map_relation_def ep_relation_cut_def opt_map_def eps_of_kh_def
                       split: option.splits)
      apply (drule heap_pspace_relation_ntfns_relation)
      apply (fastforce simp: map_relation_def ntfn_relation_cut_def opt_map_def
                      split: option.splits)
     apply (drule heap_pspace_relation_scs_relation)
     apply (fastforce simp: scs_relation_def opt_map_def scs_of_kh_def split: option.splits)
    apply (drule heap_pspace_relation_scs_relation)
    apply (fastforce simp: scs_relation_def opt_map_def scs_of_kh_def split: option.splits)
   apply (drule heap_pspace_relation_replies_relation)
   apply (fastforce simp: map_relation_def opt_map_def split: option.splits)
  apply (drule heap_pspace_relation_aobjs_relation)
  apply (rename_tac ako, case_tac ako; clarsimp)
    apply (drule aobjs_relation_asid_pools_relation)
    apply (clarsimp simp: map_relation_def)
    apply (prop_tac "ptr \<in> dom (asid_pools_of' s')", fastforce simp: opt_map_red)
    apply (force simp: opt_map_def other_aobj_relation_def aobj_of'_def asid_pool_of'_def
                split: option.splits kernel_object.splits arch_kernel_object.splits)
   apply (drule aobjs_relation_ptes_relation)
   apply (clarsimp simp: ptes_relation_def pte_relation_def)
   apply (drule_tac x=ptr in bspec, force simp: opt_map_red)
   apply (drule_tac x=x2 in spec)
   apply (drule_tac x=y in spec)
   apply (prop_tac "(ptr + (UCAST(9 \<rightarrow> 64) y << pteBits)) \<in> dom (ptes_of' s')")
    apply (force simp: ptr_to_pte_ptrs_def opt_map_def)
   apply (fastforce simp: opt_map_def aobj_of'_def pte_of'_def
                   split: option.splits kernel_object.splits arch_kernel_object.splits)
  apply (rename_tac n)
  apply (drule aobjs_relation_data_pages_relation)
  apply (clarsimp simp: data_pages_relation_def)
  apply (drule_tac x=ptr in bspec, force simp: opt_map_def page_of_def)
  apply (drule_tac x="ptr + (n << pageBits)" in bspec)
   apply (force simp: vmpage_size_to_ptrs_def page_of_def opt_map_red)
  apply (clarsimp simp: page_of_def opt_map_def)
  done

lemma data_pages_relation_lift_rcorres:
  "\<lbrakk>\<And>s'. no_fail (\<lambda>s. Q s s') f; empty_fail f;
    \<And>P s'. \<lbrace>\<lambda>s. P (aobjs_of s) \<and> Q s s'\<rbrace> f \<lbrace>\<lambda>_ s. P (aobjs_of s)\<rbrace>;
    \<And>P s. \<lbrace>\<lambda>s'. P (aobjs_of' s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (aobjs_of' s')\<rbrace>;
    \<And>P s. \<lbrace>\<lambda>s'. P (userDataDevice_at s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (userDataDevice_at s')\<rbrace>;
    \<And>P s. \<lbrace>\<lambda>s'. P (userData_at s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (userData_at s')\<rbrace>\<rbrakk>
   \<Longrightarrow> rcorres (\<lambda>s s'. data_pages_relation s s' \<and> Q s s') f  f' (\<lambda>_ _. data_pages_relation)"
   apply (rule rcorres_lift_abs[where p=aobjs_of])
   apply (rule rcorres_lift_conc)
    apply (rule rcorres_prop_fwd)
      apply (fastforce intro: no_fail_pre)
     apply fastforce
    apply fastforce
   apply (rule hoare_weaken_pre)
    apply (rule hoare_lift_Pf2_pre_conj[where f=userData_at])
     by (fastforce intro: hoare_weaken_pre)+

lemma ptes_relation_lift_rcorres:
  "\<lbrakk>\<And>s'. no_fail (\<lambda>s. Q s s') f; empty_fail f;
    \<And>P s'. \<lbrace>\<lambda>s. P (aobjs_of s) \<and> Q s s'\<rbrace> f \<lbrace>\<lambda>_ s. P (aobjs_of s)\<rbrace>;
    \<And>P s. \<lbrace>\<lambda>s'. P (aobjs_of' s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (aobjs_of' s')\<rbrace>\<rbrakk>
   \<Longrightarrow> rcorres (\<lambda>s s'. ptes_relation s s' \<and> Q s s') f  f' (\<lambda>_ _. ptes_relation)"
  apply (rule rcorres_lift_abs[where p=aobjs_of])
   apply (rule rcorres_lift_conc)
    apply (rule rcorres_prop_fwd)
     by (fastforce intro: no_fail_pre hoare_weaken_pre)+

lemma asid_pools_relation_lift_rcorres:
  "\<lbrakk>\<And>s'. no_fail (\<lambda>s. Q s s') f; empty_fail f;
    \<And>P s'. \<lbrace>\<lambda>s. P (aobjs_of s) \<and> Q s s'\<rbrace> f \<lbrace>\<lambda>_ s. P (aobjs_of s)\<rbrace>;
    \<And>P s. \<lbrace>\<lambda>s'. P (aobjs_of' s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (aobjs_of' s')\<rbrace>\<rbrakk>
   \<Longrightarrow> rcorres (\<lambda>s s'. asid_pools_relation s s' \<and> Q s s') f  f' (\<lambda>_ _. asid_pools_relation)"
  apply (rule rcorres_lift_abs[where p=aobjs_of])
   apply (rule rcorres_lift_conc)
    apply (rule rcorres_prop_fwd)
      by (fastforce intro: no_fail_pre hoare_weaken_pre)+

lemma aobjs_relation_lift_rcorres:
  "\<lbrakk>\<And>s'. det_wp (\<lambda>s. Q s s') f; empty_fail f;
    \<And>P s'. \<lbrace>\<lambda>s. P (aobjs_of s) \<and> Q s s'\<rbrace> f \<lbrace>\<lambda>_ s. P (aobjs_of s)\<rbrace>;
    \<And>P s. \<lbrace>\<lambda>s'. P (aobjs_of' s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (aobjs_of' s')\<rbrace>;
    \<And>P s. \<lbrace>\<lambda>s'. P (userDataDevice_at s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (userDataDevice_at s')\<rbrace>;
    \<And>P s. \<lbrace>\<lambda>s'. P (userData_at s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (userData_at s')\<rbrace>\<rbrakk>
   \<Longrightarrow> rcorres (\<lambda>s s'. aobjs_relation s s' \<and> Q s s') f  f' (\<lambda>_ _. aobjs_relation)"
  unfolding aobjs_relation_def
  apply (intro rcorres_conj_lift_fwd)
      apply (fastforce elim: det_wp_pre)
     apply (rule rcorres_weaken_pre)
      apply (rule data_pages_relation_lift_rcorres)
           apply (fastforce intro: det_wp_no_fail)
          apply fastforce
         apply (fastforce intro: hoare_weaken_pre)
        apply (fastforce intro: hoare_weaken_pre)
       apply wpsimp+
    apply (fastforce elim: det_wp_pre)
   apply (rule rcorres_weaken_pre)
    apply (rule ptes_relation_lift_rcorres)
       apply (fastforce intro: det_wp_no_fail)
      apply (fastforce intro: hoare_weaken_pre)
     apply (fastforce intro: hoare_weaken_pre)
    apply (fastforce intro: hoare_weaken_pre)
   apply wpsimp
  apply (rule rcorres_weaken_pre)
   apply (rule asid_pools_relation_lift_rcorres)
      by (fastforce intro: det_wp_no_fail)+

lemma ghost_relation_heap_ghost_relation[HeapStateRelation_R_assms]:
  "ghost_relation_wrapper s s' \<longleftrightarrow> heap_ghost_relation_wrapper s s'"
  apply (clarsimp simp: ghost_relation_def heap_ghost_relation_def)
  apply (rule cnf.conj_cong)
   apply (intro iffI; clarsimp)
    apply (force simp: page_of_def opt_map_def
                split: option.splits arch_kernel_obj.splits)
   apply (rename_tac a sz, drule_tac x=a in spec)
   apply (force simp: page_of_def opt_map_def split: option.splits arch_kernel_obj.splits)
  apply (intro iffI; clarsimp)
   apply (force simp: cnode_of_def opt_map_def
               split: option.splits Structures_A.kernel_object.splits)
  apply (rename_tac a sz, drule_tac x=a in spec)
  apply (force simp: cnode_of_def opt_map_def
              split: Structures_A.kernel_object.splits option.splits)
  done

lemma heap_ghost_relation_lift_rcorres:
  "\<lbrakk>\<And>s'. det_wp (\<lambda>s. Q s s') f; empty_fail f;
    \<And>P s'. \<lbrace>\<lambda>s. P (page_sizes_of s) \<and> Q s s'\<rbrace> f \<lbrace>\<lambda>_ s. P (page_sizes_of s)\<rbrace>;
    \<And>P s'. \<lbrace>\<lambda>s. P (cnode_sizes_of s) \<and> Q s s'\<rbrace> f \<lbrace>\<lambda>_ s. P (cnode_sizes_of s)\<rbrace>;
    \<And>P s'. \<lbrace>\<lambda>s. P (cnodes_of s) \<and> Q s s'\<rbrace> f \<lbrace>\<lambda>_ s. P (cnodes_of s)\<rbrace>;
    \<And>P s. \<lbrace>\<lambda>s'. P (gsUserPages s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (gsUserPages s')\<rbrace>;
    \<And>P s. \<lbrace>\<lambda>s'. P (gsCNodes s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (gsCNodes s')\<rbrace>\<rbrakk>
   \<Longrightarrow> rcorres
         (\<lambda>s s'. heap_ghost_relation_wrapper s s' \<and> Q s s')
         f  f'
         (\<lambda>_ _ s s'. heap_ghost_relation_wrapper s s')"
  apply (clarsimp simp: heap_ghost_relation_def)
  apply (rule rcorres_conj_lift_fwd)
    apply (fastforce intro: det_wp_pre)
   apply (intro rcorres_allI_fwd)
     apply (fastforce intro: det_wp_pre)
    apply (fastforce intro: det_wp_pre)
   apply (rule rcorres_lift_abs[where p=page_sizes_of])
    apply (rule rcorres_lift_conc)
     apply (rule rcorres_prop_fwd)
       apply (rule no_fail_pre)
        apply (fastforce intro!: det_wp_no_fail)
       apply fastforce
      apply fastforce
     apply force
    apply (fastforce intro: hoare_weaken_pre)
   apply (fastforce intro: hoare_weaken_pre)
  apply (rule rcorres_allI_fwd)
   apply (fastforce intro: det_wp_pre)
  apply (rename_tac p)
  apply (rule rcorres_allI_fwd)
   apply (fastforce intro: det_wp_pre)
  apply (rename_tac n)
  apply (rule rcorres_weaken_pre)
   apply (rule_tac R="\<lambda>s x _. (cnode_sizes_of s p = Some n
                               \<and> (\<exists>cs. cnode_contents_of s p = Some cs \<and> well_formed_cnode_n n cs))
                              = x"
                in rcorres_lift_conc[where Q=Q])
    apply (rule rcorres_weaken_pre)
     apply (rule_tac R="\<lambda>x' s s'. (x' = Some n
                                   \<and> (\<exists>cs. cnode_contents_of s p = Some cs \<and> well_formed_cnode_n n cs))
                                  = x"
                 and p="\<lambda>s. cnode_sizes_of s p"
                  in rcorres_lift_abs[where Q=Q])
      apply (rule_tac rcorres_lift_abs)
       apply (rule rcorres_prop_fwd)
         apply (rule no_fail_pre)
          apply (fastforce intro: det_wp_no_fail)
         apply fastforce
        apply fastforce
       apply fastforce
      by (fastforce intro: hoare_weaken_pre)+

end

global_interpretation HeapStateRelation_R?: HeapStateRelation_R
proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales; fact HeapStateRelation_R_assms)?)
qed

end
