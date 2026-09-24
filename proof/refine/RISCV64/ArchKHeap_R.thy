(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchKHeap_R
imports
  KHeap_R
begin

context Arch begin arch_global_naming

clear_named_theorems Arch_assms (* accumulate assumptions for KHeap_R locale *)

lemmas typ_at_to_obj_at_arches
  = typ_at_to_obj_at'[where 'a=pte, simplified]
    typ_at_to_obj_at'[where 'a=asidpool, simplified]
    typ_at_to_obj_at'[where 'a=user_data, simplified]
    typ_at_to_obj_at'[where 'a=user_data_device, simplified]

lemmas page_table_at_obj_at'
  = page_table_at'_def[unfolded typ_at_to_obj_at_arches]

lemma koType_objBitsKO[Arch_assms]:
  "\<lbrakk>koTypeOf k' = koTypeOf k; koTypeOf k = SchedContextT \<longrightarrow> objBitsKO k' = objBitsKO k\<rbrakk>
   \<Longrightarrow> objBitsKO k' = objBitsKO k"
  by (auto simp: objBitsKO_def archObjSize_def
          split: kernel_object.splits arch_kernel_object.splits)

lemma pspace_dom_update[Arch_assms]:
  "\<lbrakk> ps ptr = Some x; a_type x = a_type v \<rbrakk> \<Longrightarrow> pspace_dom (ps(ptr \<mapsto> v)) = pspace_dom ps"
  apply (simp add: pspace_dom_def dom_fun_upd2 del: dom_fun_upd)
  apply (rule SUP_cong [OF refl])
  apply clarsimp
  apply (simp add: obj_relation_cuts_def3)
  done

lemma cte_wp_at_ctes_of[Arch_assms]:
  "cte_wp_at' P p s = (\<exists>cte. ctes_of s p = Some cte \<and> P cte)"
  supply diff_neg_mask[simp del]
  apply (simp add: cte_wp_at_cases' map_to_ctes_def Let_def
                   cte_level_bits_def objBits_simps'
          split del: if_split)
  apply (safe del: disjCI)
    apply (clarsimp simp: ps_clear_def3 field_simps)
   apply (clarsimp simp: ps_clear_def3 field_simps
              split del: if_split)
   apply (frule is_aligned_sub_helper)
    apply (clarsimp simp: tcb_cte_cases_def cteSizeBits_def split: if_split_asm)
   apply (case_tac "n = 0")
    apply (clarsimp simp: field_simps)
   apply (subgoal_tac "ksPSpace s p = None")
    apply clarsimp
    apply (clarsimp simp: field_simps)
   apply (elim conjE)
   apply (subst(asm) mask_in_range, assumption)
   apply (drule arg_cong[where f="\<lambda>S. p \<in> S"])
   apply (simp add: dom_def field_simps)
   apply (erule mp)
   apply (rule ccontr, simp add: linorder_not_le)
   apply (drule word_le_minus_one_leq)
   apply clarsimp
   apply (simp add: field_simps)
  apply (clarsimp split: if_split_asm del: disjCI)
   apply (simp add: ps_clear_def3 field_simps)
  apply (rule disjI2, rule exI[where x="(p - (p && ~~ mask tcb_bits))"])
  apply (clarsimp simp: ps_clear_def3[where na=tcb_bits] is_aligned_mask add_ac
                        word_bw_assocs)
  done

lemma ctes_of_canonical[Arch_assms]:
  assumes canonical: "pspace_canonical' s"
  assumes ctes_of: "ctes_of s p = Some cte"
  shows "canonical_address p"
proof -
  from ctes_of have "cte_wp_at' ((=) cte) p s"
    by (simp add: cte_wp_at_ctes_of)
  thus ?thesis using canonical canonical_bit_def
    by (fastforce simp: pspace_canonical'_def tcb_cte_cases_def field_simps objBits_defs
                 split: if_splits
                 elim!: cte_wp_atE' canonical_address_add)
qed

lemma valid_updateCapDataI[Arch_assms]:
  "s \<turnstile>' c \<Longrightarrow> s \<turnstile>' updateCapData b x c"
  apply (unfold global.updateCapData_def Let_def RISCV64_H.updateCapData_def)
  apply (cases c)
  apply (simp_all add: gen_isCap_defs valid_cap'_def global.capUntypedPtr_def gen_isCap_simps
                       capAligned_def word_size word_bits_def word_bw_assocs
                split: capability.splits)
  done

lemma obj_relation_cut_same_type:
  "\<lbrakk> (y, P) \<in> obj_relation_cuts ko x; P ko z;
    (y', P') \<in> obj_relation_cuts ko' x'; P' ko' z \<rbrakk>
     \<Longrightarrow> (a_type ko = a_type ko') \<or> (\<exists>n n'. a_type ko = ACapTable n \<and> a_type ko' = ACapTable n')
         \<or> (\<exists>n n'. a_type ko = ASchedContext n \<and> a_type ko' = ASchedContext n')
         \<or> (\<exists>sz sz'. a_type ko = AArch (AUserData sz) \<and> a_type ko' = AArch (AUserData sz'))
         \<or> (\<exists>sz sz'. a_type ko = AArch (ADeviceData sz) \<and> a_type ko' = AArch (ADeviceData sz'))"
  apply (rule ccontr)
  apply (simp add: obj_relation_cuts_def2 a_type_def)
  by (auto simp: tcb_relation_cut_def
                 ep_relation_cut_def ntfn_relation_cut_def other_aobj_relation_def
                 cte_relation_def pte_relation_def
                 ep_relation_def ntfn_relation_def
          split: Structures_A.kernel_object.split_asm if_split_asm
                 Structures_H.kernel_object.split_asm
                 arch_kernel_obj.split_asm)

lemmas obj_at_simps = gen_obj_at_simps is_other_obj_relation_type_def
                      objBits_simps pageBits_def

(* No aobjs dependency on this architecture *)
lemma arch_state_relation_no_aobjs[elim!]:
  "(s, s') \<in> arch_state_relation aobjs' \<Longrightarrow> (s, s') \<in> arch_state_relation aobjs"
  by (simp add: arch_state_relation_def)

lemma setObject_other_arch_corres:
  fixes ob' :: "'a :: pspace_storable"
  assumes x: "updateObject ob' = updateObject_default ob'"
  assumes z: "\<And>s. obj_at' P ptr s
               \<Longrightarrow> map_to_ctes ((ksPSpace s) (ptr \<mapsto> injectKO ob')) = map_to_ctes (ksPSpace s)"
  assumes t: "is_other_obj_relation_type (a_type ob)"
  assumes b: "\<And>ko. P ko \<Longrightarrow> objBits ko = objBits ob'"
  assumes e: "\<And>ko. P ko \<Longrightarrow> exst_same' (injectKO ko) (injectKO ob')"
  assumes P: "\<And>v::'a::pspace_storable. (1 :: machine_word) < 2 ^ objBits v"
  assumes a: "is_ArchObj ob"
  shows      "other_aobj_relation ob (injectKO (ob' :: 'a :: pspace_storable)) \<Longrightarrow>
  corres dc (obj_at (\<lambda>ko. a_type ko = a_type ob) ptr and obj_at (same_caps ob) ptr)
            (obj_at' (P :: 'a \<Rightarrow> bool) ptr)
            (set_object ptr ob) (setObject ptr ob')"
  supply image_cong_simp [cong del] projectKOs[simp del]
  apply (rule corres_no_failI)
   apply (rule no_fail_pre)
    apply wp
    apply (rule x)
   apply (clarsimp simp: b elim!: obj_at'_weakenE)
  apply (unfold set_object_def setObject_def)
  apply (clarsimp simp: in_monad split_def bind_def gets_def get_def Bex_def
                        put_def return_def modify_def get_object_def x
                        projectKOs obj_at_def
                        updateObject_default_def in_magnitude_check [OF _ P])
  apply (rename_tac s s' ko' psp_storable_obj ko)
  apply (clarsimp simp add: state_relation_def z)
  apply (clarsimp simp add: caps_of_state_after_update cte_wp_at_after_update
                            swp_def fun_upd_def obj_at_def)
  apply (subst conj_assoc[symmetric])
  apply (extract_conjunct \<open>match conclusion in "ghost_relation _ _ _" \<Rightarrow> -\<close>)
   apply (clarsimp simp add: ghost_relation_def)
   apply (erule_tac x=ptr in allE)+
   apply (clarsimp simp: obj_at_def a_type_def
                   split: Structures_A.kernel_object.splits if_split_asm)
   apply (simp split: arch_kernel_obj.splits if_splits)
  apply (fold fun_upd_def)
  apply (simp only: pspace_relation_def pspace_dom_update dom_fun_upd2 simp_thms)
  apply (elim conjE)
  apply (frule bspec, erule domI)
  apply (prop_tac "is_ArchObj ko", clarsimp simp: a dest!: a_type_eq_is_ArchObj)
  apply (prop_tac "typ_at' (koTypeOf (injectKO ob')) ptr s'")
   subgoal
     by (clarsimp simp: typ_at'_def ko_wp_at'_def obj_at'_def projectKO_opts_defs
                        is_other_obj_relation_type_def a_type_def other_aobj_relation_def
                 split: Structures_A.kernel_object.split_asm if_split_asm
                        arch_kernel_obj.split_asm kernel_object.split_asm
                        arch_kernel_object.split_asm)
  apply (prop_tac "tcb_of' (injectKO ob') = None")
   subgoal
     by (clarsimp simp: typ_at'_def ko_wp_at'_def obj_at'_def projectKO_opts_defs
                        is_other_obj_relation_type_def a_type_def other_aobj_relation_def
                 split: Structures_A.kernel_object.split_asm if_split_asm
                        arch_kernel_obj.split_asm kernel_object.split_asm)
  apply (prop_tac "tcbs_of' s' ptr = None")
   subgoal
     by (clarsimp simp: typ_at'_def ko_wp_at'_def obj_at'_def projectKO_opts_defs
                        is_other_obj_relation_type_def a_type_def other_aobj_relation_def
                        opt_map_def
                 split: Structures_A.kernel_object.split_asm if_split_asm
                        arch_kernel_obj.split_asm kernel_object.split_asm
                        arch_kernel_object.split_asm)
  apply (rule conjI)
   apply (rule conjI)
    apply (rule ballI, drule(1) bspec)
    apply (drule domD)
    apply (clarsimp simp: is_other_obj_relation_type t a)
    apply (drule(1) bspec)
    apply clarsimp
    apply (frule_tac ko'=ko and x'=ptr in obj_relation_cut_same_type)
    apply ((fastforce simp add: is_other_obj_relation_type t)+)[3] (* loops when folded into above *)
    apply (insert t)
    apply ((erule disjE
           | clarsimp simp: is_other_obj_relation_type is_other_obj_relation_type_def a_type_def)+)[1]
   apply (clarsimp simp: ep_queues_relation_def eps_of_kh_def opt_map_def split: option.splits)
  apply (extract_conjunct \<open>match conclusion in "ntfn_queues_relation_2 _ _ _ _" \<Rightarrow> -\<close>)
   apply (clarsimp simp: ntfn_queues_relation_def typ_at'_def opt_map_def split: option.splits)
  apply (extract_conjunct \<open>match conclusion in "sc_replies_relation_2 _ _ _" \<Rightarrow> -\<close>)
   apply (simp add: sc_replies_relation_def)
   apply (clarsimp simp: sc_replies_of_scs_def map_project_def scs_of_kh_def)
   apply (drule_tac x=p in spec)
   apply (rule conjI; clarsimp split: Structures_A.kernel_object.split_asm if_split_asm)
    apply (clarsimp simp: a_type_def is_other_obj_relation_type_def)
   apply (rename_tac sc n)
   apply (drule replyPrevs_of_non_reply_update[simplified])
    subgoal
      by (clarsimp simp: other_aobj_relation_def; cases ob; cases "injectKO ob'";
          simp split: arch_kernel_obj.split_asm)
   apply (clarsimp simp: opt_map_def)
  \<comment> \<open>ready_queues_relation and release_queue_relation\<close>
  by (fastforce dest: tcbs_of'_non_tcb_update)

lemma dmo_storeWordVM' [simp]:
  "doMachineOp (storeWordVM x y) = return ()"
  by (simp add: storeWordVM_def)

lemma setObject_pspace_in_kernel_mappings'[wp]:
  "setObject p val \<lbrace>pspace_in_kernel_mappings'\<rbrace>"
  unfolding pspace_in_kernel_mappings'_def
  by (clarsimp simp: setObject_def split_def valid_def in_monad updateObject_size
                  objBits_def[symmetric] lookupAround2_char1 ps_clear_upd
            split: if_split_asm)
    (fastforce dest: bspec[OF _ domI])+

crunch setEndpoint, setNotification
  for pspace_in_kernel_mappings'[wp]: "pspace_in_kernel_mappings'"

declare setEndpoint_pspace_in_kernel_mappings'[Arch_assms]

declare setNotification_pspace_in_kernel_mappings'[Arch_assms]

(* interface lemma, but can't be done via locale *)
lemma valid_global_refs_lift':
  assumes ctes: "\<And>P. \<lbrace>\<lambda>s. P (ctes_of s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ctes_of s)\<rbrace>"
  assumes arch: "\<And>P. \<lbrace>\<lambda>s. P (ksArchState s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ksArchState s)\<rbrace>"
  assumes idle: "\<And>P. \<lbrace>\<lambda>s. P (ksIdleThread s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ksIdleThread s)\<rbrace>"
  assumes irqn: "\<And>P. \<lbrace>\<lambda>s. P (irq_node' s)\<rbrace> f \<lbrace>\<lambda>_ s. P (irq_node' s)\<rbrace>"
  assumes maxObj: "\<And>P. \<lbrace>\<lambda>s. P (gsMaxObjectSize s)\<rbrace> f \<lbrace>\<lambda>_ s. P (gsMaxObjectSize s)\<rbrace>"
  shows "\<lbrace>valid_global_refs'\<rbrace> f \<lbrace>\<lambda>_. valid_global_refs'\<rbrace>"
  apply (simp add: valid_global_refs'_def valid_refs'_def global_refs'_def valid_cap_sizes'_def)
  apply (rule hoare_lift_Pf [where f="ksArchState"])
   apply (rule hoare_lift_Pf [where f="ksIdleThread"])
    apply (rule hoare_lift_Pf [where f="irq_node'"])
     apply (rule hoare_lift_Pf [where f="gsMaxObjectSize"])
      apply (wp ctes hoare_vcg_const_Ball_lift arch idle irqn maxObj)+
  done

lemma valid_arch_state_lift':
  assumes typs: "\<And>T p P. f \<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace>"
  assumes arch: "\<And>P. f \<lbrace>\<lambda>s. P (ksArchState s)\<rbrace>"
  shows "f \<lbrace>valid_arch_state'\<rbrace>"
  apply (simp add: valid_arch_state'_def valid_asid_table'_def valid_global_pts'_def
                   vspace_table_at'_defs)
  apply (rule hoare_lift_Pf [where f="ksArchState"])
   apply (wp typs hoare_vcg_all_lift hoare_vcg_ball_lift arch)+
  done

lemma idle_is_global[Arch_assms, intro!]:
  "ksIdleThread s \<in> global_refs' s"
  by (simp add: global_refs'_def)

(* Worth adding other typ_at's? *)
lemma typ_at'_ksPSpace_exI:
  "pte_at' ptr s \<Longrightarrow> \<exists>pte. ksPSpace s ptr = Some (KOArch (KOPTE pte))"
  apply -
  apply (clarsimp simp: typ_at'_def ko_wp_at'_def,
         (case_tac ko; clarsimp),
         (rename_tac arch, case_tac arch; clarsimp)?)+
  done

lemma pspace_aligned_cross[Arch_assms]:
  "\<lbrakk> pspace_aligned s; pspace_relation (kheap s) (ksPSpace s') \<rbrakk> \<Longrightarrow> pspace_aligned' s'"
  apply (clarsimp simp: pspace_aligned'_def pspace_aligned_def pspace_relation_def)
  apply (rename_tac p' ko')
  apply (prop_tac "p' \<in> pspace_dom (kheap s)", fastforce)
  apply (thin_tac "pspace_dom k = p" for k p)
  apply (clarsimp simp: pspace_dom_def)
  apply (drule bspec, fastforce)+
  apply clarsimp
  apply (rename_tac ko' a a' P ko)
  apply (erule (1) obj_relation_cutsE; clarsimp simp: objBits_simps)

         \<comment>\<open>CNode\<close>
         apply (clarsimp simp: cte_map_def)
         apply (simp only: cteSizeBits_def cte_level_bits_def)
         apply (rule is_aligned_add)
          apply (erule is_aligned_weaken, simp)
         apply (rule is_aligned_weaken)
          apply (rule is_aligned_shiftl_self, simp)

        \<comment>\<open>SchedContext, Reply, TCB, EP, Ntfn\<close>
        apply ((clarsimp simp: minSchedContextBits_def min_sched_context_bits_def replySizeBits_def
                               sc_relation_def tcbBlockSizeBits_def epSizeBits_def ntfnSizeBits_def
                        elim!: is_aligned_weaken)+)[5]

     \<comment>\<open>PageTable\<close>
     apply (clarsimp simp: archObjSize_def pteBits_def table_size_def ptTranslationBits_def pte_bits_def)
     apply (rule is_aligned_add)
      apply (erule is_aligned_weaken)
      apply simp
     apply (rule is_aligned_shift)

    \<comment>\<open>DataPage\<close>
    apply (rule is_aligned_add)
     apply (erule is_aligned_weaken)
     apply (rule pbfs_atleast_pageBits)
   apply (rule is_aligned_shift)

   \<comment>\<open>Other non-arch\<close>
   apply (clarsimp simp: bit_simps' tcbBlockSizeBits_def epSizeBits_def ntfnSizeBits_def
                   split: kernel_object.splits Structures_A.kernel_object.splits)
  \<comment>\<open>Other arch\<close>
  apply (clarsimp simp: bit_simps' archObjSize_def other_aobj_relation_def
                  split: kernel_object.splits arch_kernel_obj.splits;
         simp add: bit_simps' split: arch_kernel_object.splits)
  done

lemma pspace_relation_pspace_bounded'[Arch_assms]:
  "\<lbrakk> pspace_relation (kheap s) (ksPSpace s') \<rbrakk> \<Longrightarrow> pspace_bounded' s'"
  apply (clarsimp simp: pspace_bounded'_def pspace_relation_def)
  apply (rename_tac p' ko')
  apply (prop_tac "p' \<in> pspace_dom (kheap s)", fastforce)
  apply (thin_tac "pspace_dom k = p" for k p)
  apply (clarsimp simp: pspace_dom_def)
  apply (drule bspec, fastforce)+
  apply clarsimp
  apply (rename_tac ko' a a' P ko)
  apply (erule (1) obj_relation_cutsE;
         clarsimp simp: objBits_simps' word_bits_def pageBits_def pteBits_def)

    \<comment>\<open>SchedContext\<close>
    apply (clarsimp simp: minSchedContextBits_def min_sched_context_bits_def replySizeBits_def
                          valid_sched_context_size_def sc_relation_def untyped_max_bits_def
                   elim!: is_aligned_weaken)

   \<comment>\<open>other_obj_relation\<close>
   apply (clarsimp simp: bit_simps' tcbBlockSizeBits_def epSizeBits_def ntfnSizeBits_def
                  split: kernel_object.splits Structures_A.kernel_object.splits)

  \<comment>\<open>other_aobj_relation\<close>
  apply (simp add: other_aobj_relation_def)
  apply (clarsimp simp: bit_simps' archObjSize_def
                 split: kernel_object.splits arch_kernel_object.splits arch_kernel_obj.splits)
  done

lemma obj_relation_cuts_obj_bits:
  "\<lbrakk> (p', P) \<in> obj_relation_cuts ko p; P ko ko' \<rbrakk> \<Longrightarrow> objBitsKO ko' \<le> obj_bits ko"
  apply (erule (1) obj_relation_cutsE;
          clarsimp simp: objBits_simps objBits_defs cte_level_bits_def sc_const_eq[symmetric]
                         pbfs_atleast_pageBits[simplified bit_simps] pteBits_def
                         table_size_def pte_bits_def ptTranslationBits_def pageBits_def
                         sc_relation_def)
  apply (cases ko; simp add: other_aobj_relation_def objBits_defs
                      split: kernel_object.splits)
  apply (case_tac ako; case_tac ko';
         clarsimp simp: archObjSize_def other_aobj_relation_def is_other_obj_relation_type_def
                  split: kernel_object.split arch_kernel_object.splits)
  done

lemma obj_relation_cuts_range_limit:
  "\<lbrakk> (p', P) \<in> obj_relation_cuts ko p; P ko ko' \<rbrakk>
   \<Longrightarrow> \<exists>x n. p' = p + x \<and> is_aligned x n \<and> n \<le> obj_bits ko \<and> x \<le> mask (obj_bits ko)"
  apply (erule (1) obj_relation_cutsE; clarsimp)
          apply (drule (1) wf_cs_nD)
          apply (clarsimp simp: cte_map_def)
          apply (rule_tac x=cte_level_bits in exI)
          apply (simp add: is_aligned_shift of_bl_shift_cte_level_bits)
         apply (rule_tac x=minSchedContextBits in exI)
         apply (simp add: objBits_simps' min_sched_context_bits_def)
        apply (rule_tac x=replySizeBits in exI)
        apply (simp add: replySizeBits_def)
       apply (rule_tac x=tcbBlockSizeBits in exI)
       apply (simp add: tcbBlockSizeBits_def)
      apply (rule_tac x=epSizeBits in exI)
      apply (simp add: epSizeBits_def)
     apply (rule_tac x=ntfnSizeBits in exI)
     apply (simp add: ntfnSizeBits_def)
    apply (rule_tac x=pteBits in exI)
    apply (simp add: bit_simps is_aligned_shift mask_def pteBits_def)
    apply word_bitwise
   apply (rule_tac x=pageBits in exI)
   apply (simp add: is_aligned_shift pbfs_atleast_pageBits is_aligned_mult_triv2)
   apply (simp add: mask_def shiftl_t2n mult_ac)
   apply (frule word_less_power_trans2, rule pbfs_atleast_pageBits)
    apply (simp add: pbfs_less_wb'[unfolded word_bits_def, simplified])
   apply (simp add: pbfs_less_wb'[unfolded word_bits_def, simplified])
  apply fastforce+
  done

lemma obj_relation_cuts_range_mask_range:
  "\<lbrakk> (p', P) \<in> obj_relation_cuts ko p; P ko ko'; is_aligned p (obj_bits ko) \<rbrakk>
   \<Longrightarrow> p' \<in> mask_range p (obj_bits ko)"
  apply (drule (1) obj_relation_cuts_range_limit, clarsimp)
  apply (rule conjI)
   apply (rule word_plus_mono_right2; assumption?)
   apply (simp add: is_aligned_no_overflow_mask)
  apply (erule word_plus_mono_right)
  apply (simp add: is_aligned_no_overflow_mask)
  done

lemma pspace_distinct_cross[Arch_assms]:
  "\<lbrakk> pspace_distinct s; pspace_aligned s; pspace_relation (kheap s) (ksPSpace s') \<rbrakk> \<Longrightarrow>
   pspace_distinct' s'"
  apply (frule (1) pspace_aligned_cross)
  apply (clarsimp simp: pspace_distinct'_def)
  apply (rename_tac p' ko')
  apply (rule pspace_dom_relatedE; assumption?)
  apply (rename_tac p ko P)
  apply (frule (1) pspace_alignedD')
  apply (frule (1) pspace_alignedD)
  apply (frule pspace_relation_pspace_bounded')
  apply (frule (1) pspace_boundedD')
  apply (rule ps_clearI, assumption)
   apply (case_tac ko';
          simp add: scBits_pos_power2 objBits_simps' bit_simps'
               del: minSchedContextBits_def)
   apply (clarsimp split: arch_kernel_object.splits simp: bit_simps' archObjSize_def)
  apply (rule ccontr, clarsimp)
  apply (rename_tac x' ko_x')
  apply (frule_tac x=x' in pspace_alignedD', assumption)
  apply (rule_tac x=x' in pspace_dom_relatedE; assumption?)
  apply (rename_tac x ko_x P')
  apply (frule_tac p=x in pspace_alignedD, assumption)
  apply (case_tac "p = x")
   apply clarsimp
   apply (erule (1) obj_relation_cutsE; clarsimp)
      apply (clarsimp simp: cte_relation_def cte_map_def objBits_simps)
      apply (rule_tac n=cteSizeBits in is_aligned_add_step_le'; assumption?)
     apply (clarsimp simp: pte_relation_def objBits_simps)
     apply (rule_tac n=pteBits in is_aligned_add_step_le'; assumption?)
    apply (simp add: objBitsKO_Data)
    apply (rule_tac n=pageBits in is_aligned_add_step_le'; assumption?)
   apply (rename_tac ako,
          case_tac ako;
          simp add: is_other_obj_relation_type_def a_type_def split: if_split_asm)
  apply (frule (1) obj_relation_cuts_obj_bits)
  apply (drule (2) obj_relation_cuts_range_mask_range)+
  apply (prop_tac "x' \<in> mask_range p' (objBitsKO ko')", simp add: mask_def add_diff_eq)
  apply (frule_tac x=p and y=x in pspace_distinctD; assumption?)
  apply (drule (4) mask_range_subsetD)
  apply (erule (2) in_empty_interE)
  done

lemma tcb_cases_related2:
  "tcb_cte_cases (v - x) = Some (getF, setF) \<Longrightarrow>
   \<exists>getF' setF' restr. tcb_cap_cases (tcb_cnode_index (unat ((v - x) >> cte_level_bits)))
                       = Some (getF', setF', restr)
          \<and> cte_map (x, tcb_cnode_index (unat ((v - x) >> cte_level_bits))) = v
          \<and> (\<forall>tcb tcb'. tcb_relation tcb tcb' \<longrightarrow> cap_relation (getF' tcb) (cteCap (getF tcb')))
          \<and> (\<forall>tcb tcb' cap cte. tcb_relation tcb tcb' \<longrightarrow> cap_relation cap (cteCap cte)
                        \<longrightarrow> tcb_relation (setF' (\<lambda>x. cap) tcb) (setF (\<lambda>x. cte) tcb'))"
  apply (clarsimp simp: tcb_cte_cases_def tcb_relation_def cte_level_bits_def cteSizeBits_def
                        tcb_cap_cases_simps[simplified]
                 split: if_split_asm)
  apply (simp_all add: tcb_cnode_index_def cte_level_bits_def cte_map_def field_simps to_bl_1)
  done

lemma hyp_live_live[Arch_assms]:
  "hyp_live ko \<Longrightarrow> live ko"
  by (clarsimp simp: hyp_live_def)

lemma hyp_live'_live'[Arch_assms]:
  "hyp_live' ko' \<Longrightarrow> live' ko'"
  by (clarsimp simp: hyp_live'_def)

lemma hyp_live_hyp_live'[Arch_assms]:
  "\<lbrakk>ksPSpace c t = Some ko'; hyp_live' ko'; tcbs_relation a c; aobjs_relation a c\<rbrakk>
   \<Longrightarrow> \<exists>ko. kheap a t = Some ko \<and> hyp_live ko"
  by (clarsimp simp: hyp_live'_def)

lemma ex_nonz_cap_to_arch_obj_cross[Arch_assms]:
  "\<lbrakk>ex_nonz_cap_to ptr s; pspace_relation (kheap s) (ksPSpace s');
    valid_objs s; pspace_aligned' s'; pspace_distinct' s';
    ksPSpace s' ptr = Some (KOArch ako); live' (KOArch ako)\<rbrakk>
   \<Longrightarrow> ex_nonz_cap_to' ptr s'"
  by (clarsimp simp: live'_def hyp_live'_def)

lemma pspace_relation_cte_wp_atI'[Arch_assms]:
  "\<lbrakk>pspace_relation (kheap s) (ksPSpace s'); cte_wp_at' ((=) cte) x s'; valid_objs s\<rbrakk>
   \<Longrightarrow> \<exists>c slot. cte_wp_at ((=) c) slot s \<and> cap_relation c (cteCap cte) \<and> x = cte_map slot"
  apply (simp add: cte_wp_at_cases')
  apply (elim disjE conjE exE)
   apply (erule(1) pspace_dom_relatedE)
   apply (erule(1) obj_relation_cutsE, simp_all split: if_split_asm)[1]
   apply (intro exI, rule conjI[OF _ conjI [OF _ refl]])
    apply (simp add: cte_wp_at_cases domI well_formed_cnode_invsI)
   apply (simp split: if_split_asm)
  apply (erule(1) pspace_dom_relatedE)
  apply (erule(1) obj_relation_cutsE, simp_all split: if_split_asm)
  apply (subgoal_tac "n = x - y", clarsimp)
   apply (drule tcb_cases_related2, clarsimp)
   apply (intro exI, rule conjI)
    apply (erule(1) cte_wp_at_tcbI[where t="(a, b)" for a b, simplified])
    apply fastforce
   apply simp
  apply clarsimp
  done

lemma pspace_relation_sc_at[Arch_assms]:
  "\<lbrakk>pspace_relation (kheap s) (ksPSpace s'); scs_of' s' scp \<noteq> None\<rbrakk> \<Longrightarrow> sc_at scp s"
  by (fastforce elim!: pspace_dom_relatedE obj_relation_cutsE
                 simp: other_aobj_relation_def is_sc_obj obj_at_def opt_map_def
                split: Structures_A.kernel_object.split_asm if_split_asm option.splits
                       arch_kernel_obj.splits kernel_object.splits)

lemma idle_sc_is_global [Arch_assms]:
  "idle_sc_ptr \<in> global_refs' s"
  by (simp add: global_refs'_def)

lemmas KHeap_R_assms = Arch_assms (* extract accumulated assumptions *)

end (* Arch *)

interpretation KHeap_R?: KHeap_R
proof goal_cases
  case 1 show ?case by (intro_locales; (unfold_locales; fact RISCV64.KHeap_R_assms)?)
qed

context Arch begin arch_global_naming

lemma setObject_ko_wp_at':
  fixes v :: "'a :: pspace_storable"
  assumes x: "\<And>v :: 'a. updateObject v = updateObject_default v"
  assumes n: "\<And>v :: 'a. objBits v = n"
  assumes v: "(1 :: machine_word) < 2 ^ n"
  shows
  "\<lbrace>\<lambda>s. P (injectKO v)\<rbrace> setObject p v \<lbrace>\<lambda>rv. ko_wp_at' P p\<rbrace>"
  by (clarsimp simp: setObject_def valid_def in_monad
                     ko_wp_at'_def x split_def n
                     updateObject_default_def
                     objBits_def[symmetric] ps_clear_upd
                     in_magnitude_check v)

sublocale setObject: typ_at_all_props' "setObject p v"
  by typ_at_props'

sublocale doMachineOp: typ_at_all_props' "doMachineOp mop"
  by typ_at_props'

end (* Arch *)

(* requalify interface lemmas which can't be locale assumptions due to free type variable *)
arch_requalify_facts
  setObject_pspace_in_kernel_mappings'
  setObject_ko_wp_at'
  valid_global_refs_lift'

(* arch-specific lemmas not required for satisfying KHeap_R interface *)

context Arch begin arch_global_naming

(* no hypervisor on this arch *)
lemma non_hyp_state_hyp_refs_of'[simp]:
  "state_hyp_refs_of' s = (\<lambda>p. {})"
  unfolding state_hyp_refs_of'_def
  apply (rule ext)
  by (clarsimp split: option.splits kernel_object.split
               simp: hyp_refs_of'_def tcb_hyp_refs'_def)

(* no hypervisor on this arch *)
lemma non_hyp_hyp_refs_of'[simp]:
  "hyp_refs_of' p = {}"
  unfolding state_hyp_refs_of'_def
  by (clarsimp split: option.splits kernel_object.split
               simp: hyp_refs_of'_def tcb_hyp_refs'_def)

end

(* FIXME: arch-split RT
   Lemmas moved out of locales in KHeap_R due to depending on arch consts/lemmas. *)
context simple_ko' begin interpretation Arch .

lemma pspace_in_kernel_mappings'[wp]:
  "f p v \<lbrace>pspace_in_kernel_mappings'\<rbrace>"
  unfolding f_def by (all \<open>wpsimp simp: default_update updateObject_default_def in_monad\<close>)

lemma valid_arch_state'[wp]:
  "f p v \<lbrace> valid_arch_state' \<rbrace>"
  by (rule valid_arch_state_lift'; wp)

end

context simple_non_tcb_ko' begin

lemma ctes_of[wp]: "f p v \<lbrace>\<lambda>s. P (ctes_of s)\<rbrace>"
  unfolding f_def by (rule setObject_ctes_of[where Q="\<top>", simplified]; simp)

lemma valid_mdb'[wp]: "f p v \<lbrace>valid_mdb'\<rbrace>"
  unfolding valid_mdb'_def by wp

lemma ifunsafe'[wp]:
  "f p v \<lbrace>if_unsafe_then_cap'\<rbrace>"
  unfolding f_def
  apply (rule setObject_ifunsafe'[where P="\<top>", simplified])
    apply (clarsimp simp: default_update updateObject_default_def in_monad not_tcb not_cte
                  intro!: equals0I)+
  apply (simp add: setObject_def split_def default_update)
  apply (wp updateObject_default_inv | simp)+
  done

lemmas irq_handlers[wp] = valid_irq_handlers_lift'' [OF ctes_of ksInterruptState]
lemmas irq_handlers'[wp] = valid_irq_handlers_lift'' [OF ctes_of ksInterruptState]

lemma valid_global_refs'[wp]:
  "f p v \<lbrace>valid_global_refs'\<rbrace>"
  by (rule valid_global_refs_lift'; wp)

lemma untyped_ranges_zero'[wp]:
  "f p ko \<lbrace>untyped_ranges_zero'\<rbrace>"
  unfolding cteCaps_of_def o_def
  apply (wpsimp wp: untyped_ranges_zero_lift)
  done

end

context simple_non_tcb_non_reply_ko' begin

lemma valid_pspace':
  "\<lbrace>valid_pspace' and valid_obj' (injectKO v) \<rbrace> f p v \<lbrace>\<lambda>_. valid_pspace'\<rbrace>"
  unfolding valid_pspace'_def by (wpsimp wp: valid_objs')

end

lemmas setEndpoint_cteCaps_of[wp] = ctes_of_cteCaps_of_lift [OF set_ep'.ctes_of]
lemmas setNotification_cteCaps_of[wp] = ctes_of_cteCaps_of_lift [OF set_ntfn'.ctes_of]

lemmas set_ep_valid_pspace'[wp] =
  set_ep'.valid_pspace'[simplified valid_obj'_def pred_conj_def, simplified]

lemmas set_ntfn_valid_pspace'[wp] =
  set_ntfn'.valid_pspace'[simplified valid_obj'_def pred_conj_def, simplified]

lemmas set_sc_valid_pspace'[wp] =
  set_sc'.valid_pspace'[simplified valid_obj'_def pred_conj_def, simplified]

lemmas valid_globals_cte_wpD'_idleThread = valid_globals_cte_wpD'[OF _ _ idle_is_global]
lemmas valid_globals_cte_wpD'_idleSC = valid_globals_cte_wpD'[OF _ _ idle_sc_is_global]

lemma setNotification_invs':
  "\<lbrace>invs' and valid_ntfn' val\<rbrace>
   setNotification ptr val
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (clarsimp simp add: invs'_def cteCaps_of_def)
  apply (wpsimp wp: irqs_masked_lift valid_irq_node_lift untyped_ranges_zero_lift
                    sym_heap_sched_pointers_lift valid_dom_schedule'_lift
              simp: o_def)
  done

lemma pspace_relation_cte_wp_atI:
  "\<lbrakk>pspace_relation (kheap (s :: det_state)) (ksPSpace s'); ctes_of (s' :: kernel_state) x = Some cte;
    valid_objs s\<rbrakk>
   \<Longrightarrow> \<exists>c slot. cte_wp_at ((=) c) slot s \<and> cap_relation c (cteCap cte) \<and> x = cte_map slot"
  apply (erule pspace_relation_cte_wp_atI'[where x=x])
   apply (simp add: cte_wp_at_ctes_of)
  apply assumption
  done

text \<open>
  FIXME arch-split RT: The following block is very similar to the block that is used to prove
  @{thm distinct_updateObject_gen_types}, and we should seek to reduce duplication between the two.
  One way of doing so would be to create two list of kernel object types: one containing the
  generic types, and the other containing the architecture-dependent types. These
  lists could then be supplied to some parts of the following ML code. Supplying only the generic
  types allows us to show distinctness between those, and then in the architecture-dependent file,
  we would supply both generic and architecture-dependent types.\<close>

context Arch begin arch_global_naming

\<comment>\<open> We're using @{command ML_goal} here because we want to show
    `distinct_updateObject_types TYPE('a) TYPE('b)` for around
    50 different combinations of 'a and 'b. Doing that by hand would
    be painful, and not as clear for future readers as this comment
    plus this ML code. \<close>
ML \<open>
local
  val ko_types = [
    @{typ notification},
    @{typ tcb},
    @{typ cte},
    @{typ sched_context},
    @{typ reply},
    @{typ endpoint},

    @{typ asidpool},
    @{typ pte}
  ];

  val skipped_pairs = [
    \<comment>\<open>This corresponds to the case where we're inserting a CTE into
       a TCB, which is the only case where the first two arguments
       to `updateObject` should have different types.

       See the comment on @{term updateObject} for more information.\<close>
    (@{typ cte}, @{typ tcb})
  ];

  fun skips (ts as (typ, typ')) =
      typ = typ' orelse Library.member (op =) skipped_pairs ts;

  fun mk_distinct_goal (typ, typ') =
      Const (@{const_name distinct_updateObject_types},
            Term.itselfT typ --> Term.itselfT typ' --> @{typ bool})
      $ Logic.mk_type typ
      $ Logic.mk_type typ';
in
  val distinct_updateObject_types_goals =
      Library.map_product pair ko_types ko_types
      |> Library.filter_out skips
      |> List.map mk_distinct_goal
end
\<close>

ML_goal distinct_updateObject_types: \<open>
  distinct_updateObject_types_goals
\<close>
  apply -
  \<comment>\<open> The produced goals match the following pattern: \<close>
  apply (all \<open>match conclusion in \<open>distinct_updateObject_types _ _\<close> \<Rightarrow> -\<close>)
  unfolding distinct_updateObject_types_def
  apply safe
  apply (clarsimp simp: distinct_updateObject_types_def
                        setObject_def updateObject_cte updateObject_default_def
                        typeError_def in_monad
                 split: if_splits kernel_object.splits)+
  done

lemmas setObject_distinct_types_preserves_obj_at'[wp] =
    distinct_updateObject_types[THEN setObject_distinct_types_preserves_obj_at'_pre]

(* FIXME RT: these overlap substantially with `setObject_distinct_types_preserves_obj_at'`,
   but fixing that requires having names for the relevant subset of lemmas. We can't do that with
   attributes, but we might be able to do it with a new command (`lemmas_matching`?) once `match`
   is factored.

   This doesn't really matter in this case because you're never going to refer to these lemmas by
   name. *)
lemmas set_distinct_types_preserves_obj_at'[wp] =
  setObject_distinct_types_preserves_obj_at'[folded setReply_def setNotification_def setCTE_def
                                                    setSchedContext_def setEndpoint_def]

lemmas set_distinct_types_preserves_pred_tcb_at'[wp] =
  set_distinct_types_preserves_obj_at'[TRY[where P="test o proj o tcb_to_itcb'" for test proj,
                                           simplified o_def, folded pred_tcb_at'_def, rule_format]]
  setObject_distinct_types_preserves_obj_at'[TRY[where P="test o proj o tcb_to_itcb'" for test proj,
                                             simplified o_def, folded pred_tcb_at'_def,
                                             rule_format]]

end

end
