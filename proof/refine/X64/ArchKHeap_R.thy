(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchKHeap_R
imports
  "AInvs.ArchDetSchedSchedule_AI"
  KHeap_R
begin

declare a_type_simps[simp] (* FIXME: on RISCV64/AARCH64 this is in ArchInvariants_AI already *)

context Arch begin arch_global_naming

named_theorems KHeap_R_assms

declare aa_type_simps[simp] (* FIXME: on RISCV64/AARCH64 this is in ArchInvariants_AI already *)

lemmas typ_at_to_obj_at_arches
  = typ_at_to_obj_at'[where 'a=pte, simplified]
    typ_at_to_obj_at'[where 'a=pde, simplified]
    typ_at_to_obj_at'[where 'a=pdpte, simplified]
    typ_at_to_obj_at'[where 'a=pml4e, simplified]
    typ_at_to_obj_at'[where 'a=asidpool, simplified]
    typ_at_to_obj_at'[where 'a=user_data, simplified]
    typ_at_to_obj_at'[where 'a=user_data_device, simplified]

lemmas page_table_at_obj_at'
  = page_table_at'_def[unfolded typ_at_to_obj_at_arches]

lemma koType_objBitsKO[KHeap_R_assms]:
  "koTypeOf k = koTypeOf k' \<Longrightarrow> objBitsKO k = objBitsKO k'"
  by (auto simp: objBitsKO_def archObjSize_def
          split: kernel_object.splits arch_kernel_object.splits)

lemma pspace_dom_update[KHeap_R_assms]:
  "\<lbrakk> ps ptr = Some x; a_type x = a_type v \<rbrakk> \<Longrightarrow> pspace_dom (ps(ptr \<mapsto> v)) = pspace_dom ps"
  apply (simp add: pspace_dom_def dom_fun_upd2 del: dom_fun_upd)
  apply (rule SUP_cong [OF refl])
  apply clarsimp
  apply (simp add: obj_relation_cuts_def3)
  done

lemma cte_wp_at_ctes_of[KHeap_R_assms]:
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

lemma ctes_of_canonical[KHeap_R_assms]:
  assumes canonical: "pspace_canonical' s"
  assumes ctes_of: "ctes_of s p = Some cte"
  shows "canonical_address p"
proof -
  from ctes_of have "cte_wp_at' ((=) cte) p s"
    by (simp add: cte_wp_at_ctes_of)
  thus ?thesis using canonical
    by (fastforce simp: pspace_canonical'_def tcb_cte_cases_def field_simps objBits_defs take_bit_Suc
                 split: if_splits
                  elim: cte_wp_atE' canonical_address_add)
qed

lemma valid_updateCapDataI[KHeap_R_assms]:
  "s \<turnstile>' c \<Longrightarrow> s \<turnstile>' updateCapData b x c"
  apply (unfold global.updateCapData_def Let_def updateCapData_def)
  apply (cases c)
  apply (simp_all add: gen_isCap_defs valid_cap'_def global.capUntypedPtr_def gen_isCap_simps
                       capAligned_def word_size word_bits_def word_bw_assocs
                split: capability.splits)
  done

lemma obj_relation_cut_same_type:
  "\<lbrakk> (y, P) \<in> obj_relation_cuts ko x; P ko z;
    (y', P') \<in> obj_relation_cuts ko' x'; P' ko' z \<rbrakk>
     \<Longrightarrow> (a_type ko = a_type ko') \<or> (\<exists>n n'. a_type ko = ACapTable n \<and> a_type ko' = ACapTable n')
         \<or> (\<exists>sz sz'. a_type ko = AArch (AUserData sz) \<and> a_type ko' = AArch (AUserData sz'))
         \<or> (\<exists>sz sz'. a_type ko = AArch (ADeviceData sz) \<and> a_type ko' = AArch (ADeviceData sz'))"
  apply (rule ccontr)
  apply (simp add: obj_relation_cuts_def2 a_type_def)
  by (auto simp: other_obj_relation_def cte_relation_def tcb_relation_cut_def
                 pte_relation_def pde_relation_def
                 pdpte_relation_def pml4e_relation_def other_aobj_relation_def
           split: Structures_A.kernel_object.split_asm if_split_asm
                  Structures_H.kernel_object.split_asm
                  X64_A.arch_kernel_obj.split_asm)

lemmas obj_at_simps = gen_obj_at_simps is_other_obj_relation_type_def
                      objBits_simps pageBits_def

lemma setObject_other_corres:
  fixes ob' :: "'a :: pspace_storable"
  assumes x: "updateObject ob' = updateObject_default ob'"
  assumes z: "\<And>s. obj_at' P ptr s
               \<Longrightarrow> map_to_ctes ((ksPSpace s) (ptr \<mapsto> injectKO ob')) = map_to_ctes (ksPSpace s)"
  assumes t: "is_other_obj_relation_type (a_type ob)"
  assumes b: "\<And>ko. P ko \<Longrightarrow> objBits ko = objBits ob'"
  assumes P: "\<And>v::'a::pspace_storable. (1 :: machine_word) < 2 ^ objBits v"
  assumes a: "\<not> is_ArchObj ob"
  shows      "other_obj_relation ob (injectKO (ob' :: 'a :: pspace_storable)) \<Longrightarrow>
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
  apply (rename_tac ko)
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
  apply (prop_tac "typ_at' (koTypeOf (injectKO ob')) ptr b")
   subgoal
     by (clarsimp simp: typ_at'_def ko_wp_at'_def obj_at'_def projectKO_opts_defs
                        a_type_def other_obj_relation_def a
                 split: Structures_A.kernel_object.split_asm if_split_asm
                        kernel_object.split_asm)
  apply (insert a)
  apply (frule a_type_eq_is_ArchObj)
  apply clarsimp
  apply (rule conjI)
   apply (rule ballI, drule(1) bspec)
   apply (drule domD)
   apply (clarsimp simp: is_other_obj_relation_type t a)
   apply (drule(1) bspec)
   apply clarsimp
   apply (frule_tac ko'=ko and x'=ptr in obj_relation_cut_same_type,
           (fastforce simp add: is_other_obj_relation_type t)+)
   apply (insert t)
   apply ((erule disjE
          | clarsimp simp: is_other_obj_relation_type is_other_obj_relation_type_def a_type_def)+)[1]
  \<comment> \<open>ready_queues_relation\<close>
  apply (prop_tac "koTypeOf (injectKO ob') \<noteq> TCBT")
   subgoal
     by (clarsimp simp: other_obj_relation_def; cases ob; cases "injectKO ob'";
         simp)
  by (fastforce dest: tcbs_of'_non_tcb_update)

(* analogous to setObject_other_corres, but for arch objects *)
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
  apply (rename_tac ko)
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
  apply (prop_tac "typ_at' (koTypeOf (injectKO ob')) ptr b")
   subgoal
     by (clarsimp simp: typ_at'_def ko_wp_at'_def obj_at'_def projectKO_opts_defs
                        is_other_obj_relation_type_def a_type_def other_aobj_relation_def
                 split: Structures_A.kernel_object.split_asm if_split_asm
                        arch_kernel_obj.split_asm kernel_object.split_asm
                        arch_kernel_object.split_asm)
  apply clarsimp
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
  \<comment> \<open>ready_queues_relation\<close>
  apply (prop_tac "koTypeOf (injectKO ob') \<noteq> TCBT")
   subgoal
     by (clarsimp simp: other_aobj_relation_def; cases ob; cases "injectKO ob'";
         simp split: arch_kernel_obj.split_asm)
  by (fastforce dest: tcbs_of'_non_tcb_update)

lemmas [KHeap_R_assms] =
  setObject_other_corres[where 'a=endpoint]
  setObject_other_corres[where 'a=notification]

lemma dmo_storeWordVM' [simp]:
  "doMachineOp (storeWordVM x y) = return ()"
  by (simp add: storeWordVM_def)

lemma updateObject_objBitsKO:
    "(ko', t') \<in> fst (updateObject (val :: 'a :: pspace_storable) ko p q n t)
         \<Longrightarrow> objBitsKO ko' = objBitsKO ko"
  apply (drule updateObject_type)
  apply (erule koType_objBitsKO)
  done

lemma setObject_distinct[wp]:
  shows "\<lbrace>pspace_distinct'\<rbrace> setObject p val \<lbrace>\<lambda>rv. pspace_distinct'\<rbrace>"
  apply (clarsimp simp: setObject_def split_def valid_def in_monad
                        pspace_distinct'_def ps_clear_upd
                        objBits_def[symmetric] lookupAround2_char1
                 split: if_split_asm
                 dest!: updateObject_objBitsKO)
   apply (fastforce dest: bspec[OF _ domI])
  apply (fastforce dest: bspec[OF _ domI])
  done

lemma setObject_aligned[wp]:
  shows "\<lbrace>pspace_aligned'\<rbrace> setObject p val \<lbrace>\<lambda>rv. pspace_aligned'\<rbrace>"
  apply (clarsimp simp: setObject_def split_def valid_def in_monad
                        pspace_aligned'_def ps_clear_upd
                        objBits_def[symmetric] lookupAround2_char1
                 split: if_split_asm
                 dest!: updateObject_objBitsKO)
   apply (fastforce dest: bspec[OF _ domI])
  apply (fastforce dest: bspec[OF _ domI])
  done

lemma setObject_canonical[wp]:
  shows "\<lbrace>pspace_canonical'\<rbrace> setObject p val \<lbrace>\<lambda>rv. pspace_canonical'\<rbrace>"
  apply (clarsimp simp: setObject_def split_def valid_def in_monad
                        pspace_canonical'_def ps_clear_upd
                        objBits_def[symmetric] lookupAround2_char1
                 split: if_split_asm
                 dest!: updateObject_objBitsKO)
   apply (fastforce dest: bspec[OF _ domI])
  apply (fastforce dest: bspec[OF _ domI])
  done

lemma setObject_pspace_in_kernel_mappings'[wp]:
  shows "\<lbrace>pspace_in_kernel_mappings'\<rbrace> setObject p val \<lbrace>\<lambda>rv. pspace_in_kernel_mappings'\<rbrace>"
  apply (clarsimp simp: setObject_def split_def valid_def in_monad
                        pspace_in_kernel_mappings'_def ps_clear_upd
                        objBits_def[symmetric] lookupAround2_char1
                 split: if_split_asm
                 dest!: updateObject_objBitsKO)
   apply (fastforce dest: bspec[OF _ domI])
  apply (fastforce dest: bspec[OF _ domI])
  done

crunch setEndpoint, getEndpoint, setNotification, getNotification
  for pspace_canonical'[wp]: "pspace_canonical'"
  and pspace_in_kernel_mappings'[wp]: "pspace_in_kernel_mappings'"

declare setEndpoint_pspace_in_kernel_mappings'[KHeap_R_assms]

declare setNotification_pspace_in_kernel_mappings'[KHeap_R_assms]

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
  assumes typs: "\<And>T p P. \<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> f \<lbrace>\<lambda>_ s. P (typ_at' T p s)\<rbrace>"
  assumes arch: "\<And>P. \<lbrace>\<lambda>s. P (ksArchState s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ksArchState s)\<rbrace>"
  shows "\<lbrace>valid_arch_state'\<rbrace> f \<lbrace>\<lambda>_. valid_arch_state'\<rbrace>"
  apply (simp add: valid_arch_state'_def
                   valid_asid_table'_def
                   valid_global_pts'_def
                   valid_global_pdpts'_def
                   valid_global_pds'_def
                   vspace_table_at'_defs
                   All_less_Ball)
  apply (rule hoare_lift_Pf [where f="ksArchState"])
   apply (wp typs hoare_vcg_const_Ball_lift arch typ_at_lifts)+
  done

lemma idle_is_global[KHeap_R_assms, intro!]:
  "ksIdleThread s \<in> global_refs' s"
  by (simp add: global_refs'_def)

end

interpretation KHeap_R?: KHeap_R
proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales; fact KHeap_R_assms)?)
qed

context Arch begin arch_global_naming

named_theorems KHeap_R_assms_2

lemmas setEndpoint_valid_globals[KHeap_R_assms_2, wp]
  = valid_global_refs_lift'[OF set_ep_ctes_of set_ep_arch'
                               setEndpoint_it setEndpoint_ksInterruptState]

lemma set_ntfn_global_refs'[KHeap_R_assms_2, wp]:
  "\<lbrace>valid_global_refs'\<rbrace> setNotification ptr val \<lbrace>\<lambda>_. valid_global_refs'\<rbrace>"
  by (rule valid_global_refs_lift'; wp)

crunch setEndpoint, setNotification
  for valid_arch'[wp]: valid_arch_state'
  (wp: valid_arch_state_lift')

lemmas [KHeap_R_assms_2] = setEndpoint_valid_arch' setNotification_valid_arch'

lemmas setObject_typ_ats[wp] = typ_at_lifts[OF setObject_typ_at']

lemmas doMachineOp_typ_ats[wp] = typ_at_lifts[OF doMachineOp_typ_at']

lemmas setEndpoint_typ_ats[wp] = typ_at_lifts[OF setEndpoint_typ_at']

end

interpretation KHeap_R_2?: KHeap_R_2
proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales; fact KHeap_R_assms_2)?)
qed

(* requalify interface lemmas which can't be locale assumptions due to free type variable *)
arch_requalify_facts
  setObject_other_corres
  setObject_pspace_in_kernel_mappings'


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

lemma tcb_at'_cross:
  assumes p: "pspace_relation (kheap s) (ksPSpace s')"
  assumes t: "tcb_at' ptr s'"
  shows "tcb_at ptr s"
  using assms
  apply (clarsimp simp: obj_at'_def )
  apply (erule (1) pspace_dom_relatedE)
  by (clarsimp simp: obj_relation_cuts_def2 obj_at_def  cte_relation_def
                     other_obj_relation_def pte_relation_def is_tcb_def pde_relation_def
                     pdpte_relation_def pml4e_relation_def
              split: Structures_A.kernel_object.split_asm if_split_asm arch_kernel_obj.split_asm)

lemma pspace_aligned_cross:
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
          apply (clarsimp simp: cte_map_def simp flip: shiftl_t2n')
          apply (simp only: cteSizeBits_def cte_level_bits_def)
          apply (rule is_aligned_add)
           apply (erule is_aligned_weaken, simp)
          apply (rule is_aligned_weaken)
          apply (rule is_aligned_shiftl_self, simp)

        \<comment>\<open>TCB\<close>
         apply (clarsimp simp: tcbBlockSizeBits_def elim!: is_aligned_weaken)

        \<comment>\<open>PTE\<close>
        apply (clarsimp simp: archObjSize_def table_size_def ptTranslationBits_def)
        apply (rule is_aligned_add)
         apply (erule is_aligned_weaken)
         apply simp
        apply (simp add: word_size_bits_def)
        apply (rule is_aligned_shift)

       \<comment>\<open>PDE\<close>
       apply (clarsimp simp: archObjSize_def table_size_def ptTranslationBits_def)
       apply (rule is_aligned_add)
        apply (erule is_aligned_weaken)
        apply simp
       apply (simp add: word_size_bits_def)
       apply (rule is_aligned_shift)

      \<comment>\<open>PDPTE\<close>
      apply (clarsimp simp: archObjSize_def table_size_def ptTranslationBits_def)
      apply (rule is_aligned_add)
       apply (erule is_aligned_weaken)
       apply simp
      apply (simp add: word_size_bits_def)
      apply (rule is_aligned_shift)

     \<comment>\<open>PML4E\<close>
     apply (clarsimp simp: archObjSize_def table_size_def ptTranslationBits_def)
     apply (rule is_aligned_add)
      apply (erule is_aligned_weaken)
      apply simp
     apply (simp add: word_size_bits_def)
     apply (rule is_aligned_shift)

    \<comment>\<open>DataPage\<close>
    apply (rule is_aligned_add)
     apply (erule is_aligned_weaken)
     apply (rule pbfs_atleast_pageBits)
    apply (rule is_aligned_mult_triv2)

   \<comment>\<open>other_obj_relation\<close>
   apply (simp add: other_obj_relation_def)
   apply (clarsimp simp: tcbBlockSizeBits_def epSizeBits_def ntfnSizeBits_def
                  split: kernel_object.splits Structures_A.kernel_object.splits)

  \<comment>\<open>other_aobj_relation\<close>
  apply (clarsimp simp: other_aobj_relation_def
                 split: kernel_object.splits Structures_A.kernel_object.splits)
  apply (fastforce simp: archObjSize_def split: arch_kernel_object.splits arch_kernel_obj.splits)
  done

lemma of_bl_shift_cte_level_bits:
  "(of_bl z :: machine_word) << cte_level_bits \<le> mask (cte_level_bits + length z)"
  by word_bitwise
     (simp add: test_bit_of_bl bit_simps word_size cte_level_bits_def rev_bl_order_simps)

lemma obj_relation_cuts_range_limit:
  "\<lbrakk> (p', P) \<in> obj_relation_cuts ko p; P ko ko' \<rbrakk>
   \<Longrightarrow> \<exists>x n. p' = p + x \<and> is_aligned x n \<and> n \<le> obj_bits ko \<and> x \<le> mask (obj_bits ko)"
  apply (erule (1) obj_relation_cutsE; clarsimp)
          apply (drule (1) wf_cs_nD)
          apply (clarsimp simp: cte_map_def simp flip: shiftl_t2n')
          apply (rule_tac x=cte_level_bits in exI)
          apply (simp add: is_aligned_shift of_bl_shift_cte_level_bits)
         apply (rule_tac x=tcbBlockSizeBits in exI)
         apply (simp add: tcbBlockSizeBits_def)
        apply (rule_tac x=word_size_bits in exI, simp add: bit_simps is_aligned_shift mask_def, word_bitwise)
       apply (rule_tac x=word_size_bits in exI, simp add: bit_simps is_aligned_shift mask_def, word_bitwise)
      apply (rule_tac x=word_size_bits in exI, simp add: bit_simps is_aligned_shift mask_def, word_bitwise)
     apply (rule_tac x=word_size_bits in exI, simp add: bit_simps is_aligned_shift mask_def, word_bitwise)
    apply (rule_tac x=pageBits in exI)
    apply (simp add: is_aligned_mult_triv2 pbfs_atleast_pageBits)
    apply (simp add: mask_def shiftl_t2n mult_ac pbfs_less_wb')
    apply (erule word_less_power_trans2, rule pbfs_atleast_pageBits)
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

lemma obj_relation_cuts_obj_bits:
  "\<lbrakk> (p', P) \<in> obj_relation_cuts ko p; P ko ko' \<rbrakk> \<Longrightarrow> objBitsKO ko' \<le> obj_bits ko"
  apply (erule (1) obj_relation_cutsE;
          clarsimp simp: objBits_simps objBits_defs bit_simps cte_level_bits_def
                         pbfs_atleast_pageBits[simplified bit_simps])
   apply (cases ko; simp add: other_obj_relation_def objBits_defs split: kernel_object.splits)
  apply (case_tac ako; simp add: other_aobj_relation_def objBits_defs archObjSize_def
                            split: kernel_object.splits arch_kernel_object.splits)
  done

lemmas is_aligned_add_step_le' = is_aligned_add_step_le[simplified mask_2pm1 add_diff_eq]

lemma pspace_distinct_cross:
  "\<lbrakk> pspace_distinct s; pspace_aligned s; pspace_relation (kheap s) (ksPSpace s') \<rbrakk> \<Longrightarrow>
   pspace_distinct' s'"
  apply (frule (1) pspace_aligned_cross)
  apply (clarsimp simp: pspace_distinct'_def)
  apply (rename_tac p' ko')
  apply (rule pspace_dom_relatedE; assumption?)
  apply (rename_tac p ko P)
  apply (frule (1) pspace_alignedD')
  apply (frule (1) pspace_alignedD)
  apply (rule ps_clearI, assumption)
   apply (case_tac ko'; simp add: objBits_simps objBits_defs pageBits_def)
   apply (simp add: archObjSize_def pageBits_def split: arch_kernel_object.splits)
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
          apply (rule_tac n=cte_level_bits in is_aligned_add_step_le'; assumption?)
            apply (rule is_aligned_add; (rule is_aligned_shift)?)
            apply (erule is_aligned_weaken, simp add: cte_level_bits_def)
           apply (rule is_aligned_add; (rule is_aligned_shift)?)
           apply (erule is_aligned_weaken, simp add: cte_level_bits_def)
          apply (simp add: cte_level_bits_def cteSizeBits_def)
         apply (clarsimp simp: pte_relation_def objBits_simps)
         apply (rule_tac n=word_size_bits in is_aligned_add_step_le'; simp add: word_size_bits_def)
        apply (clarsimp simp: pde_relation_def objBits_simps)
        apply (rule_tac n=word_size_bits in is_aligned_add_step_le'; simp add: word_size_bits_def)
       apply (clarsimp simp: pdpte_relation_def objBits_simps)
       apply (rule_tac n=word_size_bits in is_aligned_add_step_le'; simp add: word_size_bits_def)
      apply (clarsimp simp: pml4e_relation_def objBits_simps)
      apply (rule_tac n=word_size_bits in is_aligned_add_step_le'; simp add: word_size_bits_def)
     apply (simp add: objBitsKO_Data)
     apply (rule_tac n=pageBits in is_aligned_add_step_le'; assumption?)
    apply (case_tac ko; simp split: if_split_asm add: other_obj_relation_def other_aobj_relation_def)
   apply (case_tac ako; simp add: is_other_obj_relation_type_def a_type_def split: if_split_asm)
  apply (frule (1) obj_relation_cuts_obj_bits)
  apply (drule (2) obj_relation_cuts_range_mask_range)+
  apply (prop_tac "x' \<in> mask_range p' (objBitsKO ko')", simp add: mask_def add_diff_eq)
  apply (frule_tac x=p and y=x in pspace_distinctD; assumption?)
  apply (drule (4) mask_range_subsetD)
  apply (erule (2) in_empty_interE)
  done

lemma pspace_relation_tcb_at':
  assumes p: "pspace_relation (kheap a) (ksPSpace c)"
  assumes t: "tcb_at t a"
  assumes aligned: "pspace_aligned' c"
  assumes distinct: "pspace_distinct' c"
  shows "tcb_at' t c"
  using assms
  apply (clarsimp simp: obj_at_def)
  apply (drule(1) pspace_relation_absD)
  apply (clarsimp simp: is_tcb tcb_relation_cut_def)
  apply (simp split: kernel_object.split_asm)
  apply (drule(2) aligned_distinct_obj_atI'[where 'a=tcb], simp)
  apply (erule obj_at'_weakenE)
  apply simp
  done

lemma tcb_at_cross:
  "\<lbrakk>tcb_at t s; pspace_aligned s; pspace_distinct s; pspace_relation (kheap s) (ksPSpace s')\<rbrakk>
   \<Longrightarrow> tcb_at' t s'"
  apply (drule (2) pspace_distinct_cross)
  apply (drule (1) pspace_aligned_cross)
  apply (erule (3) pspace_relation_tcb_at')
  done

end
end
