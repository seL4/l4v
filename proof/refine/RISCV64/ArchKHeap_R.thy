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

named_theorems KHeap_R_assms

lemmas typ_at_to_obj_at_arches
  = typ_at_to_obj_at'[where 'a=pte, simplified]
    typ_at_to_obj_at'[where 'a=asidpool, simplified]
    typ_at_to_obj_at'[where 'a=user_data, simplified]
    typ_at_to_obj_at'[where 'a=user_data_device, simplified]

lemmas page_table_at_obj_at'
  = page_table_at'_def[unfolded typ_at_to_obj_at_arches]

lemma koType_objBitsKO[KHeap_R_assms]:
  "\<lbrakk>koTypeOf k' = koTypeOf k; koTypeOf k = SchedContextT \<longrightarrow> objBitsKO k' = objBitsKO k\<rbrakk>
   \<Longrightarrow> objBitsKO k' = objBitsKO k"
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
  thus ?thesis using canonical canonical_bit_def
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
         \<or> (\<exists>n n'. a_type ko = ASchedContext n \<and> a_type ko' = ASchedContext n')
         \<or> (\<exists>sz sz'. a_type ko = AArch (AUserData sz) \<and> a_type ko' = AArch (AUserData sz'))
         \<or> (\<exists>sz sz'. a_type ko = AArch (ADeviceData sz) \<and> a_type ko' = AArch (ADeviceData sz'))"
  apply (rule ccontr)
  apply (simp add: obj_relation_cuts_def2 a_type_def)
  apply (auto simp: other_obj_relation_def tcb_relation_cut_def cte_relation_def pte_relation_def
                    other_aobj_relation_def
             split: Structures_A.kernel_object.split_asm if_split_asm
                    Structures_H.kernel_object.split_asm
                    arch_kernel_obj.split_asm)
  done

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
  apply (rule conjI)
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
   (* sc_replies_relation *)
   apply (simp add: sc_replies_relation_def)
   apply (clarsimp simp: sc_replies_of_scs_def map_project_def scs_of_kh_def)
   apply (drule_tac x=p in spec)
   apply (rule conjI; clarsimp split: Structures_A.kernel_object.split_asm if_split_asm)
    apply (clarsimp simp: a_type_def is_other_obj_relation_type_def)
   apply (rename_tac sc n)
   apply (drule replyPrevs_of_non_reply_update[simplified])
    subgoal
      by (clarsimp simp: other_obj_relation_def; cases ob; cases "injectKO ob'";
          simp)
   apply (clarsimp simp: opt_map_def)
  \<comment> \<open>ready_queues_relation and release_queue_relation\<close>
  apply (prop_tac "koTypeOf (injectKO ob') \<noteq> TCBT")
   subgoal
     by (clarsimp simp: other_obj_relation_def; cases ob; cases "injectKO ob'";
         simp split: arch_kernel_obj.split_asm)
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
   (* sc_replies_relation *)
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

lemma setObject_pspace_in_kernel_mappings'[wp]:
  "setObject p val \<lbrace>pspace_in_kernel_mappings'\<rbrace>"
  unfolding pspace_in_kernel_mappings'_def
  by (clarsimp simp: setObject_def split_def valid_def in_monad updateObject_size
                  objBits_def[symmetric] lookupAround2_char1 ps_clear_upd
            split: if_split_asm)
    (fastforce dest: bspec[OF _ domI])+

crunch setEndpoint, getEndpoint, setNotification, getNotification
  for pspace_in_kernel_mappings'[wp]: "pspace_in_kernel_mappings'"

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
  assumes typs: "\<And>T p P. f \<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace>"
  assumes arch: "\<And>P. f \<lbrace>\<lambda>s. P (ksArchState s)\<rbrace>"
  shows "f \<lbrace>valid_arch_state'\<rbrace>"
  apply (simp add: valid_arch_state'_def valid_asid_table'_def valid_global_pts'_def
                   vspace_table_at'_defs)
  apply (rule hoare_lift_Pf [where f="ksArchState"])
   apply (wp typs hoare_vcg_all_lift hoare_vcg_ball_lift arch typ_at_lifts)+
  done

lemma idle_is_global[KHeap_R_assms, intro!]:
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

lemma st_tcb_at_coerce_abstract[KHeap_R_assms]:
  assumes t: "st_tcb_at' P t c"
  assumes sr: "(a, c) \<in> state_relation"
  shows "st_tcb_at (\<lambda>st. \<exists>st'. thread_state_relation st st' \<and> P st') t a"
  using assms
  apply (clarsimp simp: state_relation_def pred_tcb_at'_def obj_at'_def objBits_simps)
  apply (erule(1) pspace_dom_relatedE)
  apply (erule(1) obj_relation_cutsE, simp_all)
  apply (fastforce simp: st_tcb_at_def obj_at_def other_obj_relation_def tcb_relation_def
                   split: Structures_A.kernel_object.split_asm if_split_asm
                          RISCV64_A.arch_kernel_obj.split_asm)+
  done

lemma st_tcb_at_coerce_concrete[KHeap_R_assms]:
  assumes t: "st_tcb_at P t s"
  assumes sr: "(s, s') \<in> state_relation" "pspace_aligned s" "pspace_distinct s"
  shows "st_tcb_at' (\<lambda>st'. \<exists>st. thread_state_relation st st' \<and> P st) t s'"
  using assms
  apply (clarsimp simp: state_relation_def pred_tcb_at_def obj_at_def)
  apply (frule (1) pspace_distinct_cross, fastforce simp: state_relation_def)
  apply (frule pspace_aligned_cross, fastforce simp: state_relation_def)
  apply (prop_tac "tcb_at t s", clarsimp simp: st_tcb_at_def obj_at_def is_tcb)
  apply (drule (2) tcb_at_cross[rotated], fastforce simp: state_relation_def)
  apply (clarsimp simp: state_relation_def pred_tcb_at'_def obj_at'_def)
  apply (erule (1) pspace_dom_relatedE)
  apply (erule (1) obj_relation_cutsE, simp_all)
    apply (fastforce simp: st_tcb_at'_def obj_at'_def other_obj_relation_def tcb_relation_def
                    split: Structures_A.kernel_object.split_asm if_split_asm)+
  done

end

interpretation KHeap_R?: KHeap_R
proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales; fact KHeap_R_assms)?)
qed

(* requalify interface lemmas which can't be locale assumptions due to free type variable *)
arch_requalify_facts
  setObject_other_corres
  setObject_pspace_in_kernel_mappings'
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

lemma setSchedContext_iflive'[wp]:
  "\<lbrace>if_live_then_nonz_cap' and (\<lambda>s. live_sc' sc \<longrightarrow> ex_nonz_cap_to' p s)\<rbrace>
   setSchedContext p sc
   \<lbrace>\<lambda>_. if_live_then_nonz_cap'\<rbrace>"
  unfolding setSchedContext_def
  by (wpsimp wp: setObject_iflive'[where P="\<top>"]
           simp: updateObject_default_def in_monad scBits_pos_power2
                 gen_objBits_simps bind_def live'_def)

lemma setReply_iflive'[wp]:
  "\<lbrace>if_live_then_nonz_cap' and ex_nonz_cap_to' p\<rbrace>
   setReply p reply
   \<lbrace>\<lambda>_. if_live_then_nonz_cap'\<rbrace>"
  unfolding setReply_def
  by (wpsimp wp: setObject_iflive'[where P="\<top>"]
           simp: updateObject_default_def in_monad
                 gen_objBits_simps bind_def live'_def)

lemmas valid_globals_cte_wpD'_idleThread = valid_globals_cte_wpD'[OF _ _ idle_is_global]
lemmas valid_globals_cte_wpD'_idleSC = valid_globals_cte_wpD'[OF _ _ idle_sc_is_global]




(*FIXME arch-split RT: everything after this*)
lemma set_ntfn_minor_invs':
  "\<lbrace>invs'
      and valid_ntfn' val
      and (\<lambda>s. live' (KONotification val) \<longrightarrow> ex_nonz_cap_to' ptr s)\<rbrace>
   setNotification ptr val
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (clarsimp simp add: invs'_def cteCaps_of_def valid_dom_schedule'_def)
  apply (wpsimp wp: irqs_masked_lift valid_irq_node_lift untyped_ranges_zero_lift
                    sym_heap_sched_pointers_lift
              simp: o_def)
  done

context begin interpretation Arch .

lemma reply_at'_cross:
  assumes p: "pspace_relation (kheap s) (ksPSpace s')"
  assumes t: "reply_at' ptr s'"
  shows "reply_at ptr s" using assms
  apply (clarsimp simp: obj_at'_def)
  apply (erule (1) pspace_dom_relatedE)
  by (clarsimp simp: obj_relation_cuts_def2 obj_at_def is_reply cte_relation_def
                     other_obj_relation_def other_aobj_relation_def pte_relation_def tcb_relation_cut_def
              split: Structures_A.kernel_object.split_asm if_split_asm
                     arch_kernel_obj.split_asm)

lemma set_reply_corres: (* for reply update that doesn't touch the reply stack *)
  "reply_relation ae ae' \<Longrightarrow>
  corres dc \<top>
            (obj_at' (\<lambda>ko. replyPrev_same ae' ko) ptr)
            (set_reply ptr ae) (setReply ptr ae')"
proof -
  have x: "updateObject ae' = updateObject_default ae'" by clarsimp
  have z: "\<And>s. reply_at' ptr s
               \<Longrightarrow> map_to_ctes ((ksPSpace s) (ptr \<mapsto> injectKO ae')) = map_to_ctes (ksPSpace s)"
    by (clarsimp simp: gen_obj_at_simps)
  have b: "\<And>ko. (\<lambda>_ :: reply. True) ko \<Longrightarrow> objBits ko = objBits ae'"
    by (clarsimp simp: gen_obj_at_simps)
  assume r: "reply_relation ae ae'"
  show ?thesis
    apply (simp add: set_simple_ko_def setReply_def is_reply_def[symmetric])
    supply image_cong_simp [cong del]
    apply (insert r)
    apply (rule corres_no_failI)
     apply (rule no_fail_pre)
      apply wp
      apply (rule x)
     apply (clarsimp simp: obj_at'_weakenE[OF _ b])
    apply (unfold set_object_def setObject_def)
    apply (clarsimp simp: in_monad split_def bind_def gets_def get_def Bex_def
                          put_def return_def modify_def get_object_def x
                          obj_at_def obj_at'_def is_reply
                          updateObject_default_def in_magnitude_check[OF _])
    apply (prop_tac "reply_at ptr a")
     apply (clarsimp simp: obj_at'_def dest!: state_relation_pspace_relation reply_at'_cross[where ptr=ptr])
    apply (clarsimp simp: obj_at_def is_reply)
    apply (rename_tac reply)
    apply (prop_tac "obj_at (same_caps (kernel_object.Reply ae)) ptr a")
     apply (clarsimp simp: obj_at_def is_reply)
    apply (clarsimp simp: state_relation_def
                          z[simplified obj_at'_def is_reply projectKO_eq projectKO_opts_defs, simplified])
    apply (clarsimp simp add: caps_of_state_after_update cte_wp_at_after_update
                              swp_def fun_upd_def obj_at_def)
    apply (subst conj_assoc[symmetric])
    apply (extract_conjunct \<open>match conclusion in "ghost_relation _ _ _" \<Rightarrow> -\<close>)
     apply (clarsimp simp add: ghost_relation_def)
     apply (erule_tac x=ptr in allE)+
     apply (clarsimp simp: obj_at_def a_type_def
                     split: Structures_A.kernel_object.splits if_split_asm)
    apply (extract_conjunct \<open>match conclusion in "pspace_relation _ _" \<Rightarrow> -\<close>)
     apply (fold fun_upd_def)
     apply (simp only: pspace_relation_def simp_thms
                       pspace_dom_update[where x="kernel_object.Reply _"
                                           and v="kernel_object.Reply _",
                                         simplified a_type_def, simplified])
     apply (simp only: dom_fun_upd2 simp_thms)
     apply (elim conjE)
     apply (frule bspec, erule domI)
     apply (rule ballI, drule(1) bspec)
     apply (drule domD)
     apply (clarsimp simp: project_inject split: if_split_asm kernel_object.split_asm)
     apply (rename_tac bb aa ba)
     apply (drule_tac x="(aa, ba)" in bspec, simp)
     apply clarsimp
     apply (frule_tac ko'="kernel_object.Reply reply" and x'=ptr in obj_relation_cut_same_type)
        apply simp+
     apply clarsimp
    apply (extract_conjunct \<open>match conclusion in "sc_replies_relation_2 _ _ _" \<Rightarrow> -\<close>)
     apply (simp add: sc_replies_relation_def)
     apply (clarsimp simp: sc_replies_of_scs_def map_project_def scs_of_kh_def)
     apply (drule_tac x=p in spec)
     subgoal
       by (subst replyPrevs_of_replyPrev_same_update[simplified, where ob'=ae', simplified];
           simp add: typ_at'_def ko_wp_at'_def obj_at'_def project_inject opt_map_def)
    \<comment> \<open>ready_queues_relation and release_queue_relation\<close>
    apply (prop_tac "typ_at' (koTypeOf (injectKO ae')) ptr b")
     apply (simp add: typ_at'_def ko_wp_at'_def)
    by (fastforce dest: tcbs_of'_non_tcb_update)
qed

lemma setReply_not_queued_corres: (* for reply updates on replies not in fst ` replies_with_sc *)
  "reply_relation r1 r2 \<Longrightarrow>
  corres dc (\<lambda>s. ptr \<notin> fst ` replies_with_sc s) (reply_at' ptr)
            (set_reply ptr r1) (setReply ptr r2)"
proof -
  have x: "updateObject r2 = updateObject_default r2" by clarsimp
  have z: "\<And>s. reply_at' ptr s
               \<Longrightarrow> map_to_ctes ((ksPSpace s) (ptr \<mapsto> injectKO r2)) = map_to_ctes (ksPSpace s)"
    by (clarsimp simp: gen_obj_at_simps)
  have b: "\<And>ko. (\<lambda>_ :: reply. True) ko \<Longrightarrow> objBits ko = objBits r2"
    by (clarsimp simp: gen_obj_at_simps)
  assume r: "reply_relation r1 r2"
  show ?thesis
    apply (simp add: set_simple_ko_def setReply_def is_reply_def[symmetric])
    supply image_cong_simp [cong del]
    apply (insert r)
    apply (rule corres_no_failI)
     apply (rule no_fail_pre)
      apply wp
      apply (rule x)
     apply (clarsimp simp: obj_at'_weakenE[OF _ b])
    apply (unfold set_object_def setObject_def)
    apply (clarsimp simp: in_monad split_def bind_def gets_def get_def Bex_def
                          put_def return_def modify_def get_object_def x
                          obj_at_def obj_at'_def is_reply
                          updateObject_default_def in_magnitude_check[OF _])
    apply (prop_tac "reply_at ptr a")
     apply (clarsimp simp: obj_at'_def dest!: state_relation_pspace_relation reply_at'_cross[where ptr=ptr])
    apply (clarsimp simp: obj_at_def is_reply)
    apply (rename_tac reply)
    apply (prop_tac "obj_at (same_caps (kernel_object.Reply _)) ptr a")
     apply (clarsimp simp: obj_at_def is_reply)
    apply (clarsimp simp: state_relation_def
                          z[simplified obj_at'_def is_reply projectKO_eq projectKO_opts_defs, simplified])
    apply (clarsimp simp add: caps_of_state_after_update cte_wp_at_after_update
                              swp_def fun_upd_def obj_at_def)
    apply (subst conj_assoc[symmetric])
    apply (extract_conjunct \<open>match conclusion in "ghost_relation _ _ _" \<Rightarrow> -\<close>)
     apply (clarsimp simp add: ghost_relation_def)
     apply (erule_tac x=ptr in allE)+
     apply (clarsimp simp: obj_at_def a_type_def
                     split: Structures_A.kernel_object.splits if_split_asm)
    apply (extract_conjunct \<open>match conclusion in "pspace_relation _ _" \<Rightarrow> -\<close>)
     apply (fold fun_upd_def)
     apply (simp only: pspace_relation_def simp_thms
                       pspace_dom_update[where x="kernel_object.Reply _"
                                           and v="kernel_object.Reply _",
                                         simplified a_type_def, simplified])
     apply (simp only: dom_fun_upd2 simp_thms)
     apply (elim conjE)
     apply (frule bspec, erule domI)
     apply (rule ballI, drule(1) bspec)
     apply (drule domD)
     apply (clarsimp simp: project_inject split: if_split_asm kernel_object.split_asm)
     apply (rename_tac bb aa ba)
     apply (drule_tac x="(aa, ba)" in bspec, simp)
     apply clarsimp
     apply (frule_tac ko'="kernel_object.Reply reply" and x'=ptr in obj_relation_cut_same_type)
        apply simp+
     apply clarsimp
    apply (extract_conjunct \<open>match conclusion in "sc_replies_relation_2 _ _ _" \<Rightarrow> -\<close>)
     apply (simp add: sc_replies_relation_def)
     apply (clarsimp simp: sc_replies_of_scs_def map_project_def scs_of_kh_def)
     apply (drule_tac x=p in spec)
     apply (subgoal_tac "((scs_of' b)(ptr := sc_of' (KOReply r2)) |> scReply) p = scReplies_of b p")
      apply simp
      apply (subgoal_tac "heap_ls (replyPrevs_of b) (scReplies_of b p) (sc_replies z)")
       apply (erule heap_path_heap_upd_not_in)
       apply (clarsimp simp: sc_at_pred_n_def obj_at_def replies_with_sc_def image_def)
       apply (drule_tac x=p in spec)
       apply (clarsimp simp: typ_at'_def ko_wp_at'_def obj_at'_def project_inject opt_map_def
                      split: option.splits)
      apply (simp add: typ_at'_def ko_wp_at'_def obj_at'_def project_inject opt_map_def)
     apply (simp add: typ_at'_def ko_wp_at'_def obj_at'_def project_inject opt_map_def)
    \<comment> \<open>ready_queues_relation and release_queue_relation\<close>
    apply (prop_tac "typ_at' (koTypeOf (injectKO r2)) ptr b")
     apply (simp add: typ_at'_def ko_wp_at'_def)
    by (fastforce dest!: tcbs_of'_non_tcb_update)
qed

lemma sc_at'_cross:
  assumes p: "pspace_relation (kheap s) (ksPSpace s')"
  assumes t: "sc_at' ptr s'"
  shows "sc_at ptr s" using assms
  apply (clarsimp simp: obj_at'_def)
  apply (erule (1) pspace_dom_relatedE)
  by (clarsimp simp: obj_relation_cuts_def2 obj_at_def is_sc_obj cte_relation_def
                     other_obj_relation_def other_aobj_relation_def pte_relation_def tcb_relation_cut_def
              split: Structures_A.kernel_object.split_asm if_split_asm
                     arch_kernel_obj.split_asm)

lemma sc_obj_at'_cross:
  assumes p: "pspace_relation (kheap s) (ksPSpace s')"
  assumes t: "obj_at' (\<lambda>sc::sched_context. scSize sc = n) ptr s'"
  shows "sc_obj_at n ptr s" using assms
  apply (clarsimp simp: obj_at'_def)
  apply (erule (1) pspace_dom_relatedE)
  by (clarsimp simp: obj_relation_cuts_def2 obj_at_def is_sc_obj cte_relation_def
                     objBits_simps scBits_simps other_obj_relation_def
                     other_aobj_relation_def pte_relation_def sc_relation_def tcb_relation_cut_def
              split: Structures_A.kernel_object.split_asm if_split_asm
                     arch_kernel_obj.split_asm)

lemma setSchedContext_corres:
  assumes R': "sc_relation sc n sc'"
  assumes s: "n = scSize sc'"
  shows
    "corres dc
       \<top>
       (obj_at' (\<lambda>k::sched_context. objBits k = objBits sc') ptr
        and (\<lambda>s'. heap_ls (replyPrevs_of s') (scReply sc') (sc_replies sc)))
       (set_object ptr (kernel_object.SchedContext sc n)) (setSchedContext ptr sc')"
  proof -
  have z: "\<And>s. sc_at' ptr s
               \<Longrightarrow> map_to_ctes ((ksPSpace s) (ptr \<mapsto> injectKO sc')) = map_to_ctes (ksPSpace s)"
    by (clarsimp simp: gen_obj_at_simps)
  show ?thesis
    apply (insert R' s)
    apply (clarsimp simp: setSchedContext_def)
    apply (rule corres_no_failI)
     apply (rule no_fail_pre)
      apply wp
      apply clarsimp
     apply clarsimp
    apply clarsimp
    apply (rename_tac s s' rv; prop_tac "sc_obj_at n ptr s")
     apply (fastforce intro!: sc_obj_at'_cross dest: state_relation_pspace_relation
                        simp: obj_at'_def gen_objBits_simps)
    apply (clarsimp simp: obj_at_def is_sc_obj_def obj_at'_def)
    apply (unfold update_sched_context_def set_object_def setObject_def)
    apply (clarsimp simp: in_monad split_def bind_def gets_def get_def Bex_def
                          put_def return_def modify_def get_object_def2
                          obj_at_def a_type_def updateObject_default_def in_magnitude_check[OF _]
                   split: Structures_A.kernel_object.splits)
    apply (prop_tac "obj_at (same_caps (kernel_object.SchedContext sc n)) ptr s")
     apply (clarsimp simp: obj_at_def)
    apply (clarsimp simp: state_relation_def
                          z[simplified obj_at'_def is_sc_obj_def projectKO_eq projectKO_opts_defs, simplified])
    apply (clarsimp simp: caps_of_state_after_update cte_wp_at_after_update
                              swp_def fun_upd_def obj_at_def)
    apply (subst conj_assoc[symmetric])
    apply (extract_conjunct \<open>match conclusion in "ghost_relation _ _ _" \<Rightarrow> -\<close>)
     apply (clarsimp simp: ghost_relation_def)
     apply (erule_tac x=ptr in allE)+
     apply (clarsimp simp: obj_at_def a_type_def
                     split: Structures_A.kernel_object.splits if_split_asm)
    apply (extract_conjunct \<open>match conclusion in "pspace_relation _ _" \<Rightarrow> -\<close>)
    apply (fold fun_upd_def)
    apply (simp only: pspace_relation_def simp_thms
                      pspace_dom_update[where x="kernel_object.SchedContext _ _"
                                          and v="kernel_object.SchedContext _ _",
                                        simplified a_type_def, simplified])
    apply (simp only: dom_fun_upd2 simp_thms)
    apply (elim conjE)
    apply (frule bspec, erule domI)
     apply (rule ballI, drule(1) bspec)
     apply (drule domD)
     apply (clarsimp simp: project_inject split: if_split_asm kernel_object.split_asm)
     apply (rename_tac sc0 x bb aa ba)
     apply (drule_tac x="(aa, ba)" in bspec, simp)
     apply clarsimp
     apply (frule_tac ko'="kernel_object.SchedContext sc0 n" and x'=ptr
              in obj_relation_cut_same_type)
        apply simp+
     apply (clarsimp simp: a_type_def split: Structures_A.kernel_object.split_asm if_split_asm)
    apply (extract_conjunct \<open>match conclusion in "sc_replies_relation_2 _ _ _" \<Rightarrow> -\<close>)
     apply (clarsimp simp: sc_replies_relation_def sc_replies_of_scs_def map_project_def scs_of_kh_def)
     apply (drule_tac x=p in spec)
     subgoal
       by (auto simp: typ_at'_def ko_wp_at'_def opt_map_def projectKO_opts_defs
               split: if_splits)
    apply (prop_tac "typ_at' (koTypeOf (injectKO sc')) ptr s'")
     apply (clarsimp simp: obj_at'_def typ_at'_def ko_wp_at'_def)
    apply (prop_tac "koTypeOf (injectKO sc') \<noteq> TCBT", simp)
    by (fastforce dest: tcbs_of'_non_tcb_update)
qed

lemma setSchedContext_update_corres_Q:
  assumes R': "\<lbrakk>sc_relation sc n sc'; Q sc; Q' sc'\<rbrakk>
               \<Longrightarrow> sc_relation (f sc) n (f' (sc'::sched_context))"
  assumes s: "objBits sc' = objBits (f' sc')"
  shows
    "corres dc
       (\<lambda>s. kheap s ptr = Some (kernel_object.SchedContext sc n) \<and> Q sc)
       (obj_at' (\<lambda>obj. obj = sc' \<and> Q' sc') ptr
        and (\<lambda>s'. heap_ls (replyPrevs_of s') (scReply (f' sc')) (sc_replies (f sc))))
       (set_object ptr (kernel_object.SchedContext (f sc) n))
       (setSchedContext ptr (f' sc'))"
  apply (insert R' s)
  apply (rule_tac F="sc_relation sc n sc' \<and> Q sc \<and> Q' sc'" in corres_req)
   apply (drule state_relation_pspace_relation)
   apply clarsimp
   apply (drule (1) pspace_relation_absD)
   apply (clarsimp simp: obj_at'_def split: if_split_asm)
  apply (rule corres_guard_imp)
    apply (rule setSchedContext_corres)
     apply fastforce
    apply (clarsimp simp: obj_at'_def sc_relation_def gen_objBits_simps)
   apply fastforce
  apply (clarsimp simp: obj_at'_def sc_relation_def)
  done

lemmas setSchedContext_update_corres =
  setSchedContext_update_corres_Q[where Q=\<top> and Q'=\<top>, simplified]

lemma setSchedContext_no_stack_update_corres_Q:
  "\<lbrakk>\<lbrakk>sc_relation sc n sc'; Q sc; Q' sc'\<rbrakk> \<Longrightarrow> sc_relation (f sc) n (f' sc');
    sc_replies sc = sc_replies (f sc); objBits sc' = objBits (f' sc');
    scReply sc' = scReply (f' sc')\<rbrakk> \<Longrightarrow>
   corres dc
     (\<lambda>s. kheap s ptr = Some (kernel_object.SchedContext sc n) \<and> Q sc)
     (obj_at' (\<lambda>obj. obj = sc' \<and> Q' sc') ptr)
     (set_object ptr (kernel_object.SchedContext (f sc) n))
     (setSchedContext ptr (f' sc'))"
  apply (rule_tac F="sc_relation sc n sc' \<and> Q sc \<and> Q' sc'" in corres_req)
   apply (drule state_relation_pspace_relation)
   apply clarsimp
   apply (drule (1) pspace_relation_absD)
   apply (clarsimp simp: obj_at'_def split: if_split_asm)
  apply (rule stronger_corres_guard_imp)
    apply (rule setSchedContext_update_corres[where sc=sc and sc'=sc'])
     apply simp+
  apply (clarsimp dest!: state_relation_sc_replies_relation
                   simp: obj_at'_def)
  apply (drule (2) sc_replies_relation_prevs_list)
  by fastforce

lemmas setSchedContext_no_stack_update_corres =
  setSchedContext_no_stack_update_corres_Q[where Q=\<top> and Q'=\<top>, simplified]

lemma setSchedContext_update_sched_context_no_stack_update_corres_Q:
  "\<lbrakk>\<And>sc n sc'. \<lbrakk>sc_relation sc n sc'; Q sc; Q' sc'\<rbrakk> \<Longrightarrow> sc_relation (f sc) n (f' sc');
    \<forall>sc. sc_replies sc = sc_replies (f sc); objBits sc' = objBits (f' sc');
    scReply sc' = scReply (f' sc')\<rbrakk> \<Longrightarrow>
   corres dc
     (\<lambda>s. \<exists>sc n. kheap s ptr = Some (kernel_object.SchedContext sc n) \<and> Q sc)
     (obj_at' (\<lambda>obj. obj = sc' \<and> Q' sc') ptr)
     (update_sched_context ptr f) (setSchedContext ptr (f' sc'))"
  apply (clarsimp simp: update_sched_context_def)
  apply (rule corres_symb_exec_l[rotated 2, OF get_object_sp])
    apply (find_goal \<open>match conclusion in "\<lbrace>P\<rbrace> f \<exists>\<lbrace>Q\<rbrace>" for P f Q \<Rightarrow> -\<close>)
    apply (fastforce intro: get_object_exs_valid
                      simp: obj_at_def)
   apply wpsimp
   apply (clarsimp simp: obj_at_def)
  apply (rename_tac obj, case_tac obj;
         clarsimp, (solves \<open>clarsimp simp: obj_at_def is_sc_obj_def corres_underlying_def\<close>)?)
  apply (clarsimp simp: pred_conj_def)
  apply (rule abs_ex_lift_corres)
  apply clarsimp
  apply (rule abs_ex_lift_corres)
  apply (rule_tac F="sc_relation sc n sc' \<and> Q sc \<and> Q' sc'" in corres_req)
   apply (fastforce dest: state_relation_pspace_relation pspace_relation_absD
                    simp: obj_at'_def split: if_split_asm)
  apply (corres corres: setSchedContext_no_stack_update_corres_Q[where f=f and f'=f']
                  simp: gen_obj_at_simps)
  done

lemma setSchedContext_update_sched_context_no_stack_update_corres:
  "\<lbrakk>\<And>sc n sc'. sc_relation sc n sc' \<Longrightarrow> sc_relation (f sc) n (f' sc');
    \<forall>sc. sc_replies sc = sc_replies (f sc); objBits sc' = objBits (f' sc');
    scReply sc' = scReply (f' sc')\<rbrakk> \<Longrightarrow>
   corres dc (sc_at ptr) (ko_at' sc' ptr)
     (update_sched_context ptr f) (setSchedContext ptr (f' sc'))"
  apply (rule corres_guard_imp)
    apply (rule setSchedContext_update_sched_context_no_stack_update_corres_Q
                 [where Q=\<top> and Q'=\<top> and f=f and f'=f'];
           fastforce?)
   apply (clarsimp simp: obj_at_def is_sc_obj_def)
   apply (rename_tac ko n, case_tac ko; clarsimp)
  apply fastforce
  done

lemma tcb_at'_cross:
  assumes p: "pspace_relation (kheap s) (ksPSpace s')"
  assumes t: "tcb_at' ptr s'"
  shows "tcb_at ptr s"
  using assms
  apply (clarsimp simp: obj_at'_def)
  apply (erule (1) pspace_dom_relatedE)
  by (clarsimp simp: obj_relation_cuts_def2 obj_at_def  cte_relation_def
                     other_obj_relation_def pte_relation_def is_tcb_def
              split: Structures_A.kernel_object.split_asm if_split_asm arch_kernel_obj.split_asm)

lemma st_tcb_at_runnable_cross:
  "\<lbrakk> st_tcb_at runnable t s; pspace_aligned s; pspace_distinct s; (s, s') \<in> state_relation \<rbrakk>
   \<Longrightarrow> st_tcb_at' runnable' t s'"
  apply (drule (3) st_tcb_at_coerce_concrete)
  by (clarsimp simp: pred_tcb_at'_def obj_at'_def sts_rel_runnable)

lemma st_tcb_at_activatable_cross:
  "\<lbrakk>st_tcb_at activatable t s; pspace_aligned s; pspace_distinct s; (s, s') \<in> state_relation\<rbrakk>
   \<Longrightarrow> st_tcb_at' activatable' t s'"
  apply (drule (3) st_tcb_at_coerce_concrete)
  by (clarsimp simp: pred_tcb_at'_def obj_at'_def sts_rel_activatable)

lemma bound_sc_tcb_at_cross:
  assumes t: "bound_sc_tcb_at P t s"
  assumes sr: "(s, s') \<in> state_relation" "pspace_aligned s" "pspace_distinct s"
  shows "tcb_at' t s' \<and> P (tcbSCs_of s' t)"
  using assms
  apply (clarsimp simp: state_relation_def pred_tcb_at_def obj_at_def)
  apply (frule (1) pspace_distinct_cross, fastforce simp: state_relation_def)
  apply (frule pspace_aligned_cross, fastforce simp: state_relation_def)
  apply (prop_tac "tcb_at t s", clarsimp simp: obj_at_def is_tcb)
  apply (drule (2) tcb_at_cross[rotated], fastforce simp: state_relation_def)
  apply (clarsimp simp: state_relation_def pred_tcb_at'_def obj_at'_def opt_map_red)
  apply (erule (1) pspace_dom_relatedE)
  apply (erule (1) obj_relation_cutsE, simp_all)
   apply (clarsimp simp: st_tcb_at'_def obj_at'_def other_obj_relation_def tcb_relation_def
                  split: Structures_A.kernel_object.split_asm if_split_asm)+
  done

lemma bound_yt_tcb_at_cross:
  assumes t: "bound_yt_tcb_at P t s"
  assumes sr: "(s, s') \<in> state_relation" "pspace_aligned s" "pspace_distinct s"
  shows "obj_at' (\<lambda>tcb'. \<exists>tcb. tcb_relation tcb tcb' \<and> P (tcb_yield_to tcb)) t s'"
  using assms
  apply (clarsimp simp: state_relation_def pred_tcb_at_def obj_at_def)
  apply (frule (1) pspace_distinct_cross, fastforce simp: state_relation_def)
  apply (frule pspace_aligned_cross, fastforce simp: state_relation_def)
  apply (prop_tac "tcb_at t s", clarsimp simp: st_tcb_at_def obj_at_def is_tcb)
  apply (drule (2) tcb_at_cross[rotated], fastforce simp: state_relation_def)
  apply (clarsimp simp: state_relation_def pred_tcb_at'_def obj_at'_def)
  apply (erule (1) pspace_dom_relatedE)
  apply (erule (1) obj_relation_cutsE, simp_all)
    apply (fastforce simp: st_tcb_at'_def obj_at'_def other_obj_relation_def tcb_relation_def
                    split: Structures_A.kernel_object.split_asm if_split_asm)+
  done

lemma sc_tcb_sc_at_bound_cross:
  "\<lbrakk>pspace_relation (kheap s) (ksPSpace s'); valid_objs s; pspace_aligned s; pspace_distinct s;
    sc_tcb_sc_at ((\<noteq>) None) scp s\<rbrakk>
  \<Longrightarrow> obj_at' (\<lambda>sc. \<exists>y. scTCB sc = Some y) scp s'"
  apply (clarsimp simp: obj_at_def sc_tcb_sc_at_def)
  apply (frule (1) pspace_relation_absD)
  apply clarsimp
  apply (prop_tac "valid_sched_context_size n")
   apply (erule (1) valid_sched_context_size_objsI)
  apply (clarsimp simp: if_split_asm)
  apply (rename_tac z; case_tac z; simp)
  apply (drule (3) aligned_distinct_ko_at'I[where 'a=sched_context], simp)
  apply (clarsimp simp: obj_at'_def sc_relation_def)
  by (metis not_None_eq)

lemma cur_tcb_cross:
  "\<lbrakk> cur_tcb s; pspace_aligned s; pspace_distinct s; (s,s') \<in> state_relation \<rbrakk> \<Longrightarrow> cur_tcb' s'"
  apply (clarsimp simp: cur_tcb'_def cur_tcb_def state_relation_def)
  apply (erule (3) tcb_at_cross)
  done

lemma cur_sc_tcb_cross:
  "\<lbrakk>(s, s') \<in> state_relation; valid_objs s; pspace_aligned s; pspace_distinct s;
    cur_sc_tcb s; schact_is_rct s\<rbrakk>
  \<Longrightarrow> obj_at' (\<lambda>sc. scTCB sc = Some (ksCurThread s')) (ksCurSc s') s'"
  apply (clarsimp simp: obj_at_def sc_tcb_sc_at_def cur_sc_tcb_def
                 dest!: schact_is_rct state_relationD)
  apply (frule (1) pspace_relation_absD)
  apply clarsimp
  apply (prop_tac "valid_sched_context_size n")
   apply (erule (1) valid_sched_context_size_objsI)
  apply (clarsimp simp: if_split_asm)
  apply (rename_tac z; case_tac z; simp)
  apply (drule (3) aligned_distinct_ko_at'I[where 'a=sched_context], simp)
  apply (clarsimp simp: obj_at'_def sc_relation_def)
  done

lemma reply_at_cross:
  assumes p: "pspace_relation (kheap s) (ksPSpace s')"
  assumes ps: "pspace_aligned s" "pspace_distinct s"
  assumes t: "reply_at ptr s"
  shows "reply_at' ptr s'"
  using assms
  apply (clarsimp simp: obj_at_def is_reply)
  apply (drule (1) pspace_relation_absD, clarsimp)
  apply (case_tac z; simp)
  by (fastforce dest!: aligned_distinct_ko_at'I[where 'a=reply] elim: obj_at'_weakenE)

lemma ep_at_cross:
  assumes p: "pspace_relation (kheap s) (ksPSpace s')"
  assumes ps: "pspace_aligned s" "pspace_distinct s"
  assumes t: "ep_at ptr s"
  shows "ep_at' ptr s'"
  using assms
  apply (clarsimp simp: obj_at_def is_ep)
  apply (drule (1) pspace_relation_absD, clarsimp simp: other_obj_relation_def)
  apply (case_tac z; simp)
  by (fastforce dest!: aligned_distinct_ko_at'I[where 'a=endpoint] elim: obj_at'_weakenE)

lemma setEndpoint_corres:
  "ep_relation e e' \<Longrightarrow>
   corres dc
     (ep_at ptr and pspace_aligned and pspace_distinct) \<top>
     (set_endpoint ptr e) (setEndpoint ptr e')"
  apply (rule_tac Q'="ep_at' ptr" in corres_cross_add_guard)
   apply (fastforce dest!: state_relationD elim!: ep_at_cross)
  apply (simp add: set_simple_ko_def setEndpoint_def is_ep_def[symmetric])
    apply (corresK_search search: setObject_other_corres_ep[where P="\<lambda>_. True"])
  apply (corresKsimp wp: get_object_ret get_object_wp)+
  by (fastforce simp: is_ep gen_obj_at_simps objBits_defs partial_inv_def)

lemma ntfn_at_cross:
  assumes p: "pspace_relation (kheap s) (ksPSpace s')"
  assumes ps: "pspace_aligned s" "pspace_distinct s"
  assumes t: "ntfn_at ptr s"
  shows "ntfn_at' ptr s'"
  using assms
  apply (clarsimp simp: obj_at_def is_ntfn)
  apply (drule (1) pspace_relation_absD, clarsimp simp: other_obj_relation_def)
  apply (case_tac z; simp)
  by (fastforce dest!: aligned_distinct_ko_at'I[where 'a=notification] elim: obj_at'_weakenE)

lemma sc_at_cross:
  assumes p: "pspace_relation (kheap s) (ksPSpace s')"
  assumes ps: "pspace_aligned s" "pspace_distinct s"
  assumes t: "sc_at ptr s"
  shows "sc_at' ptr s'"
  using assms
  apply (clarsimp simp: obj_at_def is_sc_obj)
  apply (drule (1) pspace_relation_absD, clarsimp)
  apply (case_tac z; simp)
  by (fastforce dest!: aligned_distinct_ko_at'I[where 'a=sched_context] elim: obj_at'_weakenE)

lemma sc_at_cross_valid_objs:
  assumes p: "pspace_relation (kheap s) (ksPSpace s')"
  assumes ps: "pspace_aligned s" "pspace_distinct s"
  assumes t: "pred_map \<top> (scs_of s) ptr"
  assumes v: "valid_objs s"
  shows "sc_at' ptr s'"
  using assms
  apply (clarsimp simp: vs_all_heap_simps obj_at_def is_sc_obj)
  apply (frule (1) pspace_relation_absD, clarsimp)
  apply (frule valid_objs_valid_sched_context_size)
   apply fastforce
  apply clarsimp
  apply (rename_tac obj, case_tac obj; simp)
  by (fastforce dest!: aligned_distinct_ko_at'I[where 'a=sched_context] elim: obj_at'_weakenE)

lemma sc_at'_cross_rel:
  "cross_rel (pspace_aligned and pspace_distinct and sc_at t) (sc_at' t)"
  unfolding cross_rel_def state_relation_def
  apply clarsimp
  by (erule (3) sc_at_cross)

lemma sc_obj_at_cross:
  assumes p: "pspace_relation (kheap s) (ksPSpace s')"
  assumes ps: "pspace_aligned s" "pspace_distinct s"
  assumes t: "sc_obj_at n ptr s"
  shows "obj_at' (\<lambda>sc::sched_context. objBits sc = minSchedContextBits + n) ptr s'"
  using assms
  apply (clarsimp simp: obj_at_def is_sc_obj)
  apply (drule (1) pspace_relation_absD, clarsimp)
  apply (case_tac z; simp)
  apply (rename_tac sc')
  apply (drule (3) aligned_distinct_ko_at'I[where 'a=sched_context], simp)
  by (clarsimp simp: scBits_simps gen_objBits_simps sc_relation_def obj_at'_def)

lemma real_cte_at_cross:
  assumes p: "pspace_relation (kheap s) (ksPSpace s')"
  assumes ps: "pspace_aligned s" "pspace_distinct s"
  assumes t: "real_cte_at ptr s"
  shows "real_cte_at' (cte_map ptr) s'"
  using assms
  apply (clarsimp simp: obj_at_def is_ntfn)
  apply (drule (1) pspace_relation_absD)
  apply (clarsimp simp: is_cap_table other_obj_relation_def well_formed_cnode_n_def)
  apply (prop_tac "\<exists>z. ksPSpace s' (cte_map (fst ptr, snd ptr)) = Some z \<and>
    cte_relation (snd ptr) (CNode (length (snd ptr)) cs) z")
  apply fastforce
  apply (clarsimp split: kernel_object.split_asm simp: cte_relation_def)
  by (fastforce dest!: aligned_distinct_ko_at'I[where 'a=cte] elim: obj_at'_weakenE)

lemma valid_tcb_state_cross:
  assumes "pspace_relation (kheap s) (ksPSpace s')"
          "thread_state_relation ts ts'"
          "pspace_aligned s"
          "pspace_distinct s"
          "valid_tcb_state ts s"
  shows "valid_tcb_state' ts' s'" using assms
  by (fastforce dest: ep_at_cross reply_at_cross ntfn_at_cross
                simp: valid_bound_obj'_def valid_tcb_state_def valid_tcb_state'_def
               split: Structures_A.thread_state.split_asm option.split_asm)

lemma state_refs_of_cross_eq:
  "\<lbrakk>(s, s') \<in> state_relation; pspace_aligned s; pspace_distinct s\<rbrakk>
       \<Longrightarrow> state_refs_of' s' = state_refs_of s"
  apply (rule sym)
  apply (rule ext, rename_tac p)
  apply (frule state_relation_pspace_relation)
  apply (frule (2) pspace_distinct_cross)
  apply (frule (1) pspace_aligned_cross)
  apply (clarsimp simp: state_refs_of_def state_refs_of'_def
                 split: option.split)
  apply (rule conjI; clarsimp)
   apply (rename_tac ko')
   apply (erule (1) pspace_dom_relatedE)
   apply (rename_tac ko P; case_tac ko; clarsimp split: if_split_asm simp: cte_relation_def)
   apply (rename_tac ako; case_tac ako; clarsimp simp: pte_relation_def)
  apply (rule conjI; clarsimp)
   apply (drule (1) pspace_relation_None; clarsimp)
  apply (rule conjI[rotated]; clarsimp)
   apply (frule pspace_relation_pspace_bounded'[OF state_relation_pspace_relation])
   apply (frule pspace_alignedD'; frule pspace_boundedD'; clarsimp dest!: pspace_distinctD')
  apply (rename_tac ko ko')
  apply (frule (1) pspace_relation_absD)
  apply (case_tac ko; clarsimp split: if_split_asm)
        apply (rename_tac n sz, drule_tac x=p and y="cte_relation (replicate n False)" in spec2)
        apply (fastforce simp: cte_relation_def cte_map_def well_formed_cnode_n_def)
       apply (find_goal \<open>match premises in "_ = Some (ArchObj _)" \<Rightarrow> -\<close>)
       apply (rename_tac ako; case_tac ako; simp)
          apply (case_tac ko'; clarsimp simp: other_aobj_relation_def)
         apply ((drule_tac x=0 in spec, clarsimp simp:  pte_relation_def)+)[1]
       apply (drule_tac x=p in spec)
       apply (rename_tac b sz)
       apply (drule_tac x="\<lambda>_ obj. obj = (if b then KOUserDataDevice else KOUserData)" in spec, clarsimp)
       apply (simp only: imp_ex)
       apply (drule_tac x=0 in spec, clarsimp simp: pageBitsForSize_def ptTranslationBits_def
                                             split: vmpage_size.split_asm)
      apply (all \<open>case_tac ko'; clarsimp simp: other_obj_relation_def tcb_relation_cut_def\<close>)
      apply (rename_tac tcb tcb';
             clarsimp simp: tcb_relation_def arch_tcb_relation_def fault_rel_optionation_def
                            thread_state_relation_def tcb_st_refs_of_def tcb_st_refs_of'_def;
             rename_tac tcb'; case_tac "tcb_state tcb"; case_tac "tcbState tcb'";
             clarsimp simp: tcb_bound_refs'_def get_refs_def2 split: option.splits)
     apply (clarsimp simp: ep_q_refs_of_def ep_relation_def split: Structures_A.endpoint.splits)
    apply (clarsimp simp: ntfn_q_refs_of_def ntfn_relation_def split: Structures_A.ntfn.splits)
   apply (clarsimp simp: sc_relation_def get_refs_def2)
   apply (drule state_relation_sc_replies_relation)
   apply (frule sc_replies_relation_scReplies_of)
     apply (fastforce simp: obj_at_def is_sc_obj_def)
    apply (clarsimp simp: opt_map_def)
   apply (clarsimp simp: opt_map_def sc_replies_of_scs_def map_project_def scs_of_kh_def)
  apply (clarsimp simp: reply_relation_def split: Structures_A.ntfn.splits)
  done

lemma state_refs_of_cross:
  "\<lbrakk>P (state_refs_of s); (s, s') \<in> state_relation; pspace_aligned s; pspace_distinct s\<rbrakk>
      \<Longrightarrow> P (state_refs_of' s')"
  by (clarsimp simp: state_refs_of_cross_eq elim!: rsubst[where P=P])

lemma ct_not_inQ_cross:
  "\<lbrakk>(s, s') \<in> state_relation; ct_not_in_q s; cur_tcb s; pspace_aligned s;
    pspace_distinct s\<rbrakk>
   \<Longrightarrow> ct_not_inQ s'"
  apply (frule state_relation_ready_queues_relation)
  apply (frule state_relation_sched_act_relation)
  apply (frule (3) cur_tcb_cross)
  apply (clarsimp simp: ct_not_inQ_def ct_not_in_q_def)
   apply (case_tac "scheduler_action s"; clarsimp)
  apply (clarsimp simp: not_queued_def)
  apply (rule ccontr)
  apply (prop_tac "obj_at' tcbQueued (ksCurThread s') s'")
   apply (clarsimp simp: gen_obj_at_simps cur_tcb'_def)
  apply normalise_obj_at'
  apply (rename_tac tcb)
  apply (drule_tac x="tcbDomain tcb" in spec)
  apply (drule_tac x="tcbPriority tcb" in spec)
  apply (clarsimp simp: ready_queues_relation_def ready_queue_relation_def list_queue_relation_def
                        Let_def)
  apply (drule_tac x="tcbDomain tcb" in spec)
  apply (drule_tac x="tcbPriority tcb" in spec)
  apply (fastforce simp: curthread_relation inQ_def in_opt_pred obj_at'_def opt_map_red)
  done

lemma sch_act_wf_cross:
  "\<lbrakk>(s,s') \<in> state_relation; valid_sched_action s; cur_tcb s; pspace_aligned s; pspace_distinct s\<rbrakk>
   \<Longrightarrow> sch_act_wf (ksSchedulerAction s') s'"
  apply (clarsimp simp: sch_act_wf_def)
  apply (cases "ksSchedulerAction s'"; clarsimp)
   apply (prop_tac "scheduler_action s = resume_cur_thread")
    apply (clarsimp simp: state_relation_def)
    apply (metis sched_act_relation.simps Structures_A.scheduler_action.exhaust
                 scheduler_action.simps)
   apply (frule curthread_relation)
   apply (frule state_relation_pspace_relation)
   apply (frule (2) cur_tcb_cross)
    apply fastforce
   apply (clarsimp simp: valid_sched_action_def is_activatable_def vs_all_heap_simps
                         ct_in_state'_def st_tcb_at'_def)
   apply (clarsimp simp: pspace_relation_def)
   apply (drule_tac x="cur_thread s" in bspec, fastforce)
   apply (drule_tac x="(cur_thread s, tcb_relation_cut)" in bspec, fastforce)
   apply (clarsimp simp: tcb_relation_cut_def)
   apply (rename_tac tcb)
   apply (case_tac "tcb_state tcb"; clarsimp simp: tcb_relation_def gen_obj_at_simps cur_tcb'_def)
  apply (rename_tac target)
  apply (clarsimp simp: valid_sched_action_def weak_valid_sched_action_def vs_all_heap_simps)
  apply (prop_tac "scheduler_action s = switch_thread target")
   apply (clarsimp simp: state_relation_def)
   apply (metis sched_act_relation.simps Structures_A.scheduler_action.exhaust
                scheduler_action.simps)
  apply (prop_tac "tcb_at' target s'")
   apply (fastforce intro!: tcb_at_cross
                      simp: obj_at_def is_tcb_def)
  apply (frule state_relation_pspace_relation)
  apply (clarsimp simp: pspace_relation_def)
  apply (drule_tac x=target in bspec, fastforce)
  apply (drule_tac x="(target, tcb_relation_cut)" in bspec, fastforce)
  apply (clarsimp simp: other_obj_relation_def)
  apply (intro conjI)
   apply (fastforce intro!: st_tcb_at_runnable_cross
                      simp: obj_at_def pred_tcb_at_def)
  apply (clarsimp simp: tcb_relation_def gen_obj_at_simps switch_in_cur_domain_def
                        state_relation_def in_cur_domain_def tcb_in_cur_domain'_def
                        etcb_at'_def vs_all_heap_simps tcb_relation_cut_def)
  done

lemma ct_idle_or_in_cur_domain'_cross:
  "\<lbrakk>(s,s') \<in> state_relation; ct_in_cur_domain s; cur_tcb s; pspace_aligned s; pspace_distinct s\<rbrakk>
   \<Longrightarrow> ct_idle_or_in_cur_domain' s'"
  apply (clarsimp simp: ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def ct_in_cur_domain_def)
  apply (case_tac "cur_thread s = idle_thread s"; clarsimp)
   apply (clarsimp simp: state_relation_def)
  apply (frule curthread_relation)
  apply (frule (2) cur_tcb_cross)
   apply fastforce
  apply (prop_tac "scheduler_action s = resume_cur_thread")
   apply (clarsimp simp: state_relation_def)
   apply (metis sched_act_relation.simps Structures_A.scheduler_action.exhaust
                scheduler_action.simps)
  apply (clarsimp simp: in_cur_domain_def etcb_at_def vs_all_heap_simps gen_obj_at_simps cur_tcb'_def)
  apply (frule state_relation_pspace_relation)
  apply (clarsimp simp: pspace_relation_def)
  apply (drule_tac x="cur_thread s" in bspec)
   apply (clarsimp simp: cur_tcb_def obj_at_def)
  apply (drule_tac x="(cur_thread s, tcb_relation_cut)" in bspec)
   apply (clarsimp simp: cur_tcb_def obj_at_def is_tcb_def)
   apply (rename_tac tcb)
   apply (case_tac tcb; clarsimp)
  apply (clarsimp simp: cur_tcb_def obj_at_def is_tcb_def)
  apply (rename_tac tcb)
  apply (case_tac tcb; clarsimp)
  apply (clarsimp simp: tcb_relation_cut_def tcb_relation_def state_relation_def)
  done

lemma valid_idle'_cross:
  "\<lbrakk>(s,s') \<in> state_relation; valid_idle s; pspace_aligned s; pspace_distinct s; valid_objs s\<rbrakk>
   \<Longrightarrow> valid_idle' s'"
  apply (clarsimp simp: valid_idle'_def valid_idle_def pred_tcb_at_def obj_at_def)
  apply (prop_tac "ksIdleThread s' = idle_thread s")
   apply (clarsimp simp: state_relation_def)
  apply clarsimp
  apply (prop_tac "tcb_at' (ksIdleThread s') s'")
   apply (fastforce intro!: tcb_at_cross simp: obj_at_def state_relation_def is_tcb_def)
  apply (prop_tac "sc_at' (idle_sc_ptr) s'")
   apply (fastforce intro!: sc_at_cross valid_objs_valid_sched_context_size
                      simp: obj_at_def state_relation_def is_sc_obj_def)
  apply (frule state_relation_pspace_relation)
  apply (clarsimp simp: pspace_relation_def)
  apply (intro conjI)
   apply (drule_tac x="idle_thread s" in bspec, fastforce)
   apply (drule_tac x="(idle_thread s, tcb_relation_cut)" in bspec, fastforce)
   apply (clarsimp simp: gen_obj_at_simps idle_tcb'_def tcb_relation_def tcb_relation_cut_def)
  apply (drule_tac x="idle_sc_ptr" in bspec, fastforce)
  apply (drule_tac x="(idle_sc_ptr, sc_relation_cut)" in bspec)
   apply (fastforce intro: valid_objs_valid_sched_context_size)
  by (fastforce dest: sc_replies_prevs_walk
                simp: heap_walk_Nil_None gen_obj_at_simps sc_relation_def state_relation_def)

lemma ready_qs_runnable_cross:
  "\<lbrakk>(s, s') \<in> state_relation; pspace_aligned s; pspace_distinct s; valid_ready_qs s\<rbrakk>
   \<Longrightarrow> ready_qs_runnable s'"
  apply (clarsimp simp: ready_qs_runnable_def)
  apply normalise_obj_at'
  apply (frule state_relation_ready_queues_relation)
  apply (clarsimp simp: ready_queues_relation_def ready_queue_relation_def Let_def
                        list_queue_relation_def)
  apply (drule_tac x="tcbDomain ko" in spec)
  apply (drule_tac x="tcbPriority ko" in spec)
  apply (clarsimp simp: valid_ready_qs_def)
  apply (drule_tac x="tcbDomain ko" in spec)
  apply (drule_tac x="tcbPriority ko" in spec)
  apply clarsimp
  apply (drule_tac x=t in bspec)
   apply (fastforce simp: inQ_def in_opt_pred obj_at'_def opt_map_red)
  apply (fastforce dest: st_tcb_at_runnable_cross
              simp flip: tcb_at_kh_simps
                   simp: obj_at'_def st_tcb_at'_def)
  done

lemma replyTCBs_of_cross:
  "\<lbrakk>(s, s') \<in> state_relation; reply_tcb_reply_at P rptr s\<rbrakk>
   \<Longrightarrow> P (replyTCBs_of s' rptr)"
  apply (clarsimp simp: reply_at_ppred_def obj_at_def state_relation_def)
  apply (drule (1) pspace_relation_absD, clarsimp simp: other_obj_relation_def)
  apply (case_tac z; simp)
  apply (clarsimp simp: opt_map_def reply_relation_def)
  done

lemma replySCs_of_cross:
  "\<lbrakk>(s, s') \<in> state_relation; reply_sc_reply_at P rptr s\<rbrakk>
   \<Longrightarrow> P (replySCs_of s' rptr)"
  apply (clarsimp simp: reply_at_ppred_def obj_at_def is_tcb state_relation_def)
  apply (drule (1) pspace_relation_absD, clarsimp simp: other_obj_relation_def)
  apply (case_tac z; simp)
  apply (clarsimp simp: opt_map_def reply_relation_def)
  done

lemma valid_replies_sc_cross:
  "\<lbrakk>(s, s') \<in> state_relation; valid_replies s; sym_refs (state_refs_of s);
    pspace_aligned s; pspace_distinct s; reply_at rptr s\<rbrakk>
   \<Longrightarrow> valid_replies'_sc_asrt rptr s'"
  apply (clarsimp simp: valid_replies_defs valid_replies'_sc_asrt_def elim!: opt_mapE)
  apply (rename_tac scptr rp)
  apply (prop_tac "sc_replies_sc_at (\<lambda>rs. rptr \<in> set rs) scptr s")
   apply (frule_tac sc_ptr=scptr and reply_ptr=rptr in sym_refs_sc_replies_sc_at)
    apply (rule ccontr)
    apply (drule not_sk_obj_at_pred)
     apply (fastforce simp: sk_obj_at_pred_def obj_at_def is_obj_defs)
    apply (frule (1) replySCs_of_cross)
    apply (clarsimp simp: obj_at'_def opt_map_def)
   apply (clarsimp simp: sc_at_pred_n_eq_commute sc_at_ppred_def obj_at_def)
  apply (drule subsetD, force)
  apply (clarsimp simp: pred_tcb_at_eq_commute[symmetric])
  apply (frule (1) st_tcb_reply_state_refs)
  apply (drule (3) st_tcb_at_coerce_concrete)
  apply (drule replyTCBs_of_cross[where P="\<lambda>rtcb. rtcb = (Some tptr)" for tptr])
   apply (fastforce simp: sk_obj_at_pred_def2)
  apply (clarsimp simp: pred_tcb_at'_def obj_at'_def)
  done

lemma getCurThread_sp:
  "\<lbrace>P\<rbrace> getCurThread \<lbrace>\<lambda>rv. P and (\<lambda>s. rv = ksCurThread s)\<rbrace>"
  by (wpsimp simp: getCurThread_def)

lemma getSchedulerAction_sp:
  "\<lbrace>P\<rbrace> getSchedulerAction \<lbrace>\<lambda>rv. P and (\<lambda>s. rv = ksSchedulerAction s)\<rbrace>"
  by (wpsimp simp: getSchedulerAction_def)

lemma getReprogramTimer_sp:
  "\<lbrace>P\<rbrace> getReprogramTimer \<lbrace>\<lambda>rv. P and (\<lambda>s. rv = ksReprogramTimer s)\<rbrace>"
  by (wpsimp simp: getReprogramTimer_def)

lemma getIdleThread_sp:
  "\<lbrace>P\<rbrace> getIdleThread \<lbrace>\<lambda>rv. P and (\<lambda>s. rv = ksIdleThread s)\<rbrace>"
  by wpsimp

lemma getIdleSC_sp:
  "\<lbrace>P\<rbrace> getIdleSC \<lbrace>\<lambda>rv. P and (\<lambda>s. rv = ksIdleSC s)\<rbrace>"
  by wpsimp

lemma getReprogramTimer_wp[wp]:
  "\<lbrace>\<lambda>s. P (ksReprogramTimer s) s\<rbrace> getReprogramTimer \<lbrace>P\<rbrace>"
  by (wpsimp simp: getReprogramTimer_def)

lemma getConsumedTime_wp[wp]:
  "\<lbrace>\<lambda>s. P (ksConsumedTime s) s\<rbrace> getConsumedTime \<lbrace>P\<rbrace>"
  by (wpsimp simp: getConsumedTime_def)

lemma isRoundRobin_wp:
  "\<lbrace>\<lambda>s. \<forall>ko. ko_at' ko sc s \<longrightarrow> P (scPeriod ko = 0) s\<rbrace> isRoundRobin sc \<lbrace>P\<rbrace>"
  by (wpsimp simp: isRoundRobin_def)

lemma getCurSc_wp[wp]:
  "\<lbrace>\<lambda>s. P (ksCurSc s) s\<rbrace> getCurSc \<lbrace>P\<rbrace>"
  unfolding getCurSc_def
  by wpsimp

lemma getCurTime_wp[wp]:
  "\<lbrace>\<lambda>s. P (ksCurTime s) s\<rbrace> getCurTime \<lbrace>P\<rbrace>"
  unfolding getCurTime_def
  by wpsimp

lemma curDomain_wp[wp]:
  "\<lbrace>\<lambda>s. P (ksCurDomain s) s\<rbrace> curDomain \<lbrace>P\<rbrace>"
  unfolding curDomain_def
  by wpsimp

lemma curDomain_sp:
  "\<lbrace>P\<rbrace> curDomain \<lbrace>\<lambda>rv. P and (\<lambda>s. rv = ksCurDomain s)\<rbrace>"
  by wpsimp

lemma getReleaseQueue_wp[wp]:
  "\<lbrace>\<lambda>s. P (ksReleaseQueue s) s\<rbrace> getReleaseQueue \<lbrace>P\<rbrace>"
  unfolding getReleaseQueue_def
  by wpsimp

lemma getObject_sc_wp:
  "\<lbrace>\<lambda>s. sc_at' p s \<longrightarrow> (\<exists>t::sched_context. ko_at' t p s \<and> Q t s)\<rbrace> getObject p \<lbrace>Q\<rbrace>"
  by (clarsimp simp: getObject_def valid_def in_monad
                     split_def gen_objBits_simps loadObject_default_def
                     obj_at'_def in_magnitude_check
              dest!: readObject_misc_ko_at')

lemma getRefillNext_wp:
  "\<lbrace>\<lambda>s. sc_at' scPtr s \<longrightarrow> (\<exists>t. ko_at' t scPtr s \<and> P (refillNext t index) s)\<rbrace>
   getRefillNext scPtr index
   \<lbrace>P\<rbrace>"
  apply (simp add: getRefillNext_def readRefillNext_def readSchedContext_def
             flip: getObject_def)
  apply (wpsimp wp: getObject_sc_wp)
  done

lemma readRefillSize_SomeD:
  "readRefillSize scPtr s = Some sz \<Longrightarrow> \<exists>sc. ko_at' sc scPtr s \<and> refillSize sc = sz"
  apply (clarsimp simp: readRefillSize_def readSchedContext_def)
  apply (fastforce dest: readObject_ko_at'_sc)
  done

lemma getRefillSize_wp:
  "\<lbrace>\<lambda>s. \<forall>ko. ko_at' ko scp s \<longrightarrow> P (refillSize ko) s\<rbrace> getRefillSize scp \<lbrace>P\<rbrace>"
  apply (clarsimp simp: getRefillSize_def)
  apply wpsimp
  apply (fastforce dest: readRefillSize_SomeD)
  done

lemma getRefillFull_wp:
  "\<lbrace>\<lambda>s. \<forall>ko. ko_at' ko scp s \<longrightarrow> P (refillSize ko = scRefillMax ko) s\<rbrace> getRefillFull scp \<lbrace>P\<rbrace>"
  apply (clarsimp simp: getRefillFull_def readRefillFull_def getSchedContext_def[symmetric]
                        readSchedContext_def getObject_def[symmetric] getRefillSize_def[symmetric])
  apply (wpsimp wp: getRefillSize_wp)
  apply normalise_obj_at'
  done

lemma no_ofail_readCurTime[simp]:
  "no_ofail \<top> readCurTime"
  unfolding readCurTime_def by clarsimp

lemma ovalid_readCurTime[wp]:
  "\<lblot>\<lambda>s. P (ksCurTime s) s\<rblot> readCurTime \<lblot>\<lambda>r s. P r s \<and> r = ksCurTime s\<rblot>"
  by (simp add: readCurTime_def asks_def obind_def ovalid_def)

lemma readScActive_wp[wp]:
  "\<lblot>\<lambda>s. \<forall>ko. ko_at' ko scp s \<longrightarrow> P (0 < scRefillMax ko) s\<rblot> readScActive scp \<lblot>P\<rblot>"
  unfolding readScActive_def readSchedContext_def
  by (wpsimp wp: set_sc'.readObject_wp)

lemmas scActive_wp[wp] = ovalid_gets_the[OF readScActive_wp, simplified scActive_def[symmetric]]

lemma getRefills_wp:
  "\<lbrace>\<lambda>s. \<forall>ko. ko_at' ko scp s \<longrightarrow> P (scRefills ko) s\<rbrace>
   getRefills scp
   \<lbrace>P\<rbrace>"
  unfolding getRefills_def
  by wpsimp

lemma readRefillHead_SomeD:
  "readRefillHead scPtr s = Some refill \<Longrightarrow> \<exists>sc. ko_at' sc scPtr s \<and> refill = refillHd sc"
  apply (clarsimp simp: readRefillHead_def readSchedContext_def)
  apply (fastforce dest: readObject_ko_at'_sc)
  done

lemma readRefillHead_wp[wp]:
  "\<lblot>\<lambda>s. \<forall>sc. scs_of' s scPtr = Some sc \<longrightarrow> Q (refillHd sc) s\<rblot>
   readRefillHead scPtr
   \<lblot>Q\<rblot>"
  unfolding readRefillHead_def readSchedContext_def
  apply (wpsimp wp: set_sc'.readObject_wp)
  apply (clarsimp simp: opt_map_def obj_at'_def)
  done

lemmas getRefillHead_wp[wp] =
  ovalid_gets_the[OF readRefillHead_wp, simplified getRefillHead_def[symmetric]]

lemma readRefillTail_wp[wp]:
  "\<lblot>\<lambda>s. \<forall>sc. scs_of' s scPtr = Some sc \<longrightarrow> Q (refillTl sc) s\<rblot>
   readRefillTail scPtr
   \<lblot>Q\<rblot>"
  unfolding readRefillTail_def readSchedContext_def
  apply (wpsimp wp: set_sc'.readObject_wp)
  apply (clarsimp simp: opt_map_def obj_at'_def)
  done

lemmas getRefillTail_wp[wp] =
  ovalid_gets_the[OF readRefillTail_wp, simplified getRefillTail_def[symmetric]]

lemma getRefillHead_sp:
  "\<lbrace>P\<rbrace> getRefillHead scPtr \<lbrace>\<lambda>rv s. P s \<and> (\<exists>sc. scs_of' s scPtr = Some sc \<and> refillHd sc = rv)\<rbrace>"
  by wpsimp

lemma getRefillTail_sp:
  "\<lbrace>P\<rbrace> getRefillTail scPtr \<lbrace>\<lambda>rv s. P s \<and> (\<exists>sc. scs_of' s scPtr = Some sc \<and> refillTl sc = rv)\<rbrace>"
  by wpsimp

lemma readRefillReady_wp:
  "\<lblot>\<lambda>s. \<forall>sc. scs_of' s scp = Some sc \<longrightarrow> P (rTime (refillHd sc) \<le> ksCurTime s) s\<rblot>
   readRefillReady scp
   \<lblot>P\<rblot>"
  unfolding readRefillReady_def readCurTime_def
  by wpsimp

lemmas refillReady_wp[wp] =
  ovalid_gets_the[OF readRefillReady_wp, simplified refillReady_def[symmetric]]

lemma readRefillCapacity_SomeD:
  "readRefillCapacity scPtr usage s = Some capacity
   \<Longrightarrow> \<exists>sc. scs_of' s scPtr = Some sc \<and> capacity = refillCapacity usage (refillHd sc)"
  apply (clarsimp simp: readRefillCapacity_def)
  apply (fastforce dest: readRefillHead_SomeD simp: opt_map_def obj_at'_def)
  done

lemma getRefillCapacity_wp[wp]:
  "\<lbrace>\<lambda>s. \<forall>sc. scs_of' s scPtr = Some sc \<longrightarrow> P (refillCapacity usage (refillHd sc)) s\<rbrace>
   getRefillCapacity scPtr usage
   \<lbrace>P\<rbrace>"
  unfolding getRefillCapacity_def
  apply wpsimp
  apply (fastforce dest: readRefillCapacity_SomeD)
  done

lemma readRefillSufficient_SomeD:
  "readRefillSufficient scPtr usage s = Some sufficient
   \<Longrightarrow> \<exists>sc. scs_of' s scPtr = Some sc  \<and> sufficient = refillSufficient usage (refillHd sc)"
  apply (clarsimp simp: readRefillSufficient_def)
  apply (frule readRefillCapacity_SomeD)
  apply (fastforce simp: refillSufficient_def obj_at'_def opt_map_def split: option.splits)
  done

lemma getRefillSufficient_wp[wp]:
  "\<lbrace>\<lambda>s. \<forall>sc. scs_of' s scPtr = Some sc \<longrightarrow> P (refillSufficient usage (refillHd sc)) s\<rbrace>
   getRefillSufficient scPtr usage
   \<lbrace>P\<rbrace>"
  unfolding getRefillSufficient_def
  apply wpsimp
  apply (fastforce dest: readRefillSufficient_SomeD)
  done

(* projection rewrites *)

lemma pred_map_rewrite:
  "pred_map P proj = opt_pred P proj"
  by (fastforce simp: pred_map_def2 opt_pred_def)

abbreviation sc_of2 :: "Structures_A.kernel_object \<rightharpoonup> Structures_A.sched_context" where
  "sc_of2 ko \<equiv> case ko of kernel_object.SchedContext sc n \<Rightarrow> Some sc | _ \<Rightarrow> None"

abbreviation scs_of2 :: "'z state \<Rightarrow> obj_ref \<rightharpoonup> Structures_A.sched_context" where
  "scs_of2 \<equiv> (\<lambda>s. kheap s |> sc_of2)"

lemma scs_of_rewrite:
  "scs_of s = scs_of2 s"
  by (fastforce simp: sc_heap_of_state_def opt_map_def
              split: option.splits Structures_A.kernel_object.splits)

abbreviation sc_replies_of2 :: "'z state \<Rightarrow> obj_ref \<Rightarrow>obj_ref list option" where
  "sc_replies_of2 s \<equiv> scs_of2 s ||> sc_replies"

lemma sc_replies_of_rewrite:
  "sc_replies_of s = sc_replies_of2 s"
  by (fastforce simp: sc_heap_of_state_def sc_replies_of_scs_def opt_map_def map_project_def
              split: option.splits Structures_A.kernel_object.splits)

definition sc_replies_relation2_2 ::
  "(obj_ref \<rightharpoonup> obj_ref list) \<Rightarrow> (obj_ref \<rightharpoonup> obj_ref) \<Rightarrow> (obj_ref \<rightharpoonup> obj_ref) \<Rightarrow> bool"
  where
  "sc_replies_relation2_2 sc_repls scRepl replPrevs \<equiv>
     \<forall>p replies. sc_repls p = Some replies \<longrightarrow> heap_ls replPrevs (scRepl p) replies"

abbreviation sc_replies_relation2 :: "det_state \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "sc_replies_relation2 s s' \<equiv>
    sc_replies_relation2_2 (sc_replies_of2 s) (scReplies_of s') (replyPrevs_of s')"

lemmas sc_replies_relation2_def = sc_replies_relation2_2_def

lemma sc_replies_relation_rewrite:
  "sc_replies_relation s s' = sc_replies_relation2 s s'"
  unfolding sc_replies_relation_def sc_replies_relation2_def sc_replies_of_rewrite
  by simp

definition is_active_sc2 :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> bool" where
  "is_active_sc2 p s \<equiv> ((\<lambda>sc. 0 < sc_refill_max sc) |< scs_of2 s) p"

definition active_sc_tcb_at' :: "obj_ref \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "active_sc_tcb_at' tcbPtr s \<equiv> ((\<lambda>sc. 0 < scRefillMax sc) |< (tcbSCs_of s |> scs_of' s)) tcbPtr"

lemma is_active_sc_rewrite:
  "is_active_sc p s = is_active_sc2 p s"
  by (fastforce simp: is_active_sc2_def vs_all_heap_simps is_active_sc_def
                      active_sc_def opt_map_red opt_map_def opt_pred_def
               split: option.split_asm Structures_A.kernel_object.splits)

abbreviation valid_refills2 :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> bool" where
  "valid_refills2 scp s \<equiv>
     ((\<lambda>sc. if sc_period sc = 0 then rr_valid_refills (sc_refills sc) (sc_refill_max sc) (sc_budget sc)
      else sp_valid_refills (sc_refills sc) (sc_refill_max sc) (sc_period sc) (sc_budget sc)) |<
     scs_of2 s) scp"

lemmas valid_refills2_def = rr_valid_refills_def sp_valid_refills_def

lemma valid_refills_rewrite:
  "valid_refills scp s = valid_refills2 scp s"
  by (fastforce simp: opt_map_red vs_all_heap_simps valid_refills_def opt_pred_def
               elim!: opt_mapE
               split: option.splits Structures_A.kernel_object.splits)

definition round_robin2 :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> bool" where
  "round_robin2 sc_ptr s \<equiv> ((\<lambda>sc. sc_period sc = 0) |< scs_of2 s) sc_ptr"

lemma round_robin_rewrite:
  "round_robin scp s = round_robin2 scp s"
  by (clarsimp simp: round_robin_def round_robin2_def vs_all_heap_simps opt_map_def opt_pred_def
               elim!: opt_mapE
              split: option.splits Structures_A.kernel_object.splits)

abbreviation sc_refills_sc_at2 ::
  "(Structures_A.refill list \<Rightarrow> bool) \<Rightarrow> obj_ref \<Rightarrow> 'z state \<Rightarrow> bool"
  where
  "sc_refills_sc_at2 P scp s \<equiv> ((\<lambda>sc. P (sc_refills sc)) |< scs_of2 s) scp"

lemma sc_refills_sc_at_rewrite:
  "sc_refills_sc_at P scp s = sc_refills_sc_at2 P scp s"
  by (fastforce simp: sc_refills_sc_at_def obj_at_def is_sc_obj opt_map_red opt_pred_def
               elim!: opt_mapE
               split: option.splits Structures_A.kernel_object.split_asm)

lemmas projection_rewrites = pred_map_rewrite scs_of_rewrite is_active_sc_rewrite
                             sc_heap_of_state_def sc_refills_sc_at_rewrite
                             active_sc_at'_rewrite valid_refills_rewrite round_robin_rewrite

lemma is_active_sc'_cross:
  assumes p: "pspace_relation (kheap s) (ksPSpace s')"
  assumes t: "is_active_sc2 ptr s"
  shows "is_active_sc' ptr s'"
  using assms
  supply projection_rewrites[simp]
  apply (clarsimp simp: is_active_sc2_def is_active_sc'_def opt_pred_def
                 split: option.split_asm Structures_A.kernel_object.split_asm elim!: opt_mapE)
  apply (drule (1) pspace_relation_absD, clarsimp split: if_split_asm)
  by (case_tac z; simp add: sc_relation_def opt_map_red)

lemma set_refills_is_active_sc2[wp]:
  "set_refills ptr new \<lbrace>is_active_sc2 ptr'\<rbrace>"
  apply (wpsimp simp: is_active_sc2_def wp: set_refills_wp)
  by (clarsimp simp: obj_at_def opt_map_def opt_pred_def)

(* end : projection rewrites *)

(* updateSchedContext *)

(* update wp rules without ko_at' *)
lemma updateSchedContext_wp:
  "\<lbrace> \<lambda>s. sc_at' sc_ptr s \<longrightarrow>
       Q (s\<lparr>ksPSpace := (ksPSpace s)(sc_ptr \<mapsto> KOSchedContext (f' (the (scs_of' s sc_ptr))))\<rparr>) \<rbrace>
   updateSchedContext sc_ptr f'
   \<lbrace> \<lambda>rv. Q \<rbrace>"
  by (wpsimp simp: updateSchedContext_def wp: set_sc'.set_wp)
     (clarsimp simp: obj_at'_def opt_map_red elim!: rsubst[where P=Q])

lemma no_fail_setSchedContext[wp]:
  "no_fail (sc_at' ptr and (\<lambda>s'. ((\<lambda>k::sched_context. objBits k = objBits new) |< scs_of' s') ptr))
           (setSchedContext ptr new)"
  unfolding setSchedContext_def by (wpsimp simp: opt_map_def obj_at'_def opt_pred_def)

lemma no_fail_updateSchedContext[wp]:
  "no_fail (sc_at' ptr and (\<lambda>s'. ((\<lambda>k::sched_context. objBits k = objBits (f k)) |< scs_of' s') ptr))
           (updateSchedContext ptr f)"
  by (wpsimp simp: updateSchedContext_def obj_at'_def opt_map_def opt_pred_def)

lemma updateSchedContext_sc_obj_at':
  "\<lbrace>if scPtr = scPtr' then (\<lambda>s. \<forall>ko. ko_at' ko scPtr' s \<longrightarrow> P (f ko)) else obj_at' P scPtr'\<rbrace>
   updateSchedContext scPtr f
   \<lbrace>\<lambda>rv. obj_at' P scPtr'\<rbrace>"
  supply if_split [split del]
  apply (simp add: updateSchedContext_def)
  apply (wpsimp wp: set_sc'.obj_at')
  apply (clarsimp split: if_splits simp: obj_at'_real_def ko_wp_at'_def)
  done

lemma updateSchedContext_sc_obj_at'_inv:
  "(\<And>sc. P (f sc) = P sc) \<Longrightarrow> updateSchedContext scPtr f \<lbrace>\<lambda>s. Q (obj_at' P scPtr' s)\<rbrace>"
  unfolding updateSchedContext_def
  by (wpsimp wp: set_sc'.obj_at')
     (clarsimp split: if_splits simp: obj_at'_real_def ko_wp_at'_def)

lemma update_sched_context_rewrite:
  "monadic_rewrite False True (sc_obj_at n scp)
    (update_sched_context scp f)
      (do sc \<leftarrow> get_sched_context scp;
          set_object scp (kernel_object.SchedContext (f sc) n) od)"
  apply (clarsimp simp: update_sched_context_def get_sched_context_def bind_assoc)
  apply (rule monadic_rewrite_bind_tail)
   defer
   apply (rule get_object_sp)
  apply (case_tac obj;
         fastforce simp: monadic_rewrite_pre_imp_eq set_object_def monadic_rewrite_def obj_at_def
                         is_sc_obj_def)
  done

lemmas sc_inv_state_eq' = getObject_sc_inv[THEN use_valid[rotated], rotated,
                                           where s=s and P="(=) s" for s, OF _ refl]

lemma sc_inv_state_eq:
  "(a :: sched_context, s') \<in> fst (getSchedContext p s) \<Longrightarrow> s' = s"
  by (fastforce dest: sc_inv_state_eq' simp: getSchedContext_def)

lemma getObject_idempotent:
  "monadic_rewrite False True (sc_at' ptr)
   (do rv \<leftarrow> (getObject ptr :: sched_context kernel);
       getObject ptr
    od)
   (getObject ptr :: sched_context kernel)"
  apply (clarsimp simp: monadic_rewrite_def)
  apply (rule monad_state_eqI)
    apply ((clarsimp simp: in_monad getObject_def split_def
                           loadObject_default_def scBits_pos_power2 gen_objBits_simps
                           lookupAround2_known1 in_magnitude_check)+)[2]
  apply (fastforce dest!: sc_inv_state_eq[simplified getSchedContext_def]
                          no_fail_getObject_misc[simplified no_fail_def, rule_format]
                    simp: snd_bind)
  done

lemma getSchedContext_setSchedContext_decompose:
   "monadic_rewrite False True
     (sc_at' scPtr and K (\<forall>sc. objBits (f sc) = objBits sc) and K (\<forall>sc. objBits (g sc) = objBits sc))
     (do sc \<leftarrow> getSchedContext scPtr;
         setSchedContext scPtr (g (f sc))
      od)
     (do sc \<leftarrow> getSchedContext scPtr;
         setSchedContext scPtr (f sc);
         sc \<leftarrow> getSchedContext scPtr;
         setSchedContext scPtr (g sc)
      od)"
  apply (clarsimp simp: monadic_rewrite_def)
  apply (rule monad_state_eqI)
    apply (simp add: in_monad getSchedContext_def getObject_def)
    apply (frule no_ofailD[OF no_ofail_sc_at'_readObject])
    apply clarsimp
    apply (clarsimp simp: setSchedContext_def setObject_def obj_at'_def gen_objBits_simps
                          in_monad scBits_pos_power2 updateObject_default_def
                          in_magnitude_check ps_clear_upd magnitudeCheck_assert split_def
                   split: option.split_asm)
     apply (rename_tac sc sc')
     apply (rule_tac x="f sc" in exI)
     apply (rule conjI;
            fastforce simp: readObject_def obind_def omonad_defs split_def
                            ps_clear_upd loadObject_default_def lookupAround2_known1
                            gen_objBits_simps scBits_pos_power2 lookupAround2_None2 lookupAround2_char2
                     split: option.splits if_split_asm dest!: readObject_misc_ko_at')
    apply (rename_tac sc p sc')
    apply (rule_tac x="f sc" in exI)
    apply (rule conjI)
     apply (thin_tac "scSize _ = _")
     apply (clarsimp simp: readObject_def obind_def omonad_defs fun_upd_def split_def
                           ps_clear_upd loadObject_default_def lookupAround2_known1
                           gen_objBits_simps scBits_pos_power2 lookupAround2_None2 lookupAround2_char2
                    split: option.splits if_split_asm)
     apply (metis option.simps(3) word_le_less_eq word_le_not_less)
    apply (clarsimp simp: split: option.splits)
    apply (metis (no_types) array_rules(2) lookupAround2_char2 mcs(1) order.strict_trans2
                            word_le_less_eq word_le_not_less)
   apply (simp add: in_monad getSchedContext_def getObject_def)
   apply (frule no_ofailD[OF no_ofail_sc_at'_readObject])
   apply clarsimp
   apply (clarsimp simp: setSchedContext_def setObject_def in_monad ps_clear_upd obj_at'_def
                         split_def updateObject_default_def magnitudeCheck_assert
                  dest!: readObject_misc_ko_at')

  apply (frule no_failD[OF no_fail_getMiscObject(4)])
  apply (simp add: snd_bind)
  apply (rule iffI; clarsimp simp: snd_bind split_def setSchedContext_def; rename_tac sc s')
   apply (frule sc_inv_state_eq, simp)
   apply (rule_tac x="(sc, s)" in bexI[rotated], simp)
   apply (rule disjI2)
   apply (drule use_valid[OF _ get_sc_ko'], simp)
   apply (clarsimp simp: obj_at'_def)
   apply (prop_tac "obj_at' (\<lambda>k. objBits k = objBits (g (f sc))) scPtr s")
    apply (clarsimp simp: obj_at'_def)
    apply (rule_tac x=sc in exI, clarsimp simp: projectKO_opt_sc)
   apply (drule_tac ob1="g (f sc)" in no_failD[OF no_fail_setObject_other, rotated])
    apply simp
   apply clarsimp
  apply (frule sc_inv_state_eq, simp)
  apply (rule_tac x="(sc, s)" in bexI[rotated], simp)
  apply (drule use_valid[OF _ get_sc_ko'], simp)
  apply (erule disjE; clarsimp)
   apply (clarsimp simp: obj_at'_def)
   apply (prop_tac "obj_at' (\<lambda>k. objBits k = objBits (f sc)) scPtr s")
    apply (clarsimp simp: obj_at'_def)
    apply (rule_tac x=sc in exI, clarsimp simp: projectKO_opt_sc)
   apply (drule_tac ob1="(f sc)" in no_failD[OF no_fail_setObject_other, rotated])
    apply simp+

  apply (rename_tac s'; erule disjE; clarsimp?)
   apply (drule_tac Q2="\<lambda>s'. s' = (s\<lparr>ksPSpace := (ksPSpace s)(scPtr \<mapsto> injectKO (f sc))\<rparr>)"
                 in use_valid[OF _ setObject_sc_wp])
    apply simp+

   apply (prop_tac "sc_at' scPtr (s\<lparr>ksPSpace := (ksPSpace s)(scPtr \<mapsto> KOSchedContext (f sc))\<rparr>)")
    apply (clarsimp simp: obj_at'_def gen_objBits_simps ps_clear_upd)
   apply (frule_tac s="s\<lparr>ksPSpace := (ksPSpace s)(scPtr \<mapsto> KOSchedContext (f sc))\<rparr>"
                 in no_failD[OF no_fail_getMiscObject(4)])
   apply clarsimp

  apply (rename_tac s')
  apply (drule_tac Q2="\<lambda>s'. s' = (s\<lparr>ksPSpace := (ksPSpace s)(scPtr \<mapsto> injectKO (f sc))\<rparr>)"
                in use_valid[OF _ setObject_sc_wp])
   apply simp+

  apply (frule sc_inv_state_eq, simp)
  apply (drule use_valid[OF _ get_sc_ko'], simp)
  apply (clarsimp simp: obj_at'_def)
  apply (prop_tac "obj_at' (\<lambda>k. objBits k = objBits (g (f sc))) scPtr
                           (s\<lparr>ksPSpace := (ksPSpace s)(scPtr \<mapsto> KOSchedContext (f sc))\<rparr>)")
   apply (clarsimp simp: obj_at'_def)
   apply (rule_tac x="f sc" in exI, clarsimp)
  apply (drule_tac ob1="g (f sc)" in no_failD[OF no_fail_setObject_other, rotated])
   apply simp+
  done

lemmas getSchedContext_setSchedContext_decompose_decompose_ext
  = getSchedContext_setSchedContext_decompose[where f="f x" and g="g y" for f g x y]
lemmas getSchedContext_setSchedContext_decompose_decompose2
  = getSchedContext_setSchedContext_decompose[where g="\<lambda>sc. g (h sc)" for g h]
lemmas getSchedContext_setSchedContext_decompose_decompose_ext2
  = getSchedContext_setSchedContext_decompose[where f="f x" and g="g y" for f g x y]

(* rewrite rules for updateSchedContext *)
lemma updateSchedContext_decompose:
   "monadic_rewrite False True
     (sc_at' scPtr and K (\<forall>sc. objBits (f sc) = objBits sc) and K (\<forall>sc. objBits (g sc) = objBits sc))
     (updateSchedContext scPtr (g o f))
     (do updateSchedContext scPtr f;
         updateSchedContext scPtr g
      od)"
  unfolding updateSchedContext_def bind_assoc o_def
  using getSchedContext_setSchedContext_decompose by blast

lemma updateSchedContext_decompose_fold:
  "\<lbrakk>\<forall>f\<in> set fs. \<forall>sc. objBits (f sc) = objBits sc; \<forall>sc. objBits (f sc) = objBits sc\<rbrakk> \<Longrightarrow>
   monadic_rewrite False True
     (sc_at' scPtr)
     (updateSchedContext scPtr (fold (o) fs f))
     (do updateSchedContext scPtr f;
         mapM_x (updateSchedContext scPtr) fs
      od)"
  apply (induction fs arbitrary: f)
   apply (clarsimp simp: mapM_x_Nil)
   apply (rule monadic_rewrite_guard_imp)
    apply (rule monadic_rewrite_refl, simp)
  apply (clarsimp simp: mapM_x_Cons)
  apply (drule_tac x="a o f" in meta_spec)
  apply (rule monadic_rewrite_guard_imp)
   apply (rule monadic_rewrite_trans)
    apply simp
   apply (subst bind_assoc[symmetric])
   apply (rule monadic_rewrite_guard_imp)
    apply (rule monadic_rewrite_bind_head)
    apply (rule updateSchedContext_decompose[simplified])
   apply simp
  apply simp
  done

lemmas updateSchedContext_decompose_x2 = updateSchedContext_decompose_fold[where fs="[g, h]" for f g h,
 simplified mapM_x_Cons mapM_x_Nil fold_Cons fold_Nil id_def, simplified]

lemmas updateSchedContext_decompose_x3 = updateSchedContext_decompose_fold[where fs="[g, h, k]" for f g h k,
 simplified mapM_x_Cons mapM_x_Nil fold_Cons fold_Nil id_def, simplified]

lemma updateSchedContext_no_stack_update_corres_Q:
  "\<lbrakk>\<And>sc n sc'. \<lbrakk>sc_relation sc n sc'; Q sc; Q' sc'\<rbrakk> \<Longrightarrow> sc_relation (f sc) n (f' sc');
    \<And>sc. sc_replies sc = sc_replies (f sc); \<And>sc'. objBits sc' = objBits (f' sc');
    \<And>sc'. scReply sc' = scReply (f' sc')\<rbrakk> \<Longrightarrow>
   corres dc
     (\<lambda>s. \<exists>sc n. kheap s ptr = Some (kernel_object.SchedContext sc n) \<and> Q sc)
     (\<lambda>s'. \<exists>sc'. ko_at' sc' ptr s' \<and> Q' sc')
     (update_sched_context ptr f) (updateSchedContext ptr f')"
  apply (clarsimp simp: update_sched_context_def)
  apply (rule corres_symb_exec_l[rotated 2, OF get_object_sp])
    apply (find_goal \<open>match conclusion in "\<lbrace>P\<rbrace> f \<exists>\<lbrace>Q\<rbrace>" for P f Q \<Rightarrow> -\<close>)
    apply (fastforce intro: get_object_exs_valid
                      simp: obj_at_def)
   apply wpsimp
   apply (clarsimp simp: obj_at_def)
  apply (rename_tac obj)
  apply (case_tac obj;
         clarsimp, (solves \<open>clarsimp simp: obj_at_def is_sc_obj_def corres_underlying_def\<close>)?)
  apply (clarsimp simp: pred_conj_def)
  apply (rule abs_ex_lift_corres)
  apply clarsimp
  apply (rule abs_ex_lift_corres)
  apply (rule corres_underlying_lift_ex2')
  apply (rule_tac F="sc_relation sc n sc' \<and> Q sc \<and> Q' sc'" in corres_req)
   apply (drule state_relation_pspace_relation)
   apply clarsimp
   apply (drule (1) pspace_relation_absD)
   apply (clarsimp simp: obj_at'_def split: if_split_asm)
  apply (clarsimp simp: updateSchedContext_def)
  apply (rule corres_symb_exec_r)
     apply (rule corres_guard_imp)
       apply (rule_tac f=f and f'="f'" and Q=Q and Q'=Q'
                    in setSchedContext_no_stack_update_corres_Q;
              simp?)
      apply (clarsimp simp: obj_at_def)
     apply fastforce
    apply wpsimp
    apply (clarsimp simp: obj_at'_def)
   apply wpsimp
  apply wpsimp
  apply (clarsimp simp: obj_at'_def)
  done

lemma updateSchedContext_no_stack_update_corres:
  "\<lbrakk>\<And>sc n sc'. sc_relation sc n sc' \<Longrightarrow> sc_relation (f sc) n (f' sc');
    \<And>sc. sc_replies sc = sc_replies (f sc); \<And>sc'. objBits sc' = objBits (f' sc');
    \<And>sc'. scReply sc' = scReply (f' sc')\<rbrakk> \<Longrightarrow>
   corres dc (sc_at ptr) (sc_at' ptr)
     (update_sched_context ptr f) (updateSchedContext ptr f')"
  apply (corres corres: updateSchedContext_no_stack_update_corres_Q
                         [where f=f and f'=f' and Q=\<top> and Q'=\<top>])
   apply (clarsimp simp: obj_at_def is_sc_obj_def)
   apply (case_tac ko; clarsimp)
  apply (clarsimp simp: obj_at'_def)
  done

(* end : updateSchedContext *)

(* this lets cross the sc size information from concrete to abstract *)
lemma ko_at_sc_cross:
  assumes p: "pspace_relation (kheap s) (ksPSpace s')"
  assumes t: "ko_at' (sc'::sched_context) ptr s'"
  shows "sc_obj_at (objBits sc' - minSchedContextBits) ptr s" using assms
  apply (clarsimp simp: obj_at'_def)
  apply (erule (1) pspace_dom_relatedE)
  by (clarsimp simp: obj_relation_cuts_def2 obj_at_def is_sc_obj cte_relation_def
                     other_obj_relation_def other_aobj_relation_def pte_relation_def tcb_relation_cut_def
                     scBits_simps sc_relation_def gen_objBits_simps
              split: Structures_A.kernel_object.split_asm if_split_asm
                     RISCV64_A.arch_kernel_obj.split_asm)

end

lemma update_sc_no_reply_stack_update_ko_at'_corres:
  assumes x: "\<And>sc n. sc_relation sc n sc' \<longrightarrow> sc_relation (f sc) n (f' sc')"
  assumes y: "\<And>sc. sc_replies sc = sc_replies (f sc)"
  assumes z: "objBits sc' = objBits (f' sc')"
  assumes r: "scReply sc' = scReply (f' sc')"
  shows
    "corres dc (sc_at ptr) (ko_at' sc' ptr)
            (update_sched_context ptr f)
            (setSchedContext ptr (f' sc'))"
  unfolding update_sched_context_def
  apply (rule corres_guard_imp)
    apply (rule corres_symb_exec_l'[where Q'="\<lambda>r s. ko_at r ptr s \<and> (\<exists>n. is_sc_obj n r)",
                                    where P="\<lambda>s. obj_at \<top> ptr s"])
      apply (rule corres_guard_imp[where P'=R and Q'=R for R])
        apply (rule_tac F="(\<exists>n. is_sc_obj n obj)" in corres_gen_asm)
        apply (case_tac obj; simp add: is_sc_obj_def)
        apply (rule setSchedContext_no_stack_update_corres[where f'=f'])
           apply (clarsimp simp: x obj_at_def intro!: y z r)+
     apply (fastforce simp: exs_valid_def get_object_def in_monad)
    apply (wpsimp wp: get_object_wp)
   apply (fastforce simp: obj_at_def)
  apply simp
  done

lemma update_sc_no_reply_stack_update_corres:
  "\<lbrakk>\<forall>sc n sc'. sc_relation sc n sc' \<longrightarrow> sc_relation (f sc) n (f' sc');
    \<forall>sc. sc_replies sc = sc_replies (f sc); \<forall>sc'. objBits sc' = objBits (f' sc');
    \<forall>sc'. scReply (f' sc') = scReply sc' \<rbrakk> \<Longrightarrow>
   corres dc (sc_at ptr and pspace_aligned and pspace_distinct) \<top>
          (update_sched_context ptr f)
         (do sc' <- getSchedContext ptr;
             setSchedContext ptr (f' sc')
          od)"
  apply (rule_tac Q'="sc_at' ptr" in corres_cross_add_guard)
   apply (fastforce dest!: state_relationD sc_at_cross simp: obj_at'_def)
  apply (rule corres_symb_exec_r)
     apply (rule corres_guard1_imp)
      apply (rule update_sc_no_reply_stack_update_ko_at'_corres; simp)
     apply clarsimp
    apply (wpsimp wp: get_sched_context_exs_valid simp: is_sc_obj_def obj_at_def)
   apply (rename_tac ko; case_tac ko; simp)
   apply (wpsimp simp: obj_at_def is_sc_obj_def)+
  done

lemma ko_at'_inj:
  "ko_at' ko ptr  s \<Longrightarrow> ko_at' ko' ptr s \<Longrightarrow> ko' = ko"
  by (clarsimp simp: obj_at'_real_def ko_wp_at'_def)

(* FIXME RT: Move these to AInvs where possible *)
(* FIXME RT: Try to unify with existing notions.
             See https://sel4.atlassian.net/browse/VER-1382 *)
definition injective_ref where
  "injective_ref ref heap \<equiv> (\<forall>q p1 p2. (p1, ref) \<in> heap q \<and> (p2, ref) \<in> heap q \<longrightarrow> p1 = p2)"

lemma sym_refs_inj:
  "\<lbrakk>sym_refs heap; injective_ref (symreftype ref) heap; (x, ref) \<in> heap y; (x, ref) \<in> heap y'\<rbrakk>
   \<Longrightarrow> y = y' "
  apply (clarsimp simp: sym_refs_def injective_ref_def)
  apply fastforce
  done

lemma sym_refs_inj2:
  "\<lbrakk>sym_refs heap; injective_ref ref heap; (x, ref) \<in> heap y; (y, symreftype ref) \<in> heap z\<rbrakk>
   \<Longrightarrow> x = z "
  apply (subgoal_tac "(y, symreftype ref) \<in> heap x")
   apply (erule (3) sym_refs_inj[where ref="symreftype ref", simplified])
  apply (fastforce simp: sym_refs_def)
  done

lemma injective_ref_SCTcb[simp]:
  "injective_ref SCTcb (state_refs_of' s) "
  apply (clarsimp simp: state_refs_of'_def injective_ref_def split: option.splits if_splits)
  apply (clarsimp simp: refs_of'_def)
  apply (rename_tac p0 ko p1 p2)
  apply (prop_tac "\<exists>z. ko = KOSchedContext z")
   apply (clarsimp split: kernel_object.splits)
      apply (clarsimp split: Structures_H.endpoint.splits simp: ep_q_refs_of'_def)
     apply (clarsimp split: Structures_H.ntfn.splits option.splits
                      simp: ntfn_q_refs_of'_def get_refs_def)
    apply (clarsimp simp: tcb_st_refs_of'_def tcb_bound_refs'_def get_refs_def
                   split: Structures_H.thread_state.splits if_splits option.splits)
   apply (clarsimp simp: get_refs_def split: option.splits)
  apply (clarsimp simp: get_refs_def split: option.splits)
  done

lemma reply_at'_cross_rel:
  "cross_rel (pspace_aligned and pspace_distinct and reply_at t) (reply_at' t)"
  unfolding cross_rel_def state_relation_def
  apply clarsimp
  by (erule (3) reply_at_cross)

lemma sch_act_simple_cross_rel:
  "cross_rel simple_sched_action sch_act_simple"
  apply (clarsimp simp: cross_rel_def)
  by (fastforce simp: simple_sched_action_def sch_act_simple_def
                dest: state_relation_sched_act_relation
               split: Structures_A.scheduler_action.splits)

lemma scheduler_act_sane_cross:
  "\<lbrakk>scheduler_act_sane s; (s, s') \<in> state_relation\<rbrakk> \<Longrightarrow> sch_act_sane s'"
  apply (clarsimp simp: scheduler_act_sane_def sch_act_sane_def)
  apply (frule state_relation_sched_act_relation)
  apply (drule curthread_relation)
  apply (cases "scheduler_action s"; clarsimp)
  done

lemma valid_tcb_state'_simps[simp]:
  "valid_tcb_state' Running = \<top>"
  "valid_tcb_state' Inactive = \<top>"
  "valid_tcb_state' Restart = \<top>"
  "valid_tcb_state' IdleThreadState = \<top>"
  "valid_tcb_state' (BlockedOnSend ref b c d e) = ep_at' ref"
  "valid_tcb_state' (BlockedOnReply r) = valid_bound_reply' r"
  by (rule ext, simp add: valid_tcb_state'_def)+

lemma tcb_at'_ex1_ko_at':
  "tcb_at' t s \<Longrightarrow> \<exists>!tcb. ko_at' (tcb::tcb) t s"
  by (fastforce simp: obj_at'_def)

lemma ex1_ex_eq_all:
  "\<exists>!x. Q x \<Longrightarrow> (\<exists>x. Q x \<and> P x) = (\<forall>x. Q x \<longrightarrow> P x)"
  by fastforce

lemmas tcb_at'_ex_eq_all = ex1_ex_eq_all[OF tcb_at'_ex1_ko_at']

lemma receiveBlocked_equiv:
  "receiveBlocked st = is_BlockedOnReceive st"
  unfolding receiveBlocked_def
  by (case_tac st; simp)

lemma threadGet_getObject:
  "threadGet f t = do x <- getObject t;
                         return (f x)
                   od"
  apply (simp add: threadGet_def threadRead_def oliftM_def getObject_def[symmetric])
  done

lemma obj_at'_typ_at'[elim!]:
  "obj_at' (P :: ('a :: pspace_storable) \<Rightarrow> bool) p s \<Longrightarrow>
   obj_at' (\<top> :: ('a :: pspace_storable) \<Rightarrow> bool) p s"
  by (clarsimp simp: obj_at'_real_def ko_wp_at'_def)

lemma shows
  obj_at'_sc_tcbs_of_equiv:
    "obj_at' (\<lambda>x. scTCB x = Some t) p s = (sc_at' p s \<and> scTCBs_of s p = Some t)"
  and obj_at'_tcb_scs_of_equiv:
    "obj_at' (\<lambda>x. tcbSchedContext x = Some sc) p s = (tcb_at' p s \<and> tcbSCs_of s p = Some sc)"
  and obj_at'_replySCs_of_equiv:
    "obj_at' (\<lambda>a. replyNext a = Some (Head sc)) p s = (reply_at' p s \<and> replySCs_of s p = Some sc)"
  and obj_at'_scReplies_of_equiv:
    "obj_at' (\<lambda>a. scReply a = Some sc) p s = (sc_at' p s \<and> scReplies_of s p = Some sc)"
  by (intro iffI; clarsimp simp: obj_at'_real_def ko_wp_at'_def opt_map_def)+

lemma not_idle_scTCB:
  "\<lbrakk>sym_heap_tcbSCs s; valid_objs' s; valid_idle' s; p \<noteq> idle_sc_ptr; sc_at' p s\<rbrakk> \<Longrightarrow>
   obj_at' (\<lambda>x. scTCB x \<noteq> Some idle_thread_ptr) p s"
  apply (subgoal_tac "\<not>obj_at' (\<lambda>x. scTCB x = Some idle_thread_ptr) p s")
   apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def)
  apply (subst (asm) sym_heap_symmetric)
  apply (clarsimp simp: obj_at'_sc_tcbs_of_equiv sym_heap_def)
  apply (clarsimp simp: valid_idle'_def obj_at'_real_def ko_wp_at'_def idle_tcb'_def
                 elim!: opt_mapE)
  done

lemma not_idle_tcbSC:
  "\<lbrakk>sym_heap_tcbSCs s; valid_objs' s; valid_idle' s; p \<noteq> idle_thread_ptr; tcb_at' p s\<rbrakk> \<Longrightarrow>
   obj_at' (\<lambda>x. tcbSchedContext x \<noteq> Some idle_sc_ptr) p s"
  apply (subgoal_tac "\<not>obj_at' (\<lambda>x. tcbSchedContext x = Some idle_sc_ptr) p s")
   apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def)
  apply (clarsimp simp: obj_at'_tcb_scs_of_equiv sym_heap_def)
  apply (clarsimp simp: valid_idle'_def obj_at'_real_def ko_wp_at'_def idle_tcb'_def
                 elim!: opt_mapE)
  done

lemma setObject_tcb_tcbs_of':
  "\<lbrace>\<lambda>s. P' ((tcbs_of' s)(c \<mapsto> tcb))\<rbrace>
  setObject c (tcb::tcb)
  \<lbrace>\<lambda>_ s. P' (tcbs_of' s)\<rbrace>"
  by (setObject_easy_cases)

lemma setObject_other_tcbs_of'[wp]:
  "setObject c (r::reply) \<lbrace>\<lambda>s. P' (tcbs_of' s)\<rbrace>"
  "setObject c (e::endpoint) \<lbrace>\<lambda>s. P' (tcbs_of' s)\<rbrace>"
  "setObject c (n::notification) \<lbrace>\<lambda>s. P' (tcbs_of' s)\<rbrace>"
  "setObject c (sc::sched_context) \<lbrace>\<lambda>s. P' (tcbs_of' s)\<rbrace>"
  by setObject_easy_cases+

lemma setObject_cte_tcbSCs_of[wp]:
  "setObject c (reply::cte) \<lbrace>\<lambda>s. P' (tcbSCs_of s)\<rbrace>"
  by setObject_easy_cases

lemma threadSet_tcbSCs_of_inv:
  "\<forall>x. tcbSchedContext (f x) = tcbSchedContext x \<Longrightarrow>
  threadSet f t \<lbrace>\<lambda>s. P (tcbSCs_of s)\<rbrace>"
  unfolding threadSet_def
  apply (rule bind_wp[OF _ get_tcb_sp'])
  apply (wpsimp wp: setObject_tcb_tcbs_of')
  apply (erule subst[where P=P, rotated], rule ext)
  apply (clarsimp simp: opt_map_def obj_at'_real_def ko_wp_at'_def
                 split: option.splits)
  done

lemma aligned'_distinct'_obj_at'I:
  "\<lbrakk> \<exists>y. ksPSpace s p = Some (injectKO (y:: 'a::pspace_storable));
    pspace_aligned' s; pspace_distinct' s;
    (if koTypeOf (the (ksPSpace s p))  = SchedContextT then pspace_bounded' s else True)\<rbrakk>
   \<Longrightarrow> obj_at' (\<top> :: 'a::pspace_storable \<Rightarrow> bool) p s"
  apply (clarsimp)
  apply (frule_tac v=y in aligned'_distinct'_ko_at'I; simp?)
  apply (case_tac "injectKO y"; clarsimp simp: valid_sz_simps dest!: pspace_boundedD')
  done

lemma sym_refs_tcbSCs:
  "\<lbrakk>sym_refs (state_refs_of' s); pspace_aligned' s; pspace_distinct' s; pspace_bounded' s\<rbrakk>
   \<Longrightarrow> sym_heap_tcbSCs s"
  apply (clarsimp simp: sym_heap_def)
  apply (rule iffI)
   apply (drule_tac tp=SCTcb and x=p and y=p' in sym_refsE;
          force simp: get_refs_def2 state_refs_of'_def in_omonad refs_of_rev' tcb_bound_refs'_def
                dest: pspace_alignedD' pspace_distinctD' pspace_boundedD' elim!: opt_mapE
               split: if_split_asm option.split_asm)+
  by (drule_tac tp=TCBSchedContext and x=p' and y=p in sym_refsE;
      force simp: get_refs_def2 state_refs_of'_def in_omonad refs_of_rev'
            dest: pspace_alignedD' pspace_distinctD' pspace_boundedD'
           elim!: opt_mapE split: if_split_asm option.split_asm)+

lemma sym_refs_scReplies:
  "\<lbrakk>sym_refs (state_refs_of' s); pspace_aligned' s; pspace_distinct' s; pspace_bounded' s\<rbrakk>
   \<Longrightarrow> sym_heap_scReplies s"
  apply (clarsimp simp: sym_heap_def)
  apply (rule iffI)
   apply (drule_tac tp=ReplySchedContext and x=p and y=p' in sym_refsE;
          force simp: get_refs_def2 state_refs_of'_def opt_map_red refs_of_rev'
                dest: pspace_alignedD' pspace_distinctD' pspace_boundedD'
               elim!: opt_mapE
               split: if_split_asm option.split_asm)+
  by (drule_tac tp=SCReply and x=p' and y=p in sym_refsE;
      force simp: get_refs_def2 state_refs_of'_def opt_map_red refs_of_rev'
               dest: pspace_alignedD' pspace_distinctD' pspace_boundedD'
              elim!: opt_mapE
              split: if_split_asm option.split_asm)+

lemma setSchedContext_scTCBs_of:
  "\<lbrace>\<lambda>s. P (\<lambda>a. if a = scPtr then scTCB sc else scTCBs_of s a)\<rbrace>
   setSchedContext scPtr sc
   \<lbrace>\<lambda>_ s. P (scTCBs_of s)\<rbrace>"
  unfolding setSchedContext_def
  apply (wpsimp wp: setObject_sc_wp)
  apply (erule back_subst[where P=P], rule ext)
  by (clarsimp simp: opt_map_def)

lemma setSchedContext_scReplies_of:
  "\<lbrace>\<lambda>s. P (\<lambda>a. if a = scPtr then scReply sc else scReplies_of s a)\<rbrace>
   setSchedContext scPtr sc
   \<lbrace>\<lambda>_ s. P (scReplies_of s)\<rbrace>"
  unfolding setSchedContext_def
  apply (wpsimp wp: setObject_sc_wp)
  apply (erule back_subst[where P=P], rule ext)
  by (clarsimp simp: opt_map_def)

lemma updateSchedContext_scReplies_of:
  "(\<And>sc. scReply (f sc) = scReply sc) \<Longrightarrow> updateSchedContext scPtr f \<lbrace>\<lambda>s. P' (scReplies_of s)\<rbrace>"
  apply (wpsimp simp: updateSchedContext_def wp: setSchedContext_scReplies_of)
  apply (auto elim!: rsubst[where P=P'] simp: opt_map_def obj_at'_def)
  done

lemma getObject_tcb_wp:
  "\<lbrace>\<lambda>s. tcb_at' p s \<longrightarrow> (\<exists>t::tcb. ko_at' t p s \<and> Q t s)\<rbrace> getObject p \<lbrace>Q\<rbrace>"
  by (clarsimp simp: getObject_def valid_def in_monad
                     split_def gen_objBits_simps loadObject_default_def
                     obj_at'_def in_magnitude_check
              dest!: readObject_misc_ko_at')

lemma threadSet_tcbSCs_of:
  "\<lbrace>\<lambda>s. P (\<lambda>a. if a = t then tcbSchedContext (f (the (tcbs_of' s a))) else tcbSCs_of s a)\<rbrace>
   threadSet f t
   \<lbrace>\<lambda>_ s. P (tcbSCs_of s)\<rbrace>"
  unfolding threadSet_def
  apply (wpsimp wp: setObject_tcb_wp getObject_tcb_wp)
  apply (clarsimp simp: tcb_at'_ex_eq_all)
  apply (erule back_subst[where P=P], rule ext)
  apply (clarsimp simp: opt_map_def obj_at'_real_def ko_wp_at'_def)
  done

lemma shows
  replyNexts_Some_replySCs_None:
  "replyNexts_of s rp \<noteq> None \<Longrightarrow> replySCs_of s rp = None" and
  replySCs_Some_replyNexts_None:
  "replySCs_of s rp \<noteq> None \<Longrightarrow> replyNexts_of s rp = None"
  by (clarsimp simp: opt_map_def split: option.splits reply_next.splits)+

lemma pred_tcb_at'_equiv:
  "pred_tcb_at' p P t s = (tcb_at' t s \<and> P (p (tcb_to_itcb' (the (tcbs_of' s t)))))"
  by (rule iffI;
      clarsimp simp: pred_tcb_at'_def pred_map_def obj_at'_real_def ko_wp_at'_def opt_map_def)

lemma isBlockedOnSend_equiv:
  "isBlockedOnSend st = is_BlockedOnSend st"
  by (case_tac st; simp add: isBlockedOnSend_def)

lemma isSend_equiv:
  "isSend st = is_BlockedOnSend st"
  by (case_tac st; simp add: isSend_def)

lemma sch_act_wf_not_runnable_sch_act_not:
  "\<lbrakk>st_tcb_at' P t s; sch_act_wf (ksSchedulerAction s) s; \<forall>st. P st \<longrightarrow> \<not> runnable' st\<rbrakk> \<Longrightarrow>
   sch_act_not t s"
   by (clarsimp simp: pred_tcb_at'_def obj_at'_def)

lemma isTimeoutFault_fault_map[simp]:
  "isTimeoutFault (fault_map a) = is_timeout_fault a"
  by (clarsimp simp: isTimeoutFault_def fault_map_def is_timeout_fault_def
              split: ExceptionTypes_A.fault.splits)

lemma valid_bound_obj_lift:
  "f \<lbrace>P (the x)\<rbrace> \<Longrightarrow> f \<lbrace>valid_bound_obj P x\<rbrace>"
  unfolding valid_bound_obj_def
  by (case_tac x; wpsimp)

lemma valid_bound_obj'_lift:
  "f \<lbrace>P (the x)\<rbrace> \<Longrightarrow> f \<lbrace>valid_bound_obj' P x\<rbrace>"
  unfolding valid_bound_obj'_def
  by (case_tac x; wpsimp)

lemma ep_at'_cross_rel:
  "cross_rel (pspace_aligned and pspace_distinct and ep_at t) (ep_at' t)"
  unfolding cross_rel_def state_relation_def
  apply clarsimp
  by (erule (3) ep_at_cross)

lemma sch_act_not_cross_rel:
  "cross_rel (scheduler_act_not t) (sch_act_not t)"
  unfolding cross_rel_def state_relation_def
  apply clarsimp
  apply (case_tac "scheduler_action s"; simp)
  by (clarsimp simp: scheduler_act_not_def sched_act_relation_def)

global_interpretation set_simple_ko: typ_at_pres "set_simple_ko C ptr ep"
  unfolding typ_at_pres_def by wpsimp

global_interpretation update_sk_obj_ref: typ_at_pres "update_sk_obj_ref C update ref new"
  unfolding typ_at_pres_def by wpsimp

lemma getReprogramTimer_corres:
  "corres (=) \<top> \<top> (gets reprogram_timer) getReprogramTimer"
  by (clarsimp simp: getReprogramTimer_def state_relation_def)

lemma setDomainTime_corres:
  "dt = dt' \<Longrightarrow>
  corres dc \<top> \<top> (modify (domain_time_update (\<lambda>_. dt))) (setDomainTime dt')"
  apply (clarsimp simp: setDomainTime_def, rule corres_modify)
  by (clarsimp simp: state_relation_def swp_def)

lemma setConsumedTime_corres:
  "ct = ct' \<Longrightarrow>
  corres dc \<top> \<top> (modify (consumed_time_update (\<lambda>_. ct))) (setConsumedTime ct')"
  apply (clarsimp simp: setConsumedTime_def, rule corres_modify)
  by (clarsimp simp: state_relation_def swp_def)

lemma setCurSc_corres:
  "sc = sc' \<Longrightarrow>
   corres dc \<top> \<top> (modify (cur_sc_update (\<lambda>_. sc))) (setCurSc sc')"
  apply (clarsimp simp: setCurSc_def, rule corres_modify)
  by (clarsimp simp: state_relation_def swp_def)

lemma refillSingle_equiv:
  "sc_valid_refills' sc \<Longrightarrow>
   (length (refills_map (scRefillHead sc) (refillSize sc) (scRefillMax sc) (scRefills sc)) = Suc 0)
   = (scRefillHead sc = scRefillTail sc)"
  apply (clarsimp simp: valid_sched_context'_def refills_map_def refillSize_def)
  apply (fastforce simp: Let_def)
  done

lemma refillSingle_corres:
  "scp = scp' \<Longrightarrow>
   corres (=) (sc_at scp) (obj_at' sc_valid_refills' scp')
     (refill_single scp)
     (refillSingle scp')"
  apply (simp add: refill_single_def readRefillSingle_def refillSingle_def
                   refill_size_def get_refills_def readSchedContext_def
             flip: getSchedContext_def getObject_def)
  apply (rule stronger_corres_guard_imp)
    apply (rule_tac R'="\<lambda>sc s. sc_valid_refills' sc" and R="\<lambda>_ _ . True" in corres_split)
       apply (rule get_sc_corres)
      apply simp
      apply (metis (mono_tags, opaque_lifting) refillSingle_equiv sc_relation_def)
     apply wpsimp+
  apply (clarsimp simp: obj_at'_def)
  done

lemma active_sc_at'_cross:
  "\<lbrakk>(s,s') \<in> state_relation; pspace_aligned s; pspace_distinct s; is_active_sc sc_ptr s;
    sc_at sc_ptr s\<rbrakk>
   \<Longrightarrow> active_sc_at' sc_ptr s'"
  apply (frule state_relation_pspace_relation)
  apply (frule (3) sc_at_cross)
  apply (clarsimp simp: pspace_relation_def obj_at_def is_sc_obj_def)
  apply (drule_tac x=sc_ptr in bspec, blast)
  apply (clarsimp simp: sc_relation_def vs_all_heap_simps active_sc_at'_def obj_at'_def active_sc_def)
  done

lemma active_sc_at'_cross_valid_objs:
  "\<lbrakk>(s,s') \<in> state_relation; pspace_aligned s; pspace_distinct s; is_active_sc sc_ptr s;
    valid_objs s\<rbrakk>
   \<Longrightarrow> active_sc_at' sc_ptr s'"
  apply (frule state_relation_pspace_relation)
  apply (frule (2) sc_at_cross_valid_objs)
    apply (fastforce simp: vs_all_heap_simps )
   apply fastforce
  apply (clarsimp simp: vs_all_heap_simps )
  apply (frule valid_objs_valid_sched_context_size)
   apply fastforce
  apply (clarsimp simp: pspace_relation_def)
  apply (drule_tac x=sc_ptr in bspec, blast)
  apply (clarsimp simp: sc_relation_def active_sc_at'_def obj_at'_def active_sc_def)
  done

lemma is_active_sc'2_cross:
  "\<lbrakk>(s,s') \<in> state_relation; pspace_aligned s; pspace_distinct s; is_active_sc sc_ptr s;
    sc_at sc_ptr s\<rbrakk>
   \<Longrightarrow> is_active_sc' sc_ptr s'"
  apply (frule state_relation_pspace_relation)
  apply (frule (3) sc_at_cross)
  apply (clarsimp simp: pspace_relation_def obj_at_def is_sc_obj_def)
  apply (drule_tac x=sc_ptr in bspec, blast)
  apply (clarsimp simp: sc_relation_def vs_all_heap_simps obj_at'_def
                        active_sc_def opt_map_red StateRelation.is_active_sc'_def opt_pred_def)
  done

lemma active_sc_tcb_at_cross:
  "\<lbrakk>(s, s') \<in> state_relation; active_sc_tcb_at tcbPtr s; pspace_aligned s; pspace_distinct s;
    valid_objs s\<rbrakk>
   \<Longrightarrow> active_sc_tcb_at' tcbPtr s'"
  apply (clarsimp simp: vs_all_heap_simps)
  apply (rename_tac sc_ptr tcb sc n)
  apply (frule_tac state_relation_pspace_relation)
  apply (frule (2) tcb_at_cross[where t=tcbPtr])
   apply (clarsimp simp: obj_at_def is_tcb_def)
  apply (frule (1) pspace_relation_absD[where x=tcbPtr])
  apply clarsimp
  apply (rename_tac ko, case_tac ko; clarsimp simp: tcb_relation_cut_def)
  apply (frule (2) active_sc_at'_cross_valid_objs)
    apply (fastforce simp: vs_all_heap_simps)
   apply fastforce
  apply (rename_tac tcb')
  apply (prop_tac "tcbSchedContext tcb' = Some sc_ptr")
   apply (clarsimp simp: tcb_relation_def)
  apply (clarsimp simp: active_sc_tcb_at'_def in_omonad obj_at'_def active_sc_at'_def)
  done

defs tcbInReleaseQueue_imp_active_sc_tcb_at'_asrt_def:
  "tcbInReleaseQueue_imp_active_sc_tcb_at'_asrt \<equiv>
     \<lambda>s'. \<forall>tcbPtr.
           (tcbInReleaseQueue |< tcbs_of' s') tcbPtr
           \<longrightarrow> (tcb_at' tcbPtr s' \<and> active_sc_tcb_at' tcbPtr s')"

lemma release_queue_active_sc_tcb_at_cross:
  "\<lbrakk>(s, s') \<in> state_relation; valid_release_q s;
    pspace_aligned s; pspace_distinct s; valid_objs s\<rbrakk>
   \<Longrightarrow> \<forall>tcbPtr. (tcbInReleaseQueue |< tcbs_of' s') tcbPtr
                \<longrightarrow> (tcb_at' tcbPtr s' \<and> active_sc_tcb_at' tcbPtr s')"
  apply (clarsimp simp: valid_release_q_def)
  apply (drule_tac x=tcbPtr in bspec)
   apply (fastforce dest: heap_ls_unique state_relation_release_queue_relation
                    simp: release_queue_relation_def list_queue_relation_def)
  apply (rule conjI)
   apply (fastforce intro!: tcb_at_cross simp: obj_at_def is_tcb_def vs_all_heap_simps)
  apply (fastforce elim: active_sc_tcb_at_cross)
  done

lemma in_release_q_tcbInReleaseQueue_eq:
  "release_queue_relation s s' \<Longrightarrow> in_release_queue t s \<longleftrightarrow> (tcbInReleaseQueue |< tcbs_of' s') t"
  by (clarsimp simp: release_queue_relation_def list_queue_relation_def in_release_q_def)

lemma in_set_ready_queues_inQ_eq:
  "ready_queues_relation s s' \<Longrightarrow> t \<in> set (ready_queues s d p) \<longleftrightarrow> (inQ d p |< tcbs_of' s') t"
  by (clarsimp simp: ready_queues_relation_def ready_queue_relation_def Let_def)

lemma in_ready_q_tcbQueued_eq:
  "ready_queues_relation s s' \<Longrightarrow> in_ready_q t s \<longleftrightarrow> (tcbQueued |< tcbs_of' s') t"
  apply (intro iffI)
   apply (clarsimp simp: in_ready_q_def)
   apply (frule in_set_ready_queues_inQ_eq)
   apply (fastforce simp: inQ_def opt_map_def opt_pred_def split: option.splits)
  apply (fastforce simp: ready_queues_relation_def ready_queue_relation_def Let_def inQ_def
                         opt_pred_def in_ready_q_def
                  split: option.splits)
  done

lemma obj_at'_prop:
  "obj_at' P p s \<Longrightarrow> \<exists>ko obj. ksPSpace s p = Some ko \<and> projectKO ko s = Some obj \<and> P obj"
  by (fastforce simp: obj_at'_def')

lemma ready_or_release_cross:
  "\<lbrakk>ready_or_release s; ready_queues_relation s s'; release_queue_relation s s'\<rbrakk>
   \<Longrightarrow> ready_or_release' s'"
  apply (clarsimp simp: ready_or_release'_def ready_or_release_def opt_pred_conj[symmetric])
  apply (fastforce dest: in_release_q_tcbInReleaseQueue_eq in_ready_q_tcbQueued_eq)
  done

\<comment> \<open>Some methods to add invariants to the concrete guard of a corres proof. Often used for properties
    that are asserted to hold in the Haskell definition.\<close>

method add_sym_refs =
  rule_tac Q'="\<lambda>s'. sym_refs (state_refs_of' s')" in corres_cross_add_guard,
  (clarsimp simp: pred_conj_def)?,
  (elim conjE)?,
  (frule invs_sym_refs)?, (frule invs_psp_aligned)?, (frule invs_distinct)?,
  fastforce dest: state_refs_of_cross_eq

method add_ct_not_inQ =
  rule_tac Q'="\<lambda>s'. ct_not_inQ s'" in corres_cross_add_guard,
  (frule valid_sched_valid_sched_action)?,
  fastforce intro!: ct_not_inQ_cross simp: valid_sched_def

method add_sch_act_wf =
  rule_tac Q'="\<lambda>s'. sch_act_wf (ksSchedulerAction s') s'" in corres_cross_add_guard,
  fastforce intro!: sch_act_wf_cross simp: valid_sched_def

method add_ct_idle_or_in_cur_domain' =
  rule_tac Q'="\<lambda>s'. ct_idle_or_in_cur_domain' s'" in corres_cross_add_guard,
  fastforce intro!: ct_idle_or_in_cur_domain'_cross simp: valid_sched_def

method add_valid_idle' =
  rule_tac Q'="\<lambda>s'. valid_idle' s'" in corres_cross_add_guard,
  fastforce intro!: valid_idle'_cross

method add_ready_qs_runnable =
  rule_tac Q'=ready_qs_runnable in corres_cross_add_guard,
  (clarsimp simp: pred_conj_def)?,
  (frule valid_sched_valid_ready_qs)?, (frule invs_psp_aligned)?, (frule invs_distinct)?,
  fastforce dest: ready_qs_runnable_cross

method add_valid_replies for rptr uses simp =
  rule_tac Q'="\<lambda>s. valid_replies'_sc_asrt rptr s" in corres_cross_add_guard,
  fastforce elim: valid_replies_sc_cross simp: simp

method add_cur_tcb' =
  rule_tac Q'="\<lambda>s'. cur_tcb' s'" in corres_cross_add_guard,
  fastforce intro!: cur_tcb_cross

method add_active_sc_at' for scPtr :: machine_word =
  rule_tac Q'="\<lambda>s'. active_sc_at' scPtr s'" in corres_cross_add_guard,
  fastforce intro!: active_sc_at'_cross

end
