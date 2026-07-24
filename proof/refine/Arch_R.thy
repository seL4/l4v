(*
 * Copyright 2014, General Dynamics C4 Systems
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright 2023, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Top level architecture related proofs - generic interface *)

theory Arch_R
imports ArchUntyped_R ArchFinalise_R
begin

arch_requalify_facts
  arch_prepare_set_domain_pspace_aligned (* FIXME arch-split: ArchTcb_AI *)
  arch_prepare_set_domain_pspace_distinct (* FIXME arch-split: ArchTcb_AI *)
  arch_prepare_set_domain_typ_ats (* FIXME arch-split: ArchTcb_AI *)
lemmas [wp] =
  arch_prepare_set_domain_pspace_aligned
  arch_prepare_set_domain_pspace_distinct
  arch_prepare_set_domain_typ_ats

arch_requalify_facts delete_caller_cap_valid_list (* FIXME arch-split: Deterministic_AI *)
lemmas [wp] = delete_caller_cap_valid_list

arch_requalify_consts
  vs_valid_duplicates'

unbundle l4v_word_context

lemmas [datatype_schematic] = cap.sel list.sel(1) list.sel(3)

declare is_aligned_shiftl[intro!]
declare is_aligned_shiftr[intro!]

lemma vp_strgs':
  "valid_pspace' s \<longrightarrow> pspace_distinct' s"
  "valid_pspace' s \<longrightarrow> pspace_aligned' s"
  "valid_pspace' s \<longrightarrow> valid_mdb' s"
  by auto

lemma descendants_of'_helper:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. Q (descendants_of' t (null_filter' (ctes_of s)))\<rbrace>
   \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. Q (descendants_of' t (ctes_of s))\<rbrace>"
  by (clarsimp simp: valid_def)
     (subst null_filter_descendants_of'; fastforce)

lemma createObject_typ_at':
  "\<lbrace>\<lambda>s.  koTypeOf ty = otype \<and> is_aligned ptr (objBitsKO ty) \<and>
         pspace_aligned' s \<and> pspace_no_overlap' ptr (objBitsKO ty) s\<rbrace>
   createObjects' ptr (Suc 0) ty 0
   \<lbrace>\<lambda>rv s. typ_at' otype ptr s\<rbrace>"
  supply
    is_aligned_neg_mask_eq[simp del]
    is_aligned_neg_mask_weaken[simp del]
  apply (clarsimp simp:createObjects'_def alignError_def split_def | wp unless_wp | wpc )+
  apply (clarsimp simp:obj_at'_def ko_wp_at'_def typ_at'_def pspace_distinct'_def)+
  apply (subgoal_tac "ps_clear ptr (objBitsKO ty)
    (s\<lparr>ksPSpace := \<lambda>a. if a = ptr then Some ty else ksPSpace s a\<rparr>)")
  apply (simp add:ps_clear_def)+
  apply (rule ccontr)
  apply (drule int_not_emptyD)
  apply clarsimp
  apply (unfold pspace_no_overlap'_def)
  apply (erule allE)+
  apply (erule(1) impE)
  apply (subgoal_tac "x \<in> mask_range x (objBitsKO y)")
   apply (fastforce simp: is_aligned_neg_mask_eq)
  apply (drule(1) pspace_alignedD')
  apply (clarsimp simp: is_aligned_no_overflow_mask)
  done

lemma set_cap_device_and_range_aligned:
  "is_aligned ptr sz \<Longrightarrow> \<lbrace>\<lambda>_. True\<rbrace>
    set_cap
     (cap.UntypedCap dev ptr sz idx)
     aref
    \<lbrace>\<lambda>rv s.
        \<exists>slot.
           cte_wp_at
            (\<lambda>c. cap_is_device c = dev \<and>
                 up_aligned_area ptr sz \<subseteq> cap_range c)
            slot s\<rbrace>"
  apply (subst is_aligned_neg_mask_eq[symmetric])
   apply simp
  apply (wp set_cap_device_and_range)
  done

crunch cteInsert
  for aobjs_of'[wp]: "\<lambda>s. P (aobjs_of' s)"
  (wp: crunch_wps)

lemma case_option_corresE:
  assumes nonec: "corres r Pn Qn (nc >>=E f) (nc' >>=E g)"
  and     somec: "\<And>v'. corres r (Ps v') (Qs v') (sc v' >>=E f) (sc' v' >>=E g)"
  shows "corres r (case_option Pn Ps v) (case_option Qn Qs v) (case_option nc sc v >>=E f) (case_option nc' sc' v >>=E g)"
  apply (cases v)
   apply simp
   apply (rule nonec)
  apply simp
  apply (rule somec)
  done

lemma cap_relation_Untyped_eq:
  "cap_relation c (UntypedCap d p sz f) = (c = cap.UntypedCap d p sz f)"
  by (cases c) auto

theorem corres_throwError_ser[corres]:
  "corres (ser \<oplus> r) (\<lambda>_. b = syscall_error_map a) (\<lambda>_. True) (throwError a) (throwError b)"
  by simp

lemmas corres_liftE_rel_sumI = corres_liftE_rel_sum[THEN iffD2]
lemmas corres_liftMI = corres_liftM_simp[THEN iffD2]
lemmas corres_liftM2I = corres_liftM2_simp[THEN iffD2]

lemma assocs_map_option:
  "assocs (\<lambda>x. map_option f (pool x)) = map (\<lambda>(x,y). (x, map_option f y)) (assocs pool)"
  by (simp add: assocs_def)

lemma fst_hd_map_eq:
  "xs \<noteq> [] \<Longrightarrow> fst (hd (map (\<lambda>p. (fst p, f (snd p))) xs)) = fst (hd xs)"
  by (induct xs; simp)

lemma assocs_dom_comp_split:
  "set (map fst (filter (\<lambda>x. P (fst x) \<and> snd x = None) (assocs f))) = (- dom f \<inter> Collect P)"
  apply (clarsimp simp: in_assocs_is_fun)
  apply (rule set_eqI)
  apply clarsimp
  apply (rule iffI, clarsimp)
  apply (erule conjE)
  apply (drule not_in_domD)
  apply (rule_tac x="(x,None)" in image_eqI)
   apply simp
  apply simp
  done

lemma st_tcb_strg':
  "st_tcb_at' P p s \<longrightarrow> tcb_at' p s"
  by (auto simp: pred_tcb_at')

crunch setThreadState
  for pspace_no_overlap'[wp]: "pspace_no_overlap' w s"
  (simp: unless_def crunch_simps wp: crunch_wps)

lemma sts_cte_cap_to'[wp]:
  "\<lbrace>ex_cte_cap_to' p\<rbrace> setThreadState st t \<lbrace>\<lambda>rv. ex_cte_cap_to' p\<rbrace>"
  by (wp ex_cte_cap_to'_pres)

crunch setMRs
  for nosch[wp]: "\<lambda>s. P (ksSchedulerAction s)"
  (ignore: getRestartPC setRegister transferCapsToSlots
   wp: hoare_drop_imps hoare_vcg_split_case_option mapM_wp'
   simp: split_def zipWithM_x_mapM)

lemmas setObject_cte_st_tcb_at'[wp] = setCTE_pred_tcb_at'[unfolded setCTE_def]

(* FIXME: move *)
lemma dmo_invs'_simple:
  "no_irq f \<Longrightarrow>
   (\<And>p um. \<lbrace>\<lambda>m'. underlying_memory m' p = um\<rbrace> f \<lbrace>\<lambda>_ m'. underlying_memory m' p = um\<rbrace>) \<Longrightarrow>
   \<lbrace> invs' \<rbrace> doMachineOp f \<lbrace> \<lambda>y. invs' \<rbrace>"
  by (rule hoare_pre, rule dmo_invs', wp no_irq, simp_all add:valid_def split_def)

(* FIXME arch-split: move *)
lemmas whenE_throwError_corres_terminal =
  whenE_throwError_corres[where m="returnOk ()" and m'="returnOk ()", OF _ _ corres_returnOkTT, simplified]

(* FIXME arch-split: move *)
lemma eq_arch_update':
  "\<lbrakk> ArchObjectCap cp = cteCap cte; arch_capBadge cp = None \<rbrakk> \<Longrightarrow>
   is_arch_update' (ArchObjectCap cp) cte"
  by (drule sym, clarsimp simp: is_arch_update'_def gen_isCap_simps)

(* FIXME arch-split: move *)
lemma ex_cte_not_in_untyped_range:
  "\<lbrakk>(ctes_of s) cref = Some (CTE (capability.UntypedCap d ptr bits idx) mnode);
    descendants_of' cref (ctes_of s) = {}; invs' s;
    ex_cte_cap_wp_to' (\<lambda>_. True) x s; valid_global_refs' s\<rbrakk>
   \<Longrightarrow> x \<notin> {ptr .. ptr + mask bits}"
  apply clarsimp
  apply (drule(1) cte_cap_in_untyped_range)
   apply (fastforce simp:cte_wp_at_ctes_of)+
  done

lemma corres_splitEE':
  assumes "corres_underlying sr nf nf' (f \<oplus> r') P P' a c"
  assumes "\<And>rv rv'. r' rv rv'
           \<Longrightarrow> corres_underlying sr nf nf' (f \<oplus> r) (R rv) (R' rv') (b rv) (d rv')"
  assumes "\<lbrace>Q\<rbrace> a \<lbrace>R\<rbrace>,\<lbrace>\<top>\<top>\<rbrace>" "\<lbrace>Q'\<rbrace> c \<lbrace>R'\<rbrace>,\<lbrace>\<top>\<top>\<rbrace>"
  shows   "corres_underlying sr nf nf' (f \<oplus> r) (P and Q) (P' and Q') (a >>=E (\<lambda>rv. b rv)) (c >>=E (\<lambda>rv'. d rv'))"
  by (rule corres_splitEE; rule assms)

lemma select_ext_fa:
  "free_asid_select asid_tbl \<in> S
  \<Longrightarrow> ((select_ext (\<lambda>_. free_asid_select asid_tbl) S) :: _ det_ext_monad)
   = return (free_asid_select asid_tbl)"
  by (simp add: select_ext_def get_def gets_def bind_def assert_def return_def fail_def)

locale Arch_R =
  fixes valid_arch_inv' :: "Arch.invocation \<Rightarrow> kernel_state \<Rightarrow> bool"
  fixes archinv_relation :: "arch_invocation \<Rightarrow> Arch.invocation \<Rightarrow> bool"
  assumes invokeArch_tcb_at':
    "\<And>ai p.
     \<lbrace>invs' and valid_arch_inv' ai and ct_active' and st_tcb_at' active' p\<rbrace>
     Arch.performInvocation ai
     \<lbrace>\<lambda>rv. tcb_at' p\<rbrace>"
  assumes sts_valid_arch_inv':
    "\<And>st t ai. setThreadState st t \<lbrace>valid_arch_inv' ai\<rbrace>"
  assumes arch_performInvocation_invs':
    "\<And>invocation.
     \<lbrace>invs' and ct_active' and valid_arch_inv' invocation\<rbrace>
     Arch.performInvocation invocation
     \<lbrace>\<lambda>rv. invs'\<rbrace>"
  assumes arch_decodeInvocation_inv[wp]:
    "\<And>label args capIndex slot cap extraCaps.
     Arch.decodeInvocation label args capIndex slot cap extraCaps \<lbrace>P\<rbrace>"
  assumes arch_performInvocation_corres:
    "\<And>ai ai'.
     archinv_relation ai ai' \<Longrightarrow>
     corres (dc \<oplus> (=))
       (einvs and ct_active and valid_arch_inv ai and schact_is_rct)
       (invs' and ct_active' and valid_arch_inv' ai' and (\<lambda>s. vs_valid_duplicates' (ksPSpace s)))
       (arch_perform_invocation ai) (Arch.performInvocation ai')"
  assumes arch_decodeInvocation_corres:
    "\<And>arch_cap arch_cap' excaps excaps' slot mi args cptr'.
     \<lbrakk> acap_relation arch_cap arch_cap';
       list_all2 cap_relation (map fst excaps) (map fst excaps');
       list_all2 (\<lambda>s s'. s' = cte_map s) (map snd excaps) (map snd excaps') \<rbrakk> \<Longrightarrow>
     corres
     (ser \<oplus> archinv_relation)
     (invs and valid_cap (cap.ArchObjectCap arch_cap) and
      cte_wp_at ((=) (cap.ArchObjectCap arch_cap)) slot and
      (\<lambda>s. \<forall>x\<in>set excaps. s \<turnstile> fst x \<and> cte_at (snd x) s))
     (invs' and valid_cap' (capability.ArchObjectCap arch_cap') and
      (\<lambda>s. \<forall>x\<in>set excaps'. s \<turnstile>' fst x \<and> cte_at' (snd x) s) and
      (\<lambda>s. vs_valid_duplicates' (ksPSpace s)))
     (arch_decode_invocation (mi_label mi) args (to_bl cptr') slot arch_cap excaps)
     (Arch.decodeInvocation (mi_label mi) args cptr' (cte_map slot) arch_cap' excaps')"
  assumes arch_decodeInvocation_wf[wp]:
    "\<And>arch_cap slot excaps label args cap_index.
     \<lbrace>invs' and valid_cap' (ArchObjectCap arch_cap) and
      cte_wp_at' ((=) (ArchObjectCap arch_cap) \<circ> cteCap) slot and
      (\<lambda>s. \<forall>x \<in> set excaps. cte_wp_at' ((=) (fst x) \<circ> cteCap) (snd x) s) and
      (\<lambda>s. \<forall>x \<in> set excaps. \<forall>r \<in> cte_refs' (fst x) (irq_node' s). ex_cte_cap_to' r s) and
      (\<lambda>s. \<forall>x \<in> set excaps. s \<turnstile>' fst x) and
      sch_act_simple and (\<lambda>s. vs_valid_duplicates' (ksPSpace s))\<rbrace>
     Arch.decodeInvocation label args cap_index slot arch_cap excaps
     \<lbrace>valid_arch_inv'\<rbrace>,-"
  assumes setObject_TCB_valid_duplicates'[wp]:
    "\<And>p tcb. setObject p (tcb::tcb) \<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"

end
