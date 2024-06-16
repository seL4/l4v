(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Detype_R
imports Retype_R
begin

context begin interpretation Arch . (*FIXME: arch_split*)

text \<open>Establishing that the invariants are maintained
        when a region of memory is detyped, that is,
        removed from the model.\<close>

definition
  "descendants_range_in' S p \<equiv>
  \<lambda>m. \<forall>p' \<in> descendants_of' p m. \<forall>c n. m p' = Some (CTE c n) \<longrightarrow> capRange c \<inter> S = {}"

lemma null_filter_simp'[simp]:
  "null_filter' (null_filter' x) = null_filter' x"
  apply (rule ext)
  apply (auto simp:null_filter'_def split:if_splits)
  done

lemma descendants_range_in'_def2:
  "descendants_range_in' S p = (\<lambda>m. \<forall>p'\<in>descendants_of' p (null_filter' m).
  \<forall>c n. (null_filter' m) p' = Some (CTE c n) \<longrightarrow> capRange c \<inter> S = {})"
  apply (clarsimp simp:descendants_range_in'_def
                  split:if_splits)
  apply (rule ext)
  apply (rule subst[OF null_filter_descendants_of'])
   apply simp
  apply (rule iffI)
   apply (clarsimp simp:null_filter'_def)+
  apply (drule(1) bspec)
  apply (elim allE impE ballE)
   apply (rule ccontr)
   apply (clarsimp split:if_splits simp:descendants_of'_def)
    apply (erule(1) subtree_not_Null)
   apply fastforce
  apply simp
  done

definition
  "descendants_range' cap p \<equiv>
  \<lambda>m. \<forall>p' \<in> descendants_of' p m. \<forall>c n. m p' = Some (CTE c n) \<longrightarrow> capRange c \<inter> capRange cap = {}"

lemma descendants_rangeD':
  "\<lbrakk> descendants_range' cap p m; m \<turnstile> p \<rightarrow> p'; m p' = Some (CTE c n) \<rbrakk>
  \<Longrightarrow> capRange c \<inter> capRange cap = {}"
  by (simp add: descendants_range'_def descendants_of'_def)

lemma descendants_range_in_lift':
  assumes st: "\<And>P. \<lbrace>\<lambda>s. Q s \<and> P ((swp descendants_of') (null_filter' (ctes_of s)))\<rbrace>
  f \<lbrace>\<lambda>r s. P ((swp descendants_of') (null_filter' (ctes_of s)))\<rbrace>"
  assumes cap_range:
  "\<And>P p. \<lbrace>\<lambda>s. Q' s \<and> cte_wp_at' (\<lambda>c. P (capRange (cteCap c))) p s\<rbrace> f \<lbrace>\<lambda>r s. cte_wp_at' (\<lambda>c. P (capRange (cteCap c))) p s\<rbrace>"
  shows "\<lbrace>\<lambda>s. Q s \<and> Q' s \<and> descendants_range_in' S slot (ctes_of s)\<rbrace> f \<lbrace>\<lambda>r s. descendants_range_in' S slot (ctes_of s)\<rbrace>"
  apply (clarsimp simp:descendants_range_in'_def2)
  apply (subst swp_def[where f = descendants_of', THEN meta_eq_to_obj_eq,
                       THEN fun_cong, THEN fun_cong, symmetric])+
  apply (simp only: Ball_def[unfolded imp_conv_disj])
  apply (rule hoare_pre)
   apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift st cap_range)
   apply (rule_tac Q = "\<lambda>r s. cte_wp_at' (\<lambda>c. capRange (cteCap c) \<inter> S = {}) x s"
      in hoare_strengthen_post)
    apply (wp cap_range)
   apply (clarsimp simp:cte_wp_at_ctes_of null_filter'_def)
  apply clarsimp
  apply (drule spec, drule(1) mp)
  apply (subst (asm) null_filter_descendants_of')
   apply simp
  apply (case_tac "(ctes_of s) x")
   apply (clarsimp simp:descendants_of'_def null_filter'_def subtree_target_Some)
  apply (case_tac a)
   apply (clarsimp simp:cte_wp_at_ctes_of null_filter'_def split:if_splits)
  done

lemma descendants_range_inD':
  "\<lbrakk>descendants_range_in' S p ms; p'\<in>descendants_of' p ms; ms p' = Some cte\<rbrakk>
   \<Longrightarrow> capRange (cteCap cte) \<inter> S = {}"
  apply (case_tac cte)
  apply (auto simp:descendants_range_in'_def cte_wp_at_ctes_of dest!:bspec)
  done
end

context begin interpretation Arch . (*FIXME: arch_split*)

lemma descendants_range'_def2:
  "descendants_range' cap p = descendants_range_in' (capRange cap) p"
  by (simp add: descendants_range_in'_def descendants_range'_def)


defs deletionIsSafe_def:
  "deletionIsSafe \<equiv> \<lambda>ptr bits s. \<forall>p t m r.
       (cte_wp_at' (\<lambda>cte. cteCap cte = capability.ReplyCap t m r) p s \<longrightarrow>
       t \<notin> {ptr .. ptr + 2 ^ bits - 1}) \<and>
       (\<forall>ko. ksPSpace s p = Some (KOArch ko) \<and> p \<in> {ptr .. ptr + 2 ^ bits - 1}
        \<longrightarrow> 6 \<le> bits)"

defs deletionIsSafe_delete_locale_def:
  "deletionIsSafe_delete_locale \<equiv> \<lambda>ptr bits s. \<forall>p. ko_wp_at' live' p s \<longrightarrow> p \<notin> {ptr .. ptr + 2 ^ bits - 1}"

defs ksASIDMapSafe_def:
  "ksASIDMapSafe \<equiv> \<lambda>s. True"

defs cNodePartialOverlap_def:
  "cNodePartialOverlap \<equiv> \<lambda>cns inRange. \<exists>p n. cns p = Some n
    \<and> (\<not> is_aligned p (cte_level_bits + n)
      \<or> cte_level_bits + n \<ge> word_bits
      \<or> (\<not> {p .. p + 2 ^ (cte_level_bits + n) - 1} \<subseteq> {p. inRange p}
        \<and> \<not> {p .. p + 2 ^ (cte_level_bits + n) - 1} \<subseteq> {p. \<not> inRange p}))"

(* FIXME: move *)
lemma deleteObjects_def2:
  "is_aligned ptr bits \<Longrightarrow>
   deleteObjects ptr bits = do
     stateAssert (deletionIsSafe ptr bits) [];
     stateAssert (deletionIsSafe_delete_locale ptr bits) [];
     doMachineOp (freeMemory ptr bits);
     stateAssert (\<lambda>s. \<not> cNodePartialOverlap (gsCNodes s) (\<lambda>x. x \<in> {ptr .. ptr + 2 ^ bits - 1})) [];
     modify (\<lambda>s. s \<lparr> ksPSpace := \<lambda>x. if x \<in> {ptr .. ptr + 2 ^ bits - 1}
                                        then None else ksPSpace s x,
                     gsUserPages := \<lambda>x. if x \<in> {ptr .. ptr + 2 ^ bits - 1}
                                           then None else gsUserPages s x,
                     gsCNodes := \<lambda>x. if x \<in> {ptr .. ptr + 2 ^ bits - 1}
                                        then None else gsCNodes s x \<rparr>);
     stateAssert ksASIDMapSafe []
   od"
  apply (simp add: deleteObjects_def is_aligned_mask[symmetric] unless_def deleteGhost_def)
  apply (rule bind_eqI, rule ext)
  apply (rule bind_eqI, rule ext)
  apply (rule bind_eqI, rule ext)
  apply (simp add: bind_assoc[symmetric])
  apply (rule bind_cong[rotated], rule refl)
  apply (simp add: bind_assoc modify_modify deleteRange_def gets_modify_def)
  apply (rule ext, simp add: exec_modify stateAssert_def assert_def bind_assoc exec_get
                             NOT_eq[symmetric] mask_in_range)
  apply (clarsimp simp: simpler_modify_def)
  apply (simp add: data_map_filterWithKey_def split: if_split_asm)
  apply (rule arg_cong2[where f=gsCNodes_update])
   apply (simp add: NOT_eq[symmetric] mask_in_range ext)
  apply (rule arg_cong2[where f=gsUserPages_update])
   apply (simp add: NOT_eq[symmetric] mask_in_range ext)
  apply (rule arg_cong[where f="\<lambda>f. ksPSpace_update f s" for s])
  apply (simp add: NOT_eq[symmetric] mask_in_range ext   split: option.split)
  done

lemma deleteObjects_def3:
  "deleteObjects ptr bits =
   do
     assert (is_aligned ptr bits);
     stateAssert (deletionIsSafe ptr bits) [];
     stateAssert (deletionIsSafe_delete_locale ptr bits) [];
     doMachineOp (freeMemory ptr bits);
     stateAssert (\<lambda>s. \<not> cNodePartialOverlap (gsCNodes s) (\<lambda>x. x \<in> {ptr .. ptr + 2 ^ bits - 1})) [];
     modify (\<lambda>s. s \<lparr> ksPSpace := \<lambda>x. if x \<in> {ptr .. ptr + 2 ^ bits - 1}
                                              then None else ksPSpace s x,
                     gsUserPages := \<lambda>x. if x \<in> {ptr .. ptr + 2 ^ bits - 1}
                                           then None else gsUserPages s x,
                     gsCNodes := \<lambda>x. if x \<in> {ptr .. ptr + 2 ^ bits - 1}
                                        then None else gsCNodes s x \<rparr>);
     stateAssert ksASIDMapSafe []
   od"
  apply (cases "is_aligned ptr bits")
   apply (simp add: deleteObjects_def2)
  apply (simp add: deleteObjects_def is_aligned_mask
                   unless_def alignError_def)
  done

lemma obj_relation_cuts_in_obj_range:
  "\<lbrakk> (y, P) \<in> obj_relation_cuts ko x; x \<in> obj_range x ko;
       kheap s x = Some ko; valid_objs s; pspace_aligned s \<rbrakk> \<Longrightarrow> y \<in> obj_range x ko"
  apply (cases ko, simp_all)
   apply (clarsimp split: if_split_asm)
   apply (subgoal_tac "cte_at (x, ya) s")
    apply (drule(2) cte_at_cte_map_in_obj_bits)
    apply (simp add: obj_range_def)
   apply (fastforce intro: cte_wp_at_cteI)
  apply (frule(1) pspace_alignedD)
  apply (frule valid_obj_sizes, erule ranI)
  apply (rename_tac arch_kernel_obj)
  apply (case_tac arch_kernel_obj, simp_all)
    apply (clarsimp simp only: obj_range_def field_simps atLeastAtMost_iff bit_simps
                                obj_bits.simps arch_kobj_size.simps)
    apply (rule context_conjI)
     apply (erule is_aligned_no_wrap')
      apply simp
     apply (simp add: ucast_less_shiftl_helper')
    apply (subst add_diff_eq[symmetric])
    apply (rule word_plus_mono_right)
     apply (subst word_less_sub_le, simp)
     apply (simp add: ucast_less_shiftl_helper')
    apply (simp add: field_simps)
   apply (clarsimp simp only: obj_range_def field_simps atLeastAtMost_iff bit_simps
                              obj_bits.simps arch_kobj_size.simps)
   apply (rule context_conjI)
    apply (erule is_aligned_no_wrap')
     apply simp
    apply (simp add: ucast_less_shiftl_helper')
   apply (subst add_diff_eq[symmetric])
   apply (rule word_plus_mono_right)
    apply (subst word_less_sub_le, simp)
    apply (simp add: ucast_less_shiftl_helper')
   apply (simp add: field_simps)
apply (clarsimp simp only: obj_range_def field_simps atLeastAtMost_iff bit_simps
                              obj_bits.simps arch_kobj_size.simps)
   apply (rule context_conjI)
    apply (erule is_aligned_no_wrap')
     apply simp
    apply (simp add: ucast_less_shiftl_helper')
   apply (subst add_diff_eq[symmetric])
   apply (rule word_plus_mono_right)
    apply (subst word_less_sub_le, simp)
    apply (simp add: ucast_less_shiftl_helper')
   apply (simp add: field_simps)
apply (clarsimp simp only: obj_range_def field_simps atLeastAtMost_iff bit_simps
                              obj_bits.simps arch_kobj_size.simps)
   apply (rule context_conjI)
    apply (erule is_aligned_no_wrap')
     apply simp
    apply (simp add: ucast_less_shiftl_helper')
   apply (subst add_diff_eq[symmetric])
   apply (rule word_plus_mono_right)
    apply (subst word_less_sub_le, simp)
    apply (simp add: ucast_less_shiftl_helper')
   apply (simp add: field_simps)
  apply (rename_tac vmpage_size)
  apply (clarsimp simp only: obj_range_def field_simps atLeastAtMost_iff bit_simps
                             obj_bits.simps arch_kobj_size.simps)
  apply (subgoal_tac "n * 2 ^ pageBits < 2 ^ pageBitsForSize vmpage_size")
   apply (rule context_conjI)
    apply (erule is_aligned_no_wrap')
    apply (simp add: bit_simps)
   apply (subst add_diff_eq[symmetric])
   apply (rule word_plus_mono_right)
    apply (subst word_less_sub_le, simp add: word_bits_def)
    apply (simp add: bit_simps)
   apply (simp add: field_simps)
  apply (simp only: pageBits_def)
  apply (erule word_less_power_trans2)
   apply (case_tac vmpage_size, simp_all add: pageBits_def)[1]
  apply (simp add: word_bits_def)
  done

lemma obj_relation_cuts_eqv_base_in_detype_range:
  "\<lbrakk> (y, P) \<in> obj_relation_cuts ko x; kheap s x = Some ko;
      valid_objs s; pspace_aligned s;
      valid_untyped (cap.UntypedCap d base bits idx) s \<rbrakk>
    \<Longrightarrow> (x \<in> {base .. base + 2 ^ bits - 1}) = (y \<in> {base .. base + 2 ^ bits - 1})"
  apply (simp add: valid_untyped_def del: atLeastAtMost_iff)
  apply (subgoal_tac "x \<in> obj_range x ko")
   apply (subgoal_tac "y \<in> obj_range x ko")
    apply blast
   apply (erule(4) obj_relation_cuts_in_obj_range)
  apply (simp add: obj_range_def)
  apply (rule is_aligned_no_overflow)
  apply (erule(1) pspace_alignedD)
  done

lemma detype_pspace_relation:
  assumes psp: "pspace_relation (kheap s) (ksPSpace s')"
  and     bwb: "bits < word_bits"
  and      al: "is_aligned base bits"
  and      vs: "valid_pspace s"
  and      vu: "valid_untyped (cap.UntypedCap d base bits idx) s"
  shows        "pspace_relation (kheap (detype {base .. base + 2 ^ bits - 1} s))
                 (\<lambda>x. if x \<in> {base .. base + 2 ^ bits - 1} then None else ksPSpace s' x)"
  (is "pspace_relation ?ps ?ps'")
proof -
  let ?range = "{base .. base + 2 ^ bits - 1}"
  let ?ps'' = "(kheap s |` (-?range))"

  have pa: "pspace_aligned s" and vo: "valid_objs s"
    using vs by (simp add: valid_pspace_def)+

  have pspace:
    "\<And>x. \<lbrakk> x \<notin> ?range; x \<in> dom (kheap s) \<rbrakk> \<Longrightarrow> ?ps x = kheap s x"
    by (clarsimp simp add: detype_def field_simps)

  have pspace'':
    "\<And>x. \<lbrakk> x \<notin> ?range; x \<in> dom (kheap s) \<rbrakk> \<Longrightarrow> ?ps'' x = kheap s x"
    by (clarsimp simp add: detype_def)

  have psdom_pre: "dom ?ps = (dom (kheap s) - ?range)"
    by (fastforce simp:field_simps)

  show ?thesis
    unfolding pspace_relation_def
  proof (intro conjI)

    have domeq': "dom (ksPSpace s') = pspace_dom (kheap s)"
      using psp by (simp add: pspace_relation_def)

    note eqv_base_in = obj_relation_cuts_eqv_base_in_detype_range
                          [OF _ _ vo pa vu]

    note atLeastAtMost_iff[simp del]
    show domeq: "pspace_dom ?ps = dom ?ps'"
      apply (simp add: dom_if_None domeq')
      apply (simp add: pspace_dom_def detype_def dom_if_None)
      apply (intro set_eqI iffI, simp_all)
       apply (clarsimp simp: eqv_base_in field_simps)
       apply (rule rev_bexI, erule domI)
       apply (simp add: image_def, erule rev_bexI, simp)
      apply (elim exE bexE DiffE conjE domE)
      apply (rule bexI, assumption)
      apply (clarsimp simp add: eqv_base_in field_simps)
      done

    show "\<forall>x\<in>dom ?ps.
       \<forall>(y, P)\<in>obj_relation_cuts (the (?ps x)) x.
          P (the (?ps x))
           (the (if y \<in> ?range then None else ksPSpace s' y))"
      using psp
      apply (simp add: pspace_relation_def psdom_pre split del: if_split)
      apply (erule conjE, rule ballI, erule DiffE, drule(1) bspec)
      apply (erule domE)
      apply (simp add: field_simps detype_def cong: conj_cong)
      apply (erule ballEI, clarsimp)
      apply (simp add: eqv_base_in)
      done
  qed
qed

declare plus_Collect_helper2[simp]

lemma cte_map_obj_range_helper:
  "\<lbrakk> cte_at cref s; pspace_aligned s; valid_objs s \<rbrakk>
    \<Longrightarrow> \<exists>ko. kheap s (fst cref) = Some ko \<and> cte_map cref \<in> obj_range (fst cref) ko"
  apply (drule(2) cte_at_cte_map_in_obj_bits)
  apply (clarsimp simp: obj_range_def)
  done

lemma cte_map_untyped_range:
  "\<lbrakk> s \<turnstile> cap; cte_at cref s; pspace_aligned s; valid_objs s \<rbrakk>
     \<Longrightarrow> (cte_map cref \<in> untyped_range cap) = (fst cref \<in> untyped_range cap)"
  apply (cases cap, simp_all)
  apply (drule(2) cte_map_obj_range_helper)
  apply (clarsimp simp: valid_cap_def valid_untyped_def)
  apply (elim allE, drule(1) mp)
  apply (rule iffI)
   apply (erule impE)
    apply (rule notemptyI[where x="cte_map cref"])
    apply simp
   apply clarsimp
   apply (drule subsetD [OF _ p_in_obj_range])
   apply simp+
  apply (erule impE)
   apply (rule notemptyI[where x="fst cref"])
   apply (simp add: p_in_obj_range)
  apply clarsimp
  apply (drule(1) subsetD)
  apply simp
  done

lemma pspace_aligned'_cut:
  "pspace_aligned' s \<Longrightarrow>
   pspace_aligned' (s \<lparr> ksPSpace := \<lambda>x. if P x then None else ksPSpace s x\<rparr>)"
  by (simp add: pspace_aligned'_def dom_if_None)

lemma pspace_distinct'_cut:
  "pspace_distinct' s \<Longrightarrow>
   pspace_distinct' (s \<lparr> ksPSpace := \<lambda>x. if P x then None else ksPSpace s x\<rparr>)"
  by (simp add: pspace_distinct'_def dom_if_None ps_clear_def
                Diff_Int_distrib)

lemma ko_wp_at_delete':
  "pspace_distinct' s \<Longrightarrow>
   ko_wp_at' P p (s \<lparr> ksPSpace := \<lambda>x. if base \<le> x \<and> x \<le> base + (2 ^ magnitude - 1) then None else ksPSpace s x \<rparr>)
    = (\<not> (base \<le> p \<and> p \<le> base + (2 ^ magnitude - 1)) \<and> ko_wp_at' P p s)"
  apply (simp add: ko_wp_at'_def projectKOs ps_clear_def dom_if_None)
  apply (intro impI iffI)
   apply clarsimp
   apply (drule(1) pspace_distinctD')
   apply (simp add: ps_clear_def)
  apply (clarsimp simp: Diff_Int_distrib)
  done

lemma obj_at_delete':
  "pspace_distinct' s \<Longrightarrow>
   obj_at' P p (s \<lparr> ksPSpace := \<lambda>x. if base \<le> x \<and> x \<le> base + (2 ^ magnitude - 1) then None else ksPSpace s x \<rparr>)
    = (\<not> (base \<le> p \<and> p \<le> base + (2 ^ magnitude - 1)) \<and> obj_at' P p s)"
  unfolding obj_at'_real_def
  by (rule ko_wp_at_delete')

lemma cte_wp_at_delete':
  "\<lbrakk> s \<turnstile>' UntypedCap d base magnitude idx; pspace_distinct' s \<rbrakk> \<Longrightarrow>
   cte_wp_at' P p (s \<lparr> ksPSpace := \<lambda>x. if base \<le> x \<and> x \<le> base + (2 ^ magnitude - 1) then None else ksPSpace s x \<rparr>)
    = (\<not> (base \<le> p \<and> p \<le> base + (2 ^ magnitude - 1)) \<and> cte_wp_at' P p s)"
  apply (simp add: cte_wp_at_obj_cases' obj_at_delete')
  apply (subgoal_tac "\<forall>Q n. obj_at' Q (p - n) s \<and> tcb_cte_cases n \<noteq> None \<longrightarrow>
                             ((p - n) \<in> {base .. base + (2 ^ magnitude - 1)})
                              = (p \<in> {base .. base + (2 ^ magnitude - 1)})")
   apply auto[1]
  apply (clarsimp simp: obj_at'_real_def projectKOs valid_cap'_def
                        valid_untyped'_def
              simp del: atLeastAtMost_iff)
  apply (drule_tac x="p - n" in spec)
  apply (clarsimp simp: ko_wp_at'_def capAligned_def
              simp del: atLeastAtMost_iff)
   apply (thin_tac "is_aligned x minUntypedSizeBits" for x)
  apply (drule(1) aligned_ranges_subset_or_disjoint)
  apply (subgoal_tac "{p, p - n} \<subseteq> obj_range' (p - n) (KOTCB obj)")
   apply (clarsimp simp del: atLeastAtMost_iff
                       simp: field_simps objBits_simps obj_range'_def)
   apply fastforce
  apply (simp add: obj_range'_def mask_in_range[symmetric]
              del: atLeastAtMost_iff)
  apply (simp add: objBits_simps)
  apply (frule(1) tcb_cte_cases_aligned_helpers)
  apply (simp add: is_aligned_neg_mask_eq)
  done

lemma map_to_ctes_delete:
  assumes vc: "s \<turnstile>' UntypedCap d base magnitude idx"
      and vs: "pspace_distinct' s"
  shows
  "map_to_ctes (\<lambda>x. if base \<le> x \<and> x \<le> base + (2 ^ magnitude - 1) then None else ksPSpace s x)
    = (\<lambda>x. if base \<le> x \<and> x \<le> base + (2 ^ magnitude - 1) then None else ctes_of s x)"
  using cte_wp_at_delete' [where P="(=) cte" for cte, OF vc vs]
        arg_cong [where f=Not, OF cte_wp_at_delete' [OF vc vs, where P="\<top>"]]
  apply (simp (no_asm_use) add: cte_wp_at_ctes_of)
  apply (rule ext)
  apply (case_tac "map_to_ctes (\<lambda>x. if base \<le> x \<and> x \<le> base + (2 ^ magnitude - 1) then None else ksPSpace s x) x")
   apply (fastforce split: if_split_asm)
  apply simp
  done

lemma word_range_card:
  "base \<le>base + h \<Longrightarrow> card {base..base + (h::machine_word)} = (unat h) + 1"
proof (induct h rule: word_induct2)
  case zero show ?case by simp
next
  case (suc h)
  have interval_plus_one_machine_word:
    "\<And>base ceil. \<lbrakk>base \<le> ceil + 1;ceil \<le> ceil + 1\<rbrakk> \<Longrightarrow>
                 {base..ceil + 1} = {base .. ceil } \<union> {ceil + (1::machine_word)}"
    by (auto intro:order_antisym simp:not_le inc_le)
  show ?case
    using suc plus_one_helper2[where n = h and x = h,simplified]
    apply (subst add.commute[where a = 1])
    apply (subst add.assoc[symmetric])
    apply (subst interval_plus_one_machine_word)
      apply (simp add: field_simps)
     apply (subst add.assoc)
     apply (rule word_plus_mono_right)
      apply (simp add: field_simps)
     apply (simp add: field_simps)
    apply (subst card_Un_disjoint; simp)
     apply (clarsimp simp: field_simps)
    apply (subst suc)
     apply (erule word_plus_mono_right2)
     apply (simp add: field_simps)
    apply simp
    apply (simp add: unatSuc)
    done
qed

end

locale detype_locale' = detype_locale + constrains s::"det_state"

lemma (in detype_locale') deletionIsSafe:
  assumes sr: "(s, s') \<in> state_relation"
  and    cap: "cap = cap.UntypedCap d base magnitude idx"
  and      vs: "valid_pspace s"
  and      al: "is_aligned base magnitude"
  and      vu: "valid_untyped (cap.UntypedCap d base magnitude idx) s"
  shows       "deletionIsSafe base magnitude s'"
proof -
  interpret Arch . (* FIXME: arch_split *)
  note blah[simp del] =  atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex
          atLeastAtMost_iff
  have "\<And>t m r. \<exists>ptr. cte_wp_at ((=) (cap.ReplyCap t m r)) ptr s
        \<Longrightarrow> t \<notin> {base .. base + 2 ^ magnitude - 1}"
    by (fastforce dest!: valid_cap2 simp: cap obj_reply_refs_def)
  hence "\<forall>ptr t m r. cte_wp_at ((=) (cap.ReplyCap t m r)) ptr s
         \<longrightarrow> t \<notin> {base .. base + 2 ^ magnitude - 1}"
    by (fastforce simp del: split_paired_All)
  hence "\<forall>t. t \<in> {base .. base + 2 ^ magnitude - 1} \<longrightarrow>
          (\<forall>ptr m r. \<not> cte_wp_at ((=) (cap.ReplyCap t m r)) ptr s)"
    by fastforce
  hence cte: "\<forall>t. t \<in> {base .. base + 2 ^ magnitude - 1} \<longrightarrow>
          (\<forall>ptr m r. \<not> cte_wp_at' (\<lambda>cte. cteCap cte = ReplyCap t m r) ptr s')"
    unfolding deletionIsSafe_def
    apply -
    apply (erule allEI)
    apply (rule impI, drule(1) mp)
    apply (thin_tac "t \<in> S" for S)
    apply (intro allI)
    apply (clarsimp simp: cte_wp_at_neg2 cte_wp_at_ctes_of
                simp del: split_paired_All)
    apply (frule pspace_relation_cte_wp_atI [rotated])
      apply (rule invs_valid_objs [OF invs])
     apply (rule state_relation_pspace_relation [OF sr])
    apply (clarsimp simp: cte_wp_at_neg2 simp del: split_paired_All)
    apply (drule_tac x="(a,b)" in spec)
    apply (clarsimp simp: cte_wp_cte_at cte_wp_at_caps_of_state)
    apply (case_tac c, simp_all)
    apply fastforce
    done

  have arch: "\<And> ko p. \<lbrakk> ksPSpace s' p = Some (KOArch ko); p \<in> {base..base + 2 ^ magnitude - 1} \<rbrakk>
             \<Longrightarrow> 6 \<le> magnitude"
    using sr vs vu
    apply (clarsimp simp: state_relation_def)
    apply (erule(1) pspace_dom_relatedE)
    apply (frule obj_relation_cuts_eqv_base_in_detype_range[symmetric])
        apply simp
       apply (clarsimp simp:valid_pspace_def)+
      apply simp
    apply (clarsimp simp:valid_untyped_def)
    apply (drule spec)+
    apply (erule(1) impE)
    apply (erule impE)
     apply (drule p_in_obj_range)
       apply (clarsimp)+
     apply blast
    apply clarsimp
    apply (drule card_mono[rotated])
     apply fastforce
    apply (clarsimp simp:valid_pspace_def obj_range_def p_assoc_help)
    apply (subst (asm) word_range_card)
     apply (rule is_aligned_no_overflow')
     apply (erule(1) pspace_alignedD)
    apply (subst (asm) word_range_card)
     apply (rule is_aligned_no_overflow'[OF al])
    apply (rule ccontr)
    apply (simp add:not_le)
    apply (subgoal_tac "obj_bits koa < 32")
     prefer 2
     apply (case_tac koa,simp_all add:objBits_simps word_bits_def)
      apply (drule(1) valid_cs_size_objsI)
      apply (clarsimp simp:valid_cs_size_def word_bits_def cte_level_bits_def)
     apply (rename_tac arch_kernel_obj)
     apply (case_tac arch_kernel_obj,simp_all add:bit_simps word_bits_def)
     apply (simp add:pageBitsForSize_def bit_simps split:vmpage_size.splits)
    apply (subgoal_tac "6 \<le> obj_bits koa")
     apply simp
    apply (case_tac koa, simp_all add: other_obj_relation_def
                                       objBits_simps cte_relation_def
                                split: if_splits)
     apply (rename_tac ako,
            case_tac ako;
             simp add: arch_kobj_size_def bit_simps pageBitsForSize_def
                split: vmpage_size.splits)+
    done
  thus ?thesis using cte by (auto simp: deletionIsSafe_def)
qed

context begin interpretation Arch . (*FIXME: arch_split*)

text \<open>Invariant preservation across concrete deletion\<close>

lemma caps_containedD':
  "\<lbrakk> ctes_of s p = Some cte; ctes_of s p' = Some cte';
     \<not> isUntypedCap (cteCap cte); capRange (cteCap cte) \<inter> untypedRange (cteCap cte') \<noteq> {};
     caps_contained' (ctes_of s) \<rbrakk> \<Longrightarrow>
     capRange (cteCap cte) \<subseteq> untypedRange (cteCap cte')"
  apply (cases cte, cases cte')
  apply (simp add: caps_contained'_def)
  apply blast
  done

lemma untyped_mdbD':
  "\<lbrakk> ctes p = Some cte; ctes p' = Some cte';
     isUntypedCap (cteCap cte); capRange (cteCap cte') \<inter> untypedRange (cteCap cte) \<noteq> {};
     \<not> isUntypedCap (cteCap cte');
     untyped_mdb' ctes \<rbrakk> \<Longrightarrow> p' \<in> descendants_of' p ctes"
  by (cases cte, cases cte', simp add: untyped_mdb'_def)

lemma ko_wp_at_state_refs_ofD:
  "\<lbrakk> ko_wp_at' P p s \<rbrakk> \<Longrightarrow> (\<exists>ko. P ko \<and> state_refs_of' s p = refs_of' ko)"
  by (fastforce simp: ko_wp_at'_def state_refs_of'_def)

lemma sym_refs_ko_wp_atD:
  "\<lbrakk> ko_wp_at' P p s; sym_refs (state_refs_of' s) \<rbrakk>
      \<Longrightarrow> (\<exists>ko. P ko \<and> state_refs_of' s p = refs_of' ko
                    \<and> (\<forall>(x, tp) \<in> refs_of' ko. (p, symreftype tp) \<in> state_refs_of' s x))"
  apply (clarsimp dest!: ko_wp_at_state_refs_ofD)
  apply (rule exI, erule conjI)
  apply (drule sym)
  apply clarsimp
  apply (erule(1) sym_refsD)
  done

lemma zobj_refs_capRange:
  "capAligned c \<Longrightarrow> zobj_refs' c \<subseteq> capRange c"
  by (cases c, simp_all add: capRange_def capAligned_def is_aligned_no_overflow)
end

locale delete_locale =
  fixes s' and base and bits and ptr and idx and d
  assumes cap: "cte_wp_at' (\<lambda>cte. cteCap cte = UntypedCap d base bits idx) ptr s'"
  and  nodesc: "descendants_range' (UntypedCap d base bits idx) ptr (ctes_of s')"
  and    invs: "invs' s'"
  and  ct_act: "ct_active' s'"
  and sa_simp: "sch_act_simple s'"
  and      al: "is_aligned base bits"
  and    safe: "deletionIsSafe base bits s'"

context delete_locale begin interpretation Arch . (*FIXME: arch_split*)

lemma valid_objs: "valid_objs' s'"
  and        pa: "pspace_aligned' s'"
  and        pc: "pspace_canonical' s'"
  and       pkm: "pspace_in_kernel_mappings' s'"
  and        pd: "pspace_distinct' s'"
  and       vbm: "valid_bitmaps s'"
  and sym_sched: "sym_heap_sched_pointers s'"
  and       vsp: "valid_sched_pointers s'"
  and  sym_refs: "sym_refs (state_refs_of' s')"
  and    iflive: "if_live_then_nonz_cap' s'"
  and  ifunsafe: "if_unsafe_then_cap' s'"
  and     dlist: "valid_dlist (ctes_of s')"
  and      no_0: "no_0 (ctes_of s')"
  and   chain_0: "mdb_chain_0 (ctes_of s')"
  and    badges: "valid_badges (ctes_of s')"
  and contained: "caps_contained' (ctes_of s')"
  and   chunked: "mdb_chunked (ctes_of s')"
  and      umdb: "untyped_mdb' (ctes_of s')"
  and      uinc: "untyped_inc' (ctes_of s')"
  and  nullcaps: "valid_nullcaps (ctes_of s')"
  and    ut_rev: "ut_revocable' (ctes_of s')"
  and    dist_z: "distinct_zombies (ctes_of s')"
  and  irq_ctrl: "irq_control (ctes_of s')"
  and ioport_ctrl: "ioport_control (ctes_of s')"
  and    clinks: "class_links (ctes_of s')"
  and  rep_r_fb: "reply_masters_rvk_fb (ctes_of s')"
  and      idle: "valid_idle' s'"
  and      refs: "valid_global_refs' s'"
  and      arch: "valid_arch_state' s'"
  and      virq: "valid_irq_node' (irq_node' s') s'"
  and     virqh: "valid_irq_handlers' s'"
  and  vioports: "valid_ioports' s'"
  and     virqs: "valid_irq_states' s'"
  and no_0_objs: "no_0_obj' s'"
  and  ctnotinQ: "ct_not_inQ s'"
  and irqs_masked: "irqs_masked' s'"
  and      ctcd: "ct_idle_or_in_cur_domain' s'"
  and       cdm: "ksCurDomain s' \<le> maxDomain"
  and       vds: "valid_dom_schedule' s'"
  using invs
  by (auto simp: invs'_def valid_state'_def valid_pspace'_def valid_mdb'_def valid_mdb_ctes_def)

abbreviation
  "base_bits \<equiv> {base .. base + (2 ^ bits - 1)}"

abbreviation pspace' :: pspace where
  "pspace' \<equiv> \<lambda>x. if base \<le> x \<and> x \<le> base + (2 ^ bits - 1) then None else ksPSpace s' x"

abbreviation state' :: kernel_state where
  "state' \<equiv> (s' \<lparr> ksPSpace := pspace' \<rparr>)"

lemma ko_wp_at'[simp]:
  "\<And>P p. (ko_wp_at' P p state') = (ko_wp_at' P p s' \<and> p \<notin> base_bits)"
  by (fastforce simp add: ko_wp_at_delete'[OF pd])

lemma obj_at'[simp]:
  "\<And>P p. (obj_at' P p state') = (obj_at' P p s' \<and> p \<notin> base_bits)"
  by (fastforce simp add: obj_at'_real_def)

lemma typ_at'[simp]:
  "typ_at' P p state' = (typ_at' P p s' \<and> p \<notin> base_bits)"
  by (simp add: typ_at'_def)

lemma valid_untyped[simp]:
  "s' \<turnstile>' UntypedCap d base bits idx"
  using cte_wp_at_valid_objs_valid_cap' [OF cap valid_objs]
  by clarsimp

lemma cte_wp_at'[simp]:
  "\<And>P p. (cte_wp_at' P p state') = (cte_wp_at' P p s' \<and> p \<notin> base_bits)"
  by (fastforce simp:cte_wp_at_delete'[where idx = idx,OF valid_untyped pd ])

(* the bits of caps they need for validity argument are within their capRanges *)
lemma valid_cap_ctes_pre:
    "\<And>c. s' \<turnstile>' c \<Longrightarrow> case c of CNodeCap ref bits g gs
                      \<Rightarrow> \<forall>x. ref + (x && mask bits) * 2^cteSizeBits \<in> capRange c
                    | Zombie ref (ZombieCNode bits) n
                      \<Rightarrow> \<forall>x. ref + (x && mask bits) * 2^cteSizeBits \<in> capRange c
                    | ArchObjectCap (PageTableCap ref data)
                      \<comment> \<open>FIXME: word_size_bits should be pteSizeBits.\<close>
                      \<Rightarrow> \<forall>x < 2^ptTranslationBits. ref + x * 2^word_size_bits \<in> capRange c
                    | ArchObjectCap (PageDirectoryCap ref data)
                      \<comment> \<open>FIXME: word_size_bits should be pdeSizeBits.\<close>
                      \<Rightarrow> \<forall>x < 2^ptTranslationBits. ref + x * 2^word_size_bits \<in> capRange c
                    | ArchObjectCap (PDPointerTableCap ref data)
                      \<comment> \<open>FIXME: word_size_bits should be pdpteSizeBits.\<close>
                      \<Rightarrow> \<forall>x < 2^ptTranslationBits. ref + x * 2^word_size_bits \<in> capRange c
                    | ArchObjectCap (PML4Cap ref data)
                      \<comment> \<open>FIXME: word_size_bits should be pml4eSizeBits.\<close>
                      \<Rightarrow> \<forall>x < 2^ptTranslationBits. ref + x * 2^word_size_bits \<in> capRange c
                    | _ \<Rightarrow> True"
  apply (drule valid_capAligned)
  apply (simp split: capability.split zombie_type.split arch_capability.split, safe)
  using pre_helper[where a=cteSizeBits] (* cte_level_bits *)
       apply (clarsimp simp add: capRange_def capAligned_def objBits_simps field_simps)
      apply (clarsimp simp add: capRange_def capAligned_def
                      simp del: atLeastAtMost_iff capBits.simps)
      apply (rule pre_helper2, simp_all add: bit_simps)[1]
     apply (clarsimp simp add: capRange_def capAligned_def
                     simp del: atLeastAtMost_iff capBits.simps)
     apply (rule pre_helper2, simp_all add: bit_simps)[1]
    apply (clarsimp simp add: capRange_def capAligned_def
                    simp del: atLeastAtMost_iff capBits.simps)
    apply (rule pre_helper2, simp_all add: bit_simps)[1]
   apply (clarsimp simp add: capRange_def capAligned_def
                   simp del: atLeastAtMost_iff capBits.simps)
   apply (rule pre_helper2, simp_all add: bit_simps)[1]
  using pre_helper[where a=cteSizeBits]
  apply (clarsimp simp add: capRange_def capAligned_def objBits_simps field_simps)
  done

lemma replycap_argument:
  "\<And>p t m r. cte_wp_at' (\<lambda>cte. cteCap cte = ReplyCap t m r) p s'
   \<Longrightarrow> t \<notin> {base .. base + (2 ^ bits - 1)}"
  using safe
  by (fastforce simp add: deletionIsSafe_def cte_wp_at_ctes_of field_simps)

lemma valid_cap':
    "\<And>p c. \<lbrakk> s' \<turnstile>' c; cte_wp_at' (\<lambda>cte. cteCap cte = c) p s';
             capRange c \<inter> {base .. base + (2 ^ bits - 1)} = {} \<rbrakk> \<Longrightarrow> state' \<turnstile>' c"
  apply (subgoal_tac "capClass c = PhysicalClass \<longrightarrow> capUntypedPtr c \<in> capRange c")
   apply (subgoal_tac "capClass c = PhysicalClass \<longrightarrow>
                        capUntypedPtr c \<notin> {base .. base + (2 ^ bits - 1)}")
    apply (frule valid_cap_ctes_pre)
    apply (case_tac c, simp_all add: valid_cap'_def replycap_argument
                                del: atLeastAtMost_iff
                              split: zombie_type.split_asm)
       apply (simp add: field_simps del: atLeastAtMost_iff)
       apply blast
      apply (rename_tac arch_capability)
      apply (case_tac arch_capability,
             simp_all add: X64_H.capUntypedPtr_def
                           page_table_at'_def page_directory_at'_def
                           pd_pointer_table_at'_def page_map_l4_at'_def
                           shiftl_t2n
                      del: atLeastAtMost_iff)[1]
          apply (rename_tac word vmrights mt vmpage_size dev option)
          apply (subgoal_tac "\<forall>p < 2 ^ (pageBitsForSize vmpage_size - pageBits).
                               word + p * 2 ^ pageBits \<in> capRange c")
           apply blast
          apply (clarsimp simp: capRange_def capAligned_def)
          apply (frule word_less_power_trans2,
                  rule pbfs_atleast_pageBits, simp add: word_bits_def)
          apply (rule context_conjI)
           apply (erule(1) is_aligned_no_wrap')
          apply (simp only: add_diff_eq[symmetric])
          apply (rule word_plus_mono_right)
           apply simp
          apply (erule is_aligned_no_overflow')
         apply (simp add: field_simps bit_simps del: atLeastAtMost_iff)
         apply blast
        apply (simp add: field_simps bit_simps del: atLeastAtMost_iff)
        apply blast
       apply (simp add: field_simps bit_simps del: atLeastAtMost_iff)
       apply blast
      apply (simp add: field_simps bit_simps del: atLeastAtMost_iff)
      apply blast
     apply (simp add: valid_untyped'_def)
    apply (simp add: field_simps bit_simps word_size_def del: atLeastAtMost_iff)
    apply blast
   apply blast
  apply (clarsimp simp: capAligned_capUntypedPtr)
  done

lemma objRefs_notrange:
  assumes asms: "ctes_of s' p = Some c" "\<not> isUntypedCap (cteCap c)"
  shows "capRange (cteCap c) \<inter> base_bits = {}"
proof -
  from cap obtain node
    where ctes_of: "ctes_of s' ptr = Some (CTE (UntypedCap d base bits idx) node)"
    apply (clarsimp simp: cte_wp_at_ctes_of)
    apply (case_tac cte, simp)
    done

  show ?thesis using asms cap
    apply -
    apply (rule ccontr)
    apply (drule untyped_mdbD' [OF ctes_of _ _ _ _ umdb])
       apply (simp add: isUntypedCap_def)
      apply (simp add: field_simps)
     apply assumption
    using nodesc
    apply (simp add:descendants_range'_def2)
    apply (drule(1) descendants_range_inD')
     apply (simp add:asms)
    apply (simp add:p_assoc_help)
    done
qed

lemma ctes_of_valid [elim!]:
  "ctes_of s' p = Some cte \<Longrightarrow> s' \<turnstile>' cteCap cte"
  by (case_tac cte, simp add: ctes_of_valid_cap' [OF _ valid_objs])

lemma valid_cap2:
  "\<lbrakk> cte_wp_at' (\<lambda>cte. cteCap cte = c) p s' \<rbrakk> \<Longrightarrow> state' \<turnstile>' c"
  apply (case_tac "isUntypedCap c")
   apply (drule cte_wp_at_valid_objs_valid_cap' [OF _ valid_objs])
   apply (clarsimp simp: valid_cap'_def isCap_simps valid_untyped'_def)
  apply (rule valid_cap'[rotated], assumption)
   apply (clarsimp simp: cte_wp_at_ctes_of dest!: objRefs_notrange)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  done

lemma ex_nonz_cap_notRange:
  "ex_nonz_cap_to' p s' \<Longrightarrow> p \<notin> base_bits"
  apply (clarsimp simp: ex_nonz_cap_to'_def cte_wp_at_ctes_of)
  apply (case_tac "isUntypedCap (cteCap cte)")
   apply (clarsimp simp: isCap_simps)
  apply (drule subsetD[OF zobj_refs_capRange, rotated])
   apply (rule valid_capAligned, erule ctes_of_valid)
  apply (drule(1) objRefs_notrange)
  apply (drule_tac a=p in equals0D)
  apply simp
  done

lemma live_notRange:
  "\<lbrakk> ko_wp_at' P p s'; \<And>ko. P ko \<Longrightarrow> live' ko \<rbrakk> \<Longrightarrow> p \<notin> base_bits"
  apply (drule if_live_then_nonz_capE' [OF iflive ko_wp_at'_weakenE])
   apply simp
  apply (erule ex_nonz_cap_notRange)
  done

lemma deletionIsSafe_delete_locale_holds:
  "deletionIsSafe_delete_locale base bits s'"
  by (fastforce dest: live_notRange simp: deletionIsSafe_delete_locale_def field_simps)

lemma refs_notRange:
  "(x, tp) \<in> state_refs_of' s' y \<Longrightarrow> y \<notin> base_bits"
  apply (drule state_refs_of'_elemD)
  apply (erule live_notRange)
  apply (rule refs_of_live')
  apply clarsimp
  done
end

context begin interpretation Arch . (*FIXME: arch_split*)

(* FIXME: generalizes lemma SubMonadLib.corres_submonad *)
(* FIXME: generalizes lemma SubMonad_R.corres_machine_op *)
(* FIXME: move *)
lemma corres_machine_op:
  assumes P: "corres_underlying Id False True r P Q x x'"
  shows      "corres r (P \<circ> machine_state) (Q \<circ> ksMachineState)
                       (do_machine_op x) (doMachineOp x')"
  apply (rule corres_submonad3
              [OF submonad_do_machine_op submonad_doMachineOp _ _ _ _ P])
   apply (simp_all add: state_relation_def swp_def)
  done

lemma ekheap_relation_detype:
  "ekheap_relation ekh kh \<Longrightarrow>
   ekheap_relation (\<lambda>x. if P x then None else (ekh x)) (\<lambda>x. if P x then None else (kh x))"
  by (fastforce simp add: ekheap_relation_def split: if_split_asm)

lemma cap_table_at_gsCNodes_eq:
  "(s, s') \<in> state_relation
    \<Longrightarrow> (gsCNodes s' ptr = Some bits) = cap_table_at bits ptr s"
  apply (clarsimp simp: state_relation_def ghost_relation_def
                        obj_at_def is_cap_table)
  apply (drule_tac x = ptr in spec)+
  apply (drule_tac x = bits in spec)+
  apply fastforce
  done

lemma cNodeNoPartialOverlap:
  "corres dc (\<lambda>s. \<exists>cref. cte_wp_at ((=) (cap.UntypedCap d base magnitude idx)) cref s
                     \<and> valid_objs s \<and> pspace_aligned s)
     \<top>
    (return x) (stateAssert (\<lambda>s. \<not> cNodePartialOverlap (gsCNodes s)
       (\<lambda>x. base \<le> x \<and> x \<le> base + 2 ^ magnitude - 1)) [])"
  apply (simp add: stateAssert_def assert_def)
  apply (rule corres_symb_exec_r[OF _ get_sp])
    apply (rule corres_req[rotated], subst if_P, assumption)
     apply simp
    apply (clarsimp simp: cNodePartialOverlap_def)
    apply (drule(1) cte_wp_valid_cap)
    apply (clarsimp simp: valid_cap_def valid_untyped_def cap_table_at_gsCNodes_eq
                          obj_at_def is_cap_table)
    apply (frule(1) pspace_alignedD)
    apply simp
    apply (elim allE, drule(1) mp, simp add: obj_range_def valid_obj_def cap_aligned_def)
    apply (erule is_aligned_get_word_bits[where 'a=machine_word_len, folded word_bits_def])
     apply (clarsimp simp: is_aligned_no_overflow)
     apply (blast intro: order_trans)
    apply (simp add: is_aligned_no_overflow power_overflow word_bits_def)
   apply wp+
  done

declare wrap_ext_det_ext_ext_def[simp]

lemma sym_refs_hyp_refs_triv[simp]: "sym_refs (state_hyp_refs_of s)"
  apply (clarsimp simp: state_hyp_refs_of_def sym_refs_def)
  by (case_tac "kheap s x"; simp)

crunches doMachineOp
  for deletionIsSafe_delete_locale[wp]: "deletionIsSafe_delete_locale base magnitude"
  (simp: deletionIsSafe_delete_locale_def)

lemma detype_tcbSchedNexts_of:
  "\<lbrakk>pspace_aligned' s'; pspace_distinct' s'; \<forall>p. p \<in> S \<longrightarrow> \<not> ko_wp_at' live' p s'\<rbrakk>
   \<Longrightarrow> ((\<lambda>x. if x \<in> S then None else ksPSpace s' x) |> tcb_of' |> tcbSchedNext)
       = tcbSchedNexts_of s'"
  using pspace_alignedD' pspace_distinctD'
  supply projectKOs[simp]
  apply (clarsimp simp: opt_map_def)
  apply (rule ext)
  apply (rename_tac s)
  apply (clarsimp simp: ko_wp_at'_def split: option.splits)
  apply (drule_tac x=s in spec)
  apply force
  done

lemma detype_tcbSchedPrevs_of:
  "\<lbrakk>pspace_aligned' s'; pspace_distinct' s'; \<forall>p. p \<in> S \<longrightarrow> \<not> ko_wp_at' live' p s'\<rbrakk>
   \<Longrightarrow> ((\<lambda>x. if x \<in> S then None else ksPSpace s' x) |> tcb_of' |> tcbSchedPrev)
       = tcbSchedPrevs_of s'"
  using pspace_alignedD' pspace_distinctD'
  supply projectKOs[simp]
  apply (clarsimp simp: opt_map_def)
  apply (rule ext)
  apply (rename_tac s)
  apply (clarsimp simp: ko_wp_at'_def split: option.splits)
  apply (drule_tac x=s in spec)
  apply force
  done

lemma detype_inQ:
  "\<lbrakk>pspace_aligned' s'; pspace_distinct' s'; \<forall>p. p \<in> S \<longrightarrow> \<not> ko_wp_at' live' p s'\<rbrakk>
   \<Longrightarrow> \<forall>d p. (inQ d p |< ((\<lambda>x. if x \<in> S then None else ksPSpace s' x) |> tcb_of'))
             = (inQ d p |< tcbs_of' s')"
  using pspace_alignedD' pspace_distinctD'
  supply projectKOs[simp]
  apply (clarsimp simp: opt_map_def)
  apply (rule ext)
  apply (rename_tac s)
  apply (clarsimp simp: inQ_def opt_pred_def ko_wp_at'_def split: option.splits)
  apply (drule_tac x=s in spec)
  apply force
  done

lemma detype_ready_queues_relation:
  "\<lbrakk>pspace_aligned' s'; pspace_distinct' s';
    \<forall>p. p \<in> {lower..upper} \<longrightarrow> \<not> ko_wp_at' live' p s';
    ready_queues_relation s s'; upper = upper'\<rbrakk>
   \<Longrightarrow> ready_queues_relation_2
        (ready_queues (detype {lower..upper'} s))
        (ksReadyQueues s')
        ((\<lambda>x. if lower \<le> x \<and> x \<le> upper then None
              else ksPSpace s' x) |>
         tcb_of' |>
         tcbSchedNext)
        ((\<lambda>x. if lower \<le> x \<and> x \<le> upper then None
              else ksPSpace s' x) |>
         tcb_of' |>
         tcbSchedPrev)
        (\<lambda>d p. inQ d p |< ((\<lambda>x. if lower \<le> x \<and> x \<le> upper then None else ksPSpace s' x) |> tcb_of'))"
  apply (clarsimp simp: detype_ext_def ready_queues_relation_def Let_def)
  apply (frule (1) detype_tcbSchedNexts_of[where S="{lower..upper}"]; simp)
  apply (frule (1) detype_tcbSchedPrevs_of[where S="{lower..upper}"]; simp)
  apply (frule (1) detype_inQ[where S="{lower..upper}"]; simp)
  apply (fastforce simp add: detype_def detype_ext_def)
  done

lemma deleteObjects_corres:
  "is_aligned base magnitude \<Longrightarrow> magnitude \<ge> 3 \<Longrightarrow>
   corres dc
      (\<lambda>s. einvs s
           \<and> s \<turnstile> (cap.UntypedCap d base magnitude idx)
           \<and> (\<exists>cref. cte_wp_at ((=) (cap.UntypedCap d base magnitude idx)) cref s
                     \<and> descendants_range (cap.UntypedCap d base magnitude idx) cref s)
           \<and> untyped_children_in_mdb s \<and> if_unsafe_then_cap s
           \<and> valid_mdb s \<and> valid_global_refs s \<and> ct_active s
           \<and> schact_is_rct s)
      (\<lambda>s'. invs' s'
           \<and> cte_wp_at' (\<lambda>cte. cteCap cte = UntypedCap d base magnitude idx) ptr s'
           \<and> descendants_range' (UntypedCap d base magnitude idx) ptr (ctes_of s')
           \<and> ct_active' s'
           \<and> s' \<turnstile>' (UntypedCap d base magnitude idx))
      (delete_objects base magnitude) (deleteObjects base magnitude)"
  apply (simp add: deleteObjects_def2)
  apply (rule corres_stateAssert_implied[where P'=\<top>, simplified])
   prefer 2
   apply clarsimp
   apply (rule_tac cap="cap.UntypedCap d base magnitude idx" and ptr="(a,b)" and s=s
                in detype_locale'.deletionIsSafe,
          simp_all add: detype_locale'_def detype_locale_def invs_valid_pspace)[1]
   apply (simp add: valid_cap_simps)
  apply (rule corres_stateAssert_add_assertion[rotated])
   apply (rule_tac ptr=ptr and idx=idx and d=d in delete_locale.deletionIsSafe_delete_locale_holds)
   apply (clarsimp simp: delete_locale_def)
   apply (intro conjI)
    apply (fastforce simp: sch_act_simple_def schact_is_rct_def state_relation_def)
   apply (rule_tac cap="cap.UntypedCap d base magnitude idx" and ptr="(a,b)" and s=s
                in detype_locale'.deletionIsSafe,
          simp_all add: detype_locale'_def detype_locale_def invs_valid_pspace)[1]
   apply (simp add: valid_cap_simps)
  apply (simp add: bind_assoc[symmetric] ksASIDMapSafe_def)
  apply (simp add: delete_objects_def)
  apply (rule_tac Q="\<lambda>_ s. valid_objs s \<and> valid_list s \<and>
                           (\<exists>cref. cte_wp_at ((=) (cap.UntypedCap d base magnitude idx)) cref s \<and>
                                   descendants_range (cap.UntypedCap d base magnitude idx) cref s) \<and>
                           s \<turnstile> cap.UntypedCap d base magnitude idx \<and> pspace_aligned s \<and>
                           valid_mdb s \<and> pspace_distinct s \<and> if_live_then_nonz_cap s \<and>
                           zombies_final s \<and> sym_refs (state_refs_of s) \<and>
                           untyped_children_in_mdb s \<and> if_unsafe_then_cap s \<and>
                           valid_global_refs s" and
                  Q'="\<lambda>_ s. s \<turnstile>' capability.UntypedCap d base magnitude idx \<and>
                            valid_pspace' s \<and>
                            deletionIsSafe_delete_locale base magnitude s"
                  in corres_underlying_split)
     apply (rule corres_bind_return)
     apply (rule corres_guard_imp[where r=dc])
       apply (rule corres_split[OF _ cNodeNoPartialOverlap])
         apply (rule corres_machine_op[OF corres_Id], simp+)
         apply (rule no_fail_freeMemory, simp+)
        apply (wp hoare_vcg_ex_lift)+
      apply auto[1]
     apply (auto elim: is_aligned_weaken)[1]
    apply (rule corres_modify)
    apply (simp add: valid_pspace'_def)
    apply (rule state_relation_null_filterE, assumption,
           simp_all add: pspace_aligned'_cut pspace_distinct'_cut)[1]
            apply (simp add: detype_def, rule state.equality; simp add: detype_ext_def)
           apply (intro exI, fastforce)
          apply (rule ext, clarsimp simp add: null_filter_def)
          apply (rule sym, rule ccontr, clarsimp)
          apply (drule(4) cte_map_not_null_outside')
           apply (fastforce simp add: cte_wp_at_caps_of_state)
          apply simp
         apply (rule ext, clarsimp simp add: null_filter'_def
                            map_to_ctes_delete[simplified field_simps])
         apply (rule sym, rule ccontr, clarsimp)
         apply (frule(2) pspace_relation_cte_wp_atI
                         [OF state_relation_pspace_relation])
         apply (elim exE)
         apply (frule(4) cte_map_not_null_outside')
          apply (rule cte_wp_at_weakenE, erule conjunct1)
          apply (case_tac y, clarsimp)
          apply (clarsimp simp: valid_mdb'_def valid_mdb_ctes_def
                                valid_nullcaps_def)
         apply clarsimp
         apply (frule_tac cref="(aa, ba)" in cte_map_untyped_range,
                erule cte_wp_at_weakenE[OF _ TrueI], assumption+)
         apply simp
        apply (rule detype_pspace_relation[simplified],
               simp_all add: state_relation_pspace_relation valid_pspace_def)[1]
         apply (simp add: valid_cap'_def capAligned_def)
        apply (clarsimp simp: valid_cap_def, assumption)
       apply (fastforce simp add: detype_def detype_ext_def intro!: ekheap_relation_detype)
      apply (rule detype_ready_queues_relation; blast?)
       apply (clarsimp simp: deletionIsSafe_delete_locale_def)
      apply (frule state_relation_ready_queues_relation)
      apply (simp add: ready_queues_relation_def Let_def)
     apply (clarsimp simp: state_relation_def ghost_relation_of_heap
                           detype_def)
     apply (drule_tac t="gsUserPages s'" in sym)
     apply (drule_tac t="gsCNodes s'" in sym)
     apply (auto simp add: ups_of_heap_def cns_of_heap_def ext
                 split: option.splits kernel_object.splits)[1]
    apply (simp add: valid_mdb_def)
   apply (wp hoare_vcg_ex_lift hoare_vcg_ball_lift | wps |
          simp add: invs_def valid_state_def valid_pspace_def
                    descendants_range_def | wp (once) hoare_drop_imps)+
  apply fastforce
  done
end

context delete_locale begin interpretation Arch . (*FIXME: arch_split*)

lemma live_idle_untyped_range':
  "ko_wp_at' live' p s' \<or> p = idle_thread_ptr \<Longrightarrow> p \<notin> base_bits"
  apply (case_tac "ko_wp_at' live' p s'")
   apply (drule if_live_then_nonz_capE'[OF iflive ko_wp_at'_weakenE])
    apply simp
   apply (erule ex_nonz_cap_notRange)
  apply clarsimp
  apply (insert invs_valid_global'[OF invs] cap invs_valid_idle'[OF invs])
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (drule (1) valid_global_refsD')
  apply (clarsimp simp: valid_idle'_def)
  using atLeastAtMost_iff apply (simp add: p_assoc_help mask_eq_exp_minus_1)
  by fastforce

lemma untyped_range_live_idle':
  "p \<in> base_bits \<Longrightarrow> \<not> (ko_wp_at' live' p s' \<or> p = idle_thread_ptr)"
  using live_idle_untyped_range' by blast

lemma valid_obj':
  "\<lbrakk> valid_obj' obj s'; ko_wp_at' ((=) obj) p s'; sym_heap_sched_pointers s' \<rbrakk>
   \<Longrightarrow> valid_obj' obj state'"
  apply (case_tac obj, simp_all add: valid_obj'_def)
      apply (rename_tac endpoint)
      apply (case_tac endpoint, simp_all add: valid_ep'_def)[1]
       apply (clarsimp dest!: sym_refs_ko_wp_atD [OF _ sym_refs])
       apply (drule(1) bspec)+
       apply (clarsimp dest!: refs_notRange)
      apply (clarsimp dest!: sym_refs_ko_wp_atD [OF _ sym_refs])
      apply (drule(1) bspec)+
      apply (clarsimp dest!: refs_notRange)
     apply (rename_tac notification)
     apply (case_tac notification, simp_all add: valid_ntfn'_def valid_bound_tcb'_def)[1]
     apply (rename_tac ntfn bound)
     apply (case_tac ntfn, simp_all split:option.splits)[1]
        apply ((clarsimp dest!: sym_refs_ko_wp_atD [OF _ sym_refs] refs_notRange)+)[4]
      apply (drule(1) bspec)+
      apply (clarsimp dest!: refs_notRange)
     apply (clarsimp dest!: sym_refs_ko_wp_atD [OF _ sym_refs] refs_notRange)
    apply (frule sym_refs_ko_wp_atD [OF _ sym_refs])
    apply (clarsimp simp: valid_tcb'_def ko_wp_at'_def
                          objBits_simps)
    apply (rule conjI)
     apply (erule ballEI, clarsimp elim!: ranE)
     apply (rule_tac p="p + x" in valid_cap2)
     apply (erule(2) cte_wp_at_tcbI')
      apply fastforce
     apply simp
    apply (intro conjI)
       apply (rename_tac tcb)
       apply (case_tac "tcbState tcb"; clarsimp simp: valid_tcb_state'_def  dest!: refs_notRange)
      apply (rename_tac tcb)
      apply (case_tac "tcbState tcb";
             clarsimp simp: valid_tcb_state'_def valid_bound_ntfn'_def
                     dest!: refs_notRange split: option.splits)
     apply (clarsimp simp: none_top_bool_cases)
     apply (rename_tac prev)
     apply (cut_tac P=live' and p=prev in live_notRange; fastforce?)
     apply (fastforce dest: sym_heapD2[where p'=p]
                      simp: opt_map_def ko_wp_at'_def obj_at'_def projectKOs)
    apply (clarsimp simp: none_top_bool_cases)
    apply (rename_tac "next")
    apply (cut_tac P=live' and p="next" in live_notRange; fastforce?)
    apply (fastforce dest!: sym_heapD1[where p=p]
                     simp: opt_map_def ko_wp_at'_def obj_at'_def projectKOs)
   apply (clarsimp simp: valid_cte'_def)
   apply (rule_tac p=p in valid_cap2)
   apply (clarsimp simp: ko_wp_at'_def objBits_simps' cte_level_bits_def[symmetric])
   apply (erule(2) cte_wp_at_cteI')
   apply simp
  apply (rename_tac arch_kernel_object)
  apply (case_tac "arch_kernel_object", simp_all)
      apply (rename_tac asidpool)
      apply (case_tac asidpool, clarsimp simp: page_directory_at'_def)
     apply (rename_tac pte)
     apply (case_tac pte, simp_all add: valid_mapping'_def)
    apply (rename_tac pde)
    apply (case_tac pde, simp_all add: valid_mapping'_def)
   apply (rename_tac pdpte)
   apply (case_tac pdpte, simp_all add: valid_mapping'_def)
  apply (rename_tac pml4e)
  apply (case_tac pml4e, simp_all add: valid_mapping'_def)
  done

lemma tcbSchedNexts_of_pspace':
  "\<lbrakk>pspace_aligned' s'; pspace_distinct' s'; pspace_distinct' state'\<rbrakk>
   \<Longrightarrow> (pspace' |> tcb_of' |> tcbSchedNext) = tcbSchedNexts_of s'"
  supply projectKOs[simp]
  apply (rule ext)
  apply (rename_tac p)
  apply (case_tac "p \<in> base_bits")
   apply (frule untyped_range_live_idle')
   apply (clarsimp simp: opt_map_def)
   apply (case_tac "ksPSpace s' p"; clarsimp)
   apply (rename_tac obj)
   apply (case_tac "tcb_of' obj"; clarsimp)
   apply (clarsimp simp: ko_wp_at'_def obj_at'_def)
   apply (fastforce simp: pspace_alignedD' pspace_distinctD')
  apply (clarsimp simp: opt_map_def split: option.splits)
  done

lemma tcbSchedPrevs_of_pspace':
  "\<lbrakk>pspace_aligned' s'; pspace_distinct' s'; pspace_distinct' state'\<rbrakk>
   \<Longrightarrow> (pspace' |> tcb_of' |> tcbSchedPrev) = tcbSchedPrevs_of s'"
  supply projectKOs[simp]
  apply (rule ext)
  apply (rename_tac p)
  apply (case_tac "p \<in> base_bits")
   apply (frule untyped_range_live_idle')
   apply (clarsimp simp: opt_map_def)
   apply (case_tac "ksPSpace s' p"; clarsimp)
   apply (rename_tac obj)
   apply (case_tac "tcb_of' obj"; clarsimp)
   apply (clarsimp simp: ko_wp_at'_def obj_at'_def)
   apply (fastforce simp: pspace_alignedD' pspace_distinctD')
  apply (clarsimp simp: opt_map_def split: option.splits)
  done

lemma st_tcb:
  "\<And>P p. \<lbrakk> st_tcb_at' P p s'; \<not> P Inactive; \<not> P IdleThreadState \<rbrakk> \<Longrightarrow> st_tcb_at' P p state'"
  by (fastforce simp: pred_tcb_at'_def obj_at'_real_def projectKOs dest: live_notRange)

lemma irq_nodes_global:
    "\<forall>irq :: 8 word. irq_node' s + (ucast irq) * 32 \<in> global_refs' s" (*2^cte_level_bits *)
    by (simp add: global_refs'_def mult.commute mult.left_commute)

lemma global_refs:
  "global_refs' s' \<inter> base_bits = {}"
  using cap
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (drule valid_global_refsD' [OF _ refs])
  apply (fastforce simp add: field_simps)
  done

lemma global_refs2:
  "global_refs' s' \<subseteq> (- base_bits)"
  using global_refs by blast

lemma irq_nodes_range:
  "\<forall>irq :: 8 word. irq_node' s' + (ucast irq) * 32 \<notin> base_bits"
  using irq_nodes_global global_refs
  by blast

lemma cte_refs_notRange:
  assumes asms: "ctes_of s' p = Some c"
  shows "cte_refs' (cteCap c) (irq_node' s') \<inter> base_bits = {}"
proof -
  from cap obtain node
    where ctes_of: "ctes_of s' ptr = Some (CTE (UntypedCap d base bits idx) node)"
    apply (clarsimp simp: cte_wp_at_ctes_of)
    apply (case_tac cte, simp)
    done

  show ?thesis using asms
    apply -
    apply (rule ccontr)
    apply (clarsimp elim!: nonemptyE)
    apply (frule ctes_of_valid)
    apply (frule valid_capAligned)
    apply (case_tac "\<exists>irq. cteCap c = IRQHandlerCap irq")
     apply (insert irq_nodes_range)[1]
     apply clarsimp
    apply (frule subsetD [OF cte_refs_capRange])
      apply simp
     apply assumption
    apply (frule caps_containedD' [OF _ ctes_of _ _ contained])
      apply (clarsimp dest!: isCapDs)
     apply (rule_tac x=x in notemptyI)
     apply (simp add: field_simps)
    apply (simp add: add_diff_eq[symmetric])
    apply (drule objRefs_notrange)
     apply (clarsimp simp: isCap_simps)
    apply blast
    done
qed

lemma non_null_present:
  "cte_wp_at' (\<lambda>c. cteCap c \<noteq> NullCap) p s' \<Longrightarrow> p \<notin> base_bits"
  apply (drule (1) if_unsafe_then_capD' [OF _ ifunsafe])
  apply (clarsimp simp: ex_cte_cap_to'_def cte_wp_at_ctes_of
                  dest!: cte_refs_notRange simp del: atLeastAtMost_iff)
  apply blast
  done

lemma cte_cap:
  "ex_cte_cap_to' p s' \<Longrightarrow> ex_cte_cap_to' p state'"
  apply (clarsimp simp: ex_cte_cap_to'_def)
  apply (frule non_null_present [OF cte_wp_at_weakenE'])
   apply clarsimp
  apply fastforce
  done

lemma idle_notRange:
  "\<forall>cref. \<not> cte_wp_at' (\<lambda>c. ksIdleThread s' \<in> capRange (cteCap c)) cref s'
  \<Longrightarrow> ksIdleThread s' \<notin> base_bits"
  apply (insert cap)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (erule_tac x=ptr in allE, clarsimp simp: field_simps)
  done

abbreviation
  "ctes' \<equiv> map_to_ctes (\<lambda>x. if base \<le> x \<and> x \<le> base + (2 ^ bits - 1) then None else ksPSpace s' x)"

lemmas tree_to_ctes = map_to_ctes_delete [OF valid_untyped pd]

lemma map_to_ctesE[elim!]:
  "\<lbrakk> ctes' x = Some cte; \<lbrakk> ctes_of s' x = Some cte; x \<notin> base_bits \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (clarsimp simp: tree_to_ctes split: if_split_asm)

lemma not_nullMDBNode:
  "\<lbrakk> ctes_of s' x = Some cte; cteCap cte = NullCap; cteMDBNode cte = nullMDBNode \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using nullcaps
  apply (cases cte)
  apply (simp add: valid_nullcaps_def)
  done

lemma mdb_src: "\<lbrakk> ctes_of s' \<turnstile> x \<leadsto> y; y \<noteq> 0 \<rbrakk> \<Longrightarrow> x \<notin> base_bits"
  apply (rule non_null_present)
  apply (clarsimp simp: next_unfold' cte_wp_at_ctes_of)
  apply (erule(1) not_nullMDBNode)
  apply (simp add: nullMDBNode_def nullPointer_def)
  done

lemma mdb_dest: "\<lbrakk> ctes_of s' \<turnstile> x \<leadsto> y; y \<noteq> 0 \<rbrakk> \<Longrightarrow> y \<notin> base_bits"
  apply (case_tac "x = 0")
   apply (insert no_0, simp add: next_unfold')[1]
  apply (drule(1) vdlist_nextD0 [OF _ _ dlist])
  apply (rule non_null_present)
  apply (clarsimp simp: next_unfold' cte_wp_at_ctes_of mdb_prev_def)
  apply (erule(1) not_nullMDBNode)
  apply (simp add: nullMDBNode_def nullPointer_def)
  done

lemma trancl_next[elim]:
  "\<lbrakk> ctes_of s' \<turnstile> x \<leadsto>\<^sup>+ y; x \<notin> base_bits \<rbrakk> \<Longrightarrow> ctes' \<turnstile> x \<leadsto>\<^sup>+ y"
  apply (erule rev_mp, erule converse_trancl_induct)
   apply clarsimp
   apply (rule r_into_trancl)
   apply (simp add: next_unfold' tree_to_ctes)
  apply clarsimp
  apply (rule_tac b=z in trancl_into_trancl2)
   apply (simp add: next_unfold' tree_to_ctes)
  apply (case_tac "z = 0")
   apply (insert no_0)[1]
   apply (erule tranclE2)
    apply (simp add: next_unfold')
   apply (simp add: next_unfold')
  apply (drule(1) mdb_dest)
  apply (simp add: next_unfold')
  done

lemma mdb_parent_notrange:
  "ctes_of s' \<turnstile> x \<rightarrow> y \<Longrightarrow> x \<notin> base_bits \<and> y \<notin> base_bits"
  apply (erule subtree.induct)
   apply (frule(1) mdb_src, drule(1) mdb_dest, simp)
  apply (drule(1) mdb_dest, simp)
  done

lemma mdb_parent:
  "ctes_of s' \<turnstile> x \<rightarrow> y \<Longrightarrow> ctes' \<turnstile> x \<rightarrow> y"
  apply (erule subtree.induct)
   apply (frule(1) mdb_src, frule(1) mdb_dest)
   apply (rule subtree.direct_parent)
     apply (simp add: next_unfold' tree_to_ctes)
    apply assumption
   apply (simp add: parentOf_def tree_to_ctes)
  apply (frule(1) mdb_src, frule(1) mdb_dest)
  apply (erule subtree.trans_parent)
    apply (simp add: next_unfold' tree_to_ctes)
   apply assumption
   apply (frule mdb_parent_notrange)
  apply (simp add: parentOf_def tree_to_ctes)
  done

lemma trancl_next_rev:
  "ctes' \<turnstile> x \<leadsto>\<^sup>+ y \<Longrightarrow> ctes_of s' \<turnstile> x \<leadsto>\<^sup>+ y"
  apply (erule converse_trancl_induct)
   apply (rule r_into_trancl)
   apply (clarsimp simp: next_unfold')
  apply (rule_tac b=z in trancl_into_trancl2)
   apply (clarsimp simp: next_unfold')
  apply assumption
  done

lemma is_chunk[elim!]:
  "is_chunk (ctes_of s') cap x y \<Longrightarrow> is_chunk ctes' cap x y"
  apply (simp add: is_chunk_def)
  apply (erule allEI)
  apply (clarsimp dest!: trancl_next_rev)
  apply (drule rtranclD, erule disjE)
   apply (clarsimp simp: tree_to_ctes)
   apply (cut_tac p=y in non_null_present)
    apply (clarsimp simp: cte_wp_at_ctes_of)
   apply simp
   apply (clarsimp dest!: trancl_next_rev simp: trancl_into_rtrancl)
  apply (clarsimp simp: tree_to_ctes)
  apply (cut_tac p=p'' in non_null_present)
   apply (clarsimp simp add: cte_wp_at_ctes_of)
  apply simp
  done

end

lemma exists_disj:
  "((\<exists>a. P a \<and> Q a)\<or>(\<exists>a. P a \<and> Q' a))
   = (\<exists>a. P a \<and> (Q a \<or> Q' a))"
   by auto

lemma (in delete_locale) delete_invs':
  "invs' (ksMachineState_update
           (\<lambda>ms. underlying_memory_update
              (\<lambda>m x. if base \<le> x \<and> x \<le> base + (2 ^ bits - 1) then 0 else m x) ms)
           state')" (is "invs' (?state'')")
using vds
proof (simp add: invs'_def valid_state'_def valid_pspace'_def
                 valid_mdb'_def valid_mdb_ctes_def,
       safe)
  interpret Arch . (*FIXME: arch_split*)
  let ?s = state'
  let ?ran = base_bits

  show "pspace_aligned' ?s" using pa
    by (simp add: pspace_aligned'_def dom_def)

  show "pspace_canonical' ?s" using pc
    by (simp add: pspace_canonical'_def dom_def)

  show "pspace_in_kernel_mappings' ?s" using pkm
    by (simp add: pspace_in_kernel_mappings'_def dom_def)

  show pspace_distinct'_state': "pspace_distinct' ?s" using pd
    by (clarsimp simp add: pspace_distinct'_def ps_clear_def
                           dom_if_None Diff_Int_distrib)

  show "valid_objs' ?s" using valid_objs sym_sched
    apply (clarsimp simp: valid_objs'_def ran_def)
    apply (rule_tac p=a in valid_obj')
      apply fastforce
     apply (frule pspace_alignedD'[OF _ pa])
     apply (frule pspace_distinctD'[OF _ pd])
     apply (clarsimp simp: ko_wp_at'_def)
    apply fastforce
    done

  from sym_refs show "sym_refs (state_refs_of' ?s)"
    apply -
    apply (clarsimp simp: state_refs_ko_wp_at_eq
                   elim!: rsubst[where P=sym_refs])
    apply (rule ext)
    apply safe
    apply (simp add: refs_notRange[simplified] state_refs_ko_wp_at_eq)
    done

  show "if_live_then_nonz_cap' ?s" using iflive
    apply (clarsimp simp: if_live_then_nonz_cap'_def)
    apply (drule spec, drule(1) mp)
    apply (clarsimp simp: ex_nonz_cap_to'_def)
    apply (rule exI, rule conjI, assumption)
    apply (drule non_null_present [OF cte_wp_at_weakenE'])
     apply clarsimp
    apply simp
    done

  from ifunsafe show "if_unsafe_then_cap' ?s"
    by (clarsimp simp: if_unsafe_then_cap'_def
               intro!: cte_cap)

  from idle_notRange refs
  have "ksIdleThread s' \<notin> ?ran"
    apply (simp add: cte_wp_at_ctes_of valid_global_refs'_def valid_refs'_def)
    apply blast
    done
  with idle show "valid_idle' ?s"
    apply (clarsimp simp: valid_idle'_def pred_tcb_at'_def obj_at'_def projectKOs)
    apply (clarsimp simp add: ps_clear_def dom_if_None Diff_Int_distrib)
    done

  from tcb_at_invs' [OF invs] ct_act
  show "cur_tcb' ?s" unfolding cur_tcb'_def
    apply (clarsimp simp: cur_tcb'_def ct_in_state'_def)
    apply (drule st_tcb)
      apply simp
     apply simp
    apply (simp add: pred_tcb_at'_def)
    done

  let ?ctes' = ctes'

  from no_0 show no_0': "no_0 ?ctes'"
    by (simp add: no_0_def tree_to_ctes)

  from dlist show "valid_dlist ?ctes'"
    apply (simp only: valid_dlist_def3)
    apply (rule conjI)
     apply (drule conjunct1)
     apply (elim allEI)
     apply (clarsimp simp: mdb_prev_def next_unfold'
                           tree_to_ctes)
     apply (rule ccontr, clarsimp)
     apply (cut_tac p="mdbNext (cteMDBNode cte)" in non_null_present)
      apply (clarsimp simp: cte_wp_at_ctes_of)
      apply (erule(1) not_nullMDBNode)
      apply (simp add: nullMDBNode_def nullPointer_def no_0)
     apply simp
    apply (drule conjunct2)
    apply (elim allEI)
    apply (clarsimp simp: mdb_prev_def next_unfold'
                           tree_to_ctes)
    apply (rule ccontr, clarsimp)
    apply (cut_tac p="mdbPrev (cteMDBNode z)" in non_null_present)
     apply (clarsimp simp: cte_wp_at_ctes_of)
     apply (erule(1) not_nullMDBNode)
     apply (simp add: nullMDBNode_def nullPointer_def no_0)
    apply simp
    done

  from chain_0 show "mdb_chain_0 ?ctes'"
    by (fastforce simp: mdb_chain_0_def Ball_def)

  from umdb show "untyped_mdb' ?ctes'"
    apply (simp add: untyped_mdb'_def)
    apply (erule allEI)+
    apply (clarsimp simp: descendants_of'_def)
    apply (rule mdb_parent)
    apply (clarsimp simp: tree_to_ctes split: if_split_asm)
    done

  from badges show "valid_badges ?ctes'"
    by (simp add: valid_badges_def tree_to_ctes next_unfold')

  from contained show "caps_contained' ?ctes'"
    by (simp add: caps_contained'_def tree_to_ctes)

  from chunked show "mdb_chunked ?ctes'"
    apply (simp add: mdb_chunked_def)
    apply (elim allEI)
    apply clarsimp
    apply (intro conjI impI)
      apply (erule disjEI)
       apply fastforce
      apply fastforce
     apply (clarsimp dest!: trancl_next_rev)
    apply (clarsimp dest!: trancl_next_rev)
    done

  from uinc show "untyped_inc' ?ctes'"
    apply (simp add: untyped_inc'_def)
    apply (elim allEI)
    apply clarsimp
    apply (safe del: impCE, simp_all add: descendants_of'_def
                                          mdb_parent)
    done

  from nullcaps show "valid_nullcaps ?ctes'"
    by (clarsimp simp: valid_nullcaps_def)

  from ut_rev
  show "ut_revocable' ?ctes'"
    by (clarsimp simp: ut_revocable'_def)

  show "class_links ?ctes'" using clinks
    by (simp add: class_links_def tree_to_ctes mdb_next_unfold)

  show "valid_global_refs' ?s" using refs
    by (simp add: valid_global_refs'_def tree_to_ctes valid_cap_sizes'_def
                  global_refs'_def valid_refs'_def ball_ran_eq)

  show "valid_arch_state' ?s"
    using arch global_refs2
    apply (simp add: valid_arch_state'_def
                     global_refs'_def)
    apply (intro conjI)
      apply (simp add: valid_asid_table'_def)
     apply (simp add: page_map_l4_at'_def
                      table_refs'_def
                      subset_iff)
    apply (simp add: valid_global_pds'_def
                     subset_iff
                     page_directory_at'_def
                     table_refs'_def
                     page_map_l4_at'_def)
    subgoal by fastforce
    apply (simp add: valid_global_pdpts'_def
                     subset_iff
                     pd_pointer_table_at'_def
                     table_refs'_def
                     page_map_l4_at'_def)
    subgoal by fastforce
    apply (simp add: valid_global_pts'_def
                     subset_iff
                     page_table_at'_def
                     table_refs'_def
                     page_map_l4_at'_def)
    by fastforce

  show "valid_irq_node' (irq_node' s') ?s"
    using virq irq_nodes_range
    by (simp add: valid_irq_node'_def mult.commute mult.left_commute ucast_ucast_mask_8)

  show "valid_irq_handlers' ?s" using virqh
    apply (simp add: valid_irq_handlers'_def irq_issued'_def
                     cteCaps_of_def tree_to_ctes Ball_def)
    apply (erule allEI)
    apply (clarsimp simp: ran_def)
    done

  show "valid_ioports' ?s" using vioports
    apply (simp add: valid_ioports'_simps Ball_def cteCaps_of_def, clarsimp)
    apply (rule conjI, rule allEI, assumption, (auto simp: ran_def)[1])
    apply (erule allEI)
    apply (auto simp: ran_def)
    done

  from irq_ctrl
  show "irq_control ?ctes'"
    by (clarsimp simp: irq_control_def)

  from ioport_ctrl
  show "ioport_control ?ctes'"
    by (clarsimp simp: ioport_control_def)

  from dist_z
  show "distinct_zombies ?ctes'"
    apply (simp add: tree_to_ctes distinct_zombies_def
                     distinct_zombie_caps_def
                    split del: if_split)
    apply (erule allEI, erule allEI)
    apply clarsimp
    done

  show "reply_masters_rvk_fb ?ctes'"
    using rep_r_fb
    by (simp add: tree_to_ctes reply_masters_rvk_fb_def
                  ball_ran_eq)

  from virqs
  show "valid_irq_states' s'" .

  from no_0_objs
  show "no_0_obj' state'"
    by (simp add: no_0_obj'_def)

  from irqs_masked
  show "irqs_masked' state'"
    by (simp add: irqs_masked'_def)

  from sa_simp ct_act
  show "sch_act_wf (ksSchedulerAction s') state'"
    apply (simp add: sch_act_simple_def)
    apply (case_tac "ksSchedulerAction s'", simp_all add: ct_in_state'_def)
    apply (fastforce dest!: st_tcb elim!: pred_tcb'_weakenE)
    done

  from invs
  have "pspace_domain_valid s'" by (simp add: invs'_def valid_state'_def)
  thus "pspace_domain_valid state'"
    by (simp add: pspace_domain_valid_def)

  from invs
  have "valid_machine_state' s'" by (simp add: invs'_def valid_state'_def)
  thus "valid_machine_state' ?state''"
    apply (clarsimp simp: valid_machine_state'_def)
    apply (drule_tac x=p in spec)
    apply (simp add: pointerInUserData_def pointerInDeviceData_def typ_at'_def)
    apply (simp add: ko_wp_at'_def exists_disj)
    apply (elim exE conjE)
    apply (cut_tac ptr'=p in mask_in_range)
     apply fastforce
    using valid_untyped[simplified valid_cap'_def capability.simps]
    apply (simp add: valid_untyped'_def capAligned_def)
    apply (elim conjE)
    apply (drule_tac x="p && ~~ mask pageBits" in spec)
    apply (cut_tac x=p in is_aligned_neg_mask[OF le_refl])
    apply (clarsimp simp: mask_2pm1 ko_wp_at'_def obj_range'_def objBitsKO_def)
    apply (frule is_aligned_no_overflow'[of base bits])
    apply (frule is_aligned_no_overflow'[of _ pageBits])
    apply (frule (1) aligned_ranges_subset_or_disjoint
                     [where n=bits and n'=pageBits])
    apply (case_tac ko, simp_all add: objBits_simps)
    apply (auto simp add: x_power_minus_1)
    done

  from sa_simp ctnotinQ
  show "ct_not_inQ state'"
    apply (clarsimp simp: ct_not_inQ_def pred_tcb_at'_def)
    apply (drule obj_at'_and
                   [THEN iffD2, OF conjI,
                    OF ct_act [unfolded ct_in_state'_def pred_tcb_at'_def]])
    apply (clarsimp simp: obj_at'_real_def)
    apply (frule if_live_then_nonz_capE'[OF iflive, OF ko_wp_at'_weakenE])
     apply (clarsimp simp: projectKOs)
     apply (case_tac "tcbState obj")
            apply (clarsimp simp: projectKOs)+
    apply (clarsimp dest!: ex_nonz_cap_notRange)
    done

  from ctcd show "ct_idle_or_in_cur_domain' state'"
    apply (simp add: ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def)
    apply (intro impI)
    apply (elim disjE impE)
     apply simp+
    apply (intro impI)
    apply (rule disjI2)
    apply (drule obj_at'_and
                   [THEN iffD2, OF conjI,
                    OF ct_act [unfolded ct_in_state'_def st_tcb_at'_def]])
    apply (clarsimp simp: obj_at'_real_def)
    apply (frule if_live_then_nonz_capE'[OF iflive, OF ko_wp_at'_weakenE])
     apply (clarsimp simp: projectKOs)
     apply (case_tac "tcbState obj")
            apply (clarsimp simp: projectKOs)+
    apply (clarsimp dest!: ex_nonz_cap_notRange elim!: ko_wp_at'_weakenE)
    done

  from cdm show "ksCurDomain s' \<le> maxDomain" .

  from invs
  have urz: "untyped_ranges_zero' s'" by (simp add: invs'_def valid_state'_def)
  show "untyped_ranges_zero_inv (cteCaps_of state') (gsUntypedZeroRanges s')"
    apply (simp add: untyped_zero_ranges_cte_def
                     urz[unfolded untyped_zero_ranges_cte_def, rule_format, symmetric])
    apply (clarsimp simp: fun_eq_iff intro!: arg_cong[where f=Ex])
    apply safe
    apply (drule non_null_present[OF cte_wp_at_weakenE'])
     apply (clarsimp simp: untypedZeroRange_def)
    apply simp
    done

  from vbm
  show "valid_bitmaps state'"
    by (simp add: valid_bitmaps_def bitmapQ_defs)

  from sym_sched
  show "sym_heap (pspace' |> tcb_of' |> tcbSchedNext) (pspace' |> tcb_of' |> tcbSchedPrev)"
    using pa pd pspace_distinct'_state'
    by (fastforce simp: tcbSchedNexts_of_pspace' tcbSchedPrevs_of_pspace')

  from vsp show "valid_sched_pointers_2 (pspace' |> tcb_of' |> tcbSchedPrev)
                                        (pspace' |> tcb_of' |> tcbSchedNext)
                                        (tcbQueued |< (pspace' |> tcb_of'))"
    by (clarsimp simp: valid_sched_pointers_def opt_pred_def opt_map_def)

qed (clarsimp)

lemma (in delete_locale) delete_ko_wp_at':
  assumes    objs: "ko_wp_at' P p s' \<and> ex_nonz_cap_to' p s'"
  shows      "ko_wp_at' P p state'"
  using objs
  by (clarsimp simp: ko_wp_at'_def ps_clear_def dom_if_None Diff_Int_distrib
    dest!: ex_nonz_cap_notRange)

lemma (in delete_locale) null_filter':
  assumes  descs: "Q (null_filter' (ctes_of s'))"
  shows    "Q (null_filter' (ctes_of state'))"
  using descs ifunsafe
  apply (clarsimp elim!: rsubst[where P=Q])
  apply (rule ext)
  apply (clarsimp simp:null_filter'_def tree_to_ctes)
  apply (rule ccontr)
  apply (clarsimp)
  apply (cut_tac p = x in non_null_present)
   apply (simp add:cte_wp_at_ctes_of)
   apply (rule ccontr)
   apply simp
   apply (erule(1) not_nullMDBNode)
   apply (case_tac y,simp)
  apply simp
  done

lemma (in delete_locale) delete_ex_cte_cap_to':
  assumes  exc: "ex_cte_cap_to' p s'"
  shows    "ex_cte_cap_to' p state'"
  using exc
  by (clarsimp elim!: cte_cap)


lemma deleteObjects_null_filter:
  "\<lbrace>cte_wp_at' (\<lambda>c. cteCap c = UntypedCap d ptr bits idx) p
     and invs' and ct_active' and sch_act_simple
     and (\<lambda>s. descendants_range' (UntypedCap d ptr bits idx) p (ctes_of s))
     and (\<lambda>s. P (null_filter' (ctes_of s)))
     and K (bits < word_bits \<and> is_aligned ptr bits)\<rbrace>
  deleteObjects ptr bits
  \<lbrace>\<lambda>rv s.  P (null_filter' (ctes_of s))\<rbrace>"
  apply (simp add: deleteObjects_def3)
  apply (simp add: deleteObjects_def3 doMachineOp_def split_def)
  apply wp
  apply clarsimp
  apply (subgoal_tac "delete_locale s ptr bits p idx d")
   apply (drule_tac Q = P in delete_locale.null_filter')
    apply assumption
   apply (clarsimp simp:p_assoc_help)
   apply (simp add: eq_commute field_simps)
   apply (subgoal_tac "ksPSpace (s\<lparr>ksMachineState := snd ((), b)\<rparr>) =
                       ksPSpace s", simp only:, simp)
  apply (unfold_locales, simp_all)
  done

lemma deleteObjects_descendants:
  "\<lbrace>cte_wp_at' (\<lambda>c. cteCap c = UntypedCap d ptr bits idx) p
     and invs' and ct_active' and sch_act_simple
     and (\<lambda>s. descendants_range' (UntypedCap d ptr bits idx) p (ctes_of s))
     and (\<lambda>s. descendants_range_in' H p (ctes_of s))
     and K (bits < word_bits \<and> is_aligned ptr bits)\<rbrace>
  deleteObjects ptr bits
  \<lbrace>\<lambda>rv s.  descendants_range_in' H p (ctes_of s)\<rbrace>"
  apply (simp add:descendants_range_in'_def2)
  apply (wp deleteObjects_null_filter)
  apply fastforce
  done

lemma doMachineOp_modify:
  "doMachineOp (modify g) = modify (ksMachineState_update g)"
  apply (simp add: doMachineOp_def split_def select_f_returns)
  apply (rule ext)
  apply (simp add: simpler_gets_def simpler_modify_def bind_def)
  done
context begin interpretation Arch . (*FIXME: arch_split*)
lemma deleteObjects_invs':
  "\<lbrace>cte_wp_at' (\<lambda>c. cteCap c = UntypedCap d ptr bits idx) p
     and invs' and ct_active' and sch_act_simple
     and (\<lambda>s. descendants_range' (UntypedCap d ptr bits idx) p (ctes_of s))
     and K (bits < word_bits \<and> is_aligned ptr bits)\<rbrace>
     deleteObjects ptr bits
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
proof -
  show ?thesis
  apply (rule hoare_pre)
   apply (rule_tac G="is_aligned ptr bits \<and> 3 \<le> bits \<and> bits \<le> word_bits" in hoare_grab_asm)
   apply (clarsimp simp add: deleteObjects_def2)
   apply (simp add: freeMemory_def bind_assoc doMachineOp_bind ef_storeWord)
   apply (simp add: bind_assoc[where f="\<lambda>_. modify f" for f, symmetric])
   apply (simp add: mapM_x_storeWord_step[simplified word_size_bits_def]
                    doMachineOp_modify modify_modify)
   apply (simp add: bind_assoc intvl_range_conv'[where 'a=machine_word_len, folded word_bits_def] mask_def field_simps)
   apply (wp)
  apply (simp cong: if_cong)
  apply (subgoal_tac "is_aligned ptr bits \<and> 3 \<le> bits \<and> bits < word_bits",simp)
   apply clarsimp
   apply (frule(2) delete_locale.intro, simp_all)[1]
   apply (rule subst[rotated, where P=invs'], erule delete_locale.delete_invs')
   apply (simp add: field_simps)
  apply clarsimp
  apply (drule invs_valid_objs')
  apply (drule (1) cte_wp_at_valid_objs_valid_cap')
  apply (clarsimp simp add: valid_cap'_def capAligned_def untypedBits_defs)
  done
qed

lemma deleteObjects_st_tcb_at':
  "\<lbrace>cte_wp_at' (\<lambda>c. cteCap c = UntypedCap d ptr bits idx) p
     and invs' and ct_active' and sch_act_simple
     and (\<lambda>s. descendants_range' (UntypedCap d ptr bits idx) p (ctes_of s))
     and st_tcb_at' (P and (\<noteq>) Inactive and (\<noteq>) IdleThreadState) t
     and K (bits < word_bits \<and> is_aligned ptr bits)\<rbrace>
     deleteObjects ptr bits
   \<lbrace>\<lambda>rv. st_tcb_at' P t\<rbrace>"
  apply (simp add: deleteObjects_def3 doMachineOp_def split_def)
  apply wp
  apply clarsimp
  apply (subgoal_tac "delete_locale s ptr bits p idx d")
   apply (drule delete_locale.delete_ko_wp_at'
                [where p = t and
                       P="case_option False (P \<circ> tcbState) \<circ> projectKO_opt",
                 simplified eq_commute])
    apply (simp add: pred_tcb_at'_def obj_at'_real_def)
    apply (rule conjI)
     apply (fastforce elim: ko_wp_at'_weakenE)
    apply (erule if_live_then_nonz_capD' [rotated])
     apply (clarsimp simp: projectKOs)
    apply (clarsimp simp: invs'_def valid_state'_def)
   apply (clarsimp simp: pred_tcb_at'_def obj_at'_real_def
                  field_simps ko_wp_at'_def ps_clear_def
                  cong:if_cong
                  split: option.splits)
  apply (simp add: delete_locale_def)
  done

lemma deleteObjects_cap_to':
  "\<lbrace>cte_wp_at' (\<lambda>c. cteCap c = UntypedCap d ptr bits idx) p
     and invs' and ct_active' and sch_act_simple
     and (\<lambda>s. descendants_range' (UntypedCap d ptr bits idx) p (ctes_of s))
     and ex_cte_cap_to' p'
     and K (bits < word_bits \<and> is_aligned ptr bits)\<rbrace>
      deleteObjects ptr bits
   \<lbrace>\<lambda>rv. ex_cte_cap_to' p'\<rbrace>"
  apply (simp add: deleteObjects_def3 doMachineOp_def split_def)
  apply wp
  apply clarsimp
  apply (subgoal_tac "delete_locale s ptr bits p idx d")
   apply (drule delete_locale.delete_ex_cte_cap_to', assumption)
   apply (simp cong:if_cong)
   apply (subgoal_tac
     "s\<lparr>ksMachineState := b,
        ksPSpace := \<lambda>x. if ptr \<le> x \<and> x \<le> ptr + 2 ^ bits - 1 then None
                        else ksPSpace s x\<rparr> =
      ksMachineState_update (\<lambda>_. b)
      (s\<lparr>ksPSpace := \<lambda>x. if ptr \<le> x \<and> x \<le> ptr + 2 ^ bits - 1 then None
                         else ksPSpace s x\<rparr>)",erule ssubst)
    apply (simp add: field_simps ex_cte_cap_wp_to'_def cong:if_cong)
   apply simp
  apply (simp add: delete_locale_def)
  done

lemma valid_untyped_no_overlap:
  "\<lbrakk> valid_untyped' d ptr bits idx s; is_aligned ptr bits; valid_pspace' s \<rbrakk>
  \<Longrightarrow> pspace_no_overlap' ptr bits (s\<lparr>ksPSpace := ksPSpace s |` (- {ptr .. ptr + 2 ^ bits - 1})\<rparr>)"
  apply (clarsimp simp del: atLeastAtMost_iff
            simp: pspace_no_overlap'_def valid_cap'_def valid_untyped'_def is_aligned_neg_mask_eq)
  apply (drule_tac x=x in spec)
  apply (drule restrict_map_Some_iff[THEN iffD1])
  apply clarsimp
  apply (frule pspace_alignedD')
   apply (simp add: valid_pspace'_def)
  apply (frule pspace_distinctD')
   apply (simp add: valid_pspace'_def)
  apply (unfold ko_wp_at'_def obj_range'_def)
  apply (drule (1) aligned_ranges_subset_or_disjoint)
  apply (clarsimp simp del: Int_atLeastAtMost atLeastAtMost_iff atLeastatMost_subset_iff)
  apply (elim disjE)
    apply (subgoal_tac "ptr \<in> {x..x + 2 ^ objBitsKO ko - 1}")
     apply (clarsimp simp:p_assoc_help)
    apply (clarsimp simp:p_assoc_help)
   apply fastforce+
  done

lemma deleteObject_no_overlap[wp]:
  "\<lbrace>valid_cap' (UntypedCap d ptr bits idx) and valid_pspace'\<rbrace>
     deleteObjects ptr bits
   \<lbrace>\<lambda>rv s. pspace_no_overlap' ptr bits s\<rbrace>"
  apply (simp add: deleteObjects_def3 doMachineOp_def split_def)
  apply wp
  apply (clarsimp simp: valid_cap'_def cong:if_cong)
  apply (drule (2) valid_untyped_no_overlap)
  apply (subgoal_tac
     "s\<lparr>ksMachineState := b,
        ksPSpace := \<lambda>x. if ptr \<le> x \<and> x \<le> ptr + 2 ^ bits - 1 then None
                        else ksPSpace s x\<rparr> =
      ksMachineState_update (\<lambda>_. b)
      (s\<lparr>ksPSpace := ksPSpace s |` (- {ptr..ptr + 2 ^ bits - 1})\<rparr>)", simp)
  apply (case_tac s, simp)
  apply (rule ext)
  apply simp
  done

lemma deleteObjects_cte_wp_at':
  "\<lbrace>\<lambda>s. cte_wp_at' P p s \<and> p \<notin> {ptr .. ptr + 2 ^ bits - 1}
         \<and> s \<turnstile>' (UntypedCap d ptr bits idx) \<and> valid_pspace' s\<rbrace>
     deleteObjects ptr bits
   \<lbrace>\<lambda>rv s. cte_wp_at' P p s\<rbrace>"
  apply (simp add: deleteObjects_def3 doMachineOp_def split_def)
  apply wp
  apply (clarsimp simp: valid_pspace'_def cong:if_cong)
  apply (subgoal_tac
     "s\<lparr>ksMachineState := b,
        ksPSpace := \<lambda>x. if ptr \<le> x \<and> x \<le> ptr + 2 ^ bits - 1 then None
                        else ksPSpace s x\<rparr> =
      ksMachineState_update (\<lambda>_. b)
      (s\<lparr>ksPSpace := \<lambda>x. if ptr \<le> x \<and> x \<le> ptr + 2 ^ bits - 1 then None
                         else ksPSpace s x\<rparr>)", erule ssubst)
   apply (simp add: cte_wp_at_delete' x_power_minus_1)
  apply (case_tac s, simp)
  done

lemma deleteObjects_invs_derivatives:
  "\<lbrace>cte_wp_at' (\<lambda>c. cteCap c = UntypedCap d ptr bits idx) p
     and invs' and ct_active' and sch_act_simple
     and (\<lambda>s. descendants_range' (UntypedCap d ptr bits idx) p (ctes_of s))
     and K (bits < word_bits \<and> is_aligned ptr bits)\<rbrace>
     deleteObjects ptr bits
   \<lbrace>\<lambda>rv. valid_pspace'\<rbrace>"
  "\<lbrace>cte_wp_at' (\<lambda>c. cteCap c = UntypedCap d ptr bits idx) p
     and invs' and ct_active' and sch_act_simple
     and (\<lambda>s. descendants_range' (UntypedCap d ptr bits idx) p (ctes_of s))
     and K (bits < word_bits \<and> is_aligned ptr bits)\<rbrace>
     deleteObjects ptr bits
   \<lbrace>\<lambda>rv. valid_mdb'\<rbrace>"
  "\<lbrace>cte_wp_at' (\<lambda>c. cteCap c = UntypedCap d ptr bits idx) p
     and invs' and ct_active' and sch_act_simple
     and (\<lambda>s. descendants_range' (UntypedCap d ptr bits idx) p (ctes_of s))
     and K (bits < word_bits \<and> is_aligned ptr bits)\<rbrace>
     deleteObjects ptr bits
   \<lbrace>\<lambda>rv. pspace_aligned'\<rbrace>"
  "\<lbrace>cte_wp_at' (\<lambda>c. cteCap c = UntypedCap d ptr bits idx) p
     and invs' and ct_active' and sch_act_simple
     and (\<lambda>s. descendants_range' (UntypedCap d ptr bits idx) p (ctes_of s))
     and K (bits < word_bits \<and> is_aligned ptr bits)\<rbrace>
     deleteObjects ptr bits
   \<lbrace>\<lambda>rv. pspace_distinct'\<rbrace>"
  by (safe intro!: hoare_strengthen_post [OF deleteObjects_invs'])

lemma deleteObjects_nosch:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace>
   deleteObjects ptr sz
   \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  by (simp add: deleteObjects_def3 | wp hoare_drop_imp)+

(* Prooving the reordering here *)

lemma createObjects'_wp_subst:
  "\<lbrakk>\<lbrace>P\<rbrace>createObjects a b c d\<lbrace>\<lambda>r. Q\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace>createObjects' a b c d\<lbrace>\<lambda>r. Q\<rbrace>"
  apply (clarsimp simp:createObjects_def valid_def return_def bind_def)
  apply (drule_tac x = s in spec)
  apply (clarsimp simp:split_def)
  apply auto
  done

definition pspace_no_overlap_cell' where
  "pspace_no_overlap_cell' p \<equiv> \<lambda>kh.
     \<forall>x ko. kh x = Some ko \<longrightarrow> p \<notin> {x..x + (2 ^ objBitsKO ko - 1)}"

lemma pspace_no_overlap'_lift:
  assumes typ_at:"\<And>slot P Q. \<lbrace>\<lambda>s. P (typ_at' Q slot s)\<rbrace> f \<lbrace>\<lambda>r s. P (typ_at' Q slot s) \<rbrace>"
  assumes ps :"\<lbrace>Q\<rbrace> f \<lbrace>\<lambda>r s. pspace_aligned' s \<and> pspace_distinct' s \<rbrace>"
  shows "\<lbrace>Q and pspace_no_overlap' ptr sz \<rbrace> f \<lbrace>\<lambda>r. pspace_no_overlap' ptr sz\<rbrace>"
proof -
  note blah[simp del] = untyped_range.simps usable_untyped_range.simps atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex
  show ?thesis
    apply (clarsimp simp:valid_def pspace_no_overlap'_def)
    apply (drule_tac x = x in spec)
    apply (subgoal_tac "\<exists>ko'. ksPSpace s x = Some ko' \<and> koTypeOf ko = koTypeOf ko'")
     apply (clarsimp dest!:objBits_type)
    apply (rule ccontr)
    apply clarsimp
    apply (frule_tac slot1 = x and Q1 = "koTypeOf ko" and P1 = "\<lambda>a. \<not> a" in use_valid[OF _ typ_at])
    apply (clarsimp simp:typ_at'_def ko_wp_at'_def)+
    apply (frule(1) use_valid[OF _ ps])
    apply (clarsimp simp:valid_pspace'_def)
    apply (frule(1) pspace_alignedD')
    apply (drule(1) pspace_distinctD')
    apply simp
  done
qed

lemma setCTE_pspace_no_overlap':
  "\<lbrace>pspace_aligned' and pspace_distinct' and pspace_no_overlap' ptr sz\<rbrace>
   setCTE cte src
   \<lbrace>\<lambda>r. pspace_no_overlap' ptr sz\<rbrace>"
   apply (rule pspace_no_overlap'_lift; wp setCTE_typ_at')
   apply auto
   done

lemma getCTE_commute:
  assumes cte_at_modify:
   "\<And>Q. \<lbrace>\<lambda>s. P s \<and> cte_wp_at' Q dest s \<rbrace> f \<lbrace>\<lambda>a s. cte_wp_at' Q dest s\<rbrace>"
  shows "monad_commute (P and cte_at' dest) (getCTE dest) f"
  proof -
   have getsame: "\<And>x y s. (x,y)\<in> fst (getCTE dest s) \<Longrightarrow> y = s"
     apply (drule use_valid)
     prefer 3
     apply (simp|wp)+
     done
  show ?thesis
  apply (simp add:monad_commute_def bind_assoc getCTE_def split_def cte_at'_def)
  apply (clarsimp simp:bind_def split_def return_def)
  apply (rule conjI)
   apply (rule set_eqI)
   apply (rule iffI)
    apply clarsimp
    apply (rule bexI[rotated], assumption)
    apply (drule_tac Q1 ="(=) cte" in use_valid[OF _ cte_at_modify])
     apply (simp add:cte_wp_at'_def)
    apply (simp add:cte_wp_at'_def)
   apply clarsimp
   apply (rule conjI)
    apply (frule_tac Q1 = "(=) cte" in use_valid[OF _ cte_at_modify])
     apply (clarsimp simp:cte_wp_at'_def ko_wp_at'_def)
    apply (clarsimp simp:cte_wp_at'_def)
   apply (rule bexI[rotated], assumption)
   apply (metis fst_eqD getObject_cte_det snd_eqD)
  apply (cut_tac no_failD[OF no_fail_getCTE[unfolded getCTE_def]])
   prefer 2
   apply (simp add:cte_wp_at'_def)
    apply fastforce
  apply simp
  apply (rule iffI)
   apply clarsimp+
  apply (cut_tac s = b in no_failD[OF no_fail_getCTE[unfolded getCTE_def]])
   prefer 2
   apply fastforce
  apply (drule_tac Q1 = "(=) cte" in use_valid[OF _ cte_at_modify])
   apply (simp add:cte_wp_at'_def)
  apply (simp add:cte_wp_at_ctes_of)
  done
qed

definition "cte_check \<equiv> \<lambda>b src a next. (case b of
     KOTCB tcb \<Rightarrow> (is_aligned a (objBits tcb)
        \<and> (case next of None \<Rightarrow> True | Some z \<Rightarrow> 2^(objBits tcb) \<le> z - a)) \<and>
        (src - a = tcbVTableSlot << cteSizeBits
        \<or> src - a = tcbCTableSlot << cteSizeBits
        \<or> src - a = tcbReplySlot << cteSizeBits
        \<or> src - a = tcbCallerSlot << cteSizeBits
        \<or> src - a = tcbIPCBufferSlot << cteSizeBits )
     | KOCTE v1 \<Rightarrow> ( src = a \<and> (is_aligned a (objBits (makeObject::cte)))
        \<and> (case next of None \<Rightarrow> True | Some z \<Rightarrow> 2^(objBits (makeObject::cte)) \<le> z - a))
     | _ \<Rightarrow> False)"

definition locateCTE where
  "locateCTE src \<equiv>
  (do ps \<leftarrow> gets ksPSpace;
      (before, after) \<leftarrow> return (lookupAround2 src ps);
      (ptr,val) \<leftarrow> maybeToMonad before;
      assert (cte_check val src ptr after);
      return ptr
   od)"

definition cte_update where
  "cte_update  \<equiv> \<lambda>cte b src a. (case b of
     KOTCB tcb \<Rightarrow> if (src - a = tcbVTableSlot << cteSizeBits) then KOTCB (tcbVTable_update (\<lambda>_. cte) tcb)
        else if (src - a = tcbCTableSlot << cteSizeBits) then KOTCB (tcbCTable_update (\<lambda>_. cte) tcb)
        else if (src - a = tcbReplySlot << cteSizeBits) then KOTCB (tcbReply_update (\<lambda>_. cte) tcb)
        else if (src - a = tcbCallerSlot << cteSizeBits) then KOTCB (tcbCaller_update (\<lambda>_. cte) tcb)
        else if (src - a = tcbIPCBufferSlot << cteSizeBits) then KOTCB (tcbIPCBufferFrame_update (\<lambda>_. cte) tcb)
        else KOTCB tcb
     | KOCTE v1 \<Rightarrow> KOCTE cte
     | x \<Rightarrow> x)"

lemma simpler_updateObject_def:
  "updateObject (cte::cte) b src a next =
   (\<lambda>s. (if (cte_check b src a next) then ({(cte_update cte b src a,s)}, False)
         else fail s))"
  apply (rule ext)
  apply (clarsimp simp:ObjectInstances_H.updateObject_cte objBits_simps)
  apply (case_tac b)
   apply (simp_all add:cte_check_def typeError_def fail_def
          tcbIPCBufferSlot_def
          tcbCallerSlot_def tcbReplySlot_def
          tcbCTableSlot_def tcbVTableSlot_def)
   by (intro conjI impI;
        clarsimp simp:alignCheck_def unless_def when_def not_less[symmetric]
         alignError_def is_aligned_mask magnitudeCheck_def
         cte_update_def return_def tcbIPCBufferSlot_def
         tcbCallerSlot_def tcbReplySlot_def
         tcbCTableSlot_def tcbVTableSlot_def objBits_simps
         cteSizeBits_def split:option.splits;
          fastforce simp:return_def fail_def bind_def)+


lemma setCTE_def2:
 "(setCTE src cte) =
     (do  ptr \<leftarrow> locateCTE src;
          modify (ksPSpace_update (\<lambda>ps. ps(ptr \<mapsto> (cte_update cte (the (ps ptr)) src ptr )))) od)"
  apply (clarsimp simp:setCTE_def setObject_def split_def locateCTE_def bind_assoc)
  apply (rule ext)
  apply (rule_tac Q = "\<lambda>r s'. s'= x \<and> r = ksPSpace x " in monad_eq_split)
    apply (rule_tac Q = "\<lambda>ptr s'. s' = x \<and> snd ptr = the ((ksPSpace x) (fst ptr) ) " in monad_eq_split)
       apply (clarsimp simp:assert_def return_def fail_def bind_def simpler_modify_def)
       apply (clarsimp simp:simpler_updateObject_def fail_def)
      apply (wp|clarsimp simp:)+
    apply (simp add:lookupAround2_char1)
   apply wp
  apply simp
  done

lemma singleton_locateCTE:
  "a \<in> fst (locateCTE src s) = ({a} = fst (locateCTE src s))"
  apply (clarsimp simp:locateCTE_def assert_opt_def assert_def
    gets_def get_def bind_def return_def split_def)
  apply (clarsimp simp:return_def fail_def
    split:if_splits option.splits)+
  done

lemma locateCTE_inv:
  "\<lbrace>P\<rbrace>locateCTE s\<lbrace>\<lambda>r. P\<rbrace>"
  apply (simp add:locateCTE_def split_def)
  apply wp
  apply clarsimp
  done

lemma locateCTE_case:
  "\<lbrace>\<top>\<rbrace> locateCTE src
   \<lbrace>\<lambda>r s. \<exists>obj. ksPSpace s r = Some obj \<and>
          (case obj of KOTCB tcb \<Rightarrow> True | KOCTE v \<Rightarrow> True | _ \<Rightarrow> False)\<rbrace>"
  apply (clarsimp simp:locateCTE_def split_def | wp)+
  apply (clarsimp simp: lookupAround2_char1)
  apply (case_tac b)
   apply (simp_all add:cte_check_def)
  done

lemma cte_wp_at_top:
  "(cte_wp_at' \<top> src s)
  = (\<exists>a b. ( fst (lookupAround2 src (ksPSpace s)) = Some (a, b) \<and>
  cte_check b src a (snd (lookupAround2 src (ksPSpace s)))))"
  apply (simp add:cte_wp_at'_def getObject_def gets_def
    get_def bind_def return_def split_def
    assert_opt_def fail_def
    split:option.splits)
  apply (clarsimp simp:loadObject_cte)
  apply (case_tac b,simp_all)
       apply ((simp add: typeError_def fail_def cte_check_def
                  split: Structures_H.kernel_object.splits)+)[5]
    apply (simp add:loadObject_cte cte_check_def
      tcbIPCBufferSlot_def tcbCallerSlot_def
      tcbReplySlot_def tcbCTableSlot_def
      tcbVTableSlot_def objBits_simps cteSizeBits_def)
    apply (simp add:alignCheck_def bind_def
      alignError_def fail_def return_def objBits_simps
      magnitudeCheck_def in_monad is_aligned_mask
      when_def unless_def split:option.splits)
    apply (intro conjI impI allI,simp_all add:not_le)
   apply (clarsimp simp:cte_check_def)
   apply (simp add:alignCheck_def bind_def
     alignError_def fail_def return_def objBits_simps
     magnitudeCheck_def in_monad is_aligned_mask
     when_def unless_def split:option.splits)
    apply (intro conjI impI allI,simp_all add:not_le)
  apply (simp add:typeError_def fail_def
         cte_check_def split:Structures_H.kernel_object.splits)+
  done


lemma locateCTE_monad:
  assumes ko_wp_at: "\<And>Q dest.
  \<lbrace>\<lambda>s. P1 s \<and> ko_wp_at' (\<lambda>obj. Q (objBitsKO obj))  dest s \<rbrace> f
  \<lbrace>\<lambda>a s. ko_wp_at' (\<lambda>obj. Q (objBitsKO obj)) dest s\<rbrace>"
  assumes cte_wp_at: "\<And> dest.
  \<lbrace>\<lambda>s. P2 s \<and> cte_wp_at' \<top> dest s \<rbrace> f
  \<lbrace>\<lambda>a s. cte_wp_at' \<top> dest s\<rbrace>"
  assumes psp_distinct:
  "\<lbrace>\<lambda>s. P3 s \<rbrace> f \<lbrace>\<lambda>a s. pspace_distinct' s\<rbrace>"
  assumes psp_aligned:
  "\<lbrace>\<lambda>s. P4 s \<rbrace> f \<lbrace>\<lambda>a s. pspace_aligned' s\<rbrace>"
  shows
  "\<lbrakk>{(ptr, s)} = fst (locateCTE src s);
    (r, s') \<in> fst (f s);pspace_aligned' s;pspace_distinct' s;(P1 and P2 and P3 and P4) s\<rbrakk>
   \<Longrightarrow> {(ptr,s')} = fst (locateCTE src s')"
proof -

  have src_in_range:
   "\<And>obj src a m s'. \<lbrakk>cte_check obj src a m;ksPSpace s' a = Some obj\<rbrakk> \<Longrightarrow> src \<in> {a..a + 2 ^ objBitsKO obj - 1}"
  proof -
    fix obj src a m
    show "\<And>s'. \<lbrakk>cte_check obj src a m; ksPSpace s' a = Some obj\<rbrakk> \<Longrightarrow> src \<in> {a..a + 2 ^ objBitsKO obj - 1}"
      by (case_tac obj)
         (auto simp add: cte_check_def objBits_simps' diff_eq_eq
                         add.commute[where b=a]
                         word_plus_mono_right is_aligned_no_wrap'
                         tcbVTableSlot_def tcbCTableSlot_def tcbReplySlot_def
                         tcbCallerSlot_def tcbIPCBufferSlot_def )
  qed

  note blah[simp del] = usableUntypedRange.simps atLeastAtMost_iff
          atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex

  have step1:
    "\<lbrakk>(ptr, s) \<in> fst (locateCTE src s);
      (r, s') \<in> fst (f s); pspace_aligned' s; pspace_distinct' s; (P1 and P2 and P3 and P4) s\<rbrakk>
     \<Longrightarrow> (ptr,s') \<in> fst (locateCTE src s')"
  apply (frule use_valid[OF _ locateCTE_case])
   apply simp
  apply (clarsimp simp: locateCTE_def gets_def split_def
                        get_def bind_def return_def assert_opt_def fail_def assert_def
                  split: option.splits if_split_asm)
  apply (frule_tac dest1 = src in use_valid[OF _ cte_wp_at])
   apply simp
   apply (subst cte_wp_at_top)
   apply simp
  apply (clarsimp simp add:cte_wp_at_top)
  apply (clarsimp simp:lookupAround2_char1)
  apply (frule_tac dest1 = ptr and  Q1 = "\<lambda>x. x = objBitsKO b" in use_valid[OF _ ko_wp_at])
   apply (frule(1) pspace_alignedD')
   apply (frule(1) pspace_distinctD')
   apply (auto simp add:ko_wp_at'_def)[1]
  apply (clarsimp simp add:ko_wp_at'_def)
  apply (rule ccontr)
  apply (frule use_valid[OF _ psp_distinct])
   apply simp
  apply (frule use_valid[OF _ psp_aligned])
   apply simp
  apply (frule_tac x = a in pspace_distinctD')
   apply simp
  apply (frule_tac s = s' and a = ptr in rule_out_intv[rotated])
     apply simp+
  apply (frule_tac s = s' and b = ptr and a = a in rule_out_intv)
     apply simp+
  apply (thin_tac "\<forall>x. P x \<longrightarrow> Q x" for P Q)+
  apply (drule_tac p = ptr and p' = a in aligned_ranges_subset_or_disjoint)
   apply (erule(1) pspace_alignedD')
  apply (drule(1) src_in_range)+
  apply (drule base_member_set[OF pspace_alignedD'])
    apply simp
   apply (simp add:objBitsKO_bounded2[unfolded word_bits_def,simplified])
  apply (drule base_member_set[OF pspace_alignedD'])
    apply simp
   apply (simp add:objBitsKO_bounded2[unfolded word_bits_def,simplified])
  apply (clarsimp simp: field_simps)
  apply (elim disjE; fastforce simp: mask_def p_assoc_help)
  done
  assume
    "{(ptr, s)} = fst (locateCTE src s)"
    "(r, s') \<in> fst (f s)"
    "pspace_aligned' s"
    "pspace_distinct' s"
    "(P1 and P2 and P3 and P4) s"
  thus ?thesis
  using assms step1
  by (clarsimp simp:singleton_locateCTE)
qed

lemma empty_fail_locateCTE:
  "empty_fail (locateCTE src)"
  by (fastforce simp: locateCTE_def bind_assoc split_def)

lemma fail_empty_locateCTE:
  "snd (locateCTE src s) \<Longrightarrow> fst (locateCTE src s) = {}"
  by (auto simp: assert_def fail_def locateCTE_def bind_assoc return_def split_def gets_def
                 get_def bind_def assert_opt_def image_def
           split:option.splits if_split_asm)+

lemma locateCTE_commute:
  assumes nf: "no_fail P0 f" "no_fail P1 (locateCTE src)"
  and psp_distinct: "\<lbrace>\<lambda>s. P2 s \<rbrace> f \<lbrace>\<lambda>a s. pspace_distinct' s\<rbrace>"
  and psp_aligned: "\<lbrace>\<lambda>s. P3 s \<rbrace> f \<lbrace>\<lambda>a s. pspace_aligned' s\<rbrace>"
  assumes ko_wp_at: "\<And>Q dest.
  \<lbrace>\<lambda>s. (P0 and P1 and P2 and P3) s  \<and> ko_wp_at' (\<lambda>obj. Q (objBitsKO obj))  dest s \<rbrace> f
  \<lbrace>\<lambda>a s. ko_wp_at' (\<lambda>obj. Q (objBitsKO obj)) dest s\<rbrace>"
  and cte_wp_at: "\<And> dest.
  \<lbrace>\<lambda>s. (P0 and P1 and P2 and P3) s \<and> cte_wp_at' \<top> dest s \<rbrace> f
  \<lbrace>\<lambda>a s. cte_wp_at' \<top> dest s\<rbrace>"
  shows "monad_commute (P0 and P1 and P2 and P3 and P4 and P5 and pspace_aligned' and pspace_distinct')
  (locateCTE src) f"
proof -
  have same:
    "\<And>ptr val next s s'. (ptr, s') \<in> fst (locateCTE src s)
    \<Longrightarrow> s' = s"
    by (erule use_valid[OF _ locateCTE_inv],simp)
  show ?thesis
  apply (clarsimp simp:monad_commute_def)
  apply (clarsimp simp:bind_def return_def)
  apply (intro conjI iffI set_eqI)
     apply (clarsimp)
     apply (frule same)
     apply (clarsimp)
     apply (rule bexI[rotated], assumption)
     apply (frule singleton_locateCTE[THEN iffD1])
     apply (frule locateCTE_monad [OF ko_wp_at cte_wp_at psp_distinct psp_aligned])
         apply assumption+
      apply simp
     apply (clarsimp)
     apply (rule bexI[rotated])
      apply (fastforce)
     apply clarsimp
    apply clarsimp
    apply (frule empty_failD2[OF empty_fail_locateCTE no_failD[OF nf(2)]])
    apply clarsimp
    apply (rule bexI[rotated],assumption)
    apply (clarsimp)
    apply (frule_tac s = bb in same)
    apply (frule_tac s = s in same)
    apply clarsimp
    apply (frule_tac s1 = s in singleton_locateCTE[THEN iffD1])
    apply (frule locateCTE_monad [OF ko_wp_at cte_wp_at psp_distinct psp_aligned])
        apply assumption+
     apply simp
    apply (rule bexI[rotated],assumption)
    apply (drule sym)
    apply (clarsimp simp:singleton_locateCTE singleton_iff)
    apply fastforce
   apply (clarsimp simp:split_def image_def)
   apply (elim disjE)
    apply clarsimp
    apply (drule same)
    apply simp
   apply (frule no_failD[OF nf(2)])
   apply simp
  apply (clarsimp simp:split_def image_def)
  apply (elim disjE)
   apply clarsimp
   apply (frule empty_failD2[OF empty_fail_locateCTE no_failD[OF nf(2)]])
   apply clarsimp
   apply (frule same)
   apply simp
   apply (frule singleton_locateCTE[THEN iffD1])
   apply (frule locateCTE_monad [OF ko_wp_at cte_wp_at psp_distinct psp_aligned])
       apply assumption+
    apply simp
   apply (clarsimp)
   apply (simp add: fail_empty_locateCTE)
  apply (simp add: no_failD[OF nf(1)])
  done
qed

lemmas getObjSize_simps = X64_H.getObjectSize_def[split_simps X64_H.object_type.split apiobject_type.split]

lemma arch_toAPIType_simps:
 "X64_H.toAPIType ty = Some a \<Longrightarrow> ty = APIObjectType a"
  by (case_tac ty,auto simp:X64_H.toAPIType_def)

lemma createObject_cte_wp_at':
  "\<lbrace>\<lambda>s. Types_H.getObjectSize ty us < word_bits \<and>
        is_aligned ptr (Types_H.getObjectSize ty us) \<and>
        pspace_no_overlap' ptr (Types_H.getObjectSize ty us) s \<and>
        cte_wp_at' (\<lambda>c. P c) slot s \<and> pspace_aligned' s \<and>
        pspace_distinct' s\<rbrace>
   RetypeDecls_H.createObject ty ptr us d
   \<lbrace>\<lambda>r s. cte_wp_at' (\<lambda>c. P c) slot s \<rbrace>"
  apply (simp add:createObject_def)
  apply (rule hoare_pre)
   apply (wpc
        | wp createObjects_orig_cte_wp_at'[where sz = "(Types_H.getObjectSize ty us)"]
             threadSet_cte_wp_at'
        | simp add: X64_H.createObject_def placeNewDataObject_def
                    unless_def placeNewObject_def2 objBits_simps range_cover_full
                    curDomain_def bit_simps
                    pdBits_def getObjSize_simps archObjSize_def
                    apiGetObjectSize_def tcbBlockSizeBits_def
                    epSizeBits_def ntfnSizeBits_def
                    cteSizeBits_def
        | intro conjI impI | clarsimp dest!: arch_toAPIType_simps)+
  done

lemma createObject_getCTE_commute:
  "monad_commute
     (cte_wp_at' (\<lambda>_. True) dests and pspace_aligned' and pspace_distinct' and
      pspace_no_overlap' ptr (Types_H.getObjectSize ty us) and
      K (ptr \<noteq> dests) and K (Types_H.getObjectSize ty us < word_bits) and
      K (is_aligned ptr (Types_H.getObjectSize ty us)))
     (RetypeDecls_H.createObject ty ptr us d) (getCTE dests)"
  apply (rule monad_commute_guard_imp[OF commute_commute])
   apply (rule getCTE_commute)
   apply (rule hoare_pre)
    apply (wp createObject_cte_wp_at')
   apply (clarsimp simp:cte_wp_at_ctes_of)
   apply assumption
  apply (clarsimp simp:cte_wp_at_ctes_of)
  done

lemma simpler_placeNewObject_def:
  "\<lbrakk>us < word_bits;is_aligned ptr (objBitsKO (injectKOS val) + us);
    pspace_no_overlap' ptr (objBitsKO (injectKOS val) + us) s; pspace_aligned' s \<rbrakk> \<Longrightarrow> placeNewObject ptr val us s =
    modify (ksPSpace_update
       (\<lambda>_. foldr (\<lambda>addr map. map(addr \<mapsto> injectKOS val)) (new_cap_addrs (2 ^ us) ptr (injectKOS val))
       (ksPSpace s))) s"
  apply (clarsimp simp:placeNewObject_def2)
  apply (clarsimp simp:createObjects'_def)
  apply (simp add:bind_def in_monad when_def is_aligned_mask[THEN iffD1])
  apply (clarsimp simp:return_def bind_def gets_def assert_def fail_def get_def split_def
                  split:option.splits)
  apply (clarsimp simp: new_cap_addrs_fold' word_1_le_power[where 'a=machine_word_len, folded word_bits_def] lookupAround2_char1 not_less)
  apply (drule(1) pspace_no_overlapD'[rotated])
  apply (drule_tac x = a in in_empty_interE)
    apply clarsimp
    apply (drule(1) pspace_alignedD')
    apply (simp add:is_aligned_no_overflow)
   apply (clarsimp simp: is_aligned_neg_mask_eq shiftL_nat p_assoc_help)
  apply simp
  done

lemma fail_set: "fst (fail s) = {}"
  by (clarsimp simp: fail_def)

lemma locateCTE_cte_no_fail:
 "no_fail (cte_at' src) (locateCTE src)"
  apply (clarsimp simp:no_fail_def cte_wp_at'_def getObject_def
     locateCTE_def return_def gets_def get_def bind_def split_def
     assert_opt_def assert_def in_fail fail_set split:option.splits)
  apply (clarsimp simp:cte_check_def ObjectInstances_H.loadObject_cte)
  apply (drule in_singleton)
  by (auto simp: objBits_simps cteSizeBits_def alignError_def
    alignCheck_def in_monad is_aligned_mask magnitudeCheck_def
    typeError_def
    cong: if_cong split: if_splits option.splits kernel_object.splits)

lemma not_in_new_cap_addrs:
  "\<lbrakk>is_aligned ptr (objBitsKO obj + us);
    objBitsKO obj + us < word_bits;
    pspace_no_overlap' ptr (objBitsKO obj + us) s;
    ksPSpace s dest = Some ko;pspace_aligned' s\<rbrakk>
   \<Longrightarrow> dest \<notin> set (new_cap_addrs (2 ^ us) ptr obj)"
  supply
    is_aligned_neg_mask_eq[simp del]
    is_aligned_neg_mask_weaken[simp del]
  apply (rule ccontr)
  apply simp
  apply (drule(1) pspace_no_overlapD'[rotated])
  apply (erule_tac x = dest in in_empty_interE)
   apply (clarsimp)
   apply (erule(1) is_aligned_no_overflow[OF pspace_alignedD'])
  apply (erule subsetD[rotated])
  apply (simp add:p_assoc_help)
  apply (rule new_cap_addrs_subset[unfolded ptr_add_def,simplified])
  apply (rule range_cover_rel[OF range_cover_full])
     apply simp+
  done

lemma placeNewObject_pspace_aligned':
  "\<lbrace>K (is_aligned ptr (objBitsKO (injectKOS val) + us) \<and>
        objBitsKO (injectKOS val) + us < word_bits) and
    pspace_aligned' and pspace_distinct' and
    pspace_no_overlap' ptr (objBitsKO (injectKOS val) + us)\<rbrace>
   placeNewObject ptr val us
   \<lbrace>\<lambda>r s. pspace_aligned' s\<rbrace>"
  apply (clarsimp simp:valid_def)
  apply (simp add:simpler_placeNewObject_def simpler_modify_def)
  apply (subst data_map_insert_def[symmetric])+
  apply (erule(2) Retype_R.retype_aligned_distinct' [unfolded data_map_insert_def[symmetric]])
  apply (rule range_cover_rel[OF range_cover_full])
     apply simp+
  done

lemma placeNewObject_pspace_distinct':
  "\<lbrace>\<lambda>s. objBitsKO (injectKOS val) + us < word_bits \<and>
        is_aligned ptr (objBitsKO (injectKOS val) + us) \<and>
        pspace_no_overlap' ptr (objBitsKO (injectKOS val) + us) s \<and>
        pspace_aligned' s \<and> pspace_distinct' s\<rbrace>
   placeNewObject ptr val us
   \<lbrace>\<lambda>a. pspace_distinct'\<rbrace>"
 apply (clarsimp simp:valid_def)
  apply (simp add:simpler_placeNewObject_def simpler_modify_def)
 apply (subst data_map_insert_def[symmetric])+
 apply (erule(2) Retype_R.retype_aligned_distinct'
   [unfolded data_map_insert_def[symmetric]])
 apply (rule range_cover_rel[OF range_cover_full])
  apply simp+
 done

lemma placeNewObject_ko_wp_at':
  "\<lbrace>\<lambda>s. (if slot \<in> set (new_cap_addrs (2 ^ us) ptr (injectKOS val))
         then P (injectKOS val)
         else ko_wp_at' P slot s) \<and>
        objBitsKO (injectKOS val) + us < word_bits \<and>
        is_aligned ptr (objBitsKO (injectKOS val) + us) \<and>
        pspace_no_overlap' ptr (objBitsKO (injectKOS val) + us) s \<and>
        pspace_aligned' s \<and> pspace_distinct' s\<rbrace>
   placeNewObject ptr val us
   \<lbrace>\<lambda>a. ko_wp_at' P slot\<rbrace>"
  apply (clarsimp simp:valid_def split del:if_split)
  apply (simp add:simpler_placeNewObject_def simpler_modify_def)
  apply (subst data_map_insert_def[symmetric])+
  apply (subst retype_ko_wp_at')
      apply simp+
   apply (rule range_cover_rel[OF range_cover_full])
      apply simp+
  done

lemma cte_wp_at_cases_mask':
  "cte_wp_at' P p = (\<lambda>s.
    (obj_at' P p s
       \<or> p && mask tcbBlockSizeBits \<in> dom tcb_cte_cases
           \<and> obj_at' (P \<circ> fst (the (tcb_cte_cases (p && mask tcbBlockSizeBits))))
                     (p && ~~ mask tcbBlockSizeBits) s))"
  apply (rule ext)
  apply (simp add:cte_wp_at_obj_cases_mask)
  done

lemma not_in_new_cap_addrs':
  "\<lbrakk>dest \<in> set (new_cap_addrs (2 ^ us) ptr obj);
    is_aligned ptr (objBitsKO obj + us);
    objBitsKO obj + us < word_bits;
    pspace_no_overlap' ptr (objBitsKO obj + us) s;
    pspace_aligned' s \<rbrakk>
  \<Longrightarrow> ksPSpace s dest = None"
  apply (rule ccontr)
  apply clarsimp
  apply (drule not_in_new_cap_addrs)
      apply simp+
  done

lemma placeNewObject_cte_wp_at':
  "\<lbrace>K (is_aligned ptr (objBitsKO (injectKOS val) + us) \<and>
       objBitsKO (injectKOS val) + us < word_bits) and
    K (ptr \<noteq> src) and cte_wp_at' P src and
    pspace_aligned' and pspace_distinct' and
    pspace_no_overlap' ptr (objBitsKO (injectKOS val) + us)\<rbrace>
   placeNewObject ptr val us
   \<lbrace>\<lambda>r s. cte_wp_at' P src s\<rbrace>"
  apply (clarsimp simp:placeNewObject_def2)
  apply (wp createObjects_orig_cte_wp_at')
  apply (auto simp:range_cover_full)
  done


lemma placeNewObject_cte_wp_at'':
  "\<lbrace>\<lambda>s. cte_wp_at' P slot s \<and>
  objBitsKO (injectKOS val) + us < word_bits \<and>
  is_aligned ptr (objBitsKO (injectKOS val) + us) \<and>
  pspace_no_overlap' ptr (objBitsKO (injectKOS val) + us) s \<and>
  pspace_aligned' s \<and> pspace_distinct' s\<rbrace>
  placeNewObject ptr val us \<lbrace>\<lambda>a s. cte_wp_at' P slot s\<rbrace>"
  apply (simp add:cte_wp_at_cases_mask' obj_at'_real_def)
  apply (wp hoare_vcg_disj_lift placeNewObject_ko_wp_at')
  apply (clarsimp simp:conj_comms)
  apply (intro conjI impI allI impI)
    apply (drule(4) not_in_new_cap_addrs')
    apply (clarsimp simp:ko_wp_at'_def)
   apply (drule (4)not_in_new_cap_addrs')+
   apply (clarsimp simp:ko_wp_at'_def)
  apply (elim disjE)
   apply simp
  apply clarsimp
  apply (drule (4)not_in_new_cap_addrs')+
  apply (clarsimp simp:ko_wp_at'_def)
  done

lemma no_fail_placeNewObject:
  "no_fail (\<lambda>s. us < word_bits \<and>
                is_aligned ptr (objBitsKO (injectKOS val) + us) \<and>
                pspace_no_overlap' ptr (objBitsKO (injectKOS val) + us) s \<and>
                pspace_aligned' s)
           (placeNewObject ptr val us)"
   by (clarsimp simp:no_fail_def simpler_modify_def simpler_placeNewObject_def)

lemma placeNewObject_locateCTE_commute:
  "monad_commute
     (K (is_aligned ptr (objBitsKO (injectKOS val) + us) \<and>
         (objBitsKO (injectKOS val) + us) < word_bits \<and> ptr \<noteq> src) and
      pspace_no_overlap' ptr (objBitsKO (injectKOS val) + us) and
      pspace_aligned' and pspace_distinct' and cte_at' src)
     (placeNewObject ptr val us) (locateCTE src)"
  apply (rule monad_commute_guard_imp)
  apply (rule commute_commute[OF locateCTE_commute])
      apply (wp no_fail_placeNewObject locateCTE_cte_no_fail
        placeNewObject_pspace_aligned'
        placeNewObject_pspace_distinct'
        placeNewObject_ko_wp_at' | simp)+
    apply (clarsimp simp:ko_wp_at'_def)
    apply (drule(3) not_in_new_cap_addrs)
    apply fastforce+
   apply (wp placeNewObject_cte_wp_at'')
   apply clarsimp
  apply fastforce
  done

lemma update_ksPSpaceI:
  "kh = kh' \<Longrightarrow> s\<lparr>ksPSpace := kh\<rparr> = s\<lparr>ksPSpace := kh'\<rparr>"
 by simp

lemma placeNewObject_modify_commute:
  "monad_commute
     (K (is_aligned ptr (objBitsKO (injectKOS val) + us) \<and>
         objBitsKO (injectKOS val) + us < word_bits) and
      pspace_no_overlap' ptr (objBitsKO (injectKOS val) + us) and
      pspace_aligned' and ko_wp_at' (\<lambda>a. objBitsKO (f (Some a)) = objBitsKO a) ptr')
     (placeNewObject ptr val us)
     (modify (ksPSpace_update (\<lambda>ps. ps(ptr' \<mapsto> f (ps ptr')))))"
  apply (clarsimp simp:monad_commute_def simpler_modify_def
    bind_def split_def return_def)
  apply (subst simpler_placeNewObject_def)
      apply ((simp add:range_cover_def)+)[4]
  apply (clarsimp simp: simpler_modify_def)
  apply (frule(1) range_cover_full)
  apply (simp add: simpler_placeNewObject_def)
  apply (subgoal_tac "pspace_no_overlap' ptr (objBitsKO (injectKOS val) + us)
            (ksPSpace_update (\<lambda>ps. ps(ptr' \<mapsto> f (ps ptr'))) s)")
   prefer 2
    apply (clarsimp simp:ko_wp_at'_def)
    apply (subst pspace_no_overlap'_def)
    apply (intro allI impI)
    apply (case_tac "x = ptr'")
     apply (subgoal_tac "objBitsKO koa = objBitsKO ko")
      apply (drule(1) pspace_no_overlapD')
      apply (clarsimp simp:field_simps)
     apply (clarsimp)
    apply (drule_tac x = x and s = s in pspace_no_overlapD'[rotated])
     apply (simp)
    apply (clarsimp simp:field_simps)
  apply (subgoal_tac "pspace_aligned'
    (ksPSpace_update (\<lambda>ps. ps(ptr' \<mapsto> f (ps ptr'))) s)")
  prefer 2
   apply (subst pspace_aligned'_def)
   apply (rule ballI)
   apply (erule domE)
   apply (clarsimp simp:ko_wp_at'_def split:if_split_asm)
   apply (drule(1) pspace_alignedD')+
   apply simp
  apply (simp add:simpler_placeNewObject_def)
  apply (clarsimp simp:simpler_modify_def Fun.comp_def
      singleton_iff image_def)
  apply (intro conjI update_ksPSpaceI ext)
   apply (clarsimp simp:ko_wp_at'_def foldr_upd_app_if)
   apply (frule(1) pspace_no_overlapD')
   apply (drule subsetD[rotated])
    apply (rule new_cap_addrs_subset)
    apply (erule range_cover_rel)
     apply simp
    apply simp
   apply (drule_tac x = ptr' in in_empty_interE)
     apply (clarsimp simp:is_aligned_no_overflow)
    apply (clarsimp simp:range_cover_def ptr_add_def
     is_aligned_neg_mask_eq obj_range'_def p_assoc_help)
   apply simp
  done

lemma cte_update_objBits[simp]:
  "(objBitsKO (cte_update cte b src a)) = objBitsKO b"
  by (case_tac b,
    (simp add:objBits_simps cte_update_def)+)

lemma locateCTE_ret_neq:
  "\<lbrace>ko_wp_at' (\<lambda>x. koTypeOf x \<noteq> TCBT \<and> koTypeOf x \<noteq> CTET) ptr\<rbrace>
  locateCTE src \<lbrace>\<lambda>r s. ptr \<noteq> r\<rbrace>"
  apply (clarsimp simp add:valid_def)
  apply (frule use_valid[OF _ locateCTE_case])
   apply simp
  apply (frule(1) use_valid[OF _ locateCTE_inv])
  apply (clarsimp simp:ko_wp_at'_def koTypeOf_def)
  apply (auto split:Structures_H.kernel_object.split_asm)
  done

lemma locateCTE_ko_wp_at':
  "\<lbrace>cte_at' src and pspace_distinct' \<rbrace>
   locateCTE src
   \<lbrace>\<lambda>rv. ko_wp_at' \<top> rv \<rbrace>"
  apply (clarsimp simp:locateCTE_def split_def)
  apply wp
  apply (clarsimp simp:cte_wp_at'_def getObject_def
    gets_def split_def get_def bind_def return_def
    ko_wp_at'_def lookupAround2_char1 assert_opt_def)
  apply (clarsimp split:option.splits
    simp:fail_def return_def lookupAround2_char1)
  apply (case_tac ba)
    apply (simp_all add:cte_check_def)
    apply (clarsimp simp:lookupAround2_char1
      objBits_simps cte_update_def)
    apply (drule(1) pspace_distinctD')+
    apply (simp add:objBits_simps)
  apply (clarsimp simp:objBits_simps cte_update_def)
  apply (drule(1) pspace_distinctD')+
  apply (simp add:objBits_simps)
  done


lemma setCTE_placeNewObject_commute:
  "monad_commute
     (K (is_aligned ptr (objBitsKO (injectKOS val) + us) \<and>
         objBitsKO (injectKOS val) + us < word_bits) and
      K(ptr \<noteq> src) and cte_wp_at' (\<lambda>_. True) src and
      pspace_aligned' and pspace_distinct' and
      pspace_no_overlap' ptr (objBitsKO (injectKOS val) + us))
     (setCTE src cte) (placeNewObject ptr val us)"
  apply (clarsimp simp: setCTE_def2 split_def)
  apply (rule commute_commute)
  apply (rule monad_commute_guard_imp)
   apply (rule monad_commute_split[OF placeNewObject_modify_commute])
    apply (rule placeNewObject_locateCTE_commute)
    apply (wp locateCTE_inv locateCTE_ko_wp_at' | simp)+
  done

lemma doMachineOp_upd_heap_commute:
  "monad_commute \<top> (doMachineOp x) (modify (ksPSpace_update P))"
  apply (clarsimp simp:doMachineOp_def split_def simpler_modify_def
    gets_def get_def return_def bind_def select_f_def)
  apply (clarsimp simp:monad_commute_def bind_def return_def)
  apply fastforce
  done

lemma magnitudeCheck_det:
  "\<lbrakk>ksPSpace s ptr = Some ko; is_aligned ptr (objBitsKO ko);
    ps_clear ptr (objBitsKO ko) s\<rbrakk>
   \<Longrightarrow> magnitudeCheck ptr (snd (lookupAround2 ptr (ksPSpace s)))
                          (objBitsKO ko) s =
       ({((), s)},False)"
  apply (frule in_magnitude_check'[THEN iffD2])
   apply (case_tac ko)
     apply (simp add: objBits_simps' pageBits_def)+
    apply (rename_tac arch_kernel_object)
    apply (case_tac arch_kernel_object)
     apply (simp add:archObjSize_def pageBits_def)+
  apply (subgoal_tac
    "\<not> snd (magnitudeCheck ptr (snd (lookupAround2 ptr (ksPSpace s))) (objBitsKO ko) s)")
   apply (drule singleton_in_magnitude_check)
   apply (drule_tac x = s in spec)
   apply (case_tac
    "(magnitudeCheck ptr (snd (lookupAround2 ptr (ksPSpace s))) (objBitsKO ko) s)")
    apply simp
  apply (rule ccontr)
  apply (clarsimp simp:magnitudeCheck_assert assert_def fail_def return_def
    split:if_splits option.splits)
  done

lemma getPDE_det:
  "ko_wp_at' ((=) (KOArch (KOPDE pde))) p s
   \<Longrightarrow> getObject p s = ({((pde::X64_H.pde),s)},False)"
  apply (clarsimp simp:ko_wp_at'_def getObject_def split_def
                       bind_def gets_def return_def get_def
                       assert_opt_def split:if_splits)

  apply (clarsimp simp: fail_def return_def lookupAround2_known1)
   apply (simp add: loadObject_default_def)
  apply (clarsimp simp:projectKO_def projectKO_opt_pde alignCheck_def
    is_aligned_mask objBits_simps unless_def)
  apply (clarsimp simp:bind_def return_def)
  apply (intro conjI)
   apply (intro set_eqI iffI)
    apply clarsimp
    apply (subst (asm) in_magnitude_check')
     apply (simp add:archObjSize_def is_aligned_mask)+
    apply (rule bexI[rotated])
     apply (rule in_magnitude_check'[THEN iffD2])
      apply (simp add:is_aligned_mask)+
   apply (clarsimp simp:image_def)
  apply (clarsimp simp:magnitudeCheck_assert assert_def
    objBits_def archObjSize_def
    return_def fail_def lookupAround2_char2 split:option.splits if_split_asm)
  apply (rule ccontr)
  apply (simp add:ps_clear_def field_simps)
  apply (erule_tac x = x2 in in_empty_interE)
   apply (clarsimp simp:less_imp_le)
   apply (rule conjI)
    apply (subst add.commute)
    apply (rule word_diff_ls')
     apply (clarsimp simp: not_le plus_one_helper)
    apply (subst add.commute)
    apply (simp add: is_aligned_no_wrap' is_aligned_mask)
  apply auto
  done

lemma in_dom_eq:
  "m a = Some obj \<Longrightarrow> dom (\<lambda>b. if b = a then Some g else m b) = dom m"
  by (rule set_eqI,clarsimp simp:dom_def)

lemma setCTE_pde_at':
  "\<lbrace>ko_wp_at' ((=) (KOArch (KOPDE pde))) ptr and
    cte_wp_at' (\<lambda>_. True) src and pspace_distinct'\<rbrace>
   setCTE src cte
   \<lbrace>\<lambda>x s. ko_wp_at' ((=) (KOArch (KOPDE pde))) ptr s\<rbrace>"
   apply (clarsimp simp:setCTE_def2)
   including no_pre apply wp
   apply (simp add:split_def)
   apply (clarsimp simp:valid_def)
   apply (subgoal_tac "b = s")
   prefer 2
    apply (erule use_valid[OF _ locateCTE_inv])
    apply simp
   apply (subgoal_tac "ptr \<noteq> a")
   apply (frule use_valid[OF _ locateCTE_ko_wp_at'])
    apply simp
   apply (clarsimp simp:ko_wp_at'_def ps_clear_def)
   apply (simp add:in_dom_eq)
   apply (drule use_valid[OF _ locateCTE_case])
    apply simp
   apply (clarsimp simp:ko_wp_at'_def objBits_simps archObjSize_def)
   done

lemma storePDE_det:
  "ko_wp_at' ((=) (KOArch (KOPDE pde))) ptr s
   \<Longrightarrow> storePDE ptr (new_pde::X64_H.pde) s =
       modify
         (ksPSpace_update (\<lambda>_. (ksPSpace s)(ptr \<mapsto> KOArch (KOPDE new_pde)))) s"
  apply (clarsimp simp:ko_wp_at'_def storePDE_def split_def
                       bind_def gets_def return_def
                       get_def setObject_def
                       assert_opt_def split:if_splits)
  apply (clarsimp simp:lookupAround2_known1 return_def alignCheck_def
                       updateObject_default_def split_def
                       archObjSize_def unless_def projectKO_def
                       projectKO_opt_pde bind_def when_def
                       is_aligned_mask[symmetric] objBits_simps)
  apply (drule magnitudeCheck_det)
    apply (simp add:objBits_simps archObjSize_def)+
  apply (simp add:simpler_modify_def)
  done

lemma modify_obj_commute:
  "monad_commute (K (ptr\<noteq> ptr'))
     (modify (ksPSpace_update (\<lambda>ps. ps(ptr \<mapsto> ko))))
     (modify (ksPSpace_update (\<lambda>ps. ps(ptr' \<mapsto> ko'))))"
  apply (clarsimp simp:monad_commute_def return_def bind_def simpler_modify_def)
  apply (case_tac s)
  apply auto
  done

lemma modify_specify:
  "(\<lambda>s. modify (ksPSpace_update (\<lambda>_. P (ksPSpace s))) s) =
   modify (ksPSpace_update (\<lambda>ps. P ps))"
  by (auto simp: simpler_modify_def)

lemma modify_specify2:
  "(modify (ksPSpace_update (\<lambda>_. P (ksPSpace s))) >>= g) s =
   (modify (ksPSpace_update (\<lambda>ps. P ps)) >>=g) s"
  apply (clarsimp simp:simpler_modify_def bind_def)
  apply (rule arg_cong[where f = "\<lambda>x. g ()  x"],simp)
  done

lemma modify_pde_pde_at':
  "\<lbrace>pde_at' ptr\<rbrace>
   modify (ksPSpace_update (\<lambda>ps. ps(ptr \<mapsto> KOArch (KOPDE new_pde))))
   \<lbrace>\<lambda>a. pde_at' ptr\<rbrace>"
  apply wp
  apply (clarsimp simp del: fun_upd_apply
                  simp: typ_at'_def ko_wp_at'_def objBits_simps archObjSize_def)
  apply (clarsimp simp:ps_clear_def)
  apply (case_tac ko,simp_all)
  apply (rename_tac arch_kernel_object)
  apply (case_tac arch_kernel_object,simp_all)
  apply (clarsimp simp:archObjSize_def)
  done

lemma modify_pde_pspace_distinct':
  "\<lbrace>pde_at' ptr and pspace_distinct'\<rbrace>
   modify (ksPSpace_update (\<lambda>ps. ps(ptr \<mapsto> KOArch (KOPDE new_pde))))
   \<lbrace>\<lambda>a. pspace_distinct'\<rbrace>"
  apply (clarsimp simp: simpler_modify_def ko_wp_at'_def valid_def typ_at'_def)
  apply (case_tac ko; simp)
  apply (rename_tac arch_kernel_object)
  apply (case_tac arch_kernel_object,simp_all)
  apply (subst pspace_distinct'_def)
  apply (intro ballI)
  apply (erule domE)
  apply (clarsimp split:if_splits)
   apply (drule(1) pspace_distinctD')
   apply (simp add:objBits_simps archObjSize_def)
   apply (simp add:ps_clear_def)
  apply (drule_tac x = x in pspace_distinctD')
   apply simp
  unfolding ps_clear_def
  apply (erule disjoint_subset2[rotated])
  apply clarsimp
  done

lemma modify_pde_pspace_aligned':
  "\<lbrace>pde_at' ptr and pspace_aligned'\<rbrace>
   modify (ksPSpace_update (\<lambda>ps. ps(ptr \<mapsto> KOArch (KOPDE new_pde))))
   \<lbrace>\<lambda>a. pspace_aligned'\<rbrace>"
  apply (clarsimp simp: simpler_modify_def ko_wp_at'_def valid_def typ_at'_def)
  apply (case_tac ko,simp_all)
  apply (rename_tac arch_kernel_object)
  apply (case_tac arch_kernel_object,simp_all)
  apply (subst pspace_aligned'_def)
  apply (intro ballI)
  apply (erule domE)
  apply (clarsimp split:if_splits)
   apply (drule(1) pspace_alignedD')
    apply (simp add:objBits_simps archObjSize_def)
   apply (simp add:ps_clear_def)
  apply (drule_tac x = x in pspace_alignedD')
   apply simp
  apply simp
  done

lemma modify_pde_psp_no_overlap':
  "\<lbrace>pde_at' ptr and pspace_no_overlap' ptr' sz\<rbrace>
   modify (ksPSpace_update (\<lambda>ps. ps(ptr \<mapsto> KOArch (KOPDE new_pde))))
   \<lbrace>\<lambda>a. pspace_no_overlap' ptr' sz\<rbrace>"
  proof -
  note blah[simp del] = untyped_range.simps usable_untyped_range.simps atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex
  show ?thesis
  apply (clarsimp simp:simpler_modify_def ko_wp_at'_def
    valid_def typ_at'_def)
  apply (case_tac ko,simp_all)
  apply (rename_tac arch_kernel_object)
  apply (case_tac arch_kernel_object,simp_all)
  apply (subst pspace_no_overlap'_def)
  apply (intro allI impI)
  apply (clarsimp split:if_splits)
   apply (drule(1) pspace_no_overlapD')
    apply (simp add:objBits_simps archObjSize_def field_simps)
  apply (drule(1) pspace_no_overlapD')+
  apply (simp add:field_simps)
  done
  qed

lemma koTypeOf_pde:
  "koTypeOf ko = ArchT PDET \<Longrightarrow> \<exists>pde. ko = KOArch (KOPDE pde)"
  apply (case_tac ko,simp_all)
  apply (rename_tac arch_kernel_object)
  apply (case_tac arch_kernel_object,simp_all)
  done

lemma modify_mapM_x:
  "(modify (ksPSpace_update (foldr (\<lambda>addr map. map(addr \<mapsto> obj)) list))) =
   (mapM_x (\<lambda>x. modify (ksPSpace_update (\<lambda>m. m(x\<mapsto> obj)))) (rev list))"
   apply (induct list)
    apply (clarsimp simp:mapM_x_Nil)
    apply (rule ext)
    apply (simp add:simpler_modify_def return_def)
   apply (clarsimp simp:mapM_x_append mapM_x_singleton simpler_modify_def)
   apply (drule sym)
   apply (rule ext)
   apply (simp add:Fun.comp_def bind_def)
   done

lemma modify_obj_commute':
  "monad_commute (K (ptr\<noteq> ptr') and ko_wp_at' \<top> ptr')
     (modify (ksPSpace_update (\<lambda>ps. ps(ptr \<mapsto> ko))))
     (modify (ksPSpace_update (\<lambda>ps. ps(ptr' \<mapsto> f (the (ps ptr'))))))"
  apply (clarsimp simp:monad_commute_def return_def
    bind_def simpler_modify_def ko_wp_at'_def)
  apply (case_tac s)
   apply clarsimp
  apply (rule ext)
  apply clarsimp
  done

lemma cte_wp_at_modify_pde:
  notes blah[simp del] =  atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex
          atLeastAtMost_iff
  shows
  "\<lbrakk>ksPSpace s ptr' = Some (KOArch (KOPDE pde)); pspace_aligned' s;cte_wp_at' \<top> ptr s\<rbrakk>
       \<Longrightarrow> cte_wp_at' \<top> ptr (s\<lparr>ksPSpace := (ksPSpace s)(ptr' \<mapsto> (KOArch (KOPDE pde')))\<rparr>)"
  apply (simp add:cte_wp_at_obj_cases_mask obj_at'_real_def)
  apply (frule(1) pspace_alignedD')
  apply (elim disjE)
   apply (rule disjI1)
   apply (clarsimp simp add:ko_wp_at'_def)
   apply (intro conjI impI)
      apply (simp add:objBits_simps archObjSize_def)
     apply (clarsimp simp:projectKO_opt_cte)
    apply (simp add:ps_clear_def)+
    apply (clarsimp simp:objBits_simps archObjSize_def)
   apply (simp add:ps_clear_def)
   apply (rule ccontr)
   apply simp
   apply (erule in_emptyE, blast)
  apply simp
  apply (rule disjI2)
  apply (clarsimp simp:ko_wp_at'_def)
  apply (intro conjI impI)
     apply (simp add:objBits_simps archObjSize_def)+
    apply (clarsimp simp:projectKO_opt_cte projectKO_opt_tcb)
    apply (simp add:ps_clear_def)+
   apply (clarsimp simp:objBits_simps archObjSize_def)
  apply (simp add:ps_clear_def)
  apply (rule ccontr)
  apply simp
  apply (erule in_emptyE)
  apply blast
  done

lemma setCTE_gets_globalPML4_commute:
  "monad_commute
     (cte_wp_at' (\<lambda>_. True) src and pspace_distinct' and pspace_aligned')
     (setCTE src cte) (gets (x64KSSKIMPML4 \<circ> ksArchState))"
  apply (simp add:setCTE_def2)
  apply (rule monad_commute_guard_imp)
   apply (rule commute_commute[OF monad_commute_split[where Q = "\<lambda>r. \<top>"]])
     apply (clarsimp simp:monad_commute_def gets_def simpler_modify_def bind_def get_def return_def)
    apply (rule commute_commute[OF locateCTE_commute])
         apply (wp locateCTE_cte_no_fail)+
     apply clarsimp
    apply (wp|clarsimp)+
  apply fastforce
  done

lemma placeNewObject_gets_globalPML4_commute:
  "monad_commute
     (pspace_distinct' and pspace_aligned' and
      K (us < word_bits \<and> is_aligned ptr (objBitsKO (injectKOS val) + us)) and
      pspace_no_overlap' ptr (objBitsKO (injectKOS val) + us) )
     (placeNewObject ptr val us) (gets (x64KSSKIMPML4 \<circ> ksArchState))"
  apply (rule commute_name_pre_state)
  apply (rule monad_commute_guard_imp)
  apply (rule_tac commute_rewrite[where Q = "\<lambda>s.
    pspace_no_overlap' ptr (objBitsKO (injectKOS val) + us) s
    \<and> pspace_distinct' s \<and> pspace_aligned' s" and R = "\<top>"])
   apply (rule simpler_placeNewObject_def)
       apply simp+
    apply wp
   apply (simp add:monad_commute_def gets_def get_def
     return_def bind_def simpler_modify_def)
  apply clarsimp
  done

lemma getPML4E_det:
  "ko_wp_at' ((=) (KOArch (KOPML4E pml4e))) p s
   \<Longrightarrow> getObject p s = ({((pml4e::X64_H.pml4e),s)},False)"
  apply (clarsimp simp:ko_wp_at'_def getObject_def split_def
                       bind_def gets_def return_def get_def
                       assert_opt_def split:if_splits)

  apply (clarsimp simp: fail_def return_def lookupAround2_known1)
   apply (simp add: loadObject_default_def)
  apply (clarsimp simp:projectKO_def projectKO_opt_pml4e alignCheck_def
    is_aligned_mask objBits_simps unless_def)
  apply (clarsimp simp:bind_def return_def)
  apply (intro conjI)
   apply (intro set_eqI iffI)
    apply clarsimp
    apply (subst (asm) in_magnitude_check')
     apply (simp add:archObjSize_def is_aligned_mask)+
    apply (rule bexI[rotated])
     apply (rule in_magnitude_check'[THEN iffD2])
      apply (simp add:is_aligned_mask)+
   apply (clarsimp simp:image_def)
  apply (clarsimp simp:magnitudeCheck_assert assert_def
    objBits_def archObjSize_def
    return_def fail_def lookupAround2_char2 split:option.splits if_split_asm)
  apply (rule ccontr)
  apply (simp add:ps_clear_def field_simps)
  apply (erule_tac x = x2 in in_empty_interE)
   apply (clarsimp simp:less_imp_le)
   apply (rule conjI)
    apply (subst add.commute)
    apply (rule word_diff_ls')
     apply (clarsimp simp:field_simps not_le plus_one_helper)
    apply (subst add.commute)
    apply (simp add: is_aligned_no_wrap' is_aligned_mask)
   apply simp
  apply auto
  done

lemma setCTE_pml4e_at':
  "\<lbrace>ko_wp_at' ((=) (KOArch (KOPML4E pml4e))) ptr and
    cte_wp_at' (\<lambda>_. True) src and pspace_distinct'\<rbrace>
   setCTE src cte
   \<lbrace>\<lambda>x s. ko_wp_at' ((=) (KOArch (KOPML4E pml4e))) ptr s\<rbrace>"
   apply (clarsimp simp:setCTE_def2)
   including no_pre apply wp
   apply (simp add:split_def)
   apply (clarsimp simp:valid_def)
   apply (subgoal_tac "b = s")
   prefer 2
    apply (erule use_valid[OF _ locateCTE_inv])
    apply simp
   apply (subgoal_tac "ptr \<noteq> a")
   apply (frule use_valid[OF _ locateCTE_ko_wp_at'])
    apply simp
   apply (clarsimp simp:ko_wp_at'_def ps_clear_def)
   apply (simp add:in_dom_eq)
   apply (drule use_valid[OF _ locateCTE_case])
    apply simp
   apply (clarsimp simp:ko_wp_at'_def objBits_simps archObjSize_def)
   done

lemma getPML4E_setCTE_commute:
  "monad_commute
     (pml4e_at' ptr and pspace_distinct' and cte_wp_at' (\<lambda>_. True) src)
     (setCTE src cte)
     (getObject ptr :: KernelStateData_H.kernel_state \<Rightarrow>
                       (pml4e \<times> KernelStateData_H.kernel_state) set \<times> bool)"
  apply (rule commute_name_pre_state)
  apply (clarsimp simp:typ_at'_def ko_wp_at'_def)
  apply (case_tac ko,simp_all)
  apply (rename_tac arch_kernel_object)
  apply (case_tac arch_kernel_object,simp_all)
  apply clarsimp
  apply (rename_tac pml4e)
  apply (subgoal_tac "ko_wp_at' ((=) (KOArch (KOPML4E pml4e))) ptr s")
   prefer 2
   apply (clarsimp simp:ko_wp_at'_def)
  apply (rule monad_commute_guard_imp)
   apply (rule commute_commute)
   apply (rule commute_rewrite[OF getPML4E_det,where R = \<top>])
     apply assumption
    apply (wp setCTE_pml4e_at')
   apply (simp add:monad_commute_def bind_def)
  apply (auto simp:ko_wp_at'_def)
  done

lemma getPML4E_doMachineOp_commute:
  "monad_commute (pml4e_at' ptr) (doMachineOp f)
     ((getObject ptr) :: KernelStateData_H.kernel_state \<Rightarrow>
                         (pml4e \<times> KernelStateData_H.kernel_state) set \<times> bool)"
  apply (rule commute_name_pre_state)
  apply (clarsimp simp:typ_at'_def ko_wp_at'_def)
  apply (case_tac ko,simp_all)
  apply (rename_tac arch_kernel_object)
  apply (case_tac arch_kernel_object,simp_all)
  apply clarsimp
  apply (rename_tac pml4e)
  apply (subgoal_tac "ko_wp_at' ((=) (KOArch (KOPML4E pml4e))) ptr s")
   prefer 2
   apply (clarsimp simp:ko_wp_at'_def)
  apply (rule monad_commute_guard_imp)
   apply (rule commute_commute)
   apply (rule commute_rewrite[OF getPML4E_det,where R = \<top>])
     apply assumption
    apply (wp setCTE_pml4e_at')
   apply (simp add:monad_commute_def bind_def)
  apply auto
  done

lemma getPML4E_placeNewObject_commute:
  "monad_commute
     (pml4e_at' src and pspace_distinct' and pspace_aligned' and
      pspace_no_overlap' ptr (objBitsKO (injectKOS val) + sz) and
      K (is_aligned ptr (objBitsKO (injectKOS val) + sz) \<and>
         objBitsKO (injectKOS val) + sz < word_bits) )
     (placeNewObject ptr val sz)
     ((getObject src) :: KernelStateData_H.kernel_state \<Rightarrow>
                         (pml4e \<times> KernelStateData_H.kernel_state) set \<times> bool)"
  apply (rule commute_name_pre_state)
  apply (subgoal_tac "range_cover ptr (objBitsKO (injectKOS val) + sz) (objBitsKO (injectKOS val) + sz) (Suc 0)")
   prefer 2
   apply (rule range_cover_full)
    apply simp+
  apply (clarsimp simp:typ_at'_def ko_wp_at'_def)
  apply (case_tac ko,simp_all)
  apply (rename_tac arch_kernel_object)
  apply (case_tac arch_kernel_object,simp_all)
  apply clarsimp
  apply (rename_tac pml4e)
  apply (subgoal_tac "ko_wp_at' ((=) (KOArch (KOPML4E pml4e))) src s")
   prefer 2
   apply (clarsimp simp:ko_wp_at'_def)
  apply (rule monad_commute_guard_imp)
   apply (rule commute_commute)
   apply (rule commute_rewrite[OF getPML4E_det,where R = \<top>])
     apply assumption
    apply (simp add:placeNewObject_def2)
    apply (wp createObjects_orig_ko_wp_at2')
   apply (simp add:monad_commute_def bind_def)
  apply (auto simp:ko_wp_at'_def)
  done

lemma storePML4E_det:
  "ko_wp_at' ((=) (KOArch (KOPML4E pml4e))) ptr s
   \<Longrightarrow> storePML4E ptr (new_pml4e::X64_H.pml4e) s =
       modify
         (ksPSpace_update (\<lambda>_. (ksPSpace s)(ptr \<mapsto> KOArch (KOPML4E new_pml4e)))) s"
  apply (clarsimp simp:ko_wp_at'_def storePML4E_def split_def
                       bind_def gets_def return_def
                       get_def setObject_def
                       assert_opt_def split:if_splits)
  apply (clarsimp simp:lookupAround2_known1 return_def alignCheck_def
                       updateObject_default_def split_def
                       archObjSize_def unless_def projectKO_def
                       projectKO_opt_pml4e bind_def when_def
                       is_aligned_mask[symmetric] objBits_simps)
  apply (drule magnitudeCheck_det)
    apply (simp add:objBits_simps archObjSize_def)+
  apply (simp add:simpler_modify_def)
  done

lemma modify_pml4e_pml4e_at':
  "\<lbrace>pml4e_at' ptr\<rbrace>
   modify (ksPSpace_update (\<lambda>ps. ps(ptr \<mapsto> KOArch (KOPML4E new_pml4e))))
   \<lbrace>\<lambda>a. pml4e_at' ptr\<rbrace>"
  apply wp
  apply (clarsimp simp del: fun_upd_apply
                  simp: typ_at'_def ko_wp_at'_def objBits_simps archObjSize_def)
  apply (clarsimp simp:ps_clear_def)
  apply (case_tac ko,simp_all)
  apply (rename_tac arch_kernel_object)
  apply (case_tac arch_kernel_object,simp_all)
  apply (clarsimp simp:archObjSize_def)
  done

lemma modify_pml4e_pspace_distinct':
  "\<lbrace>pml4e_at' ptr and pspace_distinct'\<rbrace>
   modify (ksPSpace_update (\<lambda>ps. ps(ptr \<mapsto> KOArch (KOPML4E new_pml4e))))
   \<lbrace>\<lambda>a. pspace_distinct'\<rbrace>"
  apply (clarsimp simp: simpler_modify_def ko_wp_at'_def valid_def typ_at'_def)
  apply (case_tac ko; simp)
  apply (rename_tac arch_kernel_object)
  apply (case_tac arch_kernel_object,simp_all)
  apply (subst pspace_distinct'_def)
  apply (intro ballI)
  apply (erule domE)
  apply (clarsimp split:if_splits)
   apply (drule(1) pspace_distinctD')
   apply (simp add:objBits_simps archObjSize_def)
   apply (simp add:ps_clear_def)
  apply (drule_tac x = x in pspace_distinctD')
   apply simp
  unfolding ps_clear_def
  apply (erule disjoint_subset2[rotated])
  apply clarsimp
  done

lemma modify_pml4e_pspace_aligned':
  "\<lbrace>pml4e_at' ptr and pspace_aligned'\<rbrace>
   modify (ksPSpace_update (\<lambda>ps. ps(ptr \<mapsto> KOArch (KOPML4E new_pml4e))))
   \<lbrace>\<lambda>a. pspace_aligned'\<rbrace>"
  apply (clarsimp simp: simpler_modify_def ko_wp_at'_def valid_def typ_at'_def)
  apply (case_tac ko,simp_all)
  apply (rename_tac arch_kernel_object)
  apply (case_tac arch_kernel_object,simp_all)
  apply (subst pspace_aligned'_def)
  apply (intro ballI)
  apply (erule domE)
  apply (clarsimp split:if_splits)
   apply (drule(1) pspace_alignedD')
    apply (simp add:objBits_simps archObjSize_def)
   apply (simp add:ps_clear_def)
  apply (drule_tac x = x in pspace_alignedD')
   apply simp
  apply simp
  done

lemma modify_pml4e_psp_no_overlap':
  "\<lbrace>pml4e_at' ptr and pspace_no_overlap' ptr' sz\<rbrace>
   modify (ksPSpace_update (\<lambda>ps. ps(ptr \<mapsto> KOArch (KOPML4E new_pml4e))))
   \<lbrace>\<lambda>a. pspace_no_overlap' ptr' sz\<rbrace>"
  proof -
  note blah[simp del] = untyped_range.simps usable_untyped_range.simps atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex
  show ?thesis
  apply (clarsimp simp:simpler_modify_def ko_wp_at'_def
    valid_def typ_at'_def)
  apply (case_tac ko,simp_all)
  apply (rename_tac arch_kernel_object)
  apply (case_tac arch_kernel_object,simp_all)
  apply (subst pspace_no_overlap'_def)
  apply (intro allI impI)
  apply (clarsimp split:if_splits)
   apply (drule(1) pspace_no_overlapD')
    apply (simp add:objBits_simps archObjSize_def field_simps)
  apply (drule(1) pspace_no_overlapD')+
  apply (simp add:field_simps)
  done
  qed

lemma koTypeOf_pml4e:
  "koTypeOf ko = ArchT PML4ET \<Longrightarrow> \<exists>pml4e. ko = KOArch (KOPML4E pml4e)"
  apply (case_tac ko,simp_all)
  apply (rename_tac arch_kernel_object)
  apply (case_tac arch_kernel_object,simp_all)
  done

lemma doMachineOp_storePML4E_commute:
  "monad_commute (pml4e_at' src) (doMachineOp f)
                 (storePML4E src (new_pml4e::X64_H.pml4e))"
  proof -
  have  eq_fail: "\<And>sa ks. snd (doMachineOp f (sa\<lparr>ksPSpace := ks\<rparr>)) = snd (doMachineOp f sa)"
    apply (clarsimp simp:doMachineOp_def bind_def return_def gets_def
      get_def simpler_modify_def select_def)
    apply (intro iffI)
     apply (elim disjE)
      apply (clarsimp simp:image_def select_f_def)+
    done
  show ?thesis
  apply (rule commute_name_pre_state)
  apply (clarsimp simp:typ_at'_def ko_wp_at'_def)
  apply (case_tac ko,simp_all)
  apply (rename_tac arch_kernel_object)
  apply (case_tac arch_kernel_object,simp_all)
  apply clarsimp
  apply (rename_tac pml4e)
  apply (subgoal_tac "ko_wp_at' ((=) (KOArch (KOPML4E pml4e))) src s")
   prefer 2
   apply (clarsimp simp:ko_wp_at'_def)
  apply (rule monad_commute_guard_imp)
   apply (rule commute_commute)
   apply (rule commute_rewrite[OF storePML4E_det,where R = "\<top>"])
     apply assumption
    apply wp
   apply (clarsimp simp:monad_commute_def simpler_modify_def return_def bind_def)
    apply (intro conjI iffI set_eqI)
       apply (clarsimp simp:doMachineOp_def gets_def bind_def get_def select_f_def return_def)
       apply (erule bexI[rotated])
       apply (clarsimp simp:simpler_modify_def)
      apply (clarsimp simp:doMachineOp_def gets_def bind_def get_def select_f_def return_def)
      apply (erule bexI[rotated])
      apply (clarsimp simp:simpler_modify_def)
     apply (simp add:eq_fail image_def)
     apply (elim disjE)
      apply clarsimp
     apply (clarsimp simp:doMachineOp_def gets_def bind_def get_def select_f_def return_def)
    apply (clarsimp simp:eq_fail)
   apply auto
  done
  qed

lemma storePML4E_placeNewObject_commute:
  "monad_commute
     (pml4e_at' src and pspace_distinct' and pspace_aligned' and
      pspace_no_overlap' ptr (objBitsKO (injectKOS val) + sz) and
      K (is_aligned ptr (objBitsKO (injectKOS val) + sz) \<and>
      objBitsKO (injectKOS val) + sz < word_bits) )
     (placeNewObject ptr val sz) (storePML4E src (new_pml4e::X64_H.pml4e))"
  apply (rule commute_name_pre_state)
  apply (clarsimp simp:typ_at'_def ko_wp_at'_def)
  apply (case_tac ko,simp_all)
  apply (rename_tac arch_kernel_object)
  apply (case_tac arch_kernel_object,simp_all)
  apply clarsimp
  apply (rename_tac pml4e)
  apply (subgoal_tac "ko_wp_at' ((=) (KOArch (KOPML4E pml4e))) src s")
   prefer 2
   apply (clarsimp simp:ko_wp_at'_def)
  apply (subgoal_tac "range_cover ptr (objBitsKO (injectKOS val) + sz) (objBitsKO (injectKOS val) + sz) (Suc 0)")
  prefer 2
   apply (rule range_cover_full)
   apply simp+
  apply (rule monad_commute_guard_imp)
   apply (rule commute_commute)
   apply (rule commute_rewrite[OF storePML4E_det])
      apply assumption
      apply (simp add:placeNewObject_def2)
      apply (wp createObjects_orig_ko_wp_at2')
  apply (rule commute_commute)
  apply (subst modify_specify2[where g = "return",simplified])
  apply (rule_tac commute_rewrite[where Q = "\<lambda>s.
    pspace_no_overlap' ptr (objBitsKO (injectKOS val) + sz) s \<and> pml4e_at' src s
    \<and> pspace_distinct' s \<and> pspace_aligned' s"])
   apply (rule simpler_placeNewObject_def)
      apply simp+
     apply (wp modify_pml4e_psp_no_overlap' modify_pml4e_pspace_distinct'
               modify_pml4e_pspace_aligned' modify_pml4e_pml4e_at')
   apply (simp add: modify_specify modify_mapM_x)
   apply (rule commute_commute[OF mapM_x_commute[where f = id]])
    apply (rule modify_obj_commute)
   apply wp
   apply simp
   apply clarsimp
    apply (intro conjI,simp_all)
     apply (clarsimp simp:typ_at'_def ko_wp_at'_def objBits_simps archObjSize_def)
   apply (rule new_cap_addrs_distinct)
    apply (erule range_cover_rel)
     apply simp+
   apply clarsimp
   apply (simp add:not_in_new_cap_addrs)
   done

lemma cte_wp_at_modify_pml4e:
  notes blah[simp del] =  atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex
          atLeastAtMost_iff
  shows
  "\<lbrakk>ksPSpace s ptr' = Some (KOArch (KOPML4E pml4e)); pspace_aligned' s;cte_wp_at' \<top> ptr s\<rbrakk>
       \<Longrightarrow> cte_wp_at' \<top> ptr (s\<lparr>ksPSpace := (ksPSpace s)(ptr' \<mapsto> (KOArch (KOPML4E pml4e')))\<rparr>)"
  apply (simp add:cte_wp_at_obj_cases_mask obj_at'_real_def)
  apply (frule(1) pspace_alignedD')
  apply (elim disjE)
   apply (rule disjI1)
   apply (clarsimp simp add:ko_wp_at'_def)
   apply (intro conjI impI)
      apply (simp add:objBits_simps archObjSize_def)
     apply (clarsimp simp:projectKO_opt_cte)
    apply (simp add:ps_clear_def)+
    apply (clarsimp simp:objBits_simps archObjSize_def)
   apply (simp add:ps_clear_def)
   apply (rule ccontr)
   apply simp
   apply (erule in_emptyE, blast)
  apply simp
  apply (rule disjI2)
  apply (clarsimp simp:ko_wp_at'_def)
  apply (intro conjI impI)
     apply (simp add:objBits_simps archObjSize_def)+
    apply (clarsimp simp:projectKO_opt_cte projectKO_opt_tcb)
    apply (simp add:ps_clear_def)+
   apply (clarsimp simp:objBits_simps archObjSize_def)
  apply (simp add:ps_clear_def)
  apply (rule ccontr)
  apply simp
  apply (erule in_emptyE)
  apply blast
  done

lemma storePML4E_setCTE_commute:
  notes blah[simp del] =  atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex
          atLeastAtMost_iff
  shows "monad_commute
     (pml4e_at' ptr and pspace_distinct' and pspace_aligned' and
      cte_wp_at' (\<lambda>_. True) src)
     (setCTE src cte) (storePML4E ptr (new_pml4e::X64_H.pml4e))"
  apply (rule commute_name_pre_state)
  apply (clarsimp simp:typ_at'_def ko_wp_at'_def)
  apply (case_tac ko,simp_all)
  apply (rename_tac arch_kernel_object)
  apply (case_tac arch_kernel_object,simp_all)
  apply clarsimp
  apply (rename_tac pml4e)
  apply (subgoal_tac "ko_wp_at' ((=) (KOArch (KOPML4E pml4e))) ptr s")
   prefer 2
   apply (clarsimp simp:ko_wp_at'_def)
  apply (rule monad_commute_guard_imp)
   apply (rule commute_commute)
   apply (rule commute_rewrite[OF storePML4E_det])
     apply assumption
    apply (wp setCTE_pml4e_at')
   apply (simp add:setCTE_def2)
   apply (rule monad_commute_split)
     apply (subst modify_specify)
     apply (rule modify_obj_commute')
    apply (rule commute_commute[OF locateCTE_commute])
         apply (wp locateCTE_cte_no_fail no_fail_modify
                   modify_pml4e_pspace_distinct'
                   modify_pml4e_pspace_aligned'| subst modify_specify)+
     apply (clarsimp simp:simpler_modify_def valid_def typ_at'_def)
     apply (clarsimp simp:ko_wp_at'_def dest!: koTypeOf_pml4e)
     apply (intro conjI impI)
        apply (clarsimp simp:objBits_simps archObjSize_def)+
      apply (simp add:ps_clear_def in_dom_eq)
     apply (simp add:ps_clear_def in_dom_eq)
    apply (clarsimp simp:simpler_modify_def valid_def)
    apply (clarsimp simp:typ_at'_def ko_wp_at'_def)
    apply (case_tac ko,simp_all add:koTypeOf_def )[1]
    apply (rename_tac arch_kernel_object)
    apply (case_tac arch_kernel_object,simp_all add:archTypeOf_def)[1]
    apply (erule(2) cte_wp_at_modify_pml4e)
   apply wp
   apply (thin_tac "cte_wp_at' P src s" for P s)+
   apply (clarsimp simp: typ_at'_def cte_wp_at_obj_cases_mask obj_at'_real_def)
   apply (wp locateCTE_ret_neq locateCTE_ko_wp_at')
  apply (clarsimp simp:ko_wp_at'_def objBits_simps archObjSize_def typ_at'_def)
  apply fastforce
  done

lemma copyGlobalMappings_setCTE_commute:
  "monad_commute
     (valid_arch_state' and pspace_distinct' and pspace_aligned' and
      cte_wp_at' (\<lambda>_. True) src and page_map_l4_at' ptr)
     (copyGlobalMappings ptr) (setCTE src cte)"
  apply (clarsimp simp:copyGlobalMappings_def)
   apply (rule monad_commute_guard_imp)
    apply (rule commute_commute[OF monad_commute_split])
     apply (rule mapM_x_commute[where f = id])
      apply (rule monad_commute_split[OF _ getPML4E_setCTE_commute])
       apply (rule storePML4E_setCTE_commute)
      apply wp+
     apply clarsimp
    apply (rule setCTE_gets_globalPML4_commute)
   apply wp
  apply (clarsimp simp:valid_arch_state'_def page_map_l4_at'_def
         objBits_simps archObjSize_def bit_simps)
  apply (drule le_m1_iff_lt[where x = "(0x200::machine_word)",simplified,THEN iffD1])
  apply clarsimp
  done

lemma setCTE_doMachineOp_commute:
  assumes nf: "no_fail Q (doMachineOp x)"
  shows "monad_commute (cte_at' dest and pspace_aligned' and pspace_distinct' and Q)
  (setCTE dest cte)
  (doMachineOp x)"
  apply (simp add:setCTE_def2 split_def)
  apply (rule monad_commute_guard_imp)
   apply (rule commute_commute[OF monad_commute_split])
     apply (rule doMachineOp_upd_heap_commute)
    apply (rule commute_commute[OF locateCTE_commute])
        apply (wp nf locateCTE_cte_no_fail)+
       apply clarsimp
  apply (wp|clarsimp|fastforce)+
  done

lemma placeNewObject_valid_arch_state:
  "\<lbrace>valid_arch_state' and
    pspace_no_overlap' ptr (objBitsKO (injectKOS val) + us) and
    pspace_aligned' and pspace_distinct' and
    K (is_aligned ptr (objBitsKO (injectKOS val) + us)) and
    K ( (objBitsKO (injectKOS val)+ us)< word_bits)\<rbrace>
   placeNewObject ptr val us
   \<lbrace>\<lambda>rv s. valid_arch_state' s\<rbrace>"
  apply (simp add:placeNewObject_def2 split_def)
  apply (rule createObjects'_wp_subst)
  apply (wp createObjects_valid_arch)
  apply clarsimp
  apply (intro conjI,simp)
  apply (erule(1) range_cover_full)
  done

lemma placeNewObject_pml4_at':
  "\<lbrace>K (is_aligned ptr pml4Bits) and pspace_no_overlap' ptr pml4Bits and
    pspace_aligned' and pspace_distinct'\<rbrace>
   placeNewObject ptr (makeObject::X64_H.pml4e)
                      (pml4Bits - objBits (makeObject::X64_H.pml4e))
   \<lbrace>\<lambda>rv s. page_map_l4_at' ptr s\<rbrace>"
  apply (simp add:page_map_l4_at'_def typ_at'_def)
  apply (rule hoare_pre)
   apply (wp hoare_vcg_all_lift hoare_vcg_imp_lift placeNewObject_ko_wp_at')
  apply (clarsimp simp:objBits_simps archObjSize_def)
  apply (intro conjI)
   apply (clarsimp simp: bit_simps word_bits_def)+
  apply (clarsimp simp:pdBits_def pageBits_def new_cap_addrs_def objBits_simps archObjSize_def image_def)
  apply (drule_tac x = "unat x" in bspec)
   apply clarsimp
   apply (rule unat_less_helper)
   apply simp
  apply simp
  done

lemma setCTE_modify_gsCNode_commute:
  "monad_commute P (setCTE src (cte::cte))
                   (modify (%ks. ks\<lparr>gsCNodes := f (gsCNodes ks)\<rparr>))"
  by (auto simp: monad_commute_def setCTE_def setObject_def split_def bind_def
                 return_def simpler_modify_def simpler_gets_def assert_opt_def
                 fail_def simpler_updateObject_def
           split: option.splits if_split_asm)

lemma setCTE_modify_gsUserPages_commute:
  "monad_commute P (setCTE src (cte::cte))
                   (modify (%ks. ks\<lparr>gsUserPages := f (gsUserPages ks)\<rparr>))"
  by (auto simp: monad_commute_def setCTE_def setObject_def split_def bind_def
                 return_def simpler_modify_def simpler_gets_def assert_opt_def
                 fail_def simpler_updateObject_def
           split: option.splits if_split_asm)

lemma getTCB_det:
  "ko_wp_at' ((=) (KOTCB tcb)) p s
   \<Longrightarrow> getObject p s = ({(tcb,s)},False)"
  apply (clarsimp simp:ko_wp_at'_def getObject_def split_def
                       bind_def gets_def return_def get_def
                       assert_opt_def split:if_splits)
  apply (clarsimp simp: fail_def return_def lookupAround2_known1)
   apply (simp add:loadObject_default_def)
  apply (clarsimp simp:projectKO_def projectKO_opt_tcb alignCheck_def
    is_aligned_mask objBits_simps' unless_def)
  apply (clarsimp simp:bind_def return_def)
  apply (intro conjI)
   apply (intro set_eqI iffI)
    apply clarsimp
    apply (subst (asm) in_magnitude_check')
     apply (simp add:archObjSize_def is_aligned_mask)+
    apply (rule bexI[rotated])
     apply (rule in_magnitude_check'[THEN iffD2])
      apply (simp add:is_aligned_mask)+
   apply (clarsimp simp:image_def)
  apply (clarsimp simp:magnitudeCheck_assert assert_def
    objBits_def archObjSize_def
    return_def fail_def lookupAround2_char2 split:option.splits if_split_asm)
  apply (rule ccontr)
  apply (simp add:ps_clear_def field_simps)
  apply (erule_tac x = x2 in in_empty_interE)
   apply (clarsimp simp:less_imp_le)
   apply (rule conjI)
    apply (subst add.commute)
    apply (rule word_diff_ls')
     apply (clarsimp simp:field_simps not_le plus_one_helper)
    apply (simp add:field_simps is_aligned_no_wrap' is_aligned_mask)
   apply simp
  apply auto
  done

lemma threadSet_det:
  "tcb_at' ptr s
  \<Longrightarrow> threadSet f ptr s =
  modify (ksPSpace_update (\<lambda>ps. ps(ptr \<mapsto>
    (\<lambda>t. case t of Some (KOTCB tcb) \<Rightarrow> KOTCB (f tcb)) (ps ptr)))) s"
  apply (clarsimp simp add:threadSet_def bind_def obj_at'_def)
  apply (clarsimp simp:projectKO_eq projectKO_opt_tcb
    split: Structures_H.kernel_object.splits)
  apply (subst getTCB_det,simp add:ko_wp_at'_def)+
  apply (clarsimp simp:setObject_def gets_def get_def)
  apply (subst bind_def)
  apply (clarsimp simp:split_def)
  apply (simp add:lookupAround2_known1 bind_assoc projectKO_def
    assert_opt_def updateObject_default_def projectKO_opt_tcb)
  apply (clarsimp simp add:
    alignCheck_def unless_def when_def
    is_aligned_mask objBits_simps)
  apply (clarsimp simp:magnitudeCheck_det bind_def)
  apply (cut_tac ko = "KOTCB obj" in magnitudeCheck_det)
   apply (simp add:objBits_simps is_aligned_mask)+
  apply (clarsimp simp:modify_def get_def put_def bind_def)
  done


lemma setCTE_modify_tcbDomain_commute:
 " monad_commute
    (tcb_at' ptr and cte_wp_at' (\<lambda>_. True) src and pspace_distinct' and pspace_aligned') (setCTE src cte)
    (threadSet (tcbDomain_update (\<lambda>_. ra)) ptr)"
  proof -
    note blah[simp del] =  atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex
          atLeastAtMost_iff

    have hint:
      "\<And>P ptr a cte b src ra. monad_commute (tcb_at' ptr and ko_wp_at' P a )
      (threadSet (tcbDomain_update (\<lambda>_. ra)) ptr)
             (modify (ksPSpace_update (\<lambda>ps. ps(a \<mapsto> cte_update cte (the (ps a)) src a))))"
      apply (clarsimp simp add: monad_commute_def
        bind_def simpler_modify_def return_def)
      apply (clarsimp simp:threadSet_det simpler_modify_def)
      apply (subgoal_tac "tcb_at' ptr (ksPSpace_update (\<lambda>ps. ps(a \<mapsto> cte_update cte (the (ps a)) src a)) s)")
      prefer 2
       apply (clarsimp simp:obj_at'_def)
       apply (intro conjI impI)
           apply simp
          apply (clarsimp simp:projectKO_eq
            projectKO_opt_tcb split:Structures_H.kernel_object.split_asm)
          apply (simp add:cte_update_def)
         apply (clarsimp simp:projectKO_eq
           projectKO_opt_tcb split:Structures_H.kernel_object.split_asm)
         apply (simp add:ps_clear_def)
        apply (clarsimp simp:projectKO_eq
          projectKO_opt_tcb split:Structures_H.kernel_object.split_asm)
       apply (simp add:ps_clear_def)
       apply (rule ccontr,simp)
       apply (erule in_emptyE)
       apply (clarsimp simp:ko_wp_at'_def)
       apply blast
      apply (simp add:threadSet_det simpler_modify_def)
      apply (subst (asm) obj_at'_def)
      apply (thin_tac "tcb_at' ptr P" for P)
      apply (clarsimp simp: obj_at'_def projectKO_eq projectKO_opt_tcb,
             simp split: Structures_H.kernel_object.split_asm)
      apply (case_tac s,clarsimp)
      apply (intro conjI)
       apply clarsimp
       apply (rule ext,clarsimp)
       apply (case_tac obj)
       apply (simp add:cte_update_def)
      apply clarsimp
      apply (rule ext)
      apply simp
      done

  show ?thesis
  apply (rule commute_name_pre_state)
  apply (clarsimp simp add: setCTE_def2)
  apply (rule monad_commute_guard_imp)
   apply (rule commute_commute[OF  monad_commute_split])
     apply (rule hint)
    apply (rule commute_commute)
    apply (rule locateCTE_commute)
         apply (wp locateCTE_cte_no_fail)+
     apply (wp threadSet_ko_wp_at2')
     apply (clarsimp simp:objBits_simps)
    apply (wp|simp)+
   apply (wp locateCTE_inv locateCTE_ko_wp_at')
  apply clarsimp
  apply fastforce
  done
qed

lemma curDomain_commute:
  assumes cur:"\<And>P. \<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace> f \<lbrace>\<lambda>r s. P (ksCurDomain s)\<rbrace>"
  shows "monad_commute \<top> f curDomain"
  apply (clarsimp simp add:monad_commute_def curDomain_def get_def return_def
    gets_def bind_def)
  apply (rule conjI)
   apply (rule set_eqI)
   apply (rule iffI)
    apply clarsimp
    apply (rule bexI[rotated], assumption)
    apply clarsimp
    apply (frule_tac P1 = "\<lambda>x. x = ksCurDomain s" in use_valid[OF _ cur])
      apply simp+
   apply clarsimp
   apply (rule bexI[rotated], assumption)
   apply clarsimp
   apply (frule_tac P1 = "\<lambda>x. x = ksCurDomain s" in use_valid[OF _ cur])
    apply simp+
  apply auto
  done

crunches curDomain
  for inv[wp]: P

lemma placeNewObject_tcb_at':
  notes [simp del] = atLeastatMost_subset_iff atLeastLessThan_iff
                     Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex atLeastAtMost_iff
  shows "\<lbrace> pspace_aligned' and pspace_distinct'
             and pspace_no_overlap' ptr (objBits (makeObject::tcb))
             and  K(is_aligned ptr  (objBits (makeObject::tcb))) \<rbrace>
         placeNewObject ptr (makeObject::tcb) 0
         \<lbrace>\<lambda>_ s. tcb_at' ptr s \<rbrace>"
  apply (simp add: placeNewObject_def placeNewObject'_def split_def)
  apply (wp unless_wp |wpc | simp add:alignError_def)+
  by (auto simp: obj_at'_def is_aligned_mask lookupAround2_None1
                    lookupAround2_char1 field_simps objBits_simps
                    projectKO_opt_tcb projectKO_def return_def ps_clear_def
           split: if_splits
           dest!: pspace_no_overlap_disjoint')

lemma monad_commute_if_weak_r:
"\<lbrakk>monad_commute P1 f h1; monad_commute P2 f h2\<rbrakk> \<Longrightarrow>
  monad_commute (P1 and P2) f (if d then h1 else h2)"
  apply (clarsimp)
  apply (intro conjI impI)
   apply (erule monad_commute_guard_imp,simp)+
  done



lemma createObject_setCTE_commute:
  "monad_commute
     (cte_wp_at' (\<lambda>_. True) src and
        pspace_aligned' and pspace_distinct' and
        pspace_no_overlap' ptr (Types_H.getObjectSize ty us) and
        valid_arch_state' and K (ptr \<noteq> src) and
        K (is_aligned ptr (Types_H.getObjectSize ty us)) and
        K (Types_H.getObjectSize ty us < word_bits))
     (RetypeDecls_H.createObject ty ptr us d)
     (setCTE src cte)"
  apply (rule commute_grab_asm)+
  apply (subgoal_tac "ptr && mask (Types_H.getObjectSize ty us) = 0")
   prefer 2
   apply (clarsimp simp: range_cover_def is_aligned_mask)
  apply (clarsimp simp: createObject_def)
  apply (case_tac ty,
         simp_all add: X64_H.toAPIType_def)
        apply (rename_tac apiobject_type)
        apply (case_tac apiobject_type)
            apply (simp_all add:
                       X64_H.getObjectSize_def apiGetObjectSize_def
                       tcbBlockSizeBits_def epSizeBits_def ntfnSizeBits_def
                       cteSizeBits_def)
            \<comment> \<open>Untyped\<close>
            apply (simp add: monad_commute_guard_imp[OF return_commute])
           \<comment> \<open>TCB, EP, NTFN\<close>
           apply (rule monad_commute_guard_imp[OF commute_commute])
            apply (rule monad_commute_split[OF monad_commute_split])
                apply (rule monad_commute_split[OF commute_commute[OF return_commute]])
                 apply (rule setCTE_modify_tcbDomain_commute)
                apply wp
               apply (rule curDomain_commute)
               apply wp+
             apply (rule setCTE_placeNewObject_commute)
            apply (wp  placeNewObject_tcb_at' placeNewObject_cte_wp_at'
              placeNewObject_pspace_distinct'
              placeNewObject_pspace_aligned'
              | clarsimp simp: objBits_simps')+
           apply (rule monad_commute_guard_imp[OF commute_commute]
            ,rule monad_commute_split[OF commute_commute[OF return_commute]]
            ,rule setCTE_placeNewObject_commute
            ,(wp|clarsimp simp: objBits_simps')+)+
        \<comment> \<open>CNode\<close>
        apply (rule monad_commute_guard_imp[OF commute_commute])
         apply (rule monad_commute_split)+
             apply (rule return_commute[THEN commute_commute])
            apply (rule setCTE_modify_gsCNode_commute[of \<top>])
           apply (rule hoare_triv[of \<top>])
           apply wp
          apply (rule setCTE_placeNewObject_commute)
         apply (wp|clarsimp simp: objBits_simps')+
       \<comment> \<open>Arch Objects\<close>
       apply ((rule monad_commute_guard_imp[OF commute_commute]
              , rule monad_commute_split[OF commute_commute[OF return_commute]]
              , clarsimp simp: X64_H.createObject_def
                               placeNewDataObject_def bind_assoc split
                          del: if_splits
              ,(rule monad_commute_split return_commute[THEN commute_commute]
                     setCTE_modify_gsUserPages_commute[of \<top>]
                     modify_wp[of "%_. \<top>"]
                     setCTE_doMachineOp_commute
                     setCTE_placeNewObject_commute
                     monad_commute_if_weak_r
                     copyGlobalMappings_setCTE_commute[THEN commute_commute]
                 | wp placeNewObject_pspace_distinct'
                      placeNewObject_pspace_aligned'
                      placeNewObject_cte_wp_at'
                      placeNewObject_valid_arch_state
                      placeNewObject_pml4_at'[simplified bitSimps objBits_simps archObjSize_def, simplified]
                 | erule is_aligned_weaken
                 | simp add: objBits_simps word_bits_def bit_simps
                             archObjSize_def split del: if_splits)+)+)
  done


lemma createObject_updateMDB_commute:
  "monad_commute
     ((\<lambda>s. src \<noteq> 0 \<longrightarrow> cte_wp_at' (\<lambda>_. True) src s) and
      pspace_no_overlap' ptr (Types_H.getObjectSize ty us) and
      pspace_aligned' and pspace_distinct' and valid_arch_state' and
      K (ptr \<noteq> src) and
      K (is_aligned ptr (Types_H.getObjectSize ty us)) and
      K ((Types_H.getObjectSize ty us)< word_bits))
     (updateMDB src f) (RetypeDecls_H.createObject ty ptr us d)"
  apply (clarsimp simp:updateMDB_def split:if_split_asm)
  apply (intro conjI impI)
   apply (simp add: monad_commute_guard_imp[OF return_commute])
  apply (rule monad_commute_guard_imp)
   apply (rule commute_commute[OF monad_commute_split])
     apply (rule createObject_setCTE_commute)
    apply (rule createObject_getCTE_commute)
   apply wp
  apply (auto simp:range_cover_full)
  done

lemma updateMDB_pspace_no_overlap':
  "\<lbrace>pspace_aligned' and pspace_distinct' and pspace_no_overlap' ptr sz\<rbrace>
   updateMDB slot f
   \<lbrace>\<lambda>rv s. pspace_no_overlap' ptr sz s\<rbrace>"
  apply (rule hoare_pre)
  apply (clarsimp simp: updateMDB_def split del: if_split)
  apply (wp setCTE_pspace_no_overlap')
  apply clarsimp
  done

lemma ctes_of_ko_at:
  "ctes_of s p = Some a \<Longrightarrow>
  (\<exists>ptr ko. (ksPSpace s ptr = Some ko \<and> p \<in> obj_range' ptr ko))"
  apply (clarsimp simp: map_to_ctes_def Let_def split: if_split_asm)
   apply (intro exI conjI, assumption)
   apply (simp add: obj_range'_def objBits_simps' add.commute)
   apply (simp add: is_aligned_no_wrap')
  apply (intro exI conjI, assumption)
  apply (clarsimp simp: objBits_simps' obj_range'_def word_and_le2)
  apply (thin_tac "P" for P)+
  apply (simp add: mask_def)
  apply word_bitwise
  done

lemma pspace_no_overlapD2':
  "\<lbrakk>is_aligned ptr sz; pspace_no_overlap' ptr sz s;sz < word_bits;
    ctes_of s slot = Some cte\<rbrakk>
   \<Longrightarrow> slot \<noteq> ptr"
   apply (drule ctes_of_ko_at)
   apply clarsimp
   apply (drule(1) pspace_no_overlapD')
   apply (erule in_empty_interE)
    apply (simp add:obj_range'_def)
    apply clarsimp
    apply (subst is_aligned_neg_mask_eq[symmetric])
    apply simp
   apply (simp add: is_aligned_no_overflow)
   done

lemma caps_overlap_reserved'_subseteq:
  "\<lbrakk>caps_overlap_reserved' B s; A\<subseteq> B\<rbrakk> \<Longrightarrow> caps_overlap_reserved' A s"
  apply (clarsimp simp:caps_overlap_reserved'_def)
  apply (drule(1) bspec)
  apply (erule disjoint_subset2)
  apply simp
  done

definition weak_valid_dlist where
  "weak_valid_dlist \<equiv> \<lambda>m.
  (\<forall>p cte.
   m p = Some cte \<longrightarrow>
   (let next = mdbNext (cteMDBNode cte)
    in (next \<noteq> 0 \<longrightarrow> (\<exists>cte'. m next = Some cte' \<and> cteCap cte'\<noteq> capability.NullCap))))"

lemma valid_arch_state'_updateMDB:
  "\<lbrace>valid_arch_state' \<rbrace> updateMDB a b \<lbrace>\<lambda>rv. valid_arch_state'\<rbrace>"
  by (clarsimp simp:updateMDB_def valid_arch_state_def,wp)

lemma fail_commute:
  "monad_commute \<top> fail f = empty_fail f"
  apply (simp add: monad_commute_def empty_fail_def)
  apply (simp add: fail_def bind_def del: split_paired_Ex)
  apply blast
  done

lemma modify_commute:
  "monad_commute P (modify f) (modify g)
    = (\<forall>s. P s \<longrightarrow> f (g s) = g (f s))"
  apply (simp add: monad_commute_def exec_modify)
  apply (simp add: return_def eq_commute)
  done

lemma createObjects_gsUntypedZeroRanges_commute':
  "monad_commute \<top>
     (createObjects' ptr n ko us)
     (modify (\<lambda>s. s \<lparr> gsUntypedZeroRanges := f (gsUntypedZeroRanges s) \<rparr> ))"
  apply (simp add: createObjects'_def unless_def when_def alignError_def
                   fail_commute)
  apply clarsimp
  apply (rule commute_commute)
  apply (strengthen monad_commute_guard_imp[OF monad_commute_split[where P="\<top>" and Q="\<top>\<top>"], OF _ _ hoare_vcg_prop]
     | simp add: modify_commute split: option.split prod.split)+
  apply (simp add: monad_commute_def exec_modify exec_gets assert_def)
  done

lemma assert_commute2: "empty_fail f
    \<Longrightarrow> monad_commute \<top> (assert G) f"
  apply (clarsimp simp:assert_def monad_commute_def)
  apply (simp add: fail_def bind_def empty_fail_def del: split_paired_Ex)
  apply blast
  done

lemma threadSet_gsUntypedZeroRanges_commute':
  "monad_commute \<top>
     (threadSet fn ptr)
     (modify (\<lambda>s. s \<lparr> gsUntypedZeroRanges := f (gsUntypedZeroRanges s) \<rparr> ))"
  apply (simp add: threadSet_def getObject_def setObject_def)
  apply (rule commute_commute)
  apply (strengthen monad_commute_guard_imp[OF monad_commute_split[where P="\<top>" and Q="\<top>\<top>"], OF _ _ hoare_vcg_prop]
     | simp add: modify_commute updateObject_default_def alignCheck_assert
                 magnitudeCheck_assert return_commute return_commute[THEN commute_commute]
                 projectKO_def2 assert_commute2 assert_commute2[THEN commute_commute]
                 assert_opt_def2 loadObject_default_def
          split: option.split prod.split)+
  apply (simp add: monad_commute_def exec_gets exec_modify)
  done

lemma copyGlobalMappings_gsUntypedZeroRanges_commute':
  "monad_commute \<top>
     (copyGlobalMappings ptr)
     (modify (\<lambda>s. s \<lparr> gsUntypedZeroRanges := f (gsUntypedZeroRanges s) \<rparr> ))"
  apply (simp add: copyGlobalMappings_def)
  apply (rule monad_commute_guard_imp)
   apply (rule commute_commute[OF monad_commute_split[where P="\<top>"]])
     apply (rule mapM_x_commute[where f = id and P="\<top>\<top>"])
      apply (simp add: storePML4E_def getObject_def setObject_def cong: bind_cong)
      apply (strengthen monad_commute_guard_imp[OF monad_commute_split[where P="\<top>" and Q="\<top>\<top>"], OF _ _ hoare_vcg_prop]
         | simp add: modify_commute updateObject_default_def alignCheck_assert
                     magnitudeCheck_assert return_commute return_commute[THEN commute_commute]
                     projectKO_def2 assert_commute2 assert_commute2[THEN commute_commute]
                     assert_opt_def2 loadObject_default_def
              split: option.split prod.split)+
      apply (simp add: monad_commute_def exec_gets exec_modify)
     apply wp
    apply (simp add: monad_commute_def exec_gets exec_modify)
   apply wp
  apply simp
  done

lemma createObject_gsUntypedZeroRanges_commute:
  "monad_commute
     \<top>
     (RetypeDecls_H.createObject ty ptr us dev)
     (modify (\<lambda>s. s \<lparr> gsUntypedZeroRanges := f (gsUntypedZeroRanges s) \<rparr> ))"
  apply (simp add: createObject_def X64_H.createObject_def
                   placeNewDataObject_def
                   placeNewObject_def2 bind_assoc fail_commute
                   return_commute toAPIType_def
    split: option.split apiobject_type.split object_type.split)
  apply (strengthen monad_commute_guard_imp[OF monad_commute_split[where P="\<top>" and Q="\<top>\<top>"],
          OF _ _ hoare_vcg_prop, THEN commute_commute]
      monad_commute_guard_imp[OF monad_commute_split[where P="\<top>" and Q="\<top>\<top>"],
          OF _ _ hoare_vcg_prop]
     | simp add: modify_commute createObjects_gsUntypedZeroRanges_commute'
                 createObjects_gsUntypedZeroRanges_commute'[THEN commute_commute]
                 return_commute return_commute[THEN commute_commute]
                 threadSet_gsUntypedZeroRanges_commute'[THEN commute_commute]
                 copyGlobalMappings_gsUntypedZeroRanges_commute'[THEN commute_commute]
          split: option.split prod.split cong: if_cong)+
  apply (simp add: curDomain_def monad_commute_def exec_modify exec_gets)
  done

lemma monad_commute_If_rhs:
  "monad_commute P a b \<Longrightarrow> monad_commute Q a c
    \<Longrightarrow> monad_commute (\<lambda>s. (R \<longrightarrow> P s) \<and> (\<not> R \<longrightarrow> Q s)) a (if R then b else c)"
  by simp

lemma case_eq_if_isUntypedCap:
  "(case c of UntypedCap _ _ _ _ \<Rightarrow> x | _ \<Rightarrow> y)
    = (if isUntypedCap c then x else y)"
  by (cases c, simp_all add: isCap_simps)

lemma createObject_updateTrackedFreeIndex_commute:
  "monad_commute
     (cte_wp_at' (\<lambda>_. True) slot and pspace_aligned' and pspace_distinct' and
      pspace_no_overlap' ptr (Types_H.getObjectSize ty us) and
      valid_arch_state' and
      K (ptr \<noteq> slot) and K (Types_H.getObjectSize ty us < word_bits) and
      K (is_aligned ptr (Types_H.getObjectSize ty us)))
     (RetypeDecls_H.createObject ty ptr us dev) (updateTrackedFreeIndex slot idx)"
  apply (simp add: updateTrackedFreeIndex_def getSlotCap_def updateCap_def)
  apply (rule monad_commute_guard_imp)
   apply (rule monad_commute_split[OF _ createObject_getCTE_commute]
               monad_commute_split[OF _ createObject_gsUntypedZeroRanges_commute]
               createObject_gsUntypedZeroRanges_commute)+
    apply (wp getCTE_wp')+
  apply (clarsimp simp: pspace_no_overlap'_def)
  done

lemma createObject_updateNewFreeIndex_commute:
  "monad_commute
     (cte_wp_at' (\<lambda>_. True) slot and pspace_aligned' and pspace_distinct' and
      pspace_no_overlap' ptr (Types_H.getObjectSize ty us) and
      valid_arch_state' and
      K (ptr \<noteq> slot) and K (Types_H.getObjectSize ty us < word_bits) and
      K (is_aligned ptr (Types_H.getObjectSize ty us)))
     (RetypeDecls_H.createObject ty ptr us dev) (updateNewFreeIndex slot)"
  apply (simp add: updateNewFreeIndex_def getSlotCap_def case_eq_if_isUntypedCap
                   updateTrackedFreeIndex_def)
  apply (rule monad_commute_guard_imp)
   apply (rule monad_commute_split[OF _ createObject_getCTE_commute])
    apply (rule monad_commute_If_rhs)
     apply (rule createObject_updateTrackedFreeIndex_commute)
    apply (rule commute_commute[OF return_commute])
   apply (wp getCTE_wp')
  apply clarsimp
  done

lemma new_cap_object_comm_helper:
  "monad_commute
     (pspace_aligned' and pspace_distinct' and (\<lambda>s. no_0 (ctes_of s)) and
      (\<lambda>s. weak_valid_dlist (ctes_of s)) and
      (\<lambda>s. valid_nullcaps (ctes_of s)) and
      cte_wp_at' (\<lambda>c. isUntypedCap (cteCap c)) parent and
      cte_wp_at' (\<lambda>c. cteCap c = capability.NullCap) slot and
      pspace_no_overlap' ptr (Types_H.getObjectSize ty us) and
      valid_arch_state' and
      K (Types_H.getObjectSize ty us<word_bits) and
      K (cap \<noteq> capability.NullCap) and
      K (is_aligned ptr (Types_H.getObjectSize ty us) \<and> ptr \<noteq> 0 \<and> parent \<noteq> 0))
     (RetypeDecls_H.createObject ty ptr us d) (insertNewCap parent slot cap)"
  apply (clarsimp simp:insertNewCap_def bind_assoc liftM_def)
  apply (rule monad_commute_guard_imp)
   apply (rule monad_commute_split[OF _ createObject_getCTE_commute])+
    apply (rule monad_commute_split[OF _ commute_commute[OF assert_commute]])
     apply (rule monad_commute_split[OF _ createObject_setCTE_commute])
      apply (rule monad_commute_split[OF _ commute_commute[OF createObject_updateMDB_commute]])
       apply (rule monad_commute_split[OF _ commute_commute[OF createObject_updateMDB_commute]])
        apply (rule createObject_updateNewFreeIndex_commute)
       apply (wp getCTE_wp hoare_vcg_imp_lift hoare_vcg_disj_lift valid_arch_state'_updateMDB
         updateMDB_pspace_no_overlap' setCTE_pspace_no_overlap'
         | clarsimp simp:conj_comms)+
  apply (clarsimp simp:cte_wp_at_ctes_of)
  apply (frule_tac slot = slot in pspace_no_overlapD2')
   apply simp+
  apply (frule_tac slot = parent in pspace_no_overlapD2')
   apply simp+
  apply (case_tac ctea,clarsimp)
  apply (frule_tac p = slot in nullcapsD')
     apply simp+
  apply (subgoal_tac "(mdbNext (cteMDBNode cte) = 0 \<or>
           (\<exists>ctea. ctes_of s (mdbNext (cteMDBNode cte)) = Some ctea))")
   apply (elim disjE)
    apply clarsimp+
    apply (frule_tac slot = "(mdbNext (cteMDBNode cte))"
      in pspace_no_overlapD2')
    apply simp+
  apply (clarsimp simp:weak_valid_dlist_def)
  apply (drule_tac x = "parent " in spec)
   apply clarsimp
  done

crunches updateNewFreeIndex
  for pspace_aligned'[wp]: "pspace_aligned'"
crunches updateNewFreeIndex
  for pspace_canonical'[wp]: "pspace_canonical'"
crunches updateNewFreeIndex
  for pspace_in_kernel_mappings'[wp]: "pspace_in_kernel_mappings'"
crunches updateNewFreeIndex
  for pspace_distinct'[wp]: "pspace_distinct'"
crunches updateNewFreeIndex
  for valid_arch_state'[wp]: "valid_arch_state'"
crunches updateNewFreeIndex
  for pspace_no_overlap'[wp]: "pspace_no_overlap' ptr n"
crunches updateNewFreeIndex
  for ctes_of[wp]: "\<lambda>s. P (ctes_of s)"

lemma updateNewFreeIndex_cte_wp_at[wp]:
  "\<lbrace>\<lambda>s. P (cte_wp_at' P' p s)\<rbrace> updateNewFreeIndex slot \<lbrace>\<lambda>rv s. P (cte_wp_at' P' p s)\<rbrace>"
  by (simp add: cte_wp_at_ctes_of, wp)

lemma new_cap_object_commute:
  "monad_commute
     (cte_wp_at' (\<lambda>c. isUntypedCap (cteCap c)) parent and
      (\<lambda>s. \<forall>slot\<in>set list. cte_wp_at' (\<lambda>c. cteCap c = capability.NullCap) slot s) and
      pspace_no_overlap' ptr (Types_H.getObjectSize ty us) and
      valid_pspace' and valid_arch_state' and
      K (distinct (map fst (zip list caps))) and
      K (\<forall>cap \<in> set caps. cap \<noteq> capability.NullCap) and
      K (Types_H.getObjectSize ty us <word_bits) and
      K (is_aligned ptr (Types_H.getObjectSize ty us) \<and> ptr \<noteq> 0))
     (RetypeDecls_H.createObject ty ptr us d)
     (zipWithM_x (insertNewCap parent) list caps)"
  apply (clarsimp simp:zipWithM_x_mapM_x)
  apply (rule monad_commute_guard_imp)
   apply (rule mapM_x_commute[where f = fst])
    apply (simp add:split_def)
    apply (rule new_cap_object_comm_helper)
   apply (clarsimp simp:insertNewCap_def split_def)
   apply (wp updateMDB_weak_cte_wp_at updateMDB_pspace_no_overlap'
             getCTE_wp valid_arch_state'_updateMDB
             setCTE_weak_cte_wp_at setCTE_pspace_no_overlap')
   apply (clarsimp simp:cte_wp_at_ctes_of simp del:fun_upd_apply)
   apply (case_tac "parent \<noteq> aa")
    prefer 2
    apply simp
   apply (clarsimp simp: conj_comms)
   apply (intro conjI exI)
     apply (clarsimp simp: no_0_def)
    apply (clarsimp simp: weak_valid_dlist_def modify_map_def Let_def)
    subgoal by (intro conjI impI; fastforce)
   apply (clarsimp simp:valid_nullcaps_def)
   apply (frule_tac x = "p" in spec)
   apply (case_tac ctec)
   apply (case_tac cte)
   apply (rename_tac cap' node')
   apply (case_tac node')
   apply (rename_tac word1 word2 bool1 bool2)
   apply (clarsimp simp:modify_map_def split:if_split_asm)
   apply (case_tac z)
   apply (drule_tac x = word1 in spec)
   apply (clarsimp simp:weak_valid_dlist_def)
   apply (drule_tac x = parent in spec)
   apply clarsimp
  apply (clarsimp simp:valid_pspace'_def valid_mdb'_def valid_mdb_ctes_def)
  apply (intro conjI)
     apply (clarsimp simp:weak_valid_dlist_def Let_def)
     apply (frule(2) valid_dlist_nextD)
     apply clarsimp
     apply (case_tac cte')
     apply clarsimp
     apply (drule_tac m = "ctes_of s" in nullcapsD')
      apply simp
      apply (clarsimp simp: no_0_def nullPointer_def)
    apply (erule in_set_zipE)
    apply clarsimp
    apply (erule in_set_zipE)
   apply clarsimp
   apply (clarsimp simp:cte_wp_at_ctes_of)
  done

lemma createObjects'_pspace_no_overlap:
  "gz = (objBitsKO val) + us \<Longrightarrow>
   \<lbrace>pspace_no_overlap' (ptr + (1 + of_nat n << gz)) gz and
    K (range_cover ptr sz gz (Suc (Suc n)) \<and> ptr \<noteq> 0)\<rbrace>
   createObjects' ptr (Suc n) val us
   \<lbrace>\<lambda>addrs s. pspace_no_overlap' (ptr + (1 + of_nat n << gz)) gz s\<rbrace>"
proof -
  note simps [simp del] = untyped_range.simps usable_untyped_range.simps atLeastAtMost_iff
                          atLeastatMost_subset_iff atLeastLessThan_iff
                          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex
  assume "gz = (objBitsKO val) + us"
  thus ?thesis
    apply -
    apply (rule hoare_gen_asm)
    apply (clarsimp simp:createObjects'_def split_def new_cap_addrs_fold')
    apply (subst new_cap_addrs_fold')
     apply clarsimp
     apply (drule range_cover_le[where n = "Suc n"])
      apply simp
     apply (drule_tac gbits = us in range_cover_not_zero_shift[rotated])
       apply simp+
     apply (simp add:word_le_sub1)
    apply (wp haskell_assert_wp unless_wp | wpc
        | simp add:alignError_def if_apply_def2 del: fun_upd_apply hoare_fail_any)+
    apply (rule impI)
    apply (subgoal_tac
      "pspace_no_overlap' (ptr + (1 + of_nat n << objBitsKO val + us))
       (objBitsKO val + us)
       (s\<lparr>ksPSpace := foldr (\<lambda>addr map. map(addr \<mapsto> val))
                      (new_cap_addrs (unat (1 + of_nat n << us)) ptr val) (ksPSpace s)\<rparr>)")
     apply (intro conjI impI allI)
      apply assumption+
    apply (subst pspace_no_overlap'_def)
    apply (intro allI impI)
    apply (subst (asm) foldr_upd_app_if)
    apply (subst is_aligned_neg_mask_eq)
     apply (rule aligned_add_aligned[OF range_cover.aligned],assumption)
      apply (rule is_aligned_shiftl_self)
     apply (simp add:range_cover_def)
    apply simp
    apply (clarsimp split:if_splits)
     apply (drule obj_range'_subset_strong[rotated])
      apply (rule range_cover_rel[OF range_cover_le[where n = "Suc n"]],assumption)
        apply simp
       apply simp
      apply (drule range_cover.unat_of_nat_n_shift
        [OF range_cover_le[where n = "Suc n"],where gbits = us])
        apply simp
       apply (simp add:shiftl_t2n field_simps)+
     apply (simp add:obj_range'_def)
     apply (erule disjoint_subset)
     apply (clarsimp simp: simps)
     apply (thin_tac "x \<le> y" for x y)
     apply (subst (asm) le_m1_iff_lt[THEN iffD1])
      apply (drule_tac range_cover_no_0[rotated,where p = "Suc n"])
        apply simp
        apply simp
       apply (simp add:field_simps)
      apply (simp add: power_add[symmetric])
      apply (simp add: word_neq_0_conv)
     apply (simp add: power_add[symmetric] field_simps)
    apply (frule range_cover_subset[where p = "Suc n"])
      apply simp
      apply simp
     apply (drule(1) pspace_no_overlapD')
    apply (subst (asm) is_aligned_neg_mask_eq)
     apply (rule aligned_add_aligned[OF range_cover.aligned],assumption)
      apply (rule is_aligned_shiftl_self)
     apply (simp add:range_cover_def)
    apply simp
    apply (simp add:word_le_sub1 shiftl_t2n field_simps)
    done
qed

lemma createNewCaps_not_nc:
  "\<lbrace>\<top>\<rbrace> createNewCaps ty ptr (Suc (length as)) us d \<lbrace>\<lambda>r s. (\<forall>cap\<in>set r. cap \<noteq> NullCap)\<rbrace>"
  unfolding createNewCaps_def Arch_createNewCaps_def
  by (wpsimp simp: Arch_createNewCaps_def split_del: if_split)

lemma doMachineOp_psp_no_overlap:
  "\<lbrace>\<lambda>s. pspace_no_overlap' ptr sz s \<and> pspace_aligned' s \<and> pspace_distinct' s \<rbrace>
   doMachineOp f
   \<lbrace>\<lambda>y s. pspace_no_overlap' ptr sz s\<rbrace>"
  by (wp pspace_no_overlap'_lift,simp)

lemma createObjects'_psp_distinct:
  "\<lbrace>pspace_aligned' and pspace_distinct' and
    pspace_no_overlap' ptr sz and
    K (range_cover ptr sz ((objBitsKO ko) + us) n \<and> n \<noteq> 0
    \<and> is_aligned ptr (objBitsKO ko + us) \<and> objBitsKO ko + us < word_bits)\<rbrace>
    createObjects' ptr n ko us
    \<lbrace>\<lambda>rv s. pspace_distinct' s\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp:createObjects'_def split_def)
  apply (subst new_cap_addrs_fold')
   apply (drule range_cover_not_zero_shift[where gbits = us,rotated])
     apply simp+
   apply unat_arith
  apply (rule hoare_pre)
   apply (wpc|wp|simp add: unless_def alignError_def del: fun_upd_apply hoare_fail_any)+
  apply clarsimp
  apply (subst data_map_insert_def[symmetric])+
  apply (simp add: range_cover.unat_of_nat_n_shift)
  apply (drule(2) retype_aligned_distinct'(1)[where ko = ko and n= "n*2^us" ])
   apply (erule range_cover_rel)
    apply simp
   apply clarsimp
  apply (simp add: range_cover.unat_of_nat_n_shift)
  done

lemma createObjects'_psp_aligned:
  "\<lbrace>pspace_aligned' and pspace_distinct' and
    pspace_no_overlap' ptr sz and
    K (range_cover ptr sz ((objBitsKO ko) + us) n \<and> n \<noteq> 0
    \<and> is_aligned ptr (objBitsKO ko + us) \<and> objBitsKO ko + us < word_bits)\<rbrace>
    createObjects' ptr n ko us
    \<lbrace>\<lambda>rv s. pspace_aligned' s\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp: createObjects'_def split_def)
  apply (subst new_cap_addrs_fold')
   apply (drule range_cover_not_zero_shift[where gbits = us,rotated])
     apply simp+
   apply unat_arith
  apply (rule hoare_pre)
   apply (wpc|wp|simp add: unless_def alignError_def del: fun_upd_apply hoare_fail_any)+
  apply clarsimp
  apply (frule(2) retype_aligned_distinct'(2)[where ko = ko and n= "n*2^us" ])
   apply (erule range_cover_rel)
    apply simp
   apply clarsimp
  apply (subst data_map_insert_def[symmetric])+
  apply (simp add: range_cover.unat_of_nat_n_shift)
  done

lemma copyGlobalMappings_pspace_no_overlap':
  "\<lbrace>pspace_aligned' and pspace_distinct' and pspace_no_overlap' ptr sz\<rbrace>
   copyGlobalMappings xa
   \<lbrace>\<lambda>ya. pspace_no_overlap' ptr sz\<rbrace>"
  apply (rule hoare_pre)
   apply (clarsimp simp:copyGlobalMappings_def)
   apply (wp mapM_x_wp_inv pspace_no_overlap'_lift)
  apply clarsimp
  done

lemma pspace_no_overlap'_le:
  assumes psp: "pspace_no_overlap' ptr sz s" "sz'\<le> sz"
  assumes b: "sz < word_bits"
  shows "pspace_no_overlap' ptr sz' s"
  proof -
  note blah[simp del] = untyped_range.simps usable_untyped_range.simps atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex
  have diff_cancel: "\<And>a b c. (a::machine_word) + b - c = b + (a - c)"
   by simp
  have bound :"(ptr && ~~ mask sz') - (ptr && ~~ mask sz) \<le> 2 ^ sz - 2 ^ sz'"
    by (rule neg_mask_diff_bound[OF psp(2)])
  show ?thesis
  using psp
    apply (clarsimp simp:pspace_no_overlap'_def)
    apply (drule_tac x = x in spec)
    apply clarsimp
    apply (erule disjoint_subset2[rotated])
    apply (clarsimp simp:blah)
    apply (rule word_plus_mcs[OF _  is_aligned_no_overflow'])
     apply (simp add:diff_cancel p_assoc_help)
     apply (rule le_plus)
      apply (simp add:field_simps)
      apply (rule bound)
     apply (rule word_le_minus_mono_left)
      apply (erule two_power_increasing[OF _ b[unfolded word_bits_def]])
     apply (rule word_1_le_power)
     using b[unfolded word_bits_def] apply simp
    apply (simp add:is_aligned_neg_mask)
    done
qed

lemma pspace_no_overlap'_le2:
  assumes "pspace_no_overlap' ptr sz s" "ptr \<le> ptr'"  "ptr' &&~~ mask sz = ptr && ~~ mask sz"
  shows "pspace_no_overlap' ptr' sz s"
  proof -
  note blah[simp del] = untyped_range.simps usable_untyped_range.simps atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex
  show ?thesis
    using assms
    apply (clarsimp simp:pspace_no_overlap'_def)
    apply (drule_tac x = x in spec)
    apply clarsimp
    apply (erule disjoint_subset2[rotated])
    apply (clarsimp simp:blah)
    done
qed

lemma pspace_no_overlap'_tail:
  "\<lbrakk>range_cover ptr sz us (Suc (Suc n)); pspace_aligned' s; pspace_distinct' s;
    pspace_no_overlap' ptr sz s; ptr \<noteq> 0\<rbrakk>
   \<Longrightarrow> pspace_no_overlap' (ptr + (1 + of_nat n << us)) sz s"
  apply (erule pspace_no_overlap'_le2)
   apply (erule(1) range_cover_ptr_le)
  apply (erule(1) range_cover_tail_mask)
  done

lemma createNewCaps_pspace_no_overlap':
  "\<lbrace>\<lambda>s. range_cover ptr sz (Types_H.getObjectSize ty us) (Suc (Suc n)) \<and>
        pspace_aligned' s \<and> pspace_distinct' s \<and> pspace_no_overlap' ptr sz s \<and>
        ptr \<noteq> 0\<rbrace>
   createNewCaps ty ptr (Suc n) us d
   \<lbrace>\<lambda>r s. pspace_no_overlap'
             (ptr + (1 + of_nat n << Types_H.getObjectSize ty us))
             (Types_H.getObjectSize ty us) s\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp: createNewCaps_def)
  apply (subgoal_tac "pspace_no_overlap' (ptr + (1 + of_nat n << (Types_H.getObjectSize ty us)))
                                         (Types_H.getObjectSize ty us) s")
   prefer 2
   apply (rule pspace_no_overlap'_le[where sz = sz])
     apply (rule pspace_no_overlap'_tail)
         apply simp+
    apply (simp add:range_cover_def)
   apply (simp add:range_cover.sz(1)[where 'a=machine_word_len, folded word_bits_def])
  apply (rule_tac Q = "\<lambda>r. pspace_no_overlap' (ptr + (1 + of_nat n << Types_H.getObjectSize ty us))
                                              (Types_H.getObjectSize ty us) and
                           pspace_aligned' and pspace_distinct'" in hoare_strengthen_post)
   apply (case_tac ty)
         apply (simp_all add: apiGetObjectSize_def
                              X64_H.toAPIType_def tcbBlockSizeBits_def
                              X64_H.getObjectSize_def objBits_simps epSizeBits_def ntfnSizeBits_def
                              cteSizeBits_def pageBits_def ptBits_def archObjSize_def pdBits_def
                              createObjects_def)
        apply (rule hoare_pre)
         apply wpc
    apply (clarsimp simp: apiGetObjectSize_def  curDomain_def
                          X64_H.toAPIType_def tcbBlockSizeBits_def
                          X64_H.getObjectSize_def objBits_simps epSizeBits_def ntfnSizeBits_def
                          cteSizeBits_def pageBits_def ptBits_def archObjSize_def pdBits_def
                          createObjects_def Arch_createNewCaps_def
                    split: apiobject_type.splits
           | wp doMachineOp_psp_no_overlap createObjects'_pspace_no_overlap[where sz = sz]
                createObjects'_psp_aligned[where sz = sz] createObjects'_psp_distinct[where sz = sz]
                copyGlobalMappings_pspace_aligned' mapM_x_wp_inv
                copyGlobalMappings_pspace_no_overlap'[where sz = sz] | assumption)+
           apply (intro conjI range_cover_le[where n = "Suc n"] | simp)+
            apply ((simp add:objBits_simps pageBits_def range_cover_def word_bits_def)+)[5]
       by ((clarsimp simp: apiGetObjectSize_def bit_simps
                              X64_H.toAPIType_def tcbBlockSizeBits_def
                              X64_H.getObjectSize_def objBits_simps epSizeBits_def ntfnSizeBits_def
                              cteSizeBits_def pageBits_def ptBits_def archObjSize_def pdBits_def
                              createObjects_def Arch_createNewCaps_def
                              unless_def
                        split: apiobject_type.splits
               | wp doMachineOp_psp_no_overlap createObjects'_pspace_no_overlap
                    createObjects'_psp_aligned createObjects'_psp_distinct
                    copyGlobalMappings_pspace_aligned' mapM_x_wp_inv
                    copyGlobalMappings_pspace_no_overlap'
               | assumption | clarsimp simp: word_bits_def
               | intro conjI range_cover_le[where n = "Suc n"] range_cover.aligned)+)[7]

lemma objSize_eq_capBits:
  "Types_H.getObjectSize ty us = APIType_capBits ty us"
 apply (case_tac ty)
  apply (clarsimp simp:X64_H.getObjectSize_def objBits_simps bit_simps
    APIType_capBits_def apiGetObjectSize_def ptBits_def
    tcbBlockSizeBits_def epSizeBits_def ntfnSizeBits_def cteSizeBits_def
    pageBits_def pdBits_def
    split : apiobject_type.splits)+
 done

lemma createNewCaps_ret_len:
  "\<lbrace>K (n < 2 ^ word_bits \<and> n \<noteq> 0)\<rbrace>
   createNewCaps ty ptr n us d
   \<lbrace>\<lambda>rv s. n = length rv\<rbrace>"
  including no_pre
  apply (rule hoare_name_pre_state)
  apply clarsimp
  apply (case_tac ty)
   apply (simp_all add:createNewCaps_def X64_H.toAPIType_def)
    apply (rule hoare_pre)
     apply wpc
      apply ((wp+)|simp add:Arch_createNewCaps_def X64_H.toAPIType_def
           unat_of_nat_minus_1
           [where 'a=machine_word_len, folded word_bits_def] |
          erule hoare_strengthen_post[OF createObjects_ret],clarsimp+ | intro conjI impI)+
       apply (rule hoare_pre,
          ((wp+)
              | simp add: Arch_createNewCaps_def toAPIType_def
                          X64_H.toAPIType_def unat_of_nat_minus_1
              | erule hoare_strengthen_post[OF createObjects_ret],clarsimp+
              | intro conjI impI)+)+
   done


lemma no_overlap_check:
  "\<lbrakk>range_cover ptr sz bits n; pspace_no_overlap' ptr sz s;
    pspace_aligned' s;n\<noteq> 0\<rbrakk>
   \<Longrightarrow> case_option (return ())
                   (case_prod (\<lambda>x y. haskell_assert (x < fromPPtr ptr) []))
                   (fst (lookupAround2 (ptr + of_nat (shiftL n bits - Suc 0))
                                       (ksPSpace s))) s =
       return () s"
  apply (clarsimp split:option.splits simp:assert_def lookupAround2_char1 not_less)
  apply (rule ccontr)
  apply (frule(1) pspace_no_overlapD')
  apply (erule_tac x = a in in_empty_interE)
   apply clarsimp
   apply (drule(1) pspace_alignedD')
   apply (erule is_aligned_no_overflow)
  apply clarsimp
  apply (erule order_trans)
  apply (frule range_cover_cell_subset[where x = "of_nat n - 1"])
   apply (rule gt0_iff_gem1[THEN iffD1])
   apply (simp add:word_gt_0)
   apply (rule range_cover_not_zero)
    apply simp
   apply assumption
  apply (clarsimp simp:shiftL_nat field_simps)
  apply (erule impE)
   apply (frule range_cover_subset_not_empty[rotated,where x = "of_nat n - 1"])
   apply (rule gt0_iff_gem1[THEN iffD1])
   apply (simp add:word_gt_0)
   apply (rule range_cover_not_zero)
    apply simp
   apply assumption
   apply (clarsimp simp:field_simps)
  apply simp
  done

lemma new_caps_addrs_append:
  "\<lbrakk>range_cover ptr sz (objBitsKO va + us) (Suc n)\<rbrakk> \<Longrightarrow>
   new_cap_addrs (unat (of_nat n + (1::machine_word) << us)) ptr val =
   new_cap_addrs (unat (((of_nat n)::machine_word) << us)) ptr val @
   new_cap_addrs (unat ((2::machine_word) ^ us))
                 ((((of_nat n)::machine_word) << objBitsKO val + us) + ptr) val"
  apply (subst add.commute)
  apply (clarsimp simp:new_cap_addrs_def)
  apply (subst upt_add_eq_append'[where j="unat (((of_nat n)::machine_word) << us)"])
    prefer 3
    apply simp
    apply (subst upt_lhs_sub_map)
    apply (simp add:Fun.comp_def field_simps)
    apply (subst unat_sub[symmetric])
     apply (simp add:shiftl_t2n)
     apply (subst mult.commute)
     apply (subst mult.commute[where a = "2 ^ us"])+
     apply (rule word_mult_le_mono1)
       apply (simp add:word_le_nat_alt)
       apply (subst of_nat_Suc[symmetric])
       apply (frule range_cover.unat_of_nat_n)
        apply (drule range_cover.unat_of_nat_n[OF range_cover_le[where n = n]])
       apply simp
      apply simp
      apply (simp add: p2_gt_0)
     apply (simp add:range_cover_def word_bits_def)
     apply (subst word_bits_def[symmetric])
     apply (subst of_nat_Suc[symmetric])
      apply (subst range_cover.unat_of_nat_n)
     apply simp
      apply (subst unat_power_lower)
     apply (simp add:range_cover_def)
     apply (frule range_cover.range_cover_n_le(2))
     apply (subst mult.commute)
       apply (rule le_less_trans[OF nat_le_power_trans[where m = sz]])
       apply (erule le_trans)
      apply simp
     apply (simp add:range_cover_def)
    apply (simp add:range_cover_def[where 'a=machine_word_len, folded word_bits_def])
   apply (clarsimp simp: power_add [symmetric] shiftl_t2n field_simps)
  apply simp
   apply (frule range_cover_le[where n = n])
  apply simp
    apply (drule range_cover_rel[where sbit'= "objBitsKO va"])
  apply simp+
    apply (drule range_cover_rel[where sbit'= "objBitsKO va"])
  apply simp+
  apply (drule range_cover.unat_of_nat_n)+
  apply (simp add:shiftl_t2n)
  apply (clarsimp simp: power_add[symmetric] shiftl_t2n field_simps )
  done

lemma modify_comp:
  "modify (ksPSpace_update (\<lambda>a. f (g a))) =
  (do modify (ksPSpace_update (\<lambda>a. (g a)));
      modify (ksPSpace_update (\<lambda>a. f a))
   od)"
  by (clarsimp simp:simpler_modify_def bind_def Fun.comp_def)

lemma modify_objs_commute:
  "monad_commute (K ((set lst1) \<inter> (set lst2) = {}))
     (modify (ksPSpace_update (foldr (\<lambda>addr map. map(addr \<mapsto> val)) lst1)))
     (modify (ksPSpace_update (foldr (\<lambda>addr map. map(addr \<mapsto> val)) lst2)))"
  apply (clarsimp simp:monad_commute_def simpler_modify_def bind_def return_def)
  apply (case_tac s,simp)
  apply (rule ext)
  apply (clarsimp simp:foldr_upd_app_if)
  done

lemma new_cap_addrs_disjoint:
  "\<lbrakk>range_cover ptr sz (objBitsKO val + us) (Suc (Suc n))\<rbrakk>
   \<Longrightarrow> set (new_cap_addrs (2^us)
             (((1::machine_word) + of_nat n << objBitsKO val + us) + ptr) val) \<inter>
       set (new_cap_addrs (unat ((1::machine_word) + of_nat n << us)) ptr val) = {}"
  apply (frule range_cover.unat_of_nat_n_shift[where gbits = us,symmetric])
   apply simp
  apply (frule range_cover_rel[where sbit' = "objBitsKO val"])
    apply (simp add:field_simps)+
  apply (frule new_cap_addrs_distinct)
  apply (subst (asm) add.commute[where b = 2])+
  apply (subst (asm) new_caps_addrs_append[where n = "Suc n",simplified])
   apply (simp add:field_simps)
  apply (clarsimp simp:field_simps Int_ac range_cover_def)
  done

lemma pspace_no_overlap'_modify:
  "\<lbrace>K (range_cover ptr sz (objBitsKO val + us) (Suc (Suc n)) \<and> ptr \<noteq> 0) and
    pspace_no_overlap' (((1::machine_word) + of_nat n << objBitsKO val + us) + ptr)
                       (objBitsKO val + us)\<rbrace>
   modify (ksPSpace_update
     (foldr (\<lambda>addr map. map(addr \<mapsto> val))
            (new_cap_addrs (unat ((1::machine_word) + of_nat n << us)) ptr val)))
   \<lbrace>\<lambda>r. pspace_no_overlap'
          (((1::machine_word) + of_nat n << objBitsKO val + us) + ptr)
          (objBitsKO val + us)\<rbrace>"
  proof -
  note blah[simp del] = untyped_range.simps usable_untyped_range.simps atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex
  show ?thesis
  apply (clarsimp simp:simpler_modify_def valid_def pspace_no_overlap'_def)
  apply (frule(1) range_cover_tail_mask)
   apply (simp add:field_simps)
   apply (drule_tac x = x in spec)
   apply (clarsimp simp:foldr_upd_app_if split:if_splits)
   apply (frule obj_range'_subset_strong[rotated])
    apply (drule range_cover_le[where n = "Suc n"])
     apply simp
    apply (rule range_cover_rel,assumption)
     apply simp
    apply clarsimp
    apply (frule range_cover.unat_of_nat_n_shift[where gbits = us,symmetric])
     apply simp+
    apply (simp add:field_simps)
  apply (simp add:obj_range'_def)
  apply (erule disjoint_subset)
  apply (frule(1) range_cover_ptr_le)
  apply (subgoal_tac
    "\<not> ptr + (1 + of_nat n << us + objBitsKO val) \<le> ptr + (1 + of_nat n << us) * 2 ^ objBitsKO val - 1")
   apply (clarsimp simp:blah field_simps)
  apply (clarsimp simp: not_le)
  apply (rule word_leq_le_minus_one)
   apply (clarsimp simp: power_add[symmetric] shiftl_t2n field_simps objSize_eq_capBits )
  apply (rule neq_0_no_wrap)
   apply (clarsimp simp: power_add[symmetric] shiftl_t2n field_simps objSize_eq_capBits )
  apply simp
  done
qed

lemma placeNewObject_copyGlobalMapping_commute:
  "monad_commute
     (valid_arch_state' and pspace_distinct' and pspace_aligned' and
      page_map_l4_at' r and
      pspace_no_overlap' ptr (objBitsKO (injectKOS val) + us) and
      K (objBitsKO (injectKOS val) + us < word_bits \<and>
         is_aligned ptr (objBitsKO (injectKOS val) + us)) )
     (placeNewObject ptr val us) (copyGlobalMappings r)"
  apply (clarsimp simp:copyGlobalMappings_def)
  apply (rule monad_commute_guard_imp)
   apply (rule monad_commute_split)
     apply (rule mapM_x_commute[where f = id])
      apply (rule monad_commute_split[OF _ getPML4E_placeNewObject_commute])
       apply (rule storePML4E_placeNewObject_commute)
      apply wp
      apply (wp pspace_no_overlap'_lift | clarsimp)+
    apply (rule placeNewObject_gets_globalPML4_commute)
   apply wp
  apply clarsimp
  apply (clarsimp simp: valid_arch_state'_def page_map_l4_at'_def bit_simps
                        objBits_simps archObjSize_def pdBits_def pageBits_def)
  apply (drule le_m1_iff_lt[where x = "(0x200::machine_word)",simplified,THEN iffD1])
  apply (clarsimp)
  done

lemma createObjects_Cons:
  "\<lbrakk>range_cover ptr sz (objBitsKO val + us) (Suc (Suc n));
    pspace_distinct' s;pspace_aligned' s;
    pspace_no_overlap' ptr sz s;pspace_aligned' s; ptr \<noteq> 0\<rbrakk>
   \<Longrightarrow> createObjects' ptr (Suc (Suc n)) val us s =
       (do createObjects' ptr (Suc n) val us;
           createObjects' (((1 + of_nat n) << (objBitsKO val + us)) + ptr)
                          (Suc 0) val us
        od) s"
  supply option.case_cong_weak [cong] subst_all [simp del]
  apply (clarsimp simp:createObjects'_def split_def bind_assoc)
  apply (subgoal_tac "is_aligned (((1::machine_word) + of_nat n << objBitsKO val + us) + ptr) (objBitsKO val + us)")
   prefer 2
   apply (clarsimp simp:field_simps)
   apply (rule aligned_add_aligned[OF range_cover.aligned],assumption)
    apply (rule is_aligned_shiftl_self)
   apply (simp add:range_cover_def)
  apply (rule monad_eq_split[where Q ="\<lambda>x s'. s' = s \<and> ptr && mask (objBitsKO val + us) = 0"])
    apply (clarsimp simp:is_aligned_mask[symmetric])
    apply (subst new_cap_addrs_fold')
     apply (drule range_cover_not_zero_shift[rotated,where gbits = us])
       apply simp+
     apply (simp add:word_le_sub1)
    apply (subst new_cap_addrs_fold')
     apply (drule range_cover_le[where n = "Suc n"])
      apply simp
     apply (drule range_cover_not_zero_shift[rotated,where gbits = us])
       apply simp+
     apply (simp add:word_le_sub1)
    apply (subst new_cap_addrs_fold')
     apply (rule word_1_le_power)
     apply (simp add:range_cover_def)
    apply (rule monad_eq_split[where Q ="\<lambda>r s'. r = ksPSpace s \<and> s' = s"])
      apply (rule monad_eq_split2[where Q = "\<lambda>r s'. s' = s"])
         apply (simp add:field_simps)
         apply (subst no_overlap_check)
             apply (erule range_cover_le)
             apply simp+
         apply (subst no_overlap_check)
             apply (erule range_cover_le)
             apply simp+
        apply clarsimp
        apply (simp add:new_caps_addrs_append[where n = "Suc n",simplified])
        apply (subst modify_specify2[where g = return,simplified])
        apply (subst modify_specify2)
        apply (subst modify_specify)
        apply (simp add:modify_comp)
        apply (subst monad_commute_simple[OF modify_objs_commute,where g= "\<lambda>x y. return ()",simplified])
         apply (frule range_cover.sz(1))
         apply (frule range_cover.sz(2))
         apply clarsimp
         apply (erule new_cap_addrs_disjoint)
        apply (rule monad_eq_split2[where Q =
           "\<lambda>r. pspace_no_overlap' (((1::machine_word) + of_nat n << objBitsKO val + us) + ptr)
                                   (objBitsKO val + us) and pspace_aligned'"])
           apply (simp add:shiftl_t2n field_simps)
          apply (clarsimp simp:unless_True)
          apply (rule sym)
          apply (clarsimp simp:gets_def get_def)
          apply (subst bind_def,simp)
          apply (subst monad_eq)
           apply (rule no_overlap_check)
              apply (erule range_cover_full)
              apply (simp add:range_cover_def word_bits_def)
             apply (simp add:field_simps)
            apply simp+
          apply (clarsimp simp:simpler_modify_def)
         apply wp
        apply (clarsimp simp del:fun_upd_apply)
        apply (rule conjI)
         apply (rule use_valid[OF _ pspace_no_overlap'_modify[where sz = sz]])
          apply (simp add:simpler_modify_def)
         apply (clarsimp simp:field_simps)
         apply (rule pspace_no_overlap'_le)
           apply (erule pspace_no_overlap'_tail)
              apply simp+
          apply (simp add:range_cover_def)
         apply (erule range_cover.sz(1)[where 'a=machine_word_len, folded word_bits_def])
        apply (subst data_map_insert_def[symmetric])
        apply (drule(2) retype_aligned_distinct'(2))
         prefer 2
         apply (simp cong: kernel_state.fold_congs)
        apply (drule range_cover_le[where n = "Suc n"])
         apply simp
        apply (rule range_cover_le[OF range_cover_rel,OF _ _ _ le_refl])
          apply simp+
        apply (drule range_cover.unat_of_nat_n_shift[where gbits = us])
         apply simp
        apply simp
       apply (wp haskell_assert_wp | wpc)+
      apply simp
     apply (wp unless_wp |clarsimp)+
  apply (drule range_cover.aligned)
  apply (simp add:is_aligned_mask)
  done

lemma doMachineOp_ksArchState_commute:
  "monad_commute \<top> (doMachineOp f) (gets (g \<circ> ksArchState))"
  apply (clarsimp simp:monad_commute_def gets_def return_def get_def bind_def)
  apply (intro conjI set_eqI iffI)
     apply (clarsimp simp: doMachineOp_def select_f_def gets_def get_def bind_def
                           return_def simpler_modify_def)
     apply (erule bexI[rotated])
     apply clarsimp
    apply (clarsimp simp: doMachineOp_def select_f_def gets_def get_def bind_def return_def
                          simpler_modify_def)
    apply (erule bexI[rotated])
    apply clarsimp+
  done

lemma createObjects'_page_map_l4_at':
  "\<lbrace>K (range_cover ptr sz pml4Bits (Suc n)) and
    pspace_aligned' and pspace_distinct' and pspace_no_overlap' ptr sz\<rbrace>
   createObjects' ptr (Suc n) (KOArch (KOPML4E makeObject)) ptTranslationBits
   \<lbrace>\<lambda>rv s. (\<forall>x\<le>of_nat n. page_map_l4_at' (ptr + (x << 12)) s)\<rbrace>"
  apply (rule createObjects'_wp_subst)
   apply simp
  apply (clarsimp simp:valid_def)
  apply (frule use_valid[OF _  createObjects_ko_at_strg])
      apply (simp add:objBits_simps archObjSize_def bit_simps)
     apply simp
    apply (subst projectKO_opt_pml4e)
    apply (simp add: return_def)
   apply simp
  apply (clarsimp simp:page_map_l4_at'_def bit_simps)
  apply (intro conjI)
   apply (rule aligned_add_aligned[OF range_cover.aligned],simp)
    apply (rule is_aligned_shiftl_self)
   apply (simp add:range_cover_def)
  apply (drule_tac x = "ptr + (x << 12)" in bspec)
   apply (simp add:createObjects_def bind_def return_def)
   apply (clarsimp simp:objBits_simps archObjSize_def)
  apply (clarsimp simp:typ_at'_def)
  apply (drule_tac x = y in spec)
  apply (simp add:obj_at'_real_def objBits_simps archObjSize_def)
  apply (erule ko_wp_at'_weakenE)
  apply (simp add: projectKO_opt_pml4e)
  apply (case_tac ko; simp)
  apply (rename_tac arch_kernel_object)
  apply (case_tac arch_kernel_object; simp)
  done

lemma gsCNodes_upd_createObjects'_comm:
  "do _ \<leftarrow> modify (gsCNodes_update f);
      x \<leftarrow> createObjects' ptr n obj us;
      m x
   od =
   do x \<leftarrow> createObjects' ptr n obj us;
      _ \<leftarrow> modify (gsCNodes_update f);
      m x
   od"
  apply (rule ext)
  apply (case_tac x)
  by (auto simp: createObjects'_def split_def bind_assoc return_def unless_def
          when_def simpler_gets_def alignError_def fail_def assert_def
          simpler_modify_def bind_def
        split: option.splits)

lemma gsUserPages_upd_createObjects'_comm:
  "do _ \<leftarrow> modify (gsUserPages_update f);
      x \<leftarrow> createObjects' ptr n obj us;
      m x
   od =
   do x \<leftarrow> createObjects' ptr n obj us;
      _ \<leftarrow> modify (gsUserPages_update f);
      m x
   od"
  apply (rule ext)
  apply (case_tac x)
  by (auto simp: createObjects'_def split_def bind_assoc return_def unless_def
          when_def simpler_gets_def alignError_def fail_def assert_def
          simpler_modify_def bind_def
        split: option.splits)

(* FIXME: move *)
lemma ef_dmo':
  "empty_fail f \<Longrightarrow> empty_fail (doMachineOp f)"
  by (auto simp: empty_fail_def doMachineOp_def split_def select_f_def
           simpler_modify_def simpler_gets_def return_def bind_def image_def)

(* FIXME: move *)
lemma dmo'_when_fail_comm:
  assumes "empty_fail f"
  shows "doMachineOp f >>= (\<lambda>x. when P fail >>= (\<lambda>_. m x)) =
         when P fail >>= (\<lambda>_. doMachineOp f >>= m)"
  apply (rule ext)
  apply (cut_tac ef_dmo'[OF assms])
  apply (auto simp add: empty_fail_def when_def fail_def return_def
                        bind_def split_def image_def, fastforce)
  done

(* FIXME: move *)
lemma dmo'_gets_ksPSpace_comm:
  "doMachineOp f >>= (\<lambda>_. gets ksPSpace >>= m) =
   gets ksPSpace >>= (\<lambda>x. doMachineOp f >>= (\<lambda>_. m x))"
  apply (rule ext)
  apply (clarsimp simp: doMachineOp_def simpler_modify_def simpler_gets_def
                        return_def select_f_def bind_def split_def image_def)
  apply (rule conjI)
   apply (rule set_eqI, clarsimp)
   apply (rule iffI; clarsimp)
    apply (metis eq_singleton_redux prod_injects(2))
   apply (intro exI conjI bexI[rotated], simp+)[1]
  apply (rule iffI; clarsimp; intro exI conjI bexI[rotated], simp+)[1]
  done

lemma dmo'_ksPSpace_update_comm':
  assumes "empty_fail f"
  shows "doMachineOp f >>= (\<lambda>x. modify (ksPSpace_update g) >>= (\<lambda>_. m x)) =
         modify (ksPSpace_update g) >>= (\<lambda>_. doMachineOp f >>= m)"
proof -
  have ksMachineState_ksPSpace_update:
    "\<forall>s. ksMachineState (ksPSpace_update g s) = ksMachineState s"
    by simp
  have updates_independent:
    "\<And>f. ksPSpace_update g \<circ> ksMachineState_update f =
          ksMachineState_update f \<circ> ksPSpace_update g"
    by (rule ext) simp
  from assms
  show ?thesis
    apply (simp add: doMachineOp_def split_def bind_assoc)
    apply (simp add: gets_modify_comm2[OF ksMachineState_ksPSpace_update])
    apply (rule arg_cong_bind1)
    apply (simp add: empty_fail_def select_f_walk[OF empty_fail_modify]
                     modify_modify_bind updates_independent)
    done
qed

lemma dmo'_createObjects'_comm:
  assumes ef: "empty_fail f"
  shows "do _ \<leftarrow> doMachineOp f; x \<leftarrow> createObjects' ptr n obj us; m x od =
         do x \<leftarrow> createObjects' ptr n obj us; _ \<leftarrow> doMachineOp f; m x od"
  apply (simp add: createObjects'_def bind_assoc split_def unless_def
                   alignError_def dmo'_when_fail_comm[OF ef]
                   dmo'_gets_ksPSpace_comm
                   dmo'_ksPSpace_update_comm'[OF ef, symmetric])
  apply (rule arg_cong_bind1)
  apply (rule arg_cong_bind1)
  apply (rename_tac u w)
  apply (case_tac "fst (lookupAround2 (ptr + of_nat (shiftL n (objBitsKO obj +
                                         us) - Suc 0)) w)", clarsimp+)
  apply (simp add: assert_into_when dmo'_when_fail_comm[OF ef])
  done

lemma dmo'_gsUserPages_upd_comm:
  assumes "empty_fail f"
  shows "doMachineOp f >>= (\<lambda>x. modify (gsUserPages_update g) >>= (\<lambda>_. m x)) =
         modify (gsUserPages_update g) >>= (\<lambda>_. doMachineOp f >>= m)"
proof -
  have ksMachineState_ksPSpace_update:
    "\<forall>s. ksMachineState (gsUserPages_update g s) = ksMachineState s"
    by simp
  have updates_independent:
    "\<And>f. gsUserPages_update g \<circ> ksMachineState_update f =
          ksMachineState_update f \<circ> gsUserPages_update g"
    by (rule ext) simp
  from assms
  show ?thesis
    apply (simp add: doMachineOp_def split_def bind_assoc)
    apply (simp add: gets_modify_comm2[OF ksMachineState_ksPSpace_update])
    apply (rule arg_cong_bind1)
    apply (simp add: empty_fail_def select_f_walk[OF empty_fail_modify]
                     modify_modify_bind updates_independent)
    done
qed

lemma rewrite_step:
  assumes rewrite: "\<And>s. P s \<Longrightarrow> f s = f' s"
  shows "P s \<Longrightarrow> ( f >>= g ) s = (f' >>= g ) s"
  by (simp add:bind_def rewrite)

lemma rewrite_through_step:
  assumes rewrite: "\<And>s r. P s \<Longrightarrow> f r s = f' r s"
  assumes hoare: "\<lbrace>Q\<rbrace> g \<lbrace>\<lambda>r. P\<rbrace>"
  shows "Q s \<Longrightarrow>
    (do x \<leftarrow> g;
       y \<leftarrow> f x;
       h x y od) s =
    (do x \<leftarrow> g;
       y \<leftarrow> f' x;
       h x y od) s"
  apply (rule monad_eq_split[where Q = "\<lambda>r. P"])
    apply (simp add:bind_def rewrite)
   apply (rule hoare)
  apply simp
  done

lemma threadSet_commute:
  assumes preserve: "\<lbrace>P and tcb_at' ptr \<rbrace> f \<lbrace>\<lambda>r. tcb_at' ptr\<rbrace>"
  assumes commute: "monad_commute P' f
    ( modify (ksPSpace_update
       (\<lambda>ps. ps(ptr \<mapsto>
       case ps ptr of Some (KOTCB tcb) \<Rightarrow> KOTCB (tcbDomain_update (\<lambda>_. r) tcb)))))"
  shows "monad_commute (tcb_at' ptr and P and P') f (threadSet (tcbDomain_update (\<lambda>_. r)) ptr)"
  apply (clarsimp simp add: monad_commute_def)
  apply (subst rewrite_through_step[where h = "\<lambda>x y. return (x,())",simplified bind_assoc])
     apply (erule threadSet_det)
    apply (rule preserve)
    apply simp
   apply (subst rewrite_step[OF threadSet_det])
    apply assumption
   apply simp
  using commute
  apply (simp add:monad_commute_def)
  done

lemma createObjects_setDomain_commute:
  "monad_commute
  (\<lambda>s. range_cover ptr'  (objBitsKO (KOTCB makeObject))
       (objBitsKO (KOTCB makeObject) + 0) (Suc 0) \<and>
  pspace_aligned' s \<and> pspace_distinct' s \<and>
  pspace_no_overlap' ptr' (objBitsKO (KOTCB makeObject)) s \<and>
  tcb_at' ptr s \<and> is_aligned ptr' (objBitsKO (KOTCB makeObject)))
  (createObjects' ptr' (Suc 0) (KOTCB makeObject) 0)
  (threadSet (tcbDomain_update (\<lambda>_. r)) ptr)"
  apply (rule monad_commute_guard_imp)
  apply (rule threadSet_commute)
    apply (wp createObjects_orig_obj_at'[where sz = "(objBitsKO (KOTCB makeObject))"])
    apply clarsimp
    apply assumption
   apply (simp add:placeNewObject_def2[where val = "makeObject::tcb",simplified,symmetric])
   apply (rule placeNewObject_modify_commute)
  apply (clarsimp simp: objBits_simps' typ_at'_def word_bits_def
    obj_at'_def ko_wp_at'_def projectKO_eq projectKO_opt_tcb)
  apply (clarsimp split:Structures_H.kernel_object.splits)
  done


lemma createObjects_setDomains_commute:
  "monad_commute
      (\<lambda>s. \<forall>x\<in> set xs. tcb_at' (f x) s \<and>
      range_cover ptr (objBitsKO (KOTCB makeObject)) (objBitsKO (KOTCB makeObject)) (Suc 0) \<and>
      pspace_aligned' s \<and>
      pspace_distinct' s \<and>
      pspace_no_overlap' ptr (objBitsKO (KOTCB makeObject)) s \<and>
      is_aligned ptr (objBitsKO (KOTCB makeObject)))
  (mapM_x (threadSet (tcbDomain_update (\<lambda>_. r))) (map f xs))
  (createObjects' ptr (Suc 0) (KOTCB makeObject) 0)"
  proof (induct xs)
    case Nil
    show ?case
      apply (simp add:monad_commute_def mapM_x_Nil)
    done
    next
    case (Cons x xs)
    show ?case
    apply (simp add:mapM_x_Cons)
    apply (rule monad_commute_guard_imp)
    apply (rule commute_commute[OF monad_commute_split])
     apply (rule commute_commute[OF Cons.hyps])
     apply (rule createObjects_setDomain_commute)
     apply (wp hoare_vcg_ball_lift)
    apply clarsimp
   done
  qed

lemma createObjects'_pspace_no_overlap2:
  "\<lbrace>pspace_no_overlap' (ptr + (1 + of_nat n << gz)) sz
       and K (gz = (objBitsKO val) + us)
       and K (range_cover ptr sz gz (Suc (Suc n)) \<and> ptr \<noteq> 0)\<rbrace>
    createObjects' ptr (Suc n) val us
  \<lbrace>\<lambda>addrs s. pspace_no_overlap' (ptr + (1 + of_nat n << gz)) sz s\<rbrace>"
proof -
  note blah[simp del] = untyped_range.simps usable_untyped_range.simps atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex
  show ?thesis
  apply (rule hoare_gen_asm)+
  apply (clarsimp simp:createObjects'_def split_def new_cap_addrs_fold')
  apply (subst new_cap_addrs_fold')
   apply clarsimp
   apply (drule range_cover_le[where n = "Suc n"])
    apply simp
   apply (drule_tac gbits = us in range_cover_not_zero_shift[rotated])
    apply simp+
   apply (simp add:word_le_sub1)
   apply (wp haskell_assert_wp unless_wp |wpc
         |simp add:alignError_def del:fun_upd_apply)+
  apply (rule conjI)
   apply (rule impI)
   apply (subgoal_tac
     "pspace_no_overlap' (ptr + (1 + of_nat n << objBitsKO val + us))
       sz
      (s\<lparr>ksPSpace := foldr (\<lambda>addr map. map(addr \<mapsto> val))
                     (new_cap_addrs (unat (1 + of_nat n << us)) ptr val) (ksPSpace s)\<rparr>)")
   apply (intro conjI impI allI)
     apply assumption+
   apply (subst pspace_no_overlap'_def)
     apply (intro allI impI)
      apply (subst (asm) foldr_upd_app_if)
   apply (subst range_cover_tail_mask)
    apply simp+
   apply (clarsimp split:if_splits)
    apply (drule obj_range'_subset_strong[rotated])
     apply (rule range_cover_rel[OF range_cover_le[where n = "Suc n"]],assumption)
       apply simp+
     apply (drule range_cover.unat_of_nat_n_shift
       [OF range_cover_le[where n = "Suc n"],where gbits = us])
       apply simp+
     apply (simp add:shiftl_t2n field_simps)+
     apply (simp add:obj_range'_def)
     apply (erule disjoint_subset)
     apply (clarsimp simp:blah)
     apply (thin_tac "x \<le> y" for x y)
     apply (subst (asm) le_m1_iff_lt[THEN iffD1])
       apply (drule_tac range_cover_no_0[rotated,where p = "Suc n"])
        apply simp
       apply simp
      apply (simp add:field_simps)
      apply (simp add: power_add[symmetric])
      apply (simp add: word_neq_0_conv)
     apply (simp add: power_add[symmetric] field_simps)
     apply (frule range_cover_subset[where p = "Suc n"])
      apply simp
     apply simp
    apply (drule(1) pspace_no_overlapD')
   apply (subst (asm) range_cover_tail_mask)
    apply simp+
   apply (simp add:word_le_sub1 shiftl_t2n field_simps)
  apply auto
  done
qed

lemma new_cap_addrs_def2:
  "n < 2 ^ 64
   \<Longrightarrow> new_cap_addrs (Suc n) ptr obj
   = map (\<lambda>n. ptr + (n << objBitsKO obj)) [0.e.of_nat n]"
  by (simp add:new_cap_addrs_def upto_enum_word unat_of_nat Fun.comp_def)

lemma createTCBs_tcb_at':
  "\<lbrace>\<lambda>s. pspace_aligned' s \<and> pspace_distinct' s \<and>
   pspace_no_overlap' ptr sz s \<and>
   range_cover ptr sz
  (objBitsKO (KOTCB makeObject)) (Suc n) \<rbrace>
  createObjects' ptr (Suc n) (KOTCB makeObject) 0
  \<lbrace>\<lambda>rv s.
  (\<forall>x\<in>set [0.e.of_nat n]. tcb_at' (ptr + x * 2^tcbBlockSizeBits) s)\<rbrace>"
  apply (simp add:createObjects'_def split_def alignError_def)
  apply (wp unless_wp |wpc)+
  apply (subst data_map_insert_def[symmetric])+
  apply clarsimp
  apply (subgoal_tac "(\<forall>x\<le>of_nat n.
    tcb_at' (ptr + x * 2^tcbBlockSizeBits) (s\<lparr>ksPSpace :=
    foldr (\<lambda>addr. data_map_insert addr (KOTCB makeObject))
    (new_cap_addrs (Suc n) ptr (KOTCB makeObject))
    (ksPSpace s)\<rparr>))")
  apply (subst (asm) new_cap_addrs_def2)
   apply (drule range_cover.weak)
    apply simp
   apply simp
  apply (clarsimp simp: retype_obj_at_disj')
  apply (clarsimp simp: new_cap_addrs_def image_def)
  apply (drule_tac x = "unat x" in bspec)
   apply (simp add:objBits_simps' shiftl_t2n)
   apply (rule unat_less_helper)
   apply (rule ccontr)
   apply simp
  apply (simp add: objBits_simps shiftl_t2n)
  done

lemma createNewCaps_Cons:
  assumes cover:"range_cover ptr sz (Types_H.getObjectSize ty us) (Suc (Suc n))"
  and "valid_pspace' s" "valid_arch_state' s"
  and "pspace_no_overlap' ptr sz s"
  and "ptr \<noteq> 0"
  shows "createNewCaps ty ptr (Suc (Suc n)) us d s
 = (do x \<leftarrow> createNewCaps ty ptr (Suc n) us d;
      r \<leftarrow> RetypeDecls_H.createObject ty
             (((1 + of_nat n) << Types_H.getObjectSize ty us) + ptr) us d;
      return (x @ [r])
    od) s"
proof -
  have append :"[0.e.(1::machine_word) + of_nat n] = [0.e.of_nat n] @ [1 + of_nat n]"
     using cover
     apply -
     apply (frule range_cover_not_zero[rotated])
      apply simp
     apply (frule range_cover.unat_of_nat_n)
     apply (drule range_cover_le[where n = "Suc n"])
      apply simp
     apply (frule range_cover_not_zero[rotated])
      apply simp
     apply (frule range_cover.unat_of_nat_n)
     apply (subst upto_enum_red'[where X = "2 + of_nat n",simplified])
      apply (simp add:field_simps word_le_sub1)
     apply clarsimp
     apply (subst upto_enum_red'[where X = "1 + of_nat n",simplified])
      apply (simp add:field_simps word_le_sub1)
     apply simp
     done

  have conj_impI:
    "\<And>A B C. \<lbrakk>C;C\<Longrightarrow>B\<rbrakk> \<Longrightarrow> B \<and> C"
    by simp

  have suc_of_nat: "(1::machine_word) + of_nat n = of_nat (1 + n)"
     by simp

  have gsUserPages_update[simp]:
    "\<And>f. (\<lambda>ks. ks \<lparr>gsUserPages := f (gsUserPages ks)\<rparr>) = gsUserPages_update f"
    by (rule ext) simp
  have gsCNodes_update[simp]:
    "\<And>f. (\<lambda>ks. ks \<lparr>gsCNodes := f (gsCNodes ks)\<rparr>) = gsCNodes_update f"
    by (rule ext) simp

  have if_eq[simp]:
    "!!x a b pgsz. (if a = ptr + (1 + of_nat n << b) then Some pgsz
             else if a \<in> (\<lambda>n. ptr + (n << b)) ` {x. x \<le> of_nat n}
                  then Just pgsz else x a) =
            (if a \<in> (\<lambda>n. ptr + (n << b)) ` {x. x \<le> 1 + of_nat n}
             then Just pgsz else x a)"
        apply (simp only: Just_def if3_fold2)
        apply (rule_tac x="x a" in fun_cong)
        apply (rule arg_cong2[where f=If, OF _ refl])
        apply (subgoal_tac "{x. x \<le> (1::machine_word) + of_nat n} =
                        {1 + of_nat n} \<union> {x. x \<le> of_nat n}")
        apply (simp add: add.commute)
        apply safe
        apply (clarsimp simp: word_le_less_eq[of _ "1 + of_nat n"])
        apply (metis plus_one_helper add.commute)
        using cover
        apply -
        apply (drule range_cover_le[where n = "Suc n"], simp)
        apply (simp only: suc_of_nat word_le_nat_alt Suc_eq_plus1)
        apply (frule range_cover.unat_of_nat_n)
        apply simp
        apply (drule range_cover_le[where n=n], simp)
        apply (frule range_cover.unat_of_nat_n, simp)
        done

  show ?thesis
  using assms
  apply (clarsimp simp:valid_pspace'_def)
  apply (frule range_cover.aligned)
  apply (frule(3) pspace_no_overlap'_tail)
   apply simp
  apply (drule_tac ptr = "ptr + x" for x
         in pspace_no_overlap'_le[where sz' = "Types_H.getObjectSize ty us"])
    apply (simp add:range_cover_def word_bits_def)
   apply (erule range_cover.sz(1)[where 'a=machine_word_len, folded word_bits_def])
  apply (simp add: createNewCaps_def)
  apply (case_tac ty)
        apply (simp add: X64_H.toAPIType_def
                         Arch_createNewCaps_def)
        apply (rename_tac apiobject_type)
        apply (case_tac apiobject_type)
            apply (simp_all add: bind_assoc X64_H.toAPIType_def
                                 )
            \<comment> \<open>Untyped\<close>
            apply (simp add:
              bind_assoc X64_H.getObjectSize_def
              mapM_def sequence_def Retype_H.createObject_def
              X64_H.toAPIType_def
              createObjects_def X64_H.createObject_def
              Arch_createNewCaps_def comp_def
              apiGetObjectSize_def shiftl_t2n field_simps
              shiftL_nat mapM_x_def sequence_x_def append
              fromIntegral_def integral_inv[unfolded Fun.comp_def])
           \<comment> \<open>TCB, EP, NTFN\<close>
           apply (simp add: bind_assoc
                      X64_H.getObjectSize_def
                      sequence_def Retype_H.createObject_def
                      X64_H.toAPIType_def
                      createObjects_def X64_H.createObject_def
                      Arch_createNewCaps_def comp_def
                      apiGetObjectSize_def shiftl_t2n field_simps
                      shiftL_nat append mapM_x_append2
                      fromIntegral_def integral_inv[unfolded Fun.comp_def])+
           apply (subst monad_eq)
            apply (rule createObjects_Cons)
                 apply (simp add: field_simps shiftl_t2n bind_assoc pageBits_def
                               objBits_simps placeNewObject_def2)+
           apply (rule_tac Q = "\<lambda>r s. pspace_aligned' s \<and>
               pspace_distinct' s \<and>
               pspace_no_overlap' (ptr + (2^tcbBlockSizeBits + of_nat n * 2^tcbBlockSizeBits)) (objBitsKO (KOTCB makeObject)) s \<and>
               range_cover (ptr + 2^tcbBlockSizeBits) sz
               (objBitsKO (KOTCB makeObject)) (Suc n)
               \<and> (\<forall>x\<in>set [0.e.of_nat n]. tcb_at' (ptr + x * 2^tcbBlockSizeBits) s)"
               in monad_eq_split2)
              apply simp
             apply (subst monad_commute_simple[symmetric])
              apply (rule commute_commute[OF curDomain_commute])
              apply wpsimp+
             apply (rule_tac Q = "\<lambda>r s. r = (ksCurDomain s) \<and>
               pspace_aligned' s \<and>
               pspace_distinct' s \<and>
               pspace_no_overlap' (ptr + (2^tcbBlockSizeBits + of_nat n * 2^tcbBlockSizeBits)) (objBitsKO (KOTCB makeObject)) s \<and>
               range_cover (ptr + 2^tcbBlockSizeBits) sz
               (objBitsKO (KOTCB makeObject)) (Suc n)
               \<and> (\<forall>x\<in>set [0.e.of_nat n]. tcb_at' (ptr + x * 2^tcbBlockSizeBits) s)
             " in  monad_eq_split)
               apply (subst monad_commute_simple[symmetric])
                 apply (rule createObjects_setDomains_commute)
                apply (clarsimp simp:objBits_simps)
                apply (rule conj_impI)
                 apply (erule aligned_add_aligned)
                  apply (rule aligned_add_aligned[where n = tcbBlockSizeBits])
                    apply (simp add:is_aligned_def objBits_defs)
                   apply (cut_tac is_aligned_shift[where m = tcbBlockSizeBits and k = "of_nat n",
                     unfolded shiftl_t2n,simplified])
                   apply (simp add:field_simps)+
                apply (erule range_cover_full)
                apply (simp add: word_bits_conv objBits_defs)
               apply (rule_tac Q = "\<lambda>x s. (ksCurDomain s) = r" in monad_eq_split2)
                  apply simp
                 apply (rule_tac Q = "\<lambda>x s. (ksCurDomain s) = r" in monad_eq_split)
                   apply (subst rewrite_step[where f = curDomain and
                     P ="\<lambda>s. ksCurDomain s = r" and f' = "return r"])
                     apply (simp add:curDomain_def bind_def gets_def get_def)
                    apply simp
                   apply (simp add:mapM_x_singleton)
                  apply wp
                 apply simp
                apply (wp mapM_x_wp')
               apply simp
              apply (simp add:curDomain_def,wp)
             apply simp
            apply (wp createObjects'_psp_aligned[where sz = sz]
              createObjects'_psp_distinct[where sz = sz])
            apply (rule hoare_vcg_conj_lift)
             apply (rule hoare_post_imp[OF _ createObjects'_pspace_no_overlap
                [unfolded shiftl_t2n,where gz = tcbBlockSizeBits and sz = sz,simplified]])
              apply (simp add:objBits_simps field_simps)
             apply (simp add: objBits_simps)
            apply (wp createTCBs_tcb_at'[where sz = sz])
           apply (clarsimp simp:objBits_simps word_bits_def field_simps)
           apply (frule range_cover_le[where n = "Suc n"],simp+)
           apply (drule range_cover_offset[where p = 1,rotated])
            apply simp
           apply (simp add: objBits_defs)
          apply (((simp add: bind_assoc
                      X64_H.getObjectSize_def
                      mapM_def sequence_def Retype_H.createObject_def
                      X64_H.toAPIType_def
                      createObjects_def X64_H.createObject_def
                      Arch_createNewCaps_def comp_def
                      apiGetObjectSize_def shiftl_t2n field_simps
                      shiftL_nat mapM_x_def sequence_x_def append
                      fromIntegral_def integral_inv[unfolded Fun.comp_def])+
                   , subst monad_eq, rule createObjects_Cons
                   , (simp add: field_simps shiftl_t2n bind_assoc pageBits_def
                               objBits_simps placeNewObject_def2)+)+)[2]
        \<comment> \<open>CNode\<close>
        apply (simp add: bind_assoc
                      X64_H.getObjectSize_def
                      mapM_def sequence_def Retype_H.createObject_def
                      X64_H.toAPIType_def
                      createObjects_def X64_H.createObject_def
                      Arch_createNewCaps_def comp_def
                      apiGetObjectSize_def shiftl_t2n field_simps
                      shiftL_nat mapM_x_def sequence_x_def append
                      fromIntegral_def integral_inv[unfolded Fun.comp_def])+
        apply (subst monad_eq, rule createObjects_Cons)
              apply (simp add: field_simps shiftl_t2n bind_assoc pageBits_def
                               objBits_simps placeNewObject_def2)+
        apply (subst gsCNodes_update gsCNodes_upd_createObjects'_comm)+
        apply (simp add: modify_modify_bind)
        apply (rule fun_cong[where x=s])
        apply (rule arg_cong_bind1)+
        apply (rule arg_cong_bind[OF _ refl])
        apply (rule arg_cong[where f=modify, OF ext], simp)
        apply (rule arg_cong2[where f=gsCNodes_update, OF ext refl])
        apply (rule ext)
        apply simp

       \<comment> \<open>SmallPageObject\<close>
       apply (simp add: Arch_createNewCaps_def
                        Retype_H.createObject_def createObjects_def bind_assoc
                        X64_H.toAPIType_def X64_H.toAPIType_def
                        X64_H.createObject_def placeNewDataObject_def)
       apply (intro conjI impI)
        apply (subst monad_eq, rule createObjects_Cons)
             apply (simp_all add: field_simps shiftl_t2n pageBits_def
                        getObjectSize_def X64_H.getObjectSize_def
                        objBits_simps)[6]
        apply (simp add: bind_assoc placeNewObject_def2 objBits_simps
                         getObjectSize_def X64_H.getObjectSize_def bit_simps
                         pageBits_def add.commute append)
        apply ((subst gsUserPages_update gsCNodes_update
                    gsUserPages_upd_createObjects'_comm
                    dmo'_createObjects'_comm dmo'_gsUserPages_upd_comm
                   | simp add: modify_modify_bind o_def)+)[1]
        apply (subst monad_eq, rule createObjects_Cons)
             apply (simp_all add: field_simps shiftl_t2n pageBits_def
                        getObjectSize_def X64_H.getObjectSize_def
                        objBits_simps)[6]
        apply (simp add: bind_assoc placeNewObject_def2 objBits_simps
                         getObjectSize_def X64_H.getObjectSize_def
                         pageBits_def add.commute append)
        apply (subst gsUserPages_update gsCNodes_update
                    gsUserPages_upd_createObjects'_comm
                    dmo'_createObjects'_comm dmo'_gsUserPages_upd_comm
                   | simp add: modify_modify_bind o_def)+
      \<comment> \<open>LargePageObject\<close>
      apply (simp add: Arch_createNewCaps_def
                       Retype_H.createObject_def createObjects_def bind_assoc
                       X64_H.toAPIType_def X64_H.toAPIType_def
                       X64_H.createObject_def placeNewDataObject_def)
      apply (intro conjI impI)
       apply (subst monad_eq, rule createObjects_Cons)
            apply (simp_all add: field_simps shiftl_t2n pageBits_def bit_simps
                       getObjectSize_def X64_H.getObjectSize_def
                       objBits_simps)[6]
       apply (simp add: bind_assoc placeNewObject_def2 objBits_simps bit_simps
                        getObjectSize_def X64_H.getObjectSize_def
                        pageBits_def add.commute append)
       apply ((subst gsUserPages_update gsCNodes_update
                   gsUserPages_upd_createObjects'_comm
                   dmo'_createObjects'_comm dmo'_gsUserPages_upd_comm
                  | simp add: modify_modify_bind o_def)+)[1]
      apply (subst monad_eq, rule createObjects_Cons)
            apply (simp_all add: field_simps shiftl_t2n pageBits_def
                       X64_H.getObjectSize_def objBits_simps)[6]
      apply (simp add: bind_assoc placeNewObject_def2 objBits_simps
                        X64_H.getObjectSize_def
                       pageBits_def add.commute append)
      apply (subst gsUserPages_update gsCNodes_update
                   gsUserPages_upd_createObjects'_comm
                   dmo'_createObjects'_comm dmo'_gsUserPages_upd_comm
             | simp add: modify_modify_bind o_def)+
     \<comment> \<open>HugePageObject\<close>
     apply (simp add: Arch_createNewCaps_def
                      Retype_H.createObject_def createObjects_def bind_assoc
                      toAPIType_def X64_H.toAPIType_def
                      X64_H.createObject_def placeNewDataObject_def)
     apply (intro conjI impI)
      apply (subst monad_eq, rule createObjects_Cons)
           apply (simp_all add: field_simps shiftl_t2n pageBits_def
                      getObjectSize_def X64_H.getObjectSize_def
                      objBits_simps)[6]
      apply (simp add: bind_assoc placeNewObject_def2 objBits_simps bit_simps
                       getObjectSize_def X64_H.getObjectSize_def
                       pageBits_def add.commute append)
      apply ((subst gsUserPages_update gsCNodes_update
                    gsUserPages_upd_createObjects'_comm
                    dmo'_createObjects'_comm dmo'_gsUserPages_upd_comm
              | simp add: modify_modify_bind o_def)+)[1]
     apply (subst monad_eq, rule createObjects_Cons)
           apply (simp_all add: field_simps shiftl_t2n pageBits_def
                      X64_H.getObjectSize_def objBits_simps)[6]
     apply (simp add: bind_assoc placeNewObject_def2 objBits_simps
                       X64_H.getObjectSize_def bit_simps
                      pageBits_def add.commute append)
     apply (subst gsUserPages_update gsCNodes_update
                  gsUserPages_upd_createObjects'_comm
                  dmo'_createObjects'_comm dmo'_gsUserPages_upd_comm
            | simp add: modify_modify_bind o_def)+
   \<comment> \<open>PageTableObject\<close>
   apply (simp add:Arch_createNewCaps_def Retype_H.createObject_def
           createObjects_def bind_assoc X64_H.toAPIType_def
           X64_H.createObject_def)
         apply (subst monad_eq,rule createObjects_Cons)
             apply ((simp add: field_simps shiftl_t2n pageBits_def archObjSize_def
               getObjectSize_def X64_H.getObjectSize_def bit_simps
               objBits_simps ptBits_def)+)[6]
         apply (simp add:bind_assoc placeNewObject_def2)
         apply (simp add: pageBits_def field_simps bit_simps
               getObjectSize_def  ptBits_def archObjSize_def
               X64_H.getObjectSize_def placeNewObject_def2
               objBits_simps append)

   \<comment> \<open>PageDirectoryObject\<close>
   apply (simp add:Arch_createNewCaps_def Retype_H.createObject_def
           createObjects_def bind_assoc X64_H.toAPIType_def
           X64_H.createObject_def)
         apply (subst monad_eq,rule createObjects_Cons)
             apply ((simp add: field_simps shiftl_t2n pageBits_def archObjSize_def
               getObjectSize_def X64_H.getObjectSize_def bit_simps
               objBits_simps ptBits_def)+)[6]
         apply (simp add:bind_assoc placeNewObject_def2)
         apply (simp add: pageBits_def field_simps bit_simps
               getObjectSize_def  ptBits_def archObjSize_def
               X64_H.getObjectSize_def placeNewObject_def2
               objBits_simps append)

   \<comment> \<open>PDPointerTableObject\<close>
   apply (simp add:Arch_createNewCaps_def Retype_H.createObject_def
           createObjects_def bind_assoc X64_H.toAPIType_def
           X64_H.createObject_def)
         apply (subst monad_eq,rule createObjects_Cons)
             apply ((simp add: field_simps shiftl_t2n pageBits_def archObjSize_def
               getObjectSize_def X64_H.getObjectSize_def bit_simps
               objBits_simps ptBits_def)+)[6]
         apply (simp add:bind_assoc placeNewObject_def2)
         apply (simp add: pageBits_def field_simps bit_simps
               getObjectSize_def  ptBits_def archObjSize_def
               X64_H.getObjectSize_def placeNewObject_def2
               objBits_simps append)
    \<comment> \<open>PML4Object\<close>
         apply (simp add:Arch_createNewCaps_def Retype_H.createObject_def
           createObjects_def bind_assoc X64_H.toAPIType_def
           X64_H.createObject_def)
         apply (subgoal_tac "distinct (map (\<lambda>n. ptr + (n << 12)) [0.e.((of_nat n)::machine_word)])")
         prefer 2
          apply (clarsimp simp: objBits_simps archObjSize_def pdBits_def pageBits_def bit_simps
                                X64_H.getObjectSize_def)
          apply (subst upto_enum_word)
          apply (clarsimp simp:distinct_map)
          apply (frule range_cover.range_cover_n_le)
          apply (frule range_cover.range_cover_n_less)
          apply (rule conjI)
           apply (clarsimp simp:inj_on_def)
           apply (rule ccontr)
           apply (erule_tac bnd = "2^(word_bits - 12)" in shift_distinct_helper[rotated 3])
                apply simp
               apply (simp add:word_bits_def)
              apply (erule less_le_trans[OF word_of_nat_less])
              apply (simp add: word_of_nat_le word_bits_def)
              apply (erule less_le_trans[OF word_of_nat_less])
              apply (simp add:word_of_nat_le word_bits_def)
            apply (frule range_cover.unat_of_nat_n[OF range_cover_le[where n = n]])
             apply simp
            apply (rule ccontr)
            apply simp
            apply (drule of_nat_inj64[THEN iffD1,rotated -1])
             apply (simp_all add: word_bits_def)[3]
           apply (clarsimp)
           apply (erule_tac bnd = "2^(word_bits - 12)" in shift_distinct_helper[rotated 3])
                apply simp
               apply (simp add:word_bits_def)
             apply (simp add:word_of_nat_less word_bits_def)
             apply (erule less_le_trans[OF word_of_nat_less])
             apply (simp add:word_of_nat_le word_bits_def)
           apply (rule ccontr)
           apply (frule range_cover.unat_of_nat_n[OF range_cover_le[where n = n]])
            apply simp
           apply simp
           apply (drule of_nat_inj64[THEN iffD1,rotated -1])
            apply (simp_all add: word_bits_def)[3]
         apply (subst monad_eq,rule createObjects_Cons)
               apply ((simp add: field_simps shiftl_t2n pageBits_def archObjSize_def
                 X64_H.getObjectSize_def pdBits_def bit_simps
                 objBits_simps ptBits_def)+)[6]
         apply (simp add:objBits_simps archObjSize_def bit_simps X64_H.getObjectSize_def)
         apply (simp add:bind_assoc)
         apply (simp add: placeNewObject_def2[where val = "makeObject::X64_H.pml4e",simplified,symmetric])
         apply (rule_tac Q = "\<lambda>r s. valid_arch_state' s \<and>
           (\<forall>x\<le>of_nat n. page_map_l4_at' (ptr + (x << 12)) s) \<and> Q s" for Q in monad_eq_split)
           apply (rule sym)
           apply (subst monad_commute_simple)
           apply (rule commute_commute)
           apply (rule mapM_x_commute[where f=id])
           apply (rule placeNewObject_copyGlobalMapping_commute)
              apply (wp copyGlobalMappings_pspace_no_overlap' mapM_x_wp'| clarsimp)+
            apply (clarsimp simp:objBits_simps archObjSize_def bit_simps word_bits_conv)
            apply assumption (* resolve assumption , yuck *)
           apply (simp add:append mapM_x_append bind_assoc)
           apply (rule monad_eq_split[where Q = "\<lambda> r s.  pspace_aligned' s \<and> pspace_distinct' s
             \<and> valid_arch_state' s \<and> (\<forall>r \<le> of_nat n. page_map_l4_at' (ptr + (r << 12)) s)
             \<and>  page_map_l4_at' (ptr + ((1 + of_nat n) << 12)) s"])
           apply (rule monad_eq_split[where Q = "\<lambda> r s.  pspace_aligned' s \<and> pspace_distinct' s
             \<and> valid_arch_state' s \<and> (\<forall>r \<le> of_nat n. page_map_l4_at' (ptr + (r << 12)) s)
             \<and>  page_map_l4_at' (ptr + ((1 + of_nat n) << 12)) s"])
      apply (simp add: mapM_x_singleton)
      apply (subst add.commute[where b=ptr])+
      apply simp
     apply (wp mapM_x_wp')
     apply (rule hoare_pre)
      apply (clarsimp simp: page_map_l4_at'_def)
      apply (wp hoare_vcg_all_lift hoare_vcg_imp_lift)
     apply ((clarsimp simp: page_map_l4_at'_def)+)[2]
   apply (wp placeNewObject_pspace_aligned' placeNewObject_pspace_distinct')
   apply (simp add: placeNewObject_def2 field_simps)
   apply (rule hoare_vcg_conj_lift)
    apply (rule createObjects'_wp_subst)
    apply (wp createObjects_valid_arch[where sz=12])
   apply (rule hoare_vcg_conj_lift)
    apply (clarsimp simp: page_map_l4_at'_def )
    apply (wp hoare_vcg_all_lift hoare_vcg_imp_lift createObjects'_typ_at[where sz=12])
   apply (rule hoare_strengthen_post[OF createObjects'_page_map_l4_at'[where sz=12, simplified ptTranslationBits_def]])
   apply simp
  apply (clarsimp simp: objBits_simps page_map_l4_at'_def field_simps archObjSize_def word_bits_conv bit_simps
    range_cover_full aligned_add_aligned range_cover.aligned is_aligned_shiftl_self )
  apply (frule pspace_no_overlap'_le2[where ptr'="(ptr + (1 + of_nat n << 12))"])
   apply (subst shiftl_t2n, subst mult.commute, subst suc_of_nat)
   apply (rule order_trans[OF range_cover_bound, where n1="1+n"])
     apply (erule range_cover_le, simp)
    apply simp
   apply (rule word_sub_1_le)
   apply (drule(1) range_cover_no_0[where p="n+1"])
    apply simp
   apply simp
  apply (erule(1) range_cover_tail_mask)
  apply (rule hoare_vcg_conj_lift)
  apply (rule createObjects'_wp_subst)
  apply (wp createObjects_valid_arch[where sz=sz])
  apply (wp createObjects'_page_map_l4_at'[where sz=sz, unfolded ptTranslationBits_def]
    createObjects'_psp_aligned[where sz=sz]
    createObjects'_psp_distinct[where sz=sz] hoare_vcg_imp_lift
    createObjects'_pspace_no_overlap[where sz=sz]
  | simp add: objBits_simps archObjSize_def field_simps)+
  apply (drule range_cover_le[where n="Suc n"])
  apply simp
  apply (clarsimp simp: word_bits_def valid_pspace'_def bit_simps)
  apply (clarsimp simp: aligned_add_aligned[OF range_cover.aligned] is_aligned_shiftl_self word_bits_def)+
  done
qed

lemma createObject_def2:
  "(RetypeDecls_H.createObject ty ptr us dev >>= (\<lambda>x. return [x])) =
   createNewCaps ty ptr (Suc 0) us dev"
  apply (clarsimp simp:createObject_def createNewCaps_def placeNewObject_def2)
  apply (case_tac ty)
        apply (simp_all add: toAPIType_def)
        defer
        apply ((clarsimp simp: Arch_createNewCaps_def
          createObjects_def shiftL_nat
          X64_H.createObject_def placeNewDataObject_def
          placeNewObject_def2 objBits_simps bind_assoc
          clearMemory_def clearMemoryVM_def fun_upd_def[symmetric]
          word_size mapM_x_singleton storeWordVM_def)+)[7]
  apply (rename_tac apiobject_type)
  apply (case_tac apiobject_type)
      apply (clarsimp simp: Arch_createNewCaps_def
        createObjects_def shiftL_nat
        X64_H.createObject_def
        placeNewObject_def2 objBits_simps bind_assoc
        clearMemory_def clearMemoryVM_def
        word_size mapM_x_singleton storeWordVM_def)+
  done


lemma createNewObjects_def2:
  "\<lbrakk>dslots \<noteq> []; length ( dslots ) < 2^word_bits;
    cte_wp_at' (\<lambda>c. isUntypedCap (cteCap c)) parent s;
    \<forall>slot \<in> set dslots. cte_wp_at' (\<lambda>c. cteCap c = capability.NullCap) slot s;
    pspace_no_overlap' ptr sz s;
    caps_no_overlap'' ptr sz s;
    caps_overlap_reserved'
    {ptr..ptr + of_nat (length dslots) * 2 ^ Types_H.getObjectSize ty us - 1} s;
    valid_pspace' s;
    distinct dslots;
    valid_arch_state' s;
    range_cover ptr sz (Types_H.getObjectSize ty us) (length dslots);
    ptr \<noteq> 0; sz \<le> maxUntypedSizeBits; canonical_address (ptr && ~~ mask sz);
    ptr && ~~ mask sz \<in> kernel_mappings;
    ksCurDomain s \<le> maxDomain\<rbrakk>
   \<Longrightarrow> createNewObjects ty parent dslots ptr us d s =
       insertNewCaps ty parent dslots ptr us d s"
  apply (clarsimp simp:insertNewCaps_def createNewObjects_def neq_Nil_conv)
  proof -
  fix y ys
  have list_inc:  "\<And>n. [0.e.Suc n] = [0 .e. n] @ [n+1]"
    by simp
  assume le: "Suc (length (ys::machine_word list)) < 2 ^ word_bits"
  assume list_nc: "\<forall>slot \<in> set ys. cte_wp_at' (\<lambda>c. cteCap c = capability.NullCap) slot s"
  assume dist: "distinct ys"
  assume extra: "y\<notin> set ys" "cte_wp_at' (\<lambda>c. cteCap c = capability.NullCap) y s"
  assume not_0: "ptr \<noteq> 0"
  assume sz_limit: "sz \<le> maxUntypedSizeBits"
  assume ptr_cn: "canonical_address (ptr && ~~ mask sz)"
  assume ptr_km: "ptr && ~~ mask sz \<in> kernel_mappings"
  assume kscd: "ksCurDomain s \<le> maxDomain"
  assume valid_psp: "valid_pspace' s"
  assume valid_arch_state: "valid_arch_state' s"
  assume psp_no_overlap: "pspace_no_overlap' ptr sz s"
  assume caps_no_overlap: "caps_no_overlap'' ptr sz s"
  assume caps_reserved: "caps_overlap_reserved'
    {ptr..ptr +  (1 + of_nat (length ys)) * 2 ^ (Types_H.getObjectSize ty us) - 1} s"
  assume range_cover: "range_cover ptr sz (Types_H.getObjectSize ty us) (Suc (length ys))"
  assume unt_at: "cte_wp_at' (\<lambda>c. isUntypedCap (cteCap c)) parent s"
  show "zipWithM_x
        (\<lambda>num slot.
            RetypeDecls_H.createObject ty ((num << Types_H.getObjectSize ty us) + ptr) us d >>=
            insertNewCap parent slot)
        [0.e.of_nat (length ys)] (y # ys) s =
       (createNewCaps ty ptr (Suc (length ys)) us d >>= zipWithM_x (insertNewCap parent) (y # ys))  s"
    using le list_nc dist extra range_cover not_0 sz_limit ptr_cn ptr_km caps_reserved
    proof (induct ys arbitrary: y rule:rev_induct)
      case Nil
      show ?case
        by (clarsimp simp:zipWithM_x_def zipWith_def
          sequence_x_def createObject_def2[symmetric])
    next
      case (snoc a as b)
      have caps_r:"caps_overlap_reserved'
        {ptr..ptr + (1 + of_nat (length as)) * 2 ^ Types_H.getObjectSize ty us - 1} s"
        using snoc.prems
        apply -
        apply (erule caps_overlap_reserved'_subseteq)
        apply (cut_tac is_aligned_no_overflow
          [where ptr = "ptr + ((1 + of_nat (length as)) << APIType_capBits ty us)"
            and sz = " Types_H.getObjectSize ty us"])
          apply (clarsimp simp: power_add[symmetric] shiftl_t2n field_simps objSize_eq_capBits )
          apply (rule order_trans[OF word_sub_1_le])
           apply (drule(1) range_cover_no_0[where p = "Suc (length as)"])
            apply simp
           apply (simp add:word_arith_nat_Suc power_add[symmetric] field_simps)
          apply (simp add:shiftl_t2n)
         apply (rule aligned_add_aligned[OF range_cover.aligned])
            apply (simp add:objSize_eq_capBits)+
           apply (rule is_aligned_shiftl_self)
          apply (simp add:range_cover_def objSize_eq_capBits)+
         done
      show ?case
      apply simp
      using snoc.prems
      apply (subst upto_enum_inc_1_len)
       apply (rule word_of_nat_less)
       apply (simp add:word_bits_def minus_one_norm)
      apply (subst append_Cons[symmetric])
      apply (subst zipWithM_x_append1)
       apply (clarsimp simp:unat_of_nat64 bind_assoc)
      apply (subst monad_eq)
       apply (rule snoc.hyps)
              apply (simp add:caps_r | rule range_cover_le)+
      apply (simp add:snoc.hyps bind_assoc)
      apply (rule sym)
      apply (subst monad_eq)
       apply (erule createNewCaps_Cons[OF _ valid_psp valid_arch_state psp_no_overlap not_0])
      apply (rule sym)
      apply (simp add:bind_assoc del:upto_enum_nat)
      apply (rule_tac Q = "(\<lambda>r s. (\<forall>cap\<in>set r. cap \<noteq> capability.NullCap) \<and>
                            cte_wp_at' (\<lambda>c. isUntypedCap (cteCap c)) parent s \<and>
                            cte_wp_at' (\<lambda>c. cteCap c = capability.NullCap) b s \<and>
                            (\<forall>slot\<in>set as. cte_wp_at' (\<lambda>c. cteCap c = capability.NullCap) slot s) \<and>
                            pspace_no_overlap' (ptr + (1 + of_nat (length as) << Types_H.getObjectSize ty us))
                            (Types_H.getObjectSize ty us) s
                            \<and> valid_pspace' s \<and> valid_arch_state' s \<and> Q r s)" for Q in monad_eq_split)
        apply (subst append_Cons[symmetric])
        apply (subst zipWithM_x_append1)
        apply clarsimp
        apply assumption
        apply (clarsimp simp:field_simps)
        apply (subst monad_commute_simple[OF commute_commute])
         apply (rule new_cap_object_commute)
         apply (clarsimp)
        apply (frule_tac p = "1 + length as" in range_cover_no_0[rotated])
          apply clarsimp
          apply simp
          apply (subst (asm) Abs_fnat_hom_add[symmetric])
         apply (intro conjI)
         apply (simp add:range_cover_def word_bits_def)
           apply (rule aligned_add_aligned[OF range_cover.aligned],simp)
         apply (rule is_aligned_shiftl_self)
         apply (simp add:range_cover_def)
           apply (simp add:range_cover_def)
          apply (clarsimp simp:field_simps shiftl_t2n)
         apply (clarsimp simp:createNewCaps_def)
        apply (wp createNewCaps_not_nc createNewCaps_pspace_no_overlap'[where sz = sz]
                  createNewCaps_cte_wp_at'[where sz = sz] hoare_vcg_ball_lift
                  createNewCaps_valid_pspace[where sz = sz]
                  createNewCaps_obj_at'[where sz=sz])
          apply simp
         apply (rule range_cover_le)
           apply (simp add:objSize_eq_capBits caps_r)+
        apply (wp createNewCaps_ret_len createNewCaps_valid_arch_state)
       apply (frule range_cover_le[where n = "Suc (length as)"])
        apply simp+
       using psp_no_overlap caps_r valid_psp unt_at caps_no_overlap valid_arch_state
       apply (clarsimp simp: valid_pspace'_def objSize_eq_capBits)
       apply (auto simp: kscd)
       done
  qed
qed

lemma createNewObjects_corres_helper:
assumes check: "distinct dslots"
  and   cover: "range_cover ptr sz (Types_H.getObjectSize ty us) (length dslots)"
  and   not_0: "ptr \<noteq> 0" "length dslots \<noteq> 0"
  and sz_limit: "sz \<le> maxUntypedSizeBits"
  and  ptr_cn: "canonical_address (ptr && ~~ mask sz)"
  and  ptr_km: "ptr && ~~ mask sz \<in> kernel_mappings"
  and       c: "corres r P P' f (insertNewCaps ty parent dslots ptr us d)"
  and     imp: "\<And>s. P' s \<Longrightarrow> (cte_wp_at' (\<lambda>c. isUntypedCap (cteCap c)) parent s
  \<and> (\<forall>slot \<in> set dslots. cte_wp_at' (\<lambda>c. cteCap c = capability.NullCap) slot s)
  \<and> pspace_no_overlap' ptr sz s
  \<and> caps_no_overlap'' ptr sz s
  \<and> caps_overlap_reserved'
   {ptr..ptr + of_nat (length dslots) * 2^ (Types_H.getObjectSize ty us) - 1} s
  \<and> valid_pspace' s \<and> valid_arch_state' s \<and> ksCurDomain s \<le> maxDomain)"
shows "corres r P P' f (createNewObjects ty parent dslots ptr us d)"
  using check cover not_0 sz_limit ptr_cn ptr_km
  apply (clarsimp simp:corres_underlying_def)
  apply (frule imp)
  apply (frule range_cover.range_cover_le_n_less(1)[where 'a=machine_word_len, folded word_bits_def, OF _ le_refl])
  apply clarsimp
  apply (simp add:createNewObjects_def2)
  using c
  apply (clarsimp simp:corres_underlying_def)
  apply (drule(1) bspec)
  apply clarsimp
  done

lemma createNewObjects_wp_helper:
  assumes check: "distinct dslots"
  and   cover: "range_cover ptr sz (Types_H.getObjectSize ty us) (length dslots)"
  and   not_0: "ptr \<noteq> 0" "length dslots \<noteq> 0"
  and   sz_limit: "sz \<le> maxUntypedSizeBits"
  and   ptr_cn: "canonical_address (ptr && ~~ mask sz)"
  and   ptr_km: "ptr && ~~ mask sz \<in> kernel_mappings"
  shows "\<lbrace>P\<rbrace> insertNewCaps ty parent dslots ptr us d \<lbrace>Q\<rbrace>
  \<Longrightarrow> \<lbrace>P and (cte_wp_at' (\<lambda>c. isUntypedCap (cteCap c)) parent
  and (\<lambda>s. \<forall>slot \<in> set dslots. cte_wp_at' (\<lambda>c. cteCap c = capability.NullCap) slot s)
  and pspace_no_overlap' ptr sz
  and caps_no_overlap'' ptr sz
  and valid_pspace'
  and valid_arch_state'
  and caps_overlap_reserved'
   {ptr..ptr + of_nat (length dslots) * 2^ (Types_H.getObjectSize ty us) - 1} and (\<lambda>s. ksCurDomain s \<le> maxDomain))
  \<rbrace> (createNewObjects ty parent dslots ptr us d) \<lbrace>Q\<rbrace>"
  using assms
  apply (clarsimp simp:valid_def)
  apply (drule_tac x = s in spec)
  apply (frule range_cover.range_cover_le_n_less(1)[where 'a=machine_word_len, folded word_bits_def, OF _ le_refl])
  apply (simp add:createNewObjects_def2[symmetric])
  apply (drule(1) bspec)
  apply clarsimp
  done

lemma createObject_def3:
  "createObject =
   (\<lambda>ty ptr us d. createNewCaps ty ptr (Suc 0) us d >>= (\<lambda>m. return (hd m)))"
  apply (rule ext)+
  apply (simp add:createObject_def2[symmetric])
  done

lemma ArchCreateObject_pspace_no_overlap':
  "\<lbrace>\<lambda>s. pspace_no_overlap'
          (ptr + (of_nat n << APIType_capBits ty userSize)) sz s \<and>
        pspace_aligned' s \<and> pspace_distinct' s \<and>
        range_cover ptr sz (APIType_capBits ty userSize) (n + 2) \<and> ptr \<noteq> 0\<rbrace>
   X64_H.createObject ty
     (ptr + (of_nat n << APIType_capBits ty userSize)) userSize d
   \<lbrace>\<lambda>archCap. pspace_no_overlap'
                (ptr + (1 + of_nat n << APIType_capBits ty userSize)) sz\<rbrace>"
  apply (rule hoare_pre)
   apply (clarsimp simp:X64_H.createObject_def)
   apply wpc
          apply (wp doMachineOp_psp_no_overlap
              createObjects'_pspace_no_overlap2 hoare_when_weak_wp
              copyGlobalMappings_pspace_no_overlap'
              createObjects'_psp_aligned[where sz = sz]
              createObjects'_psp_distinct[where sz = sz]
            | simp add: placeNewObject_def2 word_shiftl_add_distrib
            | simp add: placeNewObject_def2 word_shiftl_add_distrib
            | simp add: placeNewDataObject_def placeNewObject_def2 word_shiftl_add_distrib
                        field_simps  split del: if_splits
            | clarsimp simp add: add.assoc[symmetric],wp createObjects'_pspace_no_overlap2[where n =0 and sz = sz,simplified]
            | clarsimp simp add: APIType_capBits_def objBits_simps pageBits_def)+

  apply (clarsimp simp: conj_comms)
  apply (frule(1) range_cover_no_0[where p = n])
   apply simp
  apply (subgoal_tac "is_aligned (ptr + (of_nat n << APIType_capBits ty userSize))
                                 (APIType_capBits ty userSize) ")
   prefer 2
   apply (rule aligned_add_aligned[OF range_cover.aligned],assumption)
    apply (simp add:is_aligned_shiftl_self range_cover_sz')
   apply (simp add: APIType_capBits_def)
  apply (frule range_cover_offset[rotated,where p = n])
   apply simp+
  apply (frule range_cover_le[where n = "Suc (Suc 0)"])
   apply simp
  apply (frule pspace_no_overlap'_le2)
    apply (rule range_cover_compare_offset)
     apply simp+
   apply (clarsimp simp:word_shiftl_add_distrib
              ,simp add:field_simps)
   apply (clarsimp simp:add.assoc[symmetric])
   apply (rule range_cover_tail_mask[where n =0,simplified])
    apply (drule range_cover_offset[rotated,where p = n])
     apply simp
    apply (clarsimp simp:shiftl_t2n field_simps)
    apply (metis numeral_2_eq_2)
   apply (simp add:shiftl_t2n field_simps)
  apply (intro conjI allI)
  apply (clarsimp simp: field_simps pageBits_def pdBits_def word_bits_conv archObjSize_def ptBits_def
                        APIType_capBits_def shiftl_t2n objBits_simps bit_simps
         | rule conjI | erule range_cover_le,simp)+
  done

lemma to_from_apiTypeD: "toAPIType ty = Some x \<Longrightarrow> ty = fromAPIType x"
  by (cases ty) (auto simp add: fromAPIType_def
    toAPIType_def)

lemma createObject_pspace_no_overlap':
  "\<lbrace>\<lambda>s. pspace_no_overlap'
          (ptr + (of_nat n << APIType_capBits ty userSize)) sz s \<and>
        pspace_aligned' s \<and> pspace_distinct' s
        \<and> range_cover ptr sz (APIType_capBits ty userSize) (n + 2)
        \<and> ptr \<noteq> 0\<rbrace>
   createObject ty (ptr + (of_nat n << APIType_capBits ty userSize)) userSize d
   \<lbrace>\<lambda>rv s. pspace_no_overlap'
             (ptr + (1 + of_nat n << APIType_capBits ty userSize)) sz s\<rbrace>"
  apply (rule hoare_pre)
   apply (clarsimp simp:createObject_def)
   apply wpc
    apply (wp ArchCreateObject_pspace_no_overlap')
   apply wpc
       apply wp
      apply (simp add:placeNewObject_def2)
      apply (wp doMachineOp_psp_no_overlap createObjects'_pspace_no_overlap2
        | simp add: placeNewObject_def2 curDomain_def word_shiftl_add_distrib
        field_simps)+
      apply (simp add:add.assoc[symmetric])
      apply (wp createObjects'_pspace_no_overlap2
        [where n =0 and sz = sz,simplified])
     apply (simp add:placeNewObject_def2)
     apply (wp doMachineOp_psp_no_overlap createObjects'_pspace_no_overlap2
        | simp add: placeNewObject_def2 word_shiftl_add_distrib
        field_simps)+
     apply (simp add:add.assoc[symmetric])
     apply (wp createObjects'_pspace_no_overlap2
        [where n =0 and sz = sz,simplified])
    apply (simp add:placeNewObject_def2)
    apply (wp doMachineOp_psp_no_overlap createObjects'_pspace_no_overlap2
      | simp add: placeNewObject_def2 word_shiftl_add_distrib
      field_simps)+
    apply (simp add:add.assoc[symmetric])
    apply (wp createObjects'_pspace_no_overlap2
      [where n =0 and sz = sz,simplified])
   apply (simp add:placeNewObject_def2)
   apply (wp doMachineOp_psp_no_overlap createObjects'_pspace_no_overlap2
     | simp add: placeNewObject_def2 word_shiftl_add_distrib
     field_simps)+
   apply (simp add:add.assoc[symmetric])
   apply (wp createObjects'_pspace_no_overlap2
     [where n =0 and sz = sz,simplified])
  apply clarsimp
  apply (frule(1) range_cover_no_0[where p = n])
   apply simp
  apply (frule pspace_no_overlap'_le2)
    apply (rule range_cover_compare_offset)
     apply simp+
   apply (clarsimp simp:word_shiftl_add_distrib
              ,simp add:field_simps)
   apply (clarsimp simp:add.assoc[symmetric])
   apply (rule range_cover_tail_mask[where n =0,simplified])
    apply (drule range_cover_offset[rotated,where p = n])
     apply simp
    apply (clarsimp simp:shiftl_t2n field_simps)
    apply (metis numeral_2_eq_2)
   apply (simp add:shiftl_t2n field_simps)
  apply (frule range_cover_offset[rotated,where p = n])
   apply simp+
  apply (auto simp: word_shiftl_add_distrib field_simps shiftl_t2n elim: range_cover_le,
    auto simp add: APIType_capBits_def fromAPIType_def objBits_def
        dest!: to_from_apiTypeD)
  done

lemma createObject_pspace_aligned_distinct':
  "\<lbrace>pspace_aligned' and K (is_aligned ptr (APIType_capBits ty us))
   and pspace_distinct' and pspace_no_overlap' ptr (APIType_capBits ty us)
   and K (ty = APIObjectType apiobject_type.CapTableObject \<longrightarrow> us < 28)\<rbrace>
  createObject ty ptr us d
  \<lbrace>\<lambda>xa s. pspace_aligned' s \<and> pspace_distinct' s\<rbrace>"
  apply (rule hoare_pre)
  apply (wp placeNewObject_pspace_aligned' unless_wp
      placeNewObject_pspace_distinct'
    | simp add:X64_H.createObject_def
      Retype_H.createObject_def objBits_simps
      curDomain_def placeNewDataObject_def
          split del: if_split
    | wpc | intro conjI impI)+
  apply (auto simp:APIType_capBits_def pdBits_def objBits_simps' bit_simps
    pageBits_def word_bits_def archObjSize_def ptBits_def X64_H.toAPIType_def
    split:X64_H.object_type.splits apiobject_type.splits)
  done

declare objSize_eq_capBits [simp]

lemma createNewObjects_Cons:
  assumes dlength: "length dest < 2 ^ word_bits"
  shows "createNewObjects ty src (dest @ [lt]) ptr us d =
  do createNewObjects ty src dest ptr us d;
     (RetypeDecls_H.createObject ty ((of_nat (length dest) << APIType_capBits ty us) + ptr) us d
       >>= insertNewCap src lt)
  od"
  proof -
    from dlength
    have expand:"dest\<noteq>[] \<longrightarrow> [(0::machine_word) .e. of_nat (length dest)]
      = [0.e.of_nat (length dest - 1)] @ [of_nat (length dest)]"
      apply (cases dest)
      apply clarsimp+
      apply (rule upto_enum_inc_1_len)
      apply (rule word_of_nat_less)
      apply (simp add: word_bits_conv minus_one_norm)
      done

    have length:"\<lbrakk>length dest < 2 ^ word_bits;dest \<noteq> []\<rbrakk>
      \<Longrightarrow> length [(0::machine_word) .e. of_nat (length dest - 1)] = length dest"
    proof (induct dest)
      case Nil thus ?case by simp
    next
      case (Cons x xs)
      thus ?case by (simp add:unat_of_nat64)
    qed

    show ?thesis
    using dlength
    apply (case_tac "dest = []")
     apply (simp add: zipWithM_x_def createNewObjects_def
          sequence_x_def zipWith_def)
    apply (clarsimp simp:createNewObjects_def)
    apply (subst expand)
    apply simp
    apply (subst zipWithM_x_append1)
     apply (rule length)
      apply (simp add:field_simps)+
    done
qed

lemma updateNewFreeIndex_cteCaps_of[wp]:
  "\<lbrace>\<lambda>s. P (cteCaps_of s)\<rbrace> updateNewFreeIndex slot \<lbrace>\<lambda>rv s. P (cteCaps_of s)\<rbrace>"
  by (simp add: cteCaps_of_def, wp)

lemma insertNewCap_wps[wp]:
  "\<lbrace>pspace_aligned'\<rbrace> insertNewCap parent slot cap \<lbrace>\<lambda>rv. pspace_aligned'\<rbrace>"
  "\<lbrace>pspace_distinct'\<rbrace> insertNewCap parent slot cap \<lbrace>\<lambda>rv. pspace_distinct'\<rbrace>"
  "\<lbrace>\<lambda>s. P ((cteCaps_of s)(slot \<mapsto> cap))\<rbrace>
      insertNewCap parent slot cap
   \<lbrace>\<lambda>rv s. P (cteCaps_of s)\<rbrace>"
  apply (simp_all add: insertNewCap_def)
   apply (wp hoare_drop_imps
            | simp add: o_def)+
  apply (fastforce elim!: rsubst[where P=P])
  done

crunches insertNewCap
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps)

end
end
