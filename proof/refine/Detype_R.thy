(*
 * Copyright 2014, General Dynamics C4 Systems
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright 2023, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)
theory Detype_R
imports ArchRetype_R
begin

(* FIXME arch-split: move, but where to? *)
lemmas unat_of_nat_eq_mw = unat_of_nat_eq[where 'a=machine_word_len, folded word_bits_def]
lemmas unat_minus_one_word_mw = unat_minus_one_word[where 'a=machine_word_len, folded word_bits_def]

(* FIXME: move to Lib *)
lemma exists_disj:
  "((\<exists>a. P a \<and> Q a) \<or> (\<exists>a. P a \<and> Q' a)) = (\<exists>a. P a \<and> (Q a \<or> Q' a))"
  by auto

lemma corres_return_bind: (* FIXME: move to Corres_UL *)
  "corres_underlying sr nf nf' r P P' (do return (); f od) g \<Longrightarrow> corres_underlying sr nf nf' r P P' f g"
  by simp

lemma corres_return_bind2: (* FIXME: move to Corres_UL *)
  "corres_underlying sr nf nf' r P P' f (do return (); g od) \<Longrightarrow> corres_underlying sr nf nf' r P P' f g"
  by simp

(* FIXME: move *)
lemma obj_range_mask_range:
  "obj_range p obj = mask_range p (obj_bits obj)"
  unfolding obj_range_def mask_def
  by simp

declare plus_Collect_helper2[simp]

text \<open>Establishing that the invariants are maintained
        when a region of memory is detyped, that is,
        removed from the model.\<close>

definition
  "descendants_range_in' S p \<equiv>
     \<lambda>m. \<forall>p' \<in> descendants_of' p m. \<forall>c n. m p' = Some (CTE c n) \<longrightarrow> capRange c \<inter> S = {}"

lemma null_filter_simp'[simp]:
  "null_filter' (null_filter' x) = null_filter' x"
  by (auto simp: null_filter'_def)

lemma descendants_range_in'_def2:
  "descendants_range_in' S p = (\<lambda>m. \<forall>p'\<in>descendants_of' p (null_filter' m).
  \<forall>c n. (null_filter' m) p' = Some (CTE c n) \<longrightarrow> capRange c \<inter> S = {})"
  apply (clarsimp simp: descendants_range_in'_def
                  split: if_splits)
  apply (rule ext)
  apply (rule subst[OF null_filter_descendants_of'])
   apply simp
  apply (fastforce simp: descendants_of'_def null_filter'_def
                   elim: subtree_not_Null
                   split: if_splits)
  done

definition
  "descendants_range' cap p \<equiv>
     \<lambda>m. \<forall>p' \<in> descendants_of' p m. \<forall>c n. m p' = Some (CTE c n) \<longrightarrow> capRange c \<inter> capRange cap = {}"

lemma descendants_rangeD':
  "\<lbrakk> descendants_range' cap p m; m \<turnstile> p \<rightarrow> p'; m p' = Some (CTE c n) \<rbrakk>
   \<Longrightarrow> capRange c \<inter> capRange cap = {}"
  by (simp add: descendants_range'_def descendants_of'_def)

lemma descendants_range_in_lift':
  assumes st:
    "\<And>P. \<lbrace>\<lambda>s. Q s \<and> P ((swp descendants_of') (null_filter' (ctes_of s)))\<rbrace>
         f
         \<lbrace>\<lambda>r s. P ((swp descendants_of') (null_filter' (ctes_of s)))\<rbrace>"
  assumes cap_range:
    "\<And>P p. \<lbrace>\<lambda>s. Q' s \<and> cte_wp_at' (\<lambda>c. P (capRange (cteCap c))) p s\<rbrace>
           f
           \<lbrace>\<lambda>r s. cte_wp_at' (\<lambda>c. P (capRange (cteCap c))) p s\<rbrace>"
  shows "\<lbrace>\<lambda>s. Q s \<and> Q' s \<and> descendants_range_in' S slot (ctes_of s)\<rbrace>
         f
         \<lbrace>\<lambda>r s. descendants_range_in' S slot (ctes_of s)\<rbrace>"
  apply (clarsimp simp:descendants_range_in'_def2)
  apply (subst swp_def[where f = descendants_of', THEN meta_eq_to_obj_eq,
                       THEN fun_cong, THEN fun_cong, symmetric])+
  apply (simp only: Ball_def[unfolded imp_conv_disj])
  apply (rule hoare_pre)
   apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift st cap_range)
   apply (rule_tac Q'="\<lambda>r s. cte_wp_at' (\<lambda>c. capRange (cteCap c) \<inter> S = {}) x s"
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

lemma descendants_range'_def2:
  "descendants_range' cap p = descendants_range_in' (capRange cap) p"
  by (simp add: descendants_range_in'_def descendants_range'_def)

(* we can't use a locale fixes for this, as deletionIsSafe_def can't contain a free variable,
   and the constant comes from the design spec *)
consts' arch_deletionIsSafe :: "machine_word \<Rightarrow> nat \<Rightarrow> kernel_state \<Rightarrow> machine_word \<Rightarrow> bool"

defs deletionIsSafe_def:
  "deletionIsSafe \<equiv> \<lambda>ptr bits s. \<forall>p t m r.
     (cte_wp_at' (\<lambda>cte. cteCap cte = capability.ReplyCap t m r) p s \<longrightarrow> t \<notin> mask_range ptr bits)
     \<and> arch_deletionIsSafe ptr bits s p"

defs deletionIsSafe_delete_locale_def:
  "deletionIsSafe_delete_locale \<equiv> \<lambda>ptr bits s. \<forall>p. ko_wp_at' live' p s \<longrightarrow> p \<notin> mask_range ptr bits"

defs cNodePartialOverlap_def:
  "cNodePartialOverlap \<equiv> \<lambda>cns inRange.
     \<exists>p n. cns p = Some n
           \<and> (\<not> is_aligned p (cte_level_bits + n)
              \<or> cte_level_bits + n \<ge> word_bits
              \<or> (\<not> mask_range p (cte_level_bits + n) \<subseteq> {p. inRange p}
                 \<and> \<not> mask_range p (cte_level_bits + n) \<subseteq> {p. \<not> inRange p}))"

lemma obj_relation_cuts_eqv_base_in_detype_range:
  "\<lbrakk> (y, P) \<in> obj_relation_cuts ko x; kheap s x = Some ko;
      valid_objs s; pspace_aligned s;
      valid_untyped (cap.UntypedCap d base bits idx) s \<rbrakk>
   \<Longrightarrow> (x \<in> mask_range base bits) = (y \<in> mask_range base bits)" for s :: det_state
  apply (simp add: valid_untyped_def mask_def add_diff_eq del: atLeastAtMost_iff)
  apply (subgoal_tac "x \<in> obj_range x ko")
   apply (subgoal_tac "y \<in> obj_range x ko")
    apply blast
   apply (erule(4) obj_relation_cuts_in_obj_range)
  apply (simp add: obj_range_def)
  apply (rule is_aligned_no_overflow)
  apply (erule(1) pspace_alignedD)
  done

lemma detype_pspace_relation:
  fixes s :: det_state
  assumes psp: "pspace_relation (kheap s) (ksPSpace s')"
  and     bwb: "bits < word_bits"
  and      al: "is_aligned base bits"
  and      vs: "valid_pspace s"
  and      vu: "valid_untyped (cap.UntypedCap d base bits idx) s"
  shows        "pspace_relation (kheap (detype (mask_range base bits) s))
                 (\<lambda>x. if x \<in> mask_range base bits then None else ksPSpace s' x)"
  (is "pspace_relation ?ps ?ps'")
proof -
  let ?range = "mask_range base bits"
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
  by (simp add: pspace_distinct'_def dom_if_None ps_clear_def Diff_Int_distrib)

lemma ko_wp_at_delete':
  "pspace_distinct' s \<Longrightarrow>
   ko_wp_at' P p (s \<lparr> ksPSpace := \<lambda>x. if base \<le> x \<and> x \<le> base + mask magnitude then None else ksPSpace s x \<rparr>)
    = (\<not> (base \<le> p \<and> p \<le> base + mask magnitude) \<and> ko_wp_at' P p s)"
  apply (simp add: ko_wp_at'_def ps_clear_def dom_if_None)
  apply (intro impI iffI)
   apply clarsimp
   apply (drule(1) pspace_distinctD')
   apply (simp add: ps_clear_def)
  apply (clarsimp simp: Diff_Int_distrib)
  done

lemma obj_at_delete':
  "pspace_distinct' s \<Longrightarrow>
   obj_at' P p (s \<lparr> ksPSpace := \<lambda>x. if base \<le> x \<and> x \<le> base + mask magnitude then None else ksPSpace s x \<rparr>)
    = (\<not> (base \<le> p \<and> p \<le> base + mask magnitude) \<and> obj_at' P p s)"
  unfolding obj_at'_real_def
  by (rule ko_wp_at_delete')

lemma cte_wp_at_delete':
  "\<lbrakk> s \<turnstile>' UntypedCap d base magnitude idx; pspace_distinct' s \<rbrakk> \<Longrightarrow>
   cte_wp_at' P p (s \<lparr> ksPSpace := \<lambda>x. if base \<le> x \<and> x \<le> base + mask magnitude then None else ksPSpace s x \<rparr>)
    = (\<not> (base \<le> p \<and> p \<le> base + mask magnitude) \<and> cte_wp_at' P p s)"
  apply (simp add: cte_wp_at_obj_cases' obj_at_delete')
  apply (subgoal_tac "\<forall>Q n. obj_at' Q (p - n) s \<and> tcb_cte_cases n \<noteq> None \<longrightarrow>
                             ((p - n) \<in> mask_range base magnitude)
                              = (p \<in> mask_range base magnitude)")
   apply auto[1]
  apply (clarsimp simp: obj_at'_real_def valid_cap'_def
                        valid_untyped'_def
              simp del: atLeastAtMost_iff)
  apply (drule_tac x="p - n" in spec)
  apply (clarsimp simp: ko_wp_at'_def capAligned_def
              simp del: atLeastAtMost_iff)
   apply (thin_tac "is_aligned x minUntypedSizeBits" for x)
  apply (drule(1) aligned_ranges_subset_or_disjoint)
  apply (subgoal_tac "{p, p - n} \<subseteq> obj_range' (p - n) (KOTCB obj)")
   apply (clarsimp simp del: atLeastAtMost_iff
                       simp: field_simps gen_objBits_simps obj_range'_def mask_def)
   apply fastforce
  apply (simp add: obj_range'_def neg_mask_in_mask_range[symmetric]
              del: atLeastAtMost_iff)
  apply (simp add: gen_objBits_simps)
  apply (frule(1) tcb_cte_cases_aligned_helpers)
  apply simp
  done

lemma map_to_ctes_delete:
  assumes vc: "s \<turnstile>' UntypedCap d base magnitude idx"
      and vs: "pspace_distinct' s"
  shows
  "map_to_ctes (\<lambda>x. if base \<le> x \<and> x \<le> base + mask magnitude then None else ksPSpace s x)
    = (\<lambda>x. if base \<le> x \<and> x \<le> base + mask magnitude then None else ctes_of s x)"
  using cte_wp_at_delete' [where P="(=) cte" for cte, OF vc vs]
        arg_cong [where f=Not, OF cte_wp_at_delete' [OF vc vs, where P="\<top>"]]
  apply (simp (no_asm_use) add: cte_wp_at_ctes_of)
  apply (rule ext)
  apply (case_tac "map_to_ctes (\<lambda>x. if base \<le> x \<and> x \<le> base + mask magnitude then None else ksPSpace s x) x")
   apply (fastforce split: if_split_asm)
  apply simp
  done

lemma word_range_card:
  "base \<le>base + h \<Longrightarrow> card {base..base + (h::machine_word)} = (unat h) + 1"
proof (induct h rule: word_induct2)
  case zero show ?case by simp
next
  case (suc h)
  have interval_plus_one_word32:
    "\<And>base ceil. \<lbrakk>base \<le> ceil + 1;ceil \<le> ceil + 1\<rbrakk> \<Longrightarrow>
                 {base..ceil + 1} = {base .. ceil } \<union> {ceil + (1::machine_word)}"
    by (auto intro:order_antisym simp:not_le inc_le)
  show ?case
    using suc plus_one_helper2[where n = h and x = h,simplified]
    apply (subst add.commute[where a = 1])
    apply (subst add.assoc[symmetric])
    apply (subst interval_plus_one_word32)
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

locale detype_locale' = detype_locale + constrains s :: "det_state"

locale detype_locale'_gen = detype_locale' +
  assumes arch_deletionIsSafe:
    "\<And>s s' base magnitude d idx.
     \<lbrakk>is_aligned base magnitude; valid_pspace s;
      valid_untyped (cap.UntypedCap d base magnitude idx) s;
      (s, s') \<in> state_relation\<rbrakk>
     \<Longrightarrow> arch_deletionIsSafe base magnitude s' p"
begin

lemma deletionIsSafe:
  assumes sr: "(s, s') \<in> state_relation"
  and    cap: "cap = cap.UntypedCap d base magnitude idx"
  and      vs: "valid_pspace s"
  and      al: "is_aligned base magnitude"
  and      vu: "valid_untyped (cap.UntypedCap d base magnitude idx) s"
  shows       "deletionIsSafe base magnitude s'"
proof -
  note [simp del] = atLeastatMost_subset_iff atLeastLessThan_iff atLeastAtMost_iff
                    Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex
  have "\<And>t m r. \<exists>ptr. cte_wp_at ((=) (cap.ReplyCap t m r)) ptr s
        \<Longrightarrow> t \<notin> mask_range base magnitude"
    by (fastforce dest!: valid_cap2 simp: cap obj_reply_refs_def mask_def add_diff_eq)
  hence "\<forall>ptr t m r. cte_wp_at ((=) (cap.ReplyCap t m r)) ptr s
         \<longrightarrow> t \<notin> mask_range base magnitude"
    by (fastforce simp del: split_paired_All)
  hence "\<forall>t. t \<in> mask_range base magnitude \<longrightarrow>
          (\<forall>ptr m r. \<not> cte_wp_at ((=) (cap.ReplyCap t m r)) ptr s)"
    by fastforce
  hence cte: "\<forall>t. t \<in> mask_range base magnitude \<longrightarrow>
          (\<forall>ptr m r. \<not> cte_wp_at' (\<lambda>cte. cteCap cte = ReplyCap t m r) ptr s')"
    unfolding deletionIsSafe_def
    apply -
    apply (erule allEI)
    apply (rule impI, drule(1) mp)
    apply (thin_tac "t \<in> S" for S)
    apply (intro allI)
    apply (clarsimp simp: cte_wp_at_neg2 cte_wp_at_ctes_of
                simp del: split_paired_All)
    apply (frule pspace_relation_cte_wp_atI[rotated])
      apply (rule invs_valid_objs[OF invs])
     apply (rule state_relation_pspace_relation[OF sr])
    apply (clarsimp simp: cte_wp_at_neg2 simp del: split_paired_All)
    apply (drule_tac x="(a,b)" in spec)
    apply (clarsimp simp: cte_wp_cte_at cte_wp_at_caps_of_state)
    apply (case_tac c; simp)
    apply fastforce
    done

  have arch: "\<And>p. arch_deletionIsSafe base magnitude s' p"
    by (rule arch_deletionIsSafe[OF al vs vu sr])

  thus ?thesis using cte by (auto simp: deletionIsSafe_def)
qed

end (* detype_locale'_gen *)

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

lemma ko_wp_at_state_hyp_refs_ofD:
  "\<lbrakk> ko_wp_at' P p s \<rbrakk> \<Longrightarrow> (\<exists>ko. P ko \<and> state_hyp_refs_of' s p = hyp_refs_of' ko)"
  by (fastforce simp: ko_wp_at'_def state_hyp_refs_of'_def)

lemma sym_hyp_refs_ko_wp_atD:
  "\<lbrakk> ko_wp_at' P p s; sym_refs (state_hyp_refs_of' s) \<rbrakk>
      \<Longrightarrow> (\<exists>ko. P ko \<and> state_hyp_refs_of' s p = hyp_refs_of' ko
                    \<and> (\<forall>(x, tp) \<in> hyp_refs_of' ko. (p, symreftype tp) \<in> state_hyp_refs_of' s x))"
  apply (clarsimp dest!: ko_wp_at_state_hyp_refs_ofD)
  apply (rule exI, erule conjI)
  apply (drule sym)
  apply clarsimp
  apply (erule(1) sym_refsD)
 done

locale delete_locale =
  fixes s' and base and bits and ptr and idx and d
  assumes cap: "cte_wp_at' (\<lambda>cte. cteCap cte = UntypedCap d base bits idx) ptr s'"
  and  nodesc: "descendants_range' (UntypedCap d base bits idx) ptr (ctes_of s')"
  and    invs: "invs' s'"
  and  ct_act: "ct_active' s'"
  and sa_simp: "sch_act_simple s'"
  and      al: "is_aligned base bits"
  and    safe: "deletionIsSafe base bits s'"

locale Arch_delete_locale = delete_locale + Arch

context delete_locale begin

lemma valid_objs: "valid_objs' s'"
  and        pa: "pspace_aligned' s'"
  and        pc: "pspace_canonical' s'"
  and       pkm: "pspace_in_kernel_mappings' s'"
  and        pd: "pspace_distinct' s'"
  and       vbm: "valid_bitmaps s'"
  and sym_sched: "sym_heap_sched_pointers s'"
  and       vsp: "valid_sched_pointers s'"
  and  sym_refs: "sym_refs (state_refs_of' s')"
  and  sym_hyp_refs: "sym_refs (state_hyp_refs_of' s')"
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
  and    clinks: "class_links (ctes_of s')"
  and  rep_r_fb: "reply_masters_rvk_fb (ctes_of s')"
  and      idle: "valid_idle' s'"
  and      refs: "valid_global_refs' s'"
  and      arch: "valid_arch_state' s'"
  and      virq: "valid_irq_node' (irq_node' s') s'"
  and     virqh: "valid_irq_handlers' s'"
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
  "base_bits \<equiv> mask_range base bits"

abbreviation pspace' :: pspace where
  "pspace' \<equiv> \<lambda>x. if base \<le> x \<and> x \<le> base + mask bits then None else ksPSpace s' x"

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
      apply (simp add: add_mask_fold)
     apply assumption
    using nodesc
    apply (simp add:descendants_range'_def2)
    apply (drule(1) descendants_range_inD')
     apply (simp add:asms)
    apply (simp add: add_mask_fold)
    done
qed

lemma ctes_of_valid [elim!]:
  "ctes_of s' p = Some cte \<Longrightarrow> s' \<turnstile>' cteCap cte"
  by (case_tac cte, simp add: ctes_of_valid_cap' [OF _ valid_objs])

lemma replycap_argument:
  "\<And>p t m r. cte_wp_at' (\<lambda>cte. cteCap cte = ReplyCap t m r) p s'
   \<Longrightarrow> t \<notin> mask_range base bits"
  using safe
  by (force simp: deletionIsSafe_def cte_wp_at_ctes_of)

lemma global_refs:
  "global_refs' s' \<inter> base_bits = {}"
  using cap
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (drule valid_global_refsD' [OF _ refs])
  apply (fastforce simp add: field_simps mask_def)
  done

lemma global_refs2:
  "global_refs' s' \<subseteq> (- base_bits)"
  using global_refs
  by blast

lemma idle_notRange:
  "\<forall>cref. \<not> cte_wp_at' (\<lambda>c. ksIdleThread s' \<in> capRange (cteCap c)) cref s'
  \<Longrightarrow> ksIdleThread s' \<notin> base_bits"
  apply (insert cap)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (erule_tac x=ptr in allE, clarsimp simp: field_simps mask_def)
  done

abbreviation
  "ctes' \<equiv> map_to_ctes (\<lambda>x. if base \<le> x \<and> x \<le> base + mask bits then None else ksPSpace s' x)"

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

end (* delete_locale *)

locale delete_locale_gen = delete_locale +
  assumes irq_nodes_range:
    "\<forall>irq :: irq. irq_node' s' + (ucast irq << cteSizeBits) \<notin> base_bits"

(* delete_locale_gen needs results from Arch which depend on delete_locale_gen; need results of both *)
locale delete_locale_gen_2 = delete_locale_gen +
  assumes valid_arch_tcb':
    "\<And>p tcb.
     \<lbrakk> ksPSpace s' p = Some (KOTCB tcb); is_aligned p tcbBlockSizeBits; ps_clear p tcbBlockSizeBits s';
       valid_arch_tcb' (tcbArch tcb) s' \<rbrakk>
     \<Longrightarrow> valid_arch_tcb' (tcbArch tcb) state'"
  assumes pspace_in_kernel_mappings':
    "pspace_in_kernel_mappings' state'"
  assumes valid_global_refs':
    "valid_global_refs' state'"
  assumes valid_arch_state':
    "valid_arch_state' state'"
  assumes valid_cap':
    "\<And>p c.
     \<lbrakk> s' \<turnstile>' c; cte_wp_at' (\<lambda>cte. cteCap cte = c) p s'; capRange c \<inter> mask_range base bits = {} \<rbrakk>
     \<Longrightarrow> state' \<turnstile>' c"

context delete_locale_gen begin

lemma ex_nonz_cap_notRange:
  "ex_nonz_cap_to' p s' \<Longrightarrow> p \<notin> base_bits"
  apply (clarsimp simp: ex_nonz_cap_to'_def cte_wp_at_ctes_of)
  apply (case_tac "isUntypedCap (cteCap cte)")
   apply (clarsimp simp: gen_isCap_simps)
  apply (drule subsetD[OF capAligned_zobj_refs'_capRange, rotated])
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

lemma st_tcb:
  "\<And>P p. \<lbrakk> st_tcb_at' P p s'; \<not> P Inactive; \<not> P IdleThreadState \<rbrakk> \<Longrightarrow> st_tcb_at' P p state'"
  by (fastforce simp: pred_tcb_at'_def obj_at'_real_def live'_def dest: live_notRange)

lemma deletionIsSafe_delete_locale_holds:
  "deletionIsSafe_delete_locale base bits s'"
  by (fastforce dest: live_notRange simp: deletionIsSafe_delete_locale_def)

lemma refs_notRange:
  "(x, tp) \<in> state_refs_of' s' y \<Longrightarrow> y \<notin> base_bits"
  apply (drule state_refs_of'_elemD)
  apply (erule live_notRange)
  apply (rule refs_of_live')
  apply clarsimp
  done

lemma hyp_refs_notRange:
  "(x, tp) \<in> state_hyp_refs_of' s' y \<Longrightarrow> y \<notin> base_bits"
  apply (drule state_hyp_refs_of'_elemD)
  apply (erule live_notRange)
  apply (rule hyp_refs_of_live')
  apply clarsimp
  done

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

lemma tcbSchedNexts_of_pspace':
  "\<lbrakk>pspace_aligned' s'; pspace_distinct' s'; pspace_distinct' state'\<rbrakk>
   \<Longrightarrow> (pspace' |> tcb_of' |> tcbSchedNext) = tcbSchedNexts_of s'"
  apply (rule ext)
  apply (rename_tac p)
  apply (case_tac "p \<in> base_bits")
   apply (frule untyped_range_live_idle')
   apply (clarsimp simp: opt_map_def)
   apply (case_tac "ksPSpace s' p"; clarsimp)
   apply (rename_tac obj)
   apply (case_tac "tcb_of' obj"; clarsimp)
   apply (clarsimp simp: ko_wp_at'_def obj_at'_def live'_def)
   apply (fastforce simp: pspace_alignedD' pspace_distinctD')
  apply (clarsimp simp: opt_map_def split: option.splits)
  done

lemma tcbSchedPrevs_of_pspace':
  "\<lbrakk>pspace_aligned' s'; pspace_distinct' s'; pspace_distinct' state'\<rbrakk>
   \<Longrightarrow> (pspace' |> tcb_of' |> tcbSchedPrev) = tcbSchedPrevs_of s'"
  apply (rule ext)
  apply (rename_tac p)
  apply (case_tac "p \<in> base_bits")
   apply (frule untyped_range_live_idle')
   apply (clarsimp simp: opt_map_def)
   apply (case_tac "ksPSpace s' p"; clarsimp)
   apply (rename_tac obj)
   apply (case_tac "tcb_of' obj"; clarsimp)
   apply (clarsimp simp: ko_wp_at'_def obj_at'_def live'_def)
   apply (fastforce simp: pspace_alignedD' pspace_distinctD')
  apply (clarsimp simp: opt_map_def split: option.splits)
  done

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
     apply fastforce
    apply (frule subsetD [OF cte_refs_capRange])
      apply simp
     apply assumption
    apply (frule caps_containedD' [OF _ ctes_of _ _ contained])
      apply (clarsimp dest!: isCapDs)
     apply (rule_tac x=x in notemptyI)
     apply (simp add: field_simps mask_def)
    apply (simp add: add_mask_fold)
    apply (drule objRefs_notrange)
     apply (clarsimp simp: gen_isCap_simps)
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

lemma delete_ex_cte_cap_to':
  "ex_cte_cap_to' p s' \<Longrightarrow> ex_cte_cap_to' p state'"
  apply (clarsimp simp: ex_cte_cap_to'_def)
  apply (frule non_null_present [OF cte_wp_at_weakenE'])
   apply clarsimp
  apply fastforce
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

lemma delete_ko_wp_at':
  assumes objs: "ko_wp_at' P p s' \<and> ex_nonz_cap_to' p s'"
  shows "ko_wp_at' P p state'"
  using objs
  by (clarsimp simp: ko_wp_at'_def ps_clear_def dom_if_None Diff_Int_distrib
    dest!: ex_nonz_cap_notRange)

lemma null_filter':
  assumes descs: "Q (null_filter' (ctes_of s'))"
  shows "Q (null_filter' (ctes_of state'))"
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

end (* delete_locale_gen *)

context delete_locale_gen_2 begin

lemma valid_cap2:
  "\<lbrakk> cte_wp_at' (\<lambda>cte. cteCap cte = c) p s' \<rbrakk> \<Longrightarrow> state' \<turnstile>' c"
  apply (case_tac "isUntypedCap c")
   apply (drule cte_wp_at_valid_objs_valid_cap' [OF _ valid_objs])
   apply (clarsimp simp: valid_cap'_def gen_isCap_simps valid_untyped'_def)
  apply (rule valid_cap'[rotated], assumption)
   apply (clarsimp simp: cte_wp_at_ctes_of dest!: objRefs_notrange)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  done

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
                         gen_objBits_simps)
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
                      simp: opt_map_def ko_wp_at'_def obj_at'_def live'_def)
    apply (clarsimp simp: none_top_bool_cases)
    apply (rename_tac "next")
    apply (cut_tac P=live' and p="next" in live_notRange; fastforce?)
    apply (fastforce dest!: sym_heapD1[where p=p]
                     simp: opt_map_def ko_wp_at'_def obj_at'_def live'_def)
   apply (fastforce elim!: valid_arch_tcb')
  apply (clarsimp simp: valid_cte'_def)
  apply (rule_tac p=p in valid_cap2)
  apply (clarsimp simp: ko_wp_at'_def gen_objBits_simps cteSizeBits_cte_level_bits)
  apply (erule (2) cte_wp_at_cteI')
  apply simp
  done

lemma delete_invs':
  "invs' (ksMachineState_update
           (\<lambda>ms. underlying_memory_update
              (\<lambda>m x. if base \<le> x \<and> x \<le> base + (2 ^ bits - 1) then 0 else m x) ms)
           state')" (is "invs' (?state'')")
using vds
proof (simp add: invs'_def valid_state'_def valid_pspace'_def
                 valid_mdb'_def valid_mdb_ctes_def,
       safe)
  let ?s = state'
  let ?ran = base_bits

  show "pspace_aligned' ?s" using pa
    by (simp add: pspace_aligned'_def dom_def)

  show "pspace_canonical' ?s" using pc
    by (simp add: pspace_canonical'_def dom_def)

  show "pspace_in_kernel_mappings' ?s"
    by (fact pspace_in_kernel_mappings')

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

  from sym_hyp_refs show "sym_refs (state_hyp_refs_of' ?s)"
    apply -
    apply (clarsimp simp: state_hyp_refs_ko_wp_at_eq
                   elim!: rsubst[where P=sym_refs])
    apply (rule ext)
    apply safe
    apply (simp add: hyp_refs_notRange[simplified] state_hyp_refs_ko_wp_at_eq)
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
               intro!: delete_ex_cte_cap_to')

  from idle_notRange refs
  have "ksIdleThread s' \<notin> ?ran"
    apply (simp add: cte_wp_at_ctes_of valid_global_refs'_def valid_refs'_def)
    apply blast
    done
  with idle show "valid_idle' ?s"
    apply (clarsimp simp: valid_idle'_def pred_tcb_at'_def obj_at'_def)
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
    by (clarsimp simp: valid_badges_def tree_to_ctes next_unfold')

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

  show "valid_global_refs' ?s"
    by (fact valid_global_refs')

  show "valid_arch_state' ?s"
    by (fact valid_arch_state')

  show "valid_irq_node' (irq_node' s') ?s"
    using virq irq_nodes_range
    by (simp add: valid_irq_node'_def mult.commute mult.left_commute ucast_ucast_mask_8)

  show "valid_irq_handlers' ?s" using virqh
    apply (simp add: valid_irq_handlers'_def irq_issued'_def
                     cteCaps_of_def tree_to_ctes Ball_def)
    apply (erule allEI)
    apply (clarsimp simp: ran_def)
    done

  from irq_ctrl
  show "irq_control ?ctes'"
    by (clarsimp simp: irq_control_def)

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
    apply (case_tac ko, simp_all add: gen_objBits_simps)
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
     apply clarsimp
     apply (case_tac "tcbState obj"; clarsimp simp: live'_def)
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
     apply (clarsimp simp: live'_def)
     apply (case_tac "tcbState obj"; clarsimp)
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

qed

end (* delete_locale_gen_2 *)

lemma cNodeNoPartialOverlap:
  "corres dc
     (\<lambda>s. \<exists>cref. cte_wp_at ((=) (cap.UntypedCap d base magnitude idx)) cref s
                 \<and> valid_objs s \<and> pspace_aligned s)
     \<top>
     (return x)
     (stateAssert (\<lambda>s. \<not> cNodePartialOverlap (gsCNodes s)
                  (\<lambda>x. base \<le> x \<and> x \<le> base + mask magnitude)) [])"
  apply (simp add: stateAssert_def assert_def)
  apply (rule corres_symb_exec_r[OF _ get_sp])
    apply (rule corres_req[rotated], subst if_P, assumption)
     apply simp
    apply (clarsimp simp: cNodePartialOverlap_def)
    apply (drule(1) cte_wp_valid_cap)
    apply (clarsimp simp: valid_cap_def valid_untyped_def cap_table_at_gsCNodes_eq
                          obj_at_def is_cap_table)
    apply (frule(1) pspace_alignedD)
    apply (simp add: add_mask_fold)
    apply (elim allE, drule(1) mp, simp add: obj_range_def valid_obj_def cap_aligned_def)
    (* avoid unfolding word_bits in proof below to keep it generic *)
    apply (erule is_aligned_get_word_bits[where 'a=machine_word_len, folded word_bits_def])
     apply (clarsimp simp: is_aligned_no_overflow_mask add_mask_fold)
     apply (blast intro: order_trans)
    apply (simp add: is_aligned_no_overflow_mask
                     power_overflow[where 'a=machine_word_len, folded word_bits_def])
   apply wp+
  done

crunch doMachineOp
  for gsCNodes[wp]: "\<lambda>s. P (gsCNodes s)"
  and deletionIsSafe_delete_locale[wp]: "deletionIsSafe_delete_locale base magnitude"
  (simp: deletionIsSafe_delete_locale_def)

lemma detype_tcbSchedNexts_of:
  "\<lbrakk>pspace_aligned' s'; pspace_distinct' s'; \<forall>p. p \<in> S \<longrightarrow> \<not> ko_wp_at' live' p s'\<rbrakk>
   \<Longrightarrow> ((\<lambda>x. if x \<in> S then None else ksPSpace s' x) |> tcb_of' |> tcbSchedNext)
       = tcbSchedNexts_of s'"
  using pspace_alignedD' pspace_distinctD'
  apply (clarsimp simp: opt_map_def)
  apply (rule ext)
  apply (rename_tac s)
  apply (clarsimp simp: ko_wp_at'_def live'_def split: option.splits)
  apply (drule_tac x=s in spec)
  apply force
  done

lemma detype_tcbSchedPrevs_of:
  "\<lbrakk>pspace_aligned' s'; pspace_distinct' s'; \<forall>p. p \<in> S \<longrightarrow> \<not> ko_wp_at' live' p s'\<rbrakk>
   \<Longrightarrow> ((\<lambda>x. if x \<in> S then None else ksPSpace s' x) |> tcb_of' |> tcbSchedPrev)
       = tcbSchedPrevs_of s'"
  using pspace_alignedD' pspace_distinctD'
  using pspace_alignedD' pspace_distinctD'
  apply (clarsimp simp: opt_map_def)
  apply (rule ext)
  apply (rename_tac s)
  apply (clarsimp simp: ko_wp_at'_def live'_def split: option.splits)
  apply (drule_tac x=s in spec)
  apply force
  done

lemma detype_inQ:
  "\<lbrakk>pspace_aligned' s'; pspace_distinct' s'; \<forall>p. p \<in> S \<longrightarrow> \<not> ko_wp_at' live' p s'\<rbrakk>
   \<Longrightarrow> \<forall>d p. (inQ d p |< ((\<lambda>x. if x \<in> S then None else ksPSpace s' x) |> tcb_of'))
             = (inQ d p |< tcbs_of' s')"
  using pspace_alignedD' pspace_distinctD'
  using pspace_alignedD' pspace_distinctD'
  apply (clarsimp simp: opt_map_def)
  apply (rule ext)
  apply (rename_tac s)
  apply (clarsimp simp: inQ_def opt_pred_def ko_wp_at'_def live'_def split: option.splits)
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
  apply (clarsimp simp: ready_queues_relation_def Let_def)
  apply (frule (1) detype_tcbSchedNexts_of[where S="{lower..upper}"]; simp)
  apply (frule (1) detype_tcbSchedPrevs_of[where S="{lower..upper}"]; simp)
  apply (frule (1) detype_inQ[where S="{lower..upper}"]; simp)
  apply (fastforce simp add: detype_def wrap_ext_det_ext_ext_def)
  done

lemma doMachineOp_modify:
  "doMachineOp (modify g) = modify (ksMachineState_update g)"
  apply (simp add: doMachineOp_def split_def select_f_returns)
  apply (rule ext)
  apply (simp add: simpler_gets_def simpler_modify_def bind_def)
  done

lemma valid_untyped_no_overlap:
  "\<lbrakk> valid_untyped' d ptr bits idx s; is_aligned ptr bits; valid_pspace' s \<rbrakk>
  \<Longrightarrow> pspace_no_overlap' ptr bits (s\<lparr>ksPSpace := ksPSpace s |` (- mask_range ptr bits)\<rparr>)"
  apply (clarsimp simp del: atLeastAtMost_iff
            simp: pspace_no_overlap'_def valid_cap'_def valid_untyped'_def)
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
    apply (subgoal_tac "ptr \<in> mask_range x (objBitsKO ko)")
     apply (clarsimp simp:p_assoc_help mask_def)
    apply (clarsimp simp:p_assoc_help mask_def)
   apply (fastforce simp: mask_def add_diff_eq)+
  done

(* Proving the reordering here *)

lemma createObjects'_wp_subst:
  "\<lbrakk>\<lbrace>P\<rbrace>createObjects a b c d\<lbrace>\<lambda>r. Q\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace>createObjects' a b c d\<lbrace>\<lambda>r. Q\<rbrace>"
  apply (clarsimp simp:createObjects_def valid_def return_def bind_def)
  apply (drule_tac x = s in spec)
  apply (clarsimp simp:split_def)
  apply auto
  done

definition pspace_no_overlap_cell' where
  "pspace_no_overlap_cell' p \<equiv> \<lambda>kh.
     \<forall>x ko. kh x = Some ko \<longrightarrow> p \<notin> mask_range x (objBitsKO ko)"

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
     apply (clarsimp dest!: koType_objBitsKO)
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
  apply (clarsimp simp:ObjectInstances_H.updateObject_cte gen_objBits_simps)
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
         tcbCTableSlot_def tcbVTableSlot_def gen_objBits_simps
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
  apply (simp add: cte_wp_at'_def getObject_def gets_def get_def bind_def return_def split_def
                   assert_opt_def fail_def
              split: option.splits)
  apply (clarsimp simp:loadObject_cte)
  apply (rename_tac obj)
  apply (case_tac obj; simp)
         apply ((simp add: typeError_def fail_def cte_check_def
                      split: Structures_H.kernel_object.splits)+)[5]
    apply (simp add: loadObject_cte cte_check_def tcbIPCBufferSlot_def tcbCallerSlot_def
                     tcbReplySlot_def tcbCTableSlot_def tcbVTableSlot_def gen_objBits_simps
                     cteSizeBits_def)
    apply (simp add: alignCheck_def bind_def alignError_def fail_def return_def gen_objBits_simps
                     magnitudeCheck_def in_monad is_aligned_mask when_def unless_def
                split: option.splits)
    apply (intro conjI impI allI; simp add: not_le)
   apply (clarsimp simp:cte_check_def)
   apply (simp add: alignCheck_def bind_def alignError_def fail_def return_def gen_objBits_simps
                    magnitudeCheck_def in_monad is_aligned_mask when_def unless_def
               split: option.splits)
   apply (intro conjI impI allI; simp add:not_le)
  apply (simp add: typeError_def fail_def cte_check_def split: Structures_H.kernel_object.splits)
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
    have "\<And>s'. \<lbrakk>cte_check obj src a m; ksPSpace s' a = Some obj\<rbrakk> \<Longrightarrow> src \<in> {a..a + mask (objBitsKO obj)}"
      apply (cases obj; clarsimp simp add: cte_check_def gen_objBits_simps is_aligned_no_overflow_mask)
      (* TCB *)
      apply (clarsimp simp: tcbSlot_defs add.commute is_aligned_no_wrap' add.commute[where b=a]
                            word_plus_mono_right)
      apply (rule conjI)
        subgoal by (auto simp add: cte_check_def gen_objBits_simps diff_eq_eq add.commute
                                   is_aligned_no_wrap')
      apply (metis (lifting) add_diff_cancel_left' is_aligned_no_overflow_mask mask_eq
                             shiftl_1 word_diff_ls(3) word_less_sub_1
                             tcb_slots_less_2p_tcbBlockSizeBits(4,5,6,7))
      done

    thus "\<And>s'. \<lbrakk>cte_check obj src a m; ksPSpace s' a = Some obj\<rbrakk> \<Longrightarrow> src \<in> {a..a + 2 ^ objBitsKO obj - 1}"
      by (auto simp: ptr_range_mask_range)
  qed

  note [simp del] = usableUntypedRange.simps atLeastAtMost_iff
                    atLeastatMost_subset_iff atLeastLessThan_iff
                    Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex

  (* avoid unfolding word_bits in proof below to keep it generic *)
  note base_member_set' = base_member_set[where 'a=machine_word_len, folded word_bits_def]

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
   apply (auto simp add: ko_wp_at'_def)[1]
  apply (clarsimp simp add: ko_wp_at'_def)
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
  apply (drule base_member_set'[OF pspace_alignedD'], (solves simp)+)+
  apply (auto simp: field_simps mask_def)
  done

  assume
    "{(ptr, s)} = fst (locateCTE src s)"
    "(r, s') \<in> fst (f s)"
    "pspace_aligned' s"
    "pspace_distinct' s"
    "(P1 and P2 and P3 and P4) s"
  thus ?thesis
  using assms step1
  by (clarsimp simp: singleton_locateCTE)
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
   apply (clarsimp simp: shiftL_nat p_assoc_help)
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
  by (auto simp: gen_objBits_simps cteSizeBits_def alignError_def
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
  (* avoid LENGTH for machine words to keep proof generic *)
  apply (rule range_cover_rel[OF range_cover_full[where 'a=machine_word_len, folded word_bits_def]])
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
  (* avoid LENGTH for machine words to keep proof generic *)
  apply (rule range_cover_rel[OF range_cover_full[where 'a=machine_word_len, folded word_bits_def]])
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
  apply (erule(2) Retype_R.retype_aligned_distinct'[unfolded data_map_insert_def[symmetric]])
  (* avoid LENGTH for machine words to keep proof generic *)
  apply (rule range_cover_rel[OF range_cover_full[where 'a=machine_word_len, folded word_bits_def]])
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
   (* avoid LENGTH for machine words to keep proof generic *)
   apply (rule range_cover_rel[OF range_cover_full[where 'a=machine_word_len, folded word_bits_def]])
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
  (* avoid LENGTH for machine words to keep proof generic *)
  apply (auto simp: range_cover_full[where 'a=machine_word_len, folded word_bits_def])
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
  apply (clarsimp simp:monad_commute_def simpler_modify_def bind_def split_def return_def)
  apply (subst simpler_placeNewObject_def; (simp add:range_cover_def)?)
  apply (clarsimp simp: simpler_modify_def)
  (* avoid LENGTH for machine words to keep proof generic *)
  apply (frule(1) range_cover_full[where 'a=machine_word_len, folded word_bits_def])
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
     apply (clarsimp simp:field_simps mask_def)
    apply (clarsimp)
   apply (drule_tac x = x and s = s in pspace_no_overlapD'[rotated])
    apply (simp)
   apply (clarsimp simp:field_simps mask_def)
  apply (subgoal_tac "pspace_aligned' (ksPSpace_update (\<lambda>ps. ps(ptr' \<mapsto> f (ps ptr'))) s)")
   prefer 2
   apply (subst pspace_aligned'_def)
   apply (rule ballI)
   apply (erule domE)
   apply (clarsimp simp:ko_wp_at'_def split:if_split_asm)
   apply (drule(1) pspace_alignedD')+
   apply simp
  apply (simp add:simpler_placeNewObject_def)
  apply (clarsimp simp:simpler_modify_def Fun.comp_def singleton_iff image_def)
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
   apply (clarsimp simp:range_cover_def ptr_add_def obj_range'_def p_assoc_help)
  apply simp
  done

lemma cte_update_objBits[simp]:
  "(objBitsKO (cte_update cte b src a)) = objBitsKO b"
  by (case_tac b,
     (simp add: gen_objBits_simps cte_update_def)+)

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
  apply (clarsimp simp: cte_wp_at'_def getObject_def gets_def split_def get_def bind_def return_def
                        ko_wp_at'_def lookupAround2_char1 assert_opt_def)
  apply (clarsimp split:option.splits
                  simp:fail_def return_def lookupAround2_char1)
  apply (rename_tac ko)
  apply (case_tac ko;
           clarsimp simp: cte_check_def gen_objBits_simps cte_update_def dest!: pspace_distinctD')
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
  apply (clarsimp simp: doMachineOp_def split_def simpler_modify_def
                        gets_def get_def return_def bind_def select_f_def)
  apply (clarsimp simp: monad_commute_def bind_def return_def)
  apply fastforce
  done

lemma magnitudeCheck_det:
  "\<lbrakk>ksPSpace s ptr = Some ko; is_aligned ptr (objBitsKO ko);
    ps_clear ptr (objBitsKO ko) s\<rbrakk>
   \<Longrightarrow> magnitudeCheck ptr (snd (lookupAround2 ptr (ksPSpace s)))
                          (objBitsKO ko) s =
       ({((), s)},False)"
  apply (frule in_magnitude_check'[THEN iffD2])
      apply (rule objBitsKO_pos_power2)
     apply simp+
  apply (subgoal_tac
           "\<not> snd (magnitudeCheck ptr (snd (lookupAround2 ptr (ksPSpace s))) (objBitsKO ko) s)")
   apply (drule singleton_in_magnitude_check)
   apply (drule_tac x = s in spec)
   apply (case_tac
            "(magnitudeCheck ptr (snd (lookupAround2 ptr (ksPSpace s))) (objBitsKO ko) s)")
   apply simp
  apply (rule ccontr)
  apply (clarsimp simp: magnitudeCheck_assert assert_def fail_def return_def
                  split: if_splits option.splits)
  done

lemma in_dom_eq:
  "m a = Some obj \<Longrightarrow> dom (\<lambda>b. if b = a then Some g else m b) = dom m"
  by (rule set_eqI,clarsimp simp:dom_def)

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

lemma setCTE_when_doMachineOp_commute:
  assumes nf: "no_fail Q (doMachineOp x)"
  shows "monad_commute (cte_at' dest and pspace_aligned' and pspace_distinct' and Q)
  (setCTE dest cte)
  (when P (doMachineOp x))"
  apply (cases P; simp add: setCTE_doMachineOp_commute nf)
  apply (rule monad_commute_guard_imp)
   apply (rule return_commute[THEN commute_commute])
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
  apply (clarsimp simp:projectKO_def projectKO_opt_tcb alignCheck_def is_aligned_mask
                       gen_objBits_simps unless_def)
  apply (clarsimp simp:bind_def return_def)
  apply (intro conjI)
   apply (intro set_eqI iffI)
    apply clarsimp
    apply (subst (asm) in_magnitude_check')
     apply (simp add: is_aligned_mask)+
    apply (rule bexI[rotated])
     apply (rule in_magnitude_check'[THEN iffD2])
      apply (simp add:is_aligned_mask)+
   apply (clarsimp simp:image_def)
  apply (clarsimp simp: magnitudeCheck_assert assert_def objBits_def
                        return_def fail_def lookupAround2_char2
                  split:option.splits if_split_asm)
  apply (rule ccontr)
  apply (simp add:ps_clear_def field_simps)
  apply (erule_tac x = x2 in in_empty_interE)
   apply (clarsimp simp:less_imp_le)
   apply (rule conjI)
    apply (subst add.commute)
    apply (rule word_diff_ls')
     apply (clarsimp simp:field_simps not_le plus_one_helper mask_def)
    apply (simp add:field_simps is_aligned_no_overflow_mask flip: is_aligned_mask)
   apply simp
  apply auto
  done

lemma threadSet_det:
  "tcb_at' ptr s
   \<Longrightarrow> threadSet f ptr s =
       modify (ksPSpace_update
                 (\<lambda>ps. ps(ptr \<mapsto> (\<lambda>t. case t of Some (KOTCB tcb) \<Rightarrow> KOTCB (f tcb)) (ps ptr)))) s"
  apply (clarsimp simp add: threadSet_def bind_def obj_at'_def)
  apply (subst getTCB_det, simp add: ko_wp_at'_def)+
  apply (clarsimp simp: setObject_def gets_def get_def)
  apply (subst bind_def)
  apply (clarsimp simp: split_def)
  apply (simp add: lookupAround2_known1 bind_assoc projectKO_def assert_opt_def
                   updateObject_default_def projectKO_opt_tcb)
  apply (clarsimp simp: alignCheck_def unless_def when_def is_aligned_mask gen_objBits_simps)
  apply (clarsimp simp: magnitudeCheck_det bind_def)
  apply (cut_tac ko = "KOTCB obj" in magnitudeCheck_det)
     apply (simp add: gen_objBits_simps is_aligned_mask)+
  apply (clarsimp simp: modify_def get_def put_def bind_def)
  done

lemma setCTE_modify_tcbDomain_commute:
  "monad_commute
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
      apply (clarsimp simp: monad_commute_def bind_def simpler_modify_def return_def)
      apply (clarsimp simp: threadSet_det simpler_modify_def)
      apply (subgoal_tac "tcb_at' ptr (ksPSpace_update (\<lambda>ps. ps(a \<mapsto> cte_update cte (the (ps a)) src a)) s)")
      prefer 2
       apply (clarsimp simp:obj_at'_def)
       apply (intro conjI impI)
           apply simp
          apply (clarsimp simp: projectKO_opt_tcb split:Structures_H.kernel_object.split_asm)
          apply (simp add:cte_update_def)
         apply (clarsimp simp: projectKO_opt_tcb split:Structures_H.kernel_object.split_asm)
         apply (simp add:ps_clear_def)
       apply (simp add:ps_clear_def)
       apply (rule ccontr,simp)
       apply (erule in_emptyE)
       apply (clarsimp simp:ko_wp_at'_def)
       apply blast
      apply (simp add:threadSet_det simpler_modify_def)
      apply (subst (asm) obj_at'_def)
      apply (thin_tac "tcb_at' ptr P" for P)
      apply (clarsimp simp: obj_at'_def projectKO_opt_tcb,
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
       apply (clarsimp simp: gen_objBits_simps)
      apply wpsimp+
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

crunch curDomain
  for inv[wp]: P

lemma placeNewObject_tcb_at':
  "\<lbrace>pspace_aligned' and pspace_distinct' and pspace_no_overlap' ptr (objBits (makeObject::tcb))
    and K (is_aligned ptr  (objBits (makeObject::tcb)))\<rbrace>
   placeNewObject ptr (makeObject::tcb) 0
   \<lbrace>\<lambda>_ s. tcb_at' ptr s \<rbrace>"
  apply (simp add: placeNewObject_def placeNewObject'_def split_def alignError_def)
  apply wpsimp
  apply (clarsimp simp: obj_at'_def gen_objBits_simps ps_clear_def)
  apply (fastforce intro!: set_eqI dest: pspace_no_overlap_disjoint' simp: add_mask_fold)
  done

lemma monad_commute_if_weak_r:
  "\<lbrakk> monad_commute P1 f h1; monad_commute P2 f h2\<rbrakk> \<Longrightarrow>
   monad_commute (P1 and P2) f (if d then h1 else h2)"
  apply (clarsimp)
  apply (intro conjI impI)
   apply (erule monad_commute_guard_imp,simp)+
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
   apply (simp add: obj_range'_def gen_objBits_simps is_aligned_no_overflow_mask)
  apply (intro exI conjI, assumption)
  apply (clarsimp simp: gen_objBits_simps obj_range'_def word_and_le2 and_neg_mask_plus_mask_mono)
  done

lemma pspace_no_overlapD2':
  "\<lbrakk>is_aligned ptr sz; pspace_no_overlap' ptr sz s;sz < word_bits;
    ctes_of s slot = Some cte\<rbrakk>
   \<Longrightarrow> slot \<noteq> ptr"
   apply (drule ctes_of_ko_at)
   apply clarsimp
   apply (drule(1) pspace_no_overlapD')
   apply (erule in_empty_interE)
    apply (simp add:obj_range'_def add_mask_fold)
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

(* FIXME: move *)
lemma assert_commute2:
  "empty_fail f \<Longrightarrow> monad_commute \<top> (assert G) f"
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

lemma dmo_gsUntypedZeroRanges_commute:
  "monad_commute \<top> (modify (\<lambda>s. s\<lparr>gsUntypedZeroRanges := f (gsUntypedZeroRanges s)\<rparr>))
                   (doMachineOp m)"
  apply (clarsimp simp: monad_commute_def doMachineOp_def)
  apply monad_eq
  by (auto simp: select_f_def)

(* FIXME: move *)
lemma monad_commute_If_rhs:
  "monad_commute P a b \<Longrightarrow> monad_commute Q a c
   \<Longrightarrow> monad_commute (\<lambda>s. (R \<longrightarrow> P s) \<and> (\<not> R \<longrightarrow> Q s)) a (if R then b else c)"
  by simp

lemma case_eq_if_isUntypedCap:
  "(case c of UntypedCap _ _ _ _ \<Rightarrow> x | _ \<Rightarrow> y)
   = (if isUntypedCap c then x else y)"
  by (cases c, simp_all add: gen_isCap_simps)

locale Detype_R =
  assumes deleteObjects_null_filter:
    "\<And>d ptr bits idx p P.
     \<lbrace>cte_wp_at' (\<lambda>c. cteCap c = UntypedCap d ptr bits idx) p
       and invs' and ct_active' and sch_act_simple
       and (\<lambda>s. descendants_range' (UntypedCap d ptr bits idx) p (ctes_of s))
       and (\<lambda>s. P (null_filter' (ctes_of s)))
       and K (bits < word_bits \<and> is_aligned ptr bits)\<rbrace>
     deleteObjects ptr bits
     \<lbrace>\<lambda>rv s.  P (null_filter' (ctes_of s))\<rbrace>"
  assumes deleteObjects_invs':
    "\<And>d ptr bits idx p.
     \<lbrace>cte_wp_at' (\<lambda>c. cteCap c = UntypedCap d ptr bits idx) p
       and invs' and ct_active' and sch_act_simple
       and (\<lambda>s. descendants_range' (UntypedCap d ptr bits idx) p (ctes_of s))
       and K (bits < word_bits \<and> is_aligned ptr bits)\<rbrace>
     deleteObjects ptr bits
     \<lbrace>\<lambda>rv. invs'\<rbrace>"
  assumes createObject_cte_wp_at':
    "\<And>ty us ptr P slot d.
     \<lbrace>\<lambda>s. Types_H.getObjectSize ty us < word_bits \<and>
          is_aligned ptr (Types_H.getObjectSize ty us) \<and>
          pspace_no_overlap' ptr (Types_H.getObjectSize ty us) s \<and>
          cte_wp_at' (\<lambda>c. P c) slot s \<and> pspace_aligned' s \<and>
          pspace_distinct' s\<rbrace>
     RetypeDecls_H.createObject ty ptr us d
     \<lbrace>\<lambda>r s. cte_wp_at' (\<lambda>c. P c) slot s \<rbrace>"
  assumes createObject_setCTE_commute:
    "\<And>src ptr ty us d cte.
     monad_commute
       (cte_wp_at' (\<lambda>_. True) src and
          pspace_aligned' and pspace_distinct' and
          pspace_no_overlap' ptr (Types_H.getObjectSize ty us) and
          valid_arch_state' and K (ptr \<noteq> src) and
          K (is_aligned ptr (Types_H.getObjectSize ty us)) and
          K (Types_H.getObjectSize ty us < word_bits))
       (RetypeDecls_H.createObject ty ptr us d)
       (setCTE src cte)"
  assumes createObject_gsUntypedZeroRanges_commute:
    "\<And>ty ptr us dev.
     monad_commute
       \<top>
       (RetypeDecls_H.createObject ty ptr us dev)
       (modify (\<lambda>s. s \<lparr> gsUntypedZeroRanges := f (gsUntypedZeroRanges s) \<rparr> ))"
  assumes createNewCaps_not_nc:
    "\<And>ty ptr n us d.
     \<lbrace>\<top>\<rbrace> createNewCaps ty ptr n us d \<lbrace>\<lambda>r s. (\<forall>cap\<in>set r. cap \<noteq> capability.NullCap)\<rbrace>"

context Detype_R begin

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
  by (safe intro!: hoare_strengthen_post[OF deleteObjects_invs'])

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
       apply (wp getCTE_wp hoare_vcg_imp_lift hoare_vcg_disj_lift
                 updateMDB_pspace_no_overlap' setCTE_pspace_no_overlap' updateMDB_valid_arch_state'
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
    apply (frule_tac slot = "(mdbNext (cteMDBNode cte))" in pspace_no_overlapD2')
    apply simp+
  apply (clarsimp simp:weak_valid_dlist_def)
  apply (drule_tac x = "parent " in spec)
   apply clarsimp
  done

crunch updateNewFreeIndex
  for pspace_aligned'[wp]: "pspace_aligned'"
  and pspace_distinct'[wp]: "pspace_distinct'"
  and pspace_canonical'[wp]: "pspace_canonical'"
  and valid_arch_state'[wp]: "valid_arch_state'"
  and pspace_no_overlap'[wp]: "pspace_no_overlap' ptr n"
  and ctes_of[wp]: "\<lambda>s. P (ctes_of s)"
  and pspace_in_kernel_mappings'[wp]: "pspace_in_kernel_mappings'"

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
             getCTE_wp updateMDB_valid_arch_state' setCTE_weak_cte_wp_at setCTE_pspace_no_overlap')
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
    apply (simp add:word_le_sub1 shiftl_t2n mask_def field_simps)
    done
qed

lemma doMachineOp_psp_no_overlap:
  "\<lbrace>\<lambda>s. pspace_no_overlap' ptr sz s \<and> pspace_aligned' s \<and> pspace_distinct' s \<rbrace>
   doMachineOp f
   \<lbrace>\<lambda>y s. pspace_no_overlap' ptr sz s\<rbrace>"
  by (wp pspace_no_overlap'_lift,simp)

lemma createObjects'_psp_distinct:
  "\<lbrace> pspace_aligned' and pspace_distinct' and pspace_no_overlap' ptr sz and
     K (range_cover ptr sz ((objBitsKO ko) + us) n \<and> n \<noteq> 0 \<and>
        is_aligned ptr (objBitsKO ko + us) \<and> objBitsKO ko + us < word_bits) \<rbrace>
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
  "\<lbrace> pspace_aligned' and pspace_distinct' and pspace_no_overlap' ptr sz and
     K (range_cover ptr sz ((objBitsKO ko) + us) n \<and> n \<noteq> 0 \<and>
     is_aligned ptr (objBitsKO ko + us) \<and> objBitsKO ko + us < word_bits)\<rbrace>
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

lemma pspace_no_overlap'_le:
  assumes psp: "pspace_no_overlap' ptr sz s" "sz'\<le> sz"
  assumes b: "sz < word_bits"
  shows "pspace_no_overlap' ptr sz' s"
proof -
  note no_simps [simp del] = untyped_range.simps usable_untyped_range.simps atLeastAtMost_iff
                             atLeastatMost_subset_iff atLeastLessThan_iff
                             Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex
  have diff_cancel: "\<And>a b c. (a::machine_word) + b - c = b + (a - c)"
    by simp
  have bound: "(ptr && ~~ mask sz') - (ptr && ~~ mask sz) \<le> mask sz - mask sz'"
    using neg_mask_diff_bound[OF psp(2)]
    by (simp add: mask_def)
  show ?thesis
    using psp
    apply (clarsimp simp:pspace_no_overlap'_def)
    apply (drule_tac x = x in spec)
    apply clarsimp
    apply (erule disjoint_subset2[rotated])
    apply (clarsimp simp: no_simps)
    apply (rule word_plus_mcs[OF _  is_aligned_no_overflow_mask])
     apply (simp add:diff_cancel p_assoc_help)
     apply (rule le_plus)
      apply (rule bound)
     apply (erule mask_mono)
    apply simp
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

lemma no_overlap_check:
  "\<lbrakk>range_cover ptr sz bits n; pspace_no_overlap' ptr sz s;
    pspace_aligned' s;n\<noteq> 0\<rbrakk>
   \<Longrightarrow> case_option (return ())
                   (\<lambda>x. assert (fst x < ptr))
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
   apply (clarsimp simp: power_add[symmetric] shiftl_t2n field_simps)
  apply (rule neq_0_no_wrap)
   apply (clarsimp simp: power_add[symmetric] shiftl_t2n field_simps)
  apply simp
  done
qed

lemma createObjects_Cons:
  "\<lbrakk>range_cover ptr sz (objBitsKO val + us) (Suc (Suc n));
    pspace_distinct' s;pspace_aligned' s;
    pspace_no_overlap' ptr sz s;pspace_aligned' s; ptr \<noteq> 0\<rbrakk>
   \<Longrightarrow> createObjects' ptr (Suc (Suc n)) val us s =
       (do createObjects' ptr (Suc n) val us;
           createObjects' (((1 + of_nat n) << (objBitsKO val + us)) + ptr)
                          (Suc 0) val us
        od) s"
  supply option.case_cong[cong] subst_all [simp del]
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
          apply (clarsimp)
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

lemma ksArchState_upd_createObjects'_comm:
  "do _ \<leftarrow> modify (\<lambda>s. ksArchState_update (f (ksArchState s)) s);
      x \<leftarrow> createObjects' ptr n obj us;
      m x
   od =
   do x \<leftarrow> createObjects' ptr n obj us;
      _ \<leftarrow> modify (\<lambda>s. ksArchState_update (f (ksArchState s)) s);
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
  "doMachineOp f >>= (\<lambda>y. gets ksPSpace >>= m y) =
   gets ksPSpace >>= (\<lambda>x. doMachineOp f >>= (\<lambda>y. m y x))"
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

lemma dmo'_createObjects'_commute:
  assumes ef: "empty_fail f"
  shows "monad_commute \<top> (doMachineOp f) (createObjects' ptr n obj us)"
  apply (clarsimp simp: createObjects'_def bind_assoc split_def unless_def
                        alignError_def monad_commute_def
                        dmo'_when_fail_comm[OF ef]
                        dmo'_gets_ksPSpace_comm
                        dmo'_ksPSpace_update_comm'[OF ef, symmetric])
  apply (rule_tac x=s in fun_cong)
  apply (rule arg_cong_bind1)
  apply (rule arg_cong_bind1)
  apply (rename_tac u w)
  apply (case_tac "fst (lookupAround2 (ptr + of_nat (shiftL n (objBitsKO obj +
                                         us) - Suc 0)) w)", clarsimp+)
  apply (simp add: assert_into_when dmo'_when_fail_comm[OF ef])
  done

lemmas map_dmo'_createObjects'_comm = dmo'_createObjects'_commute[THEN mapM_x_commute_T]

lemma dmo'_ksArchState_upd_comm:
  "monad_commute \<top> (doMachineOp m) (modify (\<lambda>s. ksArchState_update (f (ksArchState s)) s))"
  apply (clarsimp simp: monad_commute_def doMachineOp_def)
  apply monad_eq
  apply (auto simp add: select_f_def)
  done

lemmas map_dmo'_ksArchState_upd_comm = dmo'_ksArchState_upd_comm[THEN mapM_x_commute_T]

lemma dmo'_gsUserPages_upd_commute:
  "monad_commute \<top> (doMachineOp f) (modify (gsUserPages_update g))"
  apply (clarsimp simp: monad_commute_def doMachineOp_def bind_assoc)
  apply monad_eq
  apply (auto simp: select_f_def)
  done

lemmas dmo'_gsUserPages_upd_map_commute = dmo'_gsUserPages_upd_commute[THEN mapM_x_commute_T]

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
   apply (simp add: placeNewObject_def2[where val = "makeObject::tcb", simplified, symmetric])
   apply (rule placeNewObject_modify_commute)
  apply (clarsimp simp: gen_objBits_simps typ_at'_def obj_at'_def ko_wp_at'_def projectKO_opt_tcb)
  apply (clarsimp simp: obj_sizeBits_less_word_bits split: Structures_H.kernel_object.splits)
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
   apply (simp add:word_le_sub1 shiftl_t2n field_simps mask_def)
  apply auto
  done
qed

lemma new_cap_addrs_def2:
  "n < 2 ^ word_bits \<Longrightarrow> new_cap_addrs (Suc n) ptr obj = map (\<lambda>n. ptr + (n << objBitsKO obj)) [0.e.of_nat n]"
  unfolding new_cap_addrs_def
  (* avoid unfolding word_bits in proof to keep it generic *)
  by (simp add: upto_enum_word unat_of_nat[where 'a=machine_word_len, folded word_bits_def])

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
    (* avoid unfolding word_bits in proof below to keep it generic *)
    apply (drule range_cover.weak[where 'a=machine_word_len, folded word_bits_def])
    apply simp
   apply simp
  apply (clarsimp simp: retype_obj_at_disj')
  apply (clarsimp simp: new_cap_addrs_def image_def)
  apply (drule_tac x = "unat x" in bspec)
   apply (simp add: gen_objBits_simps shiftl_t2n)
   apply (rule unat_less_helper)
   apply (rule ccontr)
   apply simp
  apply (simp add: gen_objBits_simps shiftl_t2n)
  done

lemma curDomain_createObjects'_comm:
  "do x \<leftarrow> createObjects' ptr n obj us;
      y \<leftarrow> curDomain;
      m x y
   od =
   do y \<leftarrow> curDomain;
      x \<leftarrow> createObjects' ptr n obj us;
      m x y
   od"
  apply (rule ext)
  apply (case_tac x)
  by (auto simp: createObjects'_def split_def bind_assoc return_def unless_def
                 when_def simpler_gets_def alignError_def fail_def assert_def
                 bind_def curDomain_def modify_def get_def put_def
          split: option.splits)

lemma curDomain_twice_simp:
  "do x \<leftarrow> curDomain;
      y \<leftarrow> curDomain;
      m x y
   od =
   do x \<leftarrow> curDomain;
      m x x
   od"
  apply (rule ext)
  apply (case_tac x)
  by (auto simp: simpler_gets_def bind_def curDomain_def)

end (* Detype_R *)

locale Detype_R_2 = Detype_R +
  assumes createObject_def2:
    "\<And>ty ptr us dev.
     (RetypeDecls_H.createObject ty ptr us dev >>= (\<lambda>x. return [x])) =
     createNewCaps ty ptr (Suc 0) us dev"
  assumes createNewCaps_Cons:
    "\<And>ptr sz ty us n s d.
     \<lbrakk>range_cover ptr sz (getObjectSize ty us) (Suc (Suc n)); valid_pspace' s; valid_arch_state' s;
      pspace_no_overlap' ptr sz s; ptr \<noteq> 0\<rbrakk>
     \<Longrightarrow> createNewCaps ty ptr (Suc (Suc n)) us d s =
        (do x <- createNewCaps ty ptr (Suc n) us d;
            r <- global.createObject ty ((1 + of_nat n << getObjectSize ty us) + ptr) us d;
            return (x @ [r])
         od) s"
  assumes createNewCaps_pspace_no_overlap':
    "\<And>ptr sz ty us n d.
     \<lbrace>\<lambda>s. range_cover ptr sz (Types_H.getObjectSize ty us) (Suc (Suc n)) \<and>
          pspace_aligned' s \<and> pspace_distinct' s \<and> pspace_no_overlap' ptr sz s \<and>
          ptr \<noteq> 0\<rbrace>
     createNewCaps ty ptr (Suc n) us d
     \<lbrace>\<lambda>r s. pspace_no_overlap'
               (ptr + (1 + of_nat n << Types_H.getObjectSize ty us))
               (Types_H.getObjectSize ty us) s\<rbrace>"
  assumes createNewCaps_ret_len:
    "\<And>n ty ptr us d.
     \<lbrace>K (n < 2 ^ word_bits \<and> n \<noteq> 0)\<rbrace> createNewCaps ty ptr n us d \<lbrace>\<lambda>rv s. n = length rv\<rbrace>"
  assumes ArchCreateObject_pspace_no_overlap':
    "\<And>ptr n ty userSize sz d.
     \<lbrace>\<lambda>s. pspace_no_overlap'
            (ptr + (of_nat n << APIType_capBits ty userSize)) sz s \<and>
          pspace_aligned' s \<and> pspace_distinct' s \<and>
          range_cover ptr sz (APIType_capBits ty userSize) (n + 2) \<and> ptr \<noteq> 0\<rbrace>
     Arch.createObject ty
       (ptr + (of_nat n << APIType_capBits ty userSize)) userSize d
     \<lbrace>\<lambda>archCap. pspace_no_overlap'
                  (ptr + (1 + of_nat n << APIType_capBits ty userSize)) sz\<rbrace>"
begin

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
proof (clarsimp simp: insertNewCaps_def createNewObjects_def neq_Nil_conv
                simp del: objSize_eq_capBits)
  note objSize_eq_capBits[simp del]
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
       apply (clarsimp simp: power_add[symmetric] shiftl_t2n field_simps objSize_eq_capBits)
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
       apply (simp add: unat_minus_one_word_mw)
      apply (subst append_Cons[symmetric])
      apply (subst zipWithM_x_append1)
       apply (clarsimp simp: unat_of_nat_eq_mw bind_assoc)
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
      apply (auto simp: kscd dest: object_type_inject[THEN iffD1])
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
                   \<and> caps_overlap_reserved' {ptr..ptr + of_nat (length dslots) *
                                                          2^ (Types_H.getObjectSize ty us) - 1} s
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
  and  ptr_cn: "canonical_address (ptr && ~~ mask sz)"
  and  ptr_km: "ptr && ~~ mask sz \<in> kernel_mappings"
  and   sz_limit: "sz \<le> maxUntypedSizeBits"
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

lemma createObject_pspace_no_overlap':
  "\<lbrace>\<lambda>s. pspace_no_overlap'
          (ptr + (of_nat n << APIType_capBits ty userSize)) sz s \<and>
        pspace_aligned' s \<and> pspace_distinct' s
        \<and> range_cover ptr sz (APIType_capBits ty userSize) (n + 2)
        \<and> ptr \<noteq> 0\<rbrace>
   createObject ty (ptr + (of_nat n << APIType_capBits ty userSize)) userSize d
   \<lbrace>\<lambda>rv s. pspace_no_overlap'
             (ptr + (1 + of_nat n << APIType_capBits ty userSize)) sz s\<rbrace>"
  supply APIType_capBits_generic[simp del]
  apply (rule hoare_pre)
   apply (clarsimp simp:createObject_def)
   apply wpc
    apply (wp ArchCreateObject_pspace_no_overlap')
   apply wpc
         apply wp
        \<comment> \<open>TCB\<close>
        apply (wp createObjects'_pspace_no_overlap2[where n =0 and sz = sz,simplified]
               | simp add: curDomain_def placeNewObject_def2 word_shiftl_add_distrib field_simps)+
         apply (simp add:add.assoc[symmetric])
         apply (wp createObjects'_pspace_no_overlap2[where n =0 and sz = sz,simplified])
        apply (wpsimp simp: curDomain_def)
       \<comment> \<open>other objects\<close>
       apply ((wp createObjects'_pspace_no_overlap2
               | simp add: placeNewObject_def2 word_shiftl_add_distrib field_simps)+,
              simp add:add.assoc[symmetric],
              wp createObjects'_pspace_no_overlap2[where n =0 and sz = sz,simplified])+
   \<comment> \<open>Cleanup\<close>
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
  by (auto simp: word_shiftl_add_distrib field_simps shiftl_t2n elim: range_cover_le)
     (auto simp: gen_objBits_simps APIType_capBits_generic APIType_capBits_gen_def)

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
      thus ?case by (simp add: unat_of_nat_eq_mw)
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

end (* Detype_R_2 *)

crunch insertNewCap
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps)

end
