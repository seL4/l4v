(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchInvsLemmas_H
imports
  Invariants_H
begin

context Arch begin arch_global_naming

named_theorems Invariants_H_pspaceI_assms

(* FIXME arch-split: word_size is available outside of Arch due to Word_Setup, but to provide
   more guard rails during arch-split we are hiding the Haskell constant definition outside of
   Arch. To be evaluated as arch-split proceeds, since it can always be made generic again. *)
schematic_goal wordBits_def': "wordBits = numeral ?n" (* arch-specific consequence *)
  by (simp add: wordBits_def word_size)

lemmas wordRadix_def' = wordRadix_def[simplified]

lemma wordSizeCase_simp[simp]: "wordSizeCase a b = b"
  by (simp add: wordSizeCase_def wordBits_def word_size)

lemmas objBits_defs =
  tcbBlockSizeBits_def epSizeBits_def ntfnSizeBits_def cteSizeBits_def replySizeBits_def
lemmas untypedBits_defs = minUntypedSizeBits_def maxUntypedSizeBits_def
lemmas objBits_simps = objBits_def objBitsKO_def word_size_def archObjSize_def
lemmas objBits_simps' = objBits_simps objBits_defs

lemma frame_at'_pspaceI:
  "frame_at' p sz d s \<Longrightarrow> ksPSpace s = ksPSpace s' \<Longrightarrow> frame_at' p sz d s'"
  by (simp add: frame_at'_def typ_at'_def ko_wp_at'_def ps_clear_def)

lemma valid_cap'_pspaceI[Invariants_H_pspaceI_assms]:
  "s \<turnstile>' cap \<Longrightarrow> ksPSpace s = ksPSpace s' \<Longrightarrow> s' \<turnstile>' cap"
  unfolding valid_cap'_def
  by (cases cap)
     (auto intro: obj_at'_pspaceI[rotated]
                  cte_wp_at'_pspaceI valid_untyped'_pspaceI
                  typ_at'_pspaceI[rotated] sc_at'_n_pspaceI[rotated] frame_at'_pspaceI[rotated]
            simp: vspace_table_at'_defs valid_arch_cap'_def valid_arch_cap_ref'_def
           split: arch_capability.split zombie_type.split option.splits)

lemma valid_obj'_pspaceI[Invariants_H_pspaceI_assms]:
  "valid_obj' obj s \<Longrightarrow> ksPSpace s = ksPSpace s' \<Longrightarrow> valid_obj' obj s'"
  unfolding valid_obj'_def
  by (cases obj)
     (auto simp: valid_ep'_def valid_ntfn'_def valid_tcb'_def valid_cte'_def
                 valid_tcb_state'_def valid_bound_obj'_def valid_sched_context'_def valid_reply'_def
                 valid_arch_tcb'_def
           split: Structures_H.endpoint.splits Structures_H.notification.splits
                  Structures_H.thread_state.splits ntfn.splits option.splits
           intro: obj_at'_pspaceI valid_cap'_pspaceI typ_at'_pspaceI)

lemma tcb_space_clear[Invariants_H_pspaceI_assms]:
  "\<lbrakk> tcb_cte_cases (y - x) = Some (getF, setF);
     is_aligned x tcbBlockSizeBits; ps_clear x tcbBlockSizeBits s;
     ksPSpace s x = Some (KOTCB tcb); ksPSpace s y = Some v;
     \<lbrakk> x = y; getF = tcbCTable; setF = tcbCTable_update \<rbrakk> \<Longrightarrow> P
    \<rbrakk> \<Longrightarrow> P"
  apply (cases "x = y")
   apply simp
  apply (clarsimp simp: ps_clear_def mask_def add_diff_eq)
  apply (drule_tac a=y in equals0D)
  apply (simp add: domI)
  apply (subgoal_tac "\<exists>z. y = x + z \<and> z < 2 ^ tcbBlockSizeBits")
   apply (elim exE conjE)
   apply (frule(1) is_aligned_no_wrap'[rotated, rotated])
   apply (simp add: word_bits_conv objBits_defs)
   apply (erule notE, subst field_simps, rule word_plus_mono_right)
    apply (drule word_le_minus_one_leq,simp,erule is_aligned_no_wrap')
   apply (simp add: word_bits_conv)
  apply (simp add: objBits_defs)
  apply (rule_tac x="y - x" in exI)
  apply (simp add: tcb_cte_cases_def cteSizeBits_def split: if_split_asm)
  done

lemma pspace_in_kernel_mappings'_pspaceI[Invariants_H_pspaceI_assms]:
  "pspace_in_kernel_mappings' s \<Longrightarrow> ksPSpace s = ksPSpace s' \<Longrightarrow> pspace_in_kernel_mappings' s'"
  unfolding pspace_in_kernel_mappings'_def
  by simp

lemma range_cover_canonical_address[Invariants_H_pspaceI_assms]:
  "\<lbrakk> range_cover ptr sz us n ; p < n ;
     canonical_address (ptr && ~~ mask sz) ; sz \<le> maxUntypedSizeBits \<rbrakk>
   \<Longrightarrow> canonical_address (ptr + of_nat p * 2 ^ us)"
  apply (subst word_plus_and_or_coroll2[symmetric, where w = "mask sz"])
  apply (subst add.commute)
  apply (subst add.assoc)
  apply (rule canonical_address_add[where n=sz] ; simp add: untypedBits_defs is_aligned_neg_mask)
   apply (drule (1) range_cover.range_cover_compare)
   apply (clarsimp simp: word_less_nat_alt)
   apply unat_arith
  apply (simp add: canonical_bit_def)
  done

(* not interesting on this architecture *)
lemmas [simp] = pspace_in_kernel_mappings'_pspaceI

end

global_interpretation Invariants_H_pspaceI?: Invariants_H_pspaceI
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales; (fact Invariants_H_pspaceI_assms)?)?)
  qed

context Arch begin arch_global_naming

named_theorems Invariants_H_cte_ats_assms

(* FIXME arch-split: for proofs which require exact offsets lining up instead of cteSizeBits *)
lemma raw_tcb_cte_cases_simps:
  "tcb_cte_cases 32 = Some (tcbVTable, tcbVTable_update)"
  "tcb_cte_cases 64 = Some (tcbIPCBufferFrame, tcbIPCBufferFrame_update)"
  "tcb_cte_cases 96 = Some (tcbFaultHandler, tcbFaultHandler_update)"
  "tcb_cte_cases 128 = Some (tcbTimeoutHandler, tcbTimeoutHandler_update)"
  by (simp add: tcb_cte_cases_def cteSizeBits_def)+

lemma cte_wp_at_cases'[Invariants_H_cte_ats_assms]:
  shows "cte_wp_at' P p s =
  ((\<exists>cte. ksPSpace s p = Some (KOCTE cte) \<and> is_aligned p cte_level_bits
             \<and> P cte \<and> ps_clear p cteSizeBits s) \<or>
   (\<exists>n tcb getF setF. ksPSpace s (p - n) = Some (KOTCB tcb) \<and> is_aligned (p - n) tcbBlockSizeBits
             \<and> tcb_cte_cases n = Some (getF, setF) \<and> P (getF tcb) \<and> ps_clear (p - n) tcbBlockSizeBits s))"
  (is "?LHS = ?RHS")
  supply raw_tcb_cte_cases_simps[simp]
  apply (rule iffI)
   apply (clarsimp simp: cte_wp_at'_def gets_the_def readObject_def
                         getObject_def bind_def simpler_gets_def omonad_defs
                         assert_opt_def return_def fail_def
                  split: option.splits dest!: prod_injects
                    del: disjCI)
   apply (clarsimp simp: loadObject_cte read_typeError_def split_def
                         fail_def return_def objBits_simps'
                         is_aligned_mask[symmetric]
                         tcbVTableSlot_def field_simps tcbCTableSlot_def
                         tcbIPCBufferSlot_def
                         tcbFaultHandlerSlot_def tcbTimeoutHandlerSlot_def
                         lookupAround2_char1 omonad_defs
                         cte_level_bits_def Ball_def
                         unless_def when_def bind_def alignError_def alignCheck_def
                  split: kernel_object.splits if_split_asm option.splits
                    del: disjCI)
       apply (rule disjI2)
       apply (fastforce simp: field_simps elim: rsubst[where P="\<lambda>x. ksPSpace s x = v" for s v])+
  apply (simp add: cte_wp_at'_def getObject_def split_def
                   bind_def simpler_gets_def return_def
                   assert_opt_def fail_def objBits_defs
                   readObject_def omonad_defs obind_def gets_the_def
            split: option.splits)
  apply (elim disjE conjE exE)
   apply (erule(1) ps_clear_lookupAround2)
     apply simp
    apply (simp add: field_simps)
    apply (erule is_aligned_no_wrap')
     apply (simp add: cte_level_bits_def word_bits_conv)
    apply (simp add: cte_level_bits_def)
   apply (simp add: loadObject_cte unless_def alignCheck_def
                    is_aligned_mask[symmetric] objBits_simps'
                    cte_level_bits_def magnitudeCheck_def
                    return_def fail_def obind_def
                    read_magnitudeCheck_def read_alignCheck_def
                    omonad_defs)
   apply (clarsimp simp: bind_def return_def when_def fail_def
                  split: option.splits)
   apply simp
  apply (erule(1) ps_clear_lookupAround2)
    prefer 3
    apply (simp add: loadObject_cte unless_def alignCheck_def
                     is_aligned_mask[symmetric] objBits_simps'
                     cte_level_bits_def magnitudeCheck_def
                     return_def fail_def tcbCTableSlot_def tcbVTableSlot_def
                     tcbIPCBufferSlot_def tcbFaultHandlerSlot_def tcbTimeoutHandlerSlot_def
                     omonad_defs obind_def read_magnitudeCheck_def read_alignCheck_def
              split: option.split_asm)
     apply (clarsimp simp: bind_def tcb_cte_cases_def cteSizeBits_def split: if_split_asm)
    apply (clarsimp simp: bind_def tcb_cte_cases_def iffD2[OF linorder_not_less]
                          return_def cteSizeBits_def
                   split: if_split_asm)
   apply (subgoal_tac "p - n \<le> (p - n) + n", simp)
   apply (erule is_aligned_no_wrap')
    apply (simp add: word_bits_conv)
   apply (simp add: tcb_cte_cases_def cteSizeBits_def split: if_split_asm)
  apply (subgoal_tac "(p - n) + n \<le> (p - n) + 0x3FF")
   apply (simp add: field_simps)
  apply (rule word_plus_mono_right)
   apply (simp add: tcb_cte_cases_def cteSizeBits_def split: if_split_asm)
  apply (erule is_aligned_no_wrap')
  apply simp
  done

lemma cte_wp_atE'[consumes 1, case_names CTE TCB]:
  assumes cte: "cte_wp_at' P ptr s"
  and   r1: "\<And>cte.
    \<lbrakk> ksPSpace s ptr = Some (KOCTE cte); ps_clear ptr cte_level_bits s;
      is_aligned ptr cte_level_bits; P cte \<rbrakk> \<Longrightarrow> R"
  and   r2: "\<And> tcb ptr' getF setF.
  \<lbrakk> ksPSpace s ptr' = Some (KOTCB tcb); ps_clear ptr' tcbBlockSizeBits s; is_aligned ptr' tcbBlockSizeBits;
     tcb_cte_cases (ptr - ptr') = Some (getF, setF); P (getF tcb) \<rbrakk> \<Longrightarrow> R"
  shows "R"
  by (rule disjE [OF iffD1 [OF cte_wp_at_cases' cte]]) (auto intro: r1 r2 simp: cte_level_bits_def objBits_defs)

lemma cte_wp_at_cteI':
  assumes "ksPSpace s ptr = Some (KOCTE cte)"
  assumes "is_aligned ptr cte_level_bits"
  assumes "ps_clear ptr cte_level_bits s"
  assumes "P cte"
  shows "cte_wp_at' P ptr s"
  using assms by (simp add: cte_wp_at_cases' cte_level_bits_def objBits_defs)

lemma cte_at_typ'[Invariants_H_cte_ats_assms]:
  "cte_at' c = (\<lambda>s. typ_at' CTET c s \<or> (\<exists>n. typ_at' TCBT (c - n) s \<and> n \<in> dom tcb_cte_cases))"
proof -
  have P: "\<And>ko. (koTypeOf ko = CTET) = (\<exists>cte. ko = KOCTE cte)"
          "\<And>ko. (koTypeOf ko = TCBT) = (\<exists>tcb. ko = KOTCB tcb)"
    by (case_tac ko, simp_all)+
  have Q: "\<And>P f. (\<exists>x. (\<exists>y. x = f y) \<and> P x) = (\<exists>y. P (f y))"
    by fastforce
  show ?thesis
    by (fastforce simp: cte_wp_at_cases' obj_at'_real_def typ_at'_def word_bits_def
                        ko_wp_at'_def objBits_simps' P Q conj_comms cte_level_bits_def)
qed

(* interface lemma *)
lemma tcb_at_cte_at':
  "tcb_at' t s \<Longrightarrow> cte_at' t s"
  apply (clarsimp simp add: cte_wp_at_cases' obj_at'_def projectKO_def oassert_opt_def
                       del: disjCI)
  apply (case_tac ko)
   apply (simp_all add: projectKO_opt_tcb fail_def)
  apply (rule exI[where x=0])
  apply (clarsimp simp add: return_def objBits_simps)
  done

end

global_interpretation Invariants_H_cte_ats?: Invariants_H_cte_ats
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales; fact Invariants_H_cte_ats_assms)?)
  qed


(* arch-specific consequences of kernel_state field update identities *)

context Arch_pspace_update_eq'
begin

lemma page_table_at_update' [iff]:
  "page_table_at' p (f s) = page_table_at' p s"
  by (simp add: page_table_at'_def)

lemma frame_at_update' [iff]:
  "frame_at' p sz d (f s) = frame_at' p sz d s"
  by (simp add: frame_at'_def)

lemma pspace_in_kernel_mappings_update' [iff]:
  "pspace_in_kernel_mappings' (f s) = pspace_in_kernel_mappings' s"
  by (simp add: pspace pspace_in_kernel_mappings'_def)

lemma valid_global_pts_update' [iff]:
  "valid_global_pts' pts (f s) = valid_global_pts' pts s"
  by (simp add: valid_global_pts'_def)

end

context Arch_p_arch_idle_update_eq'
begin

lemma valid_arch_state_update'[iff]:
  "valid_arch_state' (f s) = valid_arch_state' s"
  by (simp add: valid_arch_state'_def arch cong: option.case_cong)

end

context Arch begin arch_global_naming

lemma mask_wordRadix_less_wordBits:
  assumes sz: "wordRadix \<le> size w"
  shows "unat ((w::'a::len word) && mask wordRadix) < wordBits"
  using word_unat_mask_lt[where m=wordRadix and w=w] assms
  by (simp add: wordRadix_def wordBits_def')

lemma priority_mask_wordRadix_size:
  "unat ((w::priority) && mask wordRadix) < wordBits"
  by (rule mask_wordRadix_less_wordBits, simp add: wordRadix_def word_size)

lemma canonical_address_neq_mask:
  "\<lbrakk> canonical_address ptr ; sz \<le> maxUntypedSizeBits \<rbrakk>
   \<Longrightarrow> canonical_address (ptr && ~~ mask sz)"
  by (simp add: canonical_address_sign_extended untypedBits_defs sign_extended_neq_mask
                canonical_bit_def)

lemma in_kernel_mappings_add:
  assumes "is_aligned p n"
  assumes "f < 2 ^ n"
  assumes "p \<in> kernel_mappings"
  shows "p + f \<in> kernel_mappings"
  using assms
  unfolding kernel_mappings_def pptr_base_def
  using is_aligned_no_wrap' word_le_plus_either by blast

lemma range_cover_in_kernel_mappings:
  "\<lbrakk> range_cover ptr sz us n ; p < n ;
     (ptr && ~~ mask sz) \<in> kernel_mappings ; sz \<le> maxUntypedSizeBits \<rbrakk>
   \<Longrightarrow> (ptr + of_nat p * 2 ^ us) \<in> kernel_mappings"
  apply (subst word_plus_and_or_coroll2[symmetric, where w = "mask sz"])
  apply (subst add.commute)
  apply (subst add.assoc)
  apply (rule in_kernel_mappings_add[where n=sz] ; simp add: untypedBits_defs is_aligned_neg_mask)
  apply (drule (1) range_cover.range_cover_compare)
  apply (clarsimp simp: word_less_nat_alt)
  apply unat_arith
  done

lemma in_kernel_mappings_neq_mask:
  "\<lbrakk> (ptr :: machine_word) \<in> kernel_mappings ; sz \<le> 38 \<rbrakk>
   \<Longrightarrow> ptr && ~~ mask sz \<in> kernel_mappings"
  apply (clarsimp simp: kernel_mappings_def untypedBits_defs pptr_base_def pptrBase_def
                        canonical_bit_def)
  by (word_bitwise, clarsimp simp: neg_mask_test_bit word_size)

lemma invs_pspace_in_kernel_mappings'[elim!]:
  "invs' s \<Longrightarrow> pspace_in_kernel_mappings' s"
  by (fastforce dest!: invs_valid_pspace' simp: valid_pspace'_def)

lemma tcb_hyp_refs_of'_simps[simp]:
  "tcb_hyp_refs' atcb = {}"
  by (auto simp: tcb_hyp_refs'_def)

lemma refs_of_a'_simps[simp]:
  "refs_of_a' ako = {}"
  by (auto simp: refs_of_a'_def)

lemma hyp_refs_of_hyp_live':
  "hyp_refs_of' ko \<noteq> {} \<Longrightarrow> hyp_live' ko"
  by (cases ko, simp_all)

lemma hyp_refs_of_live':
  "hyp_refs_of' ko \<noteq> {} \<Longrightarrow> live' ko"
  by (cases ko, simp_all add: live'_def hyp_refs_of_hyp_live')

(* FIXME arch-split RT: whole typ_at_lift section needs to be split *)
lemma typ_at_lift_page_table_at'_strong:
  "(\<And>p. f \<lbrace>\<lambda>s. P (typ_at' (ArchT PTET) p s)\<rbrace>) \<Longrightarrow> f \<lbrace>\<lambda>s. P (page_table_at' p s)\<rbrace>"
  unfolding page_table_at'_def
  apply (rule bool_to_bool_cases[where f=P]; clarsimp)
  apply (wpsimp wp: hoare_vcg_const_Ball_lift hoare_vcg_bex_lift hoare_vcg_imp_lift
                    hoare_vcg_all_lift hoare_vcg_ex_lift
         | assumption)+
  done

lemma typ_at_lift_frame_at'_strong:
  "\<lbrakk>\<And>T p. f \<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace>\<rbrakk> \<Longrightarrow> f \<lbrace>\<lambda>s. P (frame_at' p sz d s)\<rbrace>"
  supply if_split[split del]
  unfolding frame_at'_def
  apply (rule bool_to_bool_cases[where f=P]; clarsimp)
   apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_const_imp_lift  hoare_vcg_ex_lift
          | assumption)+
  done

lemma valid_arch_tcb_lift'_strong:
  assumes "\<And>T p. f \<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace>"
  shows "f \<lbrace>\<lambda>s. P (valid_arch_tcb' tcb s)\<rbrace>"
  by (clarsimp simp: valid_arch_tcb'_def, wp)

(* FIXME arch-split RT: I think this is true for all architectures, if it isn't then
                        typ_at'_valid_obj'_lift will need to be moved later, out of typ_at_lifts. *)
lemma valid_arch_obj_lift'_strong:
  assumes "\<And>T p. f \<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace>"
  shows "f \<lbrace>\<lambda>s. P (valid_arch_obj' ako s)\<rbrace>"
  by (clarsimp simp: valid_arch_obj'_def, wp)

lemmas typ_at_lifts_strong =
  typ_at_lift_tcb'_strong typ_at_lift_ep'_strong
  typ_at_lift_ntfn'_strong typ_at_lift_cte'_strong
  typ_at_lift_reply'_strong typ_at_lift_sc'_strong
  typ_at_lift_valid_tcb_state'_strong
  typ_at_lift_page_table_at'_strong
  typ_at_lift_frame_at'_strong
  valid_arch_tcb_lift'_strong
  valid_arch_obj_lift'_strong

lemma typ_at_lift_valid_irq_node':
  assumes P: "\<And>P T p. \<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at' T p s)\<rbrace>"
  shows      "\<lbrace>valid_irq_node' p\<rbrace> f \<lbrace>\<lambda>_. valid_irq_node' p\<rbrace>"
  apply (simp add: valid_irq_node'_def)
  apply (wp hoare_vcg_all_lift P typ_at_lifts_strong)
  done

context begin
\<comment>\<open> We're using @{command ML_goal} here because there are two useful formulations
    of typ_at lifting lemmas and we do not want to write all of the possibilities
    out by hand. If we use typ_at_lift_tcb' as an example, then the first is
    @{term "\<lbrace>\<lambda>s. P (typ_at' TCBT p s)\<rbrace> f \<lbrace>\<lambda>_ s. P (typ_at' TCBT p s)\<rbrace>
            \<Longrightarrow> \<lbrace>\<lambda>s. P (tcb_at' p s)\<rbrace> f \<lbrace>\<lambda>_ s. P (tcb_at' p s)\<rbrace>"} and the second is
    @{term "(\<And>P. \<lbrace>\<lambda>s. P (typ_at' TCBT p s)\<rbrace> f \<lbrace>\<lambda>_ s. P (typ_at' TCBT p s)\<rbrace>)
            \<Longrightarrow> \<lbrace>\<lambda>s. P (tcb_at' p s)\<rbrace> f \<lbrace>\<lambda>_ s. P (tcb_at' p s)\<rbrace>"}.
    The first form is stronger, and therefore preferred for backward reasoning
    using rule. However, since the P in the premise is free in the first form,
    forward unification using the OF attribute produces flex-flex pairs which
    causes problems. The second form avoids the unification issue by demanding
    that there is a P that is free in the lemma supplied to the OF attribute.
    However, it can only be applied if @{term f} preserves both
    @{term "typ_at' TCBT p s"} and @{term "\<not> typ_at' TCBT p s"}.
    The following @{command ML_goal} generates lemmas of the second form based on
    the previously proven stronger lemmas of the first form. \<close>
ML \<open>
local
  val strong_thms = @{thms typ_at_lifts_strong[no_vars]};
  fun abstract_P term = Logic.all (Free ("P", @{typ "bool \<Rightarrow> bool"})) term
  fun abstract thm =
    let
      val prems = List.map abstract_P (Thm.prems_of thm);
      fun imp [] = Thm.concl_of thm
        | imp (p :: pms) = @{const Pure.imp} $ p $ imp pms
    in
      imp prems
    end
in
  val typ_at_lifts_internal_goals = List.map abstract strong_thms
end
\<close>

private ML_goal typ_at_lifts_internal:
  \<open>typ_at_lifts_internal_goals\<close>
  by (auto simp: typ_at_lifts_strong)

lemmas typ_at_lifts = typ_at_lifts_internal
                      typ_at_lift_cte_at'
                      valid_bound_tcb_lift
                      valid_bound_reply_lift
                      valid_bound_sc_lift
                      valid_bound_ntfn_lift
                      valid_ntfn_lift'
                      valid_sc_lift'
end

lemma typ_at_lift_valid_cap':
  assumes P: "\<And>P T p. \<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at' T p s)\<rbrace>"
  assumes sz: "\<And>p n. \<lbrace>\<lambda>s. sc_at'_n n p s\<rbrace> f \<lbrace>\<lambda>rv s. sc_at'_n n p s\<rbrace>"
  shows      "\<lbrace>\<lambda>s. valid_cap' cap s\<rbrace> f \<lbrace>\<lambda>rv s. valid_cap' cap s\<rbrace>"
  including no_pre
  apply (simp add: valid_cap'_def)
  apply wp
  apply (case_tac cap;
         wpsimp wp: valid_cap'_def P typ_at_lifts_strong
                    hoare_vcg_prop  typ_at_lift_cte_at'
                    hoare_vcg_conj_lift [OF typ_at_lift_cte_at']
                    hoare_vcg_conj_lift)
     apply (rename_tac zombie_type nat)
     apply (case_tac zombie_type; simp)
      apply (wp typ_at_lifts_strong[where P=id, simplified] P
                hoare_vcg_all_lift)+
    apply (rename_tac arch_capability)
    apply (case_tac arch_capability,
           simp_all add: P [where P=id, simplified] page_table_at'_def
                         hoare_vcg_prop All_less_Ball
              split del: if_split)
       apply (wp hoare_vcg_const_Ball_lift P typ_at_lift_valid_untyped' sz
                 hoare_vcg_all_lift typ_at_lifts_strong)+
  done

lemma typ_at'_valid_obj'_lift:
  assumes P: "\<And>P T p. \<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at' T p s)\<rbrace>"
  assumes sz: "\<And>n p. \<lbrace>\<lambda>s. sc_at'_n n p s\<rbrace> f \<lbrace>\<lambda>rv s. sc_at'_n n p s\<rbrace>"
  notes [wp] = hoare_vcg_all_lift hoare_vcg_imp_lift' hoare_vcg_const_Ball_lift
               typ_at_lifts[OF P] typ_at_lift_valid_cap'[OF P]
  shows      "\<lbrace>\<lambda>s. valid_obj' obj s\<rbrace> f \<lbrace>\<lambda>rv s. valid_obj' obj s\<rbrace>"
  supply raw_tcb_cte_cases_simps[simp] (* FIXME arch-split: legacy, try use tcb_cte_cases_neqs *)
  apply (cases obj; simp add: valid_obj'_def hoare_TrueI)
        apply (rename_tac endpoint)
        apply (case_tac endpoint; simp add: valid_ep'_def, wp)
       apply (rename_tac notification)
       apply (case_tac "ntfnObj notification";
               simp add: valid_ntfn'_def split: option.splits;
               (wpsimp|rule conjI)+)
      apply (rename_tac tcb)
      apply (case_tac "tcbState tcb";
             simp add: valid_tcb'_def valid_tcb_state'_def split_def opt_tcb_at'_def;
             wpsimp wp: sz hoare_case_option_wp)
     apply (wpsimp simp: valid_cte'_def sz)
    apply (rename_tac arch_kernel_object)
    apply (case_tac arch_kernel_object; wpsimp wp: sz)
   apply wpsimp
  apply (wpsimp simp: valid_reply'_def)
  done

lemma typ_at'_valid_sched_context'_lift:
  assumes P: "\<And>P T p. \<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at' T p s)\<rbrace>"
  assumes sz: "\<And>n p. \<lbrace>\<lambda>s. sc_at'_n n p s\<rbrace> f \<lbrace>\<lambda>rv s. sc_at'_n n p s\<rbrace>"
  notes [wp] = hoare_vcg_all_lift hoare_vcg_imp_lift' hoare_vcg_const_Ball_lift
               typ_at_lifts[OF P] typ_at_lift_valid_cap'[OF P]
  shows      "\<lbrace>\<lambda>s. valid_sched_context' ko s\<rbrace> f \<lbrace>\<lambda>rv s. valid_sched_context' ko s\<rbrace>"
  by (wpsimp simp: valid_sched_context'_def)

lemmas typ_at_sc_at'_n_lifts =
  typ_at_lift_valid_untyped' typ_at_lift_valid_cap' typ_at'_valid_obj'_lift
  typ_at'_valid_obj'_lift[where obj="KOEndpoint ko" for ko, simplified valid_obj'_def kernel_object.case]
  typ_at'_valid_obj'_lift[where obj="KONotification ko" for ko, simplified valid_obj'_def kernel_object.case]
  typ_at'_valid_obj'_lift[where obj="KOTCB ko" for ko, simplified valid_obj'_def kernel_object.case]
  typ_at'_valid_obj'_lift[where obj="KOCTE ko" for ko, simplified valid_obj'_def kernel_object.case]
  typ_at'_valid_obj'_lift[where obj="KOArch ko" for ko, simplified valid_obj'_def kernel_object.case]
  typ_at'_valid_obj'_lift[where obj="KOReply ko" for ko, simplified valid_obj'_def kernel_object.case]
  typ_at'_valid_sched_context'_lift

lemmas typ_at_lifts_all = typ_at_lifts typ_at_sc_at'_n_lifts

end

locale typ_at_props' =
  fixes f :: "'a kernel"
  assumes typ': "f \<lbrace>\<lambda>s. P (typ_at' T p' s)\<rbrace>"
begin

interpretation Arch . (* FIXME arch-split RT *)

lemmas typ_at_lifts'[wp] = typ_at_lifts[REPEAT [OF typ']]

end

locale typ_at_all_props' = typ_at_props' +
  assumes scs: "f \<lbrace>\<lambda>s. Q (sc_at'_n n p s)\<rbrace>"
begin

interpretation Arch . (* FIXME arch-split RT *)

lemmas typ_at_sc_at'_n_lifts'[wp] = typ_at_sc_at'_n_lifts[OF typ' scs]
lemmas typ_at_lifts_all' = typ_at_lifts' typ_at_sc_at'_n_lifts'

context begin
(* We want to enforce that typ_at_lifts_all' only contains lemmas that have no
   assumptions. The following thm statements should fail if this is not true. *)
private lemmas check_valid_internal = iffD1[OF refl, where P="valid p g q" for p g q]
thm typ_at_lifts_all'[atomized, THEN check_valid_internal]
end

end

(* we expect typ_at' and sc_at'_n lemmas to be [wp], so this should be easy: *)
method typ_at_props' = unfold_locales; wp?


context Arch begin arch_global_naming

lemma page_table_pte_atI':
  "page_table_at' p s \<Longrightarrow> pte_at' (p + (ucast (x::pt_index) << pte_bits)) s"
  by (simp add: page_table_at'_def)

lemmas bit_simps' = pteBits_def asidHighBits_def asidPoolBits_def asid_low_bits_def
                    asid_high_bits_def minSchedContextBits_def
                    replySizeBits_def ptBits_def bit_simps

lemma objBitsT_simps:
  "objBitsT EndpointT = epSizeBits"
  "objBitsT NotificationT = ntfnSizeBits"
  "objBitsT CTET = cteSizeBits"
  "objBitsT TCBT = tcbBlockSizeBits"
  "objBitsT ReplyT = replySizeBits"
  "objBitsT UserDataT = pageBits"
  "objBitsT UserDataDeviceT = pageBits"
  "objBitsT KernelDataT = pageBits"
  "objBitsT (ArchT PTET) = word_size_bits"
  "objBitsT (ArchT ASIDPoolT) = pageBits"
  unfolding objBitsT_def makeObjectT_def archMakeObjectT_def
  by (simp add: makeObject_simps objBits_simps bit_simps')+

(* interface lemma - exports only generic equations from objBitsT_simps *)
lemmas gen_objBitsT_simps = objBitsT_simps(1-7)

end

end
