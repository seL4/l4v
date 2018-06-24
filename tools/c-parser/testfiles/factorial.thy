(*
 * Copyright 201machine_word_bytes, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory factorial
imports "CParser.CTranslation" "$L4V_ARCH/imports/MachineWords"
begin

declare hrs_simps [simp add]
declare sep_conj_ac [simp add]

consts free_pool :: "nat \<Rightarrow> heap_assert"

primrec
  fac :: "nat \<Rightarrow> machine_word"
where
  "fac 0 = 1"
| "fac (Suc n) = of_nat (Suc n) * fac n"

lemma fac_unfold:
  "unat n \<noteq> 0 \<Longrightarrow> fac (unat n) = n * fac (unat (n - 1))"
  apply(case_tac "unat n")
   apply simp
  apply(subst unat_minus_one)
   apply(simp only: unat_simps)
   apply(clarify)
   apply simp
  apply clarsimp
  apply(simp only: unat_simps)
  apply(subst mod_less)
   apply (fold len_of_addr_card)
   apply unat_arith
  apply (clarsimp simp: distrib_right split: unat_splits)
  done

primrec
  fac_list :: "nat \<Rightarrow> machine_word list"
where
  "fac_list 0 = [1]"
| "fac_list (Suc n) = fac (Suc n) # fac_list n"

lemma fac_list_length [simp]:
  "length (fac_list n) = n + 1"
  by (induct n) auto

lemma fac_list_unfold:
  "unat n \<noteq> 0 \<Longrightarrow> fac_list (unat n) = fac (unat n) # fac_list (unat (n - 1))"
  apply(case_tac "unat n")
   apply clarsimp
  apply(subst unat_minus_one)
   apply clarsimp+
  done

primrec
  sep_list :: "machine_word list \<Rightarrow> machine_word ptr \<Rightarrow> heap_assert"
where
  "sep_list [] p = (\<lambda>s. p=NULL \<and> \<box> s)"
| "sep_list (x#xs) p = (\<lambda>s. \<exists>j. ((p \<mapsto> x) \<and>\<^sup>* (p +\<^sub>p 1) \<mapsto> j \<and>\<^sup>*
      sep_list xs (Ptr j)) s)"

lemma sep_list_NULL [simp]:
  "sep_list xs NULL = (\<lambda>s. xs = [] \<and> \<box> s)"
  by (case_tac xs) auto

definition
  sep_fac_list :: "machine_word \<Rightarrow> machine_word ptr \<Rightarrow> heap_assert"
where
  "sep_fac_list n p \<equiv> sep_list (fac_list (unat n)) p"

lemma sep_fac_list_unfold:
  "((\<lambda>s. unat n \<noteq> 0 \<and> (\<exists>q. (p \<mapsto> fac (unat n) \<and>\<^sup>* (p +\<^sub>p 1) \<mapsto> q \<and>\<^sup>*
      sep_fac_list (n - 1) (Ptr q)) s)) \<and>\<^sup>* R) s \<Longrightarrow>
      (sep_fac_list n p \<and>\<^sup>* R) s"
  apply (erule sep_globalise)
  apply (simp add: sep_fac_list_def fac_list_unfold)
  done

lemma sep_fac_list_points:
  "sep_points (sep_fac_list n p) s \<Longrightarrow> (p \<hookrightarrow> fac (unat n)) s"
  apply(unfold sep_points_def)
  apply(subst sep_map'_unfold)
  apply(erule sep_conj_impl)
   apply(unfold sep_fac_list_def)
   apply(case_tac "unat n")
    apply simp
    apply(unfold sep_map'_old)
    apply(erule (1) sep_conj_impl)
    apply simp
   apply clarsimp
   apply(subst (asm) sep_conj_assoc [symmetric])+
   apply(erule sep_conj_impl)
    apply simp+
  done

external_file "factorial.c"
install_C_file memsafe "factorial.c"

thm factorial_global_addresses.factorial_body_def

lemma (in factorial_global_addresses) mem_safe_alloc:
  "mem_safe (\<acute>ret__ptr_to_unsigned_long :== PROC alloc()) \<Gamma>"
  apply(insert alloc_impl)
  apply(unfold alloc_body_def)
  apply(subst mem_safe_restrict)
  apply(rule intra_mem_safe)
   apply(simp_all add: restrict_map_def split: if_split_asm)
  apply(auto simp: whileAnno_def comp_def hrs_comm split_def mono_guard_def)
  done

lemma (in factorial_global_addresses) sep_frame_alloc:
  "\<lbrakk> \<forall>\<sigma>. \<Gamma> \<turnstile> \<lbrace>\<sigma>. (P (f \<acute>(\<lambda>x. x)))\<^bsup>sep\<^esup> \<rbrace> \<acute>ret__ptr_to_unsigned_long :== PROC alloc() \<lbrace> (Q (g \<sigma> \<acute>(\<lambda>x. x)))\<^bsup>sep\<^esup> \<rbrace>;
      htd_ind f; htd_ind g; \<forall>s. htd_ind (g s) \<rbrakk> \<Longrightarrow>
      \<forall>\<sigma>. \<Gamma> \<turnstile> \<lbrace>\<sigma>. (P (f \<acute>(\<lambda>x. x)) \<and>\<^sup>* R (h \<acute>(\<lambda>x. x)))\<^bsup>sep\<^esup> \<rbrace>
              \<acute>ret__ptr_to_unsigned_long :== PROC alloc()
              \<lbrace> (Q (g \<sigma> \<acute>(\<lambda>x. x)) \<and>\<^sup>* R (h \<sigma>))\<^bsup>sep\<^esup> \<rbrace>"
  unfolding sep_app_def
  by (rule sep_frame, auto intro!: mem_safe_alloc)

lemma (in alloc_spec) alloc_spec':
  shows "\<forall>\<sigma> k R f. factorial_global_addresses.\<Gamma> \<turnstile>
    \<lbrace>\<sigma>. ((\<lambda>x. free_pool k) ((\<lambda>x. undefined) \<acute>(\<lambda>x. x)) \<and>\<^sup>* R (f \<acute>(\<lambda>x. x)))\<^bsup>sep\<^esup> \<rbrace>
    \<acute>ret__ptr_to_unsigned_long :== PROC alloc()
    \<lbrace> ((\<lambda>p s. if k > 0 then (\<turnstile>\<^sub>s p \<and>\<^sup>* \<turnstile>\<^sub>s (p +\<^sub>p 1) \<and>\<^sup>*
        free_pool (k - 1)) s else (free_pool k) s \<and> p = NULL) \<acute>ret__ptr_to_unsigned_long
        \<and>\<^sup>* R (f \<sigma>))\<^bsup>sep\<^esup> \<rbrace>"
  apply clarify
  apply(insert alloc_spec)
  apply(rule_tac x=\<sigma> in spec)
  apply(rule sep_frame_alloc)
     apply(clarsimp simp: sep_app_def split: if_split_asm)
    apply simp+
  done

lemma (in factorial_global_addresses) mem_safe_free:
  "mem_safe (PROC free(\<acute>p)) \<Gamma>"
  apply(insert free_impl)
  apply(unfold free_body_def)
  apply(subst mem_safe_restrict)
  apply(auto simp: whileAnno_def)
  apply(rule intra_mem_safe)
   apply(auto simp: restrict_map_def split: if_split_asm)
  done

lemma (in factorial_global_addresses) sep_frame_free:
  "\<lbrakk> \<forall>\<sigma>. \<Gamma> \<turnstile> \<lbrace>\<sigma>. (P (f \<acute>(\<lambda>x. x)))\<^bsup>sep\<^esup> \<rbrace> PROC free(\<acute>p) \<lbrace> (Q (g \<sigma> \<acute>(\<lambda>x. x)))\<^bsup>sep\<^esup> \<rbrace>;
      htd_ind f; htd_ind g; \<forall>s. htd_ind (g s) \<rbrakk> \<Longrightarrow>
      \<forall>\<sigma>. \<Gamma> \<turnstile> \<lbrace>\<sigma>. (P (f \<acute>(\<lambda>x. x)) \<and>\<^sup>* R (h \<acute>(\<lambda>x. x)))\<^bsup>sep\<^esup> \<rbrace>
              PROC free(\<acute>p)
              \<lbrace> (Q (g \<sigma> \<acute>(\<lambda>x. x)) \<and>\<^sup>* R (h \<sigma>))\<^bsup>sep\<^esup> \<rbrace>"
  apply(simp only: sep_app_def)
  apply(rule sep_frame, auto intro!: mem_safe_free)
  done


lemma (in free_spec) free_spec':
  shows "\<forall>\<sigma> k R f. factorial_global_addresses.\<Gamma> \<turnstile>
    \<lbrace>\<sigma>. ((\<lambda>p. sep_cut' (ptr_val p) (2 * size_of TYPE(machine_word)) \<and>\<^sup>* free_pool k) \<acute>p  \<and>\<^sup>* R (f \<acute>(\<lambda>x. x)))\<^bsup>sep\<^esup> \<rbrace>
    PROC free(\<acute>p)
    \<lbrace> ((\<lambda>x. free_pool (k + 1)) ((\<lambda>x. ()) \<acute>(\<lambda>x. x)) \<and>\<^sup>* R (f \<sigma>))\<^bsup>sep\<^esup> \<rbrace>"
  apply clarify
  apply(insert free_spec)
  apply(rule_tac x=\<sigma> in spec)
  apply(rule sep_frame_free)
     apply(clarsimp simp: sep_app_def split: if_split_asm)
    apply simp+
  done

lemma double_word_sep_cut':
  "(p \<mapsto> x \<and>\<^sup>* (p +\<^sub>p 1) \<mapsto> y) s \<Longrightarrow> sep_cut' (ptr_val (p::machine_word ptr)) (2*machine_word_bytes) s"
apply(clarsimp simp: sep_conj_def sep_cut'_def dest!: sep_map_dom)
apply(subgoal_tac "{ptr_val p..+machine_word_bytes} \<subseteq> {ptr_val p..+(2*machine_word_bytes)}")
 apply(subgoal_tac "{ptr_val p+(of_nat machine_word_bytes)..+machine_word_bytes} \<subseteq> {ptr_val p..+(2*machine_word_bytes)}")
  apply rule
   apply (fastforce simp: ptr_add_def)
  apply clarsimp
  apply(drule intvlD)
  apply clarsimp
  apply(case_tac "k < machine_word_bytes")
   apply(erule intvlI)
  apply(erule notE)
  apply(clarsimp simp: intvl_def)
  apply(rule_tac x="k - machine_word_bytes" in exI)
  apply rule
   apply(simp only: unat_simps)
   apply(subst mod_less)
    apply(simp add: addr_card)
   apply (simp add: ptr_add_def addr_card)
  apply simp
 apply(clarsimp simp: intvl_def)
 apply(rule_tac x="machine_word_bytes+k" in exI)
 apply simp
apply(rule intvl_start_le)
apply simp
done


locale specs = factorial_global_addresses + alloc_spec + free_spec

lemma (in specs) factorial_spec:
  shows "factorial_spec"
  apply unfold_locales
  apply(hoare_rule HoarePartial.ProcRec1)
  apply (hoare_rule anno = "factorial_invs_body k" in HoarePartial.annotateI)
   prefer 2
   apply (simp add: whileAnno_def factorial_invs_body_def)
  apply(subst factorial_invs_body_def)
  apply(unfold sep_app_def)
  apply (vcg exspec=alloc_spec' exspec=free_spec')
    apply (fold lift_def)
    apply(clarsimp simp: sep_app_def)
    apply (rule conjI)
     apply clarsimp
     apply(rule_tac x=k in exI)
     apply(rule_tac x="\<lambda>p. \<box>" in exI)
     apply(rule_tac x="\<lambda>s. undefined" in exI)
     apply clarsimp
     apply (rule conjI)
      apply clarsimp
     apply clarsimp
     apply (rename_tac a b ret__ptr_to_unsigned_long)
     apply(subgoal_tac "(\<turnstile>\<^sub>s ret__ptr_to_unsigned_long \<and>\<^sup>* sep_true) (lift_state (a,b))")
      prefer 2
      apply(drule sep_conj_sep_true_right)
      apply simp
     apply(subgoal_tac "(\<turnstile>\<^sub>s (ret__ptr_to_unsigned_long +\<^sub>p 1) \<and>\<^sup>* sep_true) (lift_state (a,b))")
      prefer 2
      apply(drule sep_conj_sep_true_left)
      apply simp
      apply(subst (asm) sep_conj_assoc [symmetric])+
      apply(drule_tac Q="free_pool (k - Suc 0)" in sep_conj_sep_true_right)
      apply simp
     apply(simp add: tagd_ptr_safe tagd_g c_guard_ptr_aligned c_guard_NULL)
     apply(simp add: sep_fac_list_def)
     apply(sep_select_tac "(_ +\<^sub>p _) \<mapsto> _")
     apply(rule sep_heap_update_global')
     apply simp
     apply(rule sep_heap_update_global')
     apply simp
    apply clarsimp
    apply(rule_tac x=k in exI)
    apply clarsimp
    apply(rule_tac x="k - Suc (unat (n - 1))" in exI)
    apply clarsimp
    apply(rule_tac x="\<lambda>(n,p). sep_fac_list (n - 1) p" in exI)
    apply(rule_tac x="\<lambda>s. (n_' s,q_' s)" in exI)
    apply (rule conjI, clarsimp)
    apply clarsimp
    apply (rule conjI)
     apply clarsimp
     apply(simp add: sep_fac_list_def)
     apply(rule_tac x="fac_list (unat (n - 1))" in exI)
     apply clarsimp
    apply clarsimp
    apply(subgoal_tac "(\<turnstile>\<^sub>s ret__ptr_to_unsigned_long \<and>\<^sup>* sep_true) (lift_state (ab,bb))")
     prefer 2
     apply(erule (1) sep_conj_impl)
     apply simp
    apply(subgoal_tac "(\<turnstile>\<^sub>s (ret__ptr_to_unsigned_long +\<^sub>p 1) \<and>\<^sup>* sep_true) (lift_state (ab,bb))")
     prefer 2
     apply(subgoal_tac "(\<turnstile>\<^sub>s ret__ptr_to_unsigned_long \<and>\<^sup>*
                         \<turnstile>\<^sub>s (ret__ptr_to_unsigned_long +\<^sub>p 1) \<and>\<^sup>*
                         sep_fac_list (n - 1) ret__ptr_to_unsigned_longa \<and>\<^sup>*
                         free_pool (k - Suc (unat n))) =
                         (\<turnstile>\<^sub>s (ret__ptr_to_unsigned_long +\<^sub>p 1) \<and>\<^sup>* (\<turnstile>\<^sub>s ret__ptr_to_unsigned_long \<and>\<^sup>*
                         sep_fac_list (n - 1) ret__ptr_to_unsigned_longa \<and>\<^sup>*
                         free_pool (k - Suc (unat n))))")
      prefer 2
      apply simp
     apply (simp only:)
     apply(erule (1) sep_conj_impl)
     apply simp
    apply(sep_point_tac sep_fac_list_points)
    apply(simp add: tagd_ptr_safe tagd_g sep_map'_g c_guard_ptr_aligned c_guard_NULL sep_map'_lift)
    apply(rule sep_fac_list_unfold)
    apply clarsimp
    apply (rule conjI, unat_arith)
    apply sep_exists_tac
    apply(rule_tac x="ptr_val ret__ptr_to_unsigned_longa" in exI)
    apply clarsimp
    apply(subst fac_unfold)
     apply unat_arith
    apply clarsimp
    apply(sep_select_tac "(_ +\<^sub>p _) \<mapsto> _")
    apply(rule sep_heap_update_global')
    apply(sep_select_tac "_ \<mapsto> _")
      apply(rule sep_heap_update_global')
      apply(erule (1) sep_conj_impl)+
      apply clarsimp
   apply clarsimp
   apply(case_tac xs)
    apply simp
   apply clarsimp
   apply sep_exists_tac
   apply clarsimp
   apply sep_point_tac
   apply(simp add: sep_map'_g c_guard_ptr_aligned c_guard_NULL sep_map'_lift)
   apply(rule_tac x="k - Suc (length list)" in exI)
   apply(rule_tac x="\<lambda>p. sep_list list (Ptr j)" in exI)
   apply(rule_tac x="\<lambda>x. ()" in exI)
   apply(clarsimp simp: sep_app_def)
   apply (rule conjI)
    apply(subgoal_tac "(q \<mapsto> aa \<and>\<^sup>* sep_list list (Ptr j) \<and>\<^sup>*
                         (q +\<^sub>p 1) \<mapsto> j \<and>\<^sup>* free_pool (k - Suc (length list))) =
                       (sep_list list (Ptr j) \<and>\<^sup>* (q \<mapsto> aa \<and>\<^sup>*
                         (q +\<^sub>p 1) \<mapsto> j \<and>\<^sup>* free_pool (k - Suc (length list))))")
     apply(simp only:)
     apply(erule (1) sep_conj_impl)
     apply simp
     apply(subst sep_conj_com)
     apply(subst (asm) sep_conj_assoc [symmetric])+
     apply(erule sep_conj_impl)
      apply simp
      apply(erule double_word_sep_cut'[simplified])
     apply assumption
    apply simp
   apply clarsimp
   apply(subgoal_tac "Suc (k - Suc (length list)) = k - length list")
    apply force
   apply arith
  apply clarsimp
  done

declare hrs_simps [simp del]

lemma (in factorial_global_addresses) mem_safe_factorial:
  shows "mem_safe (\<acute>ret__ptr_to_unsigned_long :== PROC factorial(\<acute>n)) \<Gamma>"
  apply(subst mem_safe_restrict)
  apply(rule intra_mem_safe)
   apply (insert factorial_impl free_impl alloc_impl)
   apply(drule_tac t="Some C" in sym)
   apply(simp_all add: restrict_map_def call_def block_def whileAnno_def
                       free_body_def alloc_body_def factorial_body_def creturn_def
                split: if_split_asm option.splits)
  apply((erule disjE)?, simp,
        (thin_tac "C=x" for x, (thin_tac "\<Gamma> x = y" for x y)+,
        force simp: intra_sc)?)+
  done

end
