(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory swap
imports "CParser.CTranslation"
begin

declare hrs_simps [simp add]
declare sep_conj_ac [simp add]

external_file "swap.c"
install_C_file memsafe "swap.c"

thm swap_spec_def

lemma (in swap_global_addresses) swap_spec':
  shows "swap_spec"
apply unfold_locales
apply (hoare_rule HoarePartial.ProcNoRec1)
apply(unfold sep_app_def)
apply vcg
apply(fold lift_def)
apply(sep_point_tac)
apply(simp add: sep_map'_ptr_safe sep_map'_ptr_aligned sep_map'_NULL sep_map'_lift sep_map'_g)
apply(rule sep_heap_update_global)
apply(sep_select_tac "p \<mapsto> _")
apply(rule sep_heap_update_global)
apply simp
apply(erule sep_conj_impl)
 apply simp+
done

declare hrs_simps [simp del]

lemma (in swap_global_addresses) mem_safe_swap:
  "mem_safe (PROC swap(\<acute>p,\<acute>q)) \<Gamma>"
apply(insert swap_impl)
apply(unfold swap_body_def)
apply(subst mem_safe_restrict)
apply(rule intra_mem_safe)
 apply(simp_all add: restrict_map_def split: if_split_asm)
apply(auto simp: whileAnno_def intra_sc)
done

declare hrs_simps [simp add]


lemma (in swap_global_addresses) sep_frame_swap:
  "\<lbrakk> \<forall>\<sigma>. \<Gamma> \<turnstile> \<lbrace>\<sigma>. (P (f \<acute>(\<lambda>x. x)))\<^bsup>sep\<^esup> \<rbrace> PROC swap(\<acute>p,\<acute>q) \<lbrace> (Q (g \<sigma> \<acute>(\<lambda>x. x)))\<^bsup>sep\<^esup> \<rbrace>;
      htd_ind f; htd_ind g; \<forall>s. htd_ind (g s) \<rbrakk> \<Longrightarrow>
      \<forall>\<sigma>. \<Gamma> \<turnstile> \<lbrace>\<sigma>. (P (f \<acute>(\<lambda>x. x)) \<and>\<^sup>* R (h \<acute>(\<lambda>x. x)))\<^bsup>sep\<^esup> \<rbrace>
          PROC swap(\<acute>p,\<acute>q)
          \<lbrace> (Q (g \<sigma> \<acute>(\<lambda>x. x)) \<and>\<^sup>* R (h \<sigma>))\<^bsup>sep\<^esup> \<rbrace>"
apply(simp only: sep_app_def)
apply(rule sep_frame)
    apply(auto intro!: mem_safe_swap)
done

lemma expand_swap_pre:
  "(p_' s \<mapsto> x \<and>\<^sup>* q_' s \<mapsto> y) =
    (\<lambda>(v,w). v \<mapsto> x \<and>\<^sup>* w \<mapsto> y) (p_' s,q_' s)"
  by simp

lemma expand_swap_post:
  "(p_' s \<mapsto> x \<and>\<^sup>* q_' s \<mapsto> y) =
    (\<lambda>(v,w) s. v \<mapsto> x \<and>\<^sup>* w \<mapsto> y) (p_' s,q_' s) (\<lambda>s. s)"
  by simp

lemma (in swap_global_addresses) swap_spec:
  "\<forall>\<sigma> s x y R f. \<Gamma> \<turnstile>
    \<lbrace>\<sigma>. (\<acute>p \<mapsto> x \<and>\<^sup>* \<acute>q \<mapsto> y \<and>\<^sup>* R (f \<acute>(\<lambda>x. x)))\<^bsup>sep\<^esup> \<rbrace>
    PROC swap(\<acute>p,\<acute>q)
    \<lbrace>(\<^bsup>\<sigma>\<^esup>p \<mapsto> y \<and>\<^sup>* \<^bsup>\<sigma>\<^esup>q \<mapsto> x \<and>\<^sup>* R (f \<sigma>))\<^bsup>sep\<^esup> \<rbrace>"
apply clarify
apply(subst sep_conj_assoc [symmetric])+
apply(subst expand_swap_pre)
apply(subst expand_swap_post)
apply(insert swap_spec')
apply(unfold swap_spec_def)
apply(rule_tac x=\<sigma> in spec)
apply(rule sep_frame_swap)
   apply(unfold sep_app_def)
   apply clarsimp
  apply(simp add: htd_ind_def)+
done

lemma (in swap_global_addresses) test_spec:
  shows "test_spec"
apply unfold_locales
apply(hoare_rule HoarePartial.ProcNoRec1)
apply(unfold sep_app_def)
apply vcg
apply(fold lift_def)
apply(unfold sep_map_any_old)
apply sep_exists_tac
apply clarsimp
apply sep_point_tac
apply(unfold sep_app_def)
apply(simp add: sep_map'_ptr_safe sep_map'_ptr_aligned sep_map'_NULL sep_map'_lift sep_map'_g)
apply(rule_tac x=x in exI)
apply(rule_tac x=y in exI)
apply(rule_tac x="(\<lambda>z. c \<mapsto> (x + y))" in exI)
apply(rule_tac x="\<lambda>s. undefined" in exI)
apply clarsimp
apply rule
 apply(sep_select_tac "c \<mapsto> _")
 apply(rule sep_heap_update_global)
 apply(erule sep_conj_impl, simp)+
 apply simp
apply clarsimp
apply(rule_tac x="x+y" in exI)
apply(rule_tac x=y in exI)
apply(rule_tac x="(\<lambda>z. ba \<mapsto> x)" in exI)
apply fastforce
done

end
