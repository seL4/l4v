(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory list_reverse
imports "CParser.CTranslation" "$L4V_ARCH/imports/MachineWords"
begin

declare hrs_simps [simp add]
declare exists_left [simp add]
declare sep_conj_ac [simp add]

primrec
  list :: "machine_word list \<Rightarrow> machine_word ptr \<Rightarrow> heap_state \<Rightarrow> bool"
where
  "list [] i = (\<lambda>s. i=NULL \<and> \<box> s)"
| "list (x#xs) i = (\<lambda>s. i=Ptr x \<and> x\<noteq>0 \<and> (\<exists>j. ((i \<mapsto> j) \<and>\<^sup>* list xs (Ptr j)) s))"

lemma list_empty [simp]:
  shows "list xs NULL = (\<lambda>s. xs = [] \<and> \<box> s)"
  by (cases xs) (auto dest!: sep_conj_mapD)

declare sep_conj_com [simp del]
declare sep_conj_left_com [simp del]

external_file "list_reverse.c"
install_C_file memsafe "list_reverse.c"

thm list_reverse_global_addresses.reverse_body_def

lemma (in list_reverse_global_addresses)
  shows "reverse_spec"
apply (unfold reverse_spec_def)
apply (hoare_rule HoarePartial.ProcNoRec1)
apply (hoare_rule anno = "reverse_invs_body zs" in HoarePartial.annotateI)
 prefer 2
 apply (simp add: whileAnno_def reverse_invs_body_def)
apply(subst reverse_invs_body_def)
apply(unfold sep_app_def)
apply vcg
  apply (fold lift_def)
  apply(force simp: sep_conj_com)
 apply clarsimp
 apply(case_tac xs)
  apply clarsimp
 apply clarsimp
 apply sep_exists_tac
 apply clarsimp
 apply sep_point_tac
 apply rule
  apply(erule sep_map'_g)
 apply rule
  apply(erule sep_map'_ptr_safe)
 apply(rule_tac x="lista" in exI)
 apply (simp add: ucast_id)
 apply sep_exists_tac
 apply(rule_tac x=j in exI)
 apply simp
 apply(rule sep_heap_update_global)
 apply(erule sep_conj_impl)
  apply simp
 apply(sep_select_tac "list lista _")
 apply(erule sep_conj_impl)
  apply(subgoal_tac "lift a (Ptr aa) = ja")
   apply simp
  apply(erule_tac d=b in sep_map'_lift)
 apply simp
apply(simp add: sep_conj_com)
done

declare hrs_simps [simp del]

lemma (in list_reverse_global_addresses) mem_safe_reverse_invs_body:
  "mem_safe (reverse_invs_body \<alpha>) \<Gamma>"
apply(unfold reverse_invs_body_def creturn_def)
apply(subst mem_safe_restrict)
apply(rule intra_mem_safe)
apply(auto simp: whileAnno_def intra_sc)
done

declare hrs_simps [simp add]

lemma (in list_reverse_global_addresses) sep_frame_reverse_invs_body:
  "\<lbrakk> \<forall>\<sigma>. \<Gamma> \<turnstile> \<lbrace>\<sigma>. (P (f \<acute>(\<lambda>x. x)))\<^bsup>sep\<^esup> \<rbrace> reverse_invs_body \<alpha> \<lbrace> (Q (g \<sigma> \<acute>(\<lambda>x. x)))\<^bsup>sep\<^esup> \<rbrace>;
      htd_ind f; htd_ind g; \<forall>s. htd_ind (g s) \<rbrakk> \<Longrightarrow>
      \<forall>\<sigma>. \<Gamma> \<turnstile> \<lbrace>\<sigma>. (P (f \<acute>(\<lambda>x. x)) \<and>\<^sup>* R (h \<acute>(\<lambda>x. x)))\<^bsup>sep\<^esup> \<rbrace> reverse_invs_body \<alpha>
              \<lbrace> (Q (g \<sigma> \<acute>(\<lambda>x. x)) \<and>\<^sup>* R (h \<sigma>))\<^bsup>sep\<^esup> \<rbrace>"
apply(simp only: sep_app_def)
apply(rule sep_frame)
    apply simp+
apply(rule mem_safe_reverse_invs_body)
done

end
