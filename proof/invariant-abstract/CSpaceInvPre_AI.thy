(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory CSpaceInvPre_AI
imports "./$L4V_ARCH/ArchAcc_AI"
begin

context begin interpretation Arch .

requalify_consts
  table_cap_ref
  empty_table

requalify_facts
  empty_table_def

end
  
         
lemma set_cap_caps_of_state[wp]:
  "\<lbrace>\<lambda>s. P ((caps_of_state s) (ptr \<mapsto> cap))\<rbrace> set_cap cap ptr \<lbrace>\<lambda>rv s. P (caps_of_state s)\<rbrace>"
  apply (cases ptr)
  apply (clarsimp simp add: set_cap_def split_def)
  apply (rule hoare_seq_ext [OF _ get_object_sp])
  apply (case_tac obj, simp_all add: set_object_def
                          split del: if_split cong: if_cong bind_cong)
   apply (rule hoare_pre, wp)
   apply (clarsimp elim!: rsubst[where P=P]
                    simp: caps_of_state_cte_wp_at cte_wp_at_cases
                          fun_upd_def[symmetric] wf_cs_upd obj_at_def
                  intro!: ext)
   apply auto[1]
  apply (rule hoare_pre, wp)
  apply (clarsimp simp: obj_at_def)
  apply (safe elim!: rsubst[where P=P] intro!: ext)
      apply (auto simp: caps_of_state_cte_wp_at cte_wp_at_cases,
             auto simp: tcb_cap_cases_def split: if_split_asm)
  done

lemmas obj_irq_refs_Int_not =
    arg_cong [where f=Not, OF obj_irq_refs_Int, simplified, symmetric]

lemma obj_irq_refs_inD:
  "x \<in> obj_irq_refs cap \<Longrightarrow> obj_irq_refs cap = {x}"
  apply (case_tac cap, simp_all add: obj_irq_refs_def cap_irqs_def
                                     cap_irq_opt_def split: sum.split_asm)
  apply clarsimp
  done

lemma objirqrefs_distinct_or_equal:
  "\<lbrakk> obj_irq_refs cap \<inter> obj_irq_refs cap' \<noteq> {} \<rbrakk> 
     \<Longrightarrow> obj_irq_refs cap = obj_irq_refs cap'"
  by (clarsimp elim!: nonemptyE dest!: obj_irq_refs_inD)

lemma obj_ref_is_obj_irq_ref:
  "x \<in> obj_refs cap \<Longrightarrow> Inl x \<in> obj_irq_refs cap"
  by (simp add: obj_irq_refs_def)

lemma obj_irq_refs_eq:
  "(obj_irq_refs cap = obj_irq_refs cap')
      = (obj_refs cap = obj_refs cap' \<and> cap_irqs cap = cap_irqs cap')"
  apply (simp add: obj_irq_refs_def)
  apply (subgoal_tac "\<forall>x y. Inl x \<noteq> Inr y")
   apply blast
  apply simp
  done

lemma not_final_another':
  "\<lbrakk> \<not> is_final_cap' cap s; fst (get_cap p s) = {(cap, s)};
       obj_irq_refs cap \<noteq> {} \<rbrakk>
      \<Longrightarrow> \<exists>p' cap'. p' \<noteq> p \<and> fst (get_cap p' s) = {(cap', s)}
                         \<and> obj_irq_refs cap' = obj_irq_refs cap
                         \<and> \<not> is_final_cap' cap' s"
  apply (simp add: is_final_cap'_def obj_irq_refs_Int_not cong: conj_cong
              del: split_paired_Ex split_paired_All)
  apply (erule not_singleton_oneE[where p=p])
   apply simp
  apply (rule_tac x=p' in exI)
  apply clarsimp
  apply (drule objirqrefs_distinct_or_equal)
  apply simp
  done

lemma not_final_another_caps:
  "\<lbrakk> \<not> is_final_cap' cap s; caps_of_state s p = Some cap;
       r \<in> obj_irq_refs cap \<rbrakk>
      \<Longrightarrow> \<exists>p' cap'. p' \<noteq> p \<and> caps_of_state s p' = Some cap'
                         \<and> obj_irq_refs cap' = obj_irq_refs cap
                         \<and> \<not> is_final_cap' cap' s"
  apply (clarsimp dest!: caps_of_state_cteD
                   simp: cte_wp_at_def)
  apply (drule(1) not_final_another')
   apply clarsimp
  apply clarsimp
  apply (subgoal_tac "cte_wp_at (op = cap') (a, b) s")
   apply (fastforce simp: cte_wp_at_caps_of_state)
  apply (simp add: cte_wp_at_def)
  done

lemma wf_cs_ran_nonempty:
  "well_formed_cnode_n sz cs \<Longrightarrow> ran cs \<noteq> {}"
  apply (clarsimp simp: well_formed_cnode_n_def)
  apply (drule_tac f="\<lambda>S. replicate sz False \<in> S" in arg_cong)
  apply (auto intro: ranI)
  done

lemma set_cap_obj_at_impossible:
  "\<lbrace>\<lambda>s. P (obj_at P' p s) \<and> (\<forall>ko. P' ko \<longrightarrow> caps_of ko = {})\<rbrace>
     set_cap cap ptr
   \<lbrace>\<lambda>rv s. P (obj_at P' p s)\<rbrace>"
  apply (simp add: set_cap_def split_def set_object_def)
  apply (wp get_object_wp | wpc)+
  apply (clarsimp simp: obj_at_def)
  apply (subgoal_tac "\<forall>sz cs. well_formed_cnode_n sz cs \<longrightarrow> \<not> P' (CNode sz cs)")
   apply (subgoal_tac "\<forall>tcb. \<not> P' (TCB tcb)")
    apply (clarsimp simp: fun_upd_def[symmetric] wf_cs_insert dom_def)
    apply auto[1]
   apply (auto simp:caps_of_def cap_of_def ran_tcb_cnode_map wf_cs_ran_nonempty)
  done

definition
  no_cap_to_obj_with_diff_ref :: "cap \<Rightarrow> cslot_ptr set \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
 "no_cap_to_obj_with_diff_ref cap S \<equiv>
  \<lambda>s. \<forall>p \<in> UNIV - S. \<not> cte_wp_at (\<lambda>c. obj_refs c = obj_refs cap \<and>
                                     \<not> (table_cap_ref c = table_cap_ref cap)) p s"
                                                 
lemma empty_table_caps_of:
  "empty_table S ko \<Longrightarrow> caps_of ko = {}"
  by (cases ko, simp_all add: empty_table_def caps_of_def cap_of_def)

context begin interpretation Arch . 
lemma free_index_update_test_function_stuff[simp]:
  "cap_asid (src_cap\<lparr>free_index := a\<rparr>) = cap_asid src_cap"
  "obj_irq_refs (src_cap\<lparr>free_index := a\<rparr>) = obj_irq_refs src_cap"
  "vs_cap_ref (src_cap\<lparr>free_index := a\<rparr>) = vs_cap_ref src_cap"
  "untyped_range (cap \<lparr>free_index :=a \<rparr>) = untyped_range cap"
  "zobj_refs (c\<lparr>free_index:=a\<rparr>) =  zobj_refs c"
  "obj_refs (c\<lparr>free_index:=a\<rparr>) = obj_refs c"
  by (auto simp: cap_asid_def free_index_update_def vs_cap_ref_def
                 is_cap_simps obj_irq_refs_def
          split: cap.splits arch_cap.splits)
end

end
