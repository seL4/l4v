(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory CSpaceInvPre_AI
imports ArchAcc_AI
begin

context begin interpretation Arch .

requalify_consts
  table_cap_ref
  empty_table

requalify_facts
  empty_table_def
  cur_tcb_more_update
end

declare cur_tcb_more_update[iff]

lemma set_cap_caps_of_state[wp]:
  "\<lbrace>\<lambda>s. P ((caps_of_state s) (ptr \<mapsto> cap))\<rbrace> set_cap cap ptr \<lbrace>\<lambda>rv s. P (caps_of_state s)\<rbrace>"
  apply (cases ptr)
  apply (clarsimp simp add: set_cap_def split_def)
  apply (rule bind_wp [OF _ get_object_sp])
  apply (case_tac obj; simp_all split del: if_split cong: if_cong bind_cong)
   apply (wpsimp wp: set_object_wp)
   apply (fastforce elim!: rsubst[where P=P]
                    simp: caps_of_state_cte_wp_at cte_wp_at_cases
                          fun_upd_def[symmetric] wf_cs_upd obj_at_def)
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: obj_at_def)
  apply (safe elim!: rsubst[where P=P];
         rule ext; clarsimp simp: caps_of_state_cte_wp_at cte_wp_at_cases)
      apply (auto simp: tcb_cap_cases_def split: if_split_asm)
  done

lemmas gen_obj_refs_Int_not =
    arg_cong [where f=Not, OF gen_obj_refs_Int, simplified, symmetric]


lemma ObjRef_nonempty_ArchRef_empty:
  "x \<in> ObjRef ` (obj_refs c) \<Longrightarrow> ArchRef ` arch_gen_refs c = {}"
  by (clarsimp simp: obj_ref_not_arch_gen_ref)

lemma ArchRef_nonempty_ObjRef_empty:
  "x \<in> ArchRef ` arch_gen_refs c \<Longrightarrow> ObjRef ` (obj_refs c) = {}"
  by (clarsimp simp: arch_gen_ref_not_obj_ref)

lemmas gen_obj_ref_arch_cap_simps =
            ObjRef_nonempty_ArchRef_empty[where c="ArchObjectCap ac" for ac, simplified]
            ArchRef_nonempty_ObjRef_empty[where c="ArchObjectCap ac" for ac, simplified]
            obj_ref_not_arch_gen_ref[where cap="ArchObjectCap ac" for ac, simplified]
            arch_gen_ref_not_obj_ref[where cap="ArchObjectCap ac" for ac, simplified]

lemma gen_obj_refs_inD:
  "x \<in> gen_obj_refs cap \<Longrightarrow> gen_obj_refs cap = {x}"
  apply (case_tac cap; clarsimp simp: gen_obj_refs_def dest!:arch_gen_obj_refs_inD)
  apply (auto dest: gen_obj_ref_arch_cap_simps simp: arch_gen_obj_refs_inD)
  done

lemma gen_obj_refs_distinct_or_equal:
  "\<lbrakk> gen_obj_refs cap \<inter> gen_obj_refs cap' \<noteq> {} \<rbrakk>
     \<Longrightarrow> gen_obj_refs cap = gen_obj_refs cap'"
  by (clarsimp elim!: nonemptyE dest!: gen_obj_refs_inD)

lemma obj_ref_is_gen_obj_ref:
  "x \<in> obj_refs cap \<Longrightarrow> ObjRef x \<in> gen_obj_refs cap"
  by (simp add: gen_obj_refs_def)

lemma gen_obj_refs_eq:
  "(gen_obj_refs cap = gen_obj_refs cap')
      = (obj_refs cap = obj_refs cap' \<and> cap_irqs cap = cap_irqs cap'
         \<and> arch_gen_refs cap = arch_gen_refs cap')"
  apply (simp add: gen_obj_refs_def image_Un[symmetric])
  by auto

lemma not_final_another':
  "\<lbrakk> \<not> is_final_cap' cap s; fst (get_cap p s) = {(cap, s)};
       gen_obj_refs cap \<noteq> {} \<rbrakk>
      \<Longrightarrow> \<exists>p' cap'. p' \<noteq> p \<and> fst (get_cap p' s) = {(cap', s)}
                         \<and> gen_obj_refs cap' = gen_obj_refs cap
                         \<and> \<not> is_final_cap' cap' s"
  apply (simp add: is_final_cap'_def gen_obj_refs_Int_not cong: conj_cong
              del: split_paired_Ex split_paired_All)
  apply (erule not_singleton_oneE[where p=p])
   apply simp
  apply (rule_tac x=p' in exI)
  apply clarsimp
  apply (drule gen_obj_refs_distinct_or_equal)
  apply simp
  done

lemma not_final_another_caps:
  "\<lbrakk> \<not> is_final_cap' cap s; caps_of_state s p = Some cap;
       r \<in> gen_obj_refs cap \<rbrakk>
      \<Longrightarrow> \<exists>p' cap'. p' \<noteq> p \<and> caps_of_state s p' = Some cap'
                         \<and> gen_obj_refs cap' = gen_obj_refs cap
                         \<and> \<not> is_final_cap' cap' s"
  apply (clarsimp dest!: caps_of_state_cteD
                   simp: cte_wp_at_def)
  apply (drule(1) not_final_another')
   apply clarsimp
  apply clarsimp
  apply (subgoal_tac "cte_wp_at ((=) cap') (a, b) s")
   apply (fastforce simp: cte_wp_at_caps_of_state)
  apply (simp add: cte_wp_at_def)
  done

lemma wf_cs_ran_nonempty:
  "well_formed_cnode_n sz cs \<Longrightarrow> ran cs \<noteq> {}"
  apply (clarsimp simp: well_formed_cnode_n_def)
  apply (drule_tac f="\<lambda>S. replicate sz False \<in> S" in arg_cong)
  apply auto
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
  "gen_obj_refs (src_cap\<lparr>free_index := a\<rparr>) = gen_obj_refs src_cap"
  "vs_cap_ref (src_cap\<lparr>free_index := a\<rparr>) = vs_cap_ref src_cap"
  "untyped_range (cap \<lparr>free_index :=a \<rparr>) = untyped_range cap"
  "zobj_refs (c\<lparr>free_index:=a\<rparr>) =  zobj_refs c"
  "obj_refs (c\<lparr>free_index:=a\<rparr>) = obj_refs c"
  by (auto simp: cap_asid_def free_index_update_def vs_cap_ref_def
                 is_cap_simps gen_obj_refs_def
          split: cap.splits arch_cap.splits)
end

end
