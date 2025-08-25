(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
CSpace invariants
*)

theory ArchCSpaceInv_AI
imports CSpaceInv_AI
begin

context Arch begin arch_global_naming

lemma unique_table_refs_no_cap_asidE:
  "\<lbrakk>caps_of_state s p = Some cap;
    unique_table_refs (caps_of_state s)\<rbrakk>
   \<Longrightarrow> no_cap_to_obj_with_diff_ref cap S s"
  apply (clarsimp simp: no_cap_to_obj_with_diff_ref_def
                        cte_wp_at_caps_of_state)
  apply (unfold unique_table_refs_def)
  apply (drule_tac x=p in spec, drule_tac x="(a,b)" in spec)
  apply (drule spec)+
  apply (erule impE, assumption)+
  apply (clarsimp simp: is_cap_simps)
  done

lemmas unique_table_refs_no_cap_asidD
     = unique_table_refs_no_cap_asidE[where S="{}"]

lemma set_cap_valid_arch_state[wp]:
  "set_cap cap ptr \<lbrace> valid_arch_state \<rbrace>"
  by (wp valid_arch_state_lift_aobj_at_no_caps set_cap.aobj_at)

lemma replace_cap_invs:
  "\<lbrace>\<lambda>s. invs s \<and> cte_wp_at (replaceable s p cap) p s
        \<and> cap \<noteq> cap.NullCap
        \<and> ex_cte_cap_wp_to (appropriate_cte_cap cap) p s
        \<and> s \<turnstile> cap\<rbrace>
     set_cap cap p
   \<lbrace>\<lambda>rv s. invs s\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_mdb_def2)
  apply (rule hoare_pre)
   apply (wp replace_cap_valid_pspace
             set_cap_caps_of_state2 set_cap_idle
             replace_cap_ifunsafe valid_irq_node_typ
             set_cap_typ_at set_cap_irq_handlers
             set_cap_valid_arch_caps
             set_cap_cap_refs_respects_device_region_replaceable)
  apply (clarsimp simp: valid_pspace_def cte_wp_at_caps_of_state replaceable_def)
  apply (rule conjI)
   apply (fastforce simp: tcb_cap_valid_def
                   dest!: cte_wp_tcb_cap_valid [OF caps_of_state_cteD])
  apply (rule conjI)
   apply (erule_tac P="\<lambda>cps. mdb_cte_at cps (cdt s)" in rsubst)
   apply (rule ext)
   apply (safe del: disjE)[1]
    apply (simp add: gen_obj_refs_empty final_NullCap)+
  apply (rule conjI)
   apply (simp add: untyped_mdb_def is_cap_simps)
   apply (erule disjE)
    apply (clarsimp, rule conjI, clarsimp+)[1]
   apply (erule allEI, erule allEI)
   apply (drule_tac x="fst p" in spec, drule_tac x="snd p" in spec)
   apply (clarsimp simp: gen_obj_refs_subset)
   apply (drule(1) disjoint_subset, erule (1) notE)
  apply (rule conjI)
   apply (erule descendants_inc_minor)
    apply simp
   apply (elim disjE)
    apply clarsimp
   apply clarsimp
  apply (rule conjI)
   apply (erule disjE)
    apply (simp add: fun_upd_def[symmetric] fun_upd_idem)
   apply (simp add: untyped_inc_def not_is_untyped_no_range)
  apply (rule conjI)
   apply (erule disjE)
    apply (simp add: fun_upd_def[symmetric] fun_upd_idem)
   apply (simp add: ut_revocable_def)
  apply (rule conjI)
   apply (erule disjE)
    apply (clarsimp simp: irq_revocable_def)
   apply clarsimp
   apply (clarsimp simp: irq_revocable_def)
  apply (rule conjI)
   apply (erule disjE)
    apply (simp add: fun_upd_def[symmetric] fun_upd_idem)
    apply (clarsimp simp add: valid_global_refsD2)
   apply (simp add: valid_global_refsD2)
  apply (intro conjI)
         apply (erule disjE, simp, clarsimp simp: gen_obj_refs_subset subsetD)
        apply (erule disjE, auto simp: cap_refs_in_kernel_windowD)[1]
       apply (fastforce simp: unique_table_refs_no_cap_asidE valid_arch_caps_def)
      apply ((clarsimp simp only: valid_arch_caps_def valid_table_caps_def;
              erule disjE, elim allE, fastforce, simp)+)[4]
  apply (erule disjE, auto simp: cap_refs_in_kernel_windowD)
  done

definition
  "is_simple_cap_arch cap \<equiv> \<not>is_pt_cap cap \<and> \<not> is_pd_cap cap"

declare is_simple_cap_arch_def[simp]

lemma is_simple_cap_arch:
  "\<not>is_arch_cap cap \<Longrightarrow> is_simple_cap_arch cap"
  by (simp add: is_cap_simps)

definition
  "is_derived_arch cap cap' \<equiv>
    ((is_pt_cap cap \<or> is_pd_cap cap) \<longrightarrow>
         cap_asid cap = cap_asid cap' \<and> cap_asid cap \<noteq> None) \<and>
     (vs_cap_ref cap = vs_cap_ref cap' \<or> is_pg_cap cap')"

lemma is_derived_arch_non_arch:
  "\<not>is_arch_cap cap \<Longrightarrow> \<not> is_arch_cap cap' \<Longrightarrow>
      is_derived_arch cap cap'"
  unfolding is_derived_arch_def is_pg_cap_def is_pt_cap_def is_pd_cap_def
            vs_cap_ref_def is_arch_cap_def
  by (auto split: cap.splits)

lemma
  cap_master_cap_arch_simps:
  "cap_master_arch_cap ((arch_cap.PageCap dev ref rghts sz mapdata)) =
         (arch_cap.PageCap dev ref UNIV sz None)"
  "cap_master_arch_cap ( (arch_cap.ASIDPoolCap pool asid)) =
          (arch_cap.ASIDPoolCap pool 0)"
  "cap_master_arch_cap ( (arch_cap.PageTableCap ptr x)) =
          (arch_cap.PageTableCap ptr None)"
  "cap_master_arch_cap ( (arch_cap.PageDirectoryCap ptr y)) =
          (arch_cap.PageDirectoryCap ptr None)"
  "cap_master_arch_cap ( arch_cap.ASIDControlCap) =
          arch_cap.ASIDControlCap"
  by (simp add: cap_master_arch_cap_def)+

lemmas cap_master_cap_def = cap_master_cap_def[simplified cap_master_arch_cap_def]

lemma same_master_cap_same_types:
  "cap_master_cap cap = cap_master_cap cap' \<Longrightarrow>
    (is_pt_cap cap = is_pt_cap cap') \<and> (is_pd_cap cap = is_pd_cap cap')"
  by (clarsimp simp: cap_master_cap_def is_cap_simps
                  split: cap.splits arch_cap.splits)

lemma is_derived_cap_arch_asid_issues:
  "is_derived_arch cap cap' \<Longrightarrow>
    cap_master_cap cap = cap_master_cap cap'
      \<Longrightarrow> ((is_pt_cap cap \<or> is_pd_cap cap) \<longrightarrow> cap_asid cap \<noteq> None)
             \<and> (is_pg_cap cap \<or> (vs_cap_ref cap = vs_cap_ref cap'))"
  apply (simp add: is_derived_arch_def)
  by (auto simp: cap_master_cap_def is_cap_simps
                  cap_asid_def
                  split: cap.splits arch_cap.splits option.splits)

lemma is_derived_cap_arch_asid:
  "is_derived_arch cap cap' \<Longrightarrow> cap_master_cap cap = cap_master_cap cap' \<Longrightarrow>
      is_pt_cap cap' \<or> is_pd_cap cap' \<Longrightarrow> cap_asid cap = cap_asid cap'"
  unfolding is_derived_arch_def
  apply (cases cap; cases cap'; simp)
  by (auto simp: is_cap_simps cap_master_cap_def split: arch_cap.splits)

definition
  safe_parent_for_arch :: "cap \<Rightarrow> cap \<Rightarrow> bool"
where
  "safe_parent_for_arch cap parent \<equiv> False"

declare safe_parent_for_arch_def[simp]

lemma safe_parent_for_arch_not_arch:
  "\<not>is_arch_cap cap \<Longrightarrow> \<not>safe_parent_for_arch cap p"
  by clarsimp

lemma safe_parent_cap_range_arch:
  "safe_parent_for_arch cap pcap \<Longrightarrow> cap_range cap \<subseteq> cap_range pcap"
  by clarsimp

definition
  "cap_asid_base_arch cap \<equiv> case cap of
     ASIDPoolCap _ asid \<Rightarrow> Some asid
  | _ \<Rightarrow> None"

declare cap_asid_base_arch_def[abs_def, simp]

definition cap_asid_base :: "cap \<Rightarrow> asid option" where
  "cap_asid_base cap \<equiv> arch_cap_fun_lift cap_asid_base_arch None cap"

lemmas cap_asid_base_simps [simp] =
  cap_asid_base_def [simplified, split_simps cap.split arch_cap.split]

definition
  "cap_vptr_arch acap \<equiv> case acap of
     (PageCap _ _ _ _ (Some (_, vptr))) \<Rightarrow> Some vptr
  |  (PageTableCap _ (Some (_, vptr))) \<Rightarrow> Some vptr
  | _ \<Rightarrow> None"

definition
  "cap_vptr cap \<equiv> arch_cap_fun_lift cap_vptr_arch None cap"

declare cap_vptr_arch_def[abs_def, simp]

lemmas cap_vptr_simps [simp] =
  cap_vptr_def [simplified, split_simps cap.split arch_cap.split option.split prod.split]

end

end
