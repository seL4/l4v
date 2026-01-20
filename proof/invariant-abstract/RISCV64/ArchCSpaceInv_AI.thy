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

lemma set_cap_valid_arch_state[wp]:
  "set_cap cap ptr \<lbrace> valid_arch_state \<rbrace>"
  by (wp valid_arch_state_lift_aobj_at_no_caps set_cap.aobj_at)

crunch set_cap for cur_domain_list[wp]: "cur_domain_list"
  (simp: crunch_simps
   wp: crunch_wps)

lemma replace_cap_invs:
  "\<lbrace>\<lambda>s. invs s \<and> cte_wp_at (replaceable s p cap) p s
        \<and> cap \<noteq> cap.NullCap
        \<and> ex_cte_cap_wp_to (appropriate_cte_cap cap) p s
        \<and> s \<turnstile> cap\<rbrace>
     set_cap cap p
   \<lbrace>\<lambda>rv s. invs s\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_mdb_def2 valid_arch_mdb_def)
  apply (rule hoare_pre)
   apply (wp replace_cap_valid_pspace
             set_cap_caps_of_state2 set_cap_idle
             replace_cap_ifunsafe valid_irq_node_typ
             set_cap_typ_at set_cap_irq_handlers
             set_cap_valid_arch_caps
             set_cap_cap_refs_respects_device_region_replaceable)
  apply (clarsimp simp: valid_pspace_def cte_wp_at_caps_of_state
                        replaceable_def)
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
   apply (simp add: reply_master_revocable_def)
  apply (rule conjI)
   apply (erule disjE)
    apply (simp add: fun_upd_def[symmetric] fun_upd_idem)
   apply (clarsimp simp add: reply_mdb_def)
   apply (thin_tac "\<forall>a b. (a, b) \<in> cte_refs cp nd \<and> Q a b\<longrightarrow> R a b" for cp nd Q R)
   apply (thin_tac "is_pt_cap cap \<longrightarrow> P" for cap P)+
   apply (rule conjI)
    apply (unfold reply_caps_mdb_def)[1]
    apply (erule allEI, erule allEI)
    apply (clarsimp split: if_split simp add: is_cap_simps
                 simp del: split_paired_Ex split_paired_All)
    apply (rename_tac ptra ptrb rights')
    apply (rule_tac x="(ptra,ptrb)" in exI)
    apply fastforce
   apply (unfold reply_masters_mdb_def)[1]
   apply (erule allEI, erule allEI)
   subgoal by (fastforce split: if_split_asm simp: is_cap_simps)
  apply (rule conjI)
   apply (erule disjE)
    apply (clarsimp simp add: is_reply_cap_to_def)
    apply (drule caps_of_state_cteD)
    apply (subgoal_tac "cte_wp_at (is_reply_cap_to t) p s")
     apply (erule(1) valid_reply_capsD [OF has_reply_cap_cte_wpD])
    apply (erule cte_wp_at_lift)
    apply (fastforce simp add:is_reply_cap_to_def)
   apply (simp add: is_cap_simps)
  apply (frule(1) valid_global_refsD2)
  apply (frule(1) cap_refs_in_kernel_windowD)
  apply (rule conjI)
   apply (erule disjE)
    apply (clarsimp simp: valid_reply_masters_def cte_wp_at_caps_of_state)
    apply (cases p, fastforce simp:is_master_reply_cap_to_def)
   apply (simp add: is_cap_simps)
  apply (elim disjE)
   apply simp
   apply (clarsimp simp: valid_table_capsD[OF caps_of_state_cteD]
                    valid_arch_caps_def unique_table_refs_no_cap_asidE)
  apply (rule conjI, clarsimp)
  apply (rule conjI, rule Ball_emptyI, simp add: gen_obj_refs_subset)
  by clarsimp

definition
  "is_simple_cap_arch cap \<equiv> \<not>is_pt_cap cap"

lemma is_simple_cap_arch:
  "\<not>is_arch_cap cap \<Longrightarrow> is_simple_cap_arch cap"
  by (simp add: is_cap_simps is_simple_cap_arch_def)

(* True when cap' is derived from cap. *)
definition
  "is_derived_arch cap' cap \<equiv>
    (is_pt_cap cap' \<longrightarrow> cap_asid cap = cap_asid cap' \<and> cap_asid cap' \<noteq> None) \<and>
    (vs_cap_ref cap = vs_cap_ref cap' \<or> is_frame_cap cap)"

lemma is_derived_arch_non_arch:
  "\<lbrakk> \<not> is_arch_cap cap; \<not> is_arch_cap cap' \<rbrakk> \<Longrightarrow> is_derived_arch cap cap'"
  unfolding is_derived_arch_def vs_cap_ref_def is_arch_cap_def is_pt_cap_def
  by (auto split: cap.splits)

lemmas cap_master_arch_cap_simps = cap_master_arch_cap_def[split_simps arch_cap.split]

lemmas cap_master_cap_def = cap_master_cap_def[simplified cap_master_arch_cap_def]

lemma same_master_cap_same_types:
  "cap_master_cap cap = cap_master_cap cap' \<Longrightarrow>
     is_pt_cap cap = is_pt_cap cap' \<and>
     is_frame_cap cap = is_frame_cap cap' \<and>
     is_ap_cap cap = is_ap_cap cap'"
  by (clarsimp simp: cap_master_cap_def is_cap_simps split: cap.splits arch_cap.splits)

lemma is_derived_cap_arch_asid_issues:
  "\<lbrakk> is_derived_arch cap cap'; cap_master_cap cap = cap_master_cap cap' \<rbrakk>
   \<Longrightarrow> (is_pt_cap cap \<longrightarrow> cap_asid cap \<noteq> None) \<and>
       (is_frame_cap cap \<or> (vs_cap_ref cap = vs_cap_ref cap'))"
  apply (simp add: is_derived_arch_def)
  by (auto simp: cap_master_cap_def is_cap_simps cap_asid_def
          split: cap.splits arch_cap.splits option.splits)

lemma is_derived_cap_arch_asid:
  "\<lbrakk> is_derived_arch cap cap'; cap_master_cap cap = cap_master_cap cap'; is_pt_cap cap' \<rbrakk>
   \<Longrightarrow> cap_asid cap = cap_asid cap'"
  unfolding is_derived_arch_def
  apply (cases cap; cases cap'; simp)
  by (auto simp: is_cap_simps cap_master_cap_def split: arch_cap.splits)

definition safe_parent_for_arch :: "cap \<Rightarrow> cap \<Rightarrow> bool" where
  "safe_parent_for_arch cap parent \<equiv> False"

lemma safe_parent_for_arch_not_arch:
  "\<not>is_arch_cap cap \<Longrightarrow> \<not>safe_parent_for_arch cap p"
  by (clarsimp simp: safe_parent_for_arch_def is_cap_simps)

lemma safe_parent_cap_range_arch:
  "safe_parent_for_arch cap pcap \<Longrightarrow> cap_range cap \<subseteq> cap_range pcap"
  by (clarsimp simp: safe_parent_for_arch_def cap_range_def)

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
     (FrameCap _ _ _ _  (Some (_, vptr))) \<Rightarrow> Some vptr
  |  (PageTableCap _ (Some (_, vptr))) \<Rightarrow> Some vptr
  | _ \<Rightarrow> None"

definition
  "cap_vptr cap \<equiv> arch_cap_fun_lift cap_vptr_arch None cap"

declare cap_vptr_arch_def[abs_def, simp]

lemmas cap_vptr_simps [simp] =
  cap_vptr_def [simplified, split_simps cap.split arch_cap.split option.split prod.split]

end

end
