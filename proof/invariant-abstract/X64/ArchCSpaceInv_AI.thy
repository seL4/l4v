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

definition
   safe_ioport_insert :: "cap \<Rightarrow> cap \<Rightarrow> 'a::state_ext state \<Rightarrow> bool"
where
  "safe_ioport_insert newcap oldcap \<equiv>
          \<lambda>s. (cap_ioports newcap = {} \<comment> \<open>replacing with any non-IOPortCap\<close>
          \<or> ((\<forall>cap''\<in> ran (caps_of_state s).
                   cap_ioports newcap = cap_ioports cap'' \<comment> \<open>copy another IOPortCap\<close>
                \<or> cap_ioports newcap \<inter> cap_ioports cap'' = {} \<comment> \<open>new IOPortCap with unoverlapping range\<close>)))
          \<and> ((cap_ioports newcap - cap_ioports oldcap) \<subseteq> issued_ioports (arch_state s)) \<comment> \<open> all ioports are issued\<close>"

lemma cap_ioports_triv[simp]:
  "\<not>is_arch_cap cap \<Longrightarrow> cap_ioports cap = {}"
  by (clarsimp simp: is_cap_simps cap_ioports_def split: cap.splits arch_cap.splits)

lemma safe_ioport_insert_triv:
  "\<not>is_arch_cap newcap \<Longrightarrow> safe_ioport_insert newcap oldcap s"
  by (clarsimp simp: safe_ioport_insert_def)

lemma set_cap_ioports_safe:
 "\<lbrace>\<lambda>s. valid_ioports s
      \<and> cte_wp_at (\<lambda>cap'. safe_ioport_insert cap cap' s) ptr s\<rbrace>
    set_cap cap ptr
  \<lbrace>\<lambda>rv. valid_ioports\<rbrace>"
  apply (simp add: valid_ioports_def)
  apply (rule hoare_conjI)
   apply (simp add: all_ioports_issued_def Ball_def)
   apply (wp hoare_vcg_all_lift hoare_vcg_imp_lift')
   apply (clarsimp simp: cte_wp_at_caps_of_state safe_ioport_insert_def elim!: ranE split: if_split_asm)
    apply (auto)[2]
  apply (unfold ioports_no_overlap_def Ball_def)
  apply (wp hoare_vcg_all_lift hoare_vcg_imp_lift')
  apply (clarsimp simp: cte_wp_at_caps_of_state safe_ioport_insert_def elim!: ranE split: if_split_asm)
    apply blast+
  done

lemma set_cap_non_arch_valid_arch_state:
 "\<lbrace>\<lambda>s. valid_arch_state s \<and> cte_wp_at (\<lambda>_. \<not>is_arch_cap cap) ptr s\<rbrace>
  set_cap cap ptr
  \<lbrace>\<lambda>rv. valid_arch_state \<rbrace>"
  unfolding valid_arch_state_def
  by (wp set_cap.aobj_at valid_asid_table_lift valid_global_pts_lift valid_global_pds_lift
         valid_global_pdpts_lift typ_at_lift set_cap_ioports_safe)+
     (clarsimp simp: cte_wp_at_caps_of_state is_cap_simps valid_pspace_def safe_ioport_insert_triv)

lemma set_cap_ioports_no_new_ioports:
 "\<lbrace>\<lambda>s. valid_ioports s
      \<and> cte_wp_at (\<lambda>cap'. cap_ioports cap = {} \<or> cap_ioports cap = cap_ioports cap') ptr s\<rbrace>
    set_cap cap ptr
  \<lbrace>\<lambda>rv. valid_ioports\<rbrace>"
  apply (simp add: valid_ioports_def)
  apply (rule hoare_conjI)
   apply (simp add: all_ioports_issued_def Ball_def)
   apply (wp hoare_vcg_all_lift hoare_vcg_imp_lift')
   apply (clarsimp simp: cte_wp_at_caps_of_state safe_ioport_insert_def elim!: ranE split: if_split_asm)
    apply (auto)[2]
  apply (unfold ioports_no_overlap_def Ball_def)
  apply (wp hoare_vcg_all_lift hoare_vcg_imp_lift')
  apply (clarsimp simp: cte_wp_at_caps_of_state all_ioports_issued_def ioports_no_overlap_def
                  elim!: ranE
                  split: if_split_asm)
    apply (metis Int_empty_left ranI)
   apply (metis Int_empty_right ranI)
  by (meson ranI)

lemma set_cap_no_new_ioports_arch_valid_arch_state:
 "\<lbrace>\<lambda>s. valid_arch_state s
       \<and> cte_wp_at (\<lambda>cap'. cap_ioports cap = {} \<or> cap_ioports cap = cap_ioports cap') ptr s\<rbrace>
  set_cap cap ptr
  \<lbrace>\<lambda>rv. valid_arch_state \<rbrace>"
  unfolding valid_arch_state_def
  by (wp set_cap.aobj_at valid_asid_table_lift valid_global_pts_lift valid_global_pds_lift
         valid_global_pdpts_lift typ_at_lift set_cap_ioports_no_new_ioports)+
     (clarsimp simp: cte_wp_at_caps_of_state is_cap_simps valid_pspace_def)

lemma valid_ioportsD:
  "\<lbrakk>valid_ioports s; caps_of_state s p = Some cap; cap' \<in> ran (caps_of_state s);
      cap_ioports cap \<inter> cap_ioports cap' \<noteq> {}\<rbrakk>
       \<Longrightarrow> cap_ioports cap = cap_ioports cap'"
  apply (simp add: valid_ioports_def ioports_no_overlap_def)
  by auto

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
             set_cap_valid_arch_caps set_cap_no_new_ioports_arch_valid_arch_state
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
   apply (thin_tac "is_pd_cap cap \<longrightarrow> P" for cap P)+
   apply (thin_tac "is_pdpt_cap cap \<longrightarrow> P" for cap P)+
   apply (thin_tac "is_pml4_cap cap \<longrightarrow> P" for cap P)+
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
    apply (simp add: fun_upd_def[symmetric] fun_upd_idem)
   apply clarsimp
   apply (clarsimp simp: ioport_revocable_def is_cap_simps)
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
  apply clarsimp
  apply (rule conjI, solves clarsimp)
  apply (rule Ball_emptyI, simp add: gen_obj_refs_subset)
  done


definition
  "is_simple_cap_arch cap \<equiv> \<not>is_pt_cap cap \<and> \<not> is_pd_cap cap
                          \<and> \<not> is_pdpt_cap cap \<and> \<not> is_pml4_cap cap \<and> \<not> is_ioport_control_cap cap"

declare is_simple_cap_arch_def[simp]

lemma is_simple_cap_arch:
  "\<not>is_arch_cap cap \<Longrightarrow> is_simple_cap_arch cap"
  by (simp add: is_cap_simps)

(* True when cap' is derived from cap. *)
definition
  "is_derived_arch cap' cap \<equiv>
    (is_vspace_table_cap cap' \<longrightarrow> cap_asid cap = cap_asid cap' \<and> cap_asid cap' \<noteq> None) \<and>
    (vs_cap_ref cap = vs_cap_ref cap' \<or> is_pg_cap cap) \<and> \<not> is_ioport_control_cap cap'"

lemma is_derived_arch_non_arch:
  "\<not> is_arch_cap cap \<Longrightarrow> \<not> is_arch_cap cap' \<Longrightarrow> is_derived_arch cap cap'"
  unfolding is_derived_arch_def vs_cap_ref_def is_arch_cap_def is_ioport_control_cap_def
            is_pg_cap_def is_pt_cap_def is_pd_cap_def is_pdpt_cap_def is_pml4_cap_def
  by (auto split: cap.splits)

lemma
  cap_master_cap_arch_simps:
  "cap_master_arch_cap (ASIDPoolCap pool asid) = ASIDPoolCap pool 0"
  "cap_master_arch_cap ASIDControlCap = ASIDControlCap"
  "cap_master_arch_cap (IOPortCap f l) = IOPortCap f l"
  "cap_master_arch_cap (PageCap dev ref rghts maptype sz mapdata)
      = PageCap dev ref UNIV VMNoMap sz None"
  "cap_master_arch_cap (PageTableCap ptr x) = PageTableCap ptr None"
  "cap_master_arch_cap (PageDirectoryCap ptr x) = PageDirectoryCap ptr None"
  "cap_master_arch_cap (PDPointerTableCap ptr x) = PDPointerTableCap ptr None"
  "cap_master_arch_cap (PML4Cap ptr y) = PML4Cap ptr None"
  by (simp add: cap_master_arch_cap_def)+

lemmas cap_master_cap_def = cap_master_cap_def[simplified cap_master_arch_cap_def]

lemma same_master_cap_same_types:
  "cap_master_cap cap = cap_master_cap cap' \<Longrightarrow>
    (is_pt_cap cap = is_pt_cap cap') \<and> (is_pd_cap cap = is_pd_cap cap') \<and>
    (is_pdpt_cap cap = is_pdpt_cap cap') \<and> (is_pml4_cap cap = is_pml4_cap cap')"
  by (clarsimp simp: cap_master_cap_def is_cap_simps
                  split: cap.splits arch_cap.splits)

lemma is_derived_cap_arch_asid_issues:
  "is_derived_arch cap cap' \<Longrightarrow>
    cap_master_cap cap = cap_master_cap cap'
      \<Longrightarrow> (is_vspace_table_cap cap \<longrightarrow> cap_asid cap \<noteq> None)
             \<and> (is_pg_cap cap \<or> (vs_cap_ref cap = vs_cap_ref cap'))"
  apply (simp add: is_derived_arch_def)
  by (auto simp: cap_master_cap_def is_cap_simps cap_asid_def
          split: cap.splits arch_cap.splits option.splits)

lemma is_derived_cap_arch_asid:
  "is_derived_arch cap cap' \<Longrightarrow> cap_master_cap cap = cap_master_cap cap'
    \<Longrightarrow> is_vspace_table_cap cap' \<Longrightarrow> cap_asid cap = cap_asid cap'"
  unfolding is_derived_arch_def
  apply (cases cap; cases cap'; simp)
  by (auto simp: is_cap_simps cap_master_cap_def split: arch_cap.splits)

definition
  safe_parent_for_arch :: "cap \<Rightarrow> cap \<Rightarrow> bool"
where
  "safe_parent_for_arch cap parent \<equiv>
            (\<exists>f l. cap = (cap.ArchObjectCap (IOPortCap f l)))
          \<and> (parent = (cap.ArchObjectCap (IOPortControlCap)))"

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
     (PageCap _ _ _ _ _ (Some (_, vptr))) \<Rightarrow> Some vptr
  |  (PageTableCap _ (Some (_, vptr))) \<Rightarrow> Some vptr
  |  (PageDirectoryCap _ (Some (_, vptr))) \<Rightarrow> Some vptr
  |  (PDPointerTableCap _ (Some (_, vptr))) \<Rightarrow> Some vptr
  | _ \<Rightarrow> None"

definition
  "cap_vptr cap \<equiv> arch_cap_fun_lift cap_vptr_arch None cap"

declare cap_vptr_arch_def[abs_def, simp]

lemmas cap_vptr_simps [simp] =
  cap_vptr_def [simplified, split_simps cap.split arch_cap.split option.split prod.split]

end

end
