(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

(*
ARM-specific CSpace invariants
*)

theory ArchCSpace_AI
imports "../CSpacePre_AI"
begin
context Arch begin global_naming ARM

lemmas typ_at_eq_kheap_obj = typ_at_eq_kheap_obj atyp_at_eq_kheap_obj

lemmas set_cap_atyp_ats[wp] = abs_atyp_at_lifts[OF set_cap_typ_at]

lemmas cap_master_cap_def = cap_master_cap_def[simplified cap_master_arch_cap_def]

definition
  "final_matters_arch ac \<equiv>
     (case ac of
         ASIDPoolCap r as \<Rightarrow> True
       | ASIDControlCap \<Rightarrow> False
       | PageCap r rghts sz mapdata \<Rightarrow> False
       | PageTableCap r mapdata \<Rightarrow> True
       | PageDirectoryCap r mapdata \<Rightarrow> True)"

definition
  "cap_vptr_arch acap \<equiv> case acap of 
     (PageCap _ _ _ (Some (_, vptr))) \<Rightarrow> Some vptr
  |  (PageTableCap _ (Some (_, vptr))) \<Rightarrow> Some vptr
  | _ \<Rightarrow> None"

definition
  "cap_vptr cap \<equiv> arch_cap_fun_lift cap_vptr_arch None cap"

declare cap_vptr_arch_def[abs_def, simp]

lemmas cap_vptr_simps [simp] = 
  cap_vptr_def [simplified, split_simps cap.split arch_cap.split option.split prod.split]

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

lemma is_derived_cap_arch_asid:
  "is_derived_arch cap cap' \<Longrightarrow> cap_master_cap cap = cap_master_cap cap' \<Longrightarrow> 
      is_pt_cap cap' \<or> is_pd_cap cap' \<Longrightarrow> cap_asid cap = cap_asid cap'"
  unfolding is_derived_arch_def
  apply (cases cap; cases cap'; simp)
  by (auto simp: is_cap_simps cap_master_cap_def split: arch_cap.splits)


lemma is_page_cap_PageCap[simp]:
  "is_page_cap (PageCap ref rghts pgsiz mapdata)"
  by (simp add: is_page_cap_def)

lemma pageBitsForSize_eq[simp]:
  "(pageBitsForSize sz = pageBitsForSize sz') = (sz = sz')"
by (case_tac sz) (case_tac sz', simp+)+


lemma
  cap_master_cap_arch_simps:
  "cap_master_arch_cap ((arch_cap.PageCap ref rghts sz mapdata)) =
         (arch_cap.PageCap ref UNIV sz None)"
  "cap_master_arch_cap ( (arch_cap.ASIDPoolCap pool asid)) =
          (arch_cap.ASIDPoolCap pool 0)"
  "cap_master_arch_cap ( (arch_cap.PageTableCap ptr x)) =
          (arch_cap.PageTableCap ptr None)"
  "cap_master_arch_cap ( (arch_cap.PageDirectoryCap ptr y)) =
          (arch_cap.PageDirectoryCap ptr None)"
  "cap_master_arch_cap ( arch_cap.ASIDControlCap) =
          arch_cap.ASIDControlCap"
  by (simp add: cap_master_arch_cap_def)+

lemma aobj_ref_cases':
  "aobj_ref acap = (case acap of arch_cap.ASIDControlCap \<Rightarrow> aobj_ref acap
                                | _ \<Rightarrow> aobj_ref acap)"
  by (simp split: arch_cap.split)


lemma aobj_ref_cases:
  "aobj_ref acap = 
  (case acap of 
    arch_cap.ASIDPoolCap w1 w2 \<Rightarrow> Some w1 
  | arch_cap.ASIDControlCap \<Rightarrow> None
  | arch_cap.PageCap w s sz opt \<Rightarrow> Some w
  | arch_cap.PageTableCap w opt \<Rightarrow> Some w
  | arch_cap.PageDirectoryCap w opt \<Rightarrow> Some w)"
  apply (subst aobj_ref_cases')
  apply (clarsimp cong: arch_cap.case_cong)
  done

definition
  "cap_asid_base_arch cap \<equiv> case cap of 
     (arch_cap.ASIDPoolCap _ asid) \<Rightarrow> Some asid
  | _ \<Rightarrow> None"

declare cap_asid_base_arch_def[abs_def, simp]

definition
  "cap_asid_base cap \<equiv> arch_cap_fun_lift cap_asid_base_arch None cap"

lemmas cap_asid_base_simps [simp] = 
  cap_asid_base_def [simplified, split_simps cap.split arch_cap.split]

definition
  "ups_of_heap h \<equiv> \<lambda>p.
   case h p of Some (ArchObj (DataPage sz)) \<Rightarrow> Some sz | _ \<Rightarrow> None"

lemma ups_of_heap_typ_at:
  "ups_of_heap (kheap s) p = Some sz \<longleftrightarrow> typ_at (AArch (AIntData sz)) p s"
  by (simp add: typ_at_eq_kheap_obj ups_of_heap_def
      split: option.splits Structures_A.kernel_object.splits
             arch_kernel_obj.splits)

lemma ups_of_heap_typ_at_def:
  "ups_of_heap (kheap s) \<equiv> \<lambda>p.
   if \<exists>!sz. typ_at (AArch (AIntData sz)) p s
     then Some (THE sz. typ_at (AArch (AIntData sz)) p s)
   else None"
  apply (rule eq_reflection)
  apply (rule ext)
  apply (clarsimp simp: ups_of_heap_typ_at)
  apply (intro conjI impI)
   apply (frule (1) theI')
  apply safe
   apply (fastforce simp: ups_of_heap_typ_at)
  apply (clarsimp simp add: obj_at_def)
  done

lemma ups_of_heap_non_arch_upd:
  "h x = Some ko \<Longrightarrow> non_arch_obj ko \<Longrightarrow> non_arch_obj ko' \<Longrightarrow> ups_of_heap (h(x \<mapsto> ko')) = ups_of_heap h"
  by (rule ext) (auto simp add: ups_of_heap_def non_arch_obj_def split: kernel_object.splits)

definition
  "is_simple_cap_arch cap \<equiv> \<not>is_pt_cap cap \<and> \<not> is_pd_cap cap"

declare is_simple_cap_arch_def[simp]

lemma is_simple_cap_arch:
  "\<not>is_arch_cap cap \<Longrightarrow> is_simple_cap_arch cap"
  by (simp add: is_cap_simps)

crunch inv[wp]: lookup_ipc_buffer "I"


lemma vs_cap_ref_to_table_cap_ref:
  "\<not> is_pg_cap cap \<Longrightarrow> vs_cap_ref cap = table_cap_ref cap"
  by (simp add: is_pg_cap_def table_cap_ref_def vs_cap_ref_simps
         split: cap.splits arch_cap.splits)


lemma cap_master_cap_pg_cap: 
 "\<lbrakk>cap_master_cap cap = cap_master_cap capa\<rbrakk>
  \<Longrightarrow> is_pg_cap cap = is_pg_cap capa"
  by (clarsimp simp:cap_master_cap_def is_cap_simps 
    split:cap.splits arch_cap.splits dest!:cap_master_cap_eqDs)

lemma master_arch_cap_obj_refs:
  "cap_master_arch_cap c = cap_master_arch_cap c' \<Longrightarrow> aobj_ref c = aobj_ref c'"
  by (simp add: cap_master_arch_cap_def split: arch_cap.splits)

lemma master_arch_cap_cap_class:
  "cap_master_arch_cap c = cap_master_arch_cap c' \<Longrightarrow> acap_class c = acap_class c'"
  by (simp add: cap_master_arch_cap_def split: arch_cap.splits)

lemma is_cap_free_index_update[simp]:
  "is_pd_cap (src_cap\<lparr>free_index := a\<rparr>) = is_pd_cap src_cap"
  "is_pt_cap (src_cap\<lparr>free_index := a\<rparr>) = is_pt_cap src_cap"
  by (simp add:is_cap_simps free_index_update_def split:cap.splits)+

lemma masked_as_full_test_function_stuff[simp]:
  "is_pd_cap (masked_as_full a cap ) = is_pd_cap a"
  "is_pt_cap (masked_as_full a cap ) = is_pt_cap a"
  "vs_cap_ref (masked_as_full a cap ) = vs_cap_ref a"
  by (auto simp:masked_as_full_def)

lemma same_aobject_as_commute:
  "same_aobject_as x y \<Longrightarrow> same_aobject_as y x"
  by (cases x; cases y; clarsimp)

lemmas wellformed_cap_simps = wellformed_cap_simps[simplified wellformed_acap_def, split_simps arch_cap.split]

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

lemma is_pt_pd_Null[simp]:
  "\<not> is_pt_cap cap.NullCap \<and> \<not> is_pd_cap cap.NullCap"
  by (simp add: is_pt_cap_def is_pd_cap_def)

lemma unique_table_caps_upd_eqD: 
  "\<lbrakk>ms a = Some b; cap_asid b = cap_asid b'; obj_refs b = obj_refs b';
    is_pd_cap b = is_pd_cap b'; is_pt_cap b = is_pt_cap b'\<rbrakk>
   \<Longrightarrow> unique_table_caps (ms (a \<mapsto> b')) = unique_table_caps (ms)"
  unfolding unique_table_caps_def
  apply (rule iffI)
  apply (intro allI impI,elim allE)
    apply (erule impE)
    apply (rule_tac p = p in fun_upd_Some)
    apply assumption
      apply (erule impE)
      apply (rule_tac p = p' in fun_upd_Some)
      apply simp
    apply (simp add: if_distrib split:if_splits)
  apply (intro allI impI,elim allE)
    apply (erule impE)
    apply (rule_tac p = p in fun_upd_Some_rev)
      apply simp+
  apply (erule impE)
    apply (rule_tac p = p' in fun_upd_Some_rev)
    apply simp+
  apply (simp add: if_distrib split:if_splits)
  done

lemma set_untyped_cap_as_full_not_final_not_pg_cap:
  "\<lbrace>\<lambda>s. (\<exists>a b. (a, b) \<noteq> dest \<and> \<not> is_pg_cap cap' 
            \<and> cte_wp_at (\<lambda>cap. obj_irq_refs cap = obj_irq_refs cap' \<and> \<not> is_pg_cap cap) (a, b) s)
      \<and> cte_wp_at (op = src_cap) src s\<rbrace>
  set_untyped_cap_as_full src_cap cap src 
  \<lbrace>\<lambda>_ s.(\<exists>a b. (a, b) \<noteq> dest \<and> \<not> is_pg_cap cap' 
            \<and> cte_wp_at (\<lambda>cap. obj_irq_refs cap = obj_irq_refs cap' \<and> \<not> is_pg_cap cap) (a, b) s)\<rbrace>"
  apply (rule hoare_pre)
  apply (wp hoare_vcg_ex_lift)
   apply (rule_tac Q = "cte_wp_at Q slot"
               and Q'="cte_wp_at (op = src_cap) src" for Q slot in P_bool_lift' )
    apply (wp set_untyped_cap_as_full_cte_wp_at)
    subgoal by (auto simp: cte_wp_at_caps_of_state is_cap_simps masked_as_full_def cap_bits_untyped_def)
   apply (wp set_untyped_cap_as_full_cte_wp_at_neg)
   apply (auto simp: cte_wp_at_caps_of_state is_cap_simps masked_as_full_def cap_bits_untyped_def)
  done

end
end