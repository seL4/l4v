(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
X64-specific CSpace invariants
*)

theory ArchCSpacePre_AI
imports CSpacePre_AI
begin

context Arch begin arch_global_naming

lemmas typ_at_eq_kheap_obj = typ_at_eq_kheap_obj atyp_at_eq_kheap_obj

lemmas set_cap_atyp_ats[wp] = abs_atyp_at_lifts[OF set_cap_typ_at]

definition
  "final_matters_arch ac \<equiv>
     (case ac of
         ASIDPoolCap r as \<Rightarrow> True
       | ASIDControlCap \<Rightarrow> False
       | IOPortCap first_port last_port \<Rightarrow> True \<comment> \<open>FIXME: stab in the dark.\<close>
       | IOPortControlCap \<Rightarrow> False
       | PageCap dev r rghts maptype sz mapdata \<Rightarrow> False
       | PageTableCap r mapdata \<Rightarrow> True
       | PageDirectoryCap r mapdata \<Rightarrow> True
       | PDPointerTableCap r mapdata \<Rightarrow> True
       | PML4Cap r mapdata \<Rightarrow> True)"

lemma is_page_cap_PageCap[simp]:
  "is_page_cap (PageCap dev ref rghts maptype pgsiz mapdata)"
  by (simp add: is_page_cap_def)

lemma pageBitsForSize_eq[simp]:
  "(pageBitsForSize sz = pageBitsForSize sz') = (sz = sz')"
  by (cases sz; cases sz'; simp add: pageBits_def ptTranslationBits_def)

lemma aobj_ref_cases':
  "aobj_ref acap = (case acap of ASIDControlCap \<Rightarrow> aobj_ref acap
                                | _ \<Rightarrow> aobj_ref acap)"
  by (simp split: arch_cap.split)

lemma aobj_ref_cases:
  "aobj_ref acap =
  (case acap of
    ASIDPoolCap w1 w2 \<Rightarrow> Some w1
  | ASIDControlCap \<Rightarrow> None
  | IOPortCap _ _ \<Rightarrow> None
  | PageCap dev w s mt sz opt \<Rightarrow> Some w
  | PageTableCap w opt \<Rightarrow> Some w
  | PageDirectoryCap w opt \<Rightarrow> Some w
  | PDPointerTableCap w opt \<Rightarrow> Some w
  | PML4Cap w opt \<Rightarrow> Some w
  | IOPortControlCap \<Rightarrow> None)"
  apply (subst aobj_ref_cases')
  apply (clarsimp cong: arch_cap.case_cong)
  done

definition
  "ups_of_heap h \<equiv> \<lambda>p.
   case h p of Some (ArchObj (DataPage dev sz)) \<Rightarrow> Some sz | _ \<Rightarrow> None"

lemma ups_of_heap_typ_at:
  "ups_of_heap (kheap s) p = Some sz \<longleftrightarrow> data_at sz p s"
  by (auto simp: typ_at_eq_kheap_obj ups_of_heap_def data_at_def
          split: option.splits Structures_A.kernel_object.splits
                 arch_kernel_obj.splits)

lemma ups_of_heap_typ_at_def:
  "ups_of_heap (kheap s) \<equiv> \<lambda>p.
   if \<exists>!sz. data_at sz p s
     then Some (THE sz. data_at sz p s)
     else None"
  apply (rule eq_reflection)
  apply (rule ext)
  apply (clarsimp simp: ups_of_heap_typ_at)
  apply (intro conjI impI)
   apply (frule (1) theI')
  apply safe
   apply (fastforce simp: ups_of_heap_typ_at)
  by (auto simp: obj_at_def data_at_def)

lemma ups_of_heap_non_arch_upd:
  "h x = Some ko \<Longrightarrow> non_arch_obj ko \<Longrightarrow> non_arch_obj ko' \<Longrightarrow> ups_of_heap (h(x \<mapsto> ko')) = ups_of_heap h"
  by (rule ext) (auto simp add: ups_of_heap_def non_arch_obj_def split: kernel_object.splits)

crunch lookup_ipc_buffer
  for inv[wp]: "I"

lemma vs_cap_ref_to_table_cap_ref:
  "\<not> is_pg_cap cap \<Longrightarrow> vs_cap_ref cap = table_cap_ref cap"
  by (simp add: is_pg_cap_def table_cap_ref_def vs_cap_ref_simps
         split: cap.splits arch_cap.splits)


lemma cap_master_cap_pg_cap:
 "\<lbrakk>cap_master_cap cap = cap_master_cap cap'\<rbrakk>
  \<Longrightarrow> is_pg_cap cap = is_pg_cap cap'"
  by (clarsimp simp:cap_master_cap_def is_cap_simps
    split:cap.splits arch_cap.splits dest!:cap_master_cap_eqDs)

lemma master_arch_cap_obj_refs:
  "cap_master_arch_cap c = cap_master_arch_cap c' \<Longrightarrow> aobj_ref c = aobj_ref c'"
  by (simp add: cap_master_arch_cap_def split: arch_cap.splits)

lemma master_arch_cap_cap_class:
  "cap_master_arch_cap c = cap_master_arch_cap c' \<Longrightarrow> acap_class c = acap_class c'"
  by (simp add: cap_master_arch_cap_def split: arch_cap.splits)

lemma is_cap_free_index_update[simp]:
  "is_pml4_cap (src_cap\<lparr>free_index := a\<rparr>) = is_pml4_cap src_cap"
  "is_pdpt_cap (src_cap\<lparr>free_index := a\<rparr>) = is_pdpt_cap src_cap"
  "is_pd_cap (src_cap\<lparr>free_index := a\<rparr>) = is_pd_cap src_cap"
  "is_pt_cap (src_cap\<lparr>free_index := a\<rparr>) = is_pt_cap src_cap"
  by (simp add:is_cap_simps free_index_update_def split:cap.splits)+

lemma masked_as_full_test_function_stuff[simp]:
  "is_pml4_cap (masked_as_full a cap) = is_pml4_cap a"
  "is_pdpt_cap (masked_as_full a cap) = is_pdpt_cap a"
  "is_pd_cap (masked_as_full a cap) = is_pd_cap a"
  "is_pt_cap (masked_as_full a cap) = is_pt_cap a"
  "vs_cap_ref (masked_as_full a cap) = vs_cap_ref a"
  by (auto simp:masked_as_full_def)

lemma same_aobject_as_commute:
  "same_aobject_as x y \<Longrightarrow> same_aobject_as y x"
  by (cases x; cases y; clarsimp)

lemmas wellformed_cap_simps = wellformed_cap_def
  [simplified wellformed_acap_def, split_simps cap.split arch_cap.split]

lemma is_vspace_table_Null[simp]:
  "\<not> is_pt_cap NullCap \<and> \<not> is_pd_cap NullCap \<and> \<not> is_pdpt_cap NullCap \<and> \<not> is_pml4_cap NullCap"
  by (simp add: is_pt_cap_def is_pd_cap_def is_pdpt_cap_def is_pml4_cap_def)

lemma unique_table_caps_upd_eqD:
  "\<lbrakk>ms a = Some b; cap_asid b = cap_asid b'; obj_refs b = obj_refs b';
    is_pd_cap b = is_pd_cap b'; is_pt_cap b = is_pt_cap b';
    is_pdpt_cap b = is_pdpt_cap b'; is_pml4_cap b = is_pml4_cap b'\<rbrakk>
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

lemma arch_derived_is_device:
  "\<lbrakk>cap_master_arch_cap c = cap_master_arch_cap c';
        is_derived_arch (ArchObjectCap c) (ArchObjectCap c')\<rbrakk>
       \<Longrightarrow> arch_cap_is_device c' = arch_cap_is_device c"
  apply (case_tac c)
  apply (clarsimp simp: is_derived_arch_def
    cap_range_def is_cap_simps cap_master_cap_def cap_master_arch_cap_def
              split: if_split_asm cap.splits arch_cap.splits)+
  done

lemma valid_arch_mdb_simple:
  "\<And>s capa. \<lbrakk>valid_arch_mdb (is_original_cap s) (caps_of_state s);
              is_simple_cap cap; caps_of_state s src = Some capa\<rbrakk> \<Longrightarrow>
         valid_arch_mdb ((is_original_cap s) (dest := is_cap_revocable cap capa))
                       ((caps_of_state s)(dest \<mapsto> cap))"
  by (auto simp: valid_arch_mdb_def ioport_revocable_def is_cap_revocable_def arch_is_cap_revocable_def
                 is_simple_cap_def safe_parent_for_def is_cap_simps)

lemma free_index_update_irq_revocable[simp]:
  "ms src = Some src_cap \<Longrightarrow>
   ioport_revocable P (ms(src \<mapsto> src_cap\<lparr>free_index:=a\<rparr>)) = ioport_revocable P ms"
  unfolding ioport_revocable_def
  apply (rule iffI)
    apply clarify
    apply (drule_tac x = p in spec)
      apply (case_tac "p = src")
       apply (clarsimp simp:free_index_update_def)+
  apply (simp add: free_index_update_def split:cap.splits)
  done

lemma valid_arch_mdb_free_index_update:
  "\<lbrakk>m src = Some capa;m' = m (src\<mapsto> capa\<lparr>free_index :=x\<rparr>) \<rbrakk> \<Longrightarrow>
   valid_arch_mdb c (m') = valid_arch_mdb c (m)"
  by (clarsimp simp:valid_arch_mdb_def)

lemma set_cap_update_free_index_valid_arch_mdb:
  "\<lbrace>\<lambda>s. valid_arch_mdb (is_original_cap s) (caps_of_state s) \<and> is_untyped_cap src_cap\<rbrace>
         set_cap (free_index_update f src_cap) src
   \<lbrace>\<lambda>rv s. valid_arch_mdb (is_original_cap s) (caps_of_state s)\<rbrace>"
  apply (clarsimp simp: valid_arch_mdb_def)
  apply (rule hoare_pre)
   apply (wps set_cap_rvk_cdt_ct_ms)
  apply wpsimp
  by (clarsimp simp: ioport_revocable_def is_cap_simps free_index_update_def
                 split: cap.splits)

lemma set_untyped_cap_as_full_valid_arch_mdb:
  "\<lbrace>\<lambda>s. valid_arch_mdb (is_original_cap s) (caps_of_state s)\<rbrace>
            set_untyped_cap_as_full src_cap c src
   \<lbrace>\<lambda>rv s. valid_arch_mdb (is_original_cap s) (caps_of_state s)\<rbrace>"
  by (wpsimp wp: set_cap_update_free_index_valid_arch_mdb
           simp: set_untyped_cap_as_full_def)

lemma valid_arch_mdb_not_arch_cap_update:
     "\<And>s cap capa. \<lbrakk>\<not>is_arch_cap cap; valid_arch_mdb (is_original_cap s) (caps_of_state s)\<rbrakk>
       \<Longrightarrow> valid_arch_mdb ((is_original_cap s)(dest := True))
            ((caps_of_state s)(src \<mapsto> cap, dest\<mapsto>capa))"
  by (auto simp: valid_arch_mdb_def ioport_revocable_def is_cap_simps)

lemma valid_arch_mdb_derived_cap_update:
  "\<And>s capa. \<lbrakk>valid_arch_mdb (is_original_cap s) (caps_of_state s);
             is_derived (cdt s) src cap capa\<rbrakk> \<Longrightarrow>
           valid_arch_mdb ((is_original_cap s)(dest := is_cap_revocable cap capa))
                           ((caps_of_state s)(dest \<mapsto> cap))"
  apply (clarsimp simp: valid_arch_mdb_def ioport_revocable_def is_cap_simps is_cap_revocable_def
                        arch_is_cap_revocable_def)
  by (clarsimp simp: is_derived_def is_cap_simps is_derived_arch_def split: if_split_asm)

lemma valid_arch_mdb_free_index_update':
  "\<And>s capa. \<lbrakk>valid_arch_mdb (is_original_cap s) (caps_of_state s); caps_of_state s src = Some capa;
                   is_untyped_cap cap\<rbrakk> \<Longrightarrow>
           valid_arch_mdb ((is_original_cap s) (dest := is_cap_revocable cap capa))
            ((caps_of_state s)(dest \<mapsto> cap, src \<mapsto> max_free_index_update capa))"
  by (auto simp: valid_arch_mdb_def ioport_revocable_def is_cap_simps is_cap_revocable_def
                        arch_is_cap_revocable_def free_index_update_def split: cap.splits)

lemma weak_derived_IOPortControl[simp]:
  "weak_derived (ArchObjectCap IOPortControlCap) cap \<Longrightarrow>
         cap = ArchObjectCap IOPortControlCap"
  by (clarsimp simp: weak_derived_def copy_of_def same_object_as_def is_cap_simps
              split: if_split_asm cap.splits arch_cap.splits)

lemma valid_arch_mdb_weak_derived_update:
  "\<And>s capa. \<lbrakk>valid_arch_mdb (is_original_cap s) (caps_of_state s);
                      caps_of_state s src = Some capa; weak_derived cap capa\<rbrakk> \<Longrightarrow>
        valid_arch_mdb ((is_original_cap s) (dest := is_original_cap s src, src := False))
            ((caps_of_state s)(dest \<mapsto> cap, src \<mapsto> NullCap))"
  by (auto simp: valid_arch_mdb_def ioport_revocable_def
          split: if_split_asm
       simp del: split_paired_All)

lemma valid_arch_mdb_tcb_cnode_update:
  "valid_arch_mdb (is_original_cap s) (caps_of_state s) \<Longrightarrow>
           valid_arch_mdb ((is_original_cap s) ((t, tcb_cnode_index 2) := True))
              ((caps_of_state s)((t, tcb_cnode_index 2) \<mapsto> ReplyCap t True canReplyGrant))"
  by (clarsimp simp: valid_arch_mdb_def ioport_revocable_def)

lemmas valid_arch_mdb_updates = valid_arch_mdb_free_index_update valid_arch_mdb_not_arch_cap_update
                                valid_arch_mdb_derived_cap_update valid_arch_mdb_free_index_update'
                                valid_arch_mdb_weak_derived_update valid_arch_mdb_tcb_cnode_update

lemma safe_parent_for_arch_not_arch':
  "\<not>is_arch_cap cap \<Longrightarrow> \<not>safe_parent_for_arch c cap"
  by (clarsimp simp: safe_parent_for_arch_def is_cap_simps)

lemma ioport_revocableD:
  "\<lbrakk> cs p = Some (ArchObjectCap IOPortControlCap); ioport_revocable (is_original_cap s) cs \<rbrakk> \<Longrightarrow> is_original_cap s p"
  by (fastforce simp add: ioport_revocable_def simp del: split_paired_All)

lemma safe_parent_arch_is_parent:
  "\<lbrakk>safe_parent_for_arch cap pcap; caps_of_state s p = Some pcap;
      valid_arch_mdb (is_original_cap s) (caps_of_state s)\<rbrakk> \<Longrightarrow>
    should_be_parent_of pcap (is_original_cap s p) cap f"
  apply (clarsimp simp: should_be_parent_of_def safe_parent_for_arch_def valid_arch_mdb_def)
  by (erule (1) ioport_revocableD)

lemma safe_parent_for_arch_no_obj_refs:
  "safe_parent_for_arch cap c \<Longrightarrow> obj_refs cap = {}"
  by (clarsimp simp: safe_parent_for_arch_def)

lemma valid_arch_mdb_same_master_cap:
  "\<lbrakk>valid_arch_mdb ioc cs; cs sl = Some cap; cap_master_cap cap' = cap_master_cap cap\<rbrakk> \<Longrightarrow>
  valid_arch_mdb ioc (cs(sl\<mapsto>cap'))"
  by (clarsimp simp: valid_arch_mdb_def ioport_revocable_def cap_master_cap_def
              split: cap.split_asm arch_cap.split_asm)

lemma valid_arch_mdb_null_filter:
  "valid_arch_mdb (is_original_cap s) (null_filter (caps_of_state s)) = valid_arch_mdb (is_original_cap s) (caps_of_state s)"
  apply (clarsimp simp: null_filter_def valid_arch_mdb_def ioport_revocable_def)
  by auto

lemma valid_arch_mdb_untypeds:
  "\<And>s. valid_arch_mdb (is_original_cap s) (caps_of_state s)
       \<Longrightarrow> valid_arch_mdb (\<lambda>x. x \<noteq> cref \<longrightarrow> is_original_cap s x)
            ((caps_of_state s)(cref \<mapsto> default_cap tp oref sz dev))"
  "\<And>s. valid_arch_mdb (is_original_cap s) (caps_of_state s)
       \<Longrightarrow> valid_arch_mdb (is_original_cap s)
            ((caps_of_state s)(cref \<mapsto> UntypedCap dev ptr sz idx))"
  by (clarsimp simp: valid_arch_mdb_def ioport_revocable_def)+

lemma same_object_as_ioports:
  "same_object_as c c' \<Longrightarrow> cap_ioports c = cap_ioports c'"
  by (clarsimp simp: same_object_as_def is_cap_simps cap_ioports_def split: cap.splits arch_cap.splits)

lemma copy_of_ioports:
  "copy_of c c' \<Longrightarrow> cap_ioports c = cap_ioports c'"
  by (clarsimp simp: copy_of_def same_object_as_ioports split: if_split_asm)

lemma weak_derived_cap_ioports:
  "weak_derived c c' \<Longrightarrow> cap_ioports c = cap_ioports c'"
  by (auto simp : weak_derived_def copy_of_ioports)

end
end
