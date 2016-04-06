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
CSpace invariants
*)

theory ArchCSpaceInv_AI
imports "../CSpaceInvPre_AI"
begin
context ARM begin

lemma aobj_ref_acap_rights_update[simp]:
  "aobj_ref (acap_rights_update f x) = aobj_ref x"
  by (cases x; simp add: acap_rights_update_def)

lemma arch_obj_size_acap_rights_update[simp]:
  "arch_obj_size (acap_rights_update f x) = arch_obj_size x"
  by (cases x; simp add: acap_rights_update_def)

lemma valid_arch_cap_acap_rights_update[intro]:
  "valid_arch_cap x s \<Longrightarrow> valid_arch_cap (acap_rights_update f x) s"
  by (cases x; simp add: acap_rights_update_def valid_arch_cap_def)

definition
  cap_master_arch_cap where
  "cap_master_arch_cap acap \<equiv>
     (case acap of
           arch_cap.PageCap ref rghts sz mapdata \<Rightarrow>
              arch_cap.PageCap ref UNIV sz None
         | arch_cap.ASIDPoolCap pool asid \<Rightarrow>
              arch_cap.ASIDPoolCap pool 0
         | arch_cap.PageTableCap ptr data \<Rightarrow>
              arch_cap.PageTableCap ptr None
         | arch_cap.PageDirectoryCap ptr data \<Rightarrow>
              arch_cap.PageDirectoryCap ptr None
         | _ \<Rightarrow> acap)"
lemma
  cap_master_arch_cap_eqDs1:
  "cap_master_arch_cap cap =  (arch_cap.PageCap ref rghts sz mapdata)
     \<Longrightarrow> rghts = UNIV \<and> mapdata = None
          \<and> (\<exists>rghts mapdata. cap =  (arch_cap.PageCap ref rghts sz mapdata))"
  "cap_master_arch_cap cap =  arch_cap.ASIDControlCap
     \<Longrightarrow> cap =  arch_cap.ASIDControlCap"
  "cap_master_arch_cap cap =  (arch_cap.ASIDPoolCap pool asid)
     \<Longrightarrow> asid = 0 \<and> (\<exists>asid. cap =  (arch_cap.ASIDPoolCap pool asid))"
  "cap_master_arch_cap cap =  (arch_cap.PageTableCap ptr data)
     \<Longrightarrow> data = None \<and> (\<exists>data. cap =  (arch_cap.PageTableCap ptr data))"
  "cap_master_arch_cap cap =  (arch_cap.PageDirectoryCap ptr data2)
     \<Longrightarrow> data2 = None \<and> (\<exists>data2. cap =  (arch_cap.PageDirectoryCap ptr data2))"
  by (clarsimp simp: cap_master_arch_cap_def
             split: arch_cap.split_asm)+

lemma
  cap_master_arch_inv:
  "cap_master_arch_cap (cap_master_arch_cap ac) = cap_master_arch_cap ac"
  by (cases ac; simp add: cap_master_arch_cap_def)

(* FIXME: move to somewhere sensible *)
lemma pageBitsForSize_simps[simp]:
  "pageBitsForSize ARMSmallPage    = 12"
  "pageBitsForSize ARMLargePage    = 16"
  "pageBitsForSize ARMSection      = 20"
  "pageBitsForSize ARMSuperSection = 24"
  by (simp add: pageBitsForSize_def)+

definition
  "is_ap_cap cap \<equiv> case cap of (ArchObjectCap (arch_cap.ASIDPoolCap ap asid)) \<Rightarrow> True | _ \<Rightarrow> False"

lemmas is_ap_cap_simps [simp] = is_ap_cap_def [split_simps cap.split arch_cap.split]

definition
  "reachable_pg_cap cap \<equiv> \<lambda>s.
   is_pg_cap cap \<and>
   (\<exists>vref. vs_cap_ref cap = Some vref \<and> (vref \<unrhd> obj_ref_of cap) s)"


(*FIXME arch_split: These are probably subsumed by the lifting lemmas *)

(*
lemma valid_arch_obj_tcb_update':
  "\<lbrakk> valid_arch_obj obj s; kheap s p = Some (TCB t) \<rbrakk>
   \<Longrightarrow> valid_arch_obj obj (s\<lparr>kheap := kheap s(p \<mapsto> TCB t')\<rparr>)"
  apply (cases obj)
     apply (fastforce elim: typ_at_same_type [rotated -1])
    apply clarsimp
    apply (rename_tac "fun" x)
    apply (erule_tac x=x in allE)
    apply (case_tac "fun x", (clarsimp simp: obj_at_def)+)[1]
   apply clarsimp
   apply (rename_tac "fun" x)
   apply (erule_tac x=x in ballE)
   apply (case_tac "fun x", (clarsimp simp: obj_at_def)+)[1]
   apply (fastforce elim: typ_at_same_type [rotated -1])
  apply simp
  done


lemma valid_arch_obj_tcb_update:
  "kheap s p = Some (TCB t)
   \<Longrightarrow> valid_arch_obj obj (s\<lparr>kheap := kheap s(p \<mapsto> TCB t')\<rparr>) = valid_arch_obj obj s"
  apply (rule iffI)
   apply (drule valid_arch_obj_tcb_update'[where p=p and t'=t], simp)
   apply (simp add: fun_upd_idem)
  apply (erule(1) valid_arch_obj_tcb_update')
  done


lemma valid_arch_objs_tcb_update:
  "\<lbrakk> valid_arch_objs s; kheap s p = Some (TCB t)\<rbrakk>
    \<Longrightarrow> valid_arch_objs (s\<lparr>kheap := kheap s(p \<mapsto> TCB t')\<rparr>)"
  apply (erule valid_arch_objs_stateI)
    apply (clarsimp simp: obj_at_def vs_refs_def split: split_if_asm)
   apply simp
  apply (clarsimp simp: obj_at_def valid_arch_obj_tcb_update split: split_if_asm)
  done


lemma vs_lookup1_tcb_update:
  "kheap s p = Some (TCB t)
      \<Longrightarrow> vs_lookup1 (s\<lparr>kheap := kheap s(p \<mapsto> TCB t')\<rparr>) = vs_lookup1 s"
  by (clarsimp simp add: vs_lookup1_def obj_at_def vs_refs_def intro!: set_eqI)


lemma vs_lookup_tcb_update:
  "kheap s p = Some (TCB t)
      \<Longrightarrow> vs_lookup (s\<lparr>kheap := kheap s(p \<mapsto> TCB t')\<rparr>) = vs_lookup s"
  by (clarsimp simp add: vs_lookup_def vs_lookup1_tcb_update)





lemma tcb_update_global_pd_mappings:
  "\<lbrakk> valid_global_pd_mappings s; ko_at (TCB t) p s \<rbrakk>
       \<Longrightarrow> valid_global_pd_mappings (s\<lparr>kheap := kheap s(p \<mapsto> TCB t')\<rparr>)"
  apply (erule valid_global_pd_mappings_pres)
     apply (clarsimp simp: obj_at_def)+
  done
*)

lemma unique_table_refsD:
  "\<lbrakk> unique_table_refs cps; cps p = Some cap; cps p' = Some cap';
     obj_refs cap = obj_refs cap'\<rbrakk>
     \<Longrightarrow> table_cap_ref cap = table_cap_ref cap'"
  unfolding unique_table_refs_def
  by blast

lemma table_cap_ref_vs_cap_ref_Some:
  "table_cap_ref x = Some y \<Longrightarrow> vs_cap_ref x = Some y"
  by (clarsimp simp: table_cap_ref_def vs_cap_ref_def 
                 split: cap.splits arch_cap.splits)

lemma set_cap_valid_vs_lookup:
  "\<lbrace>\<lambda>s. valid_vs_lookup s
      \<and> (\<forall>vref cap'. cte_wp_at (op = cap') ptr s
                \<longrightarrow> vs_cap_ref cap' = Some vref
                \<longrightarrow> (vs_cap_ref cap = Some vref \<and> obj_refs cap = obj_refs cap')
                 \<or> (\<not> is_final_cap' cap' s \<and> \<not> reachable_pg_cap cap' s)
                 \<or> (\<forall>oref. oref \<in> obj_refs cap' \<longrightarrow> \<not> (vref \<unrhd> oref) s))
      \<and> unique_table_refs (caps_of_state s)\<rbrace>
     set_cap cap ptr
   \<lbrace>\<lambda>rv. valid_vs_lookup\<rbrace>"
  apply (simp add: valid_vs_lookup_def
              del: split_paired_All split_paired_Ex)
  apply (rule hoare_pre)
   apply (wp hoare_vcg_all_lift hoare_convert_imp[OF set_cap.vs_lookup_pages]
             hoare_vcg_disj_lift)
  apply (elim conjE allEI, rule impI, drule(1) mp)
  apply (simp only: simp_thms)
  apply (elim exE conjE)
  apply (case_tac "p' = ptr")
   apply (clarsimp simp: cte_wp_at_caps_of_state)
   apply (elim disjE impCE)
     apply fastforce
    apply clarsimp
    apply (drule (1) not_final_another_caps)
     apply (erule obj_ref_is_obj_irq_ref)
    apply (simp, elim exEI, clarsimp simp: obj_irq_refs_eq)
    apply (rule conjI, clarsimp)
    apply (drule(3) unique_table_refsD)
    apply (clarsimp simp: reachable_pg_cap_def is_pg_cap_def)
    apply (case_tac cap, simp_all add: vs_cap_ref_simps)[1]
    apply (rename_tac arch_cap)
    apply (case_tac arch_cap,
           simp_all add: vs_cap_ref_simps table_cap_ref_simps)[1]
       apply (clarsimp dest!: table_cap_ref_vs_cap_ref_Some)
      apply fastforce
     apply (clarsimp dest!: table_cap_ref_vs_cap_ref_Some)+
  apply (auto simp: cte_wp_at_caps_of_state)[1]
  done

crunch arch[wp]: set_cap "\<lambda>s. P (arch_state s)" (simp: split_def)

lemma set_cap_valid_table_caps:
  "\<lbrace>\<lambda>s. valid_table_caps s
         \<and> ((is_pt_cap cap \<or> is_pd_cap cap) \<longrightarrow> cap_asid cap = None
            \<longrightarrow> (\<forall>r \<in> obj_refs cap. obj_at (empty_table (set (arm_global_pts (arch_state s)))) r s))\<rbrace>
     set_cap cap ptr
   \<lbrace>\<lambda>rv. valid_table_caps\<rbrace>"
  apply (simp add: valid_table_caps_def)
  apply (wp hoare_vcg_all_lift
            hoare_vcg_disj_lift hoare_convert_imp[OF set_cap_caps_of_state]
            hoare_use_eq[OF set_cap_arch set_cap_obj_at_impossible])
  apply (simp add: empty_table_caps_of)
  done

lemma set_cap_unique_table_caps:
  "\<lbrace>\<lambda>s. unique_table_caps (caps_of_state s)
      \<and> ((is_pt_cap cap \<or> is_pd_cap cap)
             \<longrightarrow> (\<forall>oldcap. caps_of_state s ptr = Some oldcap \<longrightarrow>
                  (is_pt_cap cap \<and> is_pt_cap oldcap \<or> is_pd_cap cap \<and> is_pd_cap oldcap)
                    \<longrightarrow> (cap_asid cap = None \<longrightarrow> cap_asid oldcap = None)
                    \<longrightarrow> obj_refs oldcap \<noteq> obj_refs cap)
             \<longrightarrow> (\<forall>ptr'. cte_wp_at (\<lambda>cap'. obj_refs cap' = obj_refs cap
                                              \<and> (is_pd_cap cap \<and> is_pd_cap cap' \<or> is_pt_cap cap \<and> is_pt_cap cap')
                                              \<and> (cap_asid cap = None \<or> cap_asid cap' = None)) ptr' s \<longrightarrow> ptr' = ptr))\<rbrace>
     set_cap cap ptr
   \<lbrace>\<lambda>rv s. unique_table_caps (caps_of_state s)\<rbrace>"
  apply wp
  apply (simp only: unique_table_caps_def)
  apply (elim conjE)
  apply (erule impCE)
   apply clarsimp
  apply (erule impCE)
   prefer 2
   apply (simp del: imp_disjL)
   apply (thin_tac "\<forall>a b. P a b" for P)
   apply (auto simp: cte_wp_at_caps_of_state)[1]
  apply (clarsimp simp del: imp_disjL del: allI)
  apply (case_tac "cap_asid cap \<noteq> None")
   apply (clarsimp del: allI)
   apply (elim allEI | rule impI)+
   apply (auto simp: is_pt_cap_def is_pd_cap_def)[1]
  apply (elim allEI)
  apply (intro conjI impI)
   apply (elim allEI)
   apply (auto simp: is_pt_cap_def is_pd_cap_def)[1]
  apply (elim allEI)
  apply (auto simp: is_pt_cap_def is_pd_cap_def)[1]
  done

lemma set_cap_unique_table_refs:
  "\<lbrace>\<lambda>s. unique_table_refs (caps_of_state s)
      \<and> no_cap_to_obj_with_diff_ref cap {ptr} s\<rbrace>
     set_cap cap ptr
   \<lbrace>\<lambda>rv s. unique_table_refs (caps_of_state s)\<rbrace>"
  apply wp
  apply clarsimp
  apply (simp add: unique_table_refs_def
              split del: split_if del: split_paired_All)
  apply (erule allEI, erule allEI)
  apply (clarsimp split del: split_if)
  apply (clarsimp simp: no_cap_to_obj_with_diff_ref_def
                        cte_wp_at_caps_of_state
                 split: split_if_asm)
  done

definition set_arch_cap_precondition where
  "set_arch_cap_precondition cap ptr s \<equiv>
        (\<forall>vref cap'. cte_wp_at (op = cap') ptr s
                \<longrightarrow> vs_cap_ref cap' = Some vref
                \<longrightarrow> (vs_cap_ref cap = Some vref \<and> obj_refs cap = obj_refs cap')
                 \<or> (\<not> is_final_cap' cap' s \<and> \<not> reachable_pg_cap cap' s)
                 \<or> (\<forall>oref \<in> obj_refs cap'. \<not> (vref \<unrhd> oref) s))
      \<and> no_cap_to_obj_with_diff_ref cap {ptr} s
      \<and> ((is_pt_cap cap \<or> is_pd_cap cap) \<longrightarrow> cap_asid cap = None
            \<longrightarrow> (\<forall>r \<in> obj_refs cap. obj_at (empty_table (set (arm_global_pts (arch_state s)))) r s))
      \<and> ((is_pt_cap cap \<or> is_pd_cap cap)
             \<longrightarrow> (\<forall>oldcap. caps_of_state s ptr = Some oldcap \<longrightarrow>
                  (is_pt_cap cap \<and> is_pt_cap oldcap \<or> is_pd_cap cap \<and> is_pd_cap oldcap)
                    \<longrightarrow> (cap_asid cap = None \<longrightarrow> cap_asid oldcap = None)
                    \<longrightarrow> obj_refs oldcap \<noteq> obj_refs cap)
             \<longrightarrow> (\<forall>ptr'. cte_wp_at (\<lambda>cap'. obj_refs cap' = obj_refs cap
                                              \<and> (is_pd_cap cap \<and> is_pd_cap cap' \<or> is_pt_cap cap \<and> is_pt_cap cap')
                                              \<and> (cap_asid cap = None \<or> cap_asid cap' = None)) ptr' s \<longrightarrow> ptr' = ptr))"

lemma not_arch_not_pt[simp]:
  "\<not> is_arch_cap cap \<Longrightarrow> \<not> is_pt_cap cap"
  unfolding is_arch_cap_def is_pt_cap_def
  by (auto split: cap.splits arch_cap.splits)

lemma not_arch_not_pd[simp]:
  "\<not> is_arch_cap cap \<Longrightarrow> \<not> is_pd_cap cap"
  unfolding is_arch_cap_def is_pd_cap_def
  by (auto split: cap.splits arch_cap.splits)

lemma not_arch_not_reachable_pg[simp]:
  "\<not> is_arch_cap cap \<Longrightarrow> \<not> reachable_pg_cap cap s"
  unfolding is_arch_cap_def reachable_pg_cap_def is_pg_cap_def
  by (auto split: cap.splits arch_cap.splits)

(*
lemma set_cap_valid_arch_caps:
  "\<lbrace>\<lambda>s. valid_arch_caps s
      \<and> (if (\<not>is_arch_cap cap) \<and> (\<forall>cap'. cte_wp_at (op = cap') ptr s \<longrightarrow> \<not>is_arch_cap cap') then  
         ((\<forall>cap'. cte_wp_at (op = cap') ptr s \<longrightarrow> \<not>is_final_cap' cap' s) \<and> no_cap_to_obj_with_diff_ref cap {ptr} s)
         else set_arch_cap_precondition cap ptr s) \<rbrace>
        set_cap cap ptr
   \<lbrace>\<lambda>rv. valid_arch_caps\<rbrace>"
(*
  apply (simp add: valid_arch_caps_def pred_conj_def split del: split_if)
  apply (wp set_cap_valid_vs_lookup set_cap_valid_table_caps
              set_cap_unique_table_caps set_cap_unique_table_refs)
  apply (clarsimp simp: set_arch_cap_precondition_def split: split_if_asm)
  apply (clarsimp simp: set_arch_cap_precondition_def split: split_if_asm)
  apply (clarsimp simp: set_arch_cap_precondition_def split: split_if_asm)
  apply (clarsimp split: split_if_asm)
  apply (clarsimp split: split_if_asm)
  apply (clarsimp split: split_if_asm)
  apply (clarsimp split: split_if_asm)
  apply (elim disjE; simp?)
  apply blas
  apply (clarsimp simp: not_arch_not_pt not_arch_not_pd)
  apply safe
  apply clarsimp
  apply (simp add: cte_wp_at_caps_of_state)
  apply (case_tac "caps_of_state s ptr"; simp)
  done*) sorry*)

lemma set_cap_valid_arch_caps:
  "\<lbrace>\<lambda>s. valid_arch_caps s
      \<and> (\<forall>vref cap'. cte_wp_at (op = cap') ptr s
                \<longrightarrow> vs_cap_ref cap' = Some vref
                \<longrightarrow> (vs_cap_ref cap = Some vref \<and> obj_refs cap = obj_refs cap')
                 \<or> (\<not> is_final_cap' cap' s \<and> \<not> reachable_pg_cap cap' s)
                 \<or> (\<forall>oref \<in> obj_refs cap'. \<not> (vref \<unrhd> oref) s))
      \<and> no_cap_to_obj_with_diff_ref cap {ptr} s
      \<and> ((is_pt_cap cap \<or> is_pd_cap cap) \<longrightarrow> cap_asid cap = None
            \<longrightarrow> (\<forall>r \<in> obj_refs cap. obj_at (empty_table (set (arm_global_pts (arch_state s)))) r s))
      \<and> ((is_pt_cap cap \<or> is_pd_cap cap)
             \<longrightarrow> (\<forall>oldcap. caps_of_state s ptr = Some oldcap \<longrightarrow>
                  (is_pt_cap cap \<and> is_pt_cap oldcap \<or> is_pd_cap cap \<and> is_pd_cap oldcap)
                    \<longrightarrow> (cap_asid cap = None \<longrightarrow> cap_asid oldcap = None)
                    \<longrightarrow> obj_refs oldcap \<noteq> obj_refs cap)
             \<longrightarrow> (\<forall>ptr'. cte_wp_at (\<lambda>cap'. obj_refs cap' = obj_refs cap
                                              \<and> (is_pd_cap cap \<and> is_pd_cap cap' \<or> is_pt_cap cap \<and> is_pt_cap cap')
                                              \<and> (cap_asid cap = None \<or> cap_asid cap' = None)) ptr' s \<longrightarrow> ptr' = ptr))\<rbrace>
     set_cap cap ptr
   \<lbrace>\<lambda>rv. valid_arch_caps\<rbrace>"
   sorry

lemma valid_table_capsD:
  "\<lbrakk> cte_wp_at (op = cap) ptr s; valid_table_caps s;
        is_pt_cap cap | is_pd_cap cap; cap_asid cap = None \<rbrakk>
        \<Longrightarrow> \<forall>r \<in> obj_refs cap. obj_at (empty_table (set (arm_global_pts (arch_state s)))) r s"
  apply (clarsimp simp: cte_wp_at_caps_of_state valid_table_caps_def)
  apply (cases ptr, fastforce)
  done

lemma unique_table_capsD:
  "\<lbrakk> unique_table_caps cps; cps ptr = Some cap; cps ptr' = Some cap';
     obj_refs cap = obj_refs cap'; cap_asid cap = None \<or> cap_asid cap' = None;
     (is_pd_cap cap \<and> is_pd_cap cap') \<or> (is_pt_cap cap \<and> is_pt_cap cap') \<rbrakk>
     \<Longrightarrow> ptr = ptr'"
  unfolding unique_table_caps_def
  by blast

lemma set_cap_cap_refs_in_kernel_window[wp]:
  "\<lbrace>cap_refs_in_kernel_window
         and (\<lambda>s. \<forall>ref \<in> cap_range cap. arm_kernel_vspace (arch_state s) ref
                         = ArmVSpaceKernelWindow)\<rbrace>
     set_cap cap p
   \<lbrace>\<lambda>rv. cap_refs_in_kernel_window\<rbrace>"
  apply (simp add: cap_refs_in_kernel_window_def valid_refs_def2
                   pred_conj_def)
  apply (rule hoare_lift_Pf2[where f=arch_state])
   apply wp
   apply (fastforce simp: not_kernel_window_arch_def elim!: ranE split: split_if_asm)
  apply wp
  done

lemma cap_refs_in_kernel_windowD:
  "\<lbrakk> caps_of_state s ptr = Some cap; cap_refs_in_kernel_window s \<rbrakk>
   \<Longrightarrow> \<forall>ref \<in> cap_range cap.
         arm_kernel_vspace (arch_state s) ref = ArmVSpaceKernelWindow"
  apply (clarsimp simp: cap_refs_in_kernel_window_def valid_refs_def not_kernel_window_arch_def
                        cte_wp_at_caps_of_state)
  apply (cases ptr, fastforce)
  done

lemma valid_cap_imp_valid_vm_rights:
  "valid_cap (cap.ArchObjectCap (PageCap mw rs sz m)) s \<Longrightarrow>
   rs \<in> valid_vm_rights"
by (simp add: valid_cap_def valid_vm_rights_def)

lemma acap_rights_update_idem [simp]:
  "acap_rights_update R (acap_rights_update R' cap) = acap_rights_update R cap"
  by (simp add: acap_rights_update_def split: arch_cap.splits)

lemma cap_master_arch_cap_rights [simp]:
  "cap_master_arch_cap (acap_rights_update R cap) = cap_master_arch_cap cap"
  by (simp add: cap_master_arch_cap_def acap_rights_update_def 
           split: arch_cap.splits)

lemma acap_rights_update_id [intro!, simp]:
  "valid_arch_cap ac s \<Longrightarrow> acap_rights_update (acap_rights ac) ac = ac"
  unfolding acap_rights_update_def acap_rights_def valid_arch_cap_def
  by (cases ac; simp)

end
end