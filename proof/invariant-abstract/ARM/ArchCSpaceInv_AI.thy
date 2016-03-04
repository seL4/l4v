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
imports ArchAcc_AI
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
  "is_ap_cap cap \<equiv> case cap of cap.ArchObjectCap (arch_cap.ASIDPoolCap ap asid) \<Rightarrow> True | _ \<Rightarrow> False"


lemmas is_ap_cap_simps [simp] = is_ap_cap_def [split_simps cap.split arch_cap.split]


definition
  "reachable_pg_cap cap \<equiv> \<lambda>s.
   is_pg_cap cap \<and>
   (\<exists>vref. vs_cap_ref cap = Some vref \<and> (vref \<unrhd> the (aobj_ref cap)) s)"

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


lemma only_idle_tcb_update:
  "\<lbrakk>only_idle s; ko_at (TCB t) p s; tcb_state t = tcb_state t' \<or> \<not>idle (tcb_state t') \<rbrakk>
    \<Longrightarrow> only_idle (s\<lparr>kheap := kheap s(p \<mapsto> TCB t')\<rparr>)"
  by (clarsimp simp: only_idle_def pred_tcb_at_def obj_at_def)


lemma tcb_update_global_pd_mappings:
  "\<lbrakk> valid_global_pd_mappings s; ko_at (TCB t) p s \<rbrakk>
       \<Longrightarrow> valid_global_pd_mappings (s\<lparr>kheap := kheap s(p \<mapsto> TCB t')\<rparr>)"
  apply (erule valid_global_pd_mappings_pres)
     apply (clarsimp simp: obj_at_def)+
  done
*)

end
end