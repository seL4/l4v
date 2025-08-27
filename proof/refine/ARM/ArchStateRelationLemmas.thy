(*
 * Copyright 2014, General Dynamics C4 Systems
 * Copyright 2025, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
   Arch-specific lemmas related to the refinement relation between abstract and concrete states
*)

theory ArchStateRelationLemmas
imports StateRelation
begin

context Arch begin arch_global_naming

named_theorems StateRelation_R_assms

lemma obj_relation_cuts_def2:
  "obj_relation_cuts ko x =
   (case ko of CNode sz cs \<Rightarrow> if well_formed_cnode_n sz cs
                             then {(cte_map (x, y), cte_relation y) | y. y \<in> dom cs}
                             else {(x, \<bottom>\<bottom>)}
             | TCB tcb \<Rightarrow> {(x, tcb_relation_cut)}
             | ArchObj (PageTable pt) \<Rightarrow> (\<lambda>y. (x + (ucast y << 2), pte_relation y))
                                           ` (UNIV :: word8 set)
             | ArchObj (PageDirectory pd) \<Rightarrow> (\<lambda>y. (x + (ucast y << 2), pde_relation y))
                                           ` (UNIV :: 12 word set)
             | ArchObj (DataPage dev sz)      \<Rightarrow>
                 {(x + n * 2 ^ pageBits,  \<lambda>_ obj. obj =(if dev then KOUserDataDevice else KOUserData)) | n . n < 2 ^ (pageBitsForSize sz - pageBits) }
             | ArchObj _ \<Rightarrow> {(x, other_aobj_relation)}
             | _ \<Rightarrow> {(x, other_obj_relation)})"
  by (simp split: Structures_A.kernel_object.split
                  ARM_A.arch_kernel_obj.split)


lemma obj_relation_cuts_def3:
  "obj_relation_cuts ko x =
  (case (a_type ko) of
     ACapTable n \<Rightarrow> {(cte_map (x, y), cte_relation y) | y. length y = n}
   | ATCB \<Rightarrow> {(x, tcb_relation_cut)}
   | AArch APageTable \<Rightarrow> (\<lambda>y. (x + (ucast y << 2), pte_relation y))
                            ` (UNIV :: word8 set)
   | AArch APageDirectory \<Rightarrow> (\<lambda>y. (x + (ucast y << 2), pde_relation y))
                            ` (UNIV :: 12 word set)
   | AArch (AUserData sz)  \<Rightarrow> {(x + n * 2 ^ pageBits, \<lambda>_ obj. obj = KOUserData) | n . n < 2 ^ (pageBitsForSize sz - pageBits) }
   | AArch (ADeviceData sz)  \<Rightarrow> {(x + n * 2 ^ pageBits, \<lambda>_ obj. obj = KOUserDataDevice ) | n . n < 2 ^ (pageBitsForSize sz - pageBits) }
   | AArch _ \<Rightarrow> {(x, other_aobj_relation)}
   | AGarbage _ \<Rightarrow> {(x, \<bottom>\<bottom>)}
   | _ \<Rightarrow> {(x, other_obj_relation)})"
  apply (simp add: obj_relation_cuts_def2 a_type_def
            split: Structures_A.kernel_object.split
                  ARM_A.arch_kernel_obj.split)
  apply (clarsimp simp: well_formed_cnode_n_def length_set_helper)
  done

(* FIXME arch-split: split off generic? *)
lemma obj_relation_cutsE:
  "\<lbrakk> (y, P) \<in> obj_relation_cuts ko x; P ko ko';
     \<And>sz cs z cap cte. \<lbrakk> ko = CNode sz cs; well_formed_cnode_n sz cs; y = cte_map (x, z);
                      ko' = KOCTE cte; cs z = Some cap; cap_relation cap (cteCap cte) \<rbrakk>
              \<Longrightarrow> R;
     \<And>tcb tcb'. \<lbrakk> y = x; ko = TCB tcb; ko' = KOTCB tcb'; tcb_relation tcb tcb' \<rbrakk>
               \<Longrightarrow> R;
     \<And>pt (z :: word8) pte'. \<lbrakk> ko = ArchObj (PageTable pt); y = x + (ucast z << 2);
                              ko' = KOArch (KOPTE pte'); pte_relation_aligned z (pt z) pte' \<rbrakk>
              \<Longrightarrow> R;
     \<And>pd (z :: 12 word) pde'. \<lbrakk> ko = ArchObj (PageDirectory pd); y = x + (ucast z << 2);
                              ko' = KOArch (KOPDE pde'); pde_relation_aligned z (pd z) pde' \<rbrakk>
              \<Longrightarrow> R;
     \<And>sz dev n. \<lbrakk> ko = ArchObj (DataPage dev sz); ko' = (if dev then KOUserDataDevice else KOUserData);
              y = x + n * 2 ^ pageBits; n < 2 ^ (pageBitsForSize sz - pageBits) \<rbrakk> \<Longrightarrow> R;
     \<And>ako. \<lbrakk> ko \<noteq> ArchObj ako; y = x; other_obj_relation ko ko'; is_other_obj_relation_type (a_type ko) \<rbrakk> \<Longrightarrow> R;
     \<And>ako. \<lbrakk> ko = ArchObj ako; y = x; other_aobj_relation ko ko'; is_other_obj_relation_type (a_type ko) \<rbrakk> \<Longrightarrow> R
    \<rbrakk> \<Longrightarrow> R"
  apply (simp add: obj_relation_cuts_def2 is_other_obj_relation_type_def tcb_relation_cut_def
                   a_type_def
            split: Structures_A.kernel_object.split_asm if_split_asm
                   ARM_A.arch_kernel_obj.split_asm kernel_object.splits)
      apply ((clarsimp split: if_splits,
              force simp: cte_relation_def pte_relation_def pde_relation_def)+)[5]
  done

lemma is_other_obj_relation_type_gen[simp, StateRelation_R_assms]:
  "\<And>n. \<not> is_other_obj_relation_type (ACapTable n)"
  "\<not> is_other_obj_relation_type ATCB"
  "is_other_obj_relation_type AEndpoint"
  "is_other_obj_relation_type ANTFN"
  "\<And>n. \<not> is_other_obj_relation_type (AGarbage n)"
  by (auto simp: is_other_obj_relation_type_def)

lemma is_other_obj_relation_type_PageTable:
  "\<not> is_other_obj_relation_type (AArch APageTable)"
  unfolding is_other_obj_relation_type_def by simp

lemma is_other_obj_relation_type_UserData:
  "\<not> is_other_obj_relation_type (AArch (AUserData sz))"
  unfolding is_other_obj_relation_type_def by simp

lemma is_other_obj_relation_type_DeviceData:
  "\<not> is_other_obj_relation_type (AArch (ADeviceData sz))"
  unfolding is_other_obj_relation_type_def by simp

lemma cap_relation_case':
  "cap_relation cap cap' = (case cap of
                              cap.ArchObjectCap arch_cap.ASIDControlCap \<Rightarrow> cap_relation cap cap'
                            | _ \<Rightarrow> cap_relation cap cap')"
  by (simp split: cap.split arch_cap.split)

schematic_goal cap_relation_case:
  "cap_relation cap cap' = ?P"
  apply (subst cap_relation_case')
  apply (clarsimp cong: cap.case_cong arch_cap.case_cong)
  apply (rule refl)
  done

lemmas cap_relation_split =
  eq_trans_helper[where P=P, OF cap_relation_case cap.split[where P=P]] for P
lemmas cap_relation_split_asm =
  eq_trans_helper[where P=P, OF cap_relation_case cap.split_asm[where P=P]] for P

lemma ghost_relation_typ_at:
  "ghost_relation (kheap s) ups cns \<equiv>
   (\<forall>a sz. data_at sz a s = (ups a = Some sz)) \<and>
   (\<forall>a n. typ_at (ACapTable n) a s = (cns a = Some n))"
   apply (rule eq_reflection)
   apply (clarsimp simp: ghost_relation_def typ_at_eq_kheap_obj data_at_def)
   apply (intro conjI impI iffI allI; force)
   done

(* FIXME arch-split: extension of gen_isCap_defs *)
lemmas isCap_defs =
  isZombie_def isArchObjectCap_def
  isThreadCap_def isCNodeCap_def isNotificationCap_def
  isEndpointCap_def isUntypedCap_def isNullCap_def
  isIRQHandlerCap_def isIRQControlCap_def isReplyCap_def
  isPageCap_def isPageTableCap_def isPageDirectoryCap_def
  isASIDControlCap_def isASIDPoolCap_def isArchPageCap_def
  isDomainCap_def isSGISignalCap_def

lemma is_other_obj_relation_type:
  "is_other_obj_relation_type (a_type ko)
   \<Longrightarrow> obj_relation_cuts ko x = {(x, if is_ArchObj ko then other_aobj_relation else other_obj_relation)}"
  by (clarsimp simp add: obj_relation_cuts_def3 is_other_obj_relation_type_def
               split: a_type.splits aa_type.splits)

lemma a_type_eq_is_ArchObj:
  "a_type ko = a_type ko' \<Longrightarrow> is_ArchObj ko = is_ArchObj ko'"
  by (simp add: a_type_def split: Structures_A.kernel_object.splits if_splits)

(* other_aobj_relation is False for non-arch objs, just as other_obj_relation is for arch objs *)
lemma other_aobj_relation_ArchObj_nonarch[simp]:
  "\<And>ako ko. other_aobj_relation (ArchObj ako) (KOEndpoint ko) = False"
  "\<And>ako ko. other_aobj_relation (ArchObj ako) (KONotification ko) = False"
  "\<And>ako. other_aobj_relation (ArchObj ako) (KOKernelData) = False"
  "\<And>ako. other_aobj_relation (ArchObj ako) (KOUserData) = False"
  "\<And>ako. other_aobj_relation (ArchObj ako) (KOUserDataDevice) = False"
  "\<And>ako ko. other_aobj_relation (ArchObj ako) (KOTCB ko) = False"
  "\<And>ako ko. other_aobj_relation (ArchObj ako) (KOCTE ko) = False"
  by (simp_all add: other_aobj_relation_def split: arch_kernel_obj.splits)

lemma other_aobj_relation_aobj:
  "other_aobj_relation ko ko' \<Longrightarrow> is_ArchObj ko"
  unfolding other_aobj_relation_def is_ArchObj_def
  by (clarsimp split: Structures_A.kernel_object.splits)

lemma ghost_relation_wrapper_machine_state_upd_id[StateRelation_R_assms,simp]:
  "ghost_relation_wrapper (s\<lparr>machine_state := ss\<rparr>) (s'\<lparr>ksMachineState := ss'\<rparr>)
   = ghost_relation_wrapper s s'"
  by simp

(* interface lemma, can't be used in locale assumptions due to free type variable *)
lemma valid_arch_obj'_valid[wp]:
  assumes P: "\<And>P T p. \<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at' T p s)\<rbrace>"
  notes [wp] = hoare_vcg_all_lift hoare_vcg_imp_lift hoare_vcg_const_Ball_lift typ_at_lifts[OF P]
  shows "\<lbrace>valid_arch_obj' ako\<rbrace> f \<lbrace>\<lambda>rv. valid_arch_obj' ako\<rbrace>"
  unfolding valid_arch_obj'_def
  by (case_tac ako; wpsimp)

lemma ghost_relation_wrapper_ksPSpace_upd[simp, StateRelation_R_assms]:
  "ghost_relation_wrapper s (s'\<lparr>ksPSpace := ps'\<rparr>) = ghost_relation_wrapper s s'"
  by (clarsimp simp: ghost_relation_typ_at set_cap_a_type_inv)

lemma ghost_relation_wrapper_abs_upd_simps[simp, StateRelation_R_assms]:
  "\<And>f s s'. ghost_relation_wrapper (cdt_list_update f s) s' = ghost_relation_wrapper s s'"
  "\<And>f s s'. ghost_relation_wrapper (cdt_update f s) s' = ghost_relation_wrapper s s'"
  "\<And>f s s'. ghost_relation_wrapper (is_original_cap_update f s) s' = ghost_relation_wrapper s s'"
  by simp_all

end

global_interpretation StateRelation_R?: StateRelation_R
proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales; fact StateRelation_R_assms)?)
qed

end
