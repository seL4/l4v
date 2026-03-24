(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchDetype_R
imports Detype_R
begin

context Arch begin arch_global_naming

named_theorems Detype_R_assms

(* no extra constraints on this architecture *)
defs arch_deletionIsSafe_def:
  "arch_deletionIsSafe ptr bits s p \<equiv> True"

defs ksASIDMapSafe_def:
  "ksASIDMapSafe \<equiv> \<lambda>s. True"

defs pTablePartialOverlap_def:
  "pTablePartialOverlap \<equiv> \<lambda>pts inRange.
     \<exists>p pt_t. pts p = Some pt_t \<and>
              (\<not> is_aligned p (pt_bits pt_t) \<or>
                (\<not> mask_range p (pt_bits pt_t) \<subseteq> {p. inRange p} \<and>
                 \<not> mask_range p (pt_bits pt_t) \<subseteq> {p. \<not> inRange p}))"

(* FIXME: move *)
lemma deleteObjects_def2:
  "is_aligned ptr bits \<Longrightarrow>
   deleteObjects ptr bits = do
     stateAssert (deletionIsSafe ptr bits) [];
     stateAssert (deletionIsSafe_delete_locale ptr bits) [];
     doMachineOp (freeMemory ptr bits);
     stateAssert (\<lambda>s. \<not> cNodePartialOverlap (gsCNodes s) (\<lambda>x. x \<in> mask_range ptr bits)) [];
     stateAssert (\<lambda>s. \<not> pTablePartialOverlap (gsPTTypes (ksArchState s)) (\<lambda>x. x \<in> mask_range ptr bits)) [];
     modify (\<lambda>s. s \<lparr> ksPSpace := \<lambda>x. if x \<in> mask_range ptr bits
                                        then None else ksPSpace s x,
                     gsUserPages := \<lambda>x. if x \<in> mask_range ptr bits
                                           then None else gsUserPages s x,
                     gsCNodes := \<lambda>x. if x \<in> mask_range ptr bits
                                        then None else gsCNodes s x,
                     ksArchState := gsPTTypes_update (\<lambda>_ x. if x \<in> mask_range ptr bits
                                                            then Nothing
                                                            else gsPTTypes (ksArchState s) x)
                                                     (ksArchState s)\<rparr>);
     stateAssert ksASIDMapSafe []
   od"
  apply (simp add: deleteObjects_def is_aligned_mask[symmetric] unless_def deleteGhost_def o_def)
  apply (rule bind_eqI, rule ext)
  apply (rule bind_eqI, rule ext)
  apply (rule bind_eqI, rule ext)
  apply (simp add: bind_assoc[symmetric])
  apply (rule bind_cong[rotated], rule refl)
  apply (simp add: bind_assoc modify_modify deleteRange_def gets_modify_def)
  apply (rule ext, simp add: exec_modify stateAssert_def assert_def bind_assoc exec_get
                             NOT_eq[symmetric] neg_mask_in_mask_range exec_gets)
  apply (clarsimp simp: simpler_modify_def)
  apply (simp add: data_map_filterWithKey_def split: if_split_asm)
  apply (rule arg_cong2[where f=ksArchState_update])
   apply (rule ext)
   apply clarsimp
   apply (rename_tac s, case_tac s, clarsimp)
   apply (rename_tac ksArch ksMachine, case_tac ksArch, clarsimp)
   apply (simp add: NOT_eq[symmetric] mask_in_range ext)
  apply (rule arg_cong2[where f=gsCNodes_update])
   apply (simp add: NOT_eq[symmetric] mask_in_range ext)
  apply (rule arg_cong2[where f=gsUserPages_update])
   apply (simp add: NOT_eq[symmetric] mask_in_range ext)
  apply (rule arg_cong[where f="\<lambda>f. ksPSpace_update f s" for s])
  apply (simp add: NOT_eq[symmetric] mask_in_range ext split: option.split)
  done

(* deleteObjects_def2 but with is_aligned folded into definition as an assertion *)
lemma deleteObjects_def3:
  "deleteObjects ptr bits =
   do
     assert (is_aligned ptr bits);
     stateAssert (deletionIsSafe ptr bits) [];
     stateAssert (deletionIsSafe_delete_locale ptr bits) [];
     doMachineOp (freeMemory ptr bits);
     stateAssert (\<lambda>s. \<not> cNodePartialOverlap (gsCNodes s) (\<lambda>x. x \<in> mask_range ptr bits)) [];
     stateAssert (\<lambda>s. \<not> pTablePartialOverlap (gsPTTypes (ksArchState s)) (\<lambda>x. x \<in> mask_range ptr bits)) [];
     modify (\<lambda>s. s \<lparr> ksPSpace := \<lambda>x. if x \<in> mask_range ptr bits
                                              then None else ksPSpace s x,
                     gsUserPages := \<lambda>x. if x \<in> mask_range ptr bits
                                           then None else gsUserPages s x,
                     gsCNodes := \<lambda>x. if x \<in> mask_range ptr bits
                                        then None else gsCNodes s x,
                     ksArchState := gsPTTypes_update (\<lambda>_ x. if x \<in> mask_range ptr bits
                                                            then Nothing
                                                            else gsPTTypes (ksArchState s) x)
                                                     (ksArchState s) \<rparr>);
     stateAssert ksASIDMapSafe []
   od"
  apply (cases "is_aligned ptr bits")
   apply (simp add: deleteObjects_def2)
  apply (simp add: deleteObjects_def is_aligned_mask
                   unless_def alignError_def)
  done

lemma obj_relation_cuts_in_obj_range[Detype_R_assms]:
  "\<lbrakk> (y, P) \<in> obj_relation_cuts ko x; x \<in> obj_range x ko;
     kheap s x = Some ko; valid_objs s; pspace_aligned s \<rbrakk>
   \<Longrightarrow> y \<in> obj_range x ko"
  apply (cases ko; simp)
   apply (clarsimp split: if_split_asm)
   apply (subgoal_tac "cte_at (x, ya) s")
    apply (drule(2) cte_at_cte_map_in_obj_bits)
    apply (simp add: obj_range_def)
   apply (fastforce intro: cte_wp_at_cteI)
  apply (frule(1) pspace_alignedD)
  apply (frule valid_obj_sizes, erule ranI)
  apply (rename_tac arch_kernel_obj)
  apply (case_tac arch_kernel_obj; simp)
   apply (clarsimp simp only: obj_range_def atLeastAtMost_iff
                              obj_bits.simps arch_kobj_size.simps)
   apply (rule context_conjI)
    apply (erule is_aligned_no_wrap')
    apply (simp add: table_size_def)
    apply (rule shiftl_less_t2n)
     apply (erule order_le_less_trans)
     apply (simp add: bit_simps mask_def)
    apply (simp add: bit_simps)
   apply (subst add_diff_eq[symmetric])
   apply (rule word_plus_mono_right)
    apply (subst word_less_sub_le, simp add: bit_simps)
    apply (rule shiftl_less_t2n)
     apply (erule order_le_less_trans)
     apply (simp add: bit_simps mask_def)
    apply (simp add: bit_simps)
   apply (simp add: field_simps)
  apply (clarsimp simp only: obj_range_def atLeastAtMost_iff)
  apply (rule conjI)
   apply (erule is_aligned_no_wrap')
   apply (simp add: shiftl_t2n mult_ac)
   apply (erule word_less_power_trans2)
    apply (rule pbfs_atleast_pageBits)
   using pbfs_less_wb'
   apply (simp add: word_bits_def)
  apply (subst add_diff_eq[symmetric])
  apply (rule word_plus_mono_right; simp add: add_diff_eq)
  apply (simp add: shiftl_t2n mult_ac)
  apply (rule word_less_power_trans2; (simp add: pbfs_atleast_pageBits)?)
  using pbfs_less_wb'
  apply (simp add: word_bits_def)
  done

lemma zobj_refs_capRange[Detype_R_assms]:
  "capAligned c \<Longrightarrow> zobj_refs' c \<subseteq> capRange c"
  apply (cases c; simp add: capAligned_def capRange_def is_aligned_no_overflow)
  apply (rename_tac ac)
  apply (case_tac ac; simp)
  apply clarsimp
  apply (drule is_aligned_no_overflow)
  apply simp
  done

lemma arch_deletionIsSafe:
  assumes al: "is_aligned base magnitude"
  shows
    "\<lbrakk>valid_pspace s; valid_untyped (cap.UntypedCap d base magnitude idx) s;
      (s, s') \<in> state_relation\<rbrakk>
     \<Longrightarrow> arch_deletionIsSafe base magnitude s' p"
  by (simp add: arch_deletionIsSafe_def) (* trivial on this architecture *)

lemma state_rel_ghost:
  "(s,s') \<in> state_relation \<Longrightarrow>
   ghost_relation (kheap s) (gsUserPages s') (gsCNodes s') (gsPTTypes (ksArchState s'))"
  by (erule state_relationE[simplified ghost_relation_wrapper_def])

lemma ghost_PTTypes:
  "\<lbrakk> ghost_relation kh gsu gsc pt_Ts; pt_Ts p = Some pt_t \<rbrakk> \<Longrightarrow>
   (\<exists>pt. kh p = Some (ArchObj (PageTable pt)) \<and> pt_t = pt_type pt)"
  by (clarsimp simp: ghost_relation_def)

lemma pTableNoPartialOverlap:
  "corres dc
          (\<lambda>s. \<exists>cref. cte_wp_at ((=) (cap.UntypedCap d base magnitude idx)) cref s \<and>
                      valid_objs s \<and> pspace_aligned s)
          \<top>
          (return x)
          (stateAssert (\<lambda>s. \<not> pTablePartialOverlap (gsPTTypes (ksArchState s))
                                                   (\<lambda>x. base \<le> x \<and> x \<le> base + mask magnitude)) [])"
  apply (simp add: stateAssert_def assert_def)
  apply (rule corres_symb_exec_r[OF _ get_sp])
    apply (rule corres_req[rotated], subst if_P, assumption)
     apply simp
    apply (clarsimp simp: pTablePartialOverlap_def)
    apply (frule state_rel_ghost)
    apply (drule (1) ghost_PTTypes)
    apply clarsimp
    apply (drule(1) cte_wp_valid_cap)
    apply (clarsimp simp: valid_cap_def valid_untyped_def)
    apply (frule(1) pspace_alignedD)
    apply (simp add: add_mask_fold)
    apply (elim allE, drule(1) mp, simp add: obj_range_def valid_obj_def cap_aligned_def)
    apply (clarsimp simp: pt_bits_def)
    apply (erule is_aligned_get_word_bits[where 'a=machine_word_len, folded word_bits_def])
     apply (clarsimp simp: is_aligned_no_overflow_mask add_mask_fold)
     apply (blast intro: order_trans)
    apply (simp add: is_aligned_no_overflow_mask power_overflow word_bits_def)
   apply wp+
  done

lemma objSize_eq_capBits[Detype_R_assms]:
  "Types_H.getObjectSize ty us = APIType_capBits ty us"
  by (cases ty;
      clarsimp simp: getObjectSize_def objBits_simps bit_simps
                     APIType_capBits_def apiGetObjectSize_def ptBits_def
               split: apiobject_type.splits)

(* safe for generic context, and requalifying object_type.inject would yield "inject" *)
(* FIXME arch-split: can go much much earlier *)
lemma object_type_inject[Detype_R_assms]:
  "(APIObjectType x = APIObjectType y) = (x = y)"
  by simp

end (* Arch *)


text \<open>Invariant preservation across concrete deletion\<close>

context Arch_delete_locale begin

(* the bits of caps they need for validity argument are within their capRanges *)
lemma valid_cap_ctes_pre:
    "\<And>c. s' \<turnstile>' c \<Longrightarrow> case c of CNodeCap ref bits g gs \<Rightarrow>
                      \<forall>x. ref + (x && mask bits) * 2^cteSizeBits \<in> capRange c
                    | Zombie ref (ZombieCNode bits) n \<Rightarrow>
                      \<forall>x. ref + (x && mask bits) * 2^cteSizeBits \<in> capRange c
                    | ArchObjectCap (PageTableCap ref pt_t data) \<Rightarrow>
                      \<forall>x. x \<le> mask (ptTranslationBits pt_t) \<longrightarrow> ref + (x << pte_bits) \<in> capRange c
                    | ArchObjectCap (FrameCap ref r sz d m) \<Rightarrow>
                      \<forall>p<2 ^ (pageBitsForSize sz - pageBits). ref + (p << pageBits) \<in> capRange c
                    | _ \<Rightarrow> True"
  apply (drule valid_capAligned)
  apply (simp split: capability.split zombie_type.split arch_capability.split, safe)
     using pre_helper[where a=cteSizeBits]
     apply (clarsimp simp add: capRange_def capAligned_def objBits_simps field_simps)
    apply (clarsimp simp add: capRange_def capAligned_def shiftl_t2n)
    apply (frule pre_helper2[where bits=pageBits]; simp add: pbfs_atleast_pageBits mult_ac)
   using pbfs_less_wb' apply (simp add: word_bits_conv)
   apply (clarsimp simp add: capRange_def capAligned_def shiftl_t2n
                   simp del: atLeastAtMost_iff capBits.simps)
   apply (simp del: atLeastAtMost_iff)
   apply (drule_tac bits="pte_bits" and x="ucast x" in pre_helper2; simp add: mult_ac)
    apply (simp add: bit_simps)
   apply (simp add: table_size_def)
   apply (erule order_le_less_trans)
   apply (simp add: mask_def bit_simps)
  apply (clarsimp simp add: capRange_def capAligned_def
                  simp del: atLeastAtMost_iff capBits.simps)
  using pre_helper[where a=cteSizeBits]
  apply (clarsimp simp add: capRange_def capAligned_def objBits_simps field_simps)
  done

lemma valid_cap':
    "\<And>p c. \<lbrakk> s' \<turnstile>' c; cte_wp_at' (\<lambda>cte. cteCap cte = c) p s';
             capRange c \<inter> mask_range base bits = {} \<rbrakk>
           \<Longrightarrow> state' \<turnstile>' c"
  apply (subgoal_tac "capClass c = PhysicalClass \<longrightarrow> capUntypedPtr c \<in> capRange c")
   apply (subgoal_tac "capClass c = PhysicalClass \<longrightarrow>
                        capUntypedPtr c \<notin> mask_range base bits")
    apply (frule valid_cap_ctes_pre)
    apply (case_tac c, simp_all add: valid_cap'_def replycap_argument
                                del: atLeastAtMost_iff
                              split: zombie_type.split_asm)
      apply (simp add: field_simps del: atLeastAtMost_iff)
      apply blast
     defer
     apply (simp add: valid_untyped'_def)
    apply (simp add: field_simps bit_simps word_size_def del: atLeastAtMost_iff)
    apply blast
   apply blast
  apply (clarsimp simp: capAligned_capUntypedPtr)
  apply (rename_tac arch_cap)
  apply (case_tac arch_cap; simp del: atLeastAtMost_iff add: frame_at'_def page_table_at'_def)
   apply blast
  apply blast
  done

lemma sym_refs_VCPU_hyp_live':
 "\<lbrakk>ko_wp_at' ((=) (KOArch (KOVCPU v))) p s'; sym_refs (state_hyp_refs_of' s'); vcpuTCBPtr v = Some t\<rbrakk>
  \<Longrightarrow> ko_wp_at' (\<lambda>ko. koTypeOf ko = TCBT \<and> hyp_live' ko) t s'"
  apply (drule (1) sym_hyp_refs_ko_wp_atD)
  apply (clarsimp)
  apply (drule state_hyp_refs_of'_elemD)
  apply (simp add: ko_wp_at'_def)
  apply (clarsimp simp: hyp_refs_of_rev' hyp_live'_def)
  done

lemma sym_refs_TCB_hyp_live':
 "\<lbrakk>ko_wp_at' ((=) (KOTCB t)) p s'; sym_refs (state_hyp_refs_of' s'); atcbVCPUPtr (tcbArch t) = Some v\<rbrakk>
  \<Longrightarrow> ko_wp_at' (\<lambda>ko. koTypeOf ko = ArchT VCPUT \<and> hyp_live' ko) v s'"
  apply (drule (1) sym_hyp_refs_ko_wp_atD)
  apply (clarsimp)
  apply (drule state_hyp_refs_of'_elemD)
  apply (simp add: ko_wp_at'_def)
  apply (clarsimp simp: hyp_refs_of_rev' hyp_live'_def arch_live'_def)
  done

lemma irq_nodes_range:
  "\<forall>irq :: irq. irq_node' s' + (ucast irq << cteSizeBits) \<notin> base_bits"
  using global_refs
  by (fastforce simp: global_refs'_def)

end (* Arch_delete_locale *)

interpretation Detype_R?: Detype_R
proof goal_cases
  interpret Arch  .
  case 1 show ?case by (intro_locales; (unfold_locales; (fact Detype_R_assms)?)?)
qed

context delete_locale begin

(* Equivalent to doing an Arch_delete_locale interpretation and re-exporting, but as we don't need
   this name re-exported from Arch_delete_locale, it's faster to not interpret Arch *)
lemmas irq_nodes =
  Arch_delete_locale.irq_nodes_range[of s' base bits, simplified Arch_delete_locale_def,
                                     OF delete_locale_axioms]

sublocale delete_locale_gen by (unfold_locales; fact zobj_refs_capRange irq_nodes)

(* used by proof below as these names in delete_locale *)
lemmas deletionIsSafe_delete_locale_holds = deletionIsSafe_delete_locale_holds
lemmas null_filter' = null_filter'
lemmas delete_ko_wp_at' = delete_ko_wp_at'
lemmas delete_ex_cte_cap_to' = delete_ex_cte_cap_to'

end (* delete_locale *)

context detype_locale' begin

sublocale detype_locale'_gen by (unfold_locales; fact RISCV64.arch_deletionIsSafe)

lemmas deletionIsSafe = deletionIsSafe

end (* detype_locale' *)

context Arch begin arch_global_naming

(* FIXME arch-split: some of this can be generalised; 3 is same on all arches *)
lemma deleteObjects_corres:
  "is_aligned base magnitude \<Longrightarrow> magnitude \<ge> 3 \<Longrightarrow>
   corres dc
      (\<lambda>s. einvs s
           \<and> s \<turnstile> (cap.UntypedCap d base magnitude idx)
           \<and> (\<exists>cref. cte_wp_at ((=) (cap.UntypedCap d base magnitude idx)) cref s
                     \<and> descendants_range (cap.UntypedCap d base magnitude idx) cref s)
           \<and> untyped_children_in_mdb s \<and> if_unsafe_then_cap s
           \<and> valid_mdb s \<and> valid_global_refs s \<and> ct_active s
           \<and> schact_is_rct s)
      (\<lambda>s'. invs' s'
           \<and> cte_wp_at' (\<lambda>cte. cteCap cte = UntypedCap d base magnitude idx) ptr s'
           \<and> descendants_range' (UntypedCap d base magnitude idx) ptr (ctes_of s')
           \<and> ct_active' s'
           \<and> s' \<turnstile>' (UntypedCap d base magnitude idx))
      (delete_objects base magnitude) (deleteObjects base magnitude)"
  apply (simp add: deleteObjects_def2)
  apply (rule corres_stateAssert_implied[where P'=\<top>, simplified])
   prefer 2
   apply clarsimp
   apply (rule_tac cap="cap.UntypedCap d base magnitude idx" and ptr="(a,b)" and s=s
                in detype_locale'.deletionIsSafe,
          simp_all add: detype_locale'_def detype_locale_def invs_valid_pspace)[1]
   apply (simp add: valid_cap_simps)
  apply (rule corres_stateAssert_add_assertion[rotated])
   apply (rule_tac ptr=ptr and idx=idx and d=d in delete_locale.deletionIsSafe_delete_locale_holds)
   apply (clarsimp simp: delete_locale_def)
   apply (intro conjI)
    apply (fastforce simp: sch_act_simple_def schact_is_rct_def state_relation_def)
   apply (rule_tac cap="cap.UntypedCap d base magnitude idx" and ptr="(a,b)" and s=s
                in detype_locale'.deletionIsSafe,
          simp_all add: detype_locale'_def detype_locale_def invs_valid_pspace)[1]
   apply (simp add: valid_cap_simps)
  apply (simp add: ksASIDMapSafe_def)
  apply (simp add: delete_objects_def)
  apply (rule corres_underlying_split[where r'=dc])
     apply (rule corres_guard_imp[where r=dc])
       apply (rule corres_machine_op'[OF corres_Id]; simp)
       apply (rule no_fail_freeMemory; simp)
      apply simp
     apply (auto elim: is_aligned_weaken)[1]
    apply (rule corres_return_bind)
    apply (rule corres_split[OF cNodeNoPartialOverlap])
      apply (rule corres_return_bind)
      apply (rule corres_split[OF pTableNoPartialOverlap])
        apply simp
        apply (rule_tac P="\<lambda>s. valid_objs s \<and> valid_list s \<and>
                               (\<exists>cref. cte_wp_at ((=) (cap.UntypedCap d base magnitude idx)) cref s \<and>
                                       descendants_range (cap.UntypedCap d base magnitude idx) cref s ) \<and>
                               s \<turnstile> cap.UntypedCap d base magnitude idx \<and> pspace_aligned s \<and>
                               valid_mdb s \<and> pspace_distinct s \<and> if_live_then_nonz_cap s \<and>
                               zombies_final s \<and> sym_refs (state_refs_of s) \<and> sym_refs (state_hyp_refs_of s) \<and>
                               untyped_children_in_mdb s \<and> if_unsafe_then_cap s \<and>
                               valid_global_refs s"
                    and P'="\<lambda>s. s \<turnstile>' capability.UntypedCap d base magnitude idx \<and>
                                valid_pspace' s \<and> deletionIsSafe_delete_locale base magnitude s"
                     in corres_modify)
        apply (simp add: valid_pspace'_def)
        apply (rule state_relation_null_filterE, assumption,
               simp_all add: pspace_aligned'_cut pspace_distinct'_cut)[1]
                apply (simp add: detype_def)
               apply (intro exI, fastforce)
              apply (rule ext, clarsimp simp add: null_filter_def)
              apply (rule sym, rule ccontr, clarsimp)
              apply (drule(4) cte_map_not_null_outside')
               apply (fastforce simp add: cte_wp_at_caps_of_state)
              apply simp
             apply (rule ext, clarsimp simp: null_filter'_def map_to_ctes_delete)
             apply (rule sym, rule ccontr, clarsimp)
             apply (frule (2) pspace_relation_cte_wp_atI[OF state_relation_pspace_relation])
             apply (elim exE)
             apply (frule (4) cte_map_not_null_outside')
              apply (rule cte_wp_at_weakenE, erule conjunct1)
              apply (case_tac y, clarsimp)
              apply (clarsimp simp: valid_mdb'_def valid_mdb_ctes_def
                                    valid_nullcaps_def)
             apply clarsimp
             apply (frule_tac cref="(aa, ba)" in cte_map_untyped_range,
                    erule cte_wp_at_weakenE[OF _ TrueI], assumption+)
             apply (simp add: add_mask_fold)
            apply (simp add: add_mask_fold)
            apply (rule detype_pspace_relation[simplified],
                   simp_all add: state_relation_pspace_relation valid_pspace_def)[1]
             apply (simp add: valid_cap'_def capAligned_def)
            apply (clarsimp simp: valid_cap_def, assumption)
           apply (rule detype_ready_queues_relation; blast?)
             apply (clarsimp simp: deletionIsSafe_delete_locale_def)
            apply (erule state_relation_ready_queues_relation)
           apply (simp add: add_mask_fold)
          (* arch_state_relation *)
          apply (fastforce simp: arch_state_relation_def update_gs_def comp_def
                           dest!: state_relationD
                           split: Structures_A.apiobject_type.splits aobject_type.splits)
         apply (clarsimp simp: state_relation_def ghost_relation_of_heap
                               detype_def)
         apply (drule_tac t="gsUserPages s'" in sym)
         apply (drule_tac t="gsCNodes s'" in sym)
         apply (drule_tac t="gsPTTypes (ksArchState s')" in sym)
         apply (auto simp: ups_of_heap_def cns_of_heap_def ext pt_types_of_heap_def add_mask_fold
                           opt_map_def
                     split: option.splits kernel_object.splits)[1]
        apply (simp add: valid_mdb_def)
       apply (wp hoare_vcg_ex_lift hoare_vcg_ball_lift | wps |
              simp add: invs_def valid_state_def valid_pspace_def
                        descendants_range_def | wp (once) hoare_drop_imps)+
   apply fastforce
  apply (wpsimp wp: hoare_vcg_op_lift)
  done

end (* Arch *)

context Arch_delete_locale begin

lemma valid_arch_tcb':
  "\<lbrakk> ksPSpace s' p = Some (KOTCB tcb); is_aligned p tcbBlockSizeBits; ps_clear p tcbBlockSizeBits s';
     valid_arch_tcb' (tcbArch tcb) s' \<rbrakk>
   \<Longrightarrow> valid_arch_tcb' (tcbArch tcb) state'"
   using sym_hyp_refs
   apply (clarsimp simp add: valid_arch_tcb'_def split: option.split_asm)
   apply (drule (1) sym_refs_TCB_hyp_live'[rotated])
    apply (clarsimp simp: ko_wp_at'_def objBits_simps; (rule conjI|assumption)+)
   apply (drule live_notRange, clarsimp simp: live'_def)
    apply (case_tac ko; simp)
   apply clarsimp
   done

lemma pspace_in_kernel_mappings':
  "pspace_in_kernel_mappings' state'"
  using pkm
  by (simp add: dom_def)

lemma valid_global_refs':
  "valid_global_refs' state'"
  using refs
  by (simp add: valid_global_refs'_def tree_to_ctes valid_cap_sizes'_def
                global_refs'_def valid_refs'_def ball_ran_eq)

lemma valid_arch_state':
  "valid_arch_state' state'"
  using arch global_refs2
  apply (simp add: valid_arch_state'_def global_refs'_def)
  apply (case_tac "armHSCurVCPU (ksArchState s')"; clarsimp simp add: split_def)
  apply (drule live_notRange, clarsimp, case_tac ko; simp add: is_vcpu'_def live'_def)
  done

end (* Arch_delete_locale *)

context delete_locale begin

(* Equivalent to doing an Arch_delete_locale interpretation and re-exporting, but as we don't need
   these names re-exported from Arch_delete_locale, it's faster to not interpret Arch *)
lemmas Arch_delete_locale_gen_2_exports_pre =
  Arch_delete_locale.valid_arch_tcb'
  Arch_delete_locale.valid_cap'
  Arch_delete_locale.pspace_in_kernel_mappings'
  Arch_delete_locale.valid_global_refs'
  Arch_delete_locale.valid_arch_state'

lemmas Arch_delete_locale_gen_2_exports =
  Arch_delete_locale_gen_2_exports_pre[of s' base bits, simplified Arch_delete_locale_def,
                                 OF delete_locale_axioms]

sublocale delete_locale_gen_2
  by (unfold_locales; fact Arch_delete_locale_gen_2_exports)

lemmas delete_invs' = delete_invs'

end

context Arch begin arch_global_naming

named_theorems Detype_R_2_assms

(* FIXME arch-split: some lemmas in this block use deleteObjects_def3, which leaks some arch details.
   Not all of them need to deal with these arch details, so if the def2/def3 lemmas can be
   generalised or wrapped, some of the lemmas in this block can become generic. *)

lemma deleteObjects_null_filter[Detype_R_2_assms]:
  "\<lbrace>cte_wp_at' (\<lambda>c. cteCap c = UntypedCap d ptr bits idx) p
     and invs' and ct_active' and sch_act_simple
     and (\<lambda>s. descendants_range' (UntypedCap d ptr bits idx) p (ctes_of s))
     and (\<lambda>s. P (null_filter' (ctes_of s)))
     and K (bits < word_bits \<and> is_aligned ptr bits)\<rbrace>
   deleteObjects ptr bits
   \<lbrace>\<lambda>rv s.  P (null_filter' (ctes_of s))\<rbrace>"
  apply (simp add: deleteObjects_def3 doMachineOp_def split_def)
  apply wpsimp
  apply (subgoal_tac "delete_locale s ptr bits p idx d")
   apply (drule_tac Q=P in delete_locale.null_filter')
    apply assumption
   apply (clarsimp simp: p_assoc_help)
   apply (simp add: eq_commute field_simps mask_def)
   apply (subgoal_tac "ksPSpace (s\<lparr>ksMachineState := snd ((), b)\<rparr>) =
                       ksPSpace s", simp only:, simp)
  apply (unfold_locales, simp_all)
  done

lemma deleteObjects_invs'[Detype_R_2_assms]:
  "\<lbrace>cte_wp_at' (\<lambda>c. cteCap c = UntypedCap d ptr bits idx) p
     and invs' and ct_active' and sch_act_simple
     and (\<lambda>s. descendants_range' (UntypedCap d ptr bits idx) p (ctes_of s))
     and K (bits < word_bits \<and> is_aligned ptr bits)\<rbrace>
     deleteObjects ptr bits
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
proof -
  show ?thesis
  apply (rule hoare_pre)
   apply (rule_tac P'="is_aligned ptr bits \<and> 3 \<le> bits \<and> bits \<le> word_bits" in hoare_grab_asm)
   apply (clarsimp simp add: deleteObjects_def3)
   apply (simp add: freeMemory_def bind_assoc doMachineOp_bind)
   apply (simp add: bind_assoc[where f="\<lambda>_. modify f" for f, symmetric])
   apply (simp add: mapM_x_storeWord_step[simplified word_size_bits_def]
                    doMachineOp_modify modify_modify)
   apply (simp add: bind_assoc intvl_range_conv'[where 'a=machine_word_len, folded word_bits_def] mask_def field_simps)
   apply (wp)
  apply (simp cong: if_cong)
  apply (subgoal_tac "is_aligned ptr bits \<and> 3 \<le> bits \<and> bits < word_bits",simp)
   apply clarsimp
   apply (frule(2) delete_locale.intro, simp_all)[1]
   apply (simp add: ksASIDMapSafe_def invs'_gsTypes_update)
   apply (rule subst[rotated, where P=invs'], erule delete_locale.delete_invs')
   apply (simp add: field_simps mask_def)
  apply clarsimp
  apply (drule invs_valid_objs')
  apply (drule (1) cte_wp_at_valid_objs_valid_cap')
  apply (clarsimp simp add: valid_cap'_def capAligned_def untypedBits_defs)
  done
qed

lemma deleteObjects_st_tcb_at'[Detype_R_2_assms]:
  "\<lbrace>cte_wp_at' (\<lambda>c. cteCap c = UntypedCap d ptr bits idx) p
     and invs' and ct_active' and sch_act_simple
     and (\<lambda>s. descendants_range' (UntypedCap d ptr bits idx) p (ctes_of s))
     and st_tcb_at' (P and (\<noteq>) Inactive and (\<noteq>) IdleThreadState) t
     and K (bits < word_bits \<and> is_aligned ptr bits)\<rbrace>
     deleteObjects ptr bits
   \<lbrace>\<lambda>rv. st_tcb_at' P t\<rbrace>"
  apply (simp add: deleteObjects_def3 doMachineOp_def split_def)
  apply wp
  apply clarsimp
  apply (subgoal_tac "delete_locale s ptr bits p idx d")
   apply (drule delete_locale.delete_ko_wp_at'
                [where p = t and
                       P="case_option False (P \<circ> tcbState) \<circ> projectKO_opt",
                 simplified eq_commute])
    apply (simp add: pred_tcb_at'_def obj_at'_real_def)
    apply (rule conjI)
     apply (fastforce elim: ko_wp_at'_weakenE simp: projectKO_opt_tcb)
    apply (erule if_live_then_nonz_capD' [rotated])
     apply (clarsimp simp: live'_def)
    apply (clarsimp simp: invs'_def valid_state'_def)
   apply (clarsimp simp: pred_tcb_at'_def obj_at'_real_def
                  field_simps ko_wp_at'_def ps_clear_def
                  cong:if_cong
                  split: option.splits)
  apply (simp add: delete_locale_def)
  done

lemma deleteObjects_cap_to':
  "\<lbrace>cte_wp_at' (\<lambda>c. cteCap c = UntypedCap d ptr bits idx) p
     and invs' and ct_active' and sch_act_simple
     and (\<lambda>s. descendants_range' (UntypedCap d ptr bits idx) p (ctes_of s))
     and ex_cte_cap_to' p'
     and K (bits < word_bits \<and> is_aligned ptr bits)\<rbrace>
      deleteObjects ptr bits
   \<lbrace>\<lambda>rv. ex_cte_cap_to' p'\<rbrace>"
  apply (simp add: deleteObjects_def3 doMachineOp_def split_def)
  apply wp
  apply clarsimp
  apply (subgoal_tac "delete_locale s ptr bits p idx d")
   apply (drule delete_locale.delete_ex_cte_cap_to', assumption)
   apply (simp cong:if_cong)
   apply (subgoal_tac
     "s\<lparr>ksMachineState := b,
        ksPSpace := \<lambda>x. if ptr \<le> x \<and> x \<le> ptr + mask bits then None
                        else ksPSpace s x\<rparr> =
      ksMachineState_update (\<lambda>_. b)
      (s\<lparr>ksPSpace := \<lambda>x. if ptr \<le> x \<and> x \<le> ptr + mask bits then None
                         else ksPSpace s x\<rparr>)",erule ssubst)
    apply (simp add: field_simps ex_cte_cap_wp_to'_def cong:if_cong)
   apply simp
  apply (simp add: delete_locale_def)
  done

lemma deleteObject_no_overlap[wp]:
  "\<lbrace>valid_cap' (UntypedCap d ptr bits idx) and valid_pspace'\<rbrace>
     deleteObjects ptr bits
   \<lbrace>\<lambda>rv s. pspace_no_overlap' ptr bits s\<rbrace>"
  apply (simp add: deleteObjects_def3 doMachineOp_def split_def)
  apply wp
  apply (clarsimp simp: valid_cap'_def cong:if_cong)
  apply (drule (2) valid_untyped_no_overlap)
  apply (subgoal_tac
     "s\<lparr>ksMachineState := b,
        ksPSpace := \<lambda>x. if ptr \<le> x \<and> x \<le> ptr + mask bits then None
                        else ksPSpace s x\<rparr> =
      ksMachineState_update (\<lambda>_. b)
      (s\<lparr>ksPSpace := ksPSpace s |` (- mask_range ptr bits)\<rparr>)", simp)
  apply (case_tac s, simp)
  apply (rule ext)
  apply simp
  done

lemma deleteObjects_cte_wp_at':
  "\<lbrace>\<lambda>s. cte_wp_at' P p s \<and> p \<notin> mask_range ptr bits
         \<and> s \<turnstile>' (UntypedCap d ptr bits idx) \<and> valid_pspace' s\<rbrace>
     deleteObjects ptr bits
   \<lbrace>\<lambda>rv s. cte_wp_at' P p s\<rbrace>"
  apply (simp add: deleteObjects_def3 doMachineOp_def split_def)
  apply wp
  apply (clarsimp simp: valid_pspace'_def cong:if_cong)
  apply (subgoal_tac
     "s\<lparr>ksMachineState := b,
        ksPSpace := \<lambda>x. if ptr \<le> x \<and> x \<le> ptr + mask bits then None
                        else ksPSpace s x\<rparr> =
      ksMachineState_update (\<lambda>_. b)
      (s\<lparr>ksPSpace := \<lambda>x. if ptr \<le> x \<and> x \<le> ptr + mask bits then None
                         else ksPSpace s x\<rparr>)", erule ssubst)
   apply (simp add: cte_wp_at_delete' x_power_minus_1)
  apply (case_tac s, simp)
  done

lemma deleteObjects_nosch:
  "deleteObjects ptr sz \<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace>"
  by (simp add: deleteObjects_def3 | wp hoare_drop_imp)+

lemmas getObjSize_simps = RISCV64_H.getObjectSize_def[split_simps RISCV64_H.object_type.split apiobject_type.split]

lemma createObject_cte_wp_at'[Detype_R_2_assms]:
  "\<lbrace>\<lambda>s. Types_H.getObjectSize ty us < word_bits \<and>
        is_aligned ptr (Types_H.getObjectSize ty us) \<and>
        pspace_no_overlap' ptr (Types_H.getObjectSize ty us) s \<and>
        cte_wp_at' (\<lambda>c. P c) slot s \<and> pspace_aligned' s \<and>
        pspace_distinct' s\<rbrace>
   RetypeDecls_H.createObject ty ptr us d
   \<lbrace>\<lambda>r s. cte_wp_at' (\<lambda>c. P c) slot s \<rbrace>"
  unfolding global.createObject_def
  apply (wpsimp wp: createObjects_orig_cte_wp_at'[where sz = "(Types_H.getObjectSize ty us)"]
                    threadSet_cte_wp_at'
         | clarsimp simp: RISCV64_H.createObject_def placeNewDataObject_def
                          unless_def placeNewObject_def2 objBits_simps range_cover_full
                          curDomain_def bit_simps
                          getObjSize_simps apiGetObjectSize_def tcbBlockSizeBits_def
                          epSizeBits_def ntfnSizeBits_def cteSizeBits_def updatePTType_def
         | intro conjI impI)+
  done

lemma getPTE_det:
  "ko_wp_at' ((=) (KOArch (KOPTE pte))) p s
   \<Longrightarrow> getObject p s = ({((pte::pte),s)},False)"
  apply (clarsimp simp: ko_wp_at'_def getObject_def split_def
                        bind_def gets_def return_def get_def assert_opt_def
                  split: if_splits)
  apply (clarsimp simp: fail_def return_def lookupAround2_known1)
   apply (simp add: loadObject_default_def)
  apply (clarsimp simp: projectKO_def projectKO_opt_pte alignCheck_def
                        objBits_simps unless_def)
  apply (clarsimp simp: bind_def return_def is_aligned_mask)
  apply (intro conjI)
   apply (intro set_eqI iffI)
    apply clarsimp
    apply (subst (asm) in_magnitude_check')
     apply (simp add:archObjSize_def is_aligned_mask)+
    apply (rule bexI[rotated])
     apply (rule in_magnitude_check'[THEN iffD2])
         apply (simp add:is_aligned_mask)+
   apply (clarsimp simp:image_def)
  apply (clarsimp simp: magnitudeCheck_assert assert_def objBits_def archObjSize_def
                        return_def fail_def lookupAround2_char2
                  split: option.splits if_split_asm)
  apply (rule ccontr)
  apply (simp add: ps_clear_def flip: is_aligned_mask)
  apply (erule_tac x = x2 in in_empty_interE)
   apply (clarsimp simp:less_imp_le)
   apply (rule conjI)
    apply (subst add.commute)
    apply (rule word_diff_ls')
     apply (clarsimp simp:field_simps not_le plus_one_helper mask_def)
    apply (simp add: is_aligned_no_overflow_mask add_ac)
   apply simp
  apply blast
  done

lemma setCTE_pte_at':
  "\<lbrace>ko_wp_at' ((=) (KOArch (KOPTE pte))) ptr and
    cte_wp_at' (\<lambda>_. True) src and pspace_distinct'\<rbrace>
   setCTE src cte
   \<lbrace>\<lambda>x s. ko_wp_at' ((=) (KOArch (KOPTE pte))) ptr s\<rbrace>"
   apply (clarsimp simp:setCTE_def2)
   including no_pre apply wp
   apply (simp add:split_def)
   apply (clarsimp simp:valid_def)
   apply (subgoal_tac "b = s")
   prefer 2
    apply (erule use_valid[OF _ locateCTE_inv])
    apply simp
   apply (subgoal_tac "ptr \<noteq> a")
   apply (frule use_valid[OF _ locateCTE_ko_wp_at'])
    apply simp
   apply (clarsimp simp:ko_wp_at'_def ps_clear_def)
   apply (simp add:in_dom_eq)
   apply (drule use_valid[OF _ locateCTE_case])
    apply simp
   apply (clarsimp simp:ko_wp_at'_def objBits_simps)
   done

lemma storePTE_det:
  "ko_wp_at' ((=) (KOArch (KOPTE pte))) ptr s
   \<Longrightarrow> storePTE ptr (new_pte::pte) s =
       modify (ksPSpace_update (\<lambda>_. (ksPSpace s)(ptr \<mapsto> KOArch (KOPTE new_pte)))) s"
  apply (clarsimp simp:ko_wp_at'_def storePTE_def split_def
                       bind_def gets_def return_def
                       get_def setObject_def
                       assert_opt_def split:if_splits)
  apply (clarsimp simp:lookupAround2_known1 return_def alignCheck_def
                       updateObject_default_def split_def
                       unless_def projectKO_def
                       projectKO_opt_pte bind_def when_def
                       is_aligned_mask[symmetric] objBits_simps)
  apply (drule magnitudeCheck_det; simp add:objBits_simps)
  done

lemma modify_pte_pte_at':
  "\<lbrace>pte_at' ptr\<rbrace>
   modify (ksPSpace_update (\<lambda>ps. ps(ptr \<mapsto> KOArch (KOPTE new_pte))))
   \<lbrace>\<lambda>a. pte_at' ptr\<rbrace>"
  apply wp
  apply (clarsimp simp del: fun_upd_apply
                  simp: typ_at'_def ko_wp_at'_def objBits_simps)
  apply (clarsimp simp:ps_clear_def)
  apply (case_tac ko,simp_all)
  apply (rename_tac arch_kernel_object)
  apply (case_tac arch_kernel_object,simp_all)
  apply (clarsimp simp:archObjSize_def)
  done

lemma modify_pte_pspace_distinct':
  "\<lbrace>pte_at' ptr and pspace_distinct'\<rbrace>
   modify (ksPSpace_update (\<lambda>ps. ps(ptr \<mapsto> KOArch (KOPTE new_pte))))
   \<lbrace>\<lambda>a. pspace_distinct'\<rbrace>"
  apply (clarsimp simp: simpler_modify_def ko_wp_at'_def valid_def typ_at'_def)
  apply (case_tac ko; simp)
  apply (rename_tac arch_kernel_object)
  apply (case_tac arch_kernel_object,simp_all)
  apply (subst pspace_distinct'_def)
  apply (intro ballI)
  apply (erule domE)
  apply (clarsimp split:if_splits)
   apply (drule(1) pspace_distinctD')
   apply (simp add:objBits_simps)
   apply (simp add:ps_clear_def)
  apply (drule_tac x = x in pspace_distinctD')
   apply simp
  unfolding ps_clear_def
  apply (erule disjoint_subset2[rotated])
  apply clarsimp
  done

lemma modify_pte_pspace_aligned':
  "\<lbrace>pte_at' ptr and pspace_aligned'\<rbrace>
   modify (ksPSpace_update (\<lambda>ps. ps(ptr \<mapsto> KOArch (KOPTE new_pte))))
   \<lbrace>\<lambda>a. pspace_aligned'\<rbrace>"
  apply (clarsimp simp: simpler_modify_def ko_wp_at'_def valid_def typ_at'_def)
  apply (case_tac ko,simp_all)
  apply (rename_tac arch_kernel_object)
  apply (case_tac arch_kernel_object,simp_all)
  apply (subst pspace_aligned'_def)
  apply (intro ballI)
  apply (erule domE)
  apply (clarsimp split:if_splits)
   apply (drule(1) pspace_alignedD')
    apply (simp add:objBits_simps)
   apply (simp add:ps_clear_def)
  apply (drule_tac x = x in pspace_alignedD')
   apply simp
  apply simp
  done

lemma modify_pte_psp_no_overlap':
  "\<lbrace>pte_at' ptr and pspace_no_overlap' ptr' sz\<rbrace>
   modify (ksPSpace_update (\<lambda>ps. ps(ptr \<mapsto> KOArch (KOPTE new_pte))))
   \<lbrace>\<lambda>a. pspace_no_overlap' ptr' sz\<rbrace>"
proof -
  note [simp del] = untyped_range.simps usable_untyped_range.simps atLeastAtMost_iff
                    atLeastatMost_subset_iff atLeastLessThan_iff
                    Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex
  show ?thesis
    apply (clarsimp simp:simpler_modify_def ko_wp_at'_def valid_def typ_at'_def)
    apply (case_tac ko,simp_all)
    apply (rename_tac arch_kernel_object)
    apply (case_tac arch_kernel_object,simp_all)
    apply (subst pspace_no_overlap'_def)
    apply (intro allI impI)
    apply (clarsimp split:if_splits)
     apply (drule(1) pspace_no_overlapD')
     apply (simp add:objBits_simps field_simps mask_def)
    apply (drule(1) pspace_no_overlapD')+
    apply (simp add:field_simps mask_def)
    done
qed

lemma koTypeOf_pte:
  "koTypeOf ko = ArchT PTET \<Longrightarrow> \<exists>pte. ko = KOArch (KOPTE pte)"
  apply (case_tac ko,simp_all)
  apply (rename_tac arch_kernel_object)
  apply (case_tac arch_kernel_object,simp_all)
  done

lemma placeNewObject_valid_arch_state:
  "\<lbrace>valid_arch_state' and
    pspace_no_overlap' ptr (objBitsKO (injectKOS val) + us) and
    pspace_aligned' and pspace_distinct' and
    K (is_aligned ptr (objBitsKO (injectKOS val) + us)) and
    K ( (objBitsKO (injectKOS val)+ us)< word_bits)\<rbrace>
   placeNewObject ptr val us
   \<lbrace>\<lambda>rv s. valid_arch_state' s\<rbrace>"
  apply (simp add:placeNewObject_def2 split_def)
  apply (rule createObjects'_wp_subst)
  apply (wp createObjects_valid_arch)
  apply clarsimp
  apply (intro conjI,simp)
  apply (erule(1) range_cover_full)
  done

lemma setCTE_updatePTType_commute:
  "monad_commute \<top> (setCTE src cte) (updatePTType p pt_t)"
  unfolding updatePTType_def
  apply (clarsimp simp: monad_commute_def)
  apply (clarsimp simp: setCTE_def setObject_def bind_assoc exec_gets exec_modify)
  apply (case_tac "lookupAround2 src (ksPSpace s)"; clarsimp simp: bind_assoc)
  apply (simp add: assert_opt_def bind_assoc simpler_updateObject_def
                   simpler_modify_def simpler_gets_def return_def split_def fail_def
              split: option.splits)
  apply (clarsimp simp: bind_def fail_def)
  apply (case_tac s, rename_tac arch mach, case_tac arch, simp)
  apply fastforce
  done

crunch updatePTType
  for cte_wp_at'[wp]: "\<lambda>s. Q (cte_wp_at' P p s)"
  and pspace_aligned'[wp]: pspace_aligned'
  and pspace_distinct'[wp]: pspace_distinct'

lemma createObject_setCTE_commute[Detype_R_2_assms]:
  "monad_commute
     (cte_wp_at' (\<lambda>_. True) src and
        pspace_aligned' and pspace_distinct' and
        pspace_no_overlap' ptr (Types_H.getObjectSize ty us) and
        valid_arch_state' and K (ptr \<noteq> src) and
        K (is_aligned ptr (Types_H.getObjectSize ty us)) and
        K (Types_H.getObjectSize ty us < word_bits))
     (RetypeDecls_H.createObject ty ptr us d)
     (setCTE src cte)"
  apply (rule commute_grab_asm)+
  apply (subgoal_tac "ptr && mask (Types_H.getObjectSize ty us) = 0")
   prefer 2
   apply (clarsimp simp: range_cover_def is_aligned_mask)
  apply (clarsimp simp: global.createObject_def)
  apply (case_tac ty,
         simp_all add: RISCV64_H.toAPIType_def)
        apply (rename_tac apiobject_type)
        apply (case_tac apiobject_type)
            apply (simp_all add:
                       RISCV64_H.getObjectSize_def apiGetObjectSize_def
                       tcbBlockSizeBits_def epSizeBits_def ntfnSizeBits_def
                       cteSizeBits_def)
            \<comment> \<open>Untyped\<close>
            apply (simp add: monad_commute_guard_imp[OF return_commute])
           \<comment> \<open>TCB\<close>
           apply (rule monad_commute_guard_imp[OF commute_commute])
            apply (rule monad_commute_split[OF monad_commute_split[OF commute_commute]])
                apply (rule return_commute)
               apply (rule setCTE_placeNewObject_commute)
              apply wp
             apply (rule curDomain_commute)
             apply (wpsimp simp: objBits_simps')+
          \<comment> \<open>EP, NTFN\<close>
          apply (rule monad_commute_guard_imp[OF commute_commute],
                 rule monad_commute_split[OF commute_commute[OF return_commute]],
                 rule setCTE_placeNewObject_commute,
                 (wpsimp simp: objBits_simps')+)+
        \<comment> \<open>CNode\<close>
        apply (rule monad_commute_guard_imp[OF commute_commute])
         apply (rule monad_commute_split)+
             apply (rule return_commute[THEN commute_commute])
            apply (rule setCTE_modify_gsCNode_commute[of \<top>])
           apply (rule hoare_triv[of \<top>])
           apply wp
          apply (rule setCTE_placeNewObject_commute)
         apply (wp|clarsimp simp: objBits_simps')+
       \<comment> \<open>Arch Objects\<close>
       apply ((rule monad_commute_guard_imp[OF commute_commute]
              , rule monad_commute_split[OF commute_commute[OF return_commute]]
              , clarsimp simp: RISCV64_H.createObject_def
                               placeNewDataObject_def bind_assoc
                         split del: if_split
              ,(rule monad_commute_split return_commute[THEN commute_commute]
                     setCTE_modify_gsUserPages_commute[of \<top>]
                     modify_wp[of "%_. \<top>"]
                     setCTE_doMachineOp_commute
                     setCTE_when_doMachineOp_commute
                     setCTE_placeNewObject_commute
                     setCTE_updatePTType_commute
                     monad_commute_if_weak_r
                 | wp placeNewObject_pspace_distinct'
                      placeNewObject_pspace_aligned'
                      placeNewObject_cte_wp_at'
                      placeNewObject_valid_arch_state
                 | erule is_aligned_weaken
                 | simp add: objBits_simps word_bits_def mult_2 add.assoc
                             pageBits_less_word_bits[unfolded word_bits_def, simplified])+)+)
  apply (simp add: bit_simps)
  done

lemma monad_commute_gsUntyped_updatePTType:
  "monad_commute \<top> (modify (\<lambda>s. s\<lparr>gsUntypedZeroRanges := f (gsUntypedZeroRanges s)\<rparr>))
                   (updatePTType ptr pt_t)"
  unfolding updatePTType_def
  apply (clarsimp simp: monad_commute_def exec_gets exec_modify bind_assoc)
  apply (clarsimp simp: return_def)
  apply (case_tac s, rename_tac arch mach, case_tac arch)
  apply fastforce
  done

lemma createObject_gsUntypedZeroRanges_commute[Detype_R_2_assms]:
  "monad_commute
     \<top>
     (RetypeDecls_H.createObject ty ptr us dev)
     (modify (\<lambda>s. s \<lparr> gsUntypedZeroRanges := f (gsUntypedZeroRanges s) \<rparr> ))"
  apply (simp add: global.createObject_def RISCV64_H.createObject_def
                   placeNewDataObject_def
                   placeNewObject_def2 bind_assoc fail_commute
                   return_commute toAPIType_def
              split: option.split apiobject_type.split object_type.split)
  apply (strengthen monad_commute_guard_imp[OF monad_commute_split[where P="\<top>" and Q="\<top>\<top>"],
          OF _ _ hoare_vcg_prop, THEN commute_commute]
      monad_commute_guard_imp[OF monad_commute_split[where P="\<top>" and Q="\<top>\<top>"],
          OF _ _ hoare_vcg_prop]
     | simp add: modify_commute createObjects_gsUntypedZeroRanges_commute'
                 createObjects_gsUntypedZeroRanges_commute'[THEN commute_commute]
                 return_commute return_commute[THEN commute_commute]
                 threadSet_gsUntypedZeroRanges_commute'[THEN commute_commute]
                 monad_commute_gsUntyped_updatePTType dmo_gsUntypedZeroRanges_commute
          split: option.split prod.split cong: if_cong)+
  apply (simp add: curDomain_def monad_commute_def exec_modify exec_gets)
  done

lemma createNewCaps_not_nc[Detype_R_2_assms]:
  "\<lbrace>\<top>\<rbrace>
   createNewCaps ty ptr n us d
   \<lbrace>\<lambda>r s. (\<forall>cap\<in>set r. cap \<noteq> capability.NullCap)\<rbrace>"
   unfolding createNewCaps_def Arch_createNewCaps_def
   by (wpsimp simp: Arch_createNewCaps_def split_del: if_split)+

end (* Arch *)

interpretation Detype_R_2?: Detype_R_2
proof goal_cases
  interpret Arch  .
  case 1 show ?case by (intro_locales; (unfold_locales; (fact Detype_R_2_assms)?)?)
qed

context Arch begin arch_global_naming

named_theorems Detype_R_3_assms

lemma createNewCaps_pspace_no_overlap'[Detype_R_3_assms]:
  "\<lbrace>\<lambda>s. range_cover ptr sz (Types_H.getObjectSize ty us) (Suc (Suc n)) \<and>
        pspace_aligned' s \<and> pspace_distinct' s \<and> pspace_no_overlap' ptr sz s \<and>
        ptr \<noteq> 0\<rbrace>
   createNewCaps ty ptr (Suc n) us d
   \<lbrace>\<lambda>r s. pspace_no_overlap'
             (ptr + (1 + of_nat n << Types_H.getObjectSize ty us))
             (Types_H.getObjectSize ty us) s\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp: createNewCaps_def)
  apply (subgoal_tac "pspace_no_overlap' (ptr + (1 + of_nat n << (Types_H.getObjectSize ty us)))
                                         (Types_H.getObjectSize ty us) s")
   prefer 2
   apply (rule pspace_no_overlap'_le[where sz = sz])
     apply (rule pspace_no_overlap'_tail)
         apply simp+
    apply (simp add:range_cover_def)
   apply (simp add:range_cover.sz(1)[where 'a=machine_word_len, folded word_bits_def])
  apply (rule_tac Q'="\<lambda>r. pspace_no_overlap' (ptr + (1 + of_nat n << Types_H.getObjectSize ty us))
                                              (Types_H.getObjectSize ty us) and
                           pspace_aligned' and pspace_distinct'" in hoare_strengthen_post)
   apply (case_tac ty)
         apply (simp_all add: apiGetObjectSize_def
                              RISCV64_H.toAPIType_def
                              RISCV64_H.getObjectSize_def objBits_simps objBits_defs
                              pageBits_def ptBits_def
                              createObjects_def)
        apply (rule hoare_pre)
         apply wpc
    apply (clarsimp simp: apiGetObjectSize_def  curDomain_def
                          RISCV64_H.toAPIType_def
                          RISCV64_H.getObjectSize_def objBits_simps objBits_defs
                          pageBits_def ptBits_def
                          createObjects_def Arch_createNewCaps_def
                    split: apiobject_type.splits
           | wp doMachineOp_psp_no_overlap createObjects'_pspace_no_overlap[where sz = sz]
                createObjects'_psp_aligned[where sz = sz] createObjects'_psp_distinct[where sz = sz]
                mapM_x_wp_inv
           | assumption)+
           apply (intro conjI range_cover_le[where n = "Suc n"] | simp)+
            apply ((simp add:objBits_simps pageBits_def range_cover_def word_bits_def)+)[5]
       by ((clarsimp simp: apiGetObjectSize_def bit_simps toAPIType_def
                           getObjectSize_def objBits_simps
                           createObjects_def Arch_createNewCaps_def unless_def
                     split: apiobject_type.splits
               | wp doMachineOp_psp_no_overlap createObjects'_pspace_no_overlap
                    createObjects'_psp_aligned createObjects'_psp_distinct
                    mapM_x_wp_inv
               | assumption | clarsimp simp: word_bits_def
               | intro conjI range_cover_le[where n = "Suc n"] range_cover.aligned)+)

lemma createNewCaps_ret_len[Detype_R_3_assms]:
  "\<lbrace>K (n < 2 ^ word_bits \<and> n \<noteq> 0)\<rbrace>
   createNewCaps ty ptr n us d
   \<lbrace>\<lambda>rv s. n = length rv\<rbrace>"
  including no_pre
  apply (rule hoare_name_pre_state)
  apply clarsimp
  apply (case_tac ty)
   apply (simp_all add:createNewCaps_def RISCV64_H.toAPIType_def)
    apply (rule hoare_pre)
     apply wpc
      apply ((wp+)|simp add:Arch_createNewCaps_def RISCV64_H.toAPIType_def
           unat_of_nat_minus_1
           [where 'a=machine_word_len, folded word_bits_def] |
          erule hoare_strengthen_post[OF createObjects_ret],clarsimp+ | intro conjI impI)+
       apply (rule hoare_pre,
          ((wp+)
              | simp add: Arch_createNewCaps_def toAPIType_def unat_of_nat_minus_1
              | erule hoare_strengthen_post[OF createObjects_ret],clarsimp+
              | intro conjI impI)+)+
   done

lemma createNewCaps_Cons[Detype_R_3_assms]:
  assumes cover:"range_cover ptr sz (Types_H.getObjectSize ty us) (Suc (Suc n))"
  and "valid_pspace' s" "valid_arch_state' s"
  and "pspace_no_overlap' ptr sz s"
  and "ptr \<noteq> 0"
  shows "createNewCaps ty ptr (Suc (Suc n)) us d s
 = (do x \<leftarrow> createNewCaps ty ptr (Suc n) us d;
      r \<leftarrow> RetypeDecls_H.createObject ty
             (((1 + of_nat n) << Types_H.getObjectSize ty us) + ptr) us d;
      return (x @ [r])
    od) s"
proof -
  have append :"[0.e.(1::machine_word) + of_nat n] = [0.e.of_nat n] @ [1 + of_nat n]"
     using cover
     apply -
     apply (frule range_cover_not_zero[rotated])
      apply simp
     apply (frule range_cover.unat_of_nat_n)
     apply (drule range_cover_le[where n = "Suc n"])
      apply simp
     apply (frule range_cover_not_zero[rotated])
      apply simp
     apply (frule range_cover.unat_of_nat_n)
     apply (subst upto_enum_red'[where X = "2 + of_nat n",simplified])
      apply (simp add:field_simps word_le_sub1)
     apply clarsimp
     apply (subst upto_enum_red'[where X = "1 + of_nat n",simplified])
      apply (simp add:field_simps word_le_sub1)
     apply simp
     done

  have conj_impI:
    "\<And>A B C. \<lbrakk>C;C\<Longrightarrow>B\<rbrakk> \<Longrightarrow> B \<and> C"
    by simp

  have suc_of_nat: "(1::machine_word) + of_nat n = of_nat (1 + n)"
     by simp

  have gsUserPages_update[simp]:
    "\<And>f. (\<lambda>ks. ks \<lparr>gsUserPages := f (gsUserPages ks)\<rparr>) = gsUserPages_update f"
    by (rule ext) simp
  have gsCNodes_update[simp]:
    "\<And>f. (\<lambda>ks. ks \<lparr>gsCNodes := f (gsCNodes ks)\<rparr>) = gsCNodes_update f"
    by (rule ext) simp
  have ksArchState_update[simp]:
    "\<And>f. (\<lambda>ks. ks \<lparr>ksArchState := f (ksArchState ks)\<rparr>) = ksArchState_update f"
    by (rule ext) simp

  have if_eq[simp]:
    "!!x a b pgsz. (if a = ptr + (1 + of_nat n << b) then Some pgsz
             else if a \<in> (\<lambda>n. ptr + (n << b)) ` {x. x \<le> of_nat n}
                  then Just pgsz else x a) =
            (if a \<in> (\<lambda>n. ptr + (n << b)) ` {x. x \<le> 1 + of_nat n}
             then Just pgsz else x a)"
    apply (simp only: Just_def if3_fold2)
    apply (rule_tac x="x a" in fun_cong)
    apply (rule arg_cong2[where f=If, OF _ refl])
    apply (subgoal_tac "{x. x \<le> (1::machine_word) + of_nat n} =
                    {1 + of_nat n} \<union> {x. x \<le> of_nat n}")
     apply (simp add: add.commute)
    apply safe
     apply (clarsimp simp: word_le_less_eq[of _ "1 + of_nat n"])
     apply (metis plus_one_helper add.commute)
    using cover
    apply -
    apply (drule range_cover_le[where n = "Suc n"], simp)
    apply (simp only: suc_of_nat word_le_nat_alt Suc_eq_plus1)
    apply (frule range_cover.unat_of_nat_n)
    apply simp
    apply (drule range_cover_le[where n=n], simp)
    apply (frule range_cover.unat_of_nat_n, simp)
    done

  show ?thesis
    using assms
    apply (clarsimp simp:valid_pspace'_def)
    apply (frule range_cover.aligned)
    apply (frule(3) pspace_no_overlap'_tail)
     apply simp
    apply (drule_tac ptr = "ptr + x" for x
           in pspace_no_overlap'_le[where sz' = "Types_H.getObjectSize ty us"])
      apply (simp add:range_cover_def word_bits_def)
     apply (erule range_cover.sz(1)[where 'a=machine_word_len, folded word_bits_def])
    apply (simp add: createNewCaps_def)
    apply (case_tac ty)
          apply (simp add: RISCV64_H.toAPIType_def Arch_createNewCaps_def)
          apply (rename_tac apiobject_type)
          apply (case_tac apiobject_type)
              apply (simp_all add: bind_assoc RISCV64_H.toAPIType_def)
              \<comment> \<open>Untyped\<close>
              apply (simp add: bind_assoc RISCV64_H.getObjectSize_def
                               mapM_def sequence_def Retype_H.createObject_def
                               RISCV64_H.toAPIType_def
                               createObjects_def RISCV64_H.createObject_def
                               Arch_createNewCaps_def comp_def
                               apiGetObjectSize_def shiftl_t2n field_simps
                               shiftL_nat mapM_x_def sequence_x_def append
                               fromIntegral_def integral_inv[unfolded Fun.comp_def])
             \<comment> \<open>TCB\<close>
             apply (simp add: bind_assoc RISCV64_H.getObjectSize_def
                              mapM_def sequence_def Retype_H.createObject_def
                              RISCV64_H.toAPIType_def objBitsKO_def
                              createObjects_def RISCV64_H.createObject_def
                              Arch_createNewCaps_def comp_def append
                              apiGetObjectSize_def shiftl_t2n field_simps
                              shiftL_nat fromIntegral_def integral_inv[unfolded Fun.comp_def])
             apply (subst curDomain_createObjects'_comm)
             apply (subst curDomain_twice_simp)
             apply (simp add: monad_eq_simp_state)
             apply (intro conjI; clarsimp simp: in_monad)
               apply ((fastforce simp: curDomain_def simpler_gets_def return_def placeNewObject_def2
                                       field_simps shiftl_t2n bind_assoc objBits_simps in_monad
                                       createObjects_Cons[where
                                         val="KOTCB (tcbDomain_update (\<lambda>_. ksCurDomain s) makeObject)"
                                         and s=s, simplified objBitsKO_def])+)[2]
             apply ((clarsimp simp: curDomain_def simpler_gets_def return_def split_def bind_def
                                   field_simps shiftl_t2n bind_assoc objBits_simps placeNewObject_def2
                                   createObjects_Cons[where
                                     val="KOTCB (tcbDomain_update (\<lambda>_. ksCurDomain s) makeObject)"
                                     and s=s, simplified objBitsKO_def])+)[1]
            \<comment> \<open>EP, NTFN\<close>
            apply (((simp add: RISCV64_H.getObjectSize_def
                               mapM_def sequence_def Retype_H.createObject_def
                               RISCV64_H.toAPIType_def
                               createObjects_def RISCV64_H.createObject_def
                               Arch_createNewCaps_def comp_def
                               apiGetObjectSize_def shiftl_t2n field_simps
                               shiftL_nat mapM_x_def sequence_x_def append
                               fromIntegral_def integral_inv[unfolded Fun.comp_def])+,
                     subst monad_eq, rule createObjects_Cons,
                     (simp add: field_simps shiftl_t2n bind_assoc pageBits_def
                                objBits_simps' placeNewObject_def2)+)+)[2]

          apply (in_case "CapTableObject")
          apply (simp add: bind_assoc
                           RISCV64_H.getObjectSize_def
                           mapM_def sequence_def Retype_H.createObject_def
                           RISCV64_H.toAPIType_def
                           createObjects_def RISCV64_H.createObject_def
                           Arch_createNewCaps_def comp_def
                           apiGetObjectSize_def shiftl_t2n field_simps
                           shiftL_nat mapM_x_def sequence_x_def append
                           fromIntegral_def integral_inv[unfolded Fun.comp_def])+
          apply (subst monad_eq, rule createObjects_Cons)
                apply (simp add: field_simps shiftl_t2n bind_assoc pageBits_def
                                 objBits_simps placeNewObject_def2)+
          apply (subst gsCNodes_update gsCNodes_upd_createObjects'_comm)+
          apply (simp add: modify_modify_bind)
          apply (rule fun_cong[where x=s])
          apply (rule arg_cong_bind1)+
          apply (rule arg_cong_bind[OF _ refl])
          apply (rule arg_cong[where f=modify, OF ext], simp)
          apply (rule arg_cong2[where f=gsCNodes_update, OF ext refl])
          apply (rule ext)
          apply simp

         apply (in_case "HugePageObject")
         apply (simp add: Arch_createNewCaps_def
                          Retype_H.createObject_def createObjects_def bind_assoc
                          RISCV64_H.toAPIType_def
                          RISCV64_H.createObject_def placeNewDataObject_def)
         apply (intro conjI impI)
          apply (subst monad_eq, rule createObjects_Cons)
                apply (simp_all add: field_simps shiftl_t2n pageBits_def
                                     getObjectSize_def objBits_simps)[6]
          apply (simp add: bind_assoc placeNewObject_def2 objBits_simps
                           getObjectSize_def bit_simps
                           add.commute append mapM_x_append mapM_x_singleton)
          apply ((subst gsUserPages_update gsCNodes_update
                        gsUserPages_upd_createObjects'_comm
                        monad_commute_simple'[OF map_dmo'_createObjects'_comm]
                        monad_commute_simple'[OF dmo'_gsUserPages_upd_map_commute]
                     | simp add: modify_modify_bind o_def)+)[1]

         apply (subst monad_eq, rule createObjects_Cons)
               apply (simp_all add: field_simps shiftl_t2n pageBits_def
                                    getObjectSize_def objBits_simps)[6]
         apply (simp add: bind_assoc placeNewObject_def2 objBits_simps
                          getObjectSize_def
                          pageBits_def add.commute append mapM_x_append mapM_x_singleton)
         apply (subst gsUserPages_update gsCNodes_update
                      gsUserPages_upd_createObjects'_comm
                      monad_commute_simple'[OF map_dmo'_createObjects'_comm]
                      monad_commute_simple'[OF dmo'_gsUserPages_upd_map_commute]
                    | simp add: modify_modify_bind o_def)+

        apply (in_case "VSpaceObject")
        apply (simp add: Arch_createNewCaps_def Retype_H.createObject_def createObjects_def
                         bind_assoc RISCV64_H.toAPIType_def RISCV64_H.createObject_def)
        apply (subst monad_eq, rule createObjects_Cons)
              apply ((simp add: field_simps shiftl_t2n
                                getObjectSize_def bit_simps objBits_simps ptBits_def)+)[6]
        apply (simp add: bind_assoc placeNewObject_def2)
        apply (simp add: field_simps updatePTType_def bind_assoc gets_modify_def
                         getObjectSize_def placeNewObject_def2 objBits_simps append mapM_x_append
                         mapM_x_singleton)
        apply (subst ksArchState_update ksArchState_upd_createObjects'_comm
                     monad_commute_simple'[OF map_dmo'_createObjects'_comm]
                     monad_commute_simple'[OF map_dmo'_ksArchState_upd_comm]
               | simp add: modify_modify_bind o_def
               | simp only: o_def cong: if_cong)+
        apply (rule bind_apply_cong, simp)
        apply (rule bind_apply_cong, simp)
        apply (rule monad_eq_split_tail, simp)
        apply (rule fun_cong, rule arg_cong[where f=modify])
        apply (simp flip: if_eq)
        apply (simp cong: if_cong del: if_eq)
        apply (rule ext)
        apply (rename_tac s', case_tac s')
        apply (rename_tac ksArch ksMachine, case_tac ksArch)
        apply fastforce

       apply (in_case "SmallPageObject")
       apply (simp add: Arch_createNewCaps_def
                        Retype_H.createObject_def createObjects_def bind_assoc
                        toAPIType_def
                        RISCV64_H.createObject_def placeNewDataObject_def)
       apply (intro conjI impI)
        apply (subst monad_eq, rule createObjects_Cons)
              apply (simp_all add: field_simps shiftl_t2n bit_simps
                                   getObjectSize_def objBits_simps)[6]
        apply (simp add: bind_assoc placeNewObject_def2 objBits_simps bit_simps
                         getObjectSize_def add.commute append mapM_x_append mapM_x_singleton)
        apply ((subst gsUserPages_update gsCNodes_update
                      gsUserPages_upd_createObjects'_comm
                      monad_commute_simple'[OF map_dmo'_createObjects'_comm]
                      monad_commute_simple'[OF dmo'_gsUserPages_upd_map_commute]
                   | simp add: modify_modify_bind o_def)+)[1]
       apply (subst monad_eq, rule createObjects_Cons)
             apply (simp_all add: field_simps shiftl_t2n pageBits_def
                                 RISCV64_H.getObjectSize_def objBits_simps)[6]
       apply (simp add: bind_assoc placeNewObject_def2 objBits_simps
                         RISCV64_H.getObjectSize_def
                        pageBits_def add.commute append mapM_x_append mapM_x_singleton)
       apply (subst gsUserPages_update gsCNodes_update
                    gsUserPages_upd_createObjects'_comm
                    monad_commute_simple'[OF map_dmo'_createObjects'_comm]
                    monad_commute_simple'[OF dmo'_gsUserPages_upd_map_commute]
              | simp add: modify_modify_bind o_def)+

      apply (in_case "LargePageObject")
      apply (simp add: Arch_createNewCaps_def
                       Retype_H.createObject_def createObjects_def bind_assoc
                       toAPIType_def RISCV64_H.createObject_def placeNewDataObject_def)
      apply (intro conjI impI)
       apply (subst monad_eq, rule createObjects_Cons)
             apply (simp_all add: field_simps shiftl_t2n pageBits_def
                        getObjectSize_def objBits_simps)[6]
       apply (simp add: bind_assoc placeNewObject_def2 objBits_simps bit_simps
                        getObjectSize_def add.commute append mapM_x_append mapM_x_singleton)
       apply ((subst gsUserPages_update gsCNodes_update
                     gsUserPages_upd_createObjects'_comm
                     monad_commute_simple'[OF map_dmo'_createObjects'_comm]
                     monad_commute_simple'[OF dmo'_gsUserPages_upd_map_commute]
               | simp add: modify_modify_bind o_def)+)[1]
      apply (subst monad_eq, rule createObjects_Cons)
            apply (simp_all add: field_simps shiftl_t2n pageBits_def
                       RISCV64_H.getObjectSize_def objBits_simps)[6]
      apply (simp add: bind_assoc placeNewObject_def2 objBits_simps
                       getObjectSize_def bit_simps add.commute append mapM_x_append mapM_x_singleton)
      apply (subst gsUserPages_update gsCNodes_update
                   gsUserPages_upd_createObjects'_comm
                   monad_commute_simple'[OF map_dmo'_createObjects'_comm]
                   monad_commute_simple'[OF dmo'_gsUserPages_upd_map_commute]
             | simp add: modify_modify_bind o_def)+

     apply (in_case "PageTableObject")
     apply (simp add: Arch_createNewCaps_def Retype_H.createObject_def createObjects_def bind_assoc
                      RISCV64_H.toAPIType_def RISCV64_H.createObject_def)
     apply (subst monad_eq, rule createObjects_Cons)
           apply ((simp add: field_simps shiftl_t2n
                             getObjectSize_def bit_simps objBits_simps ptBits_def)+)[6]
     apply (simp add: bind_assoc placeNewObject_def2)
     apply (simp add: field_simps updatePTType_def bind_assoc gets_modify_def
                      getObjectSize_def placeNewObject_def2 objBits_simps append mapM_x_append
                      mapM_x_singleton)
     apply (subst ksArchState_update ksArchState_upd_createObjects'_comm
                  monad_commute_simple'[OF map_dmo'_createObjects'_comm]
                  monad_commute_simple'[OF map_dmo'_ksArchState_upd_comm]
            | simp add: modify_modify_bind o_def
            | simp only: o_def cong: if_cong)+
     apply (rule bind_apply_cong, simp)
     apply (rule bind_apply_cong, simp)
     apply (rule monad_eq_split_tail, simp)
     apply (rule fun_cong, rule arg_cong[where f=modify])
     apply (simp flip: if_eq)
     apply (simp cong: if_cong del: if_eq)
     apply (rule ext)
     apply (rename_tac s', case_tac s')
     apply (rename_tac ksArch ksMachine, case_tac ksArch)
     apply fastforce
    apply (in_case "VCPUObject")
    apply (simp add: Arch_createNewCaps_def Retype_H.createObject_def
                     createObjects_def bind_assoc RISCV64_H.toAPIType_def
                     RISCV64_H.createObject_def)
    apply (subst monad_eq, rule createObjects_Cons)
          apply ((simp add: field_simps shiftl_t2n getObjectSize_def
                            bit_simps objBits_simps ptBits_def)+)[6]
    apply (simp add: bind_assoc placeNewObject_def2)
    apply (simp add: add_ac bit_simps getObjectSize_def objBits_simps append)
    done
qed

lemma createObject_def2[Detype_R_3_assms]:
  "(RetypeDecls_H.createObject ty ptr us dev >>= (\<lambda>x. return [x])) =
   createNewCaps ty ptr (Suc 0) us dev"
  apply (clarsimp simp: global.createObject_def createNewCaps_def placeNewObject_def2)
  apply (case_tac ty; simp add: toAPIType_def)
      defer
      apply ((clarsimp simp: Arch_createNewCaps_def createObjects_def shiftL_nat
                             RISCV64_H.createObject_def placeNewDataObject_def
                             placeNewObject_def2 objBits_simps bind_assoc
                             clearMemory_def clearMemoryVM_def fun_upd_def[symmetric]
                             word_size mapM_x_singleton storeWordVM_def
                             updatePTType_def gets_modify_def)+)[6]
  apply (rename_tac apiobject_type)
  apply (case_tac apiobject_type)
      apply (clarsimp simp: Arch_createNewCaps_def createObjects_def shiftL_nat
                            RISCV64_H.createObject_def placeNewObject_def2 objBits_simps bind_assoc
                            clearMemory_def clearMemoryVM_def word_size mapM_x_singleton
                            storeWordVM_def)+
  done

crunch updatePTType
  for pspace_no_overlap'[wp]: "pspace_no_overlap' p n"

lemma ArchCreateObject_pspace_no_overlap'[Detype_R_3_assms]:
  "\<lbrace>\<lambda>s. pspace_no_overlap'
          (ptr + (of_nat n << APIType_capBits ty userSize)) sz s \<and>
        pspace_aligned' s \<and> pspace_distinct' s \<and>
        range_cover ptr sz (APIType_capBits ty userSize) (n + 2) \<and> ptr \<noteq> 0\<rbrace>
   Arch.createObject ty
     (ptr + (of_nat n << APIType_capBits ty userSize)) userSize d
   \<lbrace>\<lambda>archCap. pspace_no_overlap'
                (ptr + (1 + of_nat n << APIType_capBits ty userSize)) sz\<rbrace>"
  supply if_split[split del]
  apply (clarsimp simp:RISCV64_H.createObject_def)
  apply wpc
         apply (wp doMachineOp_psp_no_overlap
                   createObjects'_pspace_no_overlap2
                   createObjects'_psp_aligned[where sz = sz]
                   createObjects'_psp_distinct[where sz = sz]
                | simp add: placeNewObject_def2 word_shiftl_add_distrib
                | simp add: placeNewObject_def2 word_shiftl_add_distrib
                | simp add: placeNewDataObject_def placeNewObject_def2 word_shiftl_add_distrib
                            field_simps
                | clarsimp simp add: add.assoc[symmetric],
                  wp createObjects'_pspace_no_overlap2[where n =0 and sz = sz,simplified]
                | clarsimp simp: APIType_capBits_def objBits_simps pageBits_def
                                APIType_capBits_gen_def)+
  apply (clarsimp simp: conj_comms)
  apply (frule(1) range_cover_no_0[where p = n])
   apply simp
  apply (subgoal_tac "is_aligned (ptr + (of_nat n << APIType_capBits ty userSize))
                                 (APIType_capBits ty userSize) ")
   prefer 2
   apply (rule aligned_add_aligned[OF range_cover.aligned],assumption)
    apply (simp add:is_aligned_shiftl_self range_cover_sz')
   apply (simp add: APIType_capBits_def)
  apply (frule range_cover_offset[rotated,where p = n])
   apply simp+
  apply (frule range_cover_le[where n = "Suc (Suc 0)"])
   apply simp
  apply (frule pspace_no_overlap'_le2)
    apply (rule range_cover_compare_offset)
      apply simp+
   apply (clarsimp simp:word_shiftl_add_distrib
              ,simp add:field_simps)
   apply (clarsimp simp:add.assoc[symmetric])
   apply (rule range_cover_tail_mask[where n =0,simplified])
    apply (drule range_cover_offset[rotated,where p = n])
     apply simp
    apply (clarsimp simp:shiftl_t2n field_simps)
    apply (metis numeral_2_eq_2)
   apply (simp add:shiftl_t2n field_simps)
  apply (intro conjI allI)
      apply (clarsimp simp: field_simps word_bits_conv
                            APIType_capBits_def shiftl_t2n objBits_simps bit_simps
                      split: if_split
             | rule conjI | erule range_cover_le,simp)+
  done

lemma createObject_pspace_aligned_distinct':
  "\<lbrace>pspace_aligned' and K (is_aligned ptr (APIType_capBits ty us))
   and pspace_distinct' and pspace_no_overlap' ptr (APIType_capBits ty us)
   and K (ty = APIObjectType apiobject_type.CapTableObject \<longrightarrow> us < 28)\<rbrace>
  createObject ty ptr us d
  \<lbrace>\<lambda>xa s. pspace_aligned' s \<and> pspace_distinct' s\<rbrace>"
  (* FIXME: work around warning due to vcpuBits_def being in both bit_simps and objBits_simps' *)
  supply vcpuBits_def[bit_simps del]
  apply (rule hoare_pre)
   apply (wp placeNewObject_pspace_aligned' unless_wp
             placeNewObject_pspace_distinct'
          | simp add: RISCV64_H.createObject_def Retype_H.createObject_def gen_objBits_simps
                      curDomain_def placeNewDataObject_def
                 split del: if_split
          | wpc | intro conjI impI)+
                      apply (auto simp: APIType_capBits_def objBits_simps' bit_simps word_bits_def
                                        RISCV64_H.toAPIType_def
                                  split: RISCV64_H.object_type.splits apiobject_type.splits)
  done

end (* Arch *)

interpretation Detype_R_3?: Detype_R_3
proof goal_cases
  interpret Arch  .
  case 1 show ?case by (intro_locales; (unfold_locales; (fact Detype_R_3_assms)?)?)
qed

end
