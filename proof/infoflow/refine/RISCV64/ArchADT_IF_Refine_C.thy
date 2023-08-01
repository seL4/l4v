(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchADT_IF_Refine_C
imports ADT_IF_Refine_C
begin

context kernel_m begin

named_theorems ADT_IF_Refine_assms

lemma handleInterrupt_ccorres[ADT_IF_Refine_assms]:
  "ccorres (K dc \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
           (invs')
           (UNIV)
           []
           (handleEvent Interrupt)
           (handleInterruptEntry_C_body_if)"
proof -
  show ?thesis
  apply (rule ccorres_guard_imp2)
   apply (simp add: handleEvent_def minus_one_norm handleInterruptEntry_C_body_if_def)
   apply (clarsimp simp: liftE_def bind_assoc)
   apply (rule ccorres_rhs_assoc)
   apply (ctac (no_vcg) add: getActiveIRQ_ccorres)
    apply (rule ccorres_Guard_Seq)
    apply wpc
     apply (simp add: ccorres_cond_empty_iff)
     apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg)
     apply (rule allI, rule conseqPre, vcg)
     apply (clarsimp simp: return_def)
    apply (clarsimp simp: ucast_not_helper ccorres_cond_univ_iff ucast_ucast_a is_down)
    apply (ctac (no_vcg) add: handleInterrupt_ccorres)
     apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg)
     apply (rule allI, rule conseqPre, vcg)
     apply (clarsimp simp: return_def)
    apply wp
   apply (rule_tac Q="\<lambda>rv s. invs' s \<and> (\<forall>x. rv = Some x \<longrightarrow> x \<le> maxIRQ)" in hoare_post_imp)
    apply (clarsimp simp: non_kernel_IRQs_def)
   apply (wp getActiveIRQ_le_maxIRQ | simp)+
  apply (clarsimp simp: invs'_def valid_state'_def)
  done
qed

lemma handleInvocation_ccorres'[ADT_IF_Refine_assms]:
  "ccorres (K dc \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and arch_extras and
        ct_active' and sch_act_simple and
        (\<lambda>s. \<forall>x. ksCurThread s \<notin> set (ksReadyQueues s x)))
       (UNIV \<inter> {s. isCall_' s = from_bool isCall}
             \<inter> {s. isBlocking_' s = from_bool isBlocking}) []
       (handleInvocation isCall isBlocking) (Call handleInvocation_'proc)"
  apply (simp only: arch_extras_def pred_top_right_neutral)
  apply (rule handleInvocation_ccorres)
  done

definition
  "ptable_rights_s'' s \<equiv> ptable_rights (cur_thread (cstate_to_A s)) (cstate_to_A s)"

definition
  "ptable_lift_s'' s \<equiv> ptable_lift (cur_thread (cstate_to_A s)) (cstate_to_A s)"

definition
  "ptable_attrs_s'' s \<equiv> ptable_attrs (cur_thread (cstate_to_A s)) (cstate_to_A s)"

definition
  "ptable_xn_s'' s \<equiv> \<lambda>addr. Execute \<notin> ptable_attrs_s'' s addr"

definition
  doMachineOp_C :: "(machine_state, 'a) nondet_monad \<Rightarrow> (cstate, 'a) nondet_monad"
where
 "doMachineOp_C mop \<equiv>
  do
    ms \<leftarrow> gets (\<lambda>s. phantom_machine_state_' (globals s));
    (r, ms') \<leftarrow> select_f (mop ms);
    modify (\<lambda>s. s \<lparr>globals := globals s \<lparr> phantom_machine_state_' := ms' \<rparr>\<rparr>);
    return r
  od"

definition doUserOp_C_if
  :: "user_transition_if \<Rightarrow> user_context \<Rightarrow> (cstate, (event option \<times> user_context)) nondet_monad"
   where
  "doUserOp_C_if uop tc \<equiv>
   do
      pr \<leftarrow> gets ptable_rights_s'';
      pxn \<leftarrow> gets (\<lambda>s x. pr x \<noteq> {} \<and> ptable_xn_s'' s x);
      pl \<leftarrow> gets (\<lambda>s. restrict_map (ptable_lift_s'' s) {x. pr x \<noteq> {}});
      allow_read \<leftarrow> return {y. \<exists>x. pl x = Some y \<and> AllowRead \<in> pr x};
      allow_write \<leftarrow> return {y. \<exists>x. pl x = Some y \<and> AllowWrite \<in> pr x};
      t \<leftarrow> gets (\<lambda>s. cur_thread (cstate_to_A s));
      um \<leftarrow> gets (\<lambda>s. user_mem_C (globals s) \<circ> ptrFromPAddr);
      dm \<leftarrow> gets (\<lambda>s. device_mem_C (globals s) \<circ> ptrFromPAddr);
      ds \<leftarrow> gets (\<lambda>s. device_state (phantom_machine_state_' (globals s)));
      assert (dom (um \<circ> addrFromPPtr) \<subseteq> - dom ds);
      assert (dom (dm \<circ> addrFromPPtr) \<subseteq> dom ds);
      u \<leftarrow> return (uop t pl pr pxn (tc, um |` allow_read, (ds \<circ> ptrFromPAddr)|` allow_read));
      assert (u \<noteq> {});
      (e,(tc',um',ds')) \<leftarrow> select u;
      setUserMem_C ((um' |` allow_write \<circ> addrFromPPtr) |` (- dom ds));
      setDeviceState_C ((ds' |` allow_write \<circ> addrFromPPtr) |` dom ds);
      return (e,tc')
   od"

lemma corres_underlying_split4:
  "(\<And>a b c d. corres_underlying srel nf nf' rrel (Q a b c d) (Q' a b c d) (f a b c d) (f' a b c d))
   \<Longrightarrow> corres_underlying srel nf nf' rrel (case x of (a,b,c,d) \<Rightarrow> Q a b c d)
                                          (case x of (a,b,c,d) \<Rightarrow> Q' a b c d)
                                          (case x of (a,b,c,d) \<Rightarrow> f a b c d)
                                          (case x of (a,b,c,d) \<Rightarrow> f' a b c d)"
  by (cases x; simp)

lemma do_user_op_if_C_corres[ADT_IF_Refine_assms]:
   "corres_underlying rf_sr False False (=)
   (invs' and ex_abs einvs and (\<lambda>_. uop_nonempty f)) \<top>
   (doUserOp_if f tc) (doUserOp_C_if f tc)"
  apply (rule corres_gen_asm)
  apply (simp add: doUserOp_if_def doUserOp_C_if_def uop_nonempty_def del: split_paired_All)
  apply (rule corres_gets_same)
    apply (clarsimp simp: absKState_crelation ptable_rights_s'_def ptable_rights_s''_def
           rf_sr_def  cstate_relation_def Let_def cstate_to_H_correct)
   apply simp
  apply (rule corres_gets_same)
    apply (clarsimp simp: ptable_xn_s'_def ptable_xn_s''_def ptable_attrs_s_def
                          absKState_crelation ptable_attrs_s'_def ptable_attrs_s''_def  rf_sr_def)
   apply simp
  apply (rule corres_gets_same)
    apply (clarsimp simp: absKState_crelation curthread_relation ptable_lift_s'_def ptable_lift_s''_def
                         ptable_lift_s_def rf_sr_def)
   apply simp
  apply (simp add: getCurThread_def)
  apply (rule corres_gets_same)
    apply (simp add: absKState_crelation rf_sr_def)
   apply simp
  apply (rule corres_gets_same)
    apply (rule fun_cong[where x=ptrFromPAddr])
    apply (rule_tac f=comp in arg_cong)
    apply (rule user_mem_C_relation[symmetric])
     apply (simp add: rf_sr_def cstate_relation_def Let_def cpspace_relation_def)
    apply fastforce
   apply simp
  apply (rule corres_gets_same)
    apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                          cpspace_relation_def)
    apply (drule device_mem_C_relation[symmetric])
     apply fastforce
    apply (simp add: comp_def)
   apply simp
  apply (rule corres_gets_same)
    apply (clarsimp simp: cstate_relation_def rf_sr_def
                          Let_def cmachine_state_relation_def)
   apply simp
  apply (rule corres_guard_imp)
    apply (rule_tac P=\<top> and P'=\<top> and r'="(=)" in corres_split)
       apply (clarsimp simp add: corres_underlying_def fail_def
                                 assert_def return_def
                          split: if_splits)
      apply simp
      apply (rule_tac P=\<top> and P'=\<top> and r'="(=)" in corres_split)
         apply (clarsimp simp add: corres_underlying_def fail_def
                                   assert_def return_def
                            split: if_splits)
        apply simp
        apply (rule_tac r'="(=)" in corres_split[OF corres_select])
           apply clarsimp
          apply simp
          apply (rule corres_underlying_split4)
          apply (rule corres_split[OF user_memory_update_corres_C])
            apply (rule corres_split[OF device_update_corres_C])
              apply (wp | simp)+
   apply (clarsimp simp:  ex_abs_def restrict_map_def invs_pspace_aligned'
                          invs_pspace_distinct' ptable_lift_s'_def ptable_rights_s'_def
                  split: if_splits)
   apply (drule ptable_rights_imp_UserData[rotated -1])
       apply ((fastforce | intro conjI)+)[4]
   apply (clarsimp simp: user_mem'_def device_mem'_def dom_def split: if_splits)
   apply fastforce
  apply (clarsimp simp add: invs'_def valid_state'_def valid_pspace'_def ex_abs_def)
  done

lemma check_active_irq_corres_C[ADT_IF_Refine_assms]:
  "corres_underlying rf_sr False False (=) \<top> \<top>
                     (checkActiveIRQ_if tc) (checkActiveIRQ_C_if tc)"
  apply (simp add: checkActiveIRQ_if_def checkActiveIRQ_C_if_def)
  apply (simp add: getActiveIRQ_C_def)
  apply (subst bind_assoc[symmetric])
  apply (rule corres_guard_imp)
    apply (rule corres_split[where r'="\<lambda>a c. case a of None \<Rightarrow> c = ucast irqInvalid
                                                                | Some x \<Rightarrow> c = ucast x \<and> c \<noteq> ucast irqInvalid",
                                        OF ccorres_corres_u_xf])
        apply (rule ccorres_guard_imp)
          apply (rule ccorres_rel_imp, rule ccorres_guard_imp)
             apply (rule getActiveIRQ_ccorres)
            apply simp+
       apply (rule no_fail_dmo')
       apply (rule no_fail_getActiveIRQ)
      apply (rule corres_trivial, clarsimp split: if_split option.splits)
     apply wp+
   apply simp+
  apply fastforce
  done

lemma obs_cpspace_user_data_relation[ADT_IF_Refine_assms]:
  "\<lbrakk>pspace_aligned' bd;pspace_distinct' bd;
    cpspace_user_data_relation (ksPSpace bd) (underlying_memory (ksMachineState bd)) hgs\<rbrakk>
   \<Longrightarrow> cpspace_user_data_relation (ksPSpace bd) (underlying_memory (observable_memory (ksMachineState bd) (user_mem' bd))) hgs"
   apply (clarsimp simp: cmap_relation_def dom_heap_to_user_data)
   apply (drule bspec,fastforce)
   apply (clarsimp simp: cuser_user_data_relation_def observable_memory_def
                         heap_to_user_data_def map_comp_def Let_def
                  split: option.split_asm)
   apply (drule_tac x = off in spec)
   apply (subst option_to_0_user_mem')
   apply (subst map_option_byte_to_word_heap)
    apply (clarsimp simp: projectKO_opt_user_data pointerInUserData_def field_simps
                   split: kernel_object.split_asm option.split_asm)
    apply (frule(1) pspace_alignedD')
    apply (subst neg_mask_add_aligned)
      apply (simp add: objBits_simps)
     apply (simp add: word_less_nat_alt)
     apply (rule le_less_trans[OF unat_plus_gt])
     apply (subst add.commute)
     apply (subst unat_mult_simple)
      apply (simp add: word_bits_def)
      apply (rule less_le_trans[OF unat_lt2p])
      apply simp
     apply simp
    apply (rule nat_add_offset_less [where n = 3, simplified])
      apply simp
     apply (rule unat_lt2p)
    apply (simp add: pageBits_def objBits_simps)
   apply (frule(1) pspace_distinctD')
   apply (clarsimp simp: obj_at'_def typ_at'_def ko_wp_at'_def objBits_simps)
  apply simp
  done

end


sublocale kernel_m \<subseteq> ADT_IF_Refine_1?: ADT_IF_Refine_1 _ _ _ doUserOp_C_if
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact ADT_IF_Refine_assms)?)
qed

end
