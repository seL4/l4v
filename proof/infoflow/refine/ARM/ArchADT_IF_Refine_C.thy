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
  "ccorres (K dc \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_') (invs') (UNIV) []
           (handleEvent Interrupt) (handleInterruptEntry_C_body_if)"
  apply (rule ccorres_guard_imp2)
   apply (simp add: handleEvent_def minus_one_norm handleInterruptEntry_C_body_if_def)
   apply (rule ccorres_add_return2)
   apply (ctac (no_vcg) add: checkInterrupt_ccorres)
    apply (rule_tac R="\<lambda>_. rv = Inr ()" in ccorres_return[where R'=UNIV])
    apply (rule conseqPre, vcg)
    apply (clarsimp simp: return_def)
   apply (simp add: liftE_def)
   apply wpsimp
  apply clarsimp
  done

lemma handleInvocation_ccorres'[ADT_IF_Refine_assms]:
  "ccorres (K dc \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and arch_extras and ct_active' and sch_act_simple)
       (UNIV \<inter> {s. isCall_' s = from_bool isCall}
             \<inter> {s. isBlocking_' s = from_bool isBlocking}) []
       (handleInvocation isCall isBlocking) (Call handleInvocation_'proc)"
  apply (simp only: arch_extras_def)
  apply (rule handleInvocation_ccorres)
  done

definition
  "ptable_rights_s'' s \<equiv> ptable_rights (cur_thread (cstate_to_A s)) (cstate_to_A s)"

definition
  "ptable_lift_s'' s \<equiv> ptable_lift (cur_thread (cstate_to_A s)) (cstate_to_A s)"

definition
  "ptable_attrs_s'' s \<equiv> ptable_attrs (cur_thread (cstate_to_A s)) (cstate_to_A s)"

definition
  "ptable_xn_s'' s \<equiv> \<lambda>addr. XNever \<in> ptable_attrs_s'' s addr"

definition doMachineOp_C :: "(machine_state, 'a) nondet_monad \<Rightarrow> (cstate, 'a) nondet_monad" where
 "doMachineOp_C mop \<equiv>
  do
    ms \<leftarrow> gets (\<lambda>s. phantom_machine_state_' (globals s));
    (r, ms') \<leftarrow> select_f (mop ms);
    modify (\<lambda>s. s \<lparr>globals := globals s \<lparr> phantom_machine_state_' := ms' \<rparr>\<rparr>);
    return r
  od"

definition doUserOp_C_if ::
  "user_transition_if \<Rightarrow> user_context \<Rightarrow> (cstate, (event option \<times> user_context)) nondet_monad" where
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
      es \<leftarrow> doMachineOp_C getExMonitor;
      u \<leftarrow> return (uop t pl pr pxn (tc, um |` allow_read, (ds \<circ> ptrFromPAddr)|` allow_read ,es));
      assert (u \<noteq> {});
      (e,(tc',um',ds',es')) \<leftarrow> select u;
      setUserMem_C ((um' |` allow_write \<circ> addrFromPPtr) |` (- dom ds));
      setDeviceState_C ((ds' |` allow_write \<circ> addrFromPPtr) |` dom ds);
      doMachineOp_C (setExMonitor es');
      return (e,tc')
   od"

lemma corres_dmo_getExMonitor_C:
  "corres_underlying rf_sr nf nf' (=) \<top> \<top> (doMachineOp getExMonitor) (doMachineOp_C getExMonitor)"
  apply (clarsimp simp: doMachineOp_def doMachineOp_C_def)
  apply (rule corres_guard_imp)
    apply (rule_tac r'="\<lambda>ms ms'. exclusive_state ms = exclusive_state ms' \<and>
                                 machine_state_rest ms = machine_state_rest ms' \<and>
                                 irq_masks ms = irq_masks ms' \<and> equiv_irq_state ms ms' \<and>
                                 device_state ms = device_state ms'"
                and P="\<top>" and P'="\<top>" in corres_split)
       apply (clarsimp simp: rf_sr_def cstate_relation_def cmachine_state_relation_def Let_def)
      apply (rule_tac r'="\<lambda>(r, ms) (r', ms'). r = r' \<and> ms = rv \<and> ms' = rv'"
              in corres_split)
         apply (rule corres_trivial, rule corres_select_f')
          apply (clarsimp simp: getExMonitor_def machine_rest_lift_def Nondet_Monad.bind_def gets_def
                                get_def return_def modify_def put_def select_f_def)
         apply (clarsimp simp: getExMonitor_no_fail[simplified no_fail_def])
        apply (clarsimp simp: split_def)
        apply (rule_tac r'=dc and P="\<lambda>s. underlying_memory (snd ((aa, b), ba)) =
                                         underlying_memory (ksMachineState s)"
                              and P'="\<lambda>s. underlying_memory (snd ((aa, b), bc)) =
                                          underlying_memory (phantom_machine_state_' (globals s))"
                in corres_split)
           apply (rule corres_modify)
           apply (clarsimp simp: rf_sr_def cstate_relation_def carch_state_relation_def
                                 cmachine_state_relation_def Let_def)
          apply (rule corres_trivial, clarsimp)
         apply (wp hoare_TrueI)+
   apply (rule TrueI conjI | clarsimp simp: getExMonitor_def machine_rest_lift_def Nondet_Monad.bind_def
                                            gets_def get_def return_def modify_def put_def select_f_def)+
  done

lemma corres_dmo_setExMonitor_C:
  "corres_underlying rf_sr nf nf' dc \<top> \<top> (doMachineOp (setExMonitor es)) (doMachineOp_C (setExMonitor es))"
  apply (clarsimp simp: doMachineOp_def doMachineOp_C_def)
  apply (rule corres_guard_imp)
    apply (rule_tac r'="\<lambda>ms ms'. exclusive_state ms = exclusive_state ms' \<and>
                                 machine_state_rest ms = machine_state_rest ms' \<and>
                                 irq_masks ms = irq_masks ms' \<and> equiv_irq_state ms ms' \<and>
                                 device_state ms = device_state ms'"
                and P="\<top>" and P'="\<top>" in corres_split)
       apply (clarsimp simp: rf_sr_def cstate_relation_def cmachine_state_relation_def Let_def)
      apply (rule_tac r'="\<lambda>(r, ms) (r', ms'). ms = rv\<lparr>exclusive_state := es\<rparr> \<and>
                                              ms' = rv'\<lparr>exclusive_state := es\<rparr>"
              in corres_split)
         apply (rule corres_trivial, rule corres_select_f')
          apply (clarsimp simp: setExMonitor_def machine_rest_lift_def Nondet_Monad.bind_def gets_def
                                get_def return_def modify_def put_def select_f_def)
         apply (clarsimp simp: setExMonitor_no_fail[simplified no_fail_def])
        apply (simp add: split_def)
        apply (rule_tac P="\<lambda>s. underlying_memory (snd rva) =
                               underlying_memory (ksMachineState s)"
                    and P'="\<lambda>s. underlying_memory (snd rv'a) =
                                underlying_memory (phantom_machine_state_' (globals s))"
                     in corres_modify)
        apply (clarsimp simp: rf_sr_def cstate_relation_def carch_state_relation_def
                              cmachine_state_relation_def Let_def)
       apply (wp hoare_TrueI)+
   apply (rule TrueI conjI | clarsimp simp: setExMonitor_def machine_rest_lift_def Nondet_Monad.bind_def
                                            gets_def get_def return_def modify_def put_def select_f_def)+
  done

lemma dmo_getExMonitor_C_wp[wp]:
  "\<lbrace>\<lambda>s. P (exclusive_state (phantom_machine_state_' (globals s))) s\<rbrace>
   doMachineOp_C getExMonitor
   \<lbrace>P\<rbrace>"
  apply (simp add: doMachineOp_C_def)
  apply (wp modify_wp | wpc)+
  apply clarsimp
  apply (erule use_valid)
   apply wp
  apply simp
  done

lemma corres_underlying_split5:
  "(\<And>a b c d e. corres_underlying srel nf nf' rrel (Q a b c d e) (Q' a b c d e) (f a b c d e) (f' a b c d e))
   \<Longrightarrow> corres_underlying srel nf nf' rrel (case x of (a,b,c,d,e) \<Rightarrow> Q a b c d e)
                                          (case x of (a,b,c,d,e) \<Rightarrow> Q' a b c d e)
                                          (case x of (a,b,c,d,e) \<Rightarrow> f a b c d e)
                                          (case x of (a,b,c,d,e) \<Rightarrow> f' a b c d e)"
  by (cases x; simp)

lemma do_user_op_if_C_corres[ADT_IF_Refine_assms]:
   "corres_underlying rf_sr False False (=)
   (invs' and ex_abs einvs and (\<lambda>_. uop_nonempty f)) \<top>
   (doUserOp_if f tc) (doUserOp_C_if f tc)"
  apply (rule corres_gen_asm)
  apply (simp add: doUserOp_if_def doUserOp_C_if_def uop_nonempty_def del: split_paired_All)
  apply (rule corres_gets_same)
    apply (fastforce dest: ex_abs_ksReadyQueues_asrt
                     simp: absKState_crelation ptable_rights_s'_def ptable_rights_s''_def
                           rf_sr_def cstate_relation_def Let_def cstate_to_H_correct)
   apply simp
  apply (rule corres_gets_same)
    apply (fastforce dest: ex_abs_ksReadyQueues_asrt
                     simp: ptable_xn_s'_def ptable_xn_s''_def ptable_attrs_s_def
                           absKState_crelation ptable_attrs_s'_def ptable_attrs_s''_def rf_sr_def)
   apply simp
  apply (rule corres_gets_same)
    apply clarsimp
    apply (frule ex_abs_ksReadyQueues_asrt)
    apply (clarsimp simp: absKState_crelation curthread_relation ptable_lift_s'_def ptable_lift_s''_def
                         ptable_lift_s_def rf_sr_def)
   apply simp
  apply (simp add: getCurThread_def)
  apply (rule corres_gets_same)
    apply (fastforce dest: ex_abs_ksReadyQueues_asrt simp: absKState_crelation rf_sr_def)
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
        apply (rule corres_split[OF corres_dmo_getExMonitor_C])
          apply clarsimp
          apply (rule_tac r'="(=)" in corres_split[OF corres_select])
             apply clarsimp
            apply simp
            apply (rule corres_underlying_split5)
            apply (rule corres_split[OF user_memory_update_corres_C])
              apply (rule corres_split[OF device_update_corres_C])
                apply (rule corres_split[OF corres_dmo_setExMonitor_C,
                              where R="\<top>\<top>" and R'="\<top>\<top>"])
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
  "corres_underlying rf_sr False False (=) \<top> \<top> (checkActiveIRQ_if tc) (checkActiveIRQ_C_if tc)"
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
          apply (case_tac x; simp add: irq_type_never_invalid)
         apply simp+
       apply (rule no_fail_dmo')
       apply (rule no_fail_getActiveIRQ)
      apply (rule corres_trivial, clarsimp split: if_split option.splits)
     apply wp+
   apply simp+
  apply fastforce
  done

lemma obs_cpspace_user_data_relation[ADT_IF_Refine_assms]:
  "\<lbrakk> pspace_aligned' bd; pspace_distinct' bd;
     cpspace_user_data_relation (ksPSpace bd) (underlying_memory (ksMachineState bd)) hgs \<rbrakk>
     \<Longrightarrow> cpspace_user_data_relation (ksPSpace bd)
           (underlying_memory (observable_memory (ksMachineState bd) (user_mem' bd))) hgs"
   apply (clarsimp simp: cmap_relation_def dom_heap_to_user_data)
   apply (drule bspec, fastforce)
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
    apply (rule nat_add_offset_less [where n = 2, simplified])
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
