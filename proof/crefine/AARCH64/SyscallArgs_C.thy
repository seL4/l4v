(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2014, General Dynamics C4 Systems
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory SyscallArgs_C
imports
  TcbQueue_C
  CSpace_RAB_C
  StoreWord_C  DetWP
begin

(*FIXME: arch-split: C kernel names hidden by Haskell names *)
context kernel_m begin
abbreviation "msgRegistersC \<equiv> kernel_all_substitute.msgRegisters"
lemmas msgRegistersC_def = kernel_all_substitute.msgRegisters_def
end

context begin interpretation Arch . (*FIXME: arch-split*)

declare word_neq_0_conv[simp del]

definition
  cintr :: "irq \<Rightarrow> machine_word \<Rightarrow> errtype \<Rightarrow> bool"
where
 "cintr a x err \<equiv> x = scast EXCEPTION_PREEMPTED"

definition
  replyOnRestart :: "machine_word \<Rightarrow> machine_word list \<Rightarrow> bool \<Rightarrow> unit kernel"
where
 "replyOnRestart thread reply isCall \<equiv>
  do state \<leftarrow> getThreadState thread;
     when (state = Restart) (do
       _ \<leftarrow> when isCall (replyFromKernel thread (0, reply));
       setThreadState Running thread
     od)
  od"

crunch replyOnRestart
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps simp: crunch_simps)

lemmas replyOnRestart_typ_ats[wp] = typ_at_lifts [OF replyOnRestart_typ_at']

lemma replyOnRestart_invs'[wp]:
  "\<lbrace>invs'\<rbrace> replyOnRestart thread reply isCall \<lbrace>\<lambda>rv. invs'\<rbrace>"
  including no_pre
  apply (simp add: replyOnRestart_def)
  apply (wp setThreadState_nonqueued_state_update rfk_invs' hoare_weak_lift_imp)
  apply (rule hoare_strengthen_post, rule gts_sp')
  apply (clarsimp simp: pred_tcb_at')
  apply (auto elim!: pred_tcb'_weakenE st_tcb_ex_cap''
               dest: st_tcb_at_idle_thread')
  done


declare psubset_singleton[simp]

lemma gts_eq:
  "st_tcb_at' (\<lambda>st. st = state) t s
     \<Longrightarrow> (getThreadState t s = return state s)"
  apply (simp add: prod_eq_iff return_def)
  apply (subst conj_commute, rule context_conjI)
   apply (rule no_failD[OF no_fail_getThreadState])
   apply (erule pred_tcb_at')
  apply (rule not_psubset_eq)
   apply clarsimp
   apply (drule empty_failD [OF empty_fail_getThreadState])
   apply simp
  apply clarsimp
  apply (frule in_inv_by_hoareD[OF gts_inv'])
  apply (drule use_valid [OF _ gts_sp', OF _ TrueI])
  apply (clarsimp simp: st_tcb_at'_def obj_at'_def projectKOs objBits_simps)
  done

lemma replyOnRestart_twice':
  "((), s') \<in> fst (replyOnRestart t reply isCall s)
       \<Longrightarrow> replyOnRestart t reply' isCall' s'
             = return () s'"
  apply (clarsimp simp add: replyOnRestart_def in_monad)
  apply (drule use_valid [OF _ gts_sp', OF _ TrueI])
  apply (case_tac "state = Restart")
   apply clarsimp
   apply (drule use_valid [OF _ setThreadState_st_tcb'], simp)
   apply (simp add: gts_eq when_def cong: bind_apply_cong)
  apply (simp add: gts_eq when_def cong: bind_apply_cong)
  done

lemma replyOnRestart_twice[simplified]:
  "do replyOnRestart t reply isCall; replyOnRestart t reply' isCall'; m od
   = do replyOnRestart t reply isCall; m od"
  apply (rule ext)
  apply (rule bind_apply_cong[OF refl])
  apply simp
  apply (subst bind_apply_cong [OF _ refl])
   apply (erule replyOnRestart_twice')
  apply simp
  done

end

context kernel_m begin

lemma ccorres_pre_getWorkUnits:
  assumes cc: "\<And>rv. ccorres r xf (P rv) (P' rv) hs (f rv) c"
  shows "ccorres r xf
   (\<lambda>s. \<forall>rv. ksWorkUnitsCompleted s = rv \<longrightarrow> P rv s)
   {s. \<forall>rv. s \<in> P' rv} hs (getWorkUnits >>= f) c"
  apply (simp add: getWorkUnits_def)
  apply (rule ccorres_guard_imp)
    apply (rule ccorres_symb_exec_l)
       defer
       apply wp[1]
      apply (rule gets_sp)
     apply (clarsimp simp: empty_fail_def simpler_gets_def)
    apply assumption
   apply clarsimp
   defer
   apply (rule ccorres_guard_imp)
     apply (rule cc)
    apply clarsimp
   apply assumption
  apply clarsimp
  done

lemma preemptionPoint_ccorres:
  "ccorres (cintr \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
      invs' UNIV []
      preemptionPoint (Call preemptionPoint_'proc)"
  apply (cinit simp: workUnitsLimit_def whenE_def)
   apply (rule ccorres_liftE_Seq)
   apply (rule ccorres_split_nothrow
               [where P=\<top> and P'=UNIV and r'=dc and xf'=xfdc])
       apply (rule ccorres_from_vcg)
       apply (rule allI, rule conseqPre, vcg)
       apply (clarsimp simp: modifyWorkUnits_def simpler_modify_def)
       apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                             carch_state_relation_def
                             cmachine_state_relation_def)
      apply ceqv
     apply (rule ccorres_liftE_Seq)
     apply (rule ccorres_pre_getWorkUnits)
     apply (rule ccorres_cond_seq)
     apply (rule_tac R="\<lambda>s. rv = ksWorkUnitsCompleted s" in ccorres_cond2)
       apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def)
      prefer 2
      apply simp
      apply (rule ccorres_from_vcg_throws [where P=\<top> and P'=UNIV])
      apply (rule allI, rule conseqPre, vcg)
      apply (simp add: returnOk_def return_def)
     apply (rule ccorres_liftE_Seq)
     apply (rule ccorres_rhs_assoc)+
     apply (rule ccorres_split_nothrow
                 [where P=\<top> and P'=UNIV and r'=dc and xf'=xfdc])
         apply (rule ccorres_from_vcg)
         apply (rule allI, rule conseqPre, vcg)
         apply (thin_tac "P" for P)+
         apply (clarsimp simp: setWorkUnits_def simpler_modify_def)
         apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                               carch_state_relation_def
                                     cmachine_state_relation_def)
        apply ceqv
       apply (rule ccorres_liftE_Seq)
       apply (ctac (no_vcg) add: isIRQPending_ccorres)
        apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
        apply (rule allI, rule conseqPre, vcg)
        apply (simp add: from_bool_0 whenE_def returnOk_def throwError_def
                         return_def split: option.splits)
        apply (clarsimp simp: cintr_def exception_defs)
       apply wpsimp+
     apply vcg
    apply (unfold modifyWorkUnits_def)[1]
    apply wp
   apply vcg
  apply simp
  done

definition
  "invocationCatch thread isBlocking isCall inject
   \<equiv>
   sum.case_sum (throwError \<circ> Inl)
    (\<lambda>oper. doE y \<leftarrow> liftE (setThreadState Structures_H.thread_state.Restart thread);
             reply \<leftarrow> RetypeDecls_H.performInvocation isBlocking isCall (inject oper)
                           >>= sum.case_sum (throwError \<circ> Inr) returnOk;
             liftE (if reply = [] then replyOnRestart thread [] isCall \<sqinter> return ()
                        else replyOnRestart thread reply isCall)
       odE)"

definition
  "intr_and_se_rel seOrIRQ status err
    \<equiv> case seOrIRQ of Inl se \<Rightarrow> syscall_error_rel se status err
           | Inr irq \<Rightarrow> cintr irq status err"

lemma intr_and_se_rel_simps[simp]:
  "intr_and_se_rel (Inl se) = syscall_error_rel se"
  "intr_and_se_rel (Inr irq) = cintr irq"
  by (rule ext | simp add: intr_and_se_rel_def)+

lemma errstate_globals_overwrite[simp]:
  "errstate (s \<lparr> globals := globals t \<rparr>) = errstate t"
  by (simp add: errstate_def)

definition
  array_to_list :: "('a['b :: finite]) \<Rightarrow> 'a list"
where
 "array_to_list arr \<equiv> map (index arr) ([0 ..< card (UNIV :: 'b set)])"

definition
  interpret_excaps :: "extra_caps_C \<Rightarrow> cte_C ptr list"
where
 "interpret_excaps excps \<equiv>
    (takeWhile (\<lambda>x. ptr_val x \<noteq> 0)
          (array_to_list (excaprefs_C excps)))"

lemma interpret_excaps_test_null[unfolded array_to_list_def, simplified]:
  "\<lbrakk> length (interpret_excaps excps) \<ge> n;
        n < length (array_to_list (excaprefs_C excps)) \<rbrakk>
     \<Longrightarrow> (index (excaprefs_C excps) n = NULL) = (length (interpret_excaps excps) = n)"
  apply (simp add: interpret_excaps_def)
  apply (rule iffI)
   apply (erule order_antisym[rotated])
   apply (rule length_takeWhile_le)
   apply (simp add: array_to_list_def)
  apply simp
  apply (drule length_takeWhile_ge)
  apply (simp add: array_to_list_def NULL_ptr_val)
  done

definition
  excaps_map :: "(capability \<times> machine_word) list
                     \<Rightarrow> cte_C ptr list"
where
 "excaps_map \<equiv> map (\<lambda>(cp, slot). cte_Ptr slot)"

definition
  slotcap_in_mem :: "capability \<Rightarrow> machine_word
                        \<Rightarrow> cte_heap \<Rightarrow> bool"
where
 "slotcap_in_mem cap slot
    \<equiv> \<lambda>cte_heap. \<exists>cte. cte_heap slot = Some cte \<and> cap = cteCap cte"

lemma slotcap_in_mem_def2:
  "slotcap_in_mem cap slot (ctes_of s)
    = cte_wp_at' (\<lambda>cte. cap = cteCap cte) slot s"
  by (simp add: slotcap_in_mem_def cte_wp_at_ctes_of)

definition
  excaps_in_mem :: "(capability \<times> machine_word) list
                            \<Rightarrow> cte_heap \<Rightarrow> bool"
where
 "excaps_in_mem cps \<equiv> \<lambda>cte_heap.
     \<forall>(cp, slot) \<in> set cps. slotcap_in_mem cp slot cte_heap"


lemma ccorres_alternative1:
  "ccorres rvr xf P P' hs f c
     \<Longrightarrow> ccorres rvr xf P P' hs (f \<sqinter> g) c"
  apply (simp add: ccorres_underlying_def)
  apply (erule ballEI, clarsimp del: allI)
  apply (simp add: alternative_def)
  apply (elim allEI)
  apply (auto simp: alternative_def split: xstate.split_asm)
  done

lemma ccorres_alternative2:
  "ccorres rvr xf P P' hs g c
     \<Longrightarrow> ccorres rvr xf P P' hs (f \<sqinter> g) c"
  apply (simp add: ccorres_underlying_def)
  apply (erule ballEI, clarsimp del: allI)
  apply (simp add: alternative_def)
  apply (elim allEI)
  apply (auto simp: alternative_def split: xstate.split_asm)
  done

lemma o_xo_injector:
  "((f o f') \<currency> r) = ((f \<currency> r) o case_sum (Inl o f') Inr)"
  by (intro ext, simp split: sum.split)

lemma ccorres_invocationCatch_Inr:
  "ccorres (f \<currency> r) xf P P' hs
   (invocationCatch thread isBlocking isCall injector (Inr v)) c
   =
   ccorres ((f \<circ> Inr) \<currency> r) xf P P' hs
   (do _ \<leftarrow> setThreadState Restart thread;
       doE reply \<leftarrow> performInvocation isBlocking isCall (injector v);
           if reply = [] then liftE (replyOnRestart thread [] isCall) \<sqinter> returnOk ()
                         else liftE (replyOnRestart thread reply isCall)
       odE od) c"
  apply (simp add: invocationCatch_def liftE_bindE o_xo_injector cong: ccorres_all_cong)
  apply (subst ccorres_liftM_simp[symmetric])
  apply (simp add: liftM_def bind_assoc bindE_def)
  apply (rule_tac f="\<lambda>f. ccorres rvr xs P P' hs f c" for rvr xs in arg_cong)
  apply (rule ext)
  apply (rule bind_apply_cong [OF refl])+
  apply (simp add: throwError_bind returnOk_bind lift_def liftE_def
                   alternative_bind
            split: sum.split if_split)
  apply (simp add: throwError_def)
  done

lemma getSlotCap_eq:
  "slotcap_in_mem cap slot (ctes_of s)
    \<Longrightarrow> getSlotCap slot s = return cap s"
  apply (clarsimp simp: slotcap_in_mem_def2 getSlotCap_def)
  apply (frule cte_wp_at_weakenE'[OF _ TrueI])
  apply (drule no_failD[OF no_fail_getCTE])
  apply (clarsimp simp: cte_wp_at'_def getCTE_def[symmetric]
                        bind_def return_def)
  done

lemma getSlotCap_ccorres_fudge:
  "ccorres_underlying sr Gamm rvr xf ar axf P Q hs (do rv \<leftarrow> getSlotCap slot; _ \<leftarrow> assert (rv = cp); a rv od) c
    \<Longrightarrow> ccorres_underlying sr Gamm rvr xf ar axf
          (P and (slotcap_in_mem cp slot o ctes_of))
          Q hs (a cp) c"
  apply (simp add: ccorres_underlying_def)
  apply (erule ballEI, clarsimp del: allI)
  apply (simp add: bind_apply_cong [OF getSlotCap_eq refl]
             cong: xstate.case_cong)
  done

lemma getSlotCap_ccorres_fudge_n:
  "ccorres_underlying sr Gamm rvr xf ar axf P Q hs
     (do rv \<leftarrow> getSlotCap (snd (vals ! n));
         _ \<leftarrow> assert (rv = fst (vals ! n)); a od) c
    \<Longrightarrow> ccorres_underlying sr Gamm rvr xf ar axf
            ((\<lambda>s. cte_wp_at' (\<lambda>cte. cteCap cte = fst (vals ! n))
                        (snd (vals ! n)) s \<longrightarrow> P s)
              and (excaps_in_mem vals \<circ> ctes_of) and K (n < length vals)) Q
           hs a c"
  apply (rule ccorres_guard_imp2)
   apply (erule getSlotCap_ccorres_fudge)
  apply (clarsimp simp: excaps_in_mem_def)
  apply (drule bspec, erule nth_mem)
  apply (clarsimp simp: slotcap_in_mem_def cte_wp_at_ctes_of)
  done

definition
 "is_syscall_error_code f code
    = (\<forall>Q. (\<Gamma> \<turnstile> {s. global_exn_var_'_update (\<lambda>_. Return)
                      (ret__unsigned_long_'_update (\<lambda>_. scast EXCEPTION_SYSCALL_ERROR)
                        (globals_update (current_syscall_error_'_update f) s)) \<in> Q}
           code {}, Q))"

abbreviation(input)
  (* no longer needed *)
  "Basic_with_globals f == (Basic f)"

lemma is_syscall_error_codes:
  "is_syscall_error_code f
       (Basic (globals_update (current_syscall_error_'_update f));;
        return_C ret__unsigned_long_'_update (\<lambda>_. scast EXCEPTION_SYSCALL_ERROR))"
  "is_syscall_error_code (f' o f)
       (Basic (globals_update (current_syscall_error_'_update f));;
        Basic (globals_update (current_syscall_error_'_update f'));;
        return_C ret__unsigned_long_'_update (\<lambda>_. scast EXCEPTION_SYSCALL_ERROR))"
  "is_syscall_error_code (f'' o f' o f)
       (Basic (globals_update (current_syscall_error_'_update f));;
        Basic (globals_update (current_syscall_error_'_update f'));;
        Basic (globals_update (current_syscall_error_'_update f''));;
        return_C ret__unsigned_long_'_update (\<lambda>_. scast EXCEPTION_SYSCALL_ERROR))"
  "is_syscall_error_code f
       (SKIP;;
        Basic (globals_update (current_syscall_error_'_update f));;
        return_C ret__unsigned_long_'_update (\<lambda>_. scast EXCEPTION_SYSCALL_ERROR))"
  "is_syscall_error_code (f' o f)
       (SKIP;;
        Basic (globals_update (current_syscall_error_'_update f));;
        Basic (globals_update (current_syscall_error_'_update f'));;
        return_C ret__unsigned_long_'_update (\<lambda>_. scast EXCEPTION_SYSCALL_ERROR))"
  "is_syscall_error_code (f'' o f' o f)
       (SKIP;;
        Basic (globals_update (current_syscall_error_'_update f));;
        Basic (globals_update (current_syscall_error_'_update f'));;
        Basic (globals_update (current_syscall_error_'_update f''));;
        return_C ret__unsigned_long_'_update (\<lambda>_. scast EXCEPTION_SYSCALL_ERROR))"
  "is_syscall_error_code f
       (Basic_with_globals (globals_update (current_syscall_error_'_update f));;
        return_C ret__unsigned_long_'_update (\<lambda>_. scast EXCEPTION_SYSCALL_ERROR))"
  "is_syscall_error_code (f' o f)
       (Basic_with_globals (globals_update (current_syscall_error_'_update f));;
        Basic_with_globals (globals_update (current_syscall_error_'_update f'));;
        return_C ret__unsigned_long_'_update (\<lambda>_. scast EXCEPTION_SYSCALL_ERROR))"
  "is_syscall_error_code (f'' o f' o f)
       (Basic_with_globals (globals_update (current_syscall_error_'_update f));;
        Basic_with_globals (globals_update (current_syscall_error_'_update f'));;
        Basic_with_globals (globals_update (current_syscall_error_'_update f''));;
        return_C ret__unsigned_long_'_update (\<lambda>_. scast EXCEPTION_SYSCALL_ERROR))"
  "is_syscall_error_code (f'''' \<circ> f''' \<circ> f'' o f' o f)
       (
        Basic_with_globals (globals_update (current_syscall_error_'_update f));;
        Basic_with_globals (globals_update (current_syscall_error_'_update f'));;
        Basic_with_globals (globals_update (current_syscall_error_'_update f''));;
        Basic_with_globals (globals_update (current_syscall_error_'_update f'''));;
        Basic_with_globals (globals_update (current_syscall_error_'_update f''''));;
        return_C ret__unsigned_long_'_update (\<lambda>_. scast EXCEPTION_SYSCALL_ERROR))"
  "is_syscall_error_code f
       (SKIP;;
        Basic_with_globals (globals_update (current_syscall_error_'_update f));;
        return_C ret__unsigned_long_'_update (\<lambda>_. scast EXCEPTION_SYSCALL_ERROR))"
  "is_syscall_error_code (f' o f)
       (SKIP;;
        Basic_with_globals (globals_update (current_syscall_error_'_update f));;
        Basic_with_globals (globals_update (current_syscall_error_'_update f'));;
        return_C ret__unsigned_long_'_update (\<lambda>_. scast EXCEPTION_SYSCALL_ERROR))"
  "is_syscall_error_code (f'' o f' o f)
       (SKIP;;
        Basic_with_globals (globals_update (current_syscall_error_'_update f));;
        Basic_with_globals (globals_update (current_syscall_error_'_update f'));;
        Basic_with_globals (globals_update (current_syscall_error_'_update f''));;
        return_C ret__unsigned_long_'_update (\<lambda>_. scast EXCEPTION_SYSCALL_ERROR))"
  by ((rule iffD2[OF is_syscall_error_code_def], intro allI,
      rule conseqPre, vcg, safe, (simp_all add: o_def)?)+)

lemma syscall_error_throwError_ccorres_direct_gen:
  "\<lbrakk> is_syscall_error_code f code;
     \<And>x y g. arrel (Inl x) y = (intr_and_se_rel \<currency> g) (Inl x) y;
     \<And>err' ft'. syscall_error_to_H (f err') ft' = Some err \<rbrakk>
   \<Longrightarrow>
   ccorres_underlying rf_sr \<Gamma> rrel xf
      arrel (liftxf errstate id v' ret__unsigned_long_')
      \<top> (UNIV) (SKIP # hs)
      (throwError (Inl err)) code"
  apply (rule ccorres_from_vcg_throws)
  apply (rule allI, rule conseqPre)
  apply (erule iffD1[OF is_syscall_error_code_def, THEN spec])
  apply (clarsimp simp: throwError_def return_def)
  apply (simp add: syscall_error_rel_def exception_defs)
  done

lemma syscall_error_throwError_ccorres_succs_gen:
  "\<lbrakk> is_syscall_error_code f code;
     \<And>x y g. arrel (Inl x) y = (intr_and_se_rel \<currency> g) (Inl x) y;
     \<And>err' ft'. syscall_error_to_H (f err') ft' = Some err \<rbrakk>
   \<Longrightarrow>
   ccorres_underlying rf_sr \<Gamma> rrel xf
      arrel (liftxf errstate id v' ret__unsigned_long_')
      \<top> (UNIV) (SKIP # hs)
      (throwError (Inl err)) (code ;; remainder)"
  apply (rule ccorres_guard_imp2,
         rule ccorres_split_throws)
    apply (erule syscall_error_throwError_ccorres_direct_gen; assumption)
   apply (rule HoarePartialProps.augment_Faults)
    apply (erule iffD1[OF is_syscall_error_code_def, THEN spec])
   apply simp+
  done

lemmas syscall_error_throwError_ccorres_n_gen =
    is_syscall_error_codes[THEN syscall_error_throwError_ccorres_direct_gen,
                           simplified o_apply]
    is_syscall_error_codes[THEN syscall_error_throwError_ccorres_succs_gen,
                           simplified o_apply]

lemmas syscall_error_throwError_ccorres_n =
  syscall_error_throwError_ccorres_n_gen[where arrel="intr_and_se_rel \<currency> dc", simplified]

lemmas syscall_error_throwError_ccorres_n_inl_rrel =
  syscall_error_throwError_ccorres_n_gen[where arrel="inl_rrel (intr_and_se_rel \<currency> dc)", simplified]

definition idButNot :: "'a \<Rightarrow> 'a"
where "idButNot x = x"

lemma interpret_excaps_test_null2:
  "n < 3 \<Longrightarrow>
   (index (excaprefs_C excps) n = NULL)
      = (length (interpret_excaps excps) \<le> n
            \<and> index (idButNot excaprefs_C excps) n = NULL)"
  unfolding idButNot_def
  apply safe
  apply (rule ccontr, simp only: linorder_not_le)
  apply (frule(1) interpret_excaps_test_null [OF order_less_imp_le])
  apply simp
  done

lemma interpret_excaps_eq[unfolded array_to_list_def, simplified]:
  "interpret_excaps excps = xs \<Longrightarrow>
   \<forall>n < length xs. (index (excaprefs_C excps) n) = (xs ! n)
         \<and> (length xs < length (array_to_list (excaprefs_C excps))
              \<longrightarrow> index (excaprefs_C excps) (length xs) = NULL)"
  apply (clarsimp simp: interpret_excaps_def)
  apply (drule length_takeWhile_gt)
  apply (clarsimp simp: nth_append)
  apply (clarsimp simp: array_to_list_def)
  apply (frule_tac f=length in arg_cong, subst(asm) length_map,
         simp(no_asm_use))
  apply (rule conjI)
   apply (rule trans, erule map_upt_eq_vals_D, simp)
   apply (simp add: nth_append)
  apply clarsimp
  apply (frule nth_length_takeWhile)
  apply (rule trans, erule map_upt_eq_vals_D, simp)
  apply (simp add: nth_append NULL_ptr_val)
  done

lemma ctes_of_0_contr[elim]:
  "\<lbrakk> ctes_of s 0 = Some cte; valid_mdb' s \<rbrakk> \<Longrightarrow> P"
  by (drule(1) ctes_of_not_0, simp)

lemma invocationCatch_use_injection_handler:
  "(v >>= invocationCatch thread isBlocking isCall injector)
     = (injection_handler Inl v >>=E
           (invocationCatch thread isBlocking isCall injector o Inr))"
  apply (simp add: injection_handler_def handleE'_def
                   bind_bindE_assoc)
  apply (rule ext, rule bind_apply_cong [OF refl])
  apply (simp add: invocationCatch_def return_returnOk
            split: sum.split)
  done

lemma ccorres_injection_handler_csum1:
  "ccorres (f \<currency> r) xf P P' hs a c
    \<Longrightarrow> ccorres
           ((\<lambda>rv a b. \<exists>rv'. rv = injector rv' \<and> f rv' a b) \<currency> r) xf P P' hs
           (injection_handler injector a) c"
  apply (simp add: injection_handler_liftM)
  apply (erule ccorres_rel_imp)
  apply (auto split: sum.split)
  done

lemma ccorres_injection_handler_csum2:
  "ccorres ((f o injector) \<currency> r) xf P P' hs a c
    \<Longrightarrow> ccorres (f \<currency> r) xf P P' hs
            (injection_handler injector a) c"
  apply (simp add: injection_handler_liftM)
  apply (erule ccorres_rel_imp)
  apply (auto split: sum.split)
  done

definition
  is_nondet_refinement :: "('a, 's) nondet_monad
                              \<Rightarrow> ('a, 's) nondet_monad \<Rightarrow> bool"
where
 "is_nondet_refinement f g \<equiv> \<forall>s. (snd (f s) \<longrightarrow> snd (g s)) \<and> fst (f s) \<subseteq> fst (g s)"

lemma is_nondet_refinement_refl[simp]:
  "is_nondet_refinement a a"
  by (simp add: is_nondet_refinement_def)

lemma is_nondet_refinement_bind:
  "\<lbrakk> is_nondet_refinement a c; \<And>rv. is_nondet_refinement (b rv) (d rv) \<rbrakk>
     \<Longrightarrow> is_nondet_refinement (a >>= b) (c >>= d)"
  apply (clarsimp simp: is_nondet_refinement_def bind_def split_def)
  apply fast
  done

lemma is_nondet_refinement_bindE:
  "\<lbrakk> is_nondet_refinement a c; \<And>rv. is_nondet_refinement (b rv) (d rv) \<rbrakk>
     \<Longrightarrow> is_nondet_refinement (a >>=E b) (c >>=E d)"
  apply (simp add: bindE_def)
  apply (erule is_nondet_refinement_bind)
  apply (simp add: lift_def split: sum.split)
  done

lemma ccorres_nondet_refinement:
  "\<lbrakk> is_nondet_refinement a b;
       ccorres_underlying sr Gamm rvr xf arrel axf G G' hs a c \<rbrakk>
     \<Longrightarrow> ccorres_underlying sr Gamm rvr xf arrel axf G G' hs b c"
  apply (simp add: ccorres_underlying_def is_nondet_refinement_def
                   split_def)
  apply (rule ballI, drule(1) bspec)
  apply (intro impI)
  apply (drule mp, blast)
  apply (elim allEI)
  apply (clarsimp split: xstate.split_asm)
  apply blast
  done

lemma is_nondet_refinement_alternative1:
  "is_nondet_refinement a (a \<sqinter> b)"
  by (clarsimp simp add: is_nondet_refinement_def alternative_def)

lemma ccorres_defer:
  assumes c: "ccorres r xf P P' hs H C"
  assumes f: "no_fail Q H"
  shows "ccorres (\<lambda>_. r rv) xf (\<lambda>s. P s \<and> Q s \<and> (P s \<and> Q s \<longrightarrow> fst (H s) = {(rv,s)})) P' hs (return ()) C"
  using c
  apply (clarsimp simp: ccorres_underlying_def split: xstate.splits)
  apply (drule (1) bspec)
  apply clarsimp
  apply (erule impE)
   apply (insert f)[1]
   apply (clarsimp simp: no_fail_def)
  apply (clarsimp simp: return_def)
  apply (rule conjI)
   apply clarsimp
   apply (rename_tac s)
   apply (erule_tac x=n in allE)
   apply (erule_tac x="Normal s" in allE)
   apply (clarsimp simp: unif_rrel_def)
  apply fastforce
  done

lemma no_fail_loadWordUser:
  "no_fail (pointerInUserData x and K (is_aligned x 3)) (loadWordUser x)"
  apply (simp add: loadWordUser_def)
  apply (rule no_fail_pre, wp no_fail_stateAssert)
  apply (simp add: word_size_bits_def)
  done

lemma no_fail_getMRs:
  "no_fail (tcb_at' thread and case_option \<top> valid_ipc_buffer_ptr' buffer)
           (getMRs thread buffer info)"
  apply (rule det_wp_no_fail)
  apply (rule det_wp_getMRs)
  done

lemma nat_less_4_cases:
  "(x::nat) < 4 \<Longrightarrow> x=0 \<or> x=1 \<or> x=2 \<or> x=3"
  by clarsimp

lemma asUser_cur_obj_at':
  assumes f: "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  shows "\<lbrace>\<lambda>s. obj_at' (\<lambda>tcb. P (atcbContextGet (tcbArch tcb))) (ksCurThread s) s \<and> t = ksCurThread s\<rbrace>
          asUser t f \<lbrace>\<lambda>rv s. obj_at' (\<lambda>tcb. Q rv (atcbContextGet (tcbArch tcb))) (ksCurThread s) s\<rbrace>"
  apply (simp add: asUser_def split_def)
  apply (wp)
     apply (rule hoare_lift_Pf2 [where f=ksCurThread])
      apply (wp threadSet_obj_at'_really_strongest)+
   apply (clarsimp simp: threadGet_def)
   apply (wp getObject_tcb_wp)
  apply clarsimp
  apply (drule obj_at_ko_at')
  apply clarsimp
  apply (rename_tac tcb)
  apply (rule_tac x=tcb in exI)
  apply clarsimp
  apply (drule use_valid, rule f, assumption)
  apply clarsimp
  done

lemma asUser_const_rv:
  assumes f: "\<lbrace>\<lambda>s. P\<rbrace> f \<lbrace>\<lambda>rv s. Q rv\<rbrace>"
  shows "\<lbrace>\<lambda>s. P\<rbrace> asUser t f \<lbrace>\<lambda>rv s. Q rv\<rbrace>"
  apply (simp add: asUser_def split_def)
  apply (wp)
  apply (clarsimp simp: threadGet_def)
  apply (wp getObject_tcb_wp)
  apply clarsimp
  apply (drule obj_at_ko_at')
  apply clarsimp
  apply (rename_tac tcb)
  apply (rule_tac x=tcb in exI)
  apply clarsimp
  apply (drule use_valid, rule f, assumption)
  apply clarsimp
  done

lemma getMRs_tcbContext:
  "\<lbrace>\<lambda>s. n < unat n_msgRegisters \<and> n < unat (msgLength info) \<and> thread = ksCurThread s \<and> cur_tcb' s\<rbrace>
  getMRs thread buffer info
  \<lbrace>\<lambda>rv s. obj_at' (\<lambda>tcb. user_regs (atcbContextGet (tcbArch tcb)) (AARCH64_H.msgRegisters ! n) = rv ! n) (ksCurThread s) s\<rbrace>"
  apply (rule hoare_assume_pre)
  apply (elim conjE)
  apply (thin_tac "thread = t" for t)
  apply (clarsimp simp add: getMRs_def)
  apply (wp|wpc)+
    apply (rule_tac P="n < length rv" in hoare_gen_asm)
    apply (clarsimp simp: nth_append)
    apply (wp mapM_wp' hoare_weak_lift_imp)+
    apply simp
    apply (rule asUser_cur_obj_at')
    apply (simp add: getRegister_def msgRegisters_unfold)
    apply (simp add: mapM_Cons bind_assoc mapM_empty)
    apply wp
   apply (wp hoare_drop_imps hoare_vcg_all_lift)
   apply (wp asUser_cur_obj_at')
    apply (simp add: getRegister_def msgRegisters_unfold)
    apply (simp add: mapM_Cons bind_assoc mapM_empty)
    apply (wp asUser_const_rv)
   apply clarsimp
   apply (wp asUser_const_rv)
  apply (clarsimp simp: n_msgRegisters_def msgRegisters_unfold)
  apply (simp add: nth_Cons' cur_tcb'_def split: if_split)
  done

lemma threadGet_tcbIpcBuffer_ccorres [corres]:
  "ccorres (=) w_bufferPtr_' (tcb_at' tptr) UNIV hs
           (threadGet tcbIPCBuffer tptr)
           (Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t tcb_ptr_to_ctcb_ptr tptr\<rbrace>
               (\<acute>w_bufferPtr :==
                  h_val (hrs_mem \<acute>t_hrs)
                   (Ptr &(tcb_ptr_to_ctcb_ptr tptr\<rightarrow>[''tcbIPCBuffer_C''])::machine_word ptr)))"
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_add_return2)
   apply (rule ccorres_pre_threadGet)
   apply (rule_tac P = "obj_at' (\<lambda>tcb. tcbIPCBuffer tcb = x) tptr" and
                   P'="{s'. \<exists>ctcb.
          cslift s' (tcb_ptr_to_ctcb_ptr tptr) = Some ctcb \<and>
                 tcbIPCBuffer_C ctcb = x }" in ccorres_from_vcg)
   apply (rule allI, rule conseqPre, vcg)
   apply clarsimp
   apply (clarsimp simp: return_def typ_heap_simps')
  apply (clarsimp simp: obj_at'_def ctcb_relation_def)
  done

(* FIXME: move *)
lemma ccorres_case_bools:
  assumes P: "ccorres r xf P P' hs (a True) (c True)"
  assumes Q: "ccorres r xf Q Q' hs (a False) (c False)"
  shows "ccorres r xf (\<lambda>s. (b \<longrightarrow> P s) \<and> (\<not>b \<longrightarrow> Q s))
                      ({s. b \<longrightarrow> s \<in> P'} \<inter> {s. \<not>b \<longrightarrow> s \<in> Q'})
                      hs (a b) (c b)"
  apply (cases b)
   apply (auto simp: P Q)
  done

lemma ccap_relation_frame_tags:
  "ccap_relation (ArchObjectCap (FrameCap v0 v1 v2 dev v3)) cap \<Longrightarrow>
  cap_get_tag cap = scast cap_frame_cap"
  by (auto simp: cap_get_tag_isCap_unfolded_H_cap)

(* FIXME: move *)
lemma ccorres_case_bools':
  assumes P: "b \<Longrightarrow> ccorres r xf P P' hs (a True) (c True)"
  assumes Q: "\<not> b \<Longrightarrow> ccorres r xf Q Q' hs (a False) (c False)"
  shows "ccorres r xf (\<lambda>s. (b \<longrightarrow> P s) \<and> (\<not>b \<longrightarrow> Q s))
                      ({s. b \<longrightarrow> s \<in> P'} \<inter> {s. \<not>b \<longrightarrow> s \<in> Q'})
                      hs (a b) (c b)"
  apply (cases b)
   apply (auto simp: P Q)
  done

(* FIXME x64: does this need vmrights \<noteq> 0 *)
lemma capFVMRights_range:
  "\<And>cap. cap_get_tag cap = scast cap_frame_cap \<Longrightarrow>
   cap_frame_cap_CL.capFVMRights_CL (cap_frame_cap_lift cap) \<le> 3"
  by (simp add: cap_frame_cap_lift_def
                cap_lift_def cap_tag_defs word_and_le1 mask_def)+

lemma dumb_bool_split_for_vcg:
  "\<lbrace>d \<longrightarrow> \<acute>ret__unsigned_long \<noteq> 0\<rbrace> \<inter> \<lbrace>\<not> d \<longrightarrow> \<acute>ret__unsigned_long = 0\<rbrace>
  = \<lbrace>d = to_bool \<acute>ret__unsigned_long \<rbrace>"
  by (auto simp: to_bool_def)

lemma ccap_relation_page_is_device:
  "ccap_relation (capability.ArchObjectCap (arch_capability.FrameCap v0a v1 v2 d v3)) c
   \<Longrightarrow> (cap_frame_cap_CL.capFIsDevice_CL (cap_frame_cap_lift c) \<noteq> 0) = d"
   apply (clarsimp simp: ccap_relation_def Let_def map_option_Some_eq2 cap_to_H_def)
   apply (case_tac z)
    apply (auto split: if_splits simp: to_bool_def Let_def cap_frame_cap_lift_def)
   done

(* FIXME AARCH64 unat_of_nat_pageBitsForSize exists, but it's a 64-bit version *)
lemma unat_of_nat_32_pageBitsForSize[simp]:
  "unat (of_nat (pageBitsForSize x)::32 word) = pageBitsForSize x"
  apply (subst unat_of_nat_eq; simp)
  apply (rule order_le_less_trans, rule pageBitsForSize_le)
  apply simp
  done

lemma lookupIPCBuffer_ccorres[corres]:
  "ccorres ((=) \<circ> option_to_ptr) ret__ptr_to_unsigned_long_'
           (tcb_at' t)
           (UNIV \<inter> {s. thread_' s = tcb_ptr_to_ctcb_ptr t}
                  \<inter> {s. isReceiver_' s = from_bool isReceiver}) []
      (lookupIPCBuffer isReceiver t) (Call lookupIPCBuffer_'proc)"
  apply (cinit lift: thread_' isReceiver_')
   apply (rule ccorres_split_nothrow)
       apply simp
       apply (rule threadGet_tcbIpcBuffer_ccorres)
      apply ceqv
     apply (simp add: getThreadBufferSlot_def locateSlot_conv
                      cte_C_size word_sle_def Collect_True
                 del: Collect_const)
     apply (rule ccorres_getSlotCap_cte_at)
     apply (rule ccorres_move_array_assertion_tcb_ctes)
     apply (ctac (no_vcg))
       apply csymbr
       apply (rule_tac b="isArchObjectCap rv \<and> isFrameCap (capCap rv)" in ccorres_case_bools')
        apply simp
        apply (rule ccorres_cond_false_seq)
        apply (simp(no_asm))
        apply csymbr
        apply (rule_tac b="isDeviceCap rv" in ccorres_case_bools')
         apply (rule ccorres_cond_true_seq)
         apply (rule ccorres_from_vcg_split_throws[where P=\<top> and P'=UNIV])
          apply vcg
         apply (rule conseqPre, vcg,
                clarsimp simp: isCap_simps return_def option_to_ptr_def option_to_0_def)
        apply (rule ccorres_cond_false_seq)
        apply simp
        apply csymbr
        apply csymbr
        apply (clarsimp simp: isCap_simps)
        apply (rule ccorres_guard_imp[where A=\<top> and A'=UNIV],
                rule ccorres_cond [where R=\<top>])
            apply (clarsimp simp: from_bool_0 isCap_simps)
            apply (frule cap_get_tag_isCap_unfolded_H_cap)
            apply (clarsimp simp: cap_frame_cap_lift cap_to_H_def elim!: ccap_relationE)
            apply (clarsimp simp: vmrights_to_H_def)
            apply (simp add: Kernel_C.VMReadOnly_def Kernel_C.VMKernelOnly_def
                             Kernel_C.VMReadWrite_def
                      split: if_split)
           apply (frule cap_get_tag_isCap_unfolded_H_cap(16),simp)
           apply (frule capFVMRights_range)
           apply (simp add: cap_frame_cap_lift)
           apply (clarsimp simp: cap_to_H_def vmrights_to_H_def word_le_make_less
                                 Kernel_C.VMReadWrite_def Kernel_C.VMReadOnly_def
                                 Kernel_C.VMKernelOnly_def
                           dest: word_less_cases)
           apply (rule ccorres_rhs_assoc)+
           apply csymbr
           apply csymbr
           apply csymbr
           apply csymbr
           apply csymbr
           apply csymbr
           apply csymbr
           apply (rule ccorres_Guard)
           apply simp
           apply (rule ccorres_assert)+
           apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg_throws)
           apply (rule allI, rule conseqPre, vcg)
           apply (clarsimp simp: return_def option_to_ptr_def option_to_0_def isCap_simps
                                 is_down ucast_of_nat)
           apply (frule cap_get_tag_isCap_unfolded_H_cap)
           apply (clarsimp simp: cap_frame_cap_lift cap_to_H_def mask_def elim!: ccap_relationE)
          apply (ctac add: ccorres_return_C)
         apply clarsimp
        apply (frule cap_get_tag_isCap_unfolded_H_cap)
        apply (clarsimp simp: Collect_const_mem isCap_simps word_less_nat_alt
                              option_to_ptr_def from_bool_0 option_to_0_def ccap_relation_def
                              c_valid_cap_def cl_valid_cap_def cap_frame_cap_lift
                              is_down ucast_of_nat)
       apply (rule ccorres_cond_true_seq)
       apply simp
       apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg_throws)
       apply (rule allI, rule conseqPre, vcg)
       apply (clarsimp simp: return_def option_to_ptr_def option_to_0_def isCap_simps
                             dumb_bool_for_all
                      split: capability.splits arch_capability.splits bool.splits)
      apply wpsimp
     apply (clarsimp simp: Collect_const_mem)
     apply (rule conjI)
      apply (clarsimp simp: isCap_simps word_less_nat_alt )
      apply (frule ccap_relation_page_is_device)
      apply (frule ccap_relation_frame_tags)
      apply clarsimp
     apply (rule ccontr)
     apply clarsimp
     apply (fastforce simp: cap_get_tag_PageCap_frame
                            isCap_simps)
    apply wp
   apply vcg
  apply (simp add: word_sle_def Collect_const_mem
                   tcb_cnode_index_defs tcbSlots cte_level_bits_def
                   size_of_def)
  done


lemma doMachineOp_pointerInUserData:
  "\<lbrace>pointerInUserData p\<rbrace> doMachineOp m \<lbrace>\<lambda>rv. pointerInUserData p\<rbrace>"
  by (simp add: pointerInUserData_def) wp

lemma loadWordUser_wp:
  "\<lbrace>\<lambda>s. is_aligned p 3 \<and> (\<forall>v. user_word_at v p s \<longrightarrow> P v s)\<rbrace>
    loadWordUser p
   \<lbrace>P\<rbrace>"
  apply (simp add: loadWordUser_def loadWord_def stateAssert_def
                   user_word_at_def valid_def upto0_7_def)
  apply (clarsimp simp: in_monad in_doMachineOp)
  done

lemma ccorres_pre_loadWordUser:
  "(\<And>rv. ccorres r xf (P rv) (Q rv) hs (a rv) c) \<Longrightarrow>
   ccorres r xf (valid_pspace' and K (is_aligned ptr 3) and
                 (\<lambda>s. \<forall>v. user_word_at v ptr s \<longrightarrow> P v s))
     {s. \<forall>v. cslift s (Ptr ptr :: machine_word ptr) = Some v \<longrightarrow>
               s \<in> Q v} hs
     (loadWordUser ptr >>= a) c"
  apply (rule ccorres_guard_imp)
    apply (rule_tac Q="\<lambda>rv. P rv and user_word_at rv ptr" and Q'=Q in
          ccorres_symb_exec_l [OF _ loadWordUser_inv loadWordUser_wp])
     apply (fastforce intro: ccorres_guard_imp)
    apply simp
   apply simp
  apply clarsimp
  apply (drule(1) user_word_at_cross_over, simp)
  apply (clarsimp simp: typ_heap_simps h_t_valid_clift_Some_iff)
  done

lemma loadWordUser_user_word_at:
  "\<lbrace>\<lambda>s. \<forall>rv. user_word_at rv x s \<longrightarrow> Q rv s\<rbrace> loadWordUser x \<lbrace>Q\<rbrace>"
  apply (simp add: loadWordUser_def user_word_at_def
                   doMachineOp_def split_def)
  apply wp
  apply (clarsimp simp: pointerInUserData_def
                        loadWord_def in_monad
                        is_aligned_mask upto0_7_def)
  done

lemma mapM_loadWordUser_user_words_at:
  "\<lbrace>\<lambda>s. \<forall>rv. (\<forall>x < length xs. user_word_at (rv ! x) (xs ! x) s)
              \<and> length rv = length xs \<longrightarrow> Q rv s\<rbrace>
    mapM loadWordUser xs \<lbrace>Q\<rbrace>"
  apply (induct xs arbitrary: Q)
   apply (simp add: mapM_def sequence_def)
   apply wp
  apply (simp add: mapM_Cons)
  apply wp
   apply assumption
  apply (wp loadWordUser_user_word_at)
  apply clarsimp
  apply (drule spec, erule mp)
  apply clarsimp
  apply (case_tac x)
   apply simp
  apply simp
  done


lemma getMRs_user_word:
  "\<lbrace>\<lambda>s. valid_ipc_buffer_ptr' buffer s \<and> i < msgLength info
      \<and> msgLength info \<le> msgMaxLength \<and> i >= scast n_msgRegisters\<rbrace>
  getMRs thread (Some buffer) info
  \<lbrace>\<lambda>xs. user_word_at (xs ! unat i) (buffer + (i * 8 + 8))\<rbrace>"
  supply if_cong[cong]
  apply (rule hoare_assume_pre)
  apply (elim conjE)
  apply (thin_tac "valid_ipc_buffer_ptr' x y" for x y)
  apply (simp add: getMRs_def)
  apply wp
   apply (rule_tac P="length hardwareMRValues = unat n_msgRegisters" in hoare_gen_asm)
   apply (clarsimp simp: nth_append word_le_nat_alt
                         word_less_nat_alt word_size
                         linorder_not_less [symmetric])
   apply (wp mapM_loadWordUser_user_words_at)
   apply (wp hoare_vcg_all_lift)
    apply (rule_tac Q'="\<lambda>_. \<top>" in hoare_strengthen_post)
     apply wp
    apply clarsimp
    defer
    apply simp
    apply (wp asUser_const_rv)
   apply (simp add: msgRegisters_unfold n_msgRegisters_def)
  apply (erule_tac x="unat i - unat n_msgRegisters" in allE)
  apply (erule impE)
   apply (simp add: msgRegisters_unfold
                    msgMaxLength_def msgLengthBits_def n_msgRegisters_def)
   apply (drule (1) order_less_le_trans)
   apply (simp add: word_less_nat_alt word_le_nat_alt)
  apply (simp add: msgRegisters_unfold
                   msgMaxLength_def msgLengthBits_def n_msgRegisters_def)
  apply (simp add: upto_enum_word del: upt_rec_numeral)
  apply (subst (asm) nth_map)
   apply (simp del: upt_rec_numeral)
   apply (drule (1) order_less_le_trans)
   apply (simp add: word_less_nat_alt word_le_nat_alt)
  apply (subst (asm) nth_upt)
   apply simp
   apply (drule (1) order_less_le_trans)
   apply (simp add: word_less_nat_alt word_le_nat_alt)
  apply (simp add: word_le_nat_alt add.commute add.left_commute mult.commute mult.left_commute
                   wordSize_def' take_bit_Suc)
  done

declare if_split [split]

definition
  "getMRs_rel args buffer \<equiv> \<lambda>s. \<exists>mi. msgLength mi \<le> msgMaxLength \<and> fst (getMRs (ksCurThread s) buffer mi s) = {(args, s)}"

definition
  "sysargs_rel args buffer \<equiv>
          cur_tcb'
          and case_option \<top> valid_ipc_buffer_ptr' buffer
          and getMRs_rel args buffer
          and (\<lambda>_. length args > unat (scast n_msgRegisters :: machine_word) \<longrightarrow> buffer \<noteq> None)"

definition
  "sysargs_rel_n args buffer n \<equiv> \<lambda>s. n < length args \<and> (unat (scast n_msgRegisters :: machine_word) \<le> n \<longrightarrow> buffer \<noteq> None)"

lemma sysargs_rel_to_n:
  "sysargs_rel args buffer s \<Longrightarrow> sysargs_rel_n args buffer n s = (n < length args)"
  by (auto simp add: sysargs_rel_def sysargs_rel_n_def)

lemma getMRs_rel:
  "\<lbrace>\<lambda>s. msgLength mi \<le> msgMaxLength \<and> thread = ksCurThread s \<and>
        case_option \<top> valid_ipc_buffer_ptr' buffer s \<and>
        cur_tcb' s\<rbrace>
  getMRs thread buffer mi \<lbrace>\<lambda>args. getMRs_rel args buffer\<rbrace>"
  apply (simp add: getMRs_rel_def)
  apply (rule hoare_pre)
   apply (rule_tac x=mi in hoare_exI)
   apply wp
   apply (rule_tac Q'="\<lambda>rv s. thread = ksCurThread s \<and> fst (getMRs thread buffer mi s) = {(rv,s)}" in hoare_strengthen_post)
    apply (wp det_result det_wp_getMRs)
   apply clarsimp
  apply (clarsimp simp: cur_tcb'_def)
  done

lemma length_msgRegisters:
  "length AARCH64_H.msgRegisters = unat (scast n_msgRegisters :: machine_word)"
  by (simp add: msgRegisters_unfold n_msgRegisters_def)

lemma getMRs_len[simplified]:
  "\<lbrace>\<top>\<rbrace> getMRs thread buffer mi \<lbrace>\<lambda>args s. length args > unat (scast n_msgRegisters :: machine_word) \<longrightarrow> buffer \<noteq> None\<rbrace>"
  apply (simp add: getMRs_def)
  apply (cases buffer, simp_all add:hoare_TrueI)
  apply (wp asUser_const_rv | simp)+
  apply (simp add: length_msgRegisters)
  done

lemma getMRs_sysargs_rel:
  "\<lbrace>(\<lambda>s. thread = ksCurThread s) and cur_tcb' and case_option \<top> valid_ipc_buffer_ptr' buffer and K (msgLength mi \<le> msgMaxLength)\<rbrace>
  getMRs thread buffer mi \<lbrace>\<lambda>args. sysargs_rel args buffer\<rbrace>"
  apply (simp add: sysargs_rel_def)
  apply (wp getMRs_rel getMRs_len|simp)+
  done

lemma ccorres_assume_pre:
  assumes "\<And>s. P s \<Longrightarrow> ccorres r xf (P and (\<lambda>s'. s' = s)) P' hs H C"
  shows "ccorres r xf P P' hs H C"
  apply (clarsimp simp: ccorres_underlying_def)
  apply (frule assms)
  apply (simp add: ccorres_underlying_def)
  apply blast
  done

lemma getMRs_length:
  "\<lbrace>\<lambda>s. msgLength mi \<le> msgMaxLength\<rbrace> getMRs thread buffer mi
  \<lbrace>\<lambda>args s. if buffer = None then length args = min (unat (scast n_msgRegisters :: machine_word)) (unat (msgLength mi))
            else length args = unat (msgLength mi)\<rbrace>"
  apply (cases buffer)
   apply (simp add: getMRs_def)
   apply (rule hoare_pre, wp)
    apply (rule asUser_const_rv)
    apply simp
    apply (wp mapM_length)
   apply (simp add: min_def length_msgRegisters)
  apply clarsimp
  apply (simp add: getMRs_def)
  apply (rule hoare_pre, wp)
    apply simp
    apply (wp mapM_length asUser_const_rv mapM_length)+
  apply (clarsimp simp: length_msgRegisters)
  apply (simp add: min_def split: if_splits)
  apply (clarsimp simp: word_le_nat_alt)
  apply (simp add: msgMaxLength_def msgLengthBits_def n_msgRegisters_def)
  done

lemma index_msgRegisters_less':
  "n < 4 \<Longrightarrow> index msgRegistersC n < 37"
  by (simp add: msgRegistersC_def fupdate_def Arrays.update_def
                fcp_beta "StrictC'_register_defs")

lemma index_msgRegisters_less:
  "n < 4 \<Longrightarrow> index msgRegistersC n <s 37"
  using index_msgRegisters_less'
  by (simp_all add: word_sless_msb_less)

lemma valid_ipc_buffer_ptr_array:
  "valid_ipc_buffer_ptr' (ptr_val p) s \<Longrightarrow> (s, s') \<in> rf_sr
    \<Longrightarrow> n \<le> 2 ^ (msg_align_bits - 3)
    \<Longrightarrow> n \<noteq> 0
    \<Longrightarrow> array_assertion (p :: machine_word ptr) n (hrs_htd (t_hrs_' (globals s')))"
  apply (clarsimp simp: valid_ipc_buffer_ptr'_def typ_at_to_obj_at_arches)
  apply (drule obj_at_ko_at', clarsimp)
  apply (drule rf_sr_heap_user_data_relation)
  apply (erule cmap_relationE1)
   apply (clarsimp simp: heap_to_user_data_def Let_def)
   apply (rule conjI, rule exI, erule ko_at_projectKO_opt)
   apply (rule refl)
  apply (drule clift_field, rule user_data_C_words_C_fl_ti, simp)
  apply (erule clift_array_assertion_imp, simp+)
  apply (simp add: field_lvalue_def msg_align_bits)
  apply (rule_tac x="unat (ptr_val p && mask pageBits >> 3)" in exI,
    simp add: word_shift_by_3 shiftr_shiftl1
              is_aligned_andI1[OF is_aligned_weaken])
  apply (simp add: add.commute word_plus_and_or_coroll2)
  apply (cut_tac a="(ptr_val p && mask pageBits ) >> 3"
        and b="2 ^ (pageBits - 3) - 2 ^ (msg_align_bits - 3)" in unat_le_helper)
   apply (simp add: pageBits_def msg_align_bits mask_def is_aligned_mask)
   apply word_bitwise
   apply simp
  apply (simp add: msg_align_bits pageBits_def)
  done

lemma array_assertion_valid_ipc_buffer_ptr_abs:
  "\<forall>s s'. (s, s') \<in> rf_sr \<and> (valid_ipc_buffer_ptr' (ptr_val (p s)) s)
        \<and> (n s' \<le> 2 ^ (msg_align_bits - 3) \<and> (x s' \<noteq> 0 \<longrightarrow> n s' \<noteq> 0))
    \<longrightarrow> (x s' = 0 \<or> array_assertion (p s :: machine_word ptr) (n s') (hrs_htd (t_hrs_' (globals s'))))"
  apply (intro allI impI disjCI2, clarsimp)
  apply (erule(1) valid_ipc_buffer_ptr_array, simp_all)
  done

lemmas ccorres_move_array_assertion_ipc_buffer
    = ccorres_move_array_assertions [OF array_assertion_valid_ipc_buffer_ptr_abs]

lemma getSyscallArg_ccorres_foo:
  "ccorres (\<lambda>a rv. rv = args ! n) ret__unsigned_long_'
           (sysargs_rel args buffer and sysargs_rel_n args buffer n)
           (UNIV \<inter> \<lbrace>unat \<acute>i = n\<rbrace> \<inter> \<lbrace>\<acute>ipc_buffer = option_to_ptr buffer\<rbrace>) []
           (return ()) (Call getSyscallArg_'proc)"
  apply (rule ccorres_assume_pre)
  apply (subst (asm) sysargs_rel_def)
  apply (subst (asm) getMRs_rel_def)
  apply (subst (asm) pred_conj_def)+
  apply (elim conjE exE)
  apply (cinit lift: i_' ipc_buffer_')
   apply (fold return_def)
   apply (rule_tac H="do thread \<leftarrow> gets ksCurThread; getMRs thread buffer mi od" in ccorres_defer)
    prefer 2
    apply (rule no_fail_pre, wp no_fail_getMRs)
    apply assumption
   apply (rule ccorres_cond_seq)
   apply (rule_tac R=\<top> and P="\<lambda>_. n < unat (scast n_msgRegisters :: machine_word)" in ccorres_cond_both)
     apply (simp add: word_less_nat_alt split: if_split)
    apply (rule ccorres_add_return2)
    apply (rule ccorres_symb_exec_l)
       apply (rule_tac P="\<lambda>s. n < unat (scast n_msgRegisters :: machine_word) \<and>
                              obj_at' (\<lambda>tcb. user_regs (atcbContextGet (tcbArch tcb))
                                               (AARCH64_H.msgRegisters!n) = x!n) (ksCurThread s) s"
                   and P' = UNIV
                in ccorres_from_vcg_split_throws)
        apply vcg
       apply (simp add: return_def del: Collect_const)
       apply (rule conseqPre, vcg)
       apply (clarsimp simp: rf_sr_ksCurThread)
       apply (drule (1) obj_at_cslift_tcb)
       apply (clarsimp simp: typ_heap_simps')
       apply (clarsimp simp: ctcb_relation_def ccontext_relation_def
                             msgRegisters_ccorres atcbContextGet_def
                             carch_tcb_relation_def cregs_relation_def)
       apply (subst (asm) msgRegisters_ccorres)
        apply (clarsimp simp: n_msgRegisters_def)
       apply (clarsimp simp: n_msgRegisters_def)
       apply (clarsimp simp: word_less_nat_alt word_upcast_0_sle)
       apply (simp add: index_msgRegisters_less'[simplified word_less_nat_alt, simplified])
      apply wp[1]
     apply (wp getMRs_tcbContext)
    apply fastforce
   apply (rule ccorres_seq_skip [THEN iffD2])
   apply (rule ccorres_add_return2)
   apply (rule ccorres_symb_exec_l)
      apply (rule_tac P="\<lambda>s. user_word_at (x!n) (ptr_val (CTypesDefs.ptr_add ipc_buffer (of_nat n + 1))) s
                             \<and> valid_ipc_buffer_ptr' (ptr_val ipc_buffer) s \<and> n < msgMaxLength"
                  and P'=UNIV
               in ccorres_from_vcg_throws)
      apply (simp add: return_def split del: if_split)
      apply (rule allI, rule conseqPre, vcg)
      apply (clarsimp split del: if_split)
      apply (frule(1) user_word_at_cross_over, rule refl)
      apply (clarsimp simp: ptr_add_def mult.commute
                            msgMaxLength_def)
      apply (safe intro!: disjCI2 elim!: valid_ipc_buffer_ptr_array,
        simp_all add: unatSuc2 add.commute msg_align_bits)[1]
     apply wp[1]
    apply (rule_tac P="\<exists>b. buffer = Some b" in hoare_gen_asm)
    apply (clarsimp simp: option_to_ptr_def option_to_0_def)
    apply (rule_tac P="\<lambda>s. valid_ipc_buffer_ptr' (ptr_val (Ptr b)) s \<and> i < msgLength mi \<and>
                           msgLength mi \<le> msgMaxLength \<and> scast n_msgRegisters \<le> i"
                 in hoare_weaken_pre)
     apply (wp getMRs_user_word)
    apply (clarsimp simp: msgMaxLength_def unat_less_helper)
   apply fastforce
  apply (clarsimp simp: sysargs_rel_def sysargs_rel_n_def)
  apply (rule conjI, clarsimp simp: unat_of_nat64 word_bits_def)
   apply (drule equalityD2)
   apply clarsimp
   apply (drule use_valid, rule getMRs_length, assumption)
   apply (simp add: n_msgRegisters_def  split: if_split_asm)
  apply (rule conjI)
   apply (clarsimp simp: option_to_ptr_def option_to_0_def
                         word_less_nat_alt word_le_nat_alt unat_of_nat64 word_bits_def
                         n_msgRegisters_def not_less msgMaxLength_def)
   apply (drule equalityD2)
   apply clarsimp
   apply (drule use_valid, rule getMRs_length)
    apply (simp add: word_le_nat_alt msgMaxLength_def)
   apply (simp split: if_split_asm)
  apply (rule conjI, clarsimp simp: cur_tcb'_def)
  apply clarsimp
  apply (clarsimp simp: bind_def gets_def return_def split_def get_def)
  done

end

context begin interpretation Arch . (*FIXME: arch-split*)

lemma invocation_eq_use_type:
  "\<lbrakk> value \<equiv> (value' :: 32 signed word);
       unat (scast value' :: machine_word) < length (enum :: invocation_label list); (scast value' :: machine_word) \<noteq> 0 \<rbrakk>
     \<Longrightarrow> (label = (scast value)) = (invocation_type label = enum ! unat (scast value' :: machine_word))"
  apply (fold invocationType_eq, unfold invocationType_def)
  apply (simp add: maxBound_is_length Let_def toEnum_def
                   nth_eq_iff_index_eq nat_le_Suc_less_imp
            split: if_split)
  apply (intro impI conjI)
   apply (simp add: enum_invocation_label)
  apply (subgoal_tac "GenInvocationLabel InvalidInvocation = enum ! 0")
   apply (erule ssubst, subst nth_eq_iff_index_eq, simp+)
   apply (clarsimp simp add: unat_eq_0)
  apply (simp add: enum_invocation_label enum_gen_invocation_labels)
  done

lemmas all_invocation_label_defs = invocation_label_defs arch_invocation_label_defs sel4_arch_invocation_label_defs

lemmas invocation_eq_use_types
    = all_invocation_label_defs[THEN invocation_eq_use_type, simplified,
                                unfolded enum_invocation_label enum_gen_invocation_labels enum_arch_invocation_label, simplified]

lemma ccorres_equals_throwError:
  "\<lbrakk> f = throwError v; ccorres_underlying sr Gamm rr xf arr axf P P' hs (throwError v) c \<rbrakk>
     \<Longrightarrow> ccorres_underlying sr Gamm rr xf arr axf P P' hs f c"
  by simp

end

end
