(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory IsolatedThreadAction
imports "../../../lib/clib/MonadicRewrite_C" Finalise_C CSpace_All SyscallArgs_C
begin

datatype tcb_state_regs = TCBStateRegs "thread_state" "MachineTypes.register \<Rightarrow> machine_word"

definition
 "tsrContext tsr \<equiv> case tsr of TCBStateRegs ts regs \<Rightarrow> regs"

definition
 "tsrState tsr \<equiv> case tsr of TCBStateRegs ts regs \<Rightarrow> ts"

lemma accessors_TCBStateRegs[simp]:
  "TCBStateRegs (tsrState v) (tsrContext v) = v"
  by (cases v, simp add: tsrState_def tsrContext_def)

lemma tsrContext_simp[simp]:
  "tsrContext (TCBStateRegs st con) = con"
  by (simp add: tsrContext_def)

lemma tsrState_simp[simp]:
  "tsrState (TCBStateRegs st con) = st"
  by (simp add: tsrState_def)

definition
  get_tcb_state_regs :: "kernel_object option \<Rightarrow> tcb_state_regs"
where
 "get_tcb_state_regs oko \<equiv> case oko of
    Some (KOTCB tcb) \<Rightarrow> TCBStateRegs (tcbState tcb) ((atcbContextGet o tcbArch) tcb)"

definition
  put_tcb_state_regs_tcb :: "tcb_state_regs \<Rightarrow> tcb \<Rightarrow> tcb"
where
 "put_tcb_state_regs_tcb tsr tcb \<equiv> case tsr of
     TCBStateRegs st regs \<Rightarrow> tcb \<lparr> tcbState := st, tcbArch := atcbContextSet regs (tcbArch tcb) \<rparr>"

definition
  put_tcb_state_regs :: "tcb_state_regs \<Rightarrow> kernel_object option \<Rightarrow> kernel_object option"
where
 "put_tcb_state_regs tsr oko = Some (KOTCB (put_tcb_state_regs_tcb tsr
    (case oko of
       Some (KOTCB tcb) \<Rightarrow> tcb | _ \<Rightarrow> makeObject)))"

definition
 "partial_overwrite idx tcbs ps \<equiv>
     \<lambda>x. if x \<in> range idx
         then put_tcb_state_regs (tcbs (inv idx x)) (ps x)
         else ps x"

definition
  isolate_thread_actions :: "('x \<Rightarrow> word32) \<Rightarrow> 'a kernel
                               \<Rightarrow> (('x \<Rightarrow> tcb_state_regs) \<Rightarrow> ('x \<Rightarrow> tcb_state_regs))
                               \<Rightarrow> (scheduler_action \<Rightarrow> scheduler_action)
                               \<Rightarrow> 'a kernel"
  where
 "isolate_thread_actions idx m t f \<equiv> do
    s \<leftarrow> gets (ksSchedulerAction_update (\<lambda>_. ResumeCurrentThread)
                    o ksPSpace_update (partial_overwrite idx (K undefined)));
    tcbs \<leftarrow> gets (\<lambda>s. get_tcb_state_regs o ksPSpace s o idx);
    sa \<leftarrow> getSchedulerAction;
    (rv, s') \<leftarrow> select_f (m s);
    modify (\<lambda>s. ksPSpace_update (partial_overwrite idx (t tcbs))
                    (s' \<lparr> ksSchedulerAction := f sa \<rparr>));
    return rv
  od"

lemma put_tcb_state_regs_twice[simp]:
  "put_tcb_state_regs tsr (put_tcb_state_regs tsr' tcb)
    = put_tcb_state_regs tsr tcb"
  apply (simp add: put_tcb_state_regs_def put_tcb_state_regs_tcb_def
                   makeObject_tcb
            split: tcb_state_regs.split option.split
                   Structures_H.kernel_object.split)
  apply (intro all_tcbI impI allI)
  apply simp
  done

lemma partial_overwrite_twice[simp]:
  "partial_overwrite idx f (partial_overwrite idx g ps)
       = partial_overwrite idx f ps"
  by (rule ext, simp add: partial_overwrite_def)

lemma get_tcb_state_regs_partial_overwrite[simp]:
  "inj idx \<Longrightarrow>
   get_tcb_state_regs (partial_overwrite idx tcbs f (idx x))
      = tcbs x"
  apply (simp add: partial_overwrite_def)
  apply (simp add: put_tcb_state_regs_def
                   get_tcb_state_regs_def
                   put_tcb_state_regs_tcb_def
            split: tcb_state_regs.split)
  done

lemma isolate_thread_actions_bind:
  "inj idx \<Longrightarrow>
   isolate_thread_actions idx a b c >>=
              (\<lambda>x. isolate_thread_actions idx (d x) e f)
      = isolate_thread_actions idx a id id
          >>= (\<lambda>x. isolate_thread_actions idx (d x) (e o b) (f o c))"
  apply (rule ext)
  apply (clarsimp simp: isolate_thread_actions_def bind_assoc split_def
                        bind_select_f_bind[symmetric])
  apply (clarsimp simp: exec_gets getSchedulerAction_def)
  apply (rule select_bind_eq)
  apply (simp add: exec_gets exec_modify o_def)
  apply (rule select_bind_eq)
  apply (simp add: exec_gets exec_modify)
  done

lemmas setEndpoint_obj_at_tcb' = setEndpoint_obj_at'_tcb

lemma tcbSchedEnqueue_obj_at_unchangedT:
  assumes y: "\<And>f. \<forall>tcb. P (tcbQueued_update f tcb) = P tcb"
  shows  "\<lbrace>obj_at' P t\<rbrace> tcbSchedEnqueue t' \<lbrace>\<lambda>rv. obj_at' P t\<rbrace>"
  apply (simp add: tcbSchedEnqueue_def unless_def)
  apply (wp | simp add: y)+
  done

lemma asUser_obj_at_notQ:
  "\<lbrace>obj_at' (Not \<circ> tcbQueued) t\<rbrace>
   asUser t (setRegister r v)
   \<lbrace>\<lambda>rv. obj_at' (Not \<circ> tcbQueued) t\<rbrace>"
  apply (simp add: asUser_def)
  apply (rule hoare_seq_ext)+
    apply (simp add: split_def)
    apply (rule threadSet_obj_at'_really_strongest)
   apply (wp threadGet_wp |rule gets_inv|wpc|clarsimp)+
  apply (clarsimp simp: obj_at'_def)
  done

(* FIXME: Move to Schedule_R.thy. Make Arch_switchToThread_obj_at a specialisation of this *)
lemma Arch_switchToThread_obj_at_pre:
  "\<lbrace>obj_at' (Not \<circ> tcbQueued) t\<rbrace>
   Arch.switchToThread t
   \<lbrace>\<lambda>rv. obj_at' (Not \<circ> tcbQueued) t\<rbrace>"
  apply (simp add: ARM_HYP_H.switchToThread_def)
  apply (wp asUser_obj_at_notQ doMachineOp_obj_at setVMRoot_obj_at hoare_drop_imps|wpc)+
  done

lemma rescheduleRequired_obj_at_unchangedT:
  assumes y: "\<And>f. \<forall>tcb. P (tcbQueued_update f tcb) = P tcb"
  shows  "\<lbrace>obj_at' P t\<rbrace> rescheduleRequired \<lbrace>\<lambda>rv. obj_at' P t\<rbrace>"
  apply (simp add: rescheduleRequired_def)
  apply (wp tcbSchedEnqueue_obj_at_unchangedT[OF y] | wpc)+
  apply simp
  done

lemma setThreadState_obj_at_unchangedT:
  assumes x: "\<And>f. \<forall>tcb. P (tcbState_update f tcb) = P tcb"
  assumes y: "\<And>f. \<forall>tcb. P (tcbQueued_update f tcb) = P tcb"
  shows "\<lbrace>obj_at' P t\<rbrace> setThreadState t' ts \<lbrace>\<lambda>rv. obj_at' P t\<rbrace>"
  apply (simp add: setThreadState_def)
  apply (wp rescheduleRequired_obj_at_unchangedT[OF y], simp)
  apply (wp threadSet_obj_at'_strongish)
  apply (clarsimp simp: obj_at'_def projectKOs x cong: if_cong)
  done

lemma setBoundNotification_obj_at_unchangedT:
  assumes x: "\<And>f. \<forall>tcb. P (tcbBoundNotification_update f tcb) = P tcb"
  shows "\<lbrace>obj_at' P t\<rbrace> setBoundNotification t' ts \<lbrace>\<lambda>rv. obj_at' P t\<rbrace>"
  apply (simp add: setBoundNotification_def)
  apply (wp threadSet_obj_at'_strongish)
  apply (clarsimp simp: obj_at'_def projectKOs x cong: if_cong)
  done

lemmas setThreadState_obj_at_unchanged
    = setThreadState_obj_at_unchangedT[OF all_tcbI all_tcbI]

lemmas setBoundNotification_obj_at_unchanged
    = setBoundNotification_obj_at_unchangedT[OF all_tcbI]

lemmas setNotification_tcb = set_ntfn_tcb_obj_at'

(* FIXME: move *)
lemmas threadSet_obj_at' = threadSet_obj_at'_strongish

context kernel_m begin
lemma setObject_modify:
  fixes v :: "'a :: pspace_storable" shows
  "\<lbrakk> obj_at' (P :: 'a \<Rightarrow> bool) p s; updateObject v = updateObject_default v;
         (1 :: word32) < 2 ^ objBits v \<rbrakk>
    \<Longrightarrow> setObject p v s
      = modify (ksPSpace_update (\<lambda>ps. ps (p \<mapsto> injectKO v))) s"
  apply (clarsimp simp: setObject_def split_def exec_gets
                        obj_at'_def projectKOs lookupAround2_known1
                        assert_opt_def updateObject_default_def
                        bind_assoc)
  apply (simp add: projectKO_def alignCheck_assert)
  apply (simp add: project_inject objBits_def)
  apply (clarsimp simp only: objBitsT_koTypeOf[symmetric] koTypeOf_injectKO)
  apply (frule(2) in_magnitude_check[where s'=s])
  apply (simp add: magnitudeCheck_assert in_monad)
  apply (simp add: simpler_modify_def)
  done

context begin interpretation Arch . (*FIXME: arch_split*)

lemma getObject_return:
  fixes v :: "'a :: pspace_storable" shows
  "\<lbrakk> \<And>a b c d. (loadObject a b c d :: 'a kernel) = loadObject_default a b c d;
        ko_at' v p s; (1 :: word32) < 2 ^ objBits v \<rbrakk> \<Longrightarrow> getObject p s = return v s"
  apply (clarsimp simp: getObject_def split_def exec_gets
                        obj_at'_def projectKOs lookupAround2_known1
                        assert_opt_def loadObject_default_def)
  apply (simp add: projectKO_def alignCheck_assert)
  apply (simp add: project_inject objBits_def)
  apply (frule(2) in_magnitude_check[where s'=s])
  apply (simp add: magnitudeCheck_assert in_monad)
  done

end

lemmas getObject_return_tcb
    = getObject_return[OF meta_eq_to_obj_eq, OF loadObject_tcb,
                       unfolded objBits_simps, simplified]

lemmas setObject_modify_tcb
    = setObject_modify[OF _ meta_eq_to_obj_eq, OF _ updateObject_tcb,
                       unfolded objBits_simps, simplified]

lemma partial_overwrite_fun_upd:
  "inj idx \<Longrightarrow>
   partial_overwrite idx (tsrs (x := y))
    = (\<lambda>ps. (partial_overwrite idx tsrs ps) (idx x := put_tcb_state_regs y (ps (idx x))))"
  apply (intro ext, simp add: partial_overwrite_def)
  apply (clarsimp split: if_split)
  done

lemma get_tcb_state_regs_ko_at':
  "ko_at' ko p s \<Longrightarrow> get_tcb_state_regs (ksPSpace s p)
       = TCBStateRegs (tcbState ko) ((atcbContextGet o tcbArch) ko)"
  by (clarsimp simp: obj_at'_def projectKOs get_tcb_state_regs_def)

lemma put_tcb_state_regs_ko_at':
  "ko_at' ko p s \<Longrightarrow> put_tcb_state_regs tsr (ksPSpace s p)
       = Some (KOTCB (ko \<lparr> tcbState := tsrState tsr
                         , tcbArch := atcbContextSet (tsrContext tsr) (tcbArch ko)\<rparr>))"
  by (clarsimp simp: obj_at'_def projectKOs put_tcb_state_regs_def
                     put_tcb_state_regs_tcb_def
              split: tcb_state_regs.split)

lemma partial_overwrite_get_tcb_state_regs:
  "\<lbrakk> \<forall>x. tcb_at' (idx x) s; inj idx \<rbrakk> \<Longrightarrow>
   partial_overwrite idx (\<lambda>x. get_tcb_state_regs (ksPSpace s (idx x)))
                (ksPSpace s) = ksPSpace s"
  apply (rule ext, simp add: partial_overwrite_def
                      split: if_split)
  apply clarsimp
  apply (drule_tac x=xa in spec)
  apply (clarsimp simp: obj_at'_def projectKOs put_tcb_state_regs_def
                        get_tcb_state_regs_def put_tcb_state_regs_tcb_def)
  apply (case_tac obj, simp)
  done

lemma ksPSpace_update_partial_id:
  "\<lbrakk> \<And>ps x. f ps x = ps (idx x) \<or> f ps x = ksPSpace s (idx x);
       \<forall>x. tcb_at' (idx x) s; inj idx \<rbrakk> \<Longrightarrow>
   ksPSpace_update (\<lambda>ps. partial_overwrite idx (\<lambda>x. get_tcb_state_regs (f ps x)) ps) s
      = s"
  apply (rule trans, rule kernel_state.fold_congs[OF refl refl])
   apply (erule_tac x="ksPSpace s" in meta_allE)
   apply (clarsimp simp: partial_overwrite_get_tcb_state_regs)
   apply (rule refl)
  apply simp
  done

lemma isolate_thread_actions_asUser:
  "\<lbrakk> idx t' = t; inj idx; f = (\<lambda>s. ({(v, g s)}, False)) \<rbrakk> \<Longrightarrow>
   monadic_rewrite False True (\<lambda>s. \<forall>x. tcb_at' (idx x) s)
      (asUser t f)
      (isolate_thread_actions idx (return v)
           (\<lambda>tsrs. (tsrs (t' := TCBStateRegs (tsrState (tsrs t'))
                                    (g (tsrContext (tsrs t'))))))
            id)"
  apply (simp add: asUser_def liftM_def isolate_thread_actions_def split_def
                   select_f_returns bind_assoc select_f_singleton_return
                   threadGet_def threadSet_def)
  apply (clarsimp simp: monadic_rewrite_def)
  apply (frule_tac x=t' in spec)
  apply (drule obj_at_ko_at', clarsimp)
  apply (simp add: exec_gets getSchedulerAction_def exec_modify
                   getObject_return_tcb setObject_modify_tcb o_def
             cong: bind_apply_cong)+
  apply (simp add: partial_overwrite_fun_upd return_def get_tcb_state_regs_ko_at')
  apply (rule kernel_state.fold_congs[OF refl refl])
  apply (clarsimp simp: partial_overwrite_get_tcb_state_regs
                        put_tcb_state_regs_ko_at')
  apply (case_tac ko, simp)
  done

lemma getRegister_simple:
  "getRegister r = (\<lambda>con. ({(con r, con)}, False))"
  by (simp add: getRegister_def simpler_gets_def)

lemma mapM_getRegister_simple:
  "mapM getRegister rs = (\<lambda>con. ({(map con rs, con)}, False))"
  apply (induct rs)
   apply (simp add: mapM_Nil return_def)
  apply (simp add: mapM_Cons getRegister_def simpler_gets_def
                   bind_def return_def)
  done

lemma setRegister_simple:
  "setRegister r v = (\<lambda>con. ({((), con (r := v))}, False))"
  by (simp add: setRegister_def simpler_modify_def)

lemma zipWithM_setRegister_simple:
  "zipWithM_x setRegister rs vs
      = (\<lambda>con. ({((), foldl (\<lambda>con (r, v). con (r := v)) con (zip rs vs))}, False))"
  apply (simp add: zipWithM_x_mapM_x)
  apply (induct ("zip rs vs"))
   apply (simp add: mapM_x_Nil return_def)
  apply (clarsimp simp add: mapM_x_Cons bind_def setRegister_def
                            simpler_modify_def fun_upd_def[symmetric])
  done

lemma dom_partial_overwrite:
  "\<forall>x. tcb_at' (idx x) s \<Longrightarrow> dom (partial_overwrite idx tsrs (ksPSpace s))
       = dom (ksPSpace s)"
  apply (rule set_eqI)
  apply (clarsimp simp: dom_def partial_overwrite_def put_tcb_state_regs_def
                 split: if_split)
  apply (fastforce elim!: obj_atE')
  done

lemma map_to_ctes_partial_overwrite:
  "\<forall>x. tcb_at' (idx x) s \<Longrightarrow>
   map_to_ctes (partial_overwrite idx tsrs (ksPSpace s))
     = ctes_of s"
  apply (rule ext)
  apply (frule dom_partial_overwrite[where tsrs=tsrs])
  apply (simp add: map_to_ctes_def partial_overwrite_def
                   Let_def)
  apply (case_tac "x \<in> range idx")
   apply (clarsimp simp: put_tcb_state_regs_def)
   apply (drule_tac x=xa in spec)
   apply (clarsimp simp: obj_at'_def projectKOs objBits_simps
                   cong: if_cong)
   apply (simp add: put_tcb_state_regs_def put_tcb_state_regs_tcb_def
                    objBits_simps
              cong: if_cong option.case_cong)
   apply (case_tac obj, simp split: tcb_state_regs.split if_split)
  apply simp
  apply (rule if_cong[OF refl])
   apply simp
  apply (case_tac "x && ~~ mask (objBitsKO (KOTCB undefined)) \<in> range idx")
   apply (clarsimp simp: put_tcb_state_regs_def)
   apply (drule_tac x=xa in spec)
   apply (clarsimp simp: obj_at'_def projectKOs objBits_simps
                   cong: if_cong)
   apply (simp add: put_tcb_state_regs_def put_tcb_state_regs_tcb_def
                    objBits_simps
              cong: if_cong option.case_cong)
   apply (case_tac obj, simp split: tcb_state_regs.split if_split)
   apply (intro impI allI)
   apply (subgoal_tac "x - idx xa = x && mask 9")
    apply (clarsimp simp: tcb_cte_cases_def split: if_split)
   apply (drule_tac t = "idx xa" in sym)
    apply simp
  apply (simp cong: if_cong)
  done

definition
 "thread_actions_isolatable idx f =
    (inj idx \<longrightarrow> monadic_rewrite False True (\<lambda>s. \<forall>x. tcb_at' (idx x) s)
                   f (isolate_thread_actions idx f id id))"

lemma getCTE_assert_opt:
  "getCTE p = gets (\<lambda>s. ctes_of s p) >>= assert_opt"
  apply (intro ext)
  apply (simp add: exec_gets assert_opt_def prod_eq_iff
                   fail_def return_def
            split: option.split)
  apply (rule conjI)
   apply clarsimp
   apply (rule context_conjI)
    apply (rule ccontr, clarsimp elim!: nonemptyE)
    apply (frule use_valid[OF _ getCTE_sp], rule TrueI)
    apply (frule in_inv_by_hoareD[OF getCTE_inv])
    apply (clarsimp simp: cte_wp_at_ctes_of)
   apply (simp add: empty_failD[OF empty_fail_getCTE])
  apply clarsimp
  apply (simp add: no_failD[OF no_fail_getCTE, OF ctes_of_cte_at])
  apply (subgoal_tac "cte_wp_at' (op = x2) p x")
   apply (clarsimp simp: cte_wp_at'_def getCTE_def)
  apply (simp add: cte_wp_at_ctes_of)
  done

lemma getCTE_isolatable:
  "thread_actions_isolatable idx (getCTE p)"
  apply (clarsimp simp: thread_actions_isolatable_def)
  apply (simp add: isolate_thread_actions_def bind_assoc split_def)
  apply (simp add: getCTE_assert_opt bind_select_f_bind[symmetric]
                   bind_assoc select_f_returns)
  apply (clarsimp simp: monadic_rewrite_def exec_gets getSchedulerAction_def
                        map_to_ctes_partial_overwrite)
  apply (simp add: assert_opt_def select_f_returns select_f_asserts
            split: option.split)
  apply (clarsimp simp: exec_modify o_def return_def)
  apply (simp add: ksPSpace_update_partial_id)
  done

lemma objBits_2n:
  "(1 :: word32) < 2 ^ objBits obj"
  by (simp add: objBits_def objBitsKO_def archObjSize_def machine_bits_defs
         split: kernel_object.split arch_kernel_object.split)

lemma magnitudeCheck_assert2:
  "\<lbrakk> is_aligned x n; (1 :: word32) < 2 ^ n; ksPSpace s x = Some v \<rbrakk> \<Longrightarrow>
   magnitudeCheck x (snd (lookupAround2 x (ksPSpace (s :: kernel_state)))) n
     = assert (ps_clear x n s)"
  using in_magnitude_check[where x=x and n=n and s=s and s'=s and v="()"]
  by (simp add: magnitudeCheck_assert in_monad)

lemma getObject_get_assert:
  assumes deflt: "\<And>a b c d. (loadObject a b c d :: ('a :: pspace_storable) kernel)
                          = loadObject_default a b c d"
  shows
  "(getObject p :: ('a :: pspace_storable) kernel)
   = do v \<leftarrow> gets (obj_at' (\<lambda>x :: 'a. True) p);
        assert v;
        gets (the o projectKO_opt o the o swp fun_app p o ksPSpace)
     od"
  apply (rule ext)
  apply (simp add: exec_get getObject_def split_def exec_gets
                   deflt loadObject_default_def projectKO_def2
                   alignCheck_assert)
  apply (case_tac "ksPSpace x p")
   apply (simp add: obj_at'_def assert_opt_def assert_def
             split: option.split if_split)
  apply (simp add: lookupAround2_known1 assert_opt_def
                   obj_at'_def projectKO_def2
            split: option.split)
  apply (clarsimp simp: fail_def fst_return conj_comms project_inject
                        objBits_def)
  apply (simp only: assert2[symmetric],
         rule bind_apply_cong[OF refl])
  apply (clarsimp simp: in_monad)
  apply (fold objBits_def)
  apply (simp add: magnitudeCheck_assert2[OF _ objBits_2n])
  apply (rule bind_apply_cong[OF refl])
  apply (clarsimp simp: in_monad return_def simpler_gets_def)
  apply (simp add: iffD2[OF project_inject refl])
  done

lemma obj_at_partial_overwrite_If:
  "\<lbrakk> \<forall>x. tcb_at' (idx x) s \<rbrakk>
    \<Longrightarrow> obj_at' P p (ksPSpace_update (partial_overwrite idx f) s)
             = (if p \<in> range idx
                then obj_at' (\<lambda>tcb. P (put_tcb_state_regs_tcb (f (inv idx p)) tcb)) p s
                else obj_at' P p s)"
  apply (frule dom_partial_overwrite[where tsrs=f])
  apply (simp add: obj_at'_def ps_clear_def partial_overwrite_def
                   projectKOs split: if_split)
  apply clarsimp
  apply (drule_tac x=x in spec)
  apply (clarsimp simp: put_tcb_state_regs_def objBits_simps)
  done

lemma obj_at_partial_overwrite_id1:
  "\<lbrakk> p \<notin> range idx; \<forall>x. tcb_at' (idx x) s \<rbrakk>
    \<Longrightarrow> obj_at' P p (ksPSpace_update (partial_overwrite idx f) s)
             = obj_at' P p s"
  apply (drule dom_partial_overwrite[where tsrs=f])
  apply (simp add: obj_at'_def ps_clear_def partial_overwrite_def
                   projectKOs)
  done

lemma obj_at_partial_overwrite_id2:
  "\<lbrakk> \<forall>x. tcb_at' (idx x) s; \<And>v tcb. P v \<or> True \<Longrightarrow> injectKO v \<noteq> KOTCB tcb \<rbrakk>
    \<Longrightarrow> obj_at' P p (ksPSpace_update (partial_overwrite idx f) s)
             = obj_at' P p s"
  apply (frule dom_partial_overwrite[where tsrs=f])
  apply (simp add: obj_at'_def ps_clear_def partial_overwrite_def
                   projectKOs split: if_split)
  apply clarsimp
  apply (drule_tac x=x in spec)
  apply (clarsimp simp: put_tcb_state_regs_def objBits_simps
                        project_inject)
  done

lemma getObject_isolatable:
  "\<lbrakk> \<And>a b c d. (loadObject a b c d :: 'a kernel) = loadObject_default a b c d;
      \<And>tcb. projectKO_opt (KOTCB tcb) = (None :: 'a option) \<rbrakk> \<Longrightarrow>
   thread_actions_isolatable idx (getObject p :: ('a :: pspace_storable) kernel)"
  apply (clarsimp simp: thread_actions_isolatable_def)
  apply (simp add: getObject_get_assert split_def
                   isolate_thread_actions_def bind_select_f_bind[symmetric]
                   bind_assoc select_f_asserts select_f_returns)
  apply (clarsimp simp: monadic_rewrite_def exec_gets getSchedulerAction_def)
  apply (case_tac "p \<in> range idx")
   apply clarsimp
   apply (drule_tac x=x in spec)
   apply (clarsimp simp: obj_at'_def projectKOs partial_overwrite_def
                         put_tcb_state_regs_def)
  apply (simp add: obj_at_partial_overwrite_id1)
  apply (simp add: partial_overwrite_def)
  apply (rule bind_apply_cong[OF refl])
  apply (simp add: exec_modify return_def o_def simpler_gets_def
                   ksPSpace_update_partial_id in_monad)
  done

lemma gets_isolatable:
  "\<lbrakk>\<And>g s. \<forall>x. tcb_at' (idx x) s \<Longrightarrow>
        f (ksSchedulerAction_update g
             (ksPSpace_update (partial_overwrite idx (\<lambda>_. undefined)) s)) = f s \<rbrakk> \<Longrightarrow>
   thread_actions_isolatable idx (gets f)"
  apply (clarsimp simp: thread_actions_isolatable_def)
  apply (simp add: isolate_thread_actions_def select_f_returns
                   liftM_def bind_assoc)
  apply (clarsimp simp: monadic_rewrite_def exec_gets
                   getSchedulerAction_def exec_modify)
  apply (simp add: simpler_gets_def return_def
                   ksPSpace_update_partial_id o_def)
  done

lemma modify_isolatable:
  assumes swap:"\<And>tsrs act s. \<forall>x. tcb_at' (idx x) s \<Longrightarrow>
            (ksPSpace_update (partial_overwrite idx tsrs) ((f s)\<lparr> ksSchedulerAction := act \<rparr>))
                = f (ksPSpace_update (partial_overwrite idx tsrs)
                      (s \<lparr> ksSchedulerAction := act\<rparr>))"
  shows
     "thread_actions_isolatable idx (modify f)"
  apply (clarsimp simp: thread_actions_isolatable_def)
  apply (simp add: isolate_thread_actions_def select_f_returns
                   liftM_def bind_assoc)
  apply (clarsimp simp: monadic_rewrite_def exec_gets
                   getSchedulerAction_def)
  apply (simp add: simpler_modify_def o_def)
  apply (subst swap)
   apply (simp add: obj_at_partial_overwrite_If)
  apply (simp add: ksPSpace_update_partial_id o_def)
  done

lemma isolate_thread_actions_wrap_bind:
  "inj idx \<Longrightarrow>
   do x \<leftarrow> isolate_thread_actions idx a b c;
      isolate_thread_actions idx (d x) e f
   od =
   isolate_thread_actions idx
             (do x \<leftarrow> isolate_thread_actions idx a id id;
                 isolate_thread_actions idx (d x) id id
                od) (e o b) (f o c)
   "
  apply (rule ext)
  apply (clarsimp simp: isolate_thread_actions_def bind_assoc split_def
                        bind_select_f_bind[symmetric] liftM_def
                        select_f_returns select_f_selects
                        getSchedulerAction_def)
  apply (clarsimp simp: exec_gets getSchedulerAction_def o_def)
  apply (rule select_bind_eq)
  apply (simp add: exec_gets exec_modify o_def)
  apply (rule select_bind_eq)
  apply (simp add: exec_modify)
  done

lemma monadic_rewrite_in_isolate_thread_actions:
  "\<lbrakk> inj idx; monadic_rewrite F True P a d \<rbrakk> \<Longrightarrow>
   monadic_rewrite F True (\<lambda>s. P (ksSchedulerAction_update (\<lambda>_. ResumeCurrentThread)
                            (ksPSpace_update (partial_overwrite idx (\<lambda>_. undefined)) s)))
     (isolate_thread_actions idx a b c) (isolate_thread_actions idx d b c)"
  apply (clarsimp simp: isolate_thread_actions_def split_def)
  apply (rule monadic_rewrite_bind_tail)+
     apply (rule_tac P="\<lambda>_. P s" in monadic_rewrite_bind_head)
     apply (simp add: monadic_rewrite_def select_f_def)
    apply wp+
  apply simp
  done

lemma thread_actions_isolatable_bind:
  "\<lbrakk> thread_actions_isolatable idx f; \<And>x. thread_actions_isolatable idx (g x);
       \<And>t. \<lbrace>tcb_at' t\<rbrace> f \<lbrace>\<lambda>rv. tcb_at' t\<rbrace> \<rbrakk>
     \<Longrightarrow> thread_actions_isolatable idx (f >>= g)"
  apply (clarsimp simp: thread_actions_isolatable_def)
  apply (rule monadic_rewrite_imp)
   apply (rule monadic_rewrite_trans)
    apply (erule monadic_rewrite_bind2, assumption)
    apply (rule hoare_vcg_all_lift, assumption)
   apply (subst isolate_thread_actions_wrap_bind, simp)
   apply simp
   apply (rule monadic_rewrite_in_isolate_thread_actions, assumption)
   apply (rule monadic_rewrite_transverse)
    apply (erule monadic_rewrite_bind2, assumption)
    apply (rule hoare_vcg_all_lift, assumption)
   apply (simp add: bind_assoc id_def)
   apply (rule monadic_rewrite_refl)
  apply (simp add: obj_at_partial_overwrite_If)
  done

lemma thread_actions_isolatable_return:
  "thread_actions_isolatable idx (return v)"
  apply (clarsimp simp: thread_actions_isolatable_def
                        monadic_rewrite_def liftM_def
                        isolate_thread_actions_def
                        split_def bind_assoc select_f_returns
                        exec_gets getSchedulerAction_def)
  apply (simp add: exec_modify return_def o_def
                   ksPSpace_update_partial_id)
  done

lemma thread_actions_isolatable_fail:
  "thread_actions_isolatable idx fail"
  by (simp add: thread_actions_isolatable_def
                isolate_thread_actions_def select_f_asserts
                liftM_def bind_assoc getSchedulerAction_def
                monadic_rewrite_def exec_gets)

lemma thread_actions_isolatable_returns:
  "thread_actions_isolatable idx (return v)"
  "thread_actions_isolatable idx (returnOk v)"
  "thread_actions_isolatable idx (throwError v)"
  by (simp add: returnOk_def throwError_def
                thread_actions_isolatable_return)+

lemma thread_actions_isolatable_bindE:
  "\<lbrakk> thread_actions_isolatable idx f; \<And>x. thread_actions_isolatable idx (g x);
       \<And>t. \<lbrace>tcb_at' t\<rbrace> f \<lbrace>\<lambda>rv. tcb_at' t\<rbrace> \<rbrakk>
     \<Longrightarrow> thread_actions_isolatable idx (f >>=E g)"
  apply (simp add: bindE_def)
  apply (erule thread_actions_isolatable_bind)
   apply (simp add: lift_def thread_actions_isolatable_returns
             split: sum.split)
  apply assumption
  done

lemma thread_actions_isolatable_catch:
  "\<lbrakk> thread_actions_isolatable idx f; \<And>x. thread_actions_isolatable idx (g x);
       \<And>t. \<lbrace>tcb_at' t\<rbrace> f \<lbrace>\<lambda>rv. tcb_at' t\<rbrace> \<rbrakk>
     \<Longrightarrow> thread_actions_isolatable idx (f <catch> g)"
  apply (simp add: catch_def)
  apply (erule thread_actions_isolatable_bind)
   apply (simp add: thread_actions_isolatable_returns
             split: sum.split)
  apply assumption
  done

lemma thread_actions_isolatable_if:
  "\<lbrakk> P \<Longrightarrow> thread_actions_isolatable idx a;
     \<not> P \<Longrightarrow> thread_actions_isolatable idx b \<rbrakk>
      \<Longrightarrow> thread_actions_isolatable idx (if P then a else b)"
  by (cases P, simp_all)

lemma select_f_isolatable:
  "thread_actions_isolatable idx (select_f v)"
  apply (clarsimp simp: thread_actions_isolatable_def
                        isolate_thread_actions_def
                        split_def select_f_selects liftM_def bind_assoc)
  apply (rule monadic_rewrite_imp, rule monadic_rewrite_transverse)
    apply (rule monadic_rewrite_drop_modify monadic_rewrite_bind_tail)+
       apply wp+
   apply (simp add: gets_bind_ign getSchedulerAction_def)
   apply (rule monadic_rewrite_refl)
  apply (simp add: ksPSpace_update_partial_id o_def)
  done

lemma doMachineOp_isolatable:
  "thread_actions_isolatable idx (doMachineOp m)"
  apply (simp add: doMachineOp_def split_def)
  apply (intro thread_actions_isolatable_bind[OF _ _ hoare_pre(1)]
               gets_isolatable thread_actions_isolatable_returns
               modify_isolatable select_f_isolatable)
  apply (simp | wp)+
  done

lemma page_directory_at_partial_overwrite:
  "\<forall>x. tcb_at' (idx x) s \<Longrightarrow>
   page_directory_at' p (ksPSpace_update (partial_overwrite idx f) s)
      = page_directory_at' p s"
  by (simp add: page_directory_at'_def typ_at_to_obj_at_arches
                obj_at_partial_overwrite_id2)

lemma findPDForASID_isolatable:
  "thread_actions_isolatable idx (findPDForASID asid)"
  apply (simp add: findPDForASID_def liftE_bindE liftME_def bindE_assoc
                   case_option_If2 assertE_def liftE_def checkPDAt_def
                   stateAssert_def2
             cong: if_cong)
  apply (intro thread_actions_isolatable_bind[OF _ _ hoare_pre(1)]
               thread_actions_isolatable_bindE[OF _ _ hoare_pre(1)]
               thread_actions_isolatable_if thread_actions_isolatable_returns
               thread_actions_isolatable_fail
               gets_isolatable getObject_isolatable)
    apply (simp add: projectKO_opt_asidpool page_directory_at_partial_overwrite
           | wp getASID_wp)+
  done

lemma getHWASID_isolatable:
  "thread_actions_isolatable idx (getHWASID asid)"
  apply (simp add: getHWASID_def loadHWASID_def
                   findFreeHWASID_def
                   case_option_If2 findPDForASIDAssert_def
                   checkPDAt_def checkPDUniqueToASID_def
                   checkPDASIDMapMembership_def
                   stateAssert_def2 const_def assert_def
                   findFreeHWASID_def
                   invalidateASID_def
                   invalidateHWASIDEntry_def
                   storeHWASID_def
             cong: if_cong)
  apply (intro thread_actions_isolatable_bind[OF _ _ hoare_pre(1)]
               thread_actions_isolatable_bindE[OF _ _ hoare_pre(1)]
               thread_actions_isolatable_catch[OF _ _ hoare_pre(1)]
               thread_actions_isolatable_if thread_actions_isolatable_returns
               thread_actions_isolatable_fail
               gets_isolatable modify_isolatable
               findPDForASID_isolatable doMachineOp_isolatable)
  apply (wp hoare_drop_imps
            | simp add: page_directory_at_partial_overwrite)+
  done

lemma setVMRoot_isolatable:
  "thread_actions_isolatable idx (setVMRoot t)"
  apply (simp add: setVMRoot_def getThreadVSpaceRoot_def
                   locateSlot_conv getSlotCap_def
                   cap_case_isPageDirectoryCap if_bool_simps
                   whenE_def liftE_def
                   checkPDNotInASIDMap_def stateAssert_def2
                   checkPDASIDMapMembership_def armv_contextSwitch_def
             cong: if_cong)
  apply (intro thread_actions_isolatable_bind[OF _ _ hoare_pre(1)]
               thread_actions_isolatable_bindE[OF _ _ hoare_pre(1)]
               thread_actions_isolatable_catch[OF _ _ hoare_pre(1)]
               thread_actions_isolatable_if thread_actions_isolatable_returns
               thread_actions_isolatable_fail
               gets_isolatable getCTE_isolatable getHWASID_isolatable
               findPDForASID_isolatable doMachineOp_isolatable)
    apply (simp add: projectKO_opt_asidpool
           | wp getASID_wp typ_at_lifts [OF getHWASID_typ_at'])+
  sorry (* FIXME ARMHYP
  done *)

lemma transferCaps_simple:
  "transferCaps mi [] ep receiver rcvrBuf =
        do
          getReceiveSlots receiver rcvrBuf;
          return (mi\<lparr>msgExtraCaps := 0, msgCapsUnwrapped := 0\<rparr>)
        od"
  apply (cases mi)
  apply (clarsimp simp: transferCaps_def getThreadCSpaceRoot_def locateSlot_conv)
  apply (rule ext bind_apply_cong[OF refl])+
  apply (simp add: upto_enum_def
            split: option.split)
  done

lemma transferCaps_simple_rewrite:
  "monadic_rewrite True True ((\<lambda>_. caps = []) and \<top>)
   (transferCaps mi caps ep r rBuf)
   (return (mi \<lparr> msgExtraCaps := 0, msgCapsUnwrapped := 0 \<rparr>))"
  including no_pre
  apply (rule monadic_rewrite_gen_asm)
  apply (rule monadic_rewrite_imp)
   apply (rule monadic_rewrite_trans)
    apply (simp add: transferCaps_simple, rule monadic_rewrite_refl)
   apply (rule monadic_rewrite_symb_exec2, (wp empty_fail_getReceiveSlots)+)
   apply (rule monadic_rewrite_refl)
  apply simp
  done

lemma lookupExtraCaps_simple_rewrite:
  "msgExtraCaps mi = 0 \<Longrightarrow>
      (lookupExtraCaps thread rcvBuf mi = returnOk [])"
  by (cases mi, simp add: lookupExtraCaps_def getExtraCPtrs_def
                          liftE_bindE upto_enum_step_def mapM_Nil
                   split: option.split)

lemma lookupIPC_inv: "\<lbrace>P\<rbrace> lookupIPCBuffer f t \<lbrace>\<lambda>rv. P\<rbrace>"
  by wp

lemmas empty_fail_user_getreg = empty_fail_asUser[OF empty_fail_getRegister]

lemma user_getreg_rv:
  "\<lbrace>obj_at' (\<lambda>tcb. P ((atcbContextGet o tcbArch) tcb r)) t\<rbrace> asUser t (getRegister r) \<lbrace>\<lambda>rv s. P rv\<rbrace>"
  apply (simp add: asUser_def split_def)
  apply (wp threadGet_wp)
  apply (clarsimp simp: obj_at'_def projectKOs getRegister_def in_monad atcbContextGet_def)
  done

lemma copyMRs_simple:
  "msglen \<le> of_nat (length ARM_HYP_H.msgRegisters) \<longrightarrow>
    copyMRs sender sbuf receiver rbuf msglen
        = forM_x (take (unat msglen) ARM_HYP_H.msgRegisters)
             (\<lambda>r. do v \<leftarrow> asUser sender (getRegister r);
                    asUser receiver (setRegister r v) od)
           >>= (\<lambda>rv. return msglen)"
  apply (clarsimp simp: copyMRs_def mapM_discarded)
  apply (rule bind_cong[OF refl])
  apply (simp add: length_msgRegisters n_msgRegisters_def min_def
                   word_le_nat_alt
            split: option.split)
  apply (simp add: upto_enum_def mapM_Nil)
  done

lemma doIPCTransfer_simple_rewrite:
  "monadic_rewrite True True
   ((\<lambda>_. msgExtraCaps (messageInfoFromWord msgInfo) = 0
               \<and> msgLength (messageInfoFromWord msgInfo)
                      \<le> of_nat (length ARM_HYP_H.msgRegisters))
      and obj_at' (\<lambda>tcb. tcbFault tcb = None
               \<and> (atcbContextGet o tcbArch) tcb msgInfoRegister = msgInfo) sender)
   (doIPCTransfer sender ep badge True rcvr)
   (do rv \<leftarrow> mapM_x (\<lambda>r. do v \<leftarrow> asUser sender (getRegister r);
                             asUser rcvr (setRegister r v)
                          od)
               (take (unat (msgLength (messageInfoFromWord msgInfo))) ARM_HYP_H.msgRegisters);
         y \<leftarrow> setMessageInfo rcvr ((messageInfoFromWord msgInfo) \<lparr>msgCapsUnwrapped := 0\<rparr>);
         asUser rcvr (setRegister ARM_HYP_H.badgeRegister badge)
      od)"
  apply (rule monadic_rewrite_gen_asm)
  apply (simp add: doIPCTransfer_def bind_assoc doNormalTransfer_def
                   getMessageInfo_def
             cong: option.case_cong)
  apply (rule monadic_rewrite_imp)
   apply (rule monadic_rewrite_trans)
    apply (rule monadic_rewrite_bind_tail)+
      apply (rule_tac P="fault = None" in monadic_rewrite_gen_asm, simp)
      apply (rule monadic_rewrite_bind_tail)
       apply (rule_tac x=msgInfo in monadic_rewrite_symb_exec,
              (wp empty_fail_user_getreg user_getreg_rv)+)
       apply (simp add: lookupExtraCaps_simple_rewrite returnOk_catch_bind)
       apply (rule monadic_rewrite_bind)
         apply (rule monadic_rewrite_from_simple, rule copyMRs_simple)
        apply (rule monadic_rewrite_bind_head)
        apply (rule transferCaps_simple_rewrite)
       apply (wp threadGet_const)+
   apply (simp add: bind_assoc)
   apply (rule monadic_rewrite_symb_exec2[OF lookupIPC_inv empty_fail_lookupIPCBuffer]
               monadic_rewrite_symb_exec2[OF threadGet_inv empty_fail_threadGet]
               monadic_rewrite_symb_exec2[OF user_getreg_inv' empty_fail_user_getreg]
               monadic_rewrite_bind_head monadic_rewrite_bind_tail
                  | wp)+
    apply (case_tac "messageInfoFromWord msgInfo")
    apply simp
    apply (rule monadic_rewrite_refl)
   apply wp
  apply clarsimp
  apply (auto elim!: obj_at'_weakenE)
  done

lemma monadic_rewrite_setSchedulerAction_noop:
  "monadic_rewrite F E (\<lambda>s. ksSchedulerAction s = act) (setSchedulerAction act) (return ())"
  unfolding setSchedulerAction_def
  apply (rule monadic_rewrite_imp, rule monadic_rewrite_modify_noop)
  apply simp
  done

lemma rescheduleRequired_simple_rewrite:
  "monadic_rewrite F E
     (sch_act_simple)
     rescheduleRequired
     (setSchedulerAction ChooseNewThread)"
  apply (simp add: rescheduleRequired_def getSchedulerAction_def)
  apply (simp add: monadic_rewrite_def exec_gets sch_act_simple_def)
  apply auto
  done

lemma empty_fail_isRunnable:
  "empty_fail (isRunnable t)"
  by (simp add: isRunnable_def isBlocked_def)

lemma setThreadState_blocked_rewrite:
  "\<not> runnable' st \<Longrightarrow>
   monadic_rewrite True True
     (\<lambda>s. ksCurThread s = t \<and> ksSchedulerAction s \<noteq> ResumeCurrentThread \<and> tcb_at' t s)
     (setThreadState st t)
     (threadSet (tcbState_update (\<lambda>_. st)) t)"
  apply (simp add: setThreadState_def)
  apply (rule monadic_rewrite_imp)
   apply (rule monadic_rewrite_trans)
    apply (rule monadic_rewrite_bind_tail)
     apply (rule monadic_rewrite_trans)
      apply (rule monadic_rewrite_bind_tail)+
         apply (rule_tac P="\<not> runnable \<and> curThread = t
                              \<and> (action \<noteq> ResumeCurrentThread)"
                    in monadic_rewrite_gen_asm)
         apply (simp add: when_def)
         apply (rule monadic_rewrite_refl)
        apply wp+
     apply (rule monadic_rewrite_symb_exec2,
            (wp  empty_fail_isRunnable
               | (simp only: getCurThread_def getSchedulerAction_def
                      , rule empty_fail_gets))+)+
     apply (rule monadic_rewrite_refl)
    apply (simp add: conj_comms, wp)
    apply (rule_tac Q="\<lambda>rv s. obj_at' (Not o runnable' o tcbState) t s"
               in hoare_post_imp)
     apply (clarsimp simp: obj_at'_def sch_act_simple_def st_tcb_at'_def)
    apply (wp)
   apply simp
   apply (rule monadic_rewrite_refl)
  apply clarsimp
  done

lemma setupCallerCap_rewrite:
  "monadic_rewrite True True (\<lambda>s. reply_masters_rvk_fb (ctes_of s))
   (setupCallerCap send rcv)
   (do setThreadState BlockedOnReply send;
       replySlot \<leftarrow> getThreadReplySlot send;
       callerSlot \<leftarrow> getThreadCallerSlot rcv;
       replySlotCTE \<leftarrow> getCTE replySlot;
       assert (mdbNext (cteMDBNode replySlotCTE) = 0
                 \<and> isReplyCap (cteCap replySlotCTE)
                 \<and> capReplyMaster (cteCap replySlotCTE)
                 \<and> mdbFirstBadged (cteMDBNode replySlotCTE)
                 \<and> mdbRevocable (cteMDBNode replySlotCTE));
       cteInsert (ReplyCap send False) replySlot callerSlot
    od)"
  apply (simp add: setupCallerCap_def getThreadCallerSlot_def
                   getThreadReplySlot_def locateSlot_conv
                   getSlotCap_def)
  apply (rule monadic_rewrite_imp)
   apply (rule monadic_rewrite_bind_tail)+
     apply (rule monadic_rewrite_assert)+
     apply (rule_tac P="mdbFirstBadged (cteMDBNode masterCTE)
                        \<and> mdbRevocable (cteMDBNode masterCTE)"
                 in monadic_rewrite_gen_asm)
     apply simp
     apply (rule monadic_rewrite_trans)
      apply (rule monadic_rewrite_bind_tail)
       apply (rule monadic_rewrite_symb_exec2, (wp | simp)+)+
       apply (rule monadic_rewrite_refl)
      apply wp+
     apply (rule monadic_rewrite_symb_exec2, (wp empty_fail_getCTE)+)+
     apply (rule monadic_rewrite_refl)
    apply (wp getCTE_wp' | simp add: cte_wp_at_ctes_of)+
  apply (clarsimp simp: reply_masters_rvk_fb_def)
  apply fastforce
  done

lemma attemptSwitchTo_rewrite:
  "monadic_rewrite True True
          (\<lambda>s. obj_at' (\<lambda>tcb. tcbPriority tcb = curPrio) thread s
              \<and> obj_at' (\<lambda>tcb. tcbPriority tcb = destPrio \<and> tcbDomain tcb = destDom) t s
              \<and> destPrio \<ge> curPrio
              \<and> ksSchedulerAction s = ResumeCurrentThread
              \<and> ksCurThread s = thread
              \<and> ksCurDomain s = curDom
              \<and> destDom = curDom)
    (attemptSwitchTo t) (setSchedulerAction (SwitchToThread t))"
  apply (simp add: attemptSwitchTo_def possibleSwitchTo_def)
  apply (rule monadic_rewrite_imp)
   apply (rule monadic_rewrite_trans)
    apply (rule monadic_rewrite_bind_tail)
     apply (rule monadic_rewrite_bind_tail)
      apply (rule monadic_rewrite_bind_tail)
       apply (rule monadic_rewrite_bind_tail)
        apply (rule monadic_rewrite_bind_tail)
         apply (rule monadic_rewrite_bind_tail)
          apply (rule_tac P="curPrio \<le> targetPrio \<and> action = ResumeCurrentThread
                                \<and> targetDom = curDom"
                    in monadic_rewrite_gen_asm)
          apply (simp add: eq_commute le_less[symmetric])
          apply (rule monadic_rewrite_refl)
         apply (wp threadGet_wp)+
   apply (rule monadic_rewrite_trans)
    apply (rule monadic_rewrite_bind_tail)
     apply (rule monadic_rewrite_symb_exec2,
            (wp empty_fail_threadGet)+ | simp add: getSchedulerAction_def curDomain_def)+
     apply (rule monadic_rewrite_refl)
    apply wp
   apply (rule monadic_rewrite_symb_exec2, simp_all add: getCurThread_def)
   apply (rule monadic_rewrite_refl)
  apply (auto simp: obj_at'_def)
  done

lemma oblivious_getObject_ksPSpace_default:
  "\<lbrakk> \<forall>s. ksPSpace (f s) = ksPSpace s;
      \<And>a b c ko. (loadObject a b c ko :: 'a kernel) \<equiv> loadObject_default a b c ko \<rbrakk> \<Longrightarrow>
   oblivious f (getObject p :: ('a :: pspace_storable) kernel)"
  apply (simp add: getObject_def split_def loadObject_default_def
                   projectKO_def2 alignCheck_assert magnitudeCheck_assert)
  apply (intro oblivious_bind, simp_all)
  done

lemmas oblivious_getObject_ksPSpace_tcb[simp]
    = oblivious_getObject_ksPSpace_default[OF _ loadObject_tcb]

lemma oblivious_setObject_ksPSpace_tcb[simp]:
  "\<lbrakk> \<forall>s. ksPSpace (f s) = ksPSpace s;
     \<forall>s g. ksPSpace_update g (f s) = f (ksPSpace_update g s) \<rbrakk> \<Longrightarrow>
   oblivious f (setObject p (v :: tcb))"
  apply (simp add: setObject_def split_def updateObject_default_def
                   projectKO_def2 alignCheck_assert magnitudeCheck_assert)
  apply (intro oblivious_bind, simp_all)
  done

lemma oblivious_getObject_ksPSpace_cte[simp]:
  "\<lbrakk> \<forall>s. ksPSpace (f s) = ksPSpace s \<rbrakk> \<Longrightarrow>
   oblivious f (getObject p :: cte kernel)"
  apply (simp add: getObject_def split_def loadObject_cte
                   projectKO_def2 alignCheck_assert magnitudeCheck_assert
                   typeError_def unless_when
             cong: Structures_H.kernel_object.case_cong)
  apply (intro oblivious_bind,
         simp_all split: Structures_H.kernel_object.split if_split)
  by (safe intro!: oblivious_bind, simp_all)

lemma oblivious_doMachineOp[simp]:
  "\<lbrakk> \<forall>s. ksMachineState (f s) = ksMachineState s;
     \<forall>g s. ksMachineState_update g (f s) = f (ksMachineState_update g s) \<rbrakk>
      \<Longrightarrow> oblivious f (doMachineOp oper)"
  apply (simp add: doMachineOp_def split_def)
  apply (intro oblivious_bind, simp_all)
  done

lemmas oblivious_getObject_ksPSpace_asidpool[simp]
    = oblivious_getObject_ksPSpace_default[OF _ loadObject_asidpool]

lemma oblivious_setVMRoot_schact:
  "oblivious (ksSchedulerAction_update f) (setVMRoot t)"
  apply (simp add: setVMRoot_def getThreadVSpaceRoot_def locateSlot_conv
                   getSlotCap_def getCTE_def armv_contextSwitch_def)
sorry (* FIXME ARMHYP should still be true, vcpuSwitch does not change the scheduler info, but
                      that's harder to prove
  by (safe intro!: oblivious_bind oblivious_bindE oblivious_catch
             | simp_all add: liftE_def getHWASID_def
                             findPDForASID_def liftME_def loadHWASID_def
                             findPDForASIDAssert_def checkPDAt_def
                             checkPDUniqueToASID_def
                             checkPDASIDMapMembership_def
                             findFreeHWASID_def invalidateASID_def
                             invalidateHWASIDEntry_def storeHWASID_def
                             checkPDNotInASIDMap_def armv_contextSwitch_def
                             vcpuSwitch_def vcpuDisable_def
                      split: capability.split arch_capability.split option.split)+
*)

lemma oblivious_switchToThread_schact:
  "oblivious (ksSchedulerAction_update f) (ThreadDecls_H.switchToThread t)"
  apply (simp add: Thread_H.switchToThread_def ARM_HYP_H.switchToThread_def bind_assoc
                   getCurThread_def setCurThread_def threadGet_def liftM_def
                   threadSet_def tcbSchedEnqueue_def unless_when asUser_def
                   getQueue_def setQueue_def storeWordUser_def setRegister_def
                   pointerInUserData_def isRunnable_def isBlocked_def
                   getThreadState_def tcbSchedDequeue_def bitmap_fun_defs)
  by (safe intro!: oblivious_bind
              | simp_all add: oblivious_setVMRoot_schact)+

lemma schedule_rewrite:
  notes hoare_TrueI[simp]
  shows "monadic_rewrite True True
            (\<lambda>s. ksSchedulerAction s = SwitchToThread t \<and> ct_in_state' (op = Running) s)
            (schedule)
            (do curThread \<leftarrow> getCurThread; tcbSchedEnqueue curThread; setSchedulerAction ResumeCurrentThread; switchToThread t od)"
  apply (simp add: schedule_def)
  apply (rule monadic_rewrite_imp)
   apply (rule monadic_rewrite_trans)
    apply (rule monadic_rewrite_bind_tail)
     apply (rule monadic_rewrite_bind_tail)
      apply (rule_tac P="action = SwitchToThread t" in monadic_rewrite_gen_asm, simp)
      apply (rule monadic_rewrite_bind_tail)
       apply (rule_tac P="curRunnable \<and> action = SwitchToThread t" in monadic_rewrite_gen_asm, simp)
       apply (rule monadic_rewrite_refl)
      apply (wp,simp,wp+)
   apply (rule monadic_rewrite_trans)
    apply (rule monadic_rewrite_bind_tail)
     apply (rule monadic_rewrite_symb_exec2, wp | simp add: isRunnable_def getSchedulerAction_def)+
     apply (rule monadic_rewrite_refl)
    apply (wp)
   apply (simp add: setSchedulerAction_def)
   apply (subst oblivious_modify_swap[symmetric], rule oblivious_switchToThread_schact)
   apply (rule monadic_rewrite_refl)
  apply (clarsimp simp: st_tcb_at'_def pred_neg_def o_def obj_at'_def ct_in_state'_def)
  done

lemma empty_fail_getCurThread[iff]:
  "empty_fail getCurThread" by (simp add: getCurThread_def)

lemma schedule_rewrite_ct_not_runnable':
  "monadic_rewrite True True
            (\<lambda>s. ksSchedulerAction s = SwitchToThread t \<and> ct_in_state' (Not \<circ> runnable') s)
            (schedule)
            (do setSchedulerAction ResumeCurrentThread; switchToThread t od)"
  apply (simp add: schedule_def)
  apply (rule monadic_rewrite_imp)
   apply (rule monadic_rewrite_trans)
    apply (rule monadic_rewrite_bind_tail)
     apply (rule monadic_rewrite_bind_tail)
      apply (rule_tac P="action = SwitchToThread t" in monadic_rewrite_gen_asm, simp)
      apply (rule monadic_rewrite_bind_tail)
       apply (rule_tac P="\<not> curRunnable \<and> action = SwitchToThread t" in monadic_rewrite_gen_asm,simp)
       apply (rule monadic_rewrite_refl)
      apply (wp,simp,wp+)
   apply (rule monadic_rewrite_trans)
    apply (rule monadic_rewrite_bind_tail)
     apply (rule monadic_rewrite_symb_exec2, wp |
            simp add: isRunnable_def getSchedulerAction_def |
            rule hoare_TrueI)+
     apply (rule monadic_rewrite_refl)
    apply (wp)
   apply (simp add: setSchedulerAction_def)
   apply (subst oblivious_modify_swap[symmetric], rule oblivious_switchToThread_schact)
   apply (rule monadic_rewrite_symb_exec2)
   apply (wp, simp, rule hoare_TrueI)
   apply (rule monadic_rewrite_refl)
  apply (clarsimp simp: st_tcb_at'_def pred_neg_def o_def obj_at'_def ct_in_state'_def)
  done

lemma activateThread_simple_rewrite:
  "monadic_rewrite True True (ct_in_state' (op = Running))
       (activateThread) (return ())"
  apply (simp add: activateThread_def)
  apply (rule monadic_rewrite_imp)
   apply (rule monadic_rewrite_trans, rule monadic_rewrite_bind_tail)+
       apply (rule_tac P="state = Running" in monadic_rewrite_gen_asm)
       apply simp
       apply (rule monadic_rewrite_refl)
      apply wp
     apply (rule monadic_rewrite_symb_exec2, (wp empty_fail_getThreadState)+)
     apply (rule monadic_rewrite_refl)
    apply wp
   apply (rule monadic_rewrite_symb_exec2,
          simp_all add: getCurThread_def)
   apply (rule monadic_rewrite_refl)
  apply (clarsimp simp: ct_in_state'_def elim!: pred_tcb'_weakenE)
  done

end

lemma setCTE_obj_at_prio[wp]:
  "\<lbrace>obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t\<rbrace> setCTE p v \<lbrace>\<lambda>rv. obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t\<rbrace>"
  unfolding setCTE_def
  by (rule setObject_cte_obj_at_tcb', simp+)

crunch obj_at_prio[wp]: cteInsert "obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t"
  (wp: crunch_wps)

crunch ctes_of[wp]: asUser "\<lambda>s. P (ctes_of s)"
  (wp: crunch_wps)

lemma tcbSchedEnqueue_tcbPriority[wp]:
  "\<lbrace>obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t\<rbrace>
     tcbSchedEnqueue t'
   \<lbrace>\<lambda>rv. obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t\<rbrace>"
  apply (simp add: tcbSchedEnqueue_def unless_def)
  apply (wp | simp cong: if_cong)+
  done

crunch obj_at_prio[wp]: cteDeleteOne "obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t"
  (wp: crunch_wps setEndpoint_obj_at_tcb'
       setThreadState_obj_at_unchanged setNotification_tcb setBoundNotification_obj_at_unchanged
        simp: crunch_simps unless_def)

context kernel_m begin

lemma setThreadState_no_sch_change:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s) \<and> (runnable' st \<or> t \<noteq> ksCurThread s)\<rbrace>
      setThreadState st t
   \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  (is "NonDetMonad.valid ?P ?f ?Q")
  apply (simp add: setThreadState_def setSchedulerAction_def)
  apply (wp hoare_pre_cont[where a=rescheduleRequired])
  apply (rule_tac Q="\<lambda>_. ?P and st_tcb_at' (op = st) t" in hoare_post_imp)
   apply (clarsimp split: if_split)
   apply (clarsimp simp: obj_at'_def st_tcb_at'_def projectKOs)
  apply (wp threadSet_pred_tcb_at_state)
  apply simp
  done

lemma asUser_obj_at_unchangedT:
  assumes x: "\<forall>tcb con con'. con' \<in> fst (m con)
        \<longrightarrow> P (tcbArch_update (\<lambda>_. atcbContextSet (snd con') (tcbArch tcb)) tcb) = P tcb" shows
  "\<lbrace>obj_at' P t\<rbrace> asUser t' m \<lbrace>\<lambda>rv. obj_at' P t\<rbrace>"
  apply (simp add: asUser_def split_def)
  apply (wp threadSet_obj_at' threadGet_wp)
  apply (clarsimp simp: obj_at'_def projectKOs x cong: if_cong)
  done

lemmas asUser_obj_at_unchanged
    = asUser_obj_at_unchangedT[OF all_tcbI, rule_format]

lemma bind_assoc:
  "do y \<leftarrow> do x \<leftarrow> m; f x od; g y od
     = do x \<leftarrow> m; y \<leftarrow> f x; g y od"
  by (rule bind_assoc)

lemma setObject_modify_assert:
  "\<lbrakk> updateObject v = updateObject_default v \<rbrakk>
    \<Longrightarrow> setObject p v = do f \<leftarrow> gets (obj_at' (\<lambda>v'. v = v' \<or> True) p);
                         assert f; modify (ksPSpace_update (\<lambda>ps. ps(p \<mapsto> injectKO v))) od"
  using objBits_2n[where obj=v]
  apply (simp add: setObject_def split_def updateObject_default_def
                   bind_assoc projectKO_def2 alignCheck_assert)
  apply (rule ext, simp add: exec_gets)
  apply (case_tac "obj_at' (\<lambda>v'. v = v' \<or> True) p x")
   apply (clarsimp simp: obj_at'_def projectKOs lookupAround2_known1
                         assert_opt_def)
   apply (clarsimp simp: project_inject)
   apply (simp only: objBits_def objBitsT_koTypeOf[symmetric] koTypeOf_injectKO)
   apply (simp add: magnitudeCheck_assert2 simpler_modify_def)
  apply (clarsimp simp: assert_opt_def assert_def magnitudeCheck_assert2
                 split: option.split if_split)
  apply (clarsimp simp: obj_at'_def projectKOs)
  apply (clarsimp simp: project_inject)
  apply (simp only: objBits_def objBitsT_koTypeOf[symmetric]
                    koTypeOf_injectKO simp_thms)
  done

lemma setEndpoint_isolatable:
  "thread_actions_isolatable idx (setEndpoint p e)"
  apply (simp add: setEndpoint_def setObject_modify_assert
                   assert_def)
  apply (case_tac "p \<in> range idx")
   apply (clarsimp simp: thread_actions_isolatable_def
                         monadic_rewrite_def fun_eq_iff
                         liftM_def isolate_thread_actions_def
                         bind_assoc exec_gets getSchedulerAction_def
                         bind_select_f_bind[symmetric])
   apply (simp add: obj_at_partial_overwrite_id2)
   apply (drule_tac x=x in spec)
   apply (clarsimp simp: obj_at'_def projectKOs select_f_asserts)
  apply (intro thread_actions_isolatable_bind[OF _ _ hoare_pre(1)]
               thread_actions_isolatable_if
               thread_actions_isolatable_return
               thread_actions_isolatable_fail)
       apply (rule gets_isolatable)
       apply (simp add: obj_at_partial_overwrite_id2)
      apply (rule modify_isolatable)
      apply (clarsimp simp: o_def partial_overwrite_def)
      apply (rule kernel_state.fold_congs[OF refl refl])
      apply (clarsimp simp: fun_eq_iff
                     split: if_split)
     apply (wp | simp)+
  done

lemma setCTE_assert_modify:
  "setCTE p v = do c \<leftarrow> gets (real_cte_at' p);
                   t \<leftarrow> gets (tcb_at' (p && ~~ mask 9)
                                 and K ((p && mask 9) \<in> dom tcb_cte_cases));
                   if c then modify (ksPSpace_update (\<lambda>ps. ps(p \<mapsto> KOCTE v)))
                   else if t then
                     modify (ksPSpace_update
                               (\<lambda>ps. ps (p && ~~ mask 9 \<mapsto>
                                           KOTCB (snd (the (tcb_cte_cases (p && mask 9))) (K v)
                                                (the (projectKO_opt (the (ps (p && ~~ mask 9)))))))))
                   else fail od"
  apply (clarsimp simp: setCTE_def setObject_def split_def
                        fun_eq_iff exec_gets)
  apply (case_tac "real_cte_at' p x")
   apply (clarsimp simp: obj_at'_def projectKOs lookupAround2_known1
                         assert_opt_def alignCheck_assert objBits_simps
                         magnitudeCheck_assert2 updateObject_cte)
   apply (simp add: simpler_modify_def)
  apply (simp split: if_split, intro conjI impI)
   apply (clarsimp simp: obj_at'_def projectKOs)
   apply (subgoal_tac "p \<le> (p && ~~ mask 9) + 2 ^ 9 - 1")
    apply (subgoal_tac "fst (lookupAround2 p (ksPSpace x))
                          = Some (p && ~~ mask 9, KOTCB obj)")
     apply (simp add: assert_opt_def)
     apply (subst updateObject_cte_tcb)
      apply (fastforce simp add: subtract_mask)
     apply (simp add: assert_opt_def alignCheck_assert bind_assoc
                      magnitudeCheck_assert
                      is_aligned_neg_mask2 objBits_def)
     apply (rule ps_clear_lookupAround2, assumption+)
       apply (rule word_and_le2)
      apply (simp add: objBits_simps mask_def field_simps)
     apply (simp add: simpler_modify_def cong: option.case_cong if_cong)
     apply (rule kernel_state.fold_congs[OF refl refl])
     apply (clarsimp simp: projectKO_opt_tcb cong: if_cong)
    apply (clarsimp simp: lookupAround2_char1 word_and_le2)
    apply (rule ccontr, clarsimp)
    apply (erule(2) ps_clearD)
    apply (simp add: objBits_simps mask_def field_simps)
   apply (rule tcb_cte_cases_in_range2)
    apply (simp add: subtract_mask)
   apply simp
  apply (clarsimp simp: assert_opt_def split: option.split)
  apply (rule trans [OF bind_apply_cong[OF _ refl] fun_cong[OF fail_bind]])
  apply (simp add: fail_def prod_eq_iff)
  apply (rule context_conjI)
   apply (rule ccontr, clarsimp elim!: nonemptyE)
   apply (frule(1) updateObject_cte_is_tcb_or_cte[OF _ refl])
   apply (erule disjE)
    apply clarsimp
    apply (frule(1) tcb_cte_cases_aligned_helpers)
    apply (clarsimp simp: domI[where m = cte_cte_cases] field_simps)
    apply (clarsimp simp: lookupAround2_char1 obj_at'_def projectKOs
                          objBits_simps)
   apply (clarsimp simp: obj_at'_def lookupAround2_char1
                         objBits_simps projectKOs cte_level_bits_def)
  apply (erule empty_failD[OF empty_fail_updateObject_cte])
  done

lemma partial_overwrite_fun_upd2:
  "partial_overwrite idx tsrs (f (x := y))
     = (partial_overwrite idx tsrs f)
          (x := if x \<in> range idx then put_tcb_state_regs (tsrs (inv idx x)) y
                else y)"
  by (simp add: fun_eq_iff partial_overwrite_def split: if_split)

lemma setCTE_isolatable:
  "thread_actions_isolatable idx (setCTE p v)"
  apply (simp add: setCTE_assert_modify)
  apply (clarsimp simp: thread_actions_isolatable_def
                        monadic_rewrite_def fun_eq_iff
                        liftM_def exec_gets
                        isolate_thread_actions_def
                        bind_assoc exec_gets getSchedulerAction_def
                        bind_select_f_bind[symmetric]
                        obj_at_partial_overwrite_If
                        obj_at_partial_overwrite_id2
                  cong: if_cong)
  apply (case_tac "p && ~~ mask 9 \<in> range idx \<and> p && mask 9 \<in> dom tcb_cte_cases")
   apply clarsimp
   apply (frule_tac x=x in spec, erule obj_atE')
   apply (subgoal_tac "\<not> real_cte_at' p s")
    apply (clarsimp simp: select_f_returns select_f_asserts split: if_split)
    apply (clarsimp simp: o_def simpler_modify_def partial_overwrite_fun_upd2)
    apply (rule kernel_state.fold_congs[OF refl refl])
    apply (rule ext)
    apply (clarsimp simp: partial_overwrite_get_tcb_state_regs
                   split: if_split)
    apply (clarsimp simp: projectKOs get_tcb_state_regs_def
                          put_tcb_state_regs_def put_tcb_state_regs_tcb_def
                          partial_overwrite_def
                   split: tcb_state_regs.split)
    apply (case_tac obj, simp add: projectKO_opt_tcb)
    apply (simp add: tcb_cte_cases_def split: if_split_asm)
   apply (drule_tac x=x in spec)
   apply (clarsimp simp: obj_at'_def projectKOs objBits_simps subtract_mask(2) [symmetric])
   apply (erule notE[rotated], erule (3) tcb_ctes_clear[rotated])
  apply (simp add: select_f_returns select_f_asserts split: if_split)
  apply (intro conjI impI)
    apply (clarsimp simp: simpler_modify_def fun_eq_iff
                          partial_overwrite_fun_upd2 o_def
                  intro!: kernel_state.fold_congs[OF refl refl])
    apply (clarsimp simp: obj_at'_def projectKOs objBits_simps)
    apply (erule notE[rotated], rule tcb_ctes_clear[rotated 2], assumption+)
     apply (fastforce simp add: subtract_mask)
    apply simp
   apply (clarsimp simp: simpler_modify_def
                         partial_overwrite_fun_upd2 o_def
                         partial_overwrite_get_tcb_state_regs
                 intro!: kernel_state.fold_congs[OF refl refl]
                  split: if_split)
   apply (simp add: partial_overwrite_def)
  apply (subgoal_tac "p \<notin> range idx")
   apply (clarsimp simp: simpler_modify_def
                         partial_overwrite_fun_upd2 o_def
                         partial_overwrite_get_tcb_state_regs
                 intro!: kernel_state.fold_congs[OF refl refl])
  apply clarsimp
  apply (drule_tac x=x in spec)
  apply (clarsimp simp: obj_at'_def projectKOs)
  done

lemma assert_isolatable:
  "thread_actions_isolatable idx (assert P)"
  by (simp add: assert_def thread_actions_isolatable_if
                thread_actions_isolatable_returns
                thread_actions_isolatable_fail)

lemma cteInsert_isolatable:
  "thread_actions_isolatable idx (cteInsert cap src dest)"
  apply (simp add: cteInsert_def updateCap_def updateMDB_def
                   Let_def setUntypedCapAsFull_def)
  apply (intro thread_actions_isolatable_bind[OF _ _ hoare_pre(1)]
               thread_actions_isolatable_if
               thread_actions_isolatable_returns assert_isolatable
               getCTE_isolatable setCTE_isolatable)
  apply (wp | simp)+
  done

lemma isolate_thread_actions_threadSet_tcbState:
  "\<lbrakk> inj idx; idx t' = t \<rbrakk> \<Longrightarrow>
   monadic_rewrite False True (\<lambda>s. \<forall>x. tcb_at' (idx x) s)
     (threadSet (tcbState_update (\<lambda>_. st)) t)
     (isolate_thread_actions idx (return ())
         (\<lambda>tsrs. (tsrs (t' := TCBStateRegs st (tsrContext (tsrs t')))))
             id)"
  apply (simp add: isolate_thread_actions_def bind_assoc split_def
                   select_f_returns getSchedulerAction_def)
  apply (clarsimp simp: monadic_rewrite_def exec_gets threadSet_def
                        getObject_get_assert bind_assoc liftM_def
                        setObject_modify_assert)
  apply (frule_tac x=t' in spec, drule obj_at_ko_at')
  apply (clarsimp simp: exec_gets simpler_modify_def o_def
                intro!: kernel_state.fold_congs[OF refl refl])
  apply (simp add: partial_overwrite_fun_upd
                   partial_overwrite_get_tcb_state_regs)
  apply (clarsimp simp: put_tcb_state_regs_def put_tcb_state_regs_tcb_def
                        projectKOs get_tcb_state_regs_def
                 elim!: obj_atE')
  apply (case_tac ko)
  apply (simp add: projectKO_opt_tcb)
  done

lemma thread_actions_isolatableD:
  "\<lbrakk> thread_actions_isolatable idx f; inj idx \<rbrakk>
     \<Longrightarrow> monadic_rewrite False True (\<lambda>s. (\<forall>x. tcb_at' (idx x) s))
            f (isolate_thread_actions idx f id id)"
  by (clarsimp simp: thread_actions_isolatable_def)

lemma tcbSchedDequeue_rewrite:
  "monadic_rewrite True True (obj_at' (Not \<circ> tcbQueued) t) (tcbSchedDequeue t) (return ())"
  apply (simp add: tcbSchedDequeue_def)
  apply (rule monadic_rewrite_imp)
   apply (rule monadic_rewrite_trans)
    apply (rule monadic_rewrite_bind_tail)
     apply (rule_tac P="\<not> queued" in monadic_rewrite_gen_asm)
     apply (simp add: when_def)
     apply (rule monadic_rewrite_refl)
    apply (wp threadGet_const)
   apply (rule monadic_rewrite_symb_exec2)
      apply wp+
   apply (rule monadic_rewrite_refl)
  apply (clarsimp)
  done

lemma switchToThread_rewrite:
  "monadic_rewrite True True
       (ct_in_state' (Not \<circ> runnable') and cur_tcb' and obj_at' (Not \<circ> tcbQueued) t)
       (switchToThread t)
       (do Arch.switchToThread t; setCurThread t od)"
  apply (simp add: switchToThread_def Thread_H.switchToThread_def)
  apply (rule monadic_rewrite_imp)
   apply (rule monadic_rewrite_trans)
    apply (rule monadic_rewrite_bind_tail)
     apply (rule monadic_rewrite_bind)
     apply (rule tcbSchedDequeue_rewrite)
      apply (rule monadic_rewrite_refl)
     apply (wp Arch_switchToThread_obj_at_pre)+
   apply (rule monadic_rewrite_bind_tail)
    apply (rule monadic_rewrite_symb_exec)
       apply (wp+, simp)
    apply (rule monadic_rewrite_refl)
   apply (wp)
  apply (clarsimp simp: comp_def)
  done

lemma threadGet_isolatable:
  assumes v: "\<And>tsr. \<forall>tcb. f (put_tcb_state_regs_tcb tsr tcb) = f tcb"
  shows "thread_actions_isolatable idx (threadGet f t)"
  apply (clarsimp simp: threadGet_def thread_actions_isolatable_def
                        isolate_thread_actions_def split_def
                        getObject_get_assert liftM_def
                        bind_select_f_bind[symmetric]
                        select_f_returns select_f_asserts bind_assoc)
  apply (clarsimp simp: monadic_rewrite_def exec_gets
                        getSchedulerAction_def)
  apply (simp add: obj_at_partial_overwrite_If)
  apply (rule bind_apply_cong[OF refl])
  apply (clarsimp simp: exec_gets exec_modify o_def
                        ksPSpace_update_partial_id in_monad)
  apply (erule obj_atE')
  apply (clarsimp simp: projectKOs
                        partial_overwrite_def put_tcb_state_regs_def
                  cong: if_cong)
  apply (simp add: projectKO_opt_tcb v split: if_split)
  done

 lemma switchToThread_isolatable:
  "thread_actions_isolatable idx (Arch.switchToThread t)"
  apply (simp add: ARM_HYP_H.switchToThread_def
                   storeWordUser_def stateAssert_def2)
  apply (intro thread_actions_isolatable_bind[OF _ _ hoare_pre(1)]
               gets_isolatable setVMRoot_isolatable
               thread_actions_isolatable_if
               doMachineOp_isolatable
               threadGet_isolatable [OF all_tcbI]
               thread_actions_isolatable_returns
               thread_actions_isolatable_fail)
  apply (wp |
           simp add: pointerInUserData_def
                       typ_at_to_obj_at_arches
                       obj_at_partial_overwrite_id2
                       put_tcb_state_regs_tcb_def
                split: tcb_state_regs.split)+
  done

lemma monadic_rewrite_trans_dup:
  "\<lbrakk> monadic_rewrite F E P f g; monadic_rewrite F E P g h \<rbrakk>
      \<Longrightarrow> monadic_rewrite F E P f h"
  by (auto simp add: monadic_rewrite_def)


lemma setCurThread_isolatable:
  "thread_actions_isolatable idx (setCurThread t)"
  by (simp add: setCurThread_def modify_isolatable)

lemma isolate_thread_actions_tcbs_at:
  assumes f: "\<And>x. \<lbrace>tcb_at' (idx x)\<rbrace> f \<lbrace>\<lambda>rv. tcb_at' (idx x)\<rbrace>" shows
  "\<lbrace>\<lambda>s. \<forall>x. tcb_at' (idx x) s\<rbrace>
       isolate_thread_actions idx f f' f'' \<lbrace>\<lambda>p s. \<forall>x. tcb_at' (idx x) s\<rbrace>"
  apply (simp add: isolate_thread_actions_def split_def)
  apply wp
  apply clarsimp
  apply (simp add: obj_at_partial_overwrite_If use_valid[OF _ f])
  done

lemma isolate_thread_actions_rewrite_bind:
  "\<lbrakk> inj idx; monadic_rewrite False True (\<lambda>s. \<forall>x. tcb_at' (idx x) s)
                  f (isolate_thread_actions idx f' f'' f''');
     \<And>x. monadic_rewrite False True (\<lambda>s. \<forall>x. tcb_at' (idx x) s)
               (g x)
               (isolate_thread_actions idx (g' x) g'' g''');
     thread_actions_isolatable idx f'; \<And>x. thread_actions_isolatable idx (g' x);
     \<And>x. \<lbrace>tcb_at' (idx x)\<rbrace> f' \<lbrace>\<lambda>rv. tcb_at' (idx x)\<rbrace> \<rbrakk>
    \<Longrightarrow> monadic_rewrite False True (\<lambda>s. \<forall>x. tcb_at' (idx x) s)
               (f >>= g) (isolate_thread_actions idx
                                  (f' >>= g') (g'' o f'') (g''' o f'''))"
  apply (rule monadic_rewrite_imp)
   apply (rule monadic_rewrite_trans)
    apply (rule monadic_rewrite_bind, assumption+)
    apply (wp isolate_thread_actions_tcbs_at)
    apply simp
   apply (subst isolate_thread_actions_wrap_bind, assumption)
   apply (rule monadic_rewrite_in_isolate_thread_actions, assumption)
   apply (rule monadic_rewrite_transverse)
    apply (rule monadic_rewrite_bind2)
      apply (erule(1) thread_actions_isolatableD)
     apply (rule thread_actions_isolatableD, assumption+)
    apply (rule hoare_vcg_all_lift, assumption)
   apply (simp add: liftM_def id_def)
   apply (rule monadic_rewrite_refl)
  apply (simp add: obj_at_partial_overwrite_If)
  done

definition
 "copy_register_tsrs src dest r r' rf tsrs
     = tsrs (dest := TCBStateRegs (tsrState (tsrs dest))
                       ((tsrContext (tsrs dest)) (r' := rf (tsrContext (tsrs src) r))))"

lemma tcb_at_KOTCB_upd:
  "tcb_at' (idx x) s \<Longrightarrow>
   tcb_at' p (ksPSpace_update (\<lambda>ps. ps(idx x \<mapsto> KOTCB tcb)) s)
        = tcb_at' p s"
  apply (clarsimp simp: obj_at'_def projectKOs objBits_simps
                 split: if_split)
  apply (simp add: ps_clear_def)
  done

definition
 "set_register_tsrs dest r v tsrs
     = tsrs (dest := TCBStateRegs (tsrState (tsrs dest))
                       ((tsrContext (tsrs dest)) (r := v)))"


lemma set_register_isolate:
  "\<lbrakk> inj idx; idx y = dest \<rbrakk> \<Longrightarrow>
  monadic_rewrite False True
      (\<lambda>s. \<forall>x. tcb_at' (idx x) s)
           (asUser dest (setRegister r v))
           (isolate_thread_actions idx (return ())
                 (set_register_tsrs y r v) id)"
  apply (simp add: asUser_def split_def bind_assoc
                   getRegister_def setRegister_def
                   select_f_returns isolate_thread_actions_def
                   getSchedulerAction_def)
  apply (simp add: threadGet_def liftM_def getObject_get_assert
                   bind_assoc threadSet_def
                   setObject_modify_assert)
  apply (clarsimp simp: monadic_rewrite_def exec_gets
                        exec_modify tcb_at_KOTCB_upd)
  apply (clarsimp simp: simpler_modify_def
                intro!: kernel_state.fold_congs[OF refl refl])
  apply (clarsimp simp: set_register_tsrs_def o_def
                        partial_overwrite_fun_upd
                        partial_overwrite_get_tcb_state_regs)
  apply (drule_tac x=y in spec)
  apply (clarsimp simp: obj_at'_def projectKOs objBits_simps
                  cong: if_cong)
  apply (case_tac obj)
  apply (simp add: projectKO_opt_tcb put_tcb_state_regs_def
                   put_tcb_state_regs_tcb_def get_tcb_state_regs_def
             cong: if_cong)
  done

lemma copy_register_isolate:
  "\<lbrakk> inj idx; idx x = src; idx y = dest \<rbrakk> \<Longrightarrow>
  monadic_rewrite False True
      (\<lambda>s. \<forall>x. tcb_at' (idx x) s)
           (do v \<leftarrow> asUser src (getRegister r);
                   asUser dest (setRegister r' (rf v)) od)
           (isolate_thread_actions idx (return ())
                 (copy_register_tsrs x y r r' rf) id)"
  apply (simp add: asUser_def split_def bind_assoc
                   getRegister_def setRegister_def
                   select_f_returns isolate_thread_actions_def
                   getSchedulerAction_def)
  apply (simp add: threadGet_def liftM_def getObject_get_assert
                   bind_assoc threadSet_def
                   setObject_modify_assert)
  apply (clarsimp simp: monadic_rewrite_def exec_gets
                        exec_modify tcb_at_KOTCB_upd)
  apply (clarsimp simp: simpler_modify_def
                intro!: kernel_state.fold_congs[OF refl refl])
  apply (clarsimp simp: copy_register_tsrs_def o_def
                        partial_overwrite_fun_upd
                        partial_overwrite_get_tcb_state_regs)
  apply (frule_tac x=x in spec, drule_tac x=y in spec)
  apply (clarsimp simp: obj_at'_def projectKOs objBits_simps
                  cong: if_cong)
  apply (case_tac obj, case_tac obja)
  apply (simp add: projectKO_opt_tcb put_tcb_state_regs_def
                   put_tcb_state_regs_tcb_def get_tcb_state_regs_def
             cong: if_cong)
  apply (auto simp: fun_eq_iff split: if_split)
  done

lemmas monadic_rewrite_bind_alt
    = monadic_rewrite_trans[OF monadic_rewrite_bind_tail monadic_rewrite_bind_head, rotated -1]


lemma monadic_rewrite_isolate_final2:
  assumes  mr: "monadic_rewrite F E Q f g"
      and eqs: "\<And>s tsrs. \<lbrakk> P s; tsrs = get_tcb_state_regs o ksPSpace s o idx \<rbrakk>
                      \<Longrightarrow> f' tsrs = g' tsrs"
               "\<And>s. P s \<Longrightarrow> f'' (ksSchedulerAction s) = g'' (ksSchedulerAction s)"
               "\<And>s tsrs sa. R s \<Longrightarrow>
                           Q ((ksPSpace_update (partial_overwrite idx tsrs)
                                      s) (| ksSchedulerAction := sa |))"
  shows
  "monadic_rewrite F E (P and R)
         (isolate_thread_actions idx f f' f'')
         (isolate_thread_actions idx g g' g'')"
  apply (simp add: isolate_thread_actions_def split_def)
  apply (rule monadic_rewrite_imp)
   apply (rule monadic_rewrite_bind_tail)+
      apply (rule_tac P="\<lambda> s'. Q s" in monadic_rewrite_bind)
        apply (insert mr)[1]
        apply (simp add: monadic_rewrite_def select_f_def)
        apply auto[1]
       apply (rule_tac P="P and (\<lambda>s. tcbs = get_tcb_state_regs o ksPSpace s o idx
                                             \<and> sa = ksSchedulerAction s)"
                    in monadic_rewrite_refl3)
       apply (clarsimp simp: exec_modify eqs return_def)
      apply wp+
  apply (clarsimp simp: o_def eqs)
  done

lemmas monadic_rewrite_isolate_final
    = monadic_rewrite_isolate_final2[where R=\<top>, OF monadic_rewrite_refl2, simplified]

lemma copy_registers_isolate_general:
  "\<lbrakk> inj idx; idx x = t; idx y = t' \<rbrakk> \<Longrightarrow>
   monadic_rewrite False True
      (\<lambda>s. \<forall>x. tcb_at' (idx x) s)
           (mapM_x (\<lambda>r. do v \<leftarrow> asUser t (getRegister (f r));
                           asUser t' (setRegister (f' r) (rf r v))
                        od)
             regs)
           (isolate_thread_actions idx
               (return ()) (foldr (\<lambda>r. copy_register_tsrs x y (f r) (f' r) (rf r)) (rev regs)) id)"
  apply (induct regs)
   apply (simp add: mapM_x_Nil)
   apply (clarsimp simp: monadic_rewrite_def liftM_def bind_assoc
                         isolate_thread_actions_def
                         split_def exec_gets getSchedulerAction_def
                         select_f_returns o_def ksPSpace_update_partial_id)
   apply (simp add: return_def simpler_modify_def)
  apply (simp add: mapM_x_Cons)
  apply (rule monadic_rewrite_imp)
   apply (rule monadic_rewrite_trans)
    apply (rule isolate_thread_actions_rewrite_bind, assumption)
        apply (rule copy_register_isolate, assumption+)
      apply (rule thread_actions_isolatable_returns)+
    apply wp
   apply (rule monadic_rewrite_isolate_final[where P=\<top>], simp+)
  done

lemmas copy_registers_isolate = copy_registers_isolate_general[where f="\<lambda>x. x" and f'="\<lambda>x. x" and rf="\<lambda>_ x. x"]

lemma setSchedulerAction_isolate:
  "inj idx \<Longrightarrow>
   monadic_rewrite False True (\<lambda>s. \<forall>x. tcb_at' (idx x) s)
        (setSchedulerAction sa)
        (isolate_thread_actions idx (return ()) id (\<lambda>_. sa))"
  apply (clarsimp simp: monadic_rewrite_def liftM_def bind_assoc
                        isolate_thread_actions_def select_f_returns
                        exec_gets getSchedulerAction_def o_def
                        ksPSpace_update_partial_id setSchedulerAction_def)
  apply (simp add: simpler_modify_def)
  done

lemma updateMDB_isolatable:
  "thread_actions_isolatable idx (updateMDB slot f)"
  apply (simp add: updateMDB_def thread_actions_isolatable_return
            split: if_split)
  apply (intro impI thread_actions_isolatable_bind[OF _ _ hoare_pre(1)]
               getCTE_isolatable setCTE_isolatable,
           (wp | simp)+)
  done

lemma clearUntypedFreeIndex_isolatable:
  "thread_actions_isolatable idx (clearUntypedFreeIndex slot)"
  apply (simp add: clearUntypedFreeIndex_def getSlotCap_def)
  apply (rule thread_actions_isolatable_bind)
    apply (rule getCTE_isolatable)
   apply (simp split: capability.split, safe intro!: thread_actions_isolatable_return)
   apply (simp add: updateTrackedFreeIndex_def getSlotCap_def)
   apply (intro thread_actions_isolatable_bind getCTE_isolatable
                modify_isolatable)
      apply (wp | simp)+
  done

lemma emptySlot_isolatable:
  "thread_actions_isolatable idx (emptySlot slot None)"
  apply (simp add: emptySlot_def updateCap_def case_Null_If
             cong: if_cong)
  apply (intro thread_actions_isolatable_bind[OF _ _ hoare_pre(1)]
               clearUntypedFreeIndex_isolatable
               thread_actions_isolatable_if
               getCTE_isolatable setCTE_isolatable
               thread_actions_isolatable_return
               updateMDB_isolatable,
           (wp | simp)+)
  done

lemmas fastpath_isolatables
    = setEndpoint_isolatable getCTE_isolatable
      assert_isolatable cteInsert_isolatable
      switchToThread_isolatable setCurThread_isolatable
      emptySlot_isolatable updateMDB_isolatable
      thread_actions_isolatable_returns

lemmas fastpath_isolate_rewrites
    = isolate_thread_actions_threadSet_tcbState isolate_thread_actions_asUser
      copy_registers_isolate setSchedulerAction_isolate
      fastpath_isolatables[THEN thread_actions_isolatableD]

lemma lookupIPCBuffer_isolatable:
  "thread_actions_isolatable idx (lookupIPCBuffer w t)"
  apply (simp add: lookupIPCBuffer_def)
  apply (rule thread_actions_isolatable_bind)
  apply (clarsimp simp: put_tcb_state_regs_tcb_def threadGet_isolatable
                        getThreadBufferSlot_def locateSlot_conv getSlotCap_def
                  split: tcb_state_regs.split)+
   apply (rule thread_actions_isolatable_bind)
    apply (clarsimp simp: thread_actions_isolatable_return
                          getCTE_isolatable
                          assert_isolatable
                   split: capability.split arch_capability.split bool.split)+
    apply (rule thread_actions_isolatable_if)
    apply (rule thread_actions_isolatable_bind)
      apply (simp add: assert_isolatable thread_actions_isolatable_return | wp)+
  done

end

end
