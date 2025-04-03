(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory IsolatedThreadAction
imports ArchMove_C
begin

context begin interpretation Arch .

datatype tcb_state_regs =
  TCBStateRegs (tsrState : thread_state) (tsrContext : "MachineTypes.register \<Rightarrow> machine_word")

definition
  get_tcb_state_regs :: "kernel_object option \<Rightarrow> tcb_state_regs"
where
 "get_tcb_state_regs oko \<equiv> case oko of
    Some (KOTCB tcb) \<Rightarrow> TCBStateRegs (tcbState tcb) ((user_regs o atcbContextGet o tcbArch) tcb)"

definition
  put_tcb_state_regs_tcb :: "tcb_state_regs \<Rightarrow> tcb \<Rightarrow> tcb"
where
 "put_tcb_state_regs_tcb tsr tcb \<equiv> case tsr of
     TCBStateRegs st regs \<Rightarrow>
        tcb \<lparr> tcbState := st,
              tcbArch := atcbContextSet (UserContext regs)
                         (tcbArch tcb) \<rparr>"

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
  isolate_thread_actions :: "('x \<Rightarrow> machine_word) \<Rightarrow> 'a kernel
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

lemma UserContextGet[simp]:
  "UserContext (user_regs (atcbContextGet t)) = atcbContextGet t"
  by (cases t, simp add: atcbContextGet_def)

lemma put_tcb_state_regs_twice[simp]:
  "put_tcb_state_regs tsr (put_tcb_state_regs tsr' tcb)
    = put_tcb_state_regs tsr tcb"
  apply (simp add: put_tcb_state_regs_def put_tcb_state_regs_tcb_def
                   makeObject_tcb newArchTCB_def
            split: tcb_state_regs.split option.split
                   Structures_H.kernel_object.split)
  apply (intro all_tcbI)
  by (simp add: arch_tcb.expand)

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

end

context begin interpretation Arch . (*FIXME: arch-split*)

lemma setObject_modify:
  fixes v :: "'a :: pspace_storable" shows
  "\<lbrakk> obj_at' (P :: 'a \<Rightarrow> bool) p s; updateObject v = updateObject_default v;
         (1 :: machine_word) < 2 ^ objBits v; \<And>ko. P ko \<Longrightarrow> objBits ko = objBits v \<rbrakk>
    \<Longrightarrow> setObject p v s
      = modify (ksPSpace_update (\<lambda>ps. ps (p \<mapsto> injectKO v))) s"
  apply (clarsimp simp: setObject_def split_def exec_gets obj_at'_def lookupAround2_known1
                        assert_opt_def updateObject_default_def bind_assoc)
  apply (simp add: projectKO_def alignCheck_assert)
  apply (simp add: project_inject objBits_def)
  apply (clarsimp simp only: koTypeOf_injectKO)
  apply (frule (1) in_magnitude_check[where s'=s])
   apply blast
  apply (simp add: magnitudeCheck_assert in_monad bind_def gets_def oassert_opt_def
                   get_def return_def)
  apply (simp add: simpler_modify_def)
  done

lemma getObject_return:
  fixes v :: "'a :: pspace_storable" shows
  "\<lbrakk> \<And>q n ko. loadObject p q n ko =
                (loadObject_default p q n ko :: 'a :: pspace_storable kernel_r);
     ko_at' v p s; (1 :: machine_word) < 2 ^ objBits v \<rbrakk> \<Longrightarrow>
   getObject p s = return v s"
  apply (clarsimp simp: getObject_def readObject_def omonad_defs split_def gets_the_def gets_def
                        get_def bind_def return_def assert_opt_def fail_def obj_at'_def
                        lookupAround2_known1 loadObject_default_def in_omonad
                 split: option.splits)
  by (fastforce simp add: project_inject objBits_def)

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

context begin interpretation Arch . (*FIXME: arch-split*)

lemma get_tcb_state_regs_ko_at':
  "ko_at' ko p s \<Longrightarrow> get_tcb_state_regs (ksPSpace s p)
       = TCBStateRegs (tcbState ko) ((user_regs o atcbContextGet o tcbArch) ko)"
  by (clarsimp simp: obj_at'_def get_tcb_state_regs_def)

lemma put_tcb_state_regs_ko_at':
  "ko_at' ko p s \<Longrightarrow> put_tcb_state_regs tsr (ksPSpace s p)
       = Some (KOTCB (ko \<lparr> tcbState := tsrState tsr
                         , tcbArch := atcbContextSet (UserContext (tsrContext tsr)) (tcbArch ko)\<rparr>))"
  by (clarsimp simp: obj_at'_def put_tcb_state_regs_def
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
  apply (clarsimp simp: obj_at'_def put_tcb_state_regs_def
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
  "\<lbrakk> idx t' = t; inj idx; f = (\<lambda>s. ({(v, modify_registers g s)}, False)) \<rbrakk> \<Longrightarrow>
   monadic_rewrite False True (\<lambda>s. \<forall>x. tcb_at' (idx x) s)
      (asUser t f)
      (isolate_thread_actions idx (return v)
           (\<lambda>tsrs. (tsrs (t' := TCBStateRegs (tsrState (tsrs t'))
                                    (g (tsrContext (tsrs t'))))))
            id)"
  apply (simp add: asUser_def liftM_def isolate_thread_actions_def split_def
                   select_f_returns bind_assoc select_f_singleton_return
                   threadGet_getObject threadSet_def)
  apply (clarsimp simp: monadic_rewrite_def)
  apply (frule_tac x=t' in spec)
  apply (drule obj_at_ko_at', clarsimp)
  apply (simp add: exec_gets getSchedulerAction_def exec_modify objBits_defs
                   getObject_return_tcb setObject_modify_tcb o_def
             cong: bind_apply_cong)+
  apply (simp add: partial_overwrite_fun_upd return_def get_tcb_state_regs_ko_at')
  apply (rule kernel_state.fold_congs[OF refl refl])
  apply (clarsimp simp: partial_overwrite_get_tcb_state_regs
                        put_tcb_state_regs_ko_at')
  apply (case_tac ko, simp)
  apply (rename_tac uc)
  apply (case_tac uc, simp add: modify_registers_def atcbContextGet_def atcbContextSet_def)
  done

lemma getRegister_simple:
  "getRegister r = (\<lambda>con. ({(user_regs con r, con)}, False))"
  by (simp add: getRegister_def simpler_gets_def)

lemma mapM_getRegister_simple:
  "mapM getRegister rs = (\<lambda>con. ({(map (user_regs con) rs, con)}, False))"
  apply (induct rs)
   apply (simp add: mapM_Nil return_def)
  apply (simp add: mapM_Cons getRegister_def simpler_gets_def
                   bind_def return_def)
  done

lemma setRegister_simple:
  "setRegister r v = (\<lambda>con. ({((), UserContext ((user_regs con)(r := v)))}, False))"
  by (simp add: setRegister_def simpler_modify_def)

lemma zipWithM_setRegister_simple:
  "zipWithM_x setRegister rs vs
      = (\<lambda>con. ({((), foldl (\<lambda>con (r, v). UserContext ((user_regs con)(r := v))) con (zip rs vs))}, False))"
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
  supply if_split[split del]
  apply (rule ext)
  apply (frule dom_partial_overwrite[where tsrs=tsrs])
  apply (simp add: map_to_ctes_def partial_overwrite_def
                   Let_def)
  apply (case_tac "x \<in> range idx")
   apply (clarsimp simp: put_tcb_state_regs_def)
   apply (drule_tac x=xa in spec)
   apply (clarsimp simp: obj_at'_def projectKOs objBits_simps'
                   cong: if_cong)
   apply (simp add: put_tcb_state_regs_def put_tcb_state_regs_tcb_def
                    objBits_simps'
              cong: if_cong option.case_cong)
   apply (case_tac obj, simp split: tcb_state_regs.split if_split)
  apply simp
  apply (rule if_cong[OF refl])
   apply simp
  apply (case_tac "x && ~~ mask (objBitsKO (KOTCB undefined)) \<in> range idx")
   apply (clarsimp simp: put_tcb_state_regs_def)
   apply (drule_tac x=xa in spec)
   apply (clarsimp simp: obj_at'_def projectKOs objBits_simps'
                   cong: if_cong)
   apply (simp add: put_tcb_state_regs_def put_tcb_state_regs_tcb_def
                    objBits_simps'
              cong: if_cong option.case_cong)
   apply (case_tac obj, simp split: tcb_state_regs.split if_split)
   apply (intro impI allI)
   apply (subgoal_tac "x - idx xa = x && mask tcbBlockSizeBits")
    apply (clarsimp simp: tcb_cte_cases_def objBits_defs split: if_split)
   apply (drule_tac t = "idx xa" in sym)
    apply (simp add: objBits_defs)
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
  apply (subgoal_tac "cte_wp_at' ((=) x2) p x")
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
            split: if_split)
  apply clarsimp
  apply (drule_tac x=x in spec)
  apply (clarsimp simp: put_tcb_state_regs_def objBits_simps
                        project_inject)
  done

lemma getObject_get_assert:
  assumes deflt: "\<And>q n ko. loadObject p q n ko =
                             (loadObject_default p q n ko :: 'a :: pspace_storable kernel_r)"
  shows
  "(getObject p :: ('a :: pspace_storable) kernel)
   = do v \<leftarrow> gets (obj_at' (\<lambda>x :: 'a. True) p);
        assert v;
        gets (the o projectKO_opt o the o swp fun_app p o ksPSpace)
     od"
  apply (rule ext)
  apply (rename_tac x)
  apply (case_tac "ksPSpace x p")
   apply (clarsimp simp: obj_at'_def assert_opt_def assert_def split_def getObject_def2 deflt
                         loadObject_default_def gets_the_def  gets_def get_def bind_def return_def
                         fail_def in_omonad
                  split: option.split if_split option.splits)
  apply (clarsimp simp: getObject_def2 deflt loadObject_default_def projectKO_def)
  apply (clarsimp simp: omonad_defs split_def gets_the_def gets_def
                        get_def bind_def return_def assert_opt_def obj_at'_def
                        lookupAround2_known1 assert_def
                 split: option.splits)
  apply (fastforce elim!: ps_clear_lookupAround2
                    simp: fail_def project_inject objBits_def)
  done


lemma getObject_isolatable:
  "\<lbrakk> \<And>q n ko. loadObject p q n ko =
                             (loadObject_default p q n ko :: 'a :: pspace_storable kernel_r);
      \<And>tcb. projectKO_opt (KOTCB tcb) = (None :: 'a option) \<rbrakk> \<Longrightarrow>
   thread_actions_isolatable idx (getObject p :: 'a :: pspace_storable kernel)"
  apply (clarsimp simp: thread_actions_isolatable_def)
  apply (simp add: getObject_get_assert split_def
                   isolate_thread_actions_def bind_select_f_bind[symmetric]
                   bind_assoc select_f_asserts select_f_returns)
  apply (clarsimp simp: monadic_rewrite_def exec_gets getSchedulerAction_def)
  apply (case_tac "p \<in> range idx")
   apply clarsimp
   apply (drule_tac x=x in spec)
   apply (clarsimp simp: obj_at'_def partial_overwrite_def put_tcb_state_regs_def)
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
  apply (simp add: simpler_modify_def)
  apply (subst swap)
   apply (simp add: obj_at_partial_overwrite_If)
  apply (simp add: ksPSpace_update_partial_id o_def)
  done

lemma kernelExitAssertions_isolatable:
  "thread_actions_isolatable idx (stateAssert kernelExitAssertions [])"
  unfolding stateAssert_def kernelExitAssertions_def
  apply (clarsimp simp: thread_actions_isolatable_def get_def assert_def bind_def)
  apply (simp add: isolate_thread_actions_def select_f_returns liftM_def bind_assoc)
  apply (clarsimp simp: monadic_rewrite_def exec_gets getSchedulerAction_def)
  apply (fastforce simp: cur_tcb'_def simpler_gets_def return_def fail_def modify_def get_def
                         put_def ksPSpace_update_partial_id o_def bind_def select_f_def
                         obj_at_partial_overwrite_If)
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
  apply (rule monadic_rewrite_guard_imp)
   apply (rule monadic_rewrite_trans)
    apply (erule monadic_rewrite_bind_l, assumption)
    apply (rule hoare_vcg_all_lift, assumption)
   apply (subst isolate_thread_actions_wrap_bind, simp)
   apply simp
   apply (rule monadic_rewrite_in_isolate_thread_actions, assumption)
   apply (rule monadic_rewrite_transverse)
    apply (erule monadic_rewrite_bind_l, assumption)
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
  apply (rule monadic_rewrite_guard_imp, rule monadic_rewrite_transverse)
    apply (rule monadic_rewrite_drop_modify monadic_rewrite_bind_tail)+
       apply wp+
   apply (simp add: gets_bind_ign getSchedulerAction_def)
   apply (rule monadic_rewrite_refl)
  apply (simp add: ksPSpace_update_partial_id o_def)
  done

lemma doMachineOp_isolatable:
  "thread_actions_isolatable idx (doMachineOp m)"
  apply (simp add: doMachineOp_def split_def)
  apply (intro thread_actions_isolatable_bind[OF _ _ hoare_weaken_pre]
               gets_isolatable thread_actions_isolatable_returns
               modify_isolatable select_f_isolatable)
  apply (simp | wp)+
  done

lemma page_table_at_partial_overwrite:
  "\<forall>x. tcb_at' (idx x) s \<Longrightarrow>
   page_table_at' p (ksPSpace_update (partial_overwrite idx f) s)
      = page_table_at' p s"
  by (simp add: page_table_at'_def typ_at_to_obj_at_arches
                obj_at_partial_overwrite_id2)

lemma findVSpaceForASID_isolatable:
  "thread_actions_isolatable idx (findVSpaceForASID asid)"
  supply if_split[split del]
  apply (simp add: findVSpaceForASID_def liftE_bindE liftME_def bindE_assoc
                   case_option_If2 assertE_def liftE_def checkPTAt_def
                   stateAssert_def2
             cong: if_cong)
  apply (intro thread_actions_isolatable_bind[OF _ _ hoare_weaken_pre]
               thread_actions_isolatable_bindE[OF _ _ hoare_weaken_pre]
               thread_actions_isolatable_if thread_actions_isolatable_returns
               thread_actions_isolatable_fail
               gets_isolatable getObject_isolatable)
    apply (simp add: projectKO_opt_asidpool page_table_at_partial_overwrite
           | wp getASID_wp)+
  done

lemma modifyArchState_isolatable:
  "thread_actions_isolatable idx (modifyArchState f)"
  by (clarsimp simp: modifyArchState_def modify_isolatable)

lemma modify_not_fail[simp]:
  "modify f s \<noteq> fail s"
  by (simp add: simpler_modify_def fail_def)

lemma setObject_assert_modify:
  "\<lbrakk> updateObject v = updateObject_default v; (1::machine_word) < 2 ^ objBits v;
     \<And>ko v'. projectKO_opt ko = Some (v'::'a) \<Longrightarrow> objBitsKO ko = objBits v \<rbrakk> \<Longrightarrow>
   setObject p (v::'a::pspace_storable) s = (do
     assert (obj_at' (\<lambda>_::'a. True) p s);
     modify (ksPSpace_update (\<lambda>ps. ps(p \<mapsto> injectKOS v)))
   od) s"
  apply (clarsimp simp: assert_def)
  apply (intro conjI impI)
   apply (subst setObject_modify; assumption?)
    apply (fastforce dest: in_magnitude_check[where s'=s]
                     simp: obj_at_simps project_inject)
   apply (fastforce simp: obj_at_simps)
  apply (clarsimp simp: setObject_def split_def exec_gets updateObject_default_def assert_opt_def
                        assert_def alignCheck_assert
                 split: option.splits)
  apply (clarsimp simp: magnitudeCheck_assert2 assert_def gets_the_def gets_def
                        get_def bind_def return_def assert_opt_def fail_def obj_at'_def
                 split: option.splits)
  done

lemma thread_actions_isolatable_mapM_x:
  "\<lbrakk> \<And>x. thread_actions_isolatable idx (f x);
     \<And>x t. f x \<lbrace>tcb_at' t\<rbrace> \<rbrakk> \<Longrightarrow> thread_actions_isolatable idx (mapM_x f xs)"
  apply (induct xs; clarsimp simp: mapM_x_Nil mapM_x_Cons thread_actions_isolatable_returns)
  apply (rule thread_actions_isolatable_bind[OF _ _ hoare_weaken_pre]; clarsimp?)
   apply assumption+
  done

lemma liftM_getObject_return_tcb:
  "ko_at' v p s \<Longrightarrow> liftM f (getObject p) s = return (f (v::tcb)) s"
  by (simp add: liftM_def bind_def getObject_return_tcb return_def objBits_defs)

lemma cap_case_isPageTableCap:
  "(case cap of ArchObjectCap (PageTableCap pm (Some asid)) \<Rightarrow> fn pm asid | _ => g)
    = (if (if isArchObjectCap cap
           then if isPageTableCap (capCap cap) then capPTMappedAddress (capCap cap) \<noteq> None else False
           else False)
       then fn (capPTBasePtr (capCap cap)) (the (capPTMappedAddress (capCap cap))) else g)"
  apply (cases cap; simp add: isArchObjectCap_def)
  apply (rename_tac arch_capability)
  apply (case_tac arch_capability, simp_all add: isPageTableCap_def)
  apply (rename_tac option)
  apply (case_tac option; simp)
  done

lemma setVMRoot_isolatable:
  "thread_actions_isolatable idx (setVMRoot t)"
  supply if_split[split del]
  apply (simp add: setVMRoot_def getThreadVSpaceRoot_def
                   locateSlot_conv getSlotCap_def
                   if_bool_simps cap_case_isPageTableCap
                   whenE_def liftE_def
                   stateAssert_def2 assert_def
             cong: if_cong)
  apply (intro thread_actions_isolatable_bind[OF _ _ hoare_weaken_pre]
               thread_actions_isolatable_bindE[OF _ _ hoare_weaken_pre]
               thread_actions_isolatable_catch[OF _ _ hoare_weaken_pre]
               thread_actions_isolatable_if thread_actions_isolatable_returns
               thread_actions_isolatable_fail
               gets_isolatable getCTE_isolatable
               findVSpaceForASID_isolatable doMachineOp_isolatable
         | clarsimp simp add: projectKO_opt_asidpool
         | wp getASID_wp typ_at_lifts)+
  done

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
  supply empty_fail_getReceiveSlots[wp] (* FIXME *)
  apply (rule monadic_rewrite_gen_asm)
  apply (simp add: transferCaps_simple)
  apply (monadic_rewrite_symb_exec_l_drop, rule monadic_rewrite_refl)
  apply simp
  done

lemma lookupExtraCaps_simple_rewrite:
  "msgExtraCaps mi = 0 \<Longrightarrow>
      (lookupExtraCaps thread rcvBuf mi = returnOk [])"
  by (cases mi, simp add: lookupExtraCaps_def getExtraCPtrs_def
                          liftE_bindE upto_enum_step_def mapM_Nil mapME_Nil
                   split: option.split)

lemma lookupIPC_inv: "\<lbrace>P\<rbrace> lookupIPCBuffer f t \<lbrace>\<lambda>rv. P\<rbrace>"
  by wp

(* FIXME move *)
lemmas empty_fail_user_getreg[intro!, wp, simp] = empty_fail_asUser[OF empty_fail_getRegister]

lemma copyMRs_simple:
  "msglen \<le> of_nat (length msgRegisters) \<longrightarrow>
    copyMRs sender sbuf receiver rbuf msglen
        = forM_x (take (unat msglen) msgRegisters)
             (\<lambda>r. do v \<leftarrow> asUser sender (getRegister r);
                    asUser receiver (setRegister r v) od)
           >>= (\<lambda>rv. return msglen)"
  apply (clarsimp simp: copyMRs_def mapM_discarded)
  apply (rule bind_cong[OF refl])
  apply (simp add: length_msgRegisters min_def
                   word_le_nat_alt
            split: option.split)
  apply (simp add: upto_enum_def mapM_Nil)
  done

lemma doIPCTransfer_simple_rewrite:
  "monadic_rewrite True True
   ((\<lambda>_. msgExtraCaps (messageInfoFromWord msgInfo) = 0
               \<and> msgLength (messageInfoFromWord msgInfo)
                      \<le> of_nat (length msgRegisters))
      and obj_at' (\<lambda>tcb. tcbFault tcb = None
               \<and> (user_regs o atcbContextGet o tcbArch) tcb msgInfoRegister = msgInfo) sender)
   (doIPCTransfer sender ep badge grant rcvr)
   (do rv \<leftarrow> mapM_x (\<lambda>r. do v \<leftarrow> asUser sender (getRegister r);
                             asUser rcvr (setRegister r v)
                          od)
               (take (unat (msgLength (messageInfoFromWord msgInfo))) msgRegisters);
         y \<leftarrow> setMessageInfo rcvr ((messageInfoFromWord msgInfo) \<lparr>msgCapsUnwrapped := 0\<rparr>);
         asUser rcvr (setRegister badgeRegister badge)
      od)"
  supply if_cong[cong]
  apply (rule monadic_rewrite_gen_asm)
  apply (simp add: doIPCTransfer_def bind_assoc doNormalTransfer_def
                   getMessageInfo_def
             cong: option.case_cong)
  apply (rule monadic_rewrite_guard_imp)
   apply (rule monadic_rewrite_trans)
    apply (rule monadic_rewrite_bind_tail)
      apply (monadic_rewrite_symb_exec_l_known None, simp)
      apply (rule monadic_rewrite_bind_tail)
       apply (monadic_rewrite_symb_exec_l_known msgInfo)
          apply (simp add: lookupExtraCaps_simple_rewrite returnOk_catch_bind)
          apply (rule monadic_rewrite_bind)
            apply (rule monadic_rewrite_from_simple, rule copyMRs_simple)
           apply (rule monadic_rewrite_bind_head)
           apply (rule transferCaps_simple_rewrite)
          apply (wp threadGet_const user_getreg_rv asUser_inv)+
   apply (simp add: bind_assoc)
   apply (rule monadic_rewrite_symb_exec_l_drop[OF _ lookupIPC_inv empty_fail_lookupIPCBuffer]
               monadic_rewrite_symb_exec_l_drop[OF _ threadGet_inv empty_fail_threadGet]
               monadic_rewrite_symb_exec_l_drop[OF _ user_getreg_inv' empty_fail_user_getreg]
               monadic_rewrite_bind_head monadic_rewrite_bind_tail)+
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
  apply (rule monadic_rewrite_guard_imp, rule monadic_rewrite_modify_noop)
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

(* FIXME move *)
lemma empty_fail_isRunnable[intro!, wp, simp]:
  "empty_fail (isRunnable t)"
  by (simp add: isRunnable_def isStopped_def empty_fail_cond)

lemma oblivious_doMachineOp[simp]:
  "\<lbrakk> \<forall>s. ksMachineState (f s) = ksMachineState s;
     \<forall>g s. ksMachineState_update g (f s) = f (ksMachineState_update g s) \<rbrakk>
      \<Longrightarrow> oblivious f (doMachineOp oper)"
  apply (simp add: doMachineOp_def split_def)
  apply (intro oblivious_bind, simp_all)
  done

lemmas oblivious_getObject_ksPSpace_asidpool[simp]
    = oblivious_getObject_ksPSpace_default[OF _ loadObject_asidpool]

lemma oblivious_modifyArchState_schact[simp]:
  "oblivious (ksSchedulerAction_update f) (modifyArchState f')"
  by (simp add: oblivious_def modifyArchState_def simpler_modify_def)

lemma oblivious_setVMRoot_schact:
  "oblivious (ksSchedulerAction_update f) (setVMRoot t)"
  apply (simp add: setVMRoot_def getThreadVSpaceRoot_def locateSlot_conv
                   getSlotCap_def getCTE_def)
  by (safe intro!: oblivious_bind oblivious_bindE oblivious_catch oblivious_mapM_x
             | simp_all add: liftE_def
                             findVSpaceForASID_def liftME_def checkPTAt_def
                      split: if_split capability.split arch_capability.split option.split)+

lemma oblivious_tcbQueueRemove:
  "oblivious (ksSchedulerAction_update f) (tcbQueueRemove queue t)"
  apply (simp add: tcbQueueRemove_def getThreadVSpaceRoot_def locateSlot_conv
                   getSlotCap_def getCTE_def)
  by (safe intro!: oblivious_bind | simp_all add: threadSet_def)+

lemma ready_qs_runnable_ksSchedulerAction_update[simp]:
  "ready_qs_runnable (ksSchedulerAction_update f s) = ready_qs_runnable s"
  by (simp add: ready_qs_runnable_def)

lemma ready_or_release'_ksSchedulerAction_update[simp]:
  "ready_or_release' (ksSchedulerAction_update f s) = ready_or_release' s"
  by (simp add: ready_or_release'_def)

lemma oblivious_switchToThread_schact:
  "oblivious (ksSchedulerAction_update f) (ThreadDecls_H.switchToThread t)"
  apply (simp add: Thread_H.switchToThread_def switchToThread_def bind_assoc
                   getCurThread_def setCurThread_def liftM_def
                   threadSet_def tcbSchedEnqueue_def unless_when asUser_def
                   getQueue_def setQueue_def storeWordUser_def setRegister_def
                   pointerInUserData_def isRunnable_def readRunnable_def threadGet_def[symmetric]
                   isStopped_def threadGet_getObject
                   getThreadState_def tcbSchedDequeue_def bitmap_fun_defs ready_qs_runnable_def
                   ready_or_release'_asrt_def ksReadyQueues_asrt_def)
  by (safe intro!: oblivious_bind oblivious_tcbQueueRemove
      | simp_all add: oblivious_setVMRoot_schact idleThreadNotQueued_def)+

(* FIXME move *)
crunch getCurThread
  for (empty_fail) empty_fail[iff]

end

lemma setBoundNotification_tcbPriority_obj_at'[wp]:
  "setBoundNotification ntfnPtr tptr \<lbrace>obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t'\<rbrace>"
  unfolding setBoundNotification_def
  apply (wpsimp wp: threadSet_wp)
  apply (clarsimp simp: obj_at'_def objBits_simps ps_clear_upd)
  done

lemma tcbQueuePrepend_tcbPriority_obj_at'[wp]:
  "tcbQueuePrepend queue tptr \<lbrace>obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t'\<rbrace>"
  unfolding tcbQueuePrepend_def
  apply (wpsimp wp: threadSet_wp)
  by (auto simp: obj_at'_def objBits_simps ps_clear_def split: if_splits)

lemma tcbSchedDequeue_tcbPriority[wp]:
  "tcbSchedDequeue t \<lbrace>obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t'\<rbrace>"
  unfolding tcbSchedDequeue_def tcbQueueRemove_def
  by (wpsimp wp: hoare_when_weak_wp hoare_drop_imps)

lemma tcbSchedEnqueue_tcbPriority_obj_at'[wp]:
  "tcbSchedEnqueue tcbPtr \<lbrace>obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t'\<rbrace>"
  unfolding tcbSchedEnqueue_def setQueue_def
  by wpsimp

crunch scheduleTCB
  for tcbPriority_obj_at'[wp]: "obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t'"

lemma setThreadState_tcbPriority_obj_at'[wp]:
  "setThreadState ts tptr \<lbrace>obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t'\<rbrace>"
  unfolding setThreadState_def
  apply (wpsimp wp: threadSet_wp)
  apply (fastforce simp: obj_at'_def objBits_simps ps_clear_def)
  done

(* FIXME RT: move following lemmas about tcbPriority to Refine or possibly DInvs (see VER-1299) *)
crunch unbindMaybeNotification, blockedCancelIPC, replyRemoveTCB, cancelSignal
  for tcbPriority_obj_at'[wp]: "obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t'"
  (wp: hoare_vcg_all_lift crunch_wps simp: crunch_simps)

lemma cancelIPC_tcbPriority[wp]:
  "cancelIPC tptr \<lbrace>obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t\<rbrace>"
  apply (simp add: cancelIPC_def unless_def)
  by (wpsimp wp: threadSet_obj_at' gts_wp' hoare_drop_imps)

lemma tcbSchedContext_update_tcbPriority[wp]:
  "threadSet (tcbSchedContext_update f) t' \<lbrace>obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t\<rbrace>"
  by (wpsimp wp: threadSet_obj_at' gts_wp' hoare_drop_imps)

lemma tcbReleaseRemove_tcbPriority[wp]:
  "tcbReleaseRemove tcbPtr \<lbrace>obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t\<rbrace>"
  apply (clarsimp simp: tcbReleaseRemove_def tcbQueueRemove_def)
  by (wpsimp wp: threadSet_obj_at' gts_wp' hoare_drop_imps)

lemma schedContextDonate_tcbPriority[wp]:
  "schedContextDonate scPtr tcbPtr \<lbrace>obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t\<rbrace>"
  apply (simp add: schedContextDonate_def updateSchedContext_def)
  by (wpsimp wp: hoare_drop_imps)

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

context begin interpretation Arch . (*FIXME: arch-split*)

lemma setObject_modify_assert:
  "\<lbrakk>updateObject v = updateObject_default v\<rbrakk>
   \<Longrightarrow> setObject p v = do f \<leftarrow> gets (obj_at' (\<lambda>v'. v = v' \<or> objBits v' = objBits v) p);
                          assert f; modify (ksPSpace_update (\<lambda>ps. ps(p \<mapsto> injectKO v)))
                       od"
  apply (simp add: setObject_def split_def updateObject_default_def
                   bind_assoc projectKO_def alignCheck_assert)
  apply (rule ext, simp add: exec_gets)
  apply (case_tac "obj_at' (\<lambda>v'. v = v' \<or> objBits v' = objBits v) p x")
   apply (clarsimp simp: obj_at'_def lookupAround2_known1
                         assert_opt_def)
   apply (clarsimp simp: project_inject)
   apply (simp only: objBits_def  koTypeOf_injectKO)
   apply (simp add: magnitudeCheck_assert2 simpler_modify_def)
   apply (clarsimp simp: assert_def magnitudeCheck_assert2)
   apply (clarsimp simp: omonad_defs bind_def return_def)
   apply fastforce
  apply (clarsimp simp: assert_opt_def assert_def magnitudeCheck_assert2
                 split: option.split)
  by (fastforce simp: omonad_defs gets_the_def get_def bind_def return_def assert_opt_def fail_def
                      obj_at_simps project_inject
               split: option.splits)

lemma setEndpoint_isolatable:
  "thread_actions_isolatable idx (setEndpoint p e)"
  supply if_split[split del]
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
  apply (intro thread_actions_isolatable_bind[OF _ _ hoare_weaken_pre]
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

(* FIXME x64: tcb bits *)
lemma setCTE_assert_modify:
  "setCTE p v = do c \<leftarrow> gets (real_cte_at' p);
                   t \<leftarrow> gets (tcb_at' (p && ~~ mask tcbBlockSizeBits)
                                 and K ((p && mask tcbBlockSizeBits) \<in> dom tcb_cte_cases));
                   if c then modify (ksPSpace_update (\<lambda>ps. ps(p \<mapsto> KOCTE v)))
                   else if t then
                     modify (ksPSpace_update
                               (\<lambda>ps. ps (p && ~~ mask tcbBlockSizeBits \<mapsto>
                                           KOTCB (snd (the (tcb_cte_cases (p && mask tcbBlockSizeBits))) (K v)
                                                (the (projectKO_opt (the (ps (p && ~~ mask tcbBlockSizeBits)))))))))
                   else fail od"
  apply (clarsimp simp: setCTE_def setObject_def split_def
                        fun_eq_iff exec_gets)
  apply (case_tac "real_cte_at' p x")
   apply (clarsimp simp: obj_at'_def projectKOs lookupAround2_known1
                         assert_opt_def alignCheck_assert objBits_simps'
                         magnitudeCheck_assert2 updateObject_cte)
   apply (simp add: simpler_modify_def)
  apply (simp split: if_split, intro conjI impI)
   apply (clarsimp simp: obj_at'_def projectKOs)
   apply (subgoal_tac "p \<le> (p && ~~ mask tcbBlockSizeBits) + 2 ^ tcbBlockSizeBits - 1")
    apply (subgoal_tac "fst (lookupAround2 p (ksPSpace x))
                          = Some (p && ~~ mask tcbBlockSizeBits, KOTCB obj)")
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
    apply (clarsimp simp: domI field_simps)
    apply (clarsimp simp: lookupAround2_char1 obj_at'_def objBits_simps' scBits_simps word_bits_def)
   apply (clarsimp simp: obj_at'_def lookupAround2_char1 objBits_simps' cte_level_bits_def
                         word_bits_def)
  apply (erule empty_failD[OF empty_fail_updateObject_cte])
  done

lemma partial_overwrite_fun_upd2:
  "partial_overwrite idx tsrs (f (x := y))
     = (partial_overwrite idx tsrs f)
          (x := if x \<in> range idx then put_tcb_state_regs (tsrs (inv idx x)) y
                else y)"
  by (simp add: fun_eq_iff partial_overwrite_def split: if_split)

lemma atcbContextSetSetGet_eq[simp]:
  "atcbContextSet (UserContext (user_regs (atcbContextGet t))) t = t"
  by (cases t, simp add: atcbContextSet_def atcbContextGet_def)

lemma setCTE_isolatable:
  "thread_actions_isolatable idx (setCTE p v)"
  supply if_split[split del]
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
  apply (case_tac "p && ~~ mask tcbBlockSizeBits \<in> range idx \<and> p && mask tcbBlockSizeBits \<in> dom tcb_cte_cases")
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
    apply (clarsimp simp: simpler_modify_def fun_eq_iff partial_overwrite_fun_upd2
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
  supply if_split[split del] if_cong[cong]
  apply (simp add: cteInsert_def updateCap_def updateMDB_def
                   Let_def setUntypedCapAsFull_def)
  apply (intro thread_actions_isolatable_bind[OF _ _ hoare_weaken_pre]
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
                        setObject_modify_assert objBits_simps')
  apply (frule_tac x=t' in spec, drule obj_at_ko_at')
  apply (clarsimp simp: exec_gets simpler_modify_def o_def
                intro!: kernel_state.fold_congs[OF refl refl])
  apply (simp add: partial_overwrite_fun_upd
                   partial_overwrite_get_tcb_state_regs)
  apply (clarsimp simp: put_tcb_state_regs_def put_tcb_state_regs_tcb_def get_tcb_state_regs_def
                 elim!: obj_atE')
  apply (case_tac ko)
  apply (simp add: objBits_simps)
  done

lemma thread_actions_isolatableD:
  "\<lbrakk> thread_actions_isolatable idx f; inj idx \<rbrakk>
     \<Longrightarrow> monadic_rewrite False True (\<lambda>s. (\<forall>x. tcb_at' (idx x) s))
            f (isolate_thread_actions idx f id id)"
  by (clarsimp simp: thread_actions_isolatable_def)

lemma tcbSchedDequeue_rewrite:
  "monadic_rewrite True True (obj_at' (Not \<circ> tcbQueued) t) (tcbSchedDequeue t) (return ())"
  apply (simp add: tcbSchedDequeue_def when_def)
  apply monadic_rewrite_symb_exec_l+
      apply (monadic_rewrite_l monadic_rewrite_if_l_False)
     apply (rule monadic_rewrite_refl)
    apply (wpsimp wp: threadGet_const)+
  done

(* FIXME: improve automation here *)
lemma switchToThread_rewrite:
  "monadic_rewrite True True
       (ct_in_state' (Not \<circ> runnable') and cur_tcb' and obj_at' (Not \<circ> tcbQueued) t)
       (switchToThread t)
       (do Arch.switchToThread t; setCurThread t od)"
  apply (simp add: switchToThread_def Thread_H.switchToThread_def)
  apply (monadic_rewrite_l tcbSchedDequeue_rewrite, simp)
   (* strip LHS of getters and asserts until LHS and RHS are the same *)
   apply (repeat_unless \<open>rule monadic_rewrite_refl\<close> monadic_rewrite_symb_exec_l)
      apply wpsimp+
  apply (clarsimp simp: comp_def)
  done

lemma threadGet_isolatable:
  assumes v: "\<And>tsr. \<forall>tcb. f (put_tcb_state_regs_tcb tsr tcb) = f tcb"
  shows "thread_actions_isolatable idx (threadGet f t)"
  apply (clarsimp simp: threadGet_getObject thread_actions_isolatable_def
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
  apply (clarsimp simp: partial_overwrite_def put_tcb_state_regs_def
                  cong: if_cong)
  apply (simp add: projectKO_opt_tcb v split: if_split)
  done

 lemma switchToThread_isolatable:
  "thread_actions_isolatable idx (Arch.switchToThread t)"
  apply (simp add: switchToThread_def
                   storeWordUser_def stateAssert_def2)
  apply (intro thread_actions_isolatable_bind[OF _ _ hoare_weaken_pre]
               gets_isolatable setVMRoot_isolatable
               thread_actions_isolatable_if
               doMachineOp_isolatable
               threadGet_isolatable [OF all_tcbI]
               thread_actions_isolatable_returns
               thread_actions_isolatable_fail)
  done

(* FIXME RT: Maybe no longer true, now that setCurThread contains the ready_qs_runnable assertion,
which depends on the thread state, and could be modified by partial_overwrite *)
lemma setCurThread_isolatable:
  "thread_actions_isolatable idx (setCurThread t)"
  oops
(*  by (simp add: setCurThread_def modify_isolatable) *)

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
  apply (rule monadic_rewrite_guard_imp)
   apply (rule monadic_rewrite_trans)
    apply (rule monadic_rewrite_bind, assumption+)
    apply (wp isolate_thread_actions_tcbs_at)
    apply simp
   apply (subst isolate_thread_actions_wrap_bind, assumption)
   apply (rule monadic_rewrite_in_isolate_thread_actions, assumption)
   apply (rule monadic_rewrite_transverse)
    apply (rule monadic_rewrite_bind_l)
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
  apply (fastforce simp add: ps_clear_def)
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
  apply (simp add: threadGet_getObject liftM_def getObject_get_assert
                   bind_assoc threadSet_def
                   setObject_modify_assert objBits_simps')
  apply (clarsimp simp: monadic_rewrite_def exec_gets
                        exec_modify tcb_at_KOTCB_upd)
  apply (clarsimp simp: simpler_modify_def
                intro!: kernel_state.fold_congs[OF refl refl])
  apply (clarsimp simp: set_register_tsrs_def o_def
                        partial_overwrite_fun_upd
                        partial_overwrite_get_tcb_state_regs)
  apply (drule_tac x=y in spec)
  apply (clarsimp simp: obj_at'_def objBits_simps)
  apply (case_tac obj)
  apply (clarsimp simp: put_tcb_state_regs_def put_tcb_state_regs_tcb_def get_tcb_state_regs_def)
  done

lemma copy_register_isolate:
  "\<lbrakk> inj idx; idx x = src; idx y = dest \<rbrakk> \<Longrightarrow>
  monadic_rewrite False True
      (\<lambda>s. \<forall>x. tcb_at' (idx x) s)
           (do v \<leftarrow> asUser src (getRegister r);
                   asUser dest (setRegister r' (rf v)) od)
           (isolate_thread_actions idx (return ())
                 (copy_register_tsrs x y r r' rf) id)"
  supply if_split[split del]
  apply (simp add: asUser_def split_def bind_assoc
                   getRegister_def setRegister_def
                   select_f_returns isolate_thread_actions_def
                   getSchedulerAction_def)
  apply (simp add: threadGet_getObject liftM_def getObject_get_assert
                   bind_assoc threadSet_def
                   setObject_modify_assert objBits_simps)
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
                   atcbContextGet_def
             cong: if_cong)
  apply (auto simp: fun_eq_iff split: if_split)
  done

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
  apply (rule monadic_rewrite_guard_imp)
   apply (rule monadic_rewrite_bind_tail)+
      apply (rule_tac P="\<lambda> s'. Q s" in monadic_rewrite_bind)
        apply (insert mr)[1]
        apply (simp add: monadic_rewrite_def select_f_def)
        apply auto[1]
       apply (rule_tac P="P and (\<lambda>s. tcbs = get_tcb_state_regs o ksPSpace s o idx
                                             \<and> sa = ksSchedulerAction s)"
                    in monadic_rewrite_pre_imp_eq)
       apply (clarsimp simp: exec_modify eqs return_def)
      apply wp+
  apply (clarsimp simp: o_def eqs)
  done

lemmas monadic_rewrite_isolate_final
    = monadic_rewrite_isolate_final2[where R=\<top>, OF monadic_rewrite_is_refl, simplified]

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
  apply (rule monadic_rewrite_guard_imp)
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
  apply (intro impI thread_actions_isolatable_bind[OF _ _ hoare_weaken_pre]
               getCTE_isolatable setCTE_isolatable,
           (wp | simp)+)
  done

lemma clearUntypedFreeIndex_isolatable:
  "thread_actions_isolatable idx (clearUntypedFreeIndex slot)"
  supply option.case_cong[cong]
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
  "thread_actions_isolatable idx (emptySlot slot NullCap)"
  apply (simp add: emptySlot_def updateCap_def case_Null_If Retype_H.postCapDeletion_def
             cong: if_cong)
  apply (intro thread_actions_isolatable_bind[OF _ _ hoare_weaken_pre]
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
      switchToThread_isolatable (* setCurThread_isolatable *)
      emptySlot_isolatable updateMDB_isolatable
      thread_actions_isolatable_returns

lemmas fastpath_isolate_rewrites
    = isolate_thread_actions_threadSet_tcbState isolate_thread_actions_asUser
      copy_registers_isolate setSchedulerAction_isolate
      fastpath_isolatables[THEN thread_actions_isolatableD]

lemma lookupIPCBuffer_isolatable:
  "thread_actions_isolatable idx (lookupIPCBuffer w t)"
  supply if_cong[cong] if_split[split del]
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

crunch getSchedulable
  for (empty_fail) empty_fail[wp]

lemma setThreadState_rewrite_simple:
  "monadic_rewrite True True
     (\<lambda>s. ((runnable' st
            \<and> active_sc_tcb_at' (ksCurThread s) s
            \<and> (Not \<circ> tcbInReleaseQueue |< tcbs_of' s) (ksCurThread s))
           \<or> ksSchedulerAction s \<noteq> ResumeCurrentThread \<or> t \<noteq> ksCurThread s)
          \<and> tcb_at' t s)
     (setThreadState st t)
     (threadSet (tcbState_update (\<lambda>_. st)) t)"
  supply if_split[split del]
  apply (simp add: setThreadState_def scheduleTCB_def when_def)
  apply (monadic_rewrite_l monadic_rewrite_if_l_False
           \<open>wpsimp wp: hoare_vcg_disj_lift hoare_vcg_imp_lift' threadSet_tcbState_st_tcb_at'
                       getSchedulable_wp threadSet_wp\<close>)
   (* take the threadSet, drop everything until return () *)
   apply (rule monadic_rewrite_trans[OF monadic_rewrite_bind_tail])
     apply (rule monadic_rewrite_symb_exec_l_drop)+
           apply (rule monadic_rewrite_refl)
          apply (wpsimp simp: getCurThread_def
                          wp: hoare_vcg_disj_lift hoare_vcg_imp_lift' threadSet_tcbState_st_tcb_at')+
   apply (rule monadic_rewrite_refl)
  apply (fastforce simp: schedulable'_def obj_at_simps opt_map_def opt_pred_def active_sc_tcb_at'_def
                  split: option.splits if_splits)
  done

end

end
