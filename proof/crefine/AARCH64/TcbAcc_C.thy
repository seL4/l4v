(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2014, General Dynamics C4 Systems
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory TcbAcc_C
imports Ctac_lemmas_C
begin

context kernel
begin

lemma ccorres_pre_threadGet:
  assumes cc: "\<And>rv. ccorres r xf (P rv) (P' rv) hs (g rv) c"
  shows   "ccorres r xf
           (\<lambda>s. \<forall>tcb. ko_at' tcb p s \<longrightarrow> P (f tcb) s)
           ({s'. \<forall>tcb ctcb. cslift s' (tcb_ptr_to_ctcb_ptr p) = Some ctcb \<and> ctcb_relation tcb ctcb \<longrightarrow> s' \<in> P' (f tcb)})
           hs (threadGet f p >>= (\<lambda>rv. g rv)) c"
  apply (rule ccorres_guard_imp)
    apply (rule ccorres_symb_exec_l)
       defer
       apply wp[1]
      apply (rule tg_sp')
     apply simp
    apply assumption
   defer
   apply (rule ccorres_guard_imp)
     apply (rule cc)
    apply clarsimp
    apply (frule obj_at_ko_at')
    apply clarsimp
  apply assumption
  apply clarsimp
  apply (frule (1) obj_at_cslift_tcb)
  apply clarsimp
  done

lemma ccorres_pre_archThreadGet:
  assumes cc: "\<And>rv. ccorres r xf (P rv) (P' rv) hs (g rv) c"
  shows   "ccorres r xf
           (\<lambda>s. \<forall>tcb. ko_at' tcb p s \<longrightarrow> P (f (tcbArch tcb)) s)
           ({s'. \<forall>tcb ctcb. cslift s' (tcb_ptr_to_ctcb_ptr p) = Some ctcb
                            \<and> ctcb_relation tcb ctcb \<longrightarrow> s' \<in> P' (f (tcbArch tcb))})
           hs (archThreadGet f p >>= (\<lambda>rv. g rv)) c"
  apply (rule ccorres_guard_imp)
    apply (rule ccorres_symb_exec_l)
       defer
       apply wp[1]
      apply (rule atg_sp')
     apply simp
    apply assumption
   defer
   apply (rule ccorres_guard_imp)
     apply (rule cc)
    apply clarsimp
    apply (frule obj_at_ko_at')
    apply clarsimp
  apply assumption
  apply clarsimp
  apply (frule (1) obj_at_cslift_tcb)
  apply clarsimp
  done

lemma threadGet_eq:
  "ko_at' tcb thread s \<Longrightarrow> (f tcb, s) \<in> fst (threadGet f thread s)"
  unfolding threadGet_def
  apply (simp add: liftM_def in_monad)
  apply (rule exI [where x = tcb])
  apply simp
  apply (subst getObject_eq)
     apply simp
    apply (simp add: objBits_simps')
   apply assumption
  apply simp
  done

lemma archThreadGet_eq:
  "ko_at' tcb thread s \<Longrightarrow> (f (tcbArch tcb), s) \<in> fst (archThreadGet f thread s)"
  unfolding archThreadGet_def
  apply (simp add: liftM_def in_monad)
  apply (rule exI [where x = tcb])
  apply simp
  apply (subst getObject_eq)
     apply simp
    apply (simp add: objBits_simps')
   apply assumption
  apply simp
  done

lemma get_tsType_ccorres[corres]:
  "ccorres (\<lambda>r r'. r' = thread_state_to_tsType r) ret__unsigned_longlong_' (tcb_at' thread)
           ({s. f s = tcb_ptr_to_ctcb_ptr thread} \<inter>
            {s. cslift s (Ptr &(f s\<rightarrow>[''tcbState_C''])) = Some (thread_state_' s)}) []
  (getThreadState thread) (Call thread_state_get_tsType_'proc)"
  unfolding getThreadState_def
  apply (rule ccorres_from_spec_modifies [where P=\<top>, simplified])
     apply (rule thread_state_get_tsType_spec)
    apply (rule thread_state_get_tsType_modifies)
   apply simp
  apply (frule (1) obj_at_cslift_tcb)
  apply (clarsimp simp: typ_heap_simps)
  apply (rule bexI [rotated, OF threadGet_eq], assumption)
  apply simp
  apply (drule ctcb_relation_thread_state_to_tsType)
  apply simp
  done

lemma threadGet_obj_at2:
  "\<lbrace>\<top>\<rbrace> threadGet f thread \<lbrace>\<lambda>v. obj_at' (\<lambda>t. f t = v) thread\<rbrace>"
  apply (rule hoare_post_imp)
   prefer 2
   apply (rule tg_sp')
  apply simp
  done

lemma register_from_H_less:
  "register_from_H hr < 37"
  by (cases hr, simp_all add: "StrictC'_register_defs")

lemma register_from_H_sless:
  "UCAST(register_idx_len \<rightarrow> int_literal_len) (register_from_H hr) <s 0x25"
  by (cases hr, simp_all add: "StrictC'_register_defs" word_sless_def word_sle_def)

lemma register_from_H_0_sle'[simp]:
  "0 <=s UCAST(register_idx_len \<rightarrow> int_literal_len) (register_from_H hr)"
  by (cases hr, simp_all add: "StrictC'_register_defs" word_sless_def word_sle_def)

lemma getRegister_ccorres [corres]:
  "ccorres (=) ret__unsigned_long_' \<top>
             ({s. thread_' s = tcb_ptr_to_ctcb_ptr thread} \<inter> {s. reg_' s = register_from_H reg}) []
             (asUser thread (getRegister reg)) (Call getRegister_'proc)"
  apply (unfold asUser_def)
  apply (rule ccorres_guard_imp)
    apply (rule ccorres_symb_exec_l [where Q="\<lambda>u. obj_at' (\<lambda>t. (atcbContextGet o tcbArch) t = u) thread" and
      Q'="\<lambda>rv. {s. thread_' s = tcb_ptr_to_ctcb_ptr thread} \<inter> {s. reg_' s = register_from_H reg}"])
       apply (rule ccorres_from_vcg)
       apply (rule allI, rule conseqPre)
        apply vcg
       apply clarsimp
       apply (drule (1) obj_at_cslift_tcb)
       apply (clarsimp simp: typ_heap_simps register_from_H_less register_from_H_sless)
       apply (clarsimp simp: getRegister_def typ_heap_simps)
       apply (rule_tac x = "((user_regs o atcbContextGet o tcbArch) ko reg, \<sigma>)" in bexI [rotated])
        apply (simp add: in_monad' asUser_def select_f_def split_def)
        apply (subst arg_cong2 [where f = "(\<in>)"])
          defer
          apply (rule refl)
         apply (erule threadSet_eq)
        apply (clarsimp simp: ctcb_relation_def ccontext_relation_def cregs_relation_def carch_tcb_relation_def)
       apply (wp threadGet_obj_at2)+
   apply simp
  apply simp
  apply (erule obj_atE')
  apply (clarsimp simp: projectKOs )
  apply (subst fun_upd_idem)
   apply (case_tac ko)
   apply clarsimp
  apply simp
  done

lemma getRestartPC_ccorres [corres]:
  "ccorres (=) ret__unsigned_long_' \<top> \<lbrace>\<acute>thread = tcb_ptr_to_ctcb_ptr thread\<rbrace> []
           (asUser thread getRestartPC) (Call getRestartPC_'proc)"
  unfolding getRestartPC_def
  apply (cinit')
   apply (rule ccorres_add_return2, ctac)
     apply (rule ccorres_return_C, simp+)[1]
    apply wp
   apply vcg
  apply (simp add: scast_id)
  done

lemma threadSet_corres_lemma:
  assumes spec: "\<forall>s. \<Gamma>\<turnstile> \<lbrace>s. P s\<rbrace> Call f {t. Q s t}"
  and      mod: "modifies_heap_spec f"
  and  rl: "\<And>\<sigma> x t ko. \<lbrakk>(\<sigma>, x) \<in> rf_sr; Q x t; x \<in> P'; ko_at' ko thread \<sigma>\<rbrakk>
             \<Longrightarrow> (\<sigma>\<lparr>ksPSpace := (ksPSpace \<sigma>)(thread \<mapsto> KOTCB (g ko))\<rparr>,
                  t\<lparr>globals := globals x\<lparr>t_hrs_' := t_hrs_' (globals t)\<rparr>\<rparr>) \<in> rf_sr"
  and  g:  "\<And>s x. \<lbrakk>tcb_at' thread s; x \<in> P'; (s, x) \<in> rf_sr\<rbrakk> \<Longrightarrow> P x"
  shows "ccorres dc xfdc (tcb_at' thread) P' [] (threadSet g thread) (Call f)"
  apply (rule ccorres_Call_call_for_vcg)
   apply (rule ccorres_from_vcg)
   apply (rule allI, rule conseqPre)
   apply (rule HoarePartial.ProcModifyReturnNoAbr [where return' = "\<lambda>s t. t\<lparr> globals := globals s\<lparr>t_hrs_' := t_hrs_' (globals t) \<rparr>\<rparr>"])
     apply (rule HoarePartial.ProcSpecNoAbrupt [OF _ _ spec])
      apply (rule subset_refl)
     apply vcg
    prefer 2
    apply (rule mod)
   apply (clarsimp simp: mex_def meq_def)
  apply clarsimp
  apply (rule conjI)
   apply (erule (2) g)
  apply clarsimp
   apply (frule obj_at_ko_at')
   apply clarsimp
   apply (rule bexI [rotated])
   apply (erule threadSet_eq)
   apply simp
  apply (rule_tac x1 = "t\<lparr>globals := globals x\<lparr>t_hrs_' := t_hrs_' (globals t)\<rparr>\<rparr>" in iffD1 [OF rf_sr_upd], simp_all)[1]
  apply (erule (3) rl)
  done


lemma threadSet_ccorres_lemma4:
  "\<lbrakk> \<And>s tcb. \<Gamma> \<turnstile> (Q s tcb) c {s'. (s \<lparr>ksPSpace := (ksPSpace s)(thread \<mapsto> injectKOS (F tcb))\<rparr>, s') \<in> rf_sr};
          \<And>s s' tcb tcb'. \<lbrakk> (s, s') \<in> rf_sr; P tcb; ko_at' tcb thread s;
                             cslift s' (tcb_ptr_to_ctcb_ptr thread) = Some tcb';
                             ctcb_relation tcb tcb'; P' s ; s' \<in> R\<rbrakk> \<Longrightarrow> s' \<in> Q s tcb \<rbrakk>
         \<Longrightarrow> ccorres dc xfdc (obj_at' (P :: tcb \<Rightarrow> bool) thread and P') R hs (threadSet F thread) c"
  apply (rule ccorres_from_vcg)
  apply (rule allI)
  apply (case_tac "obj_at' P thread \<sigma>")
   apply (drule obj_at_ko_at', clarsimp)
   apply (rule conseqPre, rule conseqPost)
      apply assumption
     apply clarsimp
     apply (rule rev_bexI, rule threadSet_eq)
      apply assumption
     apply simp
    apply simp
   apply clarsimp
   apply (drule(1) obj_at_cslift_tcb, clarsimp)
  apply simp
  apply (rule hoare_complete')
  apply (simp add: cnvalid_def nvalid_def) (* pretty *)
  done

lemmas threadSet_ccorres_lemma3 = threadSet_ccorres_lemma4[where R=UNIV]

lemmas threadSet_ccorres_lemma2
    = threadSet_ccorres_lemma3[where P'=\<top>]

lemma is_aligned_tcb_ptr_to_ctcb_ptr:
  "obj_at' (P :: tcb \<Rightarrow> bool) p s
     \<Longrightarrow> is_aligned (ptr_val (tcb_ptr_to_ctcb_ptr p)) ctcb_size_bits"
  apply (clarsimp simp: obj_at'_def objBits_simps' projectKOs
                        tcb_ptr_to_ctcb_ptr_def ctcb_offset_defs)
  apply (erule aligned_add_aligned, simp_all add: word_bits_conv)
  apply (simp add: is_aligned_def)
  done

lemma sanitiseRegister_spec:
  "\<forall>s t v r. \<Gamma> \<turnstile> ({s} \<inter> \<lbrace>\<acute>v = v\<rbrace> \<inter> \<lbrace>\<acute>reg = register_from_H r\<rbrace> \<inter> \<lbrace>\<acute>archInfo = from_bool t\<rbrace>)
                   Call sanitiseRegister_'proc
                 \<lbrace>\<acute>ret__unsigned_long = sanitiseRegister t r v\<rbrace>"
  apply vcg
  by (case_tac r; simp add: C_register_defs sanitiseRegister_def)

lemma ctcb_relation_tcbVCPU:
  "ctcb_relation t ko' \<Longrightarrow> tcbVCPU_C (tcbArch_C ko') = option_to_ptr (atcbVCPUPtr (tcbArch t))"
  unfolding ctcb_relation_def carch_tcb_relation_def ccontext_relation_def
  by clarsimp

lemma valid_tcb'_vcpuE [elim_format]:
    "valid_tcb' t s \<Longrightarrow> atcbVCPUPtr (tcbArch t) = Some v \<Longrightarrow> vcpu_at' v s"
    unfolding valid_tcb'_def valid_arch_tcb'_def
    by auto

lemma rf_sr_ksArchState_armHSCurVCPU:
  "(s, s') \<in> rf_sr \<Longrightarrow> cur_vcpu_relation (armHSCurVCPU (ksArchState s)) (armHSCurVCPU_' (globals s')) (armHSVCPUActive_' (globals s'))"
  by (clarsimp simp: rf_sr_def cstate_relation_def carch_state_relation_def Let_def)

lemma ccorres_pre_getCurVCPU:
  assumes cc: "\<And>rv. ccorres r xf (P rv) (P' rv) hs (f rv) c"
  shows   "ccorres r xf
                  (\<lambda>s. (\<forall>rv. (armHSCurVCPU \<circ> ksArchState) s = rv \<longrightarrow> P rv s))
                  {s. \<forall>rv vcpu' act'. armHSCurVCPU_' (globals s) = vcpu' \<and>
                                      armHSVCPUActive_' (globals s) = act' \<and>
                                      cur_vcpu_relation rv vcpu' act'
                                 \<longrightarrow> s \<in> P' rv }
                          hs (gets (armHSCurVCPU \<circ> ksArchState) >>= (\<lambda>rv. f rv)) c"
  apply (rule ccorres_guard_imp)
    apply (rule ccorres_symb_exec_l)
       defer
       apply wp
      apply (rule hoare_gets_sp)
     apply (clarsimp simp: empty_fail_def getCurThread_def simpler_gets_def)
    apply assumption
   apply clarsimp
   defer
   apply (rule ccorres_guard_imp)
     apply (rule cc)
    apply clarsimp
   apply assumption
  apply (clarsimp simp: rf_sr_ksArchState_armHSCurVCPU)
  done

lemma rf_sr_ksArchState_armKSCurFPUOwner:
  "(s, s') \<in> rf_sr \<Longrightarrow> cur_fpu_relation (armKSCurFPUOwner (ksArchState s)) (ksCurFPUOwner_' (globals s'))"
  by (clarsimp simp: rf_sr_def cstate_relation_def carch_state_relation_def Let_def)

lemma ccorres_pre_getCurFPUOwner:
  assumes cc: "\<And>rv. ccorres r xf (P rv) (P' rv) hs (f rv) c"
  shows
    "ccorres r xf
       (\<lambda>s. (\<forall>rv. (armKSCurFPUOwner \<circ> ksArchState) s = rv \<longrightarrow> P rv s))
       {s. \<forall>rv fpu'. ksCurFPUOwner_' (globals s) = fpu' \<and> cur_fpu_relation rv fpu' \<longrightarrow> s \<in> P' rv} hs
       (gets (armKSCurFPUOwner \<circ> ksArchState) >>= (\<lambda>rv. f rv)) c"
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
  apply (simp add: rf_sr_ksArchState_armKSCurFPUOwner)
  done

lemma getObject_tcb_wp':
  "\<lbrace>\<lambda>s. \<forall>t. ko_at' (t :: tcb) p s \<longrightarrow> Q t s\<rbrace> getObject p \<lbrace>Q\<rbrace>"
  by (clarsimp simp: getObject_def valid_def in_monad
                     split_def objBits_simps' loadObject_default_def
                     projectKOs obj_at'_def in_magnitude_check)

lemma ccorres_pre_getObject_tcb:
  assumes cc: "\<And>rv. ccorres r xf (P rv) (P' rv) hs (f rv) c"
  shows   "ccorres r xf
                  (\<lambda>s. (\<forall>tcb. ko_at' tcb p s \<longrightarrow> P tcb s))
                  {s. \<forall> tcb tcb'. cslift s (tcb_ptr_to_ctcb_ptr p) = Some tcb' \<and> ctcb_relation tcb tcb'
                           \<longrightarrow> s \<in> P' tcb}
                          hs (getObject p >>= (\<lambda>rv :: tcb. f rv)) c"
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_symb_exec_l)
      apply (rule ccorres_guard_imp2)
       apply (rule cc)
      apply (rule conjI)
       apply (rule_tac Q="ko_at' rv p s" in conjunct1)
       apply assumption
      apply assumption
     apply (wpsimp wp: empty_fail_getObject getObject_tcb_wp')+
    apply (erule cmap_relationE1[OF cmap_relation_tcb],
           erule ko_at_projectKO_opt)
  apply simp
  done

lemma ccorres_pre_getObject_vcpu:
  assumes cc: "\<And>rv. ccorres r xf (P rv) (P' rv) hs (f rv) c"
  shows   "ccorres r xf
                  (\<lambda>s. (\<forall>vcpu. ko_at' vcpu p s \<longrightarrow> P vcpu s))
                  {s. \<forall> vcpu vcpu'. cslift s (vcpu_Ptr p) = Some vcpu' \<and> cvcpu_relation vcpu vcpu'
                           \<longrightarrow> s \<in> P' vcpu}
                          hs (getObject p >>= (\<lambda>rv :: vcpu. f rv)) c"
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_symb_exec_l)
      apply (rule ccorres_guard_imp2)
       apply (rule cc)
      apply (rule conjI)
       apply (rule_tac Q="ko_at' rv p s" in conjunct1)
       apply assumption
      apply assumption
     apply (wpsimp wp: getVCPU_wp empty_fail_getObject)+
    apply (erule cmap_relationE1 [OF cmap_relation_vcpu],
         erule ko_at_projectKO_opt)
  apply simp
  done

lemma armHSCurVCPU_update_active_ccorres:
  "b' = from_bool b \<Longrightarrow> v' = fst v \<Longrightarrow>
   ccorres dc xfdc (\<lambda>s. armHSCurVCPU (ksArchState s) = Some v) UNIV hs
      (modifyArchState (armHSCurVCPU_update (\<lambda>_. Some (v', b))))
      (Basic (\<lambda>s. globals_update (armHSVCPUActive_'_update (\<lambda>_. b')) s))"
  apply (clarsimp simp: modifyArchState_def)
  apply (rule ccorres_from_vcg)
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp: bind_def simpler_gets_def simpler_modify_def)
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def)
  by (clarsimp simp: carch_state_relation_def carch_globals_def cur_vcpu_relation_def
                     cmachine_state_relation_def
               split: bool.split)

lemma armHSCurVCPU_update_curv_ccorres:
  "ccorres dc xfdc (\<lambda>s. ((armHSCurVCPU (ksArchState s)) = Some (v, a)) \<and> v \<noteq> 0 \<and> new \<noteq> 0) UNIV hs
    (modifyArchState (armHSCurVCPU_update (\<lambda>_. Some (new, a))))
    (Basic (\<lambda>s. globals_update (armHSCurVCPU_'_update (\<lambda>_. Ptr new)) s))"
  apply (clarsimp simp: modifyArchState_def)
  apply (rule ccorres_from_vcg)
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp: bind_def simpler_gets_def simpler_modify_def)
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def)
  by (clarsimp simp: carch_state_relation_def carch_globals_def cur_vcpu_relation_def
                     cmachine_state_relation_def
               split: bool.split)

lemma armHSCurVCPU_update_ccorres:
  "ccorres dc xfdc (\<lambda>_. cur_vcpu_relation curv vcpu act) UNIV hs
     (modifyArchState (armHSCurVCPU_update (\<lambda>_. curv)))
     (Basic (\<lambda>s. globals_update (armHSCurVCPU_'_update (\<lambda>_. vcpu)) s);;
        Basic (\<lambda>s. globals_update (armHSVCPUActive_'_update (\<lambda>_. act)) s))"
  apply (clarsimp simp: modifyArchState_def)
  apply (rule ccorres_from_vcg)
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp: bind_def simpler_gets_def simpler_modify_def)
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def)
  by (clarsimp simp: carch_state_relation_def carch_globals_def cur_vcpu_relation_def
                     cmachine_state_relation_def
               split: bool.split)

lemmas armHSCurVCPU_update_active_ccorres2 = armHSCurVCPU_update_ccorres[where curv="Some (v, b)" for v b]

lemma armKSCurFPUOwner_update_ccorres:
  "ccorres dc xfdc (\<lambda>_. cur_fpu_relation fpu fpu') UNIV hs
     (modifyArchState (armKSCurFPUOwner_update (\<lambda>_. fpu)))
     (Basic (\<lambda>s. globals_update (ksCurFPUOwner_'_update (\<lambda>_. fpu')) s))"
  apply (clarsimp simp: modifyArchState_def)
  apply (rule ccorres_from_vcg)
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp: bind_def simpler_gets_def simpler_modify_def)
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def)
  by (clarsimp simp: carch_state_relation_def carch_globals_def cur_fpu_relation_def
                     cmachine_state_relation_def)

lemma invs'_HScurVCPU_vcpu_at':
  "\<lbrakk>invs' s; armHSCurVCPU (ksArchState s) = Some (a, b) \<rbrakk> \<Longrightarrow> vcpu_at' a s"
by (fastforce dest: invs_arch_state' simp: valid_arch_state'_def vcpu_at_is_vcpu' ko_wp_at'_def split: option.splits)

crunch vcpuDisable, vcpuRestore, vcpuSave, vcpuEnable
  for ksArch[wp]: "\<lambda>s. P (ksArchState s)"
  (wp: crunch_wps)

(* FIXME: move *)
lemma vcpu_at_c_guard:
  "\<lbrakk>vcpu_at' p s; (s, s') \<in> rf_sr\<rbrakk> \<Longrightarrow> c_guard (vcpu_Ptr p)"
  by (fastforce intro: typ_heap_simps dest!: vcpu_at_ko vcpu_at_rf_sr)

(* FIXME move *)
lemma ccorres_pre_gets_armKSGICVCPUNumListRegs_ksArchState:
  assumes cc: "\<And>rv. ccorres r xf (P rv) (P' rv) hs (f rv) c"
  shows   "ccorres r xf
                  (\<lambda>s. (\<forall>rv. (armKSGICVCPUNumListRegs \<circ> ksArchState) s = rv \<longrightarrow> P rv s))
                  {s. \<forall>rv vcpu' act'. of_nat rv = gic_vcpu_num_list_regs_' (globals s)
                                 \<longrightarrow> s \<in> P' rv }
                          hs (gets (armKSGICVCPUNumListRegs \<circ> ksArchState) >>= (\<lambda>rv. f rv)) c"
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
  apply (simp add: rf_sr_armKSGICVCPUNumListRegs)
  done

(* FIXME: MOVE, probably to CSpace_RAB  *)
lemma ccorres_gen_asm2_state:
  assumes rl: "\<And>s. P s \<Longrightarrow> ccorres r xf G G' hs a c"
  shows "ccorres r xf G (G' \<inter> {s. P s}) hs a c"
proof (rule ccorres_guard_imp2)
  show "ccorres r xf G (G' \<inter> {_. \<exists>s. P s}) hs a c"
    apply (rule ccorres_gen_asm2)
    apply (erule exE)
    apply (erule rl)
    done
next
  fix s s'
  assume "(s, s') \<in> rf_sr" and "G s" and "s' \<in> G' \<inter> {s. P s}"
  thus "G s \<and> s' \<in> (G' \<inter> {_. \<exists>s. P s})"
    by (clarsimp elim!: exI simp: Collect_const_mem)
qed

lemma cap_case_TCBCap2:
  "(case cap of ThreadCap pd
                   \<Rightarrow> f pd | _ \<Rightarrow> g)
   = (if isThreadCap cap
      then f (capTCBPtr cap)
      else g)"
  by (simp add: isCap_simps
         split: capability.split arch_capability.split)

lemma length_of_msgRegisters:
  "length AARCH64_H.msgRegisters = 4"
  by (auto simp: msgRegisters_unfold)

lemma setMRs_single:
  "setMRs thread buffer [val] = do
     _ \<leftarrow> asUser thread (setRegister register.X2 val);
     return 1
   od"
  apply (clarsimp simp: setMRs_def length_of_msgRegisters zipWithM_x_def zipWith_def split: option.splits)
  apply (subst zip_commute, subst zip_singleton)
   apply (simp add: length_of_msgRegisters length_0_conv[symmetric])
  apply (clarsimp simp: msgRegisters_unfold sequence_x_def)
  done

end
end
