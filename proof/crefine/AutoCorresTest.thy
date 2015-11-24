(*
 * @LICENSE(NICTA) (FIXME?)
 *)

(* Experimental AutoCorres proofs over CRefine: work in progress *)

theory AutoCorresTest
imports "../../tools/autocorres/AutoCorres"
        "../../tools/autocorres/L4VerifiedLinks"
        "../../../../isabelle-hacks/insulin/Insulin"
        "../../../../isabelle-hacks/ShowTypes"
        (* import Refine_C last to minimise change to global context *)
        Refine_C
begin


autocorres
  [
   skip_heap_abs, skip_word_abs, (* for compatibility *)
   scope = handleYield,
   scope_depth = 0
  ] "c/kernel_all.c_pp"

(* "nontrivial" functions translated *)
ML {*
Find_Theorems.find_theorems @{context} NONE (SOME 999) true
  [(true, Find_Theorems.Name "kernel_all_global_addresses."),
   (true, Find_Theorems.Name "_body_def"),
   (false, Find_Theorems.Pattern (Thm.term_of @{cpat "_ \<equiv> Spec _"})),
   (false, Find_Theorems.Pattern (Thm.term_of @{cpat "_ \<equiv> TRY SKIP CATCH SKIP END"}))]
|> apsnd (map (Facts.string_of_ref o fst) #> sort_strings #> app writeln)
*}

(* "nontrivial" substitutes *)
ML {*
Find_Theorems.find_theorems @{context} NONE (SOME 999) true
  [(true, Find_Theorems.Name "kernel_all_substitute."),
   (true, Find_Theorems.Name "_body_def"),
   (false, Find_Theorems.Pattern (Thm.term_of @{cpat "_ \<equiv> Spec _"})),
   (false, Find_Theorems.Pattern (Thm.term_of @{cpat "_ \<equiv> TRY SKIP CATCH SKIP END"}))]
|> apsnd (map (Facts.string_of_ref o fst) #> sort_strings #> app writeln)
*}

find_theorems name:"kernel_all_global_addresses." name:"_body_def"

context kernel_all begin
(* simple case study: handleYield *)
thm hy_corres
thm kernel_m.handleYield_ccorres

thm state_relation_def
thm kernel.rf_sr_def
thm state_rel.cstate_relation_def
end



lemma rel_sum_comb_Inr:
  "(\<lambda>_ _. False) \<oplus> (\<lambda>_ _. True) = (\<lambda>x y. isRight x \<and> isRight y)"
  apply (rule ext)+
  apply (case_tac x)
  apply (auto simp: isRight_def)
  done

context kernel_m begin

thm kernel_all.handleYield'_ac_corres
    handleYield_ccorres
thm kernel_all.handleYield'_ac_corres[THEN ac_corres_ccorres_underlying, simplified, simplified rel_sum_comb_Inr]
    handleYield_ccorres[simplified rf_sr_def dc_def xfdc_def[abs_def]]

thm ccorres_underlying_def corres_underlying_def

text \<open>
  Slignt weakening of corres_underlying.
  Here we assume termination for the abstract program.
\<close>
definition 
  my_corres_underlying :: "(('s \<times> 't) set) \<Rightarrow> bool \<Rightarrow>
                        ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('t \<Rightarrow> bool)
           \<Rightarrow> ('s, 'a) nondet_monad \<Rightarrow> ('t, 'b) nondet_monad \<Rightarrow> bool"
where
 "my_corres_underlying srel nf rrel G G' \<equiv> \<lambda>m m'. \<forall>(s, s') \<in> srel. G s \<and> G' s' \<longrightarrow>
           \<not> snd (m s) \<longrightarrow>
           (\<forall>(r', t') \<in> fst (m' s'). \<exists>(r, t) \<in> fst (m s). (t, t') \<in> srel \<and> rrel r r') \<and> 
           (nf \<longrightarrow> \<not> snd (m' s') )"


text \<open>
  From AutoCorres @{term ac_corres}, obtain @{term ccorres}.
  This requires a separate corres_underlying proof between the
  AutoCorres spec and DSpec, in order to establish @{term cstate_relation}.
\<close>
lemma autocorres_to_ccorres:
  "\<lbrakk> ac_corres globals \<Gamma> ret_xf arg_rel (liftE ac_f) (Call f_'proc);
     corres_underlying {(s, s'). cstate_relation s s'} True R P \<top> dspec_f ac_f \<rbrakk> \<Longrightarrow>
   ccorres dc xfdc P (Collect arg_rel) [] dspec_f (Call f_'proc)"
  apply (drule ac_corres_ccorres_underlying)
  apply (clarsimp simp: ccorres_underlying_def corres_underlying_def rf_sr_def Ball_def liftE_def)
  apply (erule allE, erule allE, erule_tac P="cstate_relation _ _" in impE, assumption)
  apply clarsimp
  apply (erule allE, erule impE, rule_tac P="arg_rel _" and Q="\<not>snd _" in conjI, assumption, assumption)
  apply (erule allE, erule allE, erule_tac P="\<Gamma>\<turnstile>\<^sub>h \<langle>_, _\<rangle> \<Rightarrow> _" in impE, assumption)
  apply (rename_tac s s' n ret)
  apply (case_tac ret; (simp; fail)?)
  apply (clarsimp simp: in_liftE[simplified liftE_def])
  apply (erule allE, erule allE, erule_tac P="_ \<in> fst _" in impE, assumption)
  apply (auto simp: unif_rrel_def)
  done

lemma autocorres_to_ccorres_alt:
  "\<lbrakk> ac_corres globals \<Gamma> ret_xf arg_rel (liftE ac_f) (Call f_'proc);
     my_corres_underlying {(s, s'). cstate_relation s s'} True R P \<top> dspec_f ac_f \<rbrakk> \<Longrightarrow>
   ccorres dc xfdc P (Collect arg_rel) [] dspec_f (Call f_'proc)"
  apply (drule ac_corres_ccorres_underlying)
  apply (clarsimp simp: ccorres_underlying_def my_corres_underlying_def rf_sr_def Ball_def liftE_def)
  apply (erule allE, erule allE, erule_tac P="cstate_relation _ _" in impE, assumption)
  apply clarsimp
  apply (erule allE, erule impE, rule_tac P="arg_rel _" and Q="\<not>snd _" in conjI, assumption, assumption)
  apply (erule allE, erule allE, erule_tac P="\<Gamma>\<turnstile>\<^sub>h \<langle>_, _\<rangle> \<Rightarrow> _" in impE, assumption)
  apply (rename_tac s s' n ret)
  apply (case_tac ret; (simp; fail)?)
  apply (clarsimp simp: in_liftE[simplified liftE_def])
  apply (erule allE, erule allE, erule_tac P="_ \<in> fst _" in impE, assumption)
  apply (auto simp: unif_rrel_def)
  done

text \<open>
  From @{term ccorres} obtain @{term corres}.
  This is for exporting existing ccorres theorems to be used
  in AutoCorres-based corres proofs.
\<close>
lemma EpsE:
  "\<lbrakk> \<And>x. f x \<Longrightarrow> P x;
     (\<And>x. \<not> f x) \<Longrightarrow> (\<And>y. P y)
   \<rbrakk> \<Longrightarrow> P (Eps f)"
  apply (case_tac "\<exists>x. f x")
   apply (metis someI)
  apply metis
  done

thm AC_call_L1_def L2_call_L1_def L1_call_simpl_def

thm kernel_all.rescheduleRequired'_def[unfolded AC_call_L1_def L2_call_L1_def L1_call_simpl_def]

lemma in_AC_call_simpl:
  fixes r s s' arg_pred globals ret_xf \<Gamma> f_'proc
  shows "(r, s') \<in> fst (AC_call_L1 arg_pred globals ret_xf (L1_call_simpl \<Gamma> f_'proc) s) \<Longrightarrow>
         \<exists>cs cs'. s = globals cs \<and> arg_pred cs \<and>
                  \<Gamma> \<turnstile> Call f_'proc \<down> Normal cs \<and>
                  \<Gamma> \<turnstile> \<langle>Call f_'proc, Normal cs\<rangle> \<Rightarrow> Normal cs' \<and>
                  s' = globals cs' \<and> r = ret_xf cs'"
  apply (clarsimp simp: AC_call_L1_def L2_call_L1_def L1_call_simpl_def)
  apply (monad_eq simp: liftM_def select_def select_f_def liftE_def split: xstate.splits sum.splits)
  apply (rename_tac cs cs' status)
  apply (case_tac status)
  apply auto
  done

lemma ccorres_to_corres_partial:
  assumes ac_def: "ac_f \<equiv> AC_call_L1 arg_rel globals ret_xf (L1_call_simpl \<Gamma> f_'proc)"
  assumes arg_rel_local: "\<And>gs. \<exists>s. globals s = gs \<and> arg_rel s"
  shows "\<lbrakk> ccorres R ret_xf P (Collect arg_rel) [] dspec_f (Call f_'proc) \<rbrakk> \<Longrightarrow>
         my_corres_underlying {(s, s'). cstate_relation s s'} False R P \<top> dspec_f ac_f"
  by (fastforce simp: unif_rrel_def ac_def my_corres_underlying_def ccorres_underlying_def rf_sr_def
                intro: EHOther dest: in_AC_call_simpl)

lemma ccorres_to_corres:
  assumes ac_def: "ac_f \<equiv> AC_call_L1 arg_rel globals ret_xf (L1_call_simpl \<Gamma> f_'proc)"
  assumes arg_rel_local: "\<And>gs. \<exists>s. globals s = gs \<and> arg_rel s"
  shows "\<lbrakk> ccorres R ret_xf P (Collect arg_rel) [] dspec_f (Call f_'proc) \<rbrakk> \<Longrightarrow>
         my_corres_underlying {(s, s'). cstate_relation s s'} True R P \<top> dspec_f ac_f"
  apply (clarsimp simp: ac_def my_corres_underlying_def ccorres_underlying_def rf_sr_def Ball_def Bex_def)
  apply (rename_tac s gs')
  apply (rule conjI)
   -- "proof for return values"
   apply (fastforce simp: unif_rrel_def intro: EHOther dest: in_AC_call_simpl)

  -- "proof for fail bit is trickier"
  apply (clarsimp simp: AC_call_L1_def L2_call_L1_def L1_call_simpl_def)
  apply (clarsimp simp: select_f_def)
  apply (subst (asm) snd_bind)+
  apply (clarsimp simp: select_def split: sum.splits prod.splits)
  apply (clarsimp simp: Bex_def get_def)
  apply (erule impE)
   -- "oops... @{term ccorres} doesn't give us @{term terminates}"
   subgoal sorry
  apply (erule disjE)
  apply (erule allE, erule allE, erule impE, fastforce)
  apply (erule impE, fastforce)
   apply (monad_eq split: xstate.splits sum.splits)
    apply (case_tac xa; clarsimp)
    apply (drule EHOther, fastforce)
    apply blast
   apply (drule EHOther, fastforce)
   apply blast
  apply (monad_eq split: xstate.splits)
  apply (erule allE, erule allE, erule impE, fastforce)
  apply (erule impE, fastforce)
  apply (drule EHAbrupt[OF _ EHEmpty])
  apply blast
  done


lemma ccorres_rrel_nat_unit:
  "ccorres op = (\<lambda>s. ()) st_P arg_P hs m c = ccorres dc xfdc st_P arg_P hs m c"
  by (simp add: ccorres_underlying_def dc_def xfdc_def unif_rrel_def cong del: xstate.case_cong)

(* NB: this is a lie *)
lemma \<Gamma>_eq: "kernel_all_global_addresses.\<Gamma> symbol_table = kernel_all_substitute.\<Gamma> symbol_table domain"
  sorry

(* test case: handleYield *)

lemma getCurThread_corres:
  "corres_underlying {(x, y). cstate_relation x y} True (\<lambda>ct ct'. tcb_ptr_to_ctcb_ptr ct = ct') invs' (\<lambda>_. True) getCurThread (gets ksCurThread_')"
  apply (simp add: getCurThread_def cstate_relation_def)
  by metis

thm tcbSchedDequeue_ccorres
lemma tcbSchedDequeue_corres:
  "tcb_ptr_to_ctcb_ptr ct = ct' \<Longrightarrow>
   my_corres_underlying {(x, y). cstate_relation x y} True (op=)
     (Invariants_H.valid_queues and valid_queues' and tcb_at' ct and valid_objs') \<top>
     (tcbSchedDequeue ct) (kernel_all.tcbSchedDequeue' symbol_table ct')"
  apply (rule ccorres_to_corres)
    apply (simp add: kernel_all.tcbSchedDequeue'_def \<Gamma>_eq)
   apply (rule_tac x="undefined \<lparr> globals := gs, tcb_' := ct' \<rparr>" in exI)
   apply simp
  apply (clarsimp simp: ccorres_rrel_nat_unit tcbSchedDequeue_ccorres[simplified])
  done

thm tcbSchedAppend_ccorres
lemma tcbSchedAppend_corres:
  "tcb_ptr_to_ctcb_ptr ct = ct' \<Longrightarrow>
   my_corres_underlying {(x, y). cstate_relation x y} True (op=)
     (Invariants_H.valid_queues and tcb_at' ct and valid_objs') \<top>
     (tcbSchedAppend ct) (kernel_all.tcbSchedAppend' symbol_table ct')"
  apply (rule ccorres_to_corres)
    apply (simp add: kernel_all.tcbSchedAppend'_def \<Gamma>_eq)
   apply (rule_tac x="undefined \<lparr> globals := gs, tcb_' := ct' \<rparr>" in exI)
   apply simp
  apply (clarsimp simp: ccorres_rrel_nat_unit tcbSchedAppend_ccorres[simplified])
  done

thm rescheduleRequired_ccorres
lemma rescheduleRequired_corres:
  "my_corres_underlying {(x, y). cstate_relation x y} True (op=)
     (Invariants_H.valid_queues and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s) and valid_objs') \<top>
     rescheduleRequired (kernel_all.rescheduleRequired' symbol_table)"
  apply (rule ccorres_to_corres)
    apply (simp add: kernel_all.rescheduleRequired'_def \<Gamma>_eq)
   apply (rule_tac x="undefined \<lparr> globals := gs \<rparr>" in exI)
   apply simp
  apply (clarsimp simp: ccorres_rrel_nat_unit rescheduleRequired_ccorres[simplified])
  done

lemma handleYield_alt_def:
  "handleYield \<equiv> do thread \<leftarrow> getCurThread;
                     tcbSchedDequeue thread;
                     thread \<leftarrow> getCurThread;
                     tcbSchedAppend thread;
                     rescheduleRequired
                  od"
  sorry

(* TODO: port to my_corres_UL *)
lemma (* handleYield_ccorres: *)
  "ccorres dc xfdc (invs' and ct_active') UNIV [] handleYield (Call handleYield_'proc)"
  apply (rule autocorres_to_ccorres[where arg_rel = \<top>, simplified Collect_True])
   apply (subst \<Gamma>_eq[symmetric])
   apply (rule kernel_all.handleYield'_ac_corres)
  apply (simp add: handleYield_alt_def kernel_all.handleYield'_def)
  find_theorems corres_underlying name:split bind
  apply (rule corres_split')
     apply (fastforce intro: corres_guard_imp getCurThread_corres)
    apply (rule corres_split')
       apply (erule tcbSchedDequeue_corres)
      apply (rule corres_split')
         apply (fastforce intro: corres_guard_imp getCurThread_corres)
        apply (rule corres_split')
           apply (rule tcbSchedAppend_corres)
           apply assumption
          apply (rule rescheduleRequired_corres)
         apply (wp tcbSchedAppend_valid_objs')[1]
          apply simp
         defer (* runnable *)
        apply wp[1]
       apply wp[1]
       apply (simp add: invs_queues tcb_at_invs' invs_valid_objs')
      apply wp[1]
     apply wp[1]
     apply clarsimp
     defer (* invs' *)
    apply wp[1]
   apply wp[1]
   apply (simp add: invs_queues tcb_at_invs' invs_valid_objs' invs_valid_queues')
  apply wp[1]
  oops

lemma
  "corres_underlying {(s, s'). cstate_relation s s'}
     True dc (invs' and ct_active'(* and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)*))
     (\<lambda>_. True) handleYield (kernel_all.handleYield' symbol_table)"
  apply (unfold handleYield_def kernel_all.handleYield'_def)
  apply (rule corres_split')

     apply (clarsimp simp: getCurThread_def cstate_relation_def Let_def)
     apply assumption

    apply (rule corres_split')
    thm tcbSchedDequeue_ccorres
  thm getCurThread_ccorres
  thm tcb_ptr_to_ctcb_ptr_def
  oops

end




context kernel_m
begin

lemma ccorres_dc_liftE:
  "ccorres dc xf P P' hs H C \<Longrightarrow> ccorres (\<lambda>x y. isRight x \<and> isRight y) (Inr o xf) P P' hs (liftE H) C"
  apply (clarsimp simp: ccorres_underlying_def isRight_def dc_def split: xstate.splits)
  apply (drule (1) bspec)
  apply (clarsimp simp: split_def liftE_def bind_def return_def unif_rrel_def)
  apply (fastforce)
  done

thm kernel_all.handleYield'_ac_corres[THEN ac_corres_ccorres_underlying, simplified, simplified rel_sum_comb_Inr]
    handleYield_ccorres[THEN ccorres_dc_liftE, simplified dc_def xfdc_def[abs_def] o_def]

desugar_thm handleYield_ccorres[THEN ccorres_dc_liftE, simplified dc_def xfdc_def[abs_def] o_def] "ccorres "

end

end
