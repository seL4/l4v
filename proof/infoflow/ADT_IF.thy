(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

text \<open>
  This file sets up a kernel automaton, ADT_A_if, which is
  slightly different from ADT_A.
  It then setups a big step framework to transfrom this automaton in the
  big step automaton on which the infoflow theorem will be proved
\<close>

theory ADT_IF
imports
    Noninterference_Base
    "Access.Syscall_AC"
    "Access.ADT_AC"
    IRQMasks_IF FinalCaps Scheduler_IF UserOp_IF
begin

section \<open>Generic big step automaton\<close>

inductive_set sub_big_steps
  :: "('a,'b,'c) data_type \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)  \<Rightarrow>  'a  \<Rightarrow> ('a \<times> 'c list) set"
  for A :: "('a,'b,'c) data_type" and R :: "('a \<Rightarrow> 'a \<Rightarrow> bool)" and s :: "'a"
where
  nil: "\<lbrakk>evlist = []; t = s; \<not> R s s\<rbrakk> \<Longrightarrow>  (t,evlist) \<in> sub_big_steps A R s" |
  step: "\<lbrakk>evlist = evlist' @ [e]; (s',evlist') \<in> sub_big_steps A R s;
          (s',t) \<in> data_type.Step A e; \<not> R s t\<rbrakk> \<Longrightarrow>  (t,evlist) \<in> sub_big_steps A R s"

text \<open>
  Turn the (observable) multi-step executions of one automaton into the
  steps of another. We call this second automaton a \emph{big step} automaton
  of the first. We use a relation on observable states of the original
  automaton to demarcate one big step from the next.
\<close>
inductive_set big_steps
  :: "('a,'b,'c) data_type \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('c list \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> ('a \<times> 'a) set)"
  for A :: "('a,'b,'c) data_type" and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and exmap :: "'c list \<Rightarrow> 'd"
  and ev :: "'d"
where
  cstep: "\<lbrakk>(s',as) \<in> sub_big_steps A R s; (s',t) \<in> data_type.Step A a;
           R s t; ev = exmap (as @ [a])\<rbrakk> \<Longrightarrow>
          (s,t) \<in> big_steps A R exmap ev"

definition big_step_adt
  :: "('a,'b,'c) data_type \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('c list \<Rightarrow> 'd) \<Rightarrow> ('a,'b,'d) data_type"
where
  "big_step_adt A R exmap \<equiv>
       \<lparr>Init = Init A, Fin = Fin A, Step = big_steps A R exmap\<rparr>"

lemma system_Step_def_raw:
  "system.Step = (\<lambda>A a. {(s,s') . s' \<in> execution A s [a]})"
  apply(rule ext)
  apply(rule ext)
  apply(subst system.Step_def)
  by(rule refl)

lemma big_stepsD:
  "(s,t) \<in> big_steps A R exmap ev \<Longrightarrow>
    \<exists> s' as a. (s',as) \<in> sub_big_steps A R s \<and> (s',t) \<in> data_type.Step A a \<and>
                R s t \<and> ev = exmap (as @ [a])"
  apply(erule big_steps.induct)
  apply blast
  done

lemma big_stepsE:
  assumes bs: "(s,t) \<in> big_steps A R exmap ev"
  obtains s' as a where "(s',as) \<in> sub_big_steps A R s"
                        "(s',t) \<in> data_type.Step A a"
                        "R s t"
                        "ev =  exmap (as @ [a])"
  using bs[THEN big_stepsD] by blast


lemma Run_subset:
  "(\<And> ev. Stepf ev \<subseteq> Stepf' ev) \<Longrightarrow>
   Run Stepf as \<subseteq> Run Stepf' as"
  apply(induct as)
   apply simp
  apply auto
  done

lemma rtranclp_def2:
  "(R\<^sup>*\<^sup>* s0 s) = (R\<^sup>+\<^sup>+ s0 s \<or> s = s0)"
  apply (safe)
   apply (drule rtranclpD)
   apply simp
  apply (erule tranclp_into_rtranclp)
  done

definition Fin_trancl
where
  "Fin_trancl A R s s' \<equiv> R\<^sup>+\<^sup>+ s s' \<or> Fin A s = Fin A s'"

text \<open>
  A sufficient condition to show that the big steps of a big step ADT
  terminate (i.e. that the relation R eventually becomes satisfied.)
\<close>
definition rel_terminate
  :: "('a,'b,'c) data_type \<Rightarrow> 'b \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a set) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> nat) \<Rightarrow> bool"
where
  "rel_terminate A s0 R I measuref \<equiv>
          (\<forall>s. s \<in> I \<and> (\<exists>s0'\<in> Init A s0. R\<^sup>*\<^sup>* s0' s) \<longrightarrow>
           (\<forall> as s'. (s',as) \<in> sub_big_steps A R s \<longrightarrow>
             (\<forall>s'' a. (s',s'') \<in> data_type.Step A a \<longrightarrow> ((measuref s s'' < measuref s s') \<and>
             (measuref s s' > 0 \<longrightarrow> measuref s s'' = 0 \<longrightarrow> R s s'')))))"





lemma rel_terminateE:
  assumes a: "rel_terminate A s0 R I measuref"
  assumes b: "\<lbrakk>(\<And>s s' as s'' a. \<lbrakk>s \<in> I;
                           \<exists>s0'\<in> Init A s0. R\<^sup>*\<^sup>* s0' s; (s',as) \<in> sub_big_steps A R s;
                           (s',s'') \<in> data_type.Step A a; measuref s s' > 0;
                           measuref s s'' = 0\<rbrakk> \<Longrightarrow> R s s'');
               (\<And>s s' as s'' a. \<lbrakk>s \<in> I; \<exists>s0'\<in> Init A s0. R\<^sup>*\<^sup>* s0' s;
                                 (s',as) \<in> sub_big_steps A R s;
                                 (s',s'') \<in> data_type.Step A a\<rbrakk> \<Longrightarrow>
                                measuref s s'' < measuref s s')\<rbrakk> \<Longrightarrow> C"
 shows "C"
  apply(rule b)
  using a apply(fastforce simp: rel_terminate_def)+
  done

lemma Run_big_steps_tranclp:
  "(s0, s) \<in> Run (big_steps C R exmap) js  \<Longrightarrow>
   R\<^sup>*\<^sup>* s0 s"
  apply(induct js arbitrary: s rule: rev_induct)
   apply simp
  apply(fastforce dest: Run_mid elim: big_steps.cases)
  done

lemma Step_system_reachable_trans:
  "Step_system A s0 \<Longrightarrow> system.reachable A s0 s \<Longrightarrow>
   system.reachable A s s' \<Longrightarrow> system.reachable A s0 s'"
  apply(clarsimp simp: system.reachable_def)
  apply(rule Step_system.reachable_execution[simplified system.reachable_def])
    apply blast+
  done

lemma Step_system_reachable:
  "Step_system A s0 \<Longrightarrow> system.reachable A s0 s \<Longrightarrow>
  Step_system A s"
  apply(subst Step_system_def)
  apply(rule conjI)
   apply(fastforce simp: system.reachable_def Step_system.execution_Run intro: exI[where x="[]"])
  apply clarsimp
  apply(frule Step_system_reachable_trans, assumption+)
  apply(simp add: Step_system.execution_Run)
  done

lemma Step_system_execution_Run_s0:
  "Step_system A s0 \<Longrightarrow>
   execution A s0 as = {s'. (s0,s') \<in> Run (system.Step A) as}"
  apply(rule Step_system.execution_Run, assumption)
  apply(erule Step_system.reachable_s0)
  done

text \<open>
  Define a relation on states that is basically the inverse of the
  Step relation for states @{term y} reachable from a given state @{term s}
  before the next big step has finished.
\<close>
definition step_measuref_rel_from
  :: "('a,'b,'c) data_type \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'a) set"
where
  "step_measuref_rel_from A R s \<equiv>
      {(x,y). \<exists>a as. (y,x) \<in> data_type.Step A a \<and> (y,as) \<in> sub_big_steps A R s}"

lemma wf_step_measuref_rel_from:
  "\<lbrakk>rel_terminate A s0 R I measuref;
    s \<in> I; \<exists>s0'\<in> Init A s0. R\<^sup>*\<^sup>* s0' s\<rbrakk> \<Longrightarrow>
    wf (step_measuref_rel_from A R s)"
  apply(cut_tac wf_measure[where f="measuref s"])
  apply(erule wf_subset)
  apply(fastforce simp: measure_def inv_image_def step_measuref_rel_from_def rel_terminate_def)
  done

lemma system_Step_one:
  "(x, s') \<in> system.Step A a \<Longrightarrow> (x, s') \<in> Run (system.Step A) [a]"
  apply simp
  done

definition inv_holds
  :: "('a,'b,'j) data_type \<Rightarrow> 'a set \<Rightarrow> bool" (infix "[>" 60)
where
  "D [> I \<equiv> (\<forall>j. Step D j `` I \<subseteq> I)"

lemma inv_holdsI:
  "\<lbrakk> \<forall>j. Step D j `` I \<subseteq> I \<rbrakk> \<Longrightarrow> D [> I"
  by (simp add: inv_holds_def)

lemma inv_holds_conjI:
  "D [> P \<Longrightarrow> D [> Q \<Longrightarrow> D [> P \<inter> Q"
  by (simp add: inv_holds_def) blast

lemma inv_holds_steps:
  assumes I:"A [> I"
  assumes start_I: "B \<subseteq> I"
  shows "steps (Simulation.Step A) B as \<subseteq> I"
  apply clarsimp
  apply (induct as rule: rev_induct)
   apply (simp add: steps_def)
   apply (rule set_mp)
   apply (rule start_I)
   apply simp
  apply (simp add: steps_def)
  apply (erule ImageE)
  apply (drule_tac x=xb in meta_spec)
  apply simp
  apply (rule set_mp)
   apply (rule I[simplified inv_holds_def,rule_format])
  apply (rule ImageI)
   apply assumption
  apply simp
  done

locale serial_system_weak = system +
  fixes I
  assumes I: "A [> I"
  assumes serial: "\<And>s' a. s' \<in> I \<Longrightarrow> (\<exists>t. (s', t) \<in> data_type.Step A a)"
begin

  lemma step_serial:
     assumes nonempty_start: "B \<noteq> {}"
     assumes invariant_start: "B \<subseteq> I"
     shows
    "steps (Simulation.Step A) B as \<noteq> {}"
    apply (induct as rule: rev_induct)
  apply (simp add: steps_def nonempty_start)
  apply (erule nonemptyE)
  apply (frule set_mp[OF inv_holds_steps[OF I invariant_start]])
  apply (frule_tac a=x in serial)
  apply (elim exE)
  apply (rule_tac x=t in notemptyI)
  apply (fastforce simp: steps_def)
  done

end

lemma sub_big_steps_I_holds:
  "A [> I \<Longrightarrow> s \<in> I \<Longrightarrow> (x, xs) \<in> sub_big_steps A R s \<Longrightarrow> x \<in> I"
  apply (erule sub_big_steps.induct)
   apply simp
  apply (simp add: inv_holds_def)
  apply blast
  done

lemma rel_terminate_terminates:
  assumes ss: "serial_system_weak A I"
  assumes rt: "rel_terminate A s0 R I measuref"
  assumes si: "s \<in> I"
  assumes sR: "\<exists>s0'\<in> Init A s0. R\<^sup>*\<^sup>* s0' s"
  shows "\<forall>js. (x,js) \<in> sub_big_steps A R s \<longrightarrow>
                 (\<exists> as s' a s''. (s',(js@as)) \<in> sub_big_steps A R s \<and>
                                 (s',s'') \<in> data_type.Step A a \<and> R s s'')"
  proof -
  show ?thesis
  apply(induct x rule: wf_induct)
   apply(rule wf_step_measuref_rel_from[OF rt si sR])
  apply clarsimp
  apply (frule sub_big_steps_I_holds[OF ss[THEN serial_system_weak.I] si])
  apply (frule_tac  serial_system_weak.serial[OF ss])
  apply(erule exE, rename_tac s')
  apply(drule_tac x=s' in spec)
  apply(erule impE)
   apply(fastforce simp: step_measuref_rel_from_def)
  apply(case_tac "R s s'")
   apply(rule_tac x="[]" in exI)
   apply(rule_tac x=x in exI)
   apply fastforce
  apply(fastforce intro: sub_big_steps.step)
  done
qed


lemma sub_big_steps_nrefl:
  "(\<And>s. \<not> R s s) \<Longrightarrow> (s,[]) \<in> sub_big_steps A R s"
  apply(blast intro: nil)
  done

lemma big_steps_enabled:
  assumes ss: " serial_system_weak A I"
  assumes rt: "rel_terminate A s0 R I measuref"
  assumes s_I: " s \<in> I"
  assumes nrefl: "(\<And>s. \<not> R s s)"
  shows "\<exists>s0'\<in> Init A s0. R\<^sup>*\<^sup>* s0' s
        \<Longrightarrow> \<exists>x s'. (s, s') \<in> big_steps A R exmap x"
  apply(frule rel_terminate_terminates[OF ss rt s_I])
  apply(drule_tac x="[]" in spec)
  apply(erule impE[OF _ sub_big_steps_nrefl])
   apply(rule nrefl)
  apply(fastforce intro: cstep)
  done

text \<open>
  We assume here that there is only one event that can ever occur. This
  is overly restrictive in general, but should be fine for the seL4
  automata (which shouldn't need multiple event labels since it should only
  ever be able to perform one event in each state).
\<close>
lemma Step_system_to_enabled_system:
  assumes single_event: "(\<forall>(x::'b) (y::'b). x = y)"
  assumes st: "Step_system A s0"
  assumes en: "\<And>s. system.reachable A s0 s \<Longrightarrow> \<exists>(x::'b) s'. (s,s') \<in> system.Step A x"
  shows "enabled_system A s0"
  apply(clarsimp simp: enabled_system_def)
  proof -
  fix s  js jsa
  assume a: "s \<in> execution A s0 js"
  show "\<exists> s'. s' \<in> execution A s jsa"
    proof -
    have er: "\<And> as. execution A s as = {s'. (s,s') \<in> Run (system.Step A) as}"
      apply(rule Step_system.execution_Run[OF st])
      using a apply(fastforce simp: system.reachable_def)
      done
    show ?thesis
      apply(induct jsa rule: rev_induct)
       apply(simp add: er)
      apply(clarsimp simp: er)
      apply(cut_tac s=s' in en)
       apply(rule Step_system.reachable_execution[OF st])
        using a apply(fastforce simp: system.reachable_def)
       apply(simp add: er)
      apply clarify
      apply(rename_tac b s'a)
      apply(rule_tac x=s'a in exI)
      apply(rule Run_trans, assumption)
      apply(rule system_Step_one)
      apply(cut_tac x=b and xa=x in single_event[rule_format], simp)
      done
    qed
  qed

lemma steps_subset:
  "A \<subseteq> B \<Longrightarrow> steps steps1 A as \<subseteq> steps steps1 B as"
  apply (simp add: steps_def Image_def)
  apply (induct as rule: rev_induct)
   apply simp
  apply force
  done

locale Init_Fin_serial_weak = serial_system_weak +
     assumes Init_Fin: "\<And>s'. s' \<in> I \<Longrightarrow> s' \<in> Init A (Fin A s')"
     assumes s0_I: "Init A s0 \<subseteq> I"
begin

lemma enabled:
  "enabled_system A s0"
  supply image_cong_simp [cong del]
  supply ex_image_cong_iff [simp del]
  apply (clarsimp simp: enabled_system_def)
  apply (rename_tac jsa, induct_tac jsa rule: rev_induct)
  apply (clarsimp simp: execution_def steps_def)
   apply (fold steps_def)
    apply (rule_tac x="Fin A x" in exI)
   apply (rule imageI)
   apply (rule Init_Fin)
    apply (rule set_mp)
    apply (rule inv_holds_steps[OF I])
    apply (rule s0_I)
   apply simp
  apply (clarsimp simp: execution_def steps_def)
  apply (fold steps_def)
  apply (subgoal_tac "steps (data_type.Step A) (Init A (Fin A xa)) xs \<inter> I \<noteq> {}")
   apply (erule nonemptyE)
   apply clarsimp
   apply (drule_tac a=x in serial)
   apply clarsimp
   apply (rule_tac x="Fin A t" in exI)
   apply (rule imageI)
   apply (rule ImageI)
    apply assumption
   apply assumption
  apply (cut_tac inv_holds_steps[OF I s0_I])
  apply (drule(1) subsetD)
  apply (cut_tac B="{xa}" and as=xs in inv_holds_steps[OF I])
   apply simp
  apply (cut_tac B="{xa}" and as=xs in step_serial)
    apply simp+
  apply (cut_tac A="{xa}" and B="Init A (Fin A xa)" in steps_subset)
   apply (simp add: Init_Fin)
  apply force
  done

end

lemma invariant_holds_steps:
  assumes I:"A \<Turnstile> I"
  assumes start_I: "B \<subseteq> I"
  shows "steps (Simulation.Step A) B as \<subseteq> I"
  apply clarsimp
  apply (induct as rule: rev_induct)
   apply (simp add: steps_def)
   apply (rule set_mp)
   apply (rule start_I)
   apply simp
  apply (simp add: steps_def)
  apply (erule ImageE)
  apply (drule_tac x=xb in meta_spec)
  apply simp
  apply (rule set_mp)
   apply (rule I[simplified invariant_holds_def, THEN conjunct2,rule_format])
  apply (rule ImageI)
   apply assumption
  apply simp
  done


locale serial_system = system +
  fixes I
  assumes I: "A \<Turnstile> I"
  assumes serial: "\<And>s' a. s' \<in> I \<Longrightarrow> (\<exists>t. (s', t) \<in> data_type.Step A a)"
begin

  lemma step_serial:
     assumes nonempty_start: "B \<noteq> {}"
     assumes invariant_start: "B \<subseteq> I"
     shows
    "steps (Simulation.Step A) B as \<noteq> {}"
    apply (induct as rule: rev_induct)
  apply (simp add: steps_def nonempty_start)
  apply (erule nonemptyE)
  apply (frule set_mp[OF invariant_holds_steps[OF I invariant_start]])
  apply (frule_tac a=x in serial)
  apply (elim exE)
  apply (rule_tac x=t in notemptyI)
  apply (fastforce simp: steps_def)
  done

lemma fw_sim_serial:
  assumes refines: "LI B A R (I_b \<times> I_a)"
  assumes B_I_b: "B \<Turnstile> I_b'"
  (*assumes A_I_a: "A \<Turnstile> I_a"*)
  assumes A_I_as: "I \<subseteq> I_a"
  assumes B_I_bs': "I_b' \<subseteq> I_b"
  assumes constrained_B: "\<And>s. s \<in> I_b' \<Longrightarrow> \<exists>s'. s' \<in> I \<and> (s,s') \<in> R"
  shows
  "serial_system B I_b'"
  apply unfold_locales
     apply (rule B_I_b)
  apply (insert refines)
  apply (clarsimp simp: LI_def)
  apply (drule_tac x=a in spec)
  apply (frule_tac s=s' in constrained_B)
  apply clarsimp
  apply (frule_tac a=a in serial)
  apply (clarsimp simp: rel_semi_def)
  apply (cut_tac B_I_bs' A_I_as)
  apply blast
  done

end



locale Init_Fin_serial = serial_system +
     assumes Init_Fin: "\<And>s'. s' \<in> I \<Longrightarrow> s' \<in> Init A (Fin A s')"
     assumes s0_I: "Init A s0 \<subseteq> I"
begin

lemma enabled:
  "enabled_system A s0"
  supply image_cong_simp [cong del]
  supply ex_image_cong_iff [simp del]
  apply (clarsimp simp: enabled_system_def)
  apply (induct_tac jsa  rule: rev_induct)
   apply (clarsimp simp: execution_def steps_def)
   apply (fold steps_def)
   apply (rule_tac x="Fin A x" in exI)
   apply (rule imageI)
   apply (rule Init_Fin)
   apply (rule set_mp)
    apply (rule invariant_holds_steps[OF I])
    apply (rule s0_I)
   apply simp
  apply (clarsimp simp: execution_def steps_def)
  apply (fold steps_def)
  apply (subgoal_tac "xb \<in> I")
   apply (drule_tac a=x in serial)
   apply clarsimp
   apply (rule_tac x="Fin A t" in exI)
   apply (rule imageI)
   apply (rule ImageI)
    apply assumption
   apply assumption
  apply (rule set_mp)
   apply (rule invariant_holds_steps[OF I])
   prefer 2
   apply assumption
  apply (rule I[simplified invariant_holds_def, THEN conjunct1,rule_format])
  done

end


sublocale Init_Fin_serial \<subseteq> enabled_system
  apply (rule enabled)
  done

sublocale Init_Fin_serial \<subseteq> Init_Fin_serial_weak
  apply (unfold_locales)
     using I
     apply (simp add: inv_holds_def invariant_holds_def)
    apply (erule serial)
   apply (erule Init_Fin)
  apply (rule s0_I)
  done

lemma (in Init_Fin_serial) serial_to_weak:
  "Init_Fin_serial_weak A s0 I"
  by intro_locales

definition inv_from_rel :: "('a, 'b, 'j) data_type \<Rightarrow> 'b \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set" where
  "inv_from_rel A s0 R \<equiv> {s. \<exists>s0'\<in> Init A s0. R\<^sup>*\<^sup>* s0' s}"

lemma big_step_adt_R_tranclp_inv:
  "(big_step_adt C R exmap) [> inv_from_rel C s0 R"
  apply (rule inv_holdsI)
  apply (clarsimp simp: big_step_adt_def inv_from_rel_def Fin_trancl_def)
  apply (rule_tac x="s0'" in bexI)
   apply (force elim: big_steps.cases)
  apply simp
  done

lemma  big_steps_I_holds:
  "\<lbrakk>(xa, x) \<in> big_steps A R exmap j; xa \<in> I; A [> I\<rbrakk>
       \<Longrightarrow> x \<in> I"
  apply (erule big_stepsE)
  apply (frule sub_big_steps_I_holds, assumption+)
  apply (simp add: inv_holds_def)
  apply blast
  done

lemma  big_step_adt_inv_holds:
  "A [> I \<Longrightarrow> big_step_adt A R exmap [> I"
  apply (simp add: big_step_adt_def inv_holds_def)
  apply clarsimp
  apply (rule big_steps_I_holds, assumption+)
  apply (simp add: inv_holds_def)
  done

lemma big_step_adt_Init_Fin_serial_weak:
  assumes single_event: "(\<forall>(x::'b) (y::'b). x = y)"
  assumes nrefl: "(\<And>s. \<not> R s s)"
  assumes ifsw: "Init_Fin_serial_weak A s0 I"
  assumes rt: "rel_terminate A s0 R I measuref"
  assumes J_def: "J = inv_from_rel A s0 R \<inter> I"
  shows "Init_Fin_serial_weak (big_step_adt A R (exmap::('a list \<Rightarrow> 'b))) s0 J"
  using ifsw
  apply (unfold_locales)
     apply (simp add: J_def)
     apply (rule inv_holds_conjI)
      apply (rule big_step_adt_R_tranclp_inv)
     apply (rule big_step_adt_inv_holds)
     apply (simp add: Init_Fin_serial_weak_def serial_system_weak.I)
    apply (simp add: big_step_adt_def J_def inv_from_rel_def)
    apply (elim conjE exE)
    apply (cut_tac s=s' and I=I and exmap=exmap in big_steps_enabled)
         apply (force simp: Init_Fin_serial_weak_def)
        apply (rule rt)
       apply assumption
      apply (simp add: nrefl)
     apply simp
    apply clarsimp
    apply (cut_tac x=x and xa=a in single_event[rule_format])
    apply blast
   apply (simp add: J_def big_step_adt_def Init_Fin_serial_weak.Init_Fin)
  apply (simp add: big_step_adt_def Init_Fin_serial_weak.s0_I J_def inv_from_rel_def, force)
  done

lemma big_step_adt_enabled_system:
  assumes single_event: "(\<forall>(x::'b) (y::'b). x = y)"
  assumes nrefl: "(\<And>s. \<not> R s s)"
  assumes ifsw: "Init_Fin_serial_weak A s0 I"
  assumes rt: "rel_terminate A s0 R I measuref"
  shows "enabled_system (big_step_adt A R (exmap::('a list \<Rightarrow> 'b))) s0"
  apply (cut_tac big_step_adt_Init_Fin_serial_weak[OF single_event nrefl ifsw rt])
   apply (erule Init_Fin_serial_weak.enabled)
  apply simp
  done

(* For reachability in big_step_adt we need to consider internal reachability. *)
definition reachable_i
where
  "reachable_i A s0 s \<equiv> \<exists>js. (s0, s) \<in> Run (data_type.Step A) js"

lemma sub_big_steps_Run:
  "(t,evlist) \<in> sub_big_steps A R s \<Longrightarrow> (s, t) \<in> Run (Step A) evlist \<and> \<not> R s t"
  apply(induct t evlist rule: sub_big_steps.induct)
   apply simp
  apply clarsimp
  apply (rule Run_trans)
   apply assumption
  apply simp
  done

lemma big_step_adt_reachable_i_states:
  "(s0, s) \<in> Run (data_type.Step (big_step_adt C R exmap)) js \<Longrightarrow>
         \<exists>js. (s0, s) \<in> Run (Step C) js"
  apply(induct js arbitrary: s0)
   apply (rule_tac x="[]" in exI, simp)
  apply (clarsimp simp: big_step_adt_def)
  apply(rename_tac s0 sa)
  apply(erule big_stepsE)
  apply(drule sub_big_steps_Run)
  apply(subgoal_tac "(s0,sa) \<in> Run (data_type.Step C) (as@[aa])")
   apply (blast intro: Run_trans)
  apply(fastforce intro: Run_trans)
  done

lemma reachable_i_big_step_adt:
  "reachable_i (big_step_adt C R exmap) s0 s \<Longrightarrow>
   reachable_i C s0 s"
  apply(clarsimp simp: reachable_i_def)
  apply(blast intro: big_step_adt_reachable_i_states)
  done

lemma steps_eq_Run:
  "(s' \<in> steps (Step A) (Init A s0) js)
     = (\<exists>s0'. s0' \<in> Init A s0 \<and> (s0', s') \<in> Run (Step A) js)"
  apply (rule iffI)
   apply (clarsimp simp: steps_def image_def Image_def)
   apply (induct js arbitrary: s' rule: rev_induct)
    apply simp
   apply (force intro: Run_trans)
  apply (clarsimp simp: steps_def image_def Image_def)
  apply (induct js arbitrary: s' rule: rev_induct)
   apply simp
  apply clarsimp
  apply (drule Run_mid, force)
  done

lemma reachable_reachable_i:
  "system.reachable A s0 s \<Longrightarrow> \<exists>s0' s'. s0' \<in> Init A s0 \<and> Fin A s' = s \<and> reachable_i A s0' s'"
  by (force simp: system.reachable_def reachable_i_def execution_def steps_eq_Run)

lemma reachable_i_reachable:
  "\<lbrakk>reachable_i A s0' s'; s0' \<in> Init A s0; Fin A s' = s\<rbrakk> \<Longrightarrow> system.reachable A s0 s"
  by (force simp: system.reachable_def reachable_i_def execution_def steps_eq_Run)

lemma reachable_big_step_adt:
  "system.reachable (big_step_adt C R exmap) s0 s \<Longrightarrow>
   system.reachable C s0 s"
  by (force dest: reachable_reachable_i intro: reachable_i_reachable reachable_i_big_step_adt
                simp: big_step_adt_def)

lemma big_step_adt_Init_inv_Fin_system:
  "Init_inv_Fin_system A s0 \<Longrightarrow> Init_inv_Fin_system (big_step_adt A R exmap) s0"
  apply (clarsimp simp: Init_inv_Fin_system_def big_step_adt_def)
  apply (erule_tac x=s in allE)
  apply (force intro: reachable_big_step_adt simp: big_step_adt_def)
  done

lemma big_step_adt_Step_system:
  "Init_inv_Fin_system C s0 \<Longrightarrow> Step_system (big_step_adt C R exmap) s0"
  apply(rule Init_Fin_system_Step_system)
  apply(rule Init_inv_Fin_system_Init_Fin_system)
  apply(rule big_step_adt_Init_inv_Fin_system)
  apply simp
  done

lemma big_step_adt_enabled_Step_system:
  assumes single_event: "(\<forall>(x::'b) (y::'b). x = y)"
  assumes nrefl: "(\<And>s. \<not> R s s)"
  assumes ifsw: "Init_Fin_serial_weak A s0 I"
  assumes iifs: "Init_inv_Fin_system A s0"
  assumes rt: "rel_terminate A s0 R I measuref"
  shows "enabled_Step_system (big_step_adt A R (examp::('a list \<Rightarrow> 'b))) s0"
  using assms by (simp add: enabled_Step_system_def big_step_adt_Step_system
                            big_step_adt_enabled_system)

section \<open>ADT_A_if definition and enabledness\<close>

subsection \<open>global_automaton_if definition\<close>

context begin interpretation Arch . (*FIXME: arch_split*)

text \<open>
  We define a bunch of states that the system can be in. The first two
  are when the processor is in user mode, the final four are for when in
  kernel mode.
     - in user mode (a user-level thread is running)
     - in idle mode (the idle thread is running)
     - kernel entry for some event e (kernel entry is occurring)
     - in kernel mode where kernel execution has been pre-empted by interrupt
       arrival
     - in kernel mode where the scheduler is about to execute -- the boolean here
       is ghost state to capture when the schedule event follows interrupt-handling
       (i.e. is True when the previous mode was KernelEntry Interrupt or KernelPreempted)
     - in kernel mode, about to exit to userspace
\<close>
datatype sys_mode = InUserMode | InIdleMode |
                    KernelEntry event | KernelPreempted |
                    KernelSchedule bool | KernelExit

type_synonym 'k global_sys_state = "(user_context \<times> 'k) \<times> sys_mode"

text \<open>
  We take the @{term global_automaton} and split the kernel transitions
  into multiple steps. This is done because, while the entire execution
  from kernel entry to exit is atomic, different parts of it need to be
  considered as being done on behalf of different domains. For instance,
  the part that does kernel entry and then handles the event should happen
  on behalf of the domain of the currently running thread, but the
  part that handles pre-emptions will probably need to purport to happen on
  behalf of the scheduler domain.

  - a transition for kernel entry on event e (kernel entry happens,
    and we handle the event, possibly gettting pre-empted along the way)
  - a transition for handling those pre-emptions
  - a transition for running the scheduler at the end of every kernel event
  - a transition for kernel exit

  TODO: schedule and kernel exit may be able to be put into the same
        transition. It depends on what domain each transition needs to
        purport to run on behalf of

  We also have the user operations possibly give an event, which gives us
  a handle on modelling when user programs request system calls or cause
  other exceptions to occur.
\<close>
definition global_automaton_if
  :: "((user_context \<times> 'k) \<times> irq option \<times> (user_context \<times> 'k)) set
      \<Rightarrow> ((user_context \<times> 'k) \<times> event option \<times> (user_context \<times> 'k)) set
      \<Rightarrow> (event \<Rightarrow> ((user_context \<times> 'k) \<times> bool \<times> (user_context \<times> 'k)) set)
      \<Rightarrow> (((user_context \<times> 'k) \<times> unit \<times> (user_context \<times> 'k)) set)
      \<Rightarrow> (((user_context \<times> 'k) \<times> unit \<times> (user_context \<times> 'k)) set)
      \<Rightarrow> (((user_context \<times> 'k) \<times> sys_mode \<times> (user_context \<times> 'k)) set)
      \<Rightarrow> ('k global_sys_state \<times> 'k global_sys_state) set"
where
  "global_automaton_if get_active_irqf do_user_opf kernel_callf
                       preemptionf schedulef kernel_exitf \<equiv>
  \<comment> \<open>Kernel entry with preemption during event handling
     NOTE: kernel cannot be preempted while servicing an interrupt\<close>
     { ( (s, KernelEntry e),
         (s', KernelPreempted) ) |s s' e. (s, True, s') \<in> kernel_callf e \<and>
                                          e \<noteq> Interrupt} \<union>
  \<comment> \<open>kernel entry without preemption during event handling\<close>
     { ( (s, KernelEntry e),
         (s', KernelSchedule (e = Interrupt)) ) |s s' e. (s, False, s') \<in> kernel_callf e } \<union>
  \<comment> \<open>handle in-kernel preemption\<close>
     { ( (s, KernelPreempted),
         (s', KernelSchedule True) ) |s s'. (s, (), s') \<in> preemptionf } \<union>
  \<comment> \<open>schedule\<close>
     { ( (s, KernelSchedule b),
         (s', KernelExit) ) |s s' b. (s, (), s') \<in> schedulef } \<union>
  \<comment> \<open>kernel exit\<close>
     { ( (s, KernelExit),
         (s', m) ) |s s' m. (s, m, s') \<in> kernel_exitf } \<union>
  \<comment> \<open>User runs, causes exception\<close>
     { ( (s, InUserMode),
         (s', KernelEntry e ) ) |s s_aux s' e.
                                 (s, None, s_aux) \<in> get_active_irqf \<and>
                                 (s_aux, Some e, s') \<in> do_user_opf \<and>
                                 e \<noteq> Interrupt} \<union>
  \<comment> \<open>User runs, no exception happens\<close>
     { ( (s, InUserMode),
         (s', InUserMode) ) |s s_aux s'.
                             (s, None, s_aux) \<in> get_active_irqf \<and>
                             (s_aux, None, s') \<in> do_user_opf} \<union>
  \<comment> \<open>Interrupt while in user mode\<close>
     { ( (s, InUserMode),
         (s', KernelEntry Interrupt) ) |s s' i.
                                        (s, Some i, s') \<in> get_active_irqf} \<union>
  \<comment> \<open>Interrupt while in idle mode\<close>
     { ( (s, InIdleMode),
         (s', KernelEntry Interrupt) ) |s s' i.
                                        (s, Some i, s') \<in> get_active_irqf} \<union>
  \<comment> \<open>No interrupt while in idle mode\<close>
     { ( (s, InIdleMode),
         (s', InIdleMode) ) |s s'. (s, None, s') \<in> get_active_irqf}"

type_synonym user_state_if = "user_context \<times> user_mem \<times> device_state \<times> exclusive_monitors"

text \<open>
  A user transition gives back a possible event that is the next
  event the user wants to perform
\<close>
type_synonym user_transition_if =
  "obj_ref \<Rightarrow> (word32 \<rightharpoonup> word32) \<Rightarrow> (word32 \<Rightarrow> vm_rights) \<Rightarrow> (word32 \<Rightarrow> bool) \<Rightarrow>
   user_state_if \<Rightarrow> (event option \<times> user_state_if) set"

lemma dmo_getExMonitor_wp[wp]:
  "\<lbrace>\<lambda>s. P (exclusive_state (machine_state s)) s\<rbrace>
     do_machine_op getExMonitor
   \<lbrace>P\<rbrace>"
  apply(simp add: do_machine_op_def)
  apply(wp modify_wp | wpc)+
  apply clarsimp
  apply(erule use_valid)
   apply wp
  apply simp
  done

lemma setExMonitor_wp[wp]:
  "\<lbrace>\<lambda>ms. P (ms\<lparr>exclusive_state := es\<rparr>)\<rbrace>
     setExMonitor es
   \<lbrace>\<lambda>_. P\<rbrace>"
  apply(simp add: setExMonitor_def | wp)+
  done

lemma dmo_setExMonitor_wp[wp]:
  "\<lbrace>\<lambda>s. P (s\<lparr>machine_state := machine_state s \<lparr>exclusive_state := es\<rparr>\<rparr>)\<rbrace>
     do_machine_op (setExMonitor es)
   \<lbrace>\<lambda>_. P\<rbrace>"
  apply(simp add: do_machine_op_def)
  apply(wp modify_wp | wpc)+
  apply clarsimp
  apply(erule use_valid)
   apply wp
  apply simp
  done

lemma valid_state_exclusive_state_update[iff]:
  "valid_state (s\<lparr>machine_state := machine_state s\<lparr>exclusive_state := es\<rparr>\<rparr>) = valid_state s"
  by (simp add: valid_state_def valid_irq_states_def valid_machine_state_def)

lemma cur_tcb_exclusive_state_update[iff]:
  "cur_tcb (s\<lparr>machine_state := machine_state s\<lparr>exclusive_state := es\<rparr>\<rparr>) = cur_tcb s"
  by (simp add: cur_tcb_def)

lemma invs_exclusive_state_update[iff]:
  "invs (s\<lparr>machine_state := machine_state s\<lparr>exclusive_state := es\<rparr>\<rparr>) = invs s"
  by (simp add: invs_def)

subsection \<open>do_user_op_if lemmas\<close>

(* FIXME: clagged from AInvs.do_user_op_invs *)
lemma do_user_op_if_invs:
  "\<lbrace>invs and ct_running\<rbrace>
   do_user_op_if f tc
   \<lbrace>\<lambda>_. invs and ct_running\<rbrace>"
  apply (simp add: do_user_op_if_def split_def)
  apply (wp ct_running_machine_op select_wp device_update_invs | wp (once) dmo_invs | simp)+
  apply (clarsimp simp: user_mem_def user_memory_update_def simpler_modify_def
                    restrict_map_def invs_def cur_tcb_def ptable_rights_s_def
                    ptable_lift_s_def)
  apply (frule ptable_rights_imp_frame)
    apply fastforce
   apply simp
  apply (clarsimp simp: valid_state_def device_frame_in_device_region)
  done

crunch domain_sep_inv[wp]: do_user_op_if "domain_sep_inv irqs st"
  (ignore: user_memory_update wp: select_wp)

crunch valid_sched[wp]: do_user_op_if "valid_sched"
  (ignore: user_memory_update wp: select_wp)

lemma no_irq_user_memory_update[simp]:
  "no_irq (user_memory_update a)"
  apply(wpsimp simp: no_irq_def user_memory_update_def)
  done

lemma no_irq_device_memory_update[simp]:
  "no_irq (device_memory_update a)"
  apply(wpsimp simp: no_irq_def device_memory_update_def)
  done

crunch irq_masks[wp]: do_user_op_if "\<lambda>s. P (irq_masks_of_state s)"
  (ignore: user_memory_update wp: select_wp dmo_wp no_irq)

crunch valid_list[wp]: do_user_op_if "valid_list"
  (ignore: user_memory_update wp: select_wp)

lemma do_user_op_if_scheduler_action[wp]:
  "\<lbrace>(\<lambda>s. P (scheduler_action s))\<rbrace>
   do_user_op_if f tc
   \<lbrace>\<lambda>_ s. P (scheduler_action s)\<rbrace>"
  by (simp add: do_user_op_if_def | wp select_wp | wpc)+

lemma do_user_op_silc_inv[wp]:
  "\<lbrace>silc_inv aag st\<rbrace> do_user_op_if f tc \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  apply (simp add: do_user_op_if_def)
  apply (wp select_wp | wpc | simp)+
  done

lemma do_user_op_pas_refined[wp]:
  "\<lbrace>pas_refined aag\<rbrace> do_user_op_if f tc \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (simp add: do_user_op_if_def)
  apply (wp select_wp | wpc | simp)+
  done

crunches do_user_op_if
  for cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  and idle_thread[wp]: "\<lambda>s. P (idle_thread s)"
  and domain_fields[wp]: "domain_fields P"
  (wp: select_wp ignore: user_memory_update)

lemma do_use_op_guarded_pas_domain[wp]:
  "\<lbrace>guarded_pas_domain aag\<rbrace> do_user_op_if f tc \<lbrace>\<lambda>_. guarded_pas_domain aag\<rbrace>"
  by (rule guarded_pas_domain_lift; wp)

definition do_user_op_A_if
  :: "user_transition_if
      \<Rightarrow> ((user_context \<times> det_state) \<times> event option \<times> (user_context \<times> det_state)) set"
where
  "do_user_op_A_if uop \<equiv>
       {(s,e,(tc,s'))| s e tc s'. ((e,tc),s') \<in> fst (split (do_user_op_if uop) s)}"

subsection \<open>kernel_entry_if\<close>

text \<open>
  Enter the kernel, and handle the event. Leave the user context
  unchanged; although it shouldn't matter really what its value is
  while we are still in kernel mode.
\<close>
definition kernel_entry_if
  :: "event \<Rightarrow> user_context \<Rightarrow> (((unit + unit) \<times> user_context),det_ext) s_monad"
where
  "kernel_entry_if e tc \<equiv> do
    t \<leftarrow> gets cur_thread;
    thread_set (\<lambda>tcb. tcb \<lparr> tcb_arch := arch_tcb_context_set tc (tcb_arch tcb)\<rparr>) t;
    r \<leftarrow> handle_event e;
    return (r,tc)
  od"

crunch cur_domain[wp]: kernel_entry_if "\<lambda>s. P (cur_domain s)"
crunch idle_thread[wp]: kernel_entry_if "\<lambda>s::det_state. P (idle_thread s)"
crunch cur_thread [wp]: kernel_entry_if "\<lambda>s. P (cur_thread s)"

lemma thread_set_tcb_context_update_ct_active[wp]:
  "\<lbrace>ct_active\<rbrace>
   thread_set (tcb_arch_update (arch_tcb_context_set f)) t
   \<lbrace>\<lambda>rv. ct_active\<rbrace>"
  apply(simp add: thread_set_def ct_in_state_def | wp set_object_wp)+
  apply(clarsimp simp: st_tcb_at_def obj_at_def get_tcb_def)
  done

lemma thread_set_tcb_context_update_not_ct_active[wp]:
  "\<lbrace>\<lambda>s. \<not> ct_active s\<rbrace>
   thread_set (tcb_arch_update (arch_tcb_context_set f)) t
   \<lbrace>\<lambda>r s. \<not> ct_active s\<rbrace>"
  apply(simp add: thread_set_def ct_in_state_def | wp set_object_wp)+
  apply(clarsimp simp: st_tcb_at_def obj_at_def get_tcb_def
                split: kernel_object.splits option.splits)
  done

(*FIXME: Move to FinalCaps*)
lemma thread_set_silc_inv_trivial:
  "(\<And>tcb. \<forall>(getF, v)\<in>ran tcb_cap_cases. getF (F tcb) = getF tcb) \<Longrightarrow>
   \<lbrace>silc_inv aag st\<rbrace>
   thread_set F word
   \<lbrace>\<lambda>xa. silc_inv aag st\<rbrace>"
  unfolding thread_set_def
  apply(rule silc_inv_pres)
   apply(wp set_object_wp)
   apply (simp split: kernel_object.splits)
   apply(rule impI | simp)+
   apply(fastforce simp: silc_inv_def dest: get_tcb_SomeD simp: obj_at_def is_cap_table_def)
  apply(wp set_object_wp | simp)+
  apply(case_tac "word = fst slot")
   apply(clarsimp split: kernel_object.splits)
   apply(erule notE)
   apply(erule cte_wp_atE)
    apply(fastforce simp: obj_at_def)
   apply(drule get_tcb_SomeD)
   apply(rule cte_wp_at_tcbI)
     apply(simp)
    apply assumption
   apply (clarsimp simp: tcb_cap_cases_def tcb_registers_caps_merge_def split: if_splits)
  apply(fastforce elim: cte_wp_atE intro: cte_wp_at_cteI cte_wp_at_tcbI)
  done

lemma kernel_entry_if_invs:
  "\<lbrace>invs and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_active s)\<rbrace>
   kernel_entry_if e tc
   \<lbrace>\<lambda>_. invs\<rbrace>"
  unfolding kernel_entry_if_def
  apply (wpsimp wp: thread_set_invs_trivial static_imp_wp
              simp: arch_tcb_update_aux2 ran_tcb_cap_cases)+
  done

lemma idle_equiv_as_globals_equiv:
  "arm_global_pd (arch_state s) \<noteq> idle_thread s \<Longrightarrow>
   idle_equiv st s =
              globals_equiv (st\<lparr>arch_state := arch_state s, machine_state := machine_state s,
                                kheap:= (kheap st)(arm_global_pd (arch_state s) :=
                                                   kheap s (arm_global_pd (arch_state s))),
                                cur_thread := cur_thread s\<rparr>) s"
  by (clarsimp simp: idle_equiv_def globals_equiv_def tcb_at_def2)



lemma idle_globals_lift:
  assumes g: "\<And>st. \<lbrace>globals_equiv st and P\<rbrace> f \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  assumes i: "\<And>s. P s \<Longrightarrow> arm_global_pd (arch_state s) \<noteq> idle_thread s"
  shows "\<lbrace>idle_equiv st and P\<rbrace> f \<lbrace>\<lambda>_. idle_equiv st\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (subgoal_tac "arm_global_pd (arch_state s) \<noteq> idle_thread s")
   apply (subst (asm) idle_equiv_as_globals_equiv,simp+)
   apply (frule use_valid[OF _ g])
    apply simp+
   apply (clarsimp simp: idle_equiv_def globals_equiv_def tcb_at_def2)
   apply (erule i)
  done

lemma idle_equiv_as_globals_equiv_scheduler:
  "arm_global_pd (arch_state s) \<noteq> idle_thread s \<Longrightarrow>
   idle_equiv st s =
       globals_equiv_scheduler (st\<lparr>arch_state := arch_state s, machine_state := machine_state s,
                                   kheap:= (kheap st)(arm_global_pd (arch_state s) :=
                                                     kheap s (arm_global_pd (arch_state s)))\<rparr>) s"
  by (clarsimp simp: idle_equiv_def globals_equiv_scheduler_def tcb_at_def2)



lemma idle_globals_lift_scheduler:
  assumes g: "\<And>st. \<lbrace>globals_equiv_scheduler st and P\<rbrace> f \<lbrace>\<lambda>_. globals_equiv_scheduler st\<rbrace>"
  assumes i: "\<And>s. P s \<Longrightarrow> arm_global_pd (arch_state s) \<noteq> idle_thread s"
  shows "\<lbrace>idle_equiv st and P\<rbrace> f \<lbrace>\<lambda>_. idle_equiv st\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (subgoal_tac "arm_global_pd (arch_state s) \<noteq> idle_thread s")
   apply (subst (asm) idle_equiv_as_globals_equiv_scheduler,simp+)
   apply (frule use_valid[OF _ g])
    apply simp+
   apply (clarsimp simp: idle_equiv_def globals_equiv_scheduler_def tcb_at_def2)
   apply (erule i)
  done

lemma invs_pd_not_idle_thread[intro]:
  "invs s \<Longrightarrow> arm_global_pd (arch_state s) \<noteq> idle_thread s"
  by (fastforce simp: invs_def valid_state_def valid_global_objs_def
                      obj_at_def valid_idle_def pred_tcb_at_def empty_table_def)


lemma kernel_entry_if_globals_equiv:
  "\<lbrace>invs and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_active s) and globals_equiv st
    and (\<lambda>s. ct_idle s \<longrightarrow> tc = idle_context s) \<rbrace>
    kernel_entry_if e tc
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  apply (simp add: kernel_entry_if_def)
  apply (wp static_imp_wp
            handle_event_globals_equiv
            thread_set_invs_trivial
            thread_set_context_globals_equiv
        | simp add: ran_tcb_cap_cases arch_tcb_update_aux2)+
  apply (clarsimp simp: cur_thread_idle)
  done

lemma kernel_entry_if_idle_equiv:
  "\<lbrace>invs and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_active s) and idle_equiv st
       and (\<lambda>s. ct_idle s \<longrightarrow> tc = idle_context s) \<rbrace>
     kernel_entry_if e tc
   \<lbrace>\<lambda>_. idle_equiv st\<rbrace>"
  apply (rule hoare_pre)
   apply (rule idle_globals_lift)
    apply (wp kernel_entry_if_globals_equiv)
    apply force
   apply (fastforce intro!: invs_pd_not_idle_thread)+
  done

lemma thread_set_tcb_context_update_neg_cte_wp_at[wp]:
  "\<lbrace>\<lambda>s. \<not> cte_wp_at P slot s\<rbrace>
     thread_set (tcb_arch_update (arcb_tcb_context_set blah)) param_a
   \<lbrace>\<lambda>_ s. \<not> cte_wp_at P slot s\<rbrace>"
  apply(simp add: thread_set_def)
  apply(wp set_object_wp get_object_wp | simp)+
  apply(case_tac "param_a = fst slot")
   apply(clarsimp split: kernel_object.splits)
   apply(erule notE)
   apply(erule cte_wp_atE)
    apply(fastforce simp: obj_at_def)
   apply(drule get_tcb_SomeD)
   apply(rule cte_wp_at_tcbI)
     apply(simp)
    apply assumption
   apply (fastforce simp: tcb_cap_cases_def split: if_splits)
  apply(fastforce elim: cte_wp_atE intro: cte_wp_at_cteI cte_wp_at_tcbI)
  done

lemma thread_set_tcb_context_update_domain_sep_inv[wp]:
  "\<lbrace>domain_sep_inv irqs st\<rbrace>
     thread_set (tcb_arch_update (arch_tcb_context_set f)) t
   \<lbrace>\<lambda>rv. domain_sep_inv irqs st\<rbrace>"
  by(wp domain_sep_inv_triv)

lemma kernel_entry_silc_inv[wp]:
  "\<lbrace>silc_inv aag st and einvs and simple_sched_action and
       (\<lambda>s. ev \<noteq> Interrupt \<longrightarrow> ct_active s) and
       pas_refined aag and
       (\<lambda>s. ct_active s \<longrightarrow> is_subject aag (cur_thread s)) and
       domain_sep_inv (pasMaySendIrqs aag) st'\<rbrace>
     kernel_entry_if ev tc
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  unfolding kernel_entry_if_def
  apply (wpsimp simp: ran_tcb_cap_cases arch_tcb_update_aux2
                  wp: static_imp_wp handle_event_silc_inv thread_set_silc_inv_trivial
                      thread_set_invs_trivial thread_set_not_state_valid_sched
                      thread_set_pas_refined
        | wp (once) hoare_vcg_imp_lift)+
  by force

lemma kernel_entry_pas_refined[wp]:
  "\<lbrace>pas_refined aag and guarded_pas_domain aag and
       domain_sep_inv (pasMaySendIrqs aag) st and einvs and
       schact_is_rct and
       (\<lambda>s. ct_active s \<longrightarrow> is_subject aag (cur_thread s)) and
       (\<lambda>s. ev \<noteq> Interrupt \<longrightarrow> ct_active s)\<rbrace>
     kernel_entry_if ev tc
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  unfolding kernel_entry_if_def
  apply (wpsimp simp: ran_tcb_cap_cases schact_is_rct_def arch_tcb_update_aux2 tcb_arch_ref_def
                  wp: static_imp_wp handle_event_pas_refined
             thread_set_pas_refined guarded_pas_domain_lift
             thread_set_invs_trivial thread_set_not_state_valid_sched)+
  by force

lemma kernel_entry_if_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and einvs and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_active s)\<rbrace>
     kernel_entry_if e tc
   \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  unfolding kernel_entry_if_def
  apply( wpsimp simp: ran_tcb_cap_cases arch_tcb_update_aux2 tcb_arch_ref_def
          wp: handle_event_domain_sep_inv static_imp_wp
            thread_set_invs_trivial thread_set_not_state_valid_sched)+
  done

lemma kernel_entry_if_guarded_pas_domain:
  "\<lbrace>guarded_pas_domain aag\<rbrace>
     kernel_entry_if e tc
   \<lbrace>\<lambda>_. guarded_pas_domain aag\<rbrace>"
  apply (simp add: kernel_entry_if_def)
  apply (wp guarded_pas_domain_lift)
  done

lemma kernel_entry_if_valid_sched:
  "\<lbrace>valid_sched and invs and (ct_active or ct_idle) and
       (\<lambda>s. (e \<noteq> Interrupt \<longrightarrow> ct_active s) \<and> scheduler_action s = resume_cur_thread)\<rbrace>
     kernel_entry_if e tc
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply(wpsimp simp: kernel_entry_if_def ran_tcb_cap_cases arch_tcb_update_aux2 tcb_arch_ref_def
         wp: handle_event_valid_sched thread_set_invs_trivial hoare_vcg_disj_lift
             thread_set_no_change_tcb_state ct_in_state_thread_state_lift
             thread_set_not_state_valid_sched static_imp_wp)+
  done

lemma kernel_entry_if_irq_masks:
  "\<lbrace>(\<lambda>s. P (irq_masks_of_state s)) and domain_sep_inv False st and invs\<rbrace>
     kernel_entry_if e tc
   \<lbrace>\<lambda>_ s. P (irq_masks_of_state s)\<rbrace>"
  apply( simp add: kernel_entry_if_def ran_tcb_cap_cases arch_tcb_update_aux2 tcb_arch_ref_def
       | wp handle_event_irq_masks thread_set_invs_trivial)+
  by fastforce

crunch valid_list[wp]: kernel_entry_if "valid_list"

definition kernel_call_A_if
  :: "event \<Rightarrow> ((user_context \<times> det_state) \<times> bool \<times> (user_context \<times> det_state)) set"
where
  "kernel_call_A_if e \<equiv>
      {(s, b, (tc,s'))|s b tc s' r. ((r,tc),s') \<in> fst (split (kernel_entry_if e) s) \<and>
                   b = (case r of Inl _ \<Rightarrow> True | Inr _ \<Rightarrow> False)}"

subsection \<open>handle_preemption_if\<close>

text \<open>
  Since this executes entirely in kernel mode, leave the
  user context unchanged
\<close>
definition handle_preemption_if :: "user_context \<Rightarrow> (user_context,det_ext) s_monad"
where
  "handle_preemption_if tc \<equiv> do
     irq \<leftarrow> do_machine_op (getActiveIRQ False);
     when (irq \<noteq> None) $ handle_interrupt (the irq);
     return tc
   od"


lemma handle_preemption_if_invs:
  "\<lbrace>invs\<rbrace>
     handle_preemption_if tc
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply(simp add: handle_preemption_if_def | wp)+
  done

lemma handle_preemption_if_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st\<rbrace>
     handle_preemption_if e
   \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  apply(simp add: handle_preemption_if_def | wp)+
  done

lemma handle_preemption_if_silc_inv[wp]:
  "\<lbrace>silc_inv aag st\<rbrace> handle_preemption_if tc \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  apply (simp add: handle_preemption_if_def)
  apply (wp handle_interrupt_silc_inv do_machine_op_silc_inv | simp)+
  done

lemma handle_preemption_if_pas_refined[wp]:
  "\<lbrace>pas_refined aag\<rbrace> handle_preemption_if tc \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (simp add: handle_preemption_if_def)
  apply (wp handle_interrupt_pas_refined | simp)+
  done

crunch cur_thread[wp]: handle_preemption_if "\<lambda>s. P (cur_thread s)"
crunch cur_domain[wp]: handle_preemption_if " \<lambda>s. P (cur_domain s)"
crunch idle_thread[wp]: handle_preemption_if "\<lambda>s::det_state. P (idle_thread s)"

lemma handle_preemption_if_guarded_pas_domain[wp]:
  "\<lbrace>guarded_pas_domain aag\<rbrace> handle_preemption_if tc \<lbrace>\<lambda>_. guarded_pas_domain aag\<rbrace>"
  by (rule guarded_pas_domain_lift; wp)

lemma handle_preemption_if_valid_sched[wp]:
  "\<lbrace>valid_sched and invs and (\<lambda>s. irq \<in> non_kernel_IRQs \<longrightarrow> scheduler_act_sane s \<and> ct_not_queued s)\<rbrace>
      handle_preemption_if irq \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (wpsimp simp: handle_preemption_if_def non_kernel_IRQs_def cong: if_cong)
   apply (wpsimp wp: hoare_drop_imp hoare_vcg_if_lift2)+
  done

context begin interpretation Arch . (*FIXME: arch_split*)
lemma handle_preemption_if_irq_masks:
  "\<lbrace>(\<lambda>s. P (irq_masks_of_state s)) and domain_sep_inv False st\<rbrace>
   handle_preemption_if tc
   \<lbrace>\<lambda>_ s. P (irq_masks_of_state s)\<rbrace>"
  apply(simp add: handle_preemption_if_def | wp handle_interrupt_irq_masks[where st=st])+
  apply(rule_tac Q="\<lambda>rv s. P (irq_masks_of_state s) \<and> domain_sep_inv False st s \<and>
                    (\<forall>x. rv = Some x \<longrightarrow> x \<le> maxIRQ) " in hoare_strengthen_post)
    by(wp | simp)+
end

crunch valid_list[wp]: handle_preemption_if "valid_list"
  (ignore: getActiveIRQ)

definition kernel_handle_preemption_if
  :: "((user_context \<times> det_state) \<times> unit \<times> (user_context \<times> det_state)) set"
where
  "kernel_handle_preemption_if \<equiv>
      {(s, u, s'). s' \<in> fst (split handle_preemption_if s)}"

subsection \<open>schedule_if\<close>

text \<open>
  Since this executes entirely in kernel mode, leave the
  user context unchanged
\<close>
definition schedule_if
  :: "user_context \<Rightarrow> (user_context,det_ext) s_monad"
where
  "schedule_if tc \<equiv> do
     schedule;
     activate_thread;
     return tc
   od"

lemma schedule_if_invs[wp]:
  "\<lbrace>invs\<rbrace>
     schedule_if tc
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply(simp add: schedule_if_def | wp)+
   apply(rule hoare_strengthen_post[OF activate_invs] | simp | wp)+
  done

crunch pas_refined[wp]: schedule_if "pas_refined aag"

crunch silc_inv[wp]: schedule_if "silc_inv aag st"

crunch domain_sep_inv[wp]: schedule_if "\<lambda>s::det_state. domain_sep_inv irqs st s"

crunch cur_domain[wp]: activate_thread "\<lambda>s. P (cur_domain s)"
crunch idle_thread[wp]: activate_thread "\<lambda>s. P (idle_thread s)"

lemma activate_thread_guarded_pas_domain[wp]:
  "\<lbrace>guarded_pas_domain aag\<rbrace> activate_thread \<lbrace>\<lambda>_. guarded_pas_domain aag\<rbrace>"
  by (rule guarded_pas_domain_lift; wp activate_thread_cur_thread)

lemma guarded_pas_domain_arch_state_update[simp]:
  "guarded_pas_domain aag (s\<lparr>arch_state := x\<rparr>) = guarded_pas_domain aag s"
  apply (simp add: guarded_pas_domain_def)
  done

lemma switch_to_thread_guarded_pas_domain:
  "\<lbrace>\<lambda>s. pasObjectAbs aag t \<in> pasDomainAbs aag (cur_domain s)\<rbrace>
     switch_to_thread t
   \<lbrace>\<lambda>_. guarded_pas_domain aag\<rbrace>"
  apply (simp add: switch_to_thread_def)
  apply (wp modify_wp hoare_drop_imps| simp add: guarded_pas_domain_def)+
  done

lemma guarded_pas_domain_machine_state_update[simp]:
  "guarded_pas_domain aag (s\<lparr>machine_state := x\<rparr>) = guarded_pas_domain aag s"
  apply (simp add: guarded_pas_domain_def)
  done

(* FIXME: Why was the [wp] attribute clobbered by interpretation of the Arch locale? *)
declare storeWord_irq_masks[wp]

lemma switch_to_idle_thread_guarded_pas_domain[wp]:
  "\<lbrace>\<top>\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>xb. guarded_pas_domain aag\<rbrace>"
  apply (simp add: switch_to_idle_thread_def arch_switch_to_idle_thread_def bind_assoc
                   double_gets_drop_regets)
  apply (wp modify_wp dmo_wp hoare_vcg_imp_lift | wp (once) | simp add: guarded_pas_domain_def)+
  done

lemma choose_thread_guarded_pas_domain:
  "\<lbrace>pas_refined aag and valid_queues\<rbrace> choose_thread \<lbrace>\<lambda>xb. guarded_pas_domain aag\<rbrace>"
  apply (simp add: choose_thread_def guarded_switch_to_def
        | wp switch_to_thread_respects switch_to_idle_thread_respects gts_wp
             switch_to_thread_guarded_pas_domain)+
  apply (clarsimp simp: pas_refined_def)
  apply (clarsimp simp: tcb_domain_map_wellformed_aux_def)
  apply (erule_tac x="(hd (max_non_empty_queue (ready_queues s (cur_domain s))), cur_domain s)"
                   in ballE)
   apply simp
  apply (clarsimp simp: valid_queues_def is_etcb_at_def)
  apply (erule_tac x="cur_domain s" in allE)
  apply (erule_tac x="Max {prio. ready_queues s (cur_domain s) prio \<noteq> []}" in allE)
  apply clarsimp
  apply (erule_tac x="hd (max_non_empty_queue (ready_queues s (cur_domain s)))" in ballE)
   apply (clarsimp)
   apply (erule notE, rule domtcbs)
    apply force
   apply (simp add: etcb_at_def)
  apply (simp add: max_non_empty_queue_def)
  apply (erule_tac P="hd A \<in> B" for A B in notE)
  apply (rule Max_prop)
   apply force+
   done

lemma switch_within_domain:
  "\<lbrakk>scheduler_action s = switch_thread x;valid_sched s; pas_refined aag s\<rbrakk> \<Longrightarrow>
   pasObjectAbs aag x \<in> pasDomainAbs aag (cur_domain s)"
  apply (clarsimp simp: valid_sched_def valid_sched_action_def switch_in_cur_domain_def
                        in_cur_domain_def etcb_at_def valid_etcbs_def st_tcb_at_def
                        is_etcb_at_def weak_valid_sched_action_def)
  apply (drule_tac x=x in spec)
  apply (simp add: obj_at_def)
  apply (clarsimp simp add: pas_refined_def tcb_domain_map_wellformed_aux_def)
  apply (drule_tac x="(x,tcb_domain y)" in bspec)
   apply (rule domtcbs)
    apply simp+
  done

lemma schedule_guarded_pas_domain:
  "\<lbrace>guarded_pas_domain aag and einvs and pas_refined aag\<rbrace> schedule \<lbrace>\<lambda>_. guarded_pas_domain aag\<rbrace>"
  supply ethread_get_wp[wp del]
  apply (simp add: schedule_def)
  apply (wpsimp wp: guarded_pas_domain_lift[where f="activate_thread"]
                    guarded_pas_domain_lift[where f="set_scheduler_action f" for f]
                    guarded_switch_to_lift switch_to_thread_guarded_pas_domain
                    next_domain_valid_queues activate_thread_cur_thread gts_wp
          | wpc
          | rule choose_thread_guarded_pas_domain
          | simp add: schedule_choose_new_thread_def ethread_get_when_def split del: if_split
          | wp (once) hoare_drop_imp[where f="ethread_get t v" for t v]
          | wp (once) hoare_drop_imp[where f="schedule_switch_thread_fastfail c i cp p" for c i cp p])+



apply (wp hoare_drop_imp)

apply (wpsimp wp: guarded_pas_domain_lift[where f="activate_thread"]
                    guarded_pas_domain_lift[where f="set_scheduler_action f" for f]
                    guarded_switch_to_lift switch_to_thread_guarded_pas_domain
                    next_domain_valid_queues activate_thread_cur_thread gts_wp
          | wpc
          | rule choose_thread_guarded_pas_domain
          | simp add: schedule_choose_new_thread_def ethread_get_when_def split del: if_split
          | wp (once) hoare_drop_imp[where f="ethread_get t v" for t v]
          | wp (once) hoare_drop_imp[where f="schedule_switch_thread_fastfail c i cp p" for c i cp p])+

   apply (fastforce intro: switch_within_domain switch_thread_runnable
                    simp: valid_sched_def elim!: st_tcb_weakenE)+
  done

lemma schedule_if_guarded_pas_domain[wp]:
  "\<lbrace>guarded_pas_domain aag and einvs and pas_refined aag\<rbrace>
      schedule_if tc
   \<lbrace>\<lambda>_. guarded_pas_domain aag\<rbrace>"
  apply (simp add: schedule_if_def)
  apply (wp schedule_guarded_pas_domain)
  done

lemma schedule_if_ct_running_or_ct_idle[wp]:
  "\<lbrace>invs\<rbrace>
      schedule_if tc
   \<lbrace>\<lambda>_ s. ct_running s \<or> ct_idle s\<rbrace>"
  apply(simp add: schedule_if_def | wp)+
   apply(rule hoare_strengthen_post[OF activate_invs] | simp | wp)+
  done



lemma set_thread_state_scheduler_action:
  "\<lbrace>(\<lambda>s. P (scheduler_action (s::det_state))) and st_tcb_at runnable t and K (runnable s)\<rbrace>
      set_thread_state t s
   \<lbrace>\<lambda>_ s. P (scheduler_action s)\<rbrace>"
  apply(simp add: set_thread_state_def | wp sts_ext_running_noop set_object_wp)+
  apply(clarsimp simp: st_tcb_at_def obj_at_def)
  done

lemma activate_thread_scheduler_action[wp]:
  "\<lbrace> \<lambda>s. P (scheduler_action (s::det_state)) \<rbrace> activate_thread \<lbrace> \<lambda>_ s. P (scheduler_action s)\<rbrace>"
  apply(simp add: activate_thread_def arch_activate_idle_thread_def
       | wp set_thread_state_scheduler_action gts_wp | wpc)+
  apply(fastforce elim: st_tcb_weakenE)
  done



declare gts_st_tcb_at[wp del]

lemma schedule_if_scheduler_action[wp]:
  "\<lbrace>\<top>\<rbrace>
     schedule_if tc
   \<lbrace>\<lambda>_ (s::det_state). scheduler_action s = resume_cur_thread\<rbrace>"
  apply(simp add: schedule_if_def | wp | wpc)+
  apply(simp add: schedule_def schedule_choose_new_thread_def split del: if_split | wp | wpc)+
  done

crunch valid_sched[wp]: schedule_if "valid_sched"

lemma schedule_if_irq_masks:
  "\<lbrace>(\<lambda>s. P (irq_masks_of_state s)) and domain_sep_inv False st\<rbrace>
   schedule_if tc
   \<lbrace>\<lambda>_ s. P (irq_masks_of_state s)\<rbrace>"
  apply(simp add: schedule_if_def | wp)+
  done

crunch valid_list[wp]: schedule_if "valid_list"


definition kernel_schedule_if
  :: "((user_context \<times> det_state) \<times> unit \<times> (user_context \<times> det_state)) set"
where
  "kernel_schedule_if \<equiv>
      {(s, e, s'). s' \<in> fst (split schedule_if s)}"

subsection \<open>kernel_exit_if\<close>

text \<open>
  Restore the user context
\<close>
definition kernel_exit_if
  :: "user_context \<Rightarrow> (user_context,det_ext) s_monad"
where
  "kernel_exit_if tc \<equiv> do
    t' \<leftarrow> gets cur_thread;
    thread_get (arch_tcb_context_get o tcb_arch) t'
  od"

crunch inv[wp]: kernel_exit_if "P"

definition kernel_exit_A_if
  :: "((user_context \<times> det_state) \<times> sys_mode \<times> (user_context \<times> det_state)) set"
where
  "kernel_exit_A_if \<equiv>
      {(s, m, s'). s' \<in> fst (split kernel_exit_if s) \<and>
                   m = (if ct_running (snd s') then InUserMode else InIdleMode)}"


subsection \<open>check_active_irq_if\<close>

type_synonym observable_if = "det_state global_sys_state"

text \<open>
  Check for active IRQs without updating the user context
\<close>
definition check_active_irq_if
  :: "user_context \<Rightarrow> (irq option \<times> user_context, ('z :: state_ext)) s_monad"
where
  "check_active_irq_if tc \<equiv>
   do irq \<leftarrow> do_machine_op (getActiveIRQ False);
      return (irq, tc)
   od"

subsection \<open>ADT_A_if definition\<close>

definition check_active_irq_A_if
  :: "((user_context \<times> ('z :: state_ext) state) \<times> irq option \<times>
        (user_context \<times> ('z :: state_ext) state)) set"
where
  "check_active_irq_A_if \<equiv>
      {((tc, s), irq, (tc', s')). ((irq, tc'), s') \<in> fst (check_active_irq_if tc s)}"

abbreviation internal_state_if :: "((MachineTypes.register \<Rightarrow> 32 word) \<times> 'a) \<times> sys_mode \<Rightarrow> 'a"
where
  "internal_state_if \<equiv> \<lambda>s. (snd (fst s))"

lemma valid_device_abs_state_eq:
  "\<lbrakk>valid_machine_state s\<rbrakk> \<Longrightarrow> abs_state s = s"
  apply (simp add: abs_state_def observable_memory_def)
  apply (case_tac s)
   apply clarsimp
  apply (case_tac machine_state)
   apply clarsimp
  apply (rule ext)
  apply (fastforce simp: user_mem_def option_to_0_def valid_machine_state_def)
  done




(*Weakened invs_if to properties only necessary for refinement*)
definition full_invs_if :: "observable_if set"
where
  "full_invs_if \<equiv>
    {s. einvs (internal_state_if s) \<and>
        (snd s \<noteq> KernelSchedule True \<longrightarrow> domain_time (internal_state_if s) > 0) \<and>
        (domain_time (internal_state_if s) = 0
           \<longrightarrow> scheduler_action (internal_state_if s) = choose_new_thread) \<and>
        valid_domain_list (internal_state_if s) \<and>
        (case (snd s)
          of (KernelEntry e) \<Rightarrow>
                (e \<noteq> Interrupt \<longrightarrow> ct_running (internal_state_if s))
                \<and> (ct_running (internal_state_if s) \<or> ct_idle (internal_state_if s))
                \<and> scheduler_action (internal_state_if s) = resume_cur_thread
           | KernelExit \<Rightarrow>
                (ct_running (internal_state_if s) \<or> ct_idle (internal_state_if s))
                \<and> scheduler_action (internal_state_if s) = resume_cur_thread
           | InUserMode \<Rightarrow>
                ct_running (internal_state_if s)
                \<and> scheduler_action (internal_state_if s) = resume_cur_thread
           | InIdleMode \<Rightarrow>
                ct_idle (internal_state_if s)
                \<and> scheduler_action (internal_state_if s) = resume_cur_thread
           | _ \<Rightarrow> True) }"

end

(*We'll define this later, currently it doesn't matter if
  we restrict the permitted steps of the system*)
consts step_restrict :: "(det_state global_sys_state) \<Rightarrow> bool"

context begin interpretation Arch . (*FIXME: arch_split*)

definition ADT_A_if
  :: "(user_transition_if) \<Rightarrow> (det_state global_sys_state, observable_if, unit) data_type"
where
 "ADT_A_if uop \<equiv>
  \<lparr> Init = \<lambda>s. {s} \<inter> full_invs_if \<inter> {s. step_restrict s}, Fin = id,
    Step = (\<lambda>u. global_automaton_if check_active_irq_A_if (do_user_op_A_if uop) kernel_call_A_if
                                    kernel_handle_preemption_if kernel_schedule_if kernel_exit_A_if
             \<inter> {(s,s'). step_restrict s'})\<rparr>"


lemma check_active_irq_if_wp:
  "\<lbrace>\<lambda>s. P ((irq_at (irq_state (machine_state s) + 1) (irq_masks (machine_state s))),tc)
           (s\<lparr>machine_state := (machine_state s\<lparr>irq_state := irq_state (machine_state s) + 1\<rparr>)\<rparr>)\<rbrace>
     check_active_irq_if tc
   \<lbrace>P\<rbrace>"
  apply(simp add: check_active_irq_if_def | wp dmo_getActiveIRQ_wp)+
  done


lemma do_user_op_if_only_timer_irq_inv[wp]:
  "\<lbrace>only_timer_irq_inv irq (st::det_state)\<rbrace>
   do_user_op_if a b
   \<lbrace>\<lambda>_. only_timer_irq_inv irq st\<rbrace>"
  apply(rule hoare_pre)
   apply(wp only_timer_irq_inv_pres | simp | blast)+
  done

lemma kernel_entry_if_only_timer_irq_inv:
  "\<lbrace>only_timer_irq_inv irq st and einvs and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_active s)\<rbrace>
   kernel_entry_if e tc
   \<lbrace>\<lambda>_. only_timer_irq_inv irq st\<rbrace>"
  apply(rule hoare_pre)
   apply(wp only_timer_irq_inv_pres kernel_entry_if_irq_masks kernel_entry_if_domain_sep_inv
        | simp)+
  by blast

lemma handle_preemption_if_only_timer_irq_inv[wp]:
  "\<lbrace>only_timer_irq_inv irq st\<rbrace>
   handle_preemption_if tc
   \<lbrace>\<lambda>_. only_timer_irq_inv irq st\<rbrace>"
  apply(rule hoare_pre)
   apply(wp only_timer_irq_inv_pres handle_preemption_if_irq_masks
            handle_preemption_if_domain_sep_inv
        | simp | blast)+
  done

lemma schedule_if_only_timer_irq_inv[wp]:
  "\<lbrace>only_timer_irq_inv irq st\<rbrace>
   schedule_if tc
   \<lbrace>\<lambda>_. only_timer_irq_inv irq st\<rbrace>"
  apply(rule hoare_pre)
   apply(wp only_timer_irq_inv_pres schedule_if_irq_masks | blast)+
  done

subsection \<open>Big step IF automaton\<close>

fun interrupted_modes where
  "interrupted_modes KernelPreempted = True" |
  "interrupted_modes (KernelEntry Interrupt) = True" |
  "interrupted_modes _ = False"

text \<open>
  A first attempt at defining the big steps. They look like this:

  user mode           +-----------+                   +------ ...
  - - - - - - - -    /             \                 /
  kernel mode       /               +---------------+
               KernelExit       interrupted     KernelExit


  big steps          --------------> --------------> ------- ...

  dom                 current dom      scheduler      current dom


  That is, a step of the current domain lasts from its kernel exit until
  the point at which the kernel services the next interrupt, either because
  the arrival of that interrupt traps from user- to kernel-mode (in which
  case the system has just moved into KernelEntry Interrupt state) or
  because a long-running system call was pre-empted by the arrival of an
  interrupt (in which case the system has just moved into the
  KernelPreempted state).

  The scheduler domain then runs until the next kernel exit, at which point
  whoever is now the current domain begins its big execution step.
\<close>

definition big_step_R :: "det_state global_sys_state \<Rightarrow> det_state global_sys_state \<Rightarrow> bool"
where
  "big_step_R \<equiv> \<lambda> s s'.
      (snd s = KernelExit \<and> interrupted_modes (snd s')) \<or>
      (interrupted_modes (snd s) \<and> snd s' = KernelExit)"

definition big_step_evmap :: "unit list \<Rightarrow> unit"
where
  "big_step_evmap evs \<equiv> ()"

definition big_step_ADT_A_if
  :: "user_transition_if \<Rightarrow> (observable_if, observable_if, unit) data_type"
where
  "big_step_ADT_A_if utf \<equiv> big_step_adt (ADT_A_if utf) big_step_R big_step_evmap"

definition cur_context
where
  "cur_context s = arch_tcb_context_get (tcb_arch (the (get_tcb (cur_thread s) s)))"

end

subsection \<open>Locales setup\<close>

(* the second argument of det_inv the user_context, which is saved in kernel state
   on kernel_entry_if, and restored on kernel_exit_if.
   Between these sys_modes the user_context that is passed through is not used,
   rather cur_context is. *)
locale invariant_over_ADT_if =
  fixes det_inv :: "sys_mode \<Rightarrow> user_context \<Rightarrow> det_state \<Rightarrow> bool"
  fixes utf :: "user_transition_if"

  assumes det_inv_abs_state:
     "\<And>e tc s. valid_machine_state s \<Longrightarrow> det_inv e tc s \<Longrightarrow> det_inv e tc (abs_state s)"

  assumes kernel_entry_if_det_inv:
     "\<And>e tc. \<lbrace>einvs and det_inv (KernelEntry e) tc and ct_running and K (e \<noteq> Interrupt)\<rbrace>
        kernel_entry_if e tc
      \<lbrace>\<lambda>rv s. case (fst rv) of Inl irq \<Rightarrow> det_inv KernelPreempted (cur_context s) s
              | Inr () \<Rightarrow> det_inv (KernelSchedule False) (cur_context s) s\<rbrace>"
  assumes kernel_entry_if_Interrupt_det_inv:
     "\<And>tc. \<lbrace>einvs and det_inv (KernelEntry Interrupt) tc and (\<lambda>s. ct_running s \<or> ct_idle s)\<rbrace>
        kernel_entry_if Interrupt tc
      \<lbrace>\<lambda>rv s. case (fst rv) of Inl irq \<Rightarrow> det_inv KernelPreempted (cur_context s) s
              | Inr () \<Rightarrow> det_inv (KernelSchedule True) (cur_context s) s\<rbrace>"
  assumes handle_preemption_if_det_inv:
     "\<And>tc. \<lbrace>einvs and (\<lambda>s. det_inv KernelPreempted (cur_context s) s)\<rbrace>
        handle_preemption_if tc
      \<lbrace>\<lambda>rv s. det_inv (KernelSchedule True) (cur_context s) s\<rbrace>"
  assumes schedule_if_det_inv:
     "\<And>b tc. \<lbrace>einvs and (\<lambda>s. det_inv (KernelSchedule b) (cur_context s) s)\<rbrace>
        schedule_if tc
      \<lbrace>\<lambda>rv s. det_inv KernelExit (cur_context s) s\<rbrace>"
  assumes kernel_exit_if_det_inv:
     "\<And>tc. \<lbrace>einvs and (\<lambda>s. det_inv KernelExit (cur_context s) s) and (\<lambda>s. ct_running s \<or> ct_idle s)\<rbrace>
        kernel_exit_if tc
      \<lbrace>\<lambda>rv s. if ct_running s then det_inv InUserMode rv s
              else det_inv InIdleMode rv s\<rbrace>"
  assumes do_user_op_if_det_inv:
     "\<And>tc. \<lbrace>einvs and det_inv InUserMode tc and ct_running\<rbrace>
        do_user_op_if utf tc
      \<lbrace>\<lambda>rv. case (fst rv) of Some e \<Rightarrow> det_inv (KernelEntry e) (snd rv)
            | None \<Rightarrow> det_inv InUserMode (snd rv)\<rbrace>"
  assumes check_active_irq_if_User_det_inv:
     "\<And>tc. \<lbrace>einvs and det_inv InUserMode tc and ct_running\<rbrace>
        check_active_irq_if tc
      \<lbrace>\<lambda>rv. case (fst rv) of Some irq \<Rightarrow> det_inv (KernelEntry Interrupt) (snd rv)
            | None \<Rightarrow> det_inv InUserMode (snd rv)\<rbrace>"
  assumes check_active_irq_if_Idle_det_inv:
     "\<And>tc. \<lbrace>einvs and det_inv InIdleMode tc and ct_idle\<rbrace>
        check_active_irq_if tc
      \<lbrace>\<lambda>rv. case (fst rv) of Some irq \<Rightarrow> det_inv (KernelEntry Interrupt) (snd rv)
            | None \<Rightarrow> det_inv InIdleMode (snd rv)\<rbrace>"

locale valid_initial_state_noenabled = invariant_over_ADT_if + Arch + (* FIXME: arch_split *)
  fixes s0_internal :: det_state
  fixes initial_aag :: "'a subject_label PAS"
  fixes timer_irq :: "10 word"
  fixes current_aag
  fixes s0 :: observable_if
  fixes s0_context :: user_context
  defines
  "current_aag t \<equiv>
  (initial_aag\<lparr> pasSubject := the_elem (pasDomainAbs initial_aag (cur_domain t)) \<rparr>)"

(* Run the system from right where we exit the kernel for the first time
   to user-space.
   It shouldn't matter what the initial machine context is since the first
   thing that should happen on a KernelExit is to restore it from the
   cur_thread *)
  defines
  "s0 \<equiv> ((if ct_idle s0_internal then idle_context s0_internal else s0_context,s0_internal),
          KernelExit)"
  assumes cur_domain_subject_s0:
  "pasSubject initial_aag \<in> pasDomainAbs initial_aag (cur_domain s0_internal)"
  assumes policy_wellformed:
  "pas_wellformed_noninterference initial_aag"
  fixes Invs
  defines "Invs s \<equiv> einvs s \<and> only_timer_irq_inv timer_irq s0_internal s \<and>
                               silc_inv (current_aag s) s0_internal s \<and>
                               domain_sep_inv False s0_internal s \<and>
                               pas_refined (current_aag s) s \<and>
                               guarded_pas_domain (current_aag s) s \<and>
                               idle_equiv s0_internal s \<and>
                               valid_domain_list s \<and> valid_pdpt_objs s"
  assumes Invs_s0_internal: "Invs s0_internal"
  assumes det_inv_s0: "det_inv KernelExit (cur_context s0_internal) s0_internal"

  assumes scheduler_action_s0_internal: "scheduler_action s0_internal = resume_cur_thread"
  assumes ct_running_or_ct_idle_s0_internal: "ct_running s0_internal \<or> ct_idle s0_internal"
  assumes domain_time_s0_internal: "domain_time s0_internal > 0"
  assumes utf_det: "\<forall>pl pr pxn tc um ds es s. det_inv InUserMode tc s \<and> einvs s \<and>
                               context_matches_state pl pr pxn um ds es s \<and> ct_running s
                               \<longrightarrow> (\<exists>x. utf (cur_thread s) pl pr pxn (tc, um, ds, es) = {x})"
  assumes utf_non_empty: "\<forall>t pl pr pxn tc um ds es. utf t pl pr pxn (tc, um, ds, es) \<noteq> {}"
  assumes utf_non_interrupt: "\<forall>t pl pr pxn tc um ds es e f g.
                                (e,f,g) \<in> utf t pl pr pxn (tc, um, ds, es) \<longrightarrow> e \<noteq> Some Interrupt"
  assumes extras_s0: "step_restrict s0"
  assumes pasMaySendIrqs_initial_aag[simp]: "pasMaySendIrqs initial_aag = False"


locale valid_initial_state = valid_initial_state_noenabled +
       assumes ADT_A_if_enabled_system: "enabled_system (ADT_A_if utf) s0"
       assumes ADT_A_if_Init_Fin_serial:
       "Init_Fin_serial (ADT_A_if utf) s0 (full_invs_if \<inter> {s. step_restrict s})"

subsection \<open>TODO\<close>

function (domintros) next_irq_state :: "nat \<Rightarrow> (10 word \<Rightarrow> bool) \<Rightarrow> nat" where
  "next_irq_state cur masks =
         (if irq_at cur masks = None then next_irq_state (Suc cur) masks else cur)"
  by(pat_completeness, auto)

lemma recurring_next_irq_state_dom:
  "irq_is_recurring irq s \<Longrightarrow> next_irq_state_dom (n,irq_masks (machine_state s))"
  apply(clarsimp simp: irq_is_recurring_def)
  apply(drule_tac x=n in spec)
  apply(erule exE)
  proof -
    fix m
    assume i: "is_irq_at s irq (n + m)"
    have "n \<le> n + m" by simp
    thus "next_irq_state_dom (n, irq_masks (machine_state s))"
    proof(induct rule: inc_induct)
      from i obtain irq where a: "irq_at (n + m) (irq_masks (machine_state s)) = Some irq"
        by(fastforce simp: is_irq_at_def)
      show "next_irq_state_dom (n + m, irq_masks (machine_state s))"
        using a by(fastforce intro: next_irq_state.domintros)
    next
      fix i
      assume "next_irq_state_dom (Suc i, irq_masks (machine_state s))"
      thus "next_irq_state_dom (i, irq_masks (machine_state s))"
        by(rule next_irq_state.domintros)
    qed
  qed

context begin interpretation Arch . (*FIXME: arch_split*)

subsection \<open>domain_field preserved on non-interrupt kernel event\<close>

crunch irq_state_of_state[wp]: cap_move "\<lambda>s. P (irq_state_of_state s)"
crunch domain_fields[wp]: handle_yield "domain_fields P"
crunch domain_fields[wp]: handle_vm_fault, handle_hypervisor_fault "domain_fields P"
  (ignore: getFAR getDFSR getIFSR)

crunch domain_list[wp]: schedule_if "\<lambda>s. P (domain_list s)"
  (wp: crunch_wps simp: crunch_simps)

crunch domain_fields[wp]: activate_thread "domain_fields P"

lemma next_domain_domain_time_nonzero:
  "\<lbrace>valid_domain_list\<rbrace> next_domain \<lbrace>\<lambda>r s. domain_time s > 0\<rbrace>"
  apply(simp add: next_domain_def)
  apply wp
  apply(clarsimp simp: Let_def valid_domain_list_2_def)
  apply(drule_tac x="domain_list s ! (Suc (domain_index s) mod length (domain_list s))" in bspec)
   apply simp
  apply(simp split: prod.splits)
  done

lemma nonzero_gt_zero[simp]:
  "x \<noteq> (0::word32) \<Longrightarrow> x > 0"
  apply(rule nonzero_unat_simp)
  apply(simp add: unat_gt_0)
  done

lemma schedule_if_domain_time_nonzero':
  "\<lbrace>valid_domain_list and (\<lambda>s. domain_time s = 0 \<longrightarrow> scheduler_action s = choose_new_thread)\<rbrace>
   schedule_if tc
   \<lbrace>(\<lambda>_ s. domain_time s > 0)\<rbrace>"
  apply (simp add: schedule_if_def schedule_def)
  apply (wp next_domain_domain_time_nonzero
        | wpc | simp add: crunch_simps guarded_switch_to_def switch_to_thread_def
                              choose_thread_def switch_to_idle_thread_def
                              arch_switch_to_idle_thread_def)+
              apply(wp hoare_drop_imps)
             apply(wp hoare_drop_imps)
            apply wp+
    apply (simp add: choose_thread_def switch_to_idle_thread_def arch_switch_to_idle_thread_def
                     guarded_switch_to_def switch_to_thread_def | wp)+
    apply (wp gts_wp)+
  apply auto
  done

lemma schedule_if_domain_time_nonzero:
  "\<lbrace>valid_domain_list and (\<lambda>s. domain_time s = 0 \<longrightarrow> scheduler_action s = choose_new_thread)\<rbrace>
   schedule_if tc
   \<lbrace>(\<lambda>_ s. domain_time s \<noteq> 0)\<rbrace>"
  apply(rule hoare_strengthen_post[OF schedule_if_domain_time_nonzero'])
  apply simp
  done

lemma handle_event_domain_fields:
  notes hy_inv[wp del]
  shows
  "\<lbrace>domain_fields P and K (e \<noteq> Interrupt)\<rbrace>
   handle_event e
   \<lbrace>\<lambda>_. domain_fields P\<rbrace>"
  apply(rule hoare_gen_asm)
  apply(rule hoare_pre)
  apply(case_tac e)
       apply(rename_tac syscall)
       apply(case_tac syscall)
             apply(wp | simp add: handle_call_def)+
  done

crunch domain_list[wp]: kernel_entry_if "\<lambda>s. P (domain_list s)"
crunch domain_list[wp]: handle_preemption_if "\<lambda>s. P (domain_list s)"


lemma kernel_entry_if_domain_fields:
  "\<lbrace>domain_fields P and K (e \<noteq> Interrupt)\<rbrace>
   kernel_entry_if e tc
   \<lbrace>\<lambda>_. domain_fields P\<rbrace>"
  apply(simp add: kernel_entry_if_def)
  apply(wp handle_event_domain_fields | simp)+
  done


lemma kernel_entry_if_domain_time_sched_action:
  "\<lbrace>\<lambda>s. domain_time s > 0\<rbrace>
   kernel_entry_if e tc
   \<lbrace>\<lambda>_ s. domain_time s = 0 \<longrightarrow> scheduler_action s = choose_new_thread\<rbrace>"
  apply (case_tac "e = Interrupt")
   apply (simp add: kernel_entry_if_def)
   apply (wp handle_interrupt_valid_domain_time| wpc | simp)+
      apply (rule_tac Q="\<lambda>r s. domain_time s > 0" in hoare_strengthen_post)
       apply (wp | simp)+
      apply (wp hoare_false_imp kernel_entry_if_domain_fields | fastforce)+
  done

end


subsection \<open>to split generic preservation lemma\<close>

lemma handle_preemption_if_domain_time_sched_action:
  "\<lbrace>\<lambda>s. domain_time s > 0\<rbrace>
   handle_preemption_if tc
   \<lbrace>\<lambda>_ s. domain_time s = 0 \<longrightarrow> scheduler_action s = choose_new_thread\<rbrace>"
  apply (simp add: handle_preemption_if_def)
  apply (wp handle_interrupt_valid_domain_time| wpc | simp)+
   apply (rule_tac Q="\<lambda>r s. domain_time s > 0" in hoare_strengthen_post)
    apply wpsimp+
  done

lemma timer_tick_domain_time_sched_action:
  "num_domains > 1 \<Longrightarrow>
   \<lbrace> \<top> \<rbrace>
   timer_tick
   \<lbrace>\<lambda>r s. domain_time s = 0 \<longrightarrow> scheduler_action s = choose_new_thread\<rbrace>"
  apply(simp add: timer_tick_def reschedule_required_def   | wp | wpc)+
  done

lemma gt_zero_nonzero[simp]:
  "(0::word32) < x \<Longrightarrow> x \<noteq> 0"
  by (metis word_not_simps(1))

definition user_context_of :: "'k global_sys_state \<Rightarrow> user_context"
where
  "user_context_of \<equiv> \<lambda>s. fst (fst s)"

lemma user_context_of_simp[simp]:
  "user_context_of ((uc,s),mode) = uc"
  by(simp add: user_context_of_def)

definition sys_mode_of :: "'k global_sys_state \<Rightarrow> sys_mode"
where
  "sys_mode_of \<equiv> \<lambda>s. snd s"

lemma sys_mode_of_simp[simp]:
  "sys_mode_of ((uc,s),mode) = mode"
  by(simp add: sys_mode_of_def)

lemma exit_idle_context:
  "\<lbrace>ct_idle and invs\<rbrace> kernel_exit_if tc' \<lbrace>\<lambda>tc s. tc = idle_context s\<rbrace>"
  apply (simp add: kernel_exit_if_def thread_get_def)
  apply wp
  apply (subgoal_tac "cur_thread s = idle_thread s")
  apply (clarsimp simp: cur_thread_idle idle_context_def)+
  done

lemma check_active_irq_context:
  "\<lbrace>\<top>\<rbrace> check_active_irq_if tc' \<lbrace>\<lambda>tc s. (snd tc) = tc'\<rbrace>"
  apply (simp add: check_active_irq_if_def)
  apply (wp del: no_irq| simp)+
  done

lemma kernel_entry_context:
  "\<lbrace>\<top>\<rbrace> kernel_entry_if e tc' \<lbrace>\<lambda>tc s. (snd tc) = tc'\<rbrace>"
  apply (simp add: kernel_entry_if_def)
  apply (wp del: no_irq| simp)+
  done

lemma handle_preemption_context:
  "\<lbrace>\<top>\<rbrace> handle_preemption_if tc' \<lbrace>\<lambda>tc s. tc = tc'\<rbrace>"
  apply (simp add: handle_preemption_if_def)
  apply (wp del: no_irq| simp)+
  done

lemma get_tcb_machine_stat_update[simp]:
  "get_tcb t (s\<lparr>machine_state := x\<rparr>) = get_tcb t s"
  apply (simp add: get_tcb_def)
  done

lemma handle_preemption_globals_equiv[wp]:
  "\<lbrace>globals_equiv st and invs\<rbrace>
      handle_preemption_if a
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  apply (simp add: handle_preemption_if_def)
  apply (wp handle_interrupt_globals_equiv dmo_getActiveIRQ_globals_equiv crunch_wps
        | simp add: crunch_simps)+
  done

lemmas handle_preemption_idle_equiv[wp] =
             idle_globals_lift[OF handle_preemption_globals_equiv
                                  invs_pd_not_idle_thread,
                               simplified]

lemma schedule_if_globals_equiv_scheduler[wp]:
  "\<lbrace>globals_equiv_scheduler st and invs\<rbrace> schedule_if tc \<lbrace>\<lambda>_. globals_equiv_scheduler st\<rbrace>"
  apply (simp add: schedule_if_def)
  apply wp
  apply (wp globals_equiv_scheduler_inv'[where P="invs"] activate_thread_globals_equiv)
  apply (simp add: invs_valid_ko_at_arm invs_valid_idle)
  apply (wp | simp)+
  done

lemmas schedule_if_idle_equiv[wp] =
            idle_globals_lift_scheduler[OF schedule_if_globals_equiv_scheduler
                                           invs_pd_not_idle_thread,
                                        simplified]

lemma dmo_user_memory_update_idle_equiv:
  "\<lbrace>idle_equiv st\<rbrace> do_machine_op (user_memory_update um) \<lbrace>\<lambda>y. idle_equiv st\<rbrace>"
  by (wpsimp wp: dmo_wp)

lemma dmo_device_memory_update_idle_equiv:
  "\<lbrace>idle_equiv st\<rbrace> do_machine_op (device_memory_update um) \<lbrace>\<lambda>y. idle_equiv st\<rbrace>"
  by (wpsimp wp: dmo_wp)

lemma do_user_op_if_idle_equiv[wp]:
  "\<lbrace>idle_equiv st and invs\<rbrace>
   do_user_op_if tc uop
   \<lbrace>\<lambda>_. idle_equiv st\<rbrace>"
  unfolding do_user_op_if_def
  by (wpsimp wp: dmo_user_memory_update_idle_equiv dmo_device_memory_update_idle_equiv select_wp)

lemma ct_active_not_idle':
  "ct_active s \<Longrightarrow> \<not> ct_idle s"
  apply (clarsimp simp add: ct_in_state_def st_tcb_at_def obj_at_def)
  done

lemma Init_Fin_serial_weak_strengthen:
  "\<lbrakk>Init_Fin_serial_weak A s0 I; A [> J; J \<subseteq> I; Init A s0 \<subseteq> J\<rbrakk> \<Longrightarrow> Init_Fin_serial_weak A s0 J"
  by (force simp: Init_Fin_serial_weak_def serial_system_weak_def Init_Fin_serial_weak_axioms_def)

lemma rel_terminate_weaken:
  "rel_terminate A s0 R I measuref \<Longrightarrow> J \<subseteq> I \<Longrightarrow> rel_terminate A s0 R J measuref"
  by (force simp: rel_terminate_def)

context valid_initial_state begin

interpretation Arch . (*FIXME arch_split*)

lemma domains_distinct:
  "pas_domains_distinct initial_aag"
  apply (rule pas_wellformed_noninterference_domains_distinct)
  apply (rule policy_wellformed)
  done

lemma current_domains_distinct:
  "pas_domains_distinct (current_aag s)"
  using domains_distinct
  apply (simp add: current_aag_def pas_domains_distinct_def)
  done

lemmas the_subject_of_aag_domain = domain_has_the_label[OF domains_distinct]

lemma current_aag_initial:
  "current_aag s0_internal = initial_aag"
  apply (simp add: current_aag_def the_subject_of_aag_domain cur_domain_subject_s0)
  done

subsection \<open>@{term ADT_A_if} is a step system with the invs_if invariant\<close>

definition cur_thread_context_of :: "observable_if \<Rightarrow> user_context"
where
  "cur_thread_context_of \<equiv>
     \<lambda>s. case sys_mode_of s of
           InUserMode \<Rightarrow> user_context_of s
         | InIdleMode \<Rightarrow> user_context_of s
         | KernelEntry e \<Rightarrow> user_context_of s
         | _ \<Rightarrow> cur_context (internal_state_if s)"

definition invs_if :: "observable_if \<Rightarrow> bool"
where
  "invs_if s \<equiv>
    Invs (internal_state_if s) \<and>
    det_inv (sys_mode_of s) (cur_thread_context_of s) (internal_state_if s) \<and>
    (snd s \<noteq> KernelSchedule True \<longrightarrow> domain_time (internal_state_if s) > 0) \<and>
    (domain_time (internal_state_if s) = 0
       \<longrightarrow> scheduler_action (internal_state_if s) = choose_new_thread) \<and>
    (snd s \<noteq> KernelExit
       \<longrightarrow> (ct_idle (internal_state_if s)
             \<longrightarrow> user_context_of s = idle_context (internal_state_if s))) \<and>
    (case (snd s)
      of KernelEntry e \<Rightarrow>
                     (e \<noteq> Interrupt \<longrightarrow> ct_running (internal_state_if s)) \<and>
                     (ct_running (internal_state_if s) \<or> ct_idle (internal_state_if s)) \<and>
                     scheduler_action (internal_state_if s) = resume_cur_thread
        | KernelExit \<Rightarrow>
                     (ct_running (internal_state_if s) \<or> ct_idle (internal_state_if s)) \<and>
                     scheduler_action (internal_state_if s) = resume_cur_thread
        | InUserMode \<Rightarrow>
                     ct_running (internal_state_if s) \<and>
                     scheduler_action (internal_state_if s) = resume_cur_thread
        | InIdleMode \<Rightarrow>
                     ct_idle (internal_state_if s) \<and>
                     scheduler_action (internal_state_if s) = resume_cur_thread
        | _ \<Rightarrow> True)"

lemma invs_if_s0[simp]:
  "invs_if s0"
  apply(clarsimp simp: s0_def invs_if_def Invs_s0_internal[simplified]
                       ct_running_or_ct_idle_s0_internal domain_time_s0_internal
                       det_inv_s0 cur_thread_context_of_def)
  apply(simp add: scheduler_action_s0_internal)
  done

lemma only_timer_irq_inv_irq_state_update[simp]:
  "only_timer_irq_inv timer_irq s0_internal
           (b\<lparr>machine_state := machine_state b
                \<lparr>irq_state := Suc (irq_state (machine_state b))\<rparr>\<rparr>) =
   only_timer_irq_inv timer_irq s0_internal b"
  apply(clarsimp simp: only_timer_irq_inv_def only_timer_irq_def irq_is_recurring_def
        is_irq_at_def)
  done

lemma initial_aag_bak:
  "initial_aag = (current_aag s)\<lparr>pasSubject := the_elem (pasDomainAbs (current_aag s) (cur_domain s0_internal))\<rparr>"
  using current_aag_def cur_domain_subject_s0 the_subject_of_aag_domain
  by simp

(* By our locale assumptions, every domain has an associated label *)
lemma the_label_of_domain_exists[intro, simp]:
  "the_elem (pasDomainAbs initial_aag l) \<in> pasDomainAbs initial_aag l"
  using domains_distinct[simplified pas_domains_distinct_def] the_subject_of_aag_domain
  apply blast
  done

(* Corollary for current_aag *)
lemma pas_cur_domain_current_aag:
  "pas_cur_domain (current_aag s) s"
  apply (simp add: current_aag_def)
  done

lemma subject_current_aag:
  "pasSubject (current_aag s) \<in> pasDomainAbs initial_aag (cur_domain s)"
  apply (simp add: current_aag_def)
  done

lemma pas_wellformed_cur[iff]:
 "pas_wellformed_noninterference (current_aag s)"
  apply (cut_tac policy_wellformed)
  apply (simp add: pas_wellformed_noninterference_def current_aag_def pas_domains_distinct_def)
  done

declare policy_wellformed[iff]

lemma current_aag_lift:
  assumes b: "(\<And>aag. \<lbrace>P aag\<rbrace> f \<lbrace>\<lambda>r s. Q aag r s\<rbrace>)"
  assumes a: "(\<And>P. \<lbrace>\<lambda>s. P (cur_domain s)\<rbrace> f \<lbrace>\<lambda>r s. P (cur_domain s)\<rbrace>)"
  shows "\<lbrace>\<lambda>s. P (current_aag s) s\<rbrace> f \<lbrace>\<lambda>r s. Q (current_aag s) r s\<rbrace>"
  apply (simp add: current_aag_def)
  apply (rule hoare_lift_Pf3[where f="cur_domain", OF b a])
  done

lemma silc_inv_cur:
  "silc_inv (current_aag s) st s = silc_inv initial_aag st s"
  apply (rule iffI)
   apply (subst initial_aag_bak[where s=s])
   apply (rule silc_inv_pasSubject_update)
     apply simp+
   apply (simp add: current_aag_def)
   apply (subst the_subject_of_aag_domain[where l = "pasSubject initial_aag"])
    apply (rule cur_domain_subject_s0)
   apply (blast intro: cur_domain_subject_s0)
  apply (simp add: current_aag_def)
  apply (rule silc_inv_pasSubject_update)
    apply blast+
  done

lemma guarded_pas_domain_cur:
  "guarded_pas_domain (current_aag s) s = guarded_pas_domain initial_aag s"
  by (simp add: current_aag_def)

lemma pas_refined_cur:
  "pas_refined (current_aag s) s = pas_refined initial_aag s"
  apply (rule iffI)
   apply (subst initial_aag_bak[where s=s])
   apply (erule pas_refined_pasSubject_update)
    apply simp
   apply (simp add: current_aag_def)
   apply (subst the_subject_of_aag_domain[where l = "pasSubject initial_aag"])
    apply (rule cur_domain_subject_s0)
   apply (blast intro: cur_domain_subject_s0)
  apply (simp add: current_aag_def)
  apply (rule pas_refined_pasSubject_update)
    apply blast+
  done

lemma pas_cur_domain_cur:
  "pas_cur_domain initial_aag s \<Longrightarrow> pas_cur_domain (current_aag s) s"
  using subject_current_aag current_aag_def
  by auto

lemma pasObjectAbs_current_aag:
  "pasObjectAbs (current_aag x) = pasObjectAbs initial_aag"
  by(simp add: current_aag_def)

lemma pasIRQAbs_current_aag:
  "pasIRQAbs (current_aag x) = pasIRQAbs initial_aag"
  by(simp add: current_aag_def)

lemma pasASIDAbs_current_aag:
  "pasASIDAbs (current_aag x) = pasASIDAbs initial_aag"
  by(simp add: current_aag_def)

lemma pasPolicy_current_aag:
  "pasPolicy (current_aag x) = pasPolicy initial_aag"
  by(simp add: current_aag_def)



lemma guarded_pas_is_subject_current_aag:
  "\<lbrakk>guarded_pas_domain (current_aag s) s; invs s\<rbrakk> \<Longrightarrow>
   ct_active s \<longrightarrow> is_subject (current_aag s) (cur_thread s)"
  apply (clarsimp simp add: guarded_pas_domain_def current_aag_def)
  apply (rule sym)
  apply (blast intro: the_elemI dest: domains_distinct[THEN pas_domains_distinct_inj] ct_active_not_idle)
  done

lemma guarded_pas_domain_machine_state_update[simp]:
  "guarded_pas_domain aag (s\<lparr>machine_state := x\<rparr>) = guarded_pas_domain aag s"
  apply (simp add: guarded_pas_domain_def)
  done

lemma handle_event_was_not_Interrupt:
  "\<lbrace>\<top>\<rbrace> handle_event e -,\<lbrace>\<lambda> r s. e \<noteq> Interrupt\<rbrace>"
  apply(case_tac e)
  apply(simp | wp | wpc)+
  done

lemma kernel_entry_if_was_not_Interrupt:
  "\<lbrakk>(x, ba) \<in> fst (kernel_entry_if e a b)\<rbrakk> \<Longrightarrow> (case fst x of Inr a \<Rightarrow> True | _ \<Rightarrow>  e \<noteq> Interrupt)"
  apply(simp add: kernel_entry_if_def)
  apply(erule use_valid)
   apply wp
     apply simp
     apply(rule handle_event_was_not_Interrupt[simplified validE_E_def validE_def])
    apply wpsimp+
  done

lemma ct_idle_lift:
  assumes a: "\<And>P. \<lbrace>\<lambda>s. P (cur_thread s)\<rbrace> f \<lbrace>\<lambda>r s. P (cur_thread s)\<rbrace>"
  assumes d: "\<And>P. \<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> f \<lbrace>\<lambda>r s. P (idle_thread s)\<rbrace>"
  assumes b: "\<lbrace>Q\<rbrace> f \<lbrace>\<lambda>_. invs\<rbrace>"
  assumes c: "\<And>s. Q s \<Longrightarrow> invs s"
  shows "\<lbrace>Q and (\<lambda>s. P (ct_idle s))\<rbrace> f \<lbrace>\<lambda>r s. P (ct_idle s)\<rbrace>"
  apply (rule hoare_add_post[OF b],simp)
  apply (clarsimp simp: valid_def)
  apply (drule c)
  apply (clarsimp simp: cur_thread_idle)
  apply (rule use_valid[OF _ a],assumption)
  apply (erule use_valid[OF _ d],simp)
  done

lemma idle_equiv_context_equiv:
  "idle_equiv s s' \<Longrightarrow> invs s' \<Longrightarrow> idle_context s' = idle_context s"
  apply (clarsimp simp add: idle_equiv_def idle_context_def invs_def valid_state_def
                            valid_idle_def)
  apply (drule pred_tcb_at_tcb_at)
  apply (clarsimp simp add: tcb_at_def2 get_tcb_def)
  done

lemma kernel_entry_if_valid_pdpt_objs[wp]:
 "\<lbrace>valid_pdpt_objs and invs and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_active s)\<rbrace>
     kernel_entry_if e tc
  \<lbrace>\<lambda>s. valid_pdpt_objs\<rbrace>"
  apply (case_tac "e = Interrupt")
   apply (simp add: kernel_entry_if_def)
   apply (wp|wpc|simp add: kernel_entry_if_def)+
  apply (wpsimp simp: ran_tcb_cap_cases arch_tcb_update_aux2
         wp: static_imp_wp thread_set_invs_trivial)+
  done

lemma kernel_entry_if_det_inv':
  "\<lbrace>einvs and det_inv (KernelEntry e) tc and (\<lambda>s. ct_running s \<or> ct_idle s) and
        (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running s)\<rbrace>
      kernel_entry_if e tc
   \<lbrace>\<lambda>rv s. det_inv (case (fst rv) of Inl irq \<Rightarrow> KernelPreempted
                                   | Inr () \<Rightarrow> KernelSchedule (e = Interrupt)) (cur_context s) s\<rbrace>"
  apply (case_tac "e = Interrupt")
   apply simp
   apply (rule hoare_strengthen_post[OF kernel_entry_if_Interrupt_det_inv])
   apply (simp split: sum.splits unit.splits)
  apply simp
  apply (rule hoare_weaken_pre[OF hoare_strengthen_post[OF kernel_entry_if_det_inv]])
   apply (simp split: sum.splits unit.splits)
  apply simp
  done

lemma pasMaySendIrqs_current_aag[simp]:
  "pasMaySendIrqs (current_aag s) = False"
  apply(simp add: current_aag_def)
  done

lemma handle_preemption_if_valid_pdpt_objs[wp]:
  "\<lbrace>valid_pdpt_objs\<rbrace> handle_preemption_if a \<lbrace>\<lambda>rv s. valid_pdpt_objs s\<rbrace>"
  by (simp add: handle_preemption_if_def | wp)+

lemma schedule_if_valid_pdpt_objs[wp]:
  "\<lbrace>valid_pdpt_objs\<rbrace> schedule_if a \<lbrace>\<lambda>rv s. valid_pdpt_objs s\<rbrace>"
  by (simp add: schedule_if_def | wp)+

lemma do_user_op_if_valid_pdpt_objs[wp]:
  "\<lbrace>valid_pdpt_objs\<rbrace> do_user_op_if a b \<lbrace>\<lambda>rv s. valid_pdpt_objs s\<rbrace>"
  by (simp add: do_user_op_if_def | wp select_wp | wpc)+

lemma invs_if_Step_ADT_A_if:
  notes active_from_running[simp]
  shows
  "\<lbrakk>invs_if s; (s,t) \<in> data_type.Step (ADT_A_if utf) e\<rbrakk> \<Longrightarrow> invs_if t"
  apply(clarsimp simp: ADT_A_if_def global_automaton_if_def invs_if_def Invs_def
                       cur_thread_context_of_def
       | rule guarded_active_ct_cur_domain
       | clarify )+
  apply (elim disjE)
           apply(clarsimp simp: kernel_call_A_if_def)
           apply (frule kernel_entry_if_was_not_Interrupt)
           apply (frule use_valid[OF _ kernel_entry_if_det_inv])
            apply simp
           apply simp
           apply(erule use_valid)
            apply (rule current_aag_lift)
             apply (wp kernel_entry_if_invs kernel_entry_silc_inv[where st'=s0_internal]
                       kernel_entry_pas_refined[where st=s0_internal]
                       kernel_entry_if_valid_sched kernel_entry_if_only_timer_irq_inv
                       kernel_entry_if_domain_sep_inv kernel_entry_if_guarded_pas_domain
                       kernel_entry_if_domain_fields kernel_entry_if_idle_equiv
                       kernel_entry_if_domain_time_sched_action
                       hoare_false_imp ct_idle_lift
                    | clarsimp intro!: guarded_pas_is_subject_current_aag[rule_format]
                    | intro conjI)+
              apply (rule guarded_pas_is_subject_current_aag[rule_format],assumption+)
              apply (simp add: schact_is_rct_def)+
            apply (rule guarded_pas_is_subject_current_aag[rule_format],assumption+)
            apply(simp add: ct_active_not_idle' | elim exE)+

          apply(simp add: kernel_call_A_if_def | elim exE conjE)+
          apply (rule context_conjI)
          apply(erule use_valid)
          apply (rule kernel_entry_if_invs,simp)
          apply (subgoal_tac "idle_equiv s0_internal ba")
          prefer 2
          apply (erule use_valid)
          apply (rule kernel_entry_if_idle_equiv)
          apply simp
          apply (simp add: idle_equiv_context_equiv)
          apply (frule use_valid[OF _ kernel_entry_context],simp)
          apply (frule use_valid[OF _ kernel_entry_if_det_inv'])
           apply simp
          apply (simp split: unit.splits)
          apply (erule use_valid)
           apply (rule current_aag_lift)
            apply (wp hoare_vcg_const_imp_lift kernel_entry_if_invs
                      kernel_entry_silc_inv[where st'=s0_internal]
                      kernel_entry_pas_refined[where st=s0_internal]
                      kernel_entry_if_valid_sched kernel_entry_if_only_timer_irq_inv
                      kernel_entry_if_domain_sep_inv kernel_entry_if_guarded_pas_domain
                      kernel_entry_if_domain_time_sched_action
                      ct_idle_lift
                   | clarsimp intro: guarded_pas_is_subject_current_aag
                   | wp kernel_entry_if_domain_fields)+
          apply (rule conjI, fastforce intro!: active_from_running)
          apply (simp add: schact_is_rct_def)
          apply (rule guarded_pas_is_subject_current_aag,assumption+)
         apply (simp_all only: silc_inv_cur pas_refined_cur guarded_pas_domain_cur)
         apply(simp | elim exE)+
         apply (elim exE conjE)
         apply (clarsimp simp add: kernel_handle_preemption_if_def)
         apply (subgoal_tac "idle_equiv s0_internal ba \<and> invs ba")
         prefer 2
         apply (erule use_valid)
         apply (wp handle_preemption_if_invs | simp)+
         apply (clarsimp simp add: idle_equiv_context_equiv)
         apply (erule use_valid)
          apply (rule hoare_add_post[OF handle_preemption_context, OF TrueI], simp,
                 rule hoare_drop_imps)
          apply (wp handle_preemption_if_invs handle_preemption_if_domain_sep_inv
                    handle_preemption_if_domain_time_sched_action
                    handle_preemption_if_det_inv ct_idle_lift)
         apply (fastforce simp: non_kernel_IRQs_def)
        apply (simp add: kernel_schedule_if_def | elim exE conjE)+
        apply (erule use_valid)
         apply ((wp schedule_if_ct_running_or_ct_idle schedule_if_domain_time_nonzero'
                    schedule_if_domain_time_nonzero schedule_if_det_inv hoare_false_imp
                 | fastforce simp: invs_valid_idle)+)[2]
       apply (simp add: kernel_exit_A_if_def | elim exE conjE)+
       apply (frule state_unchanged[OF kernel_exit_if_inv])
       apply (frule use_valid[OF _ kernel_exit_if_det_inv])
        apply simp
       apply(clarsimp)
       apply (elim disjE)
        apply (simp add: ct_active_not_idle')+
       apply (erule use_valid[OF _ exit_idle_context],simp+)
      apply(simp add: do_user_op_A_if_def check_active_irq_A_if_def | elim exE conjE)+
      apply (frule use_valid[OF _ do_user_op_if_det_inv])
       apply (frule use_valid[OF _ check_active_irq_if_User_det_inv])
        apply simp
       apply simp
       apply (erule use_valid[OF _ check_active_irq_if_wp])
       apply simp
      apply simp
      apply(erule use_valid, erule use_valid[OF _ check_active_irq_if_wp])
       apply(rule_tac Q="\<lambda>a. (invs and ct_running) and (\<lambda>b.
                 valid_pdpt_objs b \<and>
                 valid_list b \<and>
                 valid_sched b \<and>
                 only_timer_irq_inv timer_irq s0_internal b \<and>
                 silc_inv initial_aag s0_internal b \<and>
                 pas_refined initial_aag b \<and>
                 guarded_pas_domain initial_aag b \<and>
                 idle_equiv s0_internal b \<and>
                 domain_sep_inv False s0_internal b \<and>
                 valid_domain_list b \<and> 0 < domain_time b \<and>
                 scheduler_action b = resume_cur_thread)" in hoare_strengthen_post)

        apply((wp do_user_op_if_invs ct_idle_lift
              | simp add: ct_active_not_idle' | clarsimp)+)[2]
      apply(erule use_valid[OF _ check_active_irq_if_wp])
      apply(simp add: ct_in_state_def)
     apply(simp add: do_user_op_A_if_def check_active_irq_A_if_def
           | elim exE conjE)+
     apply (frule use_valid[OF _ do_user_op_if_det_inv])
      apply (frule use_valid[OF _ check_active_irq_if_User_det_inv])
       apply simp
      apply simp
      apply (erule use_valid[OF _ check_active_irq_if_wp])
      apply simp
     apply simp
     apply(erule use_valid, erule use_valid[OF _ check_active_irq_if_wp])
      apply(rule_tac Q="\<lambda>a. (invs and ct_running) and (\<lambda>b.
                 valid_pdpt_objs b \<and>
                 valid_list b \<and>
                 valid_sched b \<and>
                 only_timer_irq_inv timer_irq s0_internal b \<and>
                 silc_inv initial_aag s0_internal b \<and>
                 pas_refined initial_aag b \<and>
                 guarded_pas_domain initial_aag b \<and>
                 idle_equiv s0_internal b \<and>
                 domain_sep_inv False s0_internal b \<and>
                 valid_domain_list b \<and> 0 < domain_time b \<and>
                 scheduler_action b = resume_cur_thread)" in hoare_strengthen_post)
       apply((wp do_user_op_if_invs | simp | clarsimp simp: ct_active_not_idle')+)[2]
     apply(erule use_valid[OF _ check_active_irq_if_wp])
     apply(simp add: ct_in_state_def)
    apply(simp add: check_active_irq_A_if_def | elim exE conjE)+
    apply (frule use_valid[OF _ check_active_irq_if_User_det_inv])
     apply simp
    apply simp
    apply(erule use_valid[OF _ check_active_irq_if_wp])
    apply(clarsimp simp add: ct_in_state_def st_tcb_at_def obj_at_def)
   apply(simp add: check_active_irq_A_if_def | elim exE conjE)+
   apply (frule use_valid[OF _ check_active_irq_context],simp)
   apply (frule use_valid[OF _ check_active_irq_if_Idle_det_inv])
    apply simp
   apply simp
   apply(erule use_valid[OF _ check_active_irq_if_wp])
   apply(simp add: ct_in_state_def idle_context_def)
  apply(simp add: check_active_irq_A_if_def | elim exE conjE)+
  apply (frule use_valid[OF _ check_active_irq_if_Idle_det_inv])
   apply simp
  apply simp
  apply(rule use_valid[OF _ check_active_irq_if_wp],assumption)
  apply(simp add: ct_in_state_def)
  apply (frule use_valid[OF _ check_active_irq_context],simp+)
  apply (simp add: idle_context_def)
  done


lemma Fin_ADT_if:
  "Fin (ADT_A_if utf) = id"
  apply (simp add: ADT_A_if_def)
  done


lemma Init_ADT_if:
  "Init (ADT_A_if utf) = (\<lambda>s. {s} \<inter> full_invs_if \<inter> {s. step_restrict s})"
  apply (simp add: ADT_A_if_def)
  done

lemma execution_invs:
 assumes e: "s \<in> execution (ADT_A_if utf) s0 js"
 shows "invs_if s"
  apply (insert e)
  apply (induct js arbitrary: s rule: rev_induct)
   apply (clarsimp simp add: execution_def Fin_ADT_if Init_ADT_if
                             image_def)
   apply (simp add: execution_def Fin_ADT_if Init_ADT_if steps_def)
  apply (simp add: execution_def steps_def image_def)
  apply (erule bexE)
  unfolding Image_def
  apply (drule CollectD)
  apply (erule bexE)
   apply simp
  apply (rule invs_if_Step_ADT_A_if)
   apply (drule_tac meta_spec)
   apply (fastforce)
  apply simp
  apply (clarsimp simp: Fin_ADT_if ADT_A_if_def)
  done

lemma execution_restrict:
 assumes e: "s \<in> execution (ADT_A_if utf) s0 js"
 shows "step_restrict s"
  apply (insert e)
  apply (induct js arbitrary: s rule: rev_induct)
  apply (clarsimp simp add: execution_def ADT_A_if_def steps_def)
  apply (clarsimp simp add: execution_def Fin_ADT_if Init_ADT_if steps_def)
  apply (simp add: ADT_A_if_def)
  done

lemma invs_if_full_invs_if:
  "invs_if s \<Longrightarrow> s \<in> full_invs_if"
  by (clarsimp simp add: full_invs_if_def invs_if_def Invs_def)

lemma ADT_A_if_Step_system:
  "Step_system (ADT_A_if utf) s0"
  apply(rule Init_Fin_system_Step_system)
  apply(rule Init_inv_Fin_system_Init_Fin_system)
  apply(clarsimp simp add: Init_inv_Fin_system_def ADT_A_if_def invs_if_full_invs_if
                  system.reachable_def extras_s0)
  apply (frule execution_invs[simplified ADT_A_if_def])
  apply (frule execution_restrict[simplified ADT_A_if_def])
  apply (frule invs_if_full_invs_if,force)
  done

lemma ADT_A_if_Run_reachable:
  "(s0, t) \<in> Run (system.Step (ADT_A_if utf)) as \<Longrightarrow> system.reachable (ADT_A_if utf) s0 t"
  apply(simp add: system.reachable_def)
  apply(simp add: Step_system_execution_Run_s0[OF ADT_A_if_Step_system])
  by blast

lemma Step_ADT_A_if:
  "system.reachable (ADT_A_if utf) s0 s \<Longrightarrow>
     ((s,s') \<in> system.Step (ADT_A_if utf) u) = ((s,s') \<in> Step (ADT_A_if utf) u)"
  apply (simp add: system.reachable_def)
  apply (clarsimp)
  apply (frule execution_invs)
  apply (frule invs_if_full_invs_if)
  apply (frule execution_restrict)
  apply(simp add: system.Step_def execution_def steps_def ADT_A_if_def)
  done

lemma Step_ADT_A_if':
  "((s,s') \<in> system.Step (ADT_A_if utf) u) \<Longrightarrow> ((s,s') \<in> Step (ADT_A_if utf) u)"
  apply(simp add: system.Step_def execution_def steps_def ADT_A_if_def)
  apply fastforce
  done

lemma ADT_A_if_reachable_invs_if:
  "system.reachable (ADT_A_if utf) s0 s \<Longrightarrow> invs_if s"
  apply(clarsimp simp: system.reachable_def)
  apply (erule execution_invs)
  done

lemma ADT_A_if_reachable_full_invs_if:
  "system.reachable (ADT_A_if utf) s0 s \<Longrightarrow> s \<in> full_invs_if"
  apply(clarsimp simp: system.reachable_def)
  apply (rule invs_if_full_invs_if)
  apply (rule ADT_A_if_reachable_invs_if)
  apply (simp add: system.reachable_def)
  apply force
  done


lemma ADT_A_if_enabled_Step_system:
  "enabled_Step_system (ADT_A_if utf) s0"
  apply(simp add: enabled_Step_system_def ADT_A_if_Step_system ADT_A_if_enabled_system)
  done

section \<open>IRQs and big step automaton enabledness\<close>

definition irq_measure_if
where
  "irq_measure_if s \<equiv>
   let cur = Suc (irq_state (machine_state s)) in
     (next_irq_state cur (irq_masks (machine_state s))) - cur"

definition measuref_if :: "det_state global_sys_state \<Rightarrow> det_state global_sys_state \<Rightarrow> nat"
where
  "measuref_if s s' \<equiv>
     (if (snd s) = KernelExit then
        (if interrupted_modes (snd s') then 0
         else 1 + (4 * irq_measure_if (internal_state_if s')) +
              (case (snd s') of (KernelEntry e) \<Rightarrow> 3 |
               _ \<Rightarrow>
                    (if (\<exists> b. (snd s') = KernelSchedule b) then 2
                     else (if (snd s') = KernelExit then 1 else 0)
                    )
              )
        )
      else
        (if interrupted_modes (snd s') then 2 else
           (if (\<exists> b. (snd s') = KernelSchedule b) then 1 else 0)
        )
     )"

crunch irq_state_of_state_inv[wp]: device_memory_update "\<lambda>ms. P (irq_state ms)"
crunch irq_masks_inv[wp]: device_memory_update "\<lambda>ms. P (irq_masks ms)"
  (wp: crunch_wps simp: crunch_simps no_irq_device_memory_update no_irq_def)

lemma do_user_op_if_irq_state_of_state:
  "\<lbrace>\<lambda>s. P (irq_state_of_state s)\<rbrace> do_user_op_if utf uc
   \<lbrace>\<lambda>_ s. P (irq_state_of_state s)\<rbrace>"
  apply(rule hoare_pre)
  apply(simp add: do_user_op_if_def user_memory_update_def | wp dmo_wp select_wp | wpc)+
  done

lemma do_user_op_if_irq_masks_of_state:
  "\<lbrace>\<lambda>s. P (irq_masks_of_state s)\<rbrace> do_user_op_if utf uc
   \<lbrace>\<lambda>_ s. P (irq_masks_of_state s)\<rbrace>"
  apply(rule hoare_pre)
  apply(simp add: do_user_op_if_def user_memory_update_def | wp dmo_wp select_wp | wpc)+
  done

lemma do_user_op_if_irq_measure_if:
  "\<lbrace>\<lambda>s. P (irq_measure_if s)\<rbrace> do_user_op_if utf uc
   \<lbrace>\<lambda>_ s. P (irq_measure_if s)\<rbrace>"
  apply(rule hoare_pre)
  apply(simp add: do_user_op_if_def user_memory_update_def irq_measure_if_def
    | wps |wp dmo_wp select_wp | wpc)+
  done

lemma next_irq_state_Suc:
  "\<lbrakk>irq_at cur masks = None; next_irq_state_dom (cur,masks)\<rbrakk> \<Longrightarrow>
   next_irq_state (Suc cur) masks = next_irq_state cur masks"
  apply(simp add: next_irq_state.psimps split: if_splits)
  done

lemma next_irq_state_Suc':
  "\<lbrakk>irq_at cur masks = Some i; next_irq_state_dom (cur,masks)\<rbrakk> \<Longrightarrow>
   next_irq_state cur masks = cur"
  apply(simp add: next_irq_state.psimps split: if_splits)
  done

lemma getActiveIRQ_None:
  "(None,s') \<in> fst (do_machine_op (getActiveIRQ in_kernel) s)  \<Longrightarrow>
   irq_at (irq_state (machine_state s) + 1) (irq_masks (machine_state s)) = None"
  apply(erule use_valid)
   apply(wp dmo_getActiveIRQ_wp)
  by simp

lemma getActiveIRQ_Some:
  "(Some i,s') \<in> fst (do_machine_op (getActiveIRQ in_kernel) s)  \<Longrightarrow>
   irq_at (irq_state (machine_state s) + 1) (irq_masks (machine_state s)) = Some i"
  apply(erule use_valid)
   apply(wp dmo_getActiveIRQ_wp)
  by simp

lemma is_irq_at_next_irq_state_dom':
  "is_irq_at s irq pos \<Longrightarrow>
   next_irq_state_dom (pos,irq_masks (machine_state s))"
  apply(rule next_irq_state.domintros)
  apply(fastforce simp: is_irq_at_def irq_at_def)
  done

lemma is_irq_at_next_irq_state_dom:
  "\<lbrakk>pos \<le> next; is_irq_at s irq next\<rbrakk> \<Longrightarrow>
   next_irq_state_dom (pos,irq_masks (machine_state s))"
  apply(induct rule: inc_induct)
   apply(erule is_irq_at_next_irq_state_dom')
  apply(rule next_irq_state.domintros)
  apply(blast)
  done

lemma is_irq_at_next_irq_state:
  "is_irq_at s irq pos \<Longrightarrow>
   next_irq_state pos (irq_masks (machine_state s)) = pos"
  apply(subst next_irq_state.psimps[OF is_irq_at_next_irq_state_dom'])
   apply assumption
  apply(fastforce simp: is_irq_at_def)
  done

lemma next_irq_state_le:
  "\<lbrakk>irq_is_recurring irq s; masks = (irq_masks (machine_state s))\<rbrakk> \<Longrightarrow>
   cur \<le> next_irq_state cur masks"
  apply(clarsimp simp: irq_is_recurring_def)
  apply(drule_tac x=cur in spec)
  apply(erule exE)
  proof -
    fix m
    assume i: "is_irq_at s irq (cur + m)"
    have le: "cur \<le> cur + m" by simp
    thus "cur \<le> next_irq_state cur (irq_masks (machine_state s))"
      apply -
      apply(induct rule: inc_induct)
       apply(clarsimp simp: is_irq_at_next_irq_state[OF i])
      apply(case_tac "is_irq_at s irq n")
       apply(simp add: is_irq_at_next_irq_state)
      apply(subst next_irq_state.psimps)
       apply(rule is_irq_at_next_irq_state_dom[OF _ i])
       apply simp
      apply simp
      done
  qed

lemma next_irq_state_mono:
  assumes lep: "pos \<le> pos'"
  assumes recur: "irq_is_recurring irq s"
  assumes m: "masks = irq_masks (machine_state s)"
  shows
   "next_irq_state pos masks \<le> next_irq_state pos' masks"
  apply(insert recur m)
  apply(clarsimp simp: irq_is_recurring_def)
  apply(drule_tac x=pos' in spec)
  apply(erule exE)
  proof -
    fix m
    assume i: "is_irq_at s irq (pos' + m)"
    from lep have le: "pos \<le> pos' + m" by fastforce
    from lep show "next_irq_state pos (irq_masks (machine_state s)) \<le>
                      next_irq_state pos' (irq_masks (machine_state s))"
      apply -
      apply(induct rule: inc_induct)
       apply simp
      apply(case_tac "is_irq_at s irq n")
       apply(simp add: is_irq_at_next_irq_state)
       apply(rule less_imp_le_nat)
       apply(erule less_le_trans)
       apply(blast intro: next_irq_state_le[OF recur])
      apply(subst next_irq_state.psimps)
       apply(rule is_irq_at_next_irq_state_dom[OF _ i])
       apply simp
      apply(clarsimp simp: is_irq_at_def irq_at_def Let_def)
      apply(rule less_imp_le_nat)
      apply(erule less_le_trans)
      apply(blast intro: next_irq_state_le[OF recur])
      done
  qed


lemma next_irq_state_less:
  "\<lbrakk>irq_at cur masks = None; irq_is_recurring irq s; masks = (irq_masks (machine_state s))\<rbrakk> \<Longrightarrow>
   cur < next_irq_state cur masks"
  apply(frule_tac n=cur in recurring_next_irq_state_dom)
  apply(simp add: next_irq_state.psimps)
  apply(rule less_le_trans[OF _ next_irq_state_le])
    apply simp
   apply assumption
  apply(rule refl)
  done

lemma next_irq_state_Suc_le:
  assumes recur: "irq_is_recurring irq s"
  assumes m: "masks = irq_masks (machine_state s)"
  shows
   "next_irq_state pos masks \<le> next_irq_state (Suc pos) masks"
  apply(rule next_irq_state_mono[OF _ recur m], simp)
  done

lemma kernel_exit_if_inv:
  "\<lbrace>P\<rbrace> kernel_exit_if blah \<lbrace>\<lambda>_. P\<rbrace>"
  apply(simp add: kernel_exit_if_def | wp)+
  done

lemma invs_if_irq_is_recurring[simp]:
  "invs_if s \<Longrightarrow> irq_is_recurring timer_irq (internal_state_if s)"
  apply(clarsimp simp: invs_if_def Invs_def only_timer_irq_inv_def only_timer_irq_def)
  done

definition irq_measure_if_inv where
  "irq_measure_if_inv st s \<equiv> irq_measure_if (s::det_state) \<le> irq_measure_if (st::det_state)"

definition irq_state_inv where
  "irq_state_inv (st::det_state) (s::det_state) \<equiv>
        irq_state (machine_state s) \<ge> irq_state (machine_state st) \<and>
        irq_masks (machine_state s) = irq_masks (machine_state st) \<and>
        next_irq_state (Suc (irq_state (machine_state s))) (irq_masks (machine_state s)) =
        next_irq_state (Suc (irq_state (machine_state st))) (irq_masks (machine_state s))"

lemma irq_state_inv_refl:
  "irq_state_inv s s"
  apply(simp add: irq_state_inv_def)
  done


lemma irq_state_inv_triv:
  assumes irq_state:
    "\<And> P. \<lbrace> \<lambda>s. P (irq_state_of_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (irq_state_of_state s)\<rbrace>"
  assumes irq_masks:
    "\<And> P. \<lbrace> \<lambda>s. P (irq_masks_of_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (irq_masks_of_state s)\<rbrace>"
  shows
    "\<lbrace>irq_state_inv st\<rbrace> f \<lbrace>\<lambda>_. irq_state_inv st\<rbrace>"
  apply(clarsimp simp: valid_def irq_state_inv_def)
  apply(rule use_valid[OF _ irq_state], assumption)
  apply(erule use_valid[OF _ irq_masks])
  apply simp
  done

lemma irq_state_inv_triv':
  assumes irq_state:
    "\<And> P. \<lbrace> \<lambda>s. P (irq_state_of_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (irq_state_of_state s)\<rbrace>"
  assumes irq_masks:
    "\<And> P. \<lbrace> (\<lambda>s. P (irq_masks_of_state s)) and Q\<rbrace> f \<lbrace>\<lambda>_ s. P (irq_masks_of_state s)\<rbrace>"
  shows
    "\<lbrace>irq_state_inv st and Q\<rbrace> f \<lbrace>\<lambda>_. irq_state_inv st\<rbrace>"
  apply(clarsimp simp: valid_def irq_state_inv_def)
  apply(rule use_valid[OF _ irq_state], assumption)
  apply(erule use_valid[OF _ irq_masks])
  apply simp
  done


lemma OR_choiceE_wp:
  assumes a: "\<And>s. \<lbrace>P and (=) s\<rbrace> b \<lbrace>\<lambda> r s'. (r \<longrightarrow> P' s) \<and> (\<not> r \<longrightarrow> P'' s)\<rbrace>"
  assumes b: "\<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  assumes c: "\<lbrace>P''\<rbrace> g \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  shows
  "\<lbrace>P::det_state \<Rightarrow> bool\<rbrace> OR_choiceE b f g \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  apply(simp add: OR_choiceE_def)
  apply (wp b c| wpc)+
  apply(clarsimp simp: mk_ef_def wrap_ext_bool_det_ext_ext_def)
  apply(drule a[simplified valid_def, rule_format, rotated])
   apply simp
  apply(fastforce split: prod.splits)
  done

definition irq_state_next where
  "irq_state_next (st::det_state) (s::det_state) \<equiv>
        irq_state (machine_state s) \<ge> irq_state (machine_state st) \<and>
        irq_masks (machine_state s) = irq_masks (machine_state st) \<and>
        irq_state (machine_state s) = next_irq_state (Suc (irq_state (machine_state st)))
                                                     (irq_masks (machine_state s))"


lemma preemption_point_irq_state_inv'[wp]:
  "\<lbrace>irq_state_inv st and K (irq_is_recurring irq st)\<rbrace>
   preemption_point
  \<lbrace>\<lambda>a. irq_state_inv st\<rbrace>, \<lbrace>\<lambda>_. irq_state_next st\<rbrace>"
  apply (simp add: preemption_point_def)
  apply (wp OR_choiceE_wp[where P'="irq_state_inv st and K(irq_is_recurring irq st)"
                            and P''="irq_state_inv st and K(irq_is_recurring irq st)"]
            dmo_getActiveIRQ_wp
        | wpc
        | simp add: reset_work_units_def)+
     apply (elim conjE)
     apply simp
    apply (wp OR_choiceE_wp[where P'="irq_state_inv st" and P''="irq_state_inv st"]
              dmo_getActiveIRQ_wp
          | wpc
          | simp add: reset_work_units_def)+
     apply(clarsimp simp: irq_state_inv_def)
     apply(simp add: next_irq_state_Suc[OF _ recurring_next_irq_state_dom])
     apply (clarsimp simp: irq_state_next_def)
     apply(simp add: next_irq_state_Suc'[OF _ recurring_next_irq_state_dom])

    apply(wp | simp add: update_work_units_def irq_state_inv_def | fastforce)+
     done

lemma validE_validE_E':
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f -,\<lbrace>E\<rbrace>"
  apply (rule validE_validE_E)
  apply (rule hoare_post_impErr)
  apply assumption
  apply simp+
  done

lemmas preemption_point_irq_state_inv[wp] = validE_validE_R'[OF preemption_point_irq_state_inv']
lemmas preemption_point_irq_state_next[wp] = validE_validE_E'[OF preemption_point_irq_state_inv']



lemma hoare_add_postE:
  "\<lbrakk> \<lbrace>S\<rbrace> f \<lbrace>\<lambda>_. S'\<rbrace>;
     \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. S' s \<longrightarrow> Q r s\<rbrace>,\<lbrace>\<lambda>r s. S' s \<longrightarrow> E r s\<rbrace>
   \<rbrakk> \<Longrightarrow> \<lbrace>P and S\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  apply (clarsimp simp: validE_def)
  apply (rule hoare_add_post)
    apply assumption
   apply simp
  apply (rule hoare_strengthen_post)
   apply (rule hoare_pre)
    apply assumption
   back
   apply simp
  apply (clarsimp split: sum.splits)
  done

lemma rec_del_irq_state_inv':
  notes drop_spec_valid[wp_split del] drop_spec_validE[wp_split del]
         rec_del.simps[simp del]
  shows
  "s \<turnstile> \<lbrace>irq_state_inv st and domain_sep_inv False sta and K (irq_is_recurring irq st)\<rbrace>
        rec_del call
        \<lbrace>\<lambda>a s. (case call of
             FinaliseSlotCall x y \<Rightarrow> y \<or> fst a \<longrightarrow> snd a = NullCap
          | _ \<Rightarrow> True) \<and>
         domain_sep_inv False sta s \<and> irq_state_inv st s\<rbrace>, \<lbrace>\<lambda>_. irq_state_next st\<rbrace>"
  proof (induct s arbitrary: rule: rec_del.induct, simp_all only: rec_del_fails hoare_fail_any)
  case (1 slot exposed s) show ?case
    apply(simp add: split_def rec_del.simps)
    apply(wp drop_spec_validE[OF returnOk_wp] drop_spec_validE[OF liftE_wp]
             empty_slot_domain_sep_inv)
     apply(wp irq_state_inv_triv' empty_slot_irq_masks)
    apply(rule spec_strengthen_postE[OF "1.hyps", simplified])
    apply fastforce
    done
  next
  case (2 slot exposed s) show ?case
    apply(rule hoare_spec_gen_asm)
    apply(simp add: rec_del.simps split del: if_split)
    apply(rule hoare_pre_spec_validE)
     apply(wp drop_spec_validE[OF returnOk_wp] drop_spec_validE[OF liftE_wp] set_cap_domain_sep_inv
          |simp add: split_def split del: if_split)+
         apply(wp irq_state_inv_triv)[1]
        apply (wp | simp split del: if_split)+
           apply(rule spec_strengthen_postE)
            apply(rule "2.hyps"[simplified], fastforce+)
          apply(rule drop_spec_validE, (wp preemption_point_irq_state_inv[where irq=irq]
                                       | simp)+)[1]
         apply(rule spec_strengthen_postE)
          apply(rule "2.hyps"[simplified], fastforce+)
         apply(wp  finalise_cap_domain_sep_inv_cap get_cap_wp
                   finalise_cap_returns_NullCap[where irqs=False, simplified]
                   drop_spec_validE[OF liftE_wp] set_cap_domain_sep_inv
               |simp add: without_preemption_def split del: if_split
               |wp (once) hoare_drop_imps
               |wp irq_state_inv_triv)+
    apply(blast dest: cte_wp_at_domain_sep_inv_cap)
    done
  next
  case (3 ptr bits n slot s) show ?case
    apply(simp add: rec_del.simps)
    apply (wp drop_spec_validE[OF returnOk_wp] drop_spec_validE[OF liftE_wp] irq_state_inv_triv)
    apply(rule hoare_pre_spec_validE)
    apply (wp drop_spec_validE[OF assertE_wp])
    apply(fastforce)
    done
  next
  case (4 ptr bits n slot s) show ?case
    apply(simp add: rec_del.simps)
    apply (wp drop_spec_validE[OF returnOk_wp] drop_spec_validE[OF liftE_wp] set_cap_domain_sep_inv
              drop_spec_validE[OF assertE_wp] get_cap_wp
          | simp add: without_preemption_def
          | wp irq_state_inv_triv)+
    apply (rule spec_strengthen_postE[OF "4.hyps", simplified])
     apply(simp add: returnOk_def return_def)
    apply(clarsimp simp: domain_sep_inv_cap_def)
    done
  qed

lemma rec_del_irq_state_inv:
  "\<lbrace>irq_state_inv st and domain_sep_inv False sta and K (irq_is_recurring irq st)\<rbrace>
    rec_del call
        \<lbrace>\<lambda>a s. irq_state_inv st s\<rbrace>, \<lbrace>\<lambda>_. irq_state_next st\<rbrace>"
  apply(rule hoare_post_impErr)
   apply(rule use_spec)
   apply(rule rec_del_irq_state_inv')
   apply auto
  done

lemma cap_delete_irq_state_inv':
  "\<lbrace>irq_state_inv st and domain_sep_inv False sta and K (irq_is_recurring irq st)\<rbrace>
   cap_delete slot
   \<lbrace>\<lambda>_. irq_state_inv st\<rbrace>, \<lbrace>\<lambda>_. irq_state_next st\<rbrace>"
  apply(simp add: cap_delete_def | wp rec_del_irq_state_inv)+
  by auto

lemmas cap_delete_irq_state_inv[wp] = validE_validE_R'[OF cap_delete_irq_state_inv']
lemmas cap_delete_irq_state_next[wp] = validE_validE_E'[OF cap_delete_irq_state_inv']



lemma cap_revoke_irq_state_inv'':
  notes drop_spec_valid[wp_split del] drop_spec_validE[wp_split del]
  shows
  "s \<turnstile> \<lbrace> irq_state_inv st and domain_sep_inv False sta and K (irq_is_recurring irq st)\<rbrace>
   cap_revoke slot
   \<lbrace> \<lambda>_ s. irq_state_inv st s\<rbrace>, \<lbrace>\<lambda>_. irq_state_next st\<rbrace>"
  proof(induct rule: cap_revoke.induct[where ?a1.0=s])
  case (1 slot s)
  show ?case
  apply(subst cap_revoke.simps)
  apply(rule hoare_spec_gen_asm)
  apply(rule hoare_pre_spec_validE)
   apply (wp "1.hyps")
           apply(wp spec_valid_conj_liftE2 | simp)+
           apply(wp drop_spec_validE[OF preemption_point_irq_state_inv[simplified validE_R_def]]
                    drop_spec_validE[OF preemption_point_irq_state_inv'[where irq=irq]]
                    drop_spec_validE[OF valid_validE[OF preemption_point_domain_sep_inv]]
                    cap_delete_domain_sep_inv cap_delete_irq_state_inv
                    drop_spec_validE[OF assertE_wp] drop_spec_validE[OF returnOk_wp]
                    drop_spec_validE[OF liftE_wp] select_wp
                    drop_spec_validE[OF  hoare_vcg_conj_liftE1]
                | simp | wp (once) hoare_drop_imps)+
  apply fastforce
  done
  qed

lemmas cap_revoke_irq_state_inv' = use_spec(2)[OF cap_revoke_irq_state_inv'']

lemmas cap_revoke_irq_state_inv[wp] = validE_validE_R'[OF cap_revoke_irq_state_inv']
lemmas cap_revoke_irq_state_next[wp] = validE_validE_E'[OF cap_revoke_irq_state_inv']


lemma finalise_slot_irq_state_inv:
  "\<lbrace>irq_state_inv st and domain_sep_inv False sta and K (irq_is_recurring irq st)\<rbrace>
    finalise_slot p e \<lbrace>\<lambda>_ s. irq_state_inv st s\<rbrace>,\<lbrace>\<lambda>_. irq_state_next st\<rbrace>"
  apply(simp add: finalise_slot_def | wp rec_del_irq_state_inv[folded validE_R_def])+
  by blast


lemma invoke_cnode_irq_state_inv:
  "\<lbrace>irq_state_inv st and domain_sep_inv False sta and
    valid_cnode_inv cnode_invocation and K (irq_is_recurring irq st)\<rbrace>
   invoke_cnode cnode_invocation
   \<lbrace>\<lambda>y. irq_state_inv st\<rbrace>, \<lbrace>\<lambda>_. irq_state_next st\<rbrace>"
  apply (rule hoare_assume_preE)
  apply(simp add: invoke_cnode_def)
  apply(rule hoare_pre)
   apply wpc
         apply((wp cap_revoke_irq_state_inv' cap_delete_irq_state_inv hoare_vcg_all_lift
               | wpc
               | simp add: cap_move_def split del: if_split
               | wp (once) irq_state_inv_triv
               | wp (once) hoare_drop_imps)+)[7]
  apply fastforce
  done

lemma checked_insert_irq_state_of_state[wp]:
  "\<lbrace>\<lambda> s. P (irq_state_of_state s)\<rbrace>
   check_cap_at a b
           (check_cap_at c d
             (cap_insert e f g))
          \<lbrace>\<lambda>r s. P (irq_state_of_state s)\<rbrace>"
  apply(wp | simp add: check_cap_at_def)+
  done

lemma irq_state_inv_invoke_domain[wp]:
  "\<lbrace>irq_state_inv st\<rbrace> invoke_domain a b \<lbrace>\<lambda>_. irq_state_inv st\<rbrace>"
  apply (simp add: irq_state_inv_def[abs_def])
  apply (rule hoare_pre)
   apply wps
   apply (wp | clarsimp)+
  done

crunch irq_state_of_state: bind_notification "\<lambda>s. P (irq_state_of_state s)"

lemmas bind_notification_irq_state_inv[wp] =
  irq_state_inv_triv[OF bind_notification_irq_state_of_state bind_notification_irq_masks]

crunch machine_state[wp]: set_mcpriority "\<lambda>s. P (machine_state s)"

lemma invoke_tcb_irq_state_inv:
  "\<lbrace>(\<lambda>s. irq_state_inv st s) and domain_sep_inv False sta and
    Tcb_AI.tcb_inv_wf tinv and K (irq_is_recurring irq st)\<rbrace>
   invoke_tcb tinv
   \<lbrace>\<lambda>_ s. irq_state_inv st s\<rbrace>,\<lbrace>\<lambda>_. irq_state_next st\<rbrace>"
  apply(case_tac tinv)
       apply((wp hoare_vcg_if_lift  mapM_x_wp[OF _ subset_refl]
            | wpc
            | simp split del: if_split add: check_cap_at_def
            | clarsimp
            | wp (once) irq_state_inv_triv)+)[3]
    defer
    apply((wp irq_state_inv_triv | simp )+)[2]
  (* just ThreadControl left *)
  apply (simp add: split_def cong: option.case_cong)

  by (wp hoare_vcg_all_lift_R
            hoare_vcg_all_lift hoare_vcg_const_imp_lift_R
            checked_cap_insert_domain_sep_inv
            cap_delete_deletes  cap_delete_irq_state_inv[where st=st and sta=sta and irq=irq]
            cap_delete_irq_state_next[where st=st and sta=sta and irq=irq]
            cap_delete_valid_cap cap_delete_cte_at
        |wpc
        |simp add: emptyable_def tcb_cap_cases_def tcb_cap_valid_def
                  tcb_at_st_tcb_at option_update_thread_def
        |strengthen use_no_cap_to_obj_asid_strg
        |wp (once) irq_state_inv_triv
        |wp (once) hoare_drop_imps | clarsimp split: option.splits | intro impI conjI allI)+

lemma do_reply_transfer_irq_state_inv_triv[wp]:
  "\<lbrace>irq_state_inv st\<rbrace> do_reply_transfer a b c d \<lbrace>\<lambda>_. irq_state_inv st\<rbrace>"
  apply (wp irq_state_inv_triv)
  done

lemma set_domain_irq_state_inv_triv[wp]:
  "\<lbrace>irq_state_inv st\<rbrace> set_domain a b \<lbrace>\<lambda>_. irq_state_inv st\<rbrace>"
  apply (wp irq_state_inv_triv)
  done

lemma arch_invoke_irq_control_noErr[wp]:
  "\<lbrace>\<top>\<rbrace> arch_invoke_irq_control a -,\<lbrace>Q\<rbrace>"
  apply (cases a)
  apply (wp | simp)+
  done

lemma invoke_irq_control_noErr[wp]:
  "\<lbrace>\<top>\<rbrace> invoke_irq_control a -,\<lbrace>Q\<rbrace>"
  apply (cases a)
  apply (wp | simp add: arch_invoke_irq_control_noErr)+
  done

lemma arch_perform_invocation_noErr[wp]:
  "\<lbrace>\<top>\<rbrace> arch_perform_invocation a -,\<lbrace>Q\<rbrace>"
  apply (simp add: arch_perform_invocation_def)
  apply wp
  done

lemma use_validE_E:
  "\<lbrakk>(Inl r, s') \<in> fst (fa s); \<lbrace>P\<rbrace> fa -, \<lbrace>Q\<rbrace>; P s\<rbrakk> \<Longrightarrow> Q r s'"
  apply (fastforce simp: validE_E_def validE_def valid_def)
  done


lemma irq_state_inv_trivE':
  assumes irq_state:
    "\<And> P. \<lbrace> \<lambda>s. P (irq_state_of_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (irq_state_of_state s)\<rbrace>"
  assumes irq_masks:
    "\<And> P. \<lbrace> (\<lambda>s. P (irq_masks_of_state s)) and Q\<rbrace> f \<lbrace>\<lambda>_ s. P (irq_masks_of_state s)\<rbrace>"
  assumes no_err:
    "\<And> P. \<lbrace>\<top>\<rbrace> f -,\<lbrace>P\<rbrace>"
  shows
    "\<lbrace>irq_state_inv st and Q\<rbrace> f \<lbrace>\<lambda>_. irq_state_inv st\<rbrace>, \<lbrace>\<lambda>_. irq_state_next st\<rbrace>"
  apply(clarsimp simp: validE_def valid_def irq_state_inv_def split: sum.splits)
  apply(rule use_valid[OF _ irq_state], assumption)
  apply(rule use_valid[OF _ irq_masks],assumption)
  apply clarsimp
  apply (erule use_validE_E[OF _ no_err])
  apply simp
  done

crunch irq_state_of_state[wp]: init_arch_objects "\<lambda>s. P (irq_state_of_state s)"
  (wp: crunch_wps dmo_wp ignore: do_machine_op)

lemma reset_untyped_cap_irq_state_inv:
  "\<lbrace>irq_state_inv st and K (irq_is_recurring irq st)\<rbrace>
      reset_untyped_cap slot \<lbrace>\<lambda>y. irq_state_inv st\<rbrace>, \<lbrace>\<lambda>y. irq_state_next st\<rbrace>"
  apply (cases "irq_is_recurring irq st", simp_all)
  apply (simp add: reset_untyped_cap_def)
  apply (rule hoare_pre)
   apply (wp no_irq_clearMemory mapME_x_wp'
             hoare_vcg_const_imp_lift
             preemption_point_irq_state_inv'[where irq=irq]
             get_cap_wp
     | rule irq_state_inv_triv
     | simp add: unless_def
     | wp (once) dmo_wp)+
  done

lemma invoke_untyped_irq_state_inv:
  "\<lbrace>irq_state_inv st and K (irq_is_recurring irq st)\<rbrace>
    invoke_untyped ui \<lbrace>\<lambda>y. irq_state_inv st\<rbrace>, \<lbrace>\<lambda>y. irq_state_next st\<rbrace>"
  apply (cases ui, simp add: invoke_untyped_def mapM_x_def[symmetric])
  apply (rule hoare_pre)
   apply (wp mapM_x_wp' hoare_whenE_wp
             reset_untyped_cap_irq_state_inv[where irq=irq]
     | rule irq_state_inv_triv
     | simp)+
  done

lemma perform_invocation_irq_state_inv:
   "\<lbrace>irq_state_inv st and
      (\<lambda>s. \<forall>blah.
            oper = InvokeIRQHandler blah \<longrightarrow>
             (\<exists>ptr'.
                 cte_wp_at
                 ((=) (IRQHandlerCap (irq_of_handler_inv blah)))
                 ptr' s)) and
     domain_sep_inv False sta and
     valid_invocation oper and K (irq_is_recurring irq st)\<rbrace>
   perform_invocation x y oper \<lbrace>\<lambda>_. irq_state_inv st\<rbrace>, \<lbrace>\<lambda>_. irq_state_next st\<rbrace>"
  apply(case_tac oper; simp;
    (solves \<open>(wp invoke_untyped_irq_state_inv[where irq=irq]
                 invoke_tcb_irq_state_inv invoke_cnode_irq_state_inv[simplified validE_R_def]
                 irq_state_inv_triv
               | simp | clarsimp
               | simp add: invoke_domain_def)+\<close>)?)
   apply wp
    apply (wp irq_state_inv_triv' invoke_irq_control_irq_masks)
    apply clarsimp
    apply assumption
   apply auto[1]
  apply wp
   apply(wp irq_state_inv_triv' invoke_irq_handler_irq_masks | clarsimp)+
   apply assumption
  apply auto[1]
  done


lemma hoare_drop_impE:
  assumes a: "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  shows "\<lbrace>P\<rbrace> f \<lbrace>\<lambda> r s. R r s \<longrightarrow> Q r s\<rbrace>,\<lbrace>E\<rbrace>"
  using assms apply(fastforce simp: validE_def valid_def split: sum.splits)
  done

lemma handle_invocation_irq_state_inv:
   "\<lbrace>invs and domain_sep_inv False sta and irq_state_inv st and K (irq_is_recurring irq st)\<rbrace>
    handle_invocation x y \<lbrace>\<lambda>_. irq_state_inv st\<rbrace>, \<lbrace>\<lambda>_. irq_state_next st\<rbrace>"
  apply (simp add: handle_invocation_def ts_Restart_case_helper split_def
                   liftE_liftM_liftME liftME_def bindE_assoc
              split del: if_split)
  apply(wp syscall_valid)
         apply ((wp irq_state_inv_triv | wpc | simp)+)[2]
       apply(wp static_imp_wp perform_invocation_irq_state_inv hoare_vcg_all_lift
                hoare_vcg_ex_lift decode_invocation_IRQHandlerCap
            | wpc
            | wp (once) hoare_drop_imps
            | simp split del: if_split
            | wp (once) irq_state_inv_triv)+
  apply fastforce
  done

lemma handle_event_irq_state_inv:
  "event \<noteq> Interrupt \<Longrightarrow>
   \<lbrace>irq_state_inv st and invs and domain_sep_inv False sta and K (irq_is_recurring irq st)\<rbrace>
   handle_event event \<lbrace>\<lambda>_. irq_state_inv st\<rbrace>, \<lbrace>\<lambda>_. irq_state_next st\<rbrace>"
  apply(case_tac event; simp)
      apply(rename_tac syscall)
      apply(case_tac syscall)
      apply simp_all
             apply ((simp add: handle_send_def handle_call_def
                    | wp handle_invocation_irq_state_inv[where sta=sta and irq=irq]
                         irq_state_inv_triv[OF handle_recv_irq_state_of_state]
                         irq_state_inv_triv[OF handle_reply_irq_state_of_state])+)
       apply (wp irq_state_inv_triv hy_inv | simp)+
  done

lemma schedule_if_irq_state_inv:
  "\<lbrace>irq_state_inv st\<rbrace> schedule_if tc \<lbrace>\<lambda>_. irq_state_inv st\<rbrace>"
  by (wp irq_state_inv_triv
     | simp add: schedule_if_def activate_thread_def arch_activate_idle_thread_def
     | wpc
     | wp (once) hoare_drop_imps)+

lemma irq_measure_if_inv:
  assumes irq_state:
    "\<And> st. \<lbrace>P st\<rbrace> f \<lbrace>\<lambda>_. irq_state_inv st\<rbrace>,-"
  shows
    "\<lbrace>\<lambda>s. irq_measure_if_inv st s \<and> (irq_state_inv s s \<longrightarrow> P s s)\<rbrace> f \<lbrace>\<lambda>_. irq_measure_if_inv st\<rbrace>,-"
  apply (clarsimp simp: valid_def validE_R_def validE_def)
  apply (simp add: irq_measure_if_inv_def)
  apply (erule order_trans[rotated])
  apply (simp add: irq_state_inv_refl)
  apply (drule use_validE_R, rule irq_state, assumption)
  apply (simp add: irq_state_inv_def irq_measure_if_inv_def Let_def
                   irq_measure_if_def)
  apply auto
  done

lemma irq_measure_if_inv_old:
  assumes irq_state:
    "\<And> st. \<lbrace>irq_state_inv st and Q\<rbrace> f \<lbrace>\<lambda>_. irq_state_inv st\<rbrace>,-"
  shows
    "\<lbrace>irq_measure_if_inv st and Q\<rbrace> f \<lbrace>\<lambda>_. irq_measure_if_inv st\<rbrace>,-"
  by (wpsimp wp: irq_measure_if_inv irq_state)

lemma irq_measure_if_inv':
  assumes irq_state:
    "\<And> st. \<lbrace>P st\<rbrace> f \<lbrace>\<lambda>_. irq_state_inv st\<rbrace>"
  shows
    "\<lbrace>\<lambda>s. irq_measure_if_inv st s \<and> (irq_state_inv s s \<longrightarrow> P s s)\<rbrace> f \<lbrace>\<lambda>_. irq_measure_if_inv st\<rbrace>"
  apply(clarsimp simp: valid_def irq_measure_if_inv_def irq_state_inv_refl)
  apply(erule le_trans[rotated])
  apply(drule(1) use_valid[OF _ irq_state])
  apply(clarsimp simp: irq_measure_if_def Let_def irq_state_inv_def)
  apply auto
  done

lemma irq_measure_if_inv_old':
  assumes irq_state:
    "\<And> st. \<lbrace>irq_state_inv st and Q\<rbrace> f \<lbrace>\<lambda>_. irq_state_inv st\<rbrace>"
  shows
    "\<lbrace>irq_measure_if_inv st and Q\<rbrace> f \<lbrace>\<lambda>_. irq_measure_if_inv st\<rbrace>"
  by (wpsimp wp: irq_measure_if_inv' irq_state)

lemma irq_state_inv_irq_is_recurring:
  "irq_state_inv sta s \<Longrightarrow>
     irq_is_recurring irq sta = irq_is_recurring irq s"
  apply(clarsimp simp: irq_is_recurring_def irq_state_inv_def is_irq_at_def)
  done

abbreviation next_irq_state_of_state where
  "next_irq_state_of_state s \<equiv>
     next_irq_state (Suc (irq_state_of_state s)) (irq_masks_of_state s)"

lemma kernel_entry_if_next_irq_state_of_state:
  "\<lbrakk>event \<noteq> Interrupt; invs i_s; domain_sep_inv False st i_s; irq_is_recurring irq i_s;
    ((Inr (), a), b) \<in> fst (kernel_entry_if event uc i_s)\<rbrakk>
  \<Longrightarrow> next_irq_state_of_state b = next_irq_state_of_state i_s"
  apply(simp add: kernel_entry_if_def in_bind in_return | elim conjE exE)+
  apply(erule use_validE_R)
   apply(rule_tac Q'="\<lambda>_. irq_state_inv i_s" in hoare_post_imp_R)
   apply (rule validE_validE_R')
    apply(rule handle_event_irq_state_inv[where sta=st and irq=irq] | simp)+
   apply(clarsimp simp: irq_state_inv_def)
  apply (simp add: arch_tcb_update_aux2)
  apply(erule_tac f="thread_set (tcb_arch_update (arch_tcb_context_set uc)) t" in use_valid)
   apply(wpsimp wp: irq_measure_if_inv' irq_state_inv_triv thread_set_invs_trivial
                    irq_is_recurring_triv[where Q="\<top>"]
              simp: ran_tcb_cap_cases tcb_arch_ref_def)+
  apply(erule use_valid)
   apply (wp | simp )+
  apply(simp add: irq_state_inv_def)
  done

lemma kernel_entry_if_next_irq_state_of_state_next:
  "\<lbrakk>event \<noteq> Interrupt; invs i_s; domain_sep_inv False st i_s; irq_is_recurring irq i_s;
    ((Inl r, a), b) \<in> fst (kernel_entry_if event uc i_s)\<rbrakk>
  \<Longrightarrow> irq_state_of_state b = next_irq_state_of_state i_s"
  apply(simp add: kernel_entry_if_def in_bind in_return | elim conjE exE)+
  apply(erule use_validE_E)
   apply (rule validE_validE_E)
   apply (rule hoare_post_impErr)
     apply (rule handle_event_irq_state_inv[where sta=st and irq=irq and st=i_s])
     apply simp+
   apply (simp add: irq_state_next_def)
  apply (simp add: arch_tcb_update_aux2)
  apply(erule_tac f="thread_set (tcb_arch_update (arch_tcb_context_set uc)) t" in use_valid)
   apply(wpsimp wp: irq_measure_if_inv' irq_state_inv_triv
                    thread_set_invs_trivial irq_is_recurring_triv[where Q="\<top>"]
              simp: ran_tcb_cap_cases tcb_arch_ref_def)+
  apply(erule use_valid)
   apply (wp | simp )+
  apply(simp add: irq_state_inv_def)
  done

lemma kernel_entry_if_irq_measure:
  "\<lbrakk>event \<noteq> Interrupt; invs i_s; domain_sep_inv False st i_s; irq_is_recurring irq i_s\<rbrakk>
   \<Longrightarrow> ((Inr (), a), b) \<in> fst (kernel_entry_if event uc i_s)
  \<Longrightarrow> irq_measure_if b \<le> irq_measure_if i_s"
 apply (fold irq_measure_if_inv_def)
  apply (rule mp)
   apply (erule_tac P="(=) i_s" and Q="\<lambda>rv s. (isRight (fst rv)) \<longrightarrow> Q s" for Q in use_valid)
    apply (simp_all add: isRight_def)
  apply (simp add: kernel_entry_if_def)
  apply (rule hoare_pre, wp)
     apply (rule validE_cases_valid, simp)
     apply (wp irq_measure_if_inv handle_event_irq_state_inv[THEN validE_validE_R'])+
    apply(wpsimp wp: irq_measure_if_inv' irq_state_inv_triv
                    thread_set_invs_trivial irq_is_recurring_triv[where Q="\<top>"]
              simp: ran_tcb_cap_cases arch_tcb_update_aux2 tcb_arch_ref_def
                    irq_state_inv_refl)+
  apply(simp add: irq_measure_if_inv_def)
  done


lemma schedule_if_irq_measure_if:
  "(r, b) \<in> fst (schedule_if uc i_s)
  \<Longrightarrow> irq_measure_if b \<le> irq_measure_if i_s"
  apply(fold irq_measure_if_inv_def)
  apply(erule use_valid[OF _ irq_measure_if_inv'] | wp schedule_if_irq_state_inv | simp)+
  apply(simp add: irq_measure_if_inv_def)
  done

lemma schedule_if_next_irq_state_of_state:
  "(r, b) \<in> fst (schedule_if uc i_s)
  \<Longrightarrow> next_irq_state_of_state b = next_irq_state_of_state i_s"
  apply(erule use_valid)
   apply(rule_tac Q="\<lambda>_. irq_state_inv i_s" in hoare_strengthen_post)
    apply(wp schedule_if_irq_state_inv)
   apply(auto simp: irq_state_inv_def)
  done

lemma next_irq_state_of_state_triv:
  assumes masks: "\<And>P. \<lbrace>\<lambda> s. P (irq_masks_of_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (irq_masks_of_state s)\<rbrace>"
  assumes sta: "\<And>P. \<lbrace>\<lambda> s. P (irq_state_of_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (irq_state_of_state s)\<rbrace>"
  shows
  "\<lbrace>\<lambda>s. P (next_irq_state_of_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (next_irq_state_of_state s)\<rbrace>"
  apply(clarsimp simp: valid_def)
  apply(frule use_valid[OF _ masks])
   apply assumption
  apply(erule use_valid[OF _ sta])
  by assumption

lemmas do_user_op_if_next_irq_state_of_state =
                  next_irq_state_of_state_triv[OF do_user_op_if_irq_masks_of_state
                                                  do_user_op_if_irq_state_of_state]

lemma interrupted_modes_KernelEntry[simp]:
  "interrupted_modes (KernelEntry e) = (e = Interrupt)"
  apply(case_tac e, simp_all)
  done

lemma rah4:
  "b < a \<Longrightarrow> 4 * (a - Suc b) + 3 < 4 * (a - b)"
  apply(rule Suc_le_lessD)
  apply (simp)
  done

lemma tranclp_s0:
  "big_step_R\<^sup>*\<^sup>* s0 s \<Longrightarrow>
   interrupted_modes (snd s) \<or> (snd s) = KernelExit"
  apply (simp only: rtranclp_def2)
  apply(erule disjE)
   apply(induct rule: tranclp.induct)
    apply (auto simp: big_step_R_def s0_def)
  done

lemma ADT_A_if_sub_big_steps_measuref_if:
  "\<lbrakk>(s',evs) \<in> sub_big_steps (ADT_A_if utf) big_step_R s; big_step_R\<^sup>*\<^sup>* s0 s\<rbrakk> \<Longrightarrow>
  measuref_if s s' > 0"
  apply(drule tranclp_s0)
  apply(erule sub_big_steps.induct)
   apply(clarsimp simp: big_step_R_def measuref_if_def)
  apply(clarsimp simp: big_step_R_def measuref_if_def split: if_splits)
   apply(case_tac ba, simp_all, case_tac bc, simp_all add: Step_ADT_A_if')
       apply(simp_all add: ADT_A_if_def global_automaton_if_def)
  done

lemma rah_simp:
  "(\<forall>b. b) = False"
  apply blast
  done

lemma ADT_A_if_Step_measure_if':
  "\<lbrakk>(s,s') \<in> data_type.Step (ADT_A_if utf) x; invs_if s;
   measuref_if y s > 0\<rbrakk>
       \<Longrightarrow> measuref_if y s' < measuref_if y s \<and>
          (\<not> interrupted_modes (snd s) \<longrightarrow> \<not> interrupted_modes (snd s') \<longrightarrow>
               next_irq_state_of_state (internal_state_if s') =
               next_irq_state_of_state (internal_state_if s))"
  apply(frule invs_if_irq_is_recurring)
  apply(case_tac s, clarsimp)
  apply(rename_tac uc i_s mode)
  apply(case_tac mode)
       apply(simp_all add: rah_simp system.Step_def execution_def steps_def ADT_A_if_def
                           global_automaton_if_def check_active_irq_A_if_def do_user_op_A_if_def
                           check_active_irq_if_def in_monad measuref_if_def
            | safe
            | split if_splits)+
                              apply(frule getActiveIRQ_None)
                              apply(erule use_valid[OF _ do_user_op_if_irq_measure_if])
                              apply(erule use_valid[OF _ dmo_getActiveIRQ_wp])
                              apply(clarsimp simp: irq_measure_if_def Let_def)
                              apply(simp add: next_irq_state_Suc recurring_next_irq_state_dom)
                              apply(blast intro: rah4[OF next_irq_state_less])
                             apply(frule getActiveIRQ_None)
                             apply(erule use_valid[OF _ do_user_op_if_next_irq_state_of_state])
                             apply(erule use_valid[OF _ dmo_getActiveIRQ_wp])
                             apply(simp add: next_irq_state_Suc recurring_next_irq_state_dom)
                            apply(clarsimp split: if_splits)
                           apply(frule getActiveIRQ_None)
                           apply(erule use_valid[OF _ do_user_op_if_irq_measure_if])
                           apply(erule use_valid[OF _ dmo_getActiveIRQ_wp])
                           apply(clarsimp simp: irq_measure_if_def Let_def)
                           apply(simp add: next_irq_state_Suc recurring_next_irq_state_dom)
                           apply(fastforce dest: next_irq_state_less)
                          apply(frule getActiveIRQ_None)
                          apply(erule use_valid[OF _ do_user_op_if_next_irq_state_of_state])
                          apply(erule use_valid[OF _ dmo_getActiveIRQ_wp])
                          apply(simp add: next_irq_state_Suc recurring_next_irq_state_dom)
                         apply(clarsimp split: if_splits)+
                      apply(frule getActiveIRQ_None)
                      apply(erule use_valid[OF _ dmo_getActiveIRQ_wp])
                      apply(clarsimp simp: irq_measure_if_def Let_def)
                      apply(simp add: next_irq_state_Suc recurring_next_irq_state_dom)
                      apply(fastforce dest: next_irq_state_less)
                     apply(frule getActiveIRQ_None)
                     apply(erule use_valid[OF _ dmo_getActiveIRQ_wp])
                     apply(simp add: next_irq_state_Suc recurring_next_irq_state_dom)
                    apply(clarsimp split: if_splits)
                   apply(clarsimp simp: kernel_call_A_if_def kernel_entry_if_def in_monad)
                  apply(clarsimp split: if_splits)
                 apply(rule Suc_le_lessD)
                 apply simp
                 apply(simp add: kernel_call_A_if_def)
                 apply(elim exE conjE)
                 apply(rule_tac event=x3 in kernel_entry_if_irq_measure)
                     apply((simp add: invs_if_def Invs_def only_timer_irq_inv_def
                           | elim conjE | assumption)+)[4]
                 apply(simp)
                apply(simp add: kernel_call_A_if_def | elim conjE exE)+
                apply(erule kernel_entry_if_next_irq_state_of_state)
                    apply((simp add: invs_if_def Invs_def only_timer_irq_inv_def
                          | elim conjE | assumption)+)[4]

               apply(clarsimp split: if_splits)
              apply(rule Suc_le_lessD)
              apply(simp add: kernel_schedule_if_def)
              apply(blast intro: schedule_if_irq_measure_if)
             apply(simp add: kernel_schedule_if_def)
             apply(blast intro: schedule_if_next_irq_state_of_state)
            apply(simp add: kernel_schedule_if_def)
            apply(blast intro: schedule_if_next_irq_state_of_state)
           apply(clarsimp simp: kernel_exit_A_if_def split: if_splits)
          apply(clarsimp simp: kernel_exit_A_if_def)
          apply((erule use_valid, wp | simp)+)[1]
         apply(clarsimp split: if_splits)
        apply(clarsimp simp: kernel_exit_A_if_def split: if_splits)
       apply(clarsimp simp: kernel_exit_A_if_def)
       apply((erule use_valid, wp | simp)+)[1]
      apply(clarsimp split: if_splits)+
    apply(clarsimp split: sys_mode.splits | safe)+
       apply(clarsimp simp: irq_measure_if_def kernel_exit_A_if_def split: if_splits)
       apply(drule state_unchanged[OF kernel_exit_if_inv], simp)
      apply(clarsimp simp: irq_measure_if_def kernel_exit_A_if_def split: if_splits)
      apply(drule state_unchanged[OF kernel_exit_if_inv], simp)
     apply(clarsimp simp: kernel_exit_A_if_def split: if_splits)
    apply(clarsimp simp: kernel_exit_A_if_def split: if_splits)
   apply(clarsimp simp: kernel_exit_A_if_def)
   apply((erule use_valid, wp | simp)+)[1]
  apply(clarsimp simp: kernel_exit_A_if_def split: if_splits)
  done

lemma ADT_A_if_Step_measure_if'':
  "\<lbrakk>(s,s') \<in> data_type.Step (ADT_A_if utf) x; invs_if s;
   measuref_if y s > 0\<rbrakk>
       \<Longrightarrow> measuref_if y s' < measuref_if y s \<and>
          (\<not> interrupted_modes (snd s) \<longrightarrow> interrupted_modes (snd s')
            \<longrightarrow> irq_state_of_state (internal_state_if s') =
                next_irq_state_of_state (internal_state_if s))"
  apply(frule invs_if_irq_is_recurring)
  apply(case_tac s, clarsimp)
  apply(rename_tac uc i_s mode)
  apply(case_tac mode)
       apply(simp_all add: rah_simp system.Step_def execution_def steps_def ADT_A_if_def
                           global_automaton_if_def check_active_irq_A_if_def do_user_op_A_if_def
                           check_active_irq_if_def in_monad measuref_if_def
             | safe | split if_splits)+
                         apply(frule getActiveIRQ_None)
                         apply(erule use_valid[OF _ do_user_op_if_irq_measure_if])
                         apply(erule use_valid[OF _ dmo_getActiveIRQ_wp])
                         apply(clarsimp simp: irq_measure_if_def Let_def)
                         apply(simp add: next_irq_state_Suc recurring_next_irq_state_dom)
                         apply(blast intro: rah4[OF next_irq_state_less])
                        apply(frule getActiveIRQ_None)
                        apply(erule use_valid[OF _ do_user_op_if_next_irq_state_of_state])
                        apply(erule use_valid[OF _ dmo_getActiveIRQ_wp])
                        apply(simp add: next_irq_state_Suc recurring_next_irq_state_dom)
                        apply(clarsimp split: if_splits)
                       apply(frule getActiveIRQ_None)
                       apply(erule use_valid[OF _ do_user_op_if_irq_measure_if])
                       apply(erule use_valid[OF _ dmo_getActiveIRQ_wp])
                       apply(clarsimp simp: irq_measure_if_def Let_def)
                       apply(simp add: next_irq_state_Suc recurring_next_irq_state_dom)
                       apply(fastforce dest: next_irq_state_less)
                      apply(frule getActiveIRQ_None)
                      apply(erule use_valid[OF _ do_user_op_if_next_irq_state_of_state])
                      apply(erule use_valid[OF _ dmo_getActiveIRQ_wp])
                      apply(simp add: next_irq_state_Suc recurring_next_irq_state_dom)
                      apply(clarsimp split: if_splits)+
                     apply (frule getActiveIRQ_Some)
                     apply(erule use_valid[OF _ dmo_getActiveIRQ_wp])
                     apply(simp add: next_irq_state_Suc' recurring_next_irq_state_dom)
                    apply(clarsimp split: if_splits)
                   apply (frule getActiveIRQ_Some)
                   apply(erule use_valid[OF _ dmo_getActiveIRQ_wp])
                   apply(simp add: next_irq_state_Suc' recurring_next_irq_state_dom)
                  apply(clarsimp split: if_splits)
                 apply(frule getActiveIRQ_None)
                 apply(erule use_valid[OF _ dmo_getActiveIRQ_wp])
                 apply(clarsimp simp: irq_measure_if_def Let_def)
                 apply(simp add: next_irq_state_Suc recurring_next_irq_state_dom)
                 apply(fastforce dest: next_irq_state_less)
                apply(clarsimp split: if_splits)

               apply(clarsimp simp: kernel_call_A_if_def in_monad)
               apply (rule kernel_entry_if_next_irq_state_of_state_next,assumption+)
                  prefer 4
                  apply fastforce
                 apply((simp add: invs_if_def Invs_def only_timer_irq_inv_def
                       | elim conjE
                       | assumption)+)[3]
              apply(clarsimp split: if_splits)

            apply(rule Suc_le_lessD)
            apply simp
            apply(simp add: kernel_call_A_if_def)
            apply(elim exE conjE)
            apply(rule_tac event=x3 in kernel_entry_if_irq_measure)
                apply((simp add: invs_if_def Invs_def only_timer_irq_inv_def
                      | elim conjE
                      | assumption)+)[4]
            apply(simp)
           apply(clarsimp split: if_splits)
          apply(rule Suc_le_lessD)
          apply(simp add: kernel_schedule_if_def)
          apply(blast intro: schedule_if_irq_measure_if)
         apply(clarsimp simp: kernel_exit_A_if_def split: if_splits)
        apply(clarsimp simp: kernel_exit_A_if_def)
        apply((erule use_valid, wp | simp)+)[1]
        apply(clarsimp split: if_splits)
       apply(clarsimp simp: kernel_exit_A_if_def split: if_splits)
      apply(clarsimp simp: kernel_exit_A_if_def)
      apply((erule use_valid, wp | simp)+)[1]
      apply(clarsimp split: if_splits)+
     apply(clarsimp simp: kernel_exit_A_if_def split: if_splits)
    apply(clarsimp split: if_splits)
   apply(clarsimp split: sys_mode.splits | safe)+
      apply(clarsimp simp: irq_measure_if_def kernel_exit_A_if_def split: if_splits)
      apply(drule state_unchanged[OF kernel_exit_if_inv], simp)
     apply(clarsimp simp: irq_measure_if_def kernel_exit_A_if_def split: if_splits)
     apply(drule state_unchanged[OF kernel_exit_if_inv], simp)
    apply(clarsimp simp: kernel_exit_A_if_def split: if_splits)
   apply(clarsimp simp: kernel_exit_A_if_def split: if_splits)
  apply(clarsimp simp: kernel_exit_A_if_def)
  apply((erule use_valid, wp | simp)+)[1]
  apply(clarsimp simp: kernel_exit_A_if_def split: if_splits)
  done

lemma invs_if_domain_sep_invs[intro]:
  "invs_if ((a,s),b) \<Longrightarrow> domain_sep_inv False s0_internal s"
  apply (simp add: invs_if_def Invs_def)
  done

lemma invs_if_invs[intro]:
  "invs_if ((a,s),b) \<Longrightarrow> invs s"
  apply (simp add: invs_if_def Invs_def)
  done

lemma kernel_exit_irq_masks[wp]:
  "\<lbrace>\<lambda>s. P (irq_masks_of_state s)\<rbrace> kernel_exit_if uc \<lbrace>\<lambda>r s. P (irq_masks_of_state s)\<rbrace>"
  apply (simp add: kernel_exit_if_def)
  apply wp
  done

lemma ADT_A_if_Step_irq_masks:
  "\<lbrakk>(s,s') \<in> data_type.Step (ADT_A_if utf) x; invs_if s\<rbrakk>
       \<Longrightarrow> irq_masks_of_state (internal_state_if s') = irq_masks_of_state (internal_state_if s)"
  apply(case_tac s, clarsimp)
  apply(rename_tac uc i_s mode)
  apply(case_tac mode)
       apply(simp_all add: rah_simp system.Step_def execution_def steps_def ADT_A_if_def
                           global_automaton_if_def check_active_irq_A_if_def do_user_op_A_if_def
                           check_active_irq_if_def in_monad measuref_if_def kernel_call_A_if_def
                           kernel_handle_preemption_if_def kernel_schedule_if_def
                           kernel_exit_A_if_def
            | safe
            | split if_splits)+
           apply (erule use_valid[OF _ do_user_op_if_irq_masks_of_state] |
                  erule use_valid[OF _ dmo_getActiveIRQ_irq_masks] |
                  erule use_valid[OF _ kernel_entry_if_irq_masks]
                  | rule refl)+
      apply fastforce
     apply (subgoal_tac "irq_masks_of_state b = irq_masks_of_state i_s",simp)
     apply (erule use_valid[OF _ kernel_entry_if_irq_masks])
     apply fastforce
    apply (erule use_valid[OF _ handle_preemption_if_irq_masks])
    apply fastforce
   apply (erule use_valid[OF _ schedule_if_irq_masks])
   apply fastforce
  apply (erule use_valid[OF _ kernel_exit_irq_masks])
  apply simp
       done


lemma steps_preserves_equivalence:
  "\<lbrakk>(s', as) \<in> sub_big_steps A R s1;
    \<forall>t t' as a. (t, as) \<in> sub_big_steps A R s1 \<longrightarrow>
                (t, t') \<in> data_type.Step A a \<longrightarrow>
                \<not> R s1 t' \<longrightarrow>
               f t = f t'
   \<rbrakk> \<Longrightarrow> f s1 = f s'"
  apply (erule sub_big_steps.induct)
  apply simp
  apply fastforce
  done

lemma step_out_equivalent:
  "\<lbrakk> (s', as) \<in> sub_big_steps A R s1;
     (s', s2) \<in> data_type.Step A a;
     g s2 = f (g s');
     \<forall>t t' as a. (t, as) \<in> sub_big_steps A R s1 \<longrightarrow>
                 (t, t') \<in> data_type.Step A a \<longrightarrow>
                 \<not> R s1 t' \<longrightarrow>
                 f (g t) = f (g t')
   \<rbrakk> \<Longrightarrow> f (g s1) = g s2"
  apply simp
  apply (erule steps_preserves_equivalence)
  apply simp+
  done



(*Clagged from Noninterference*)

lemma irq_state_back:
  "P (irq_state_of_state (internal_state_if ((a,b),c)))
     (irq_masks_of_state (internal_state_if ((a,b),c))) \<Longrightarrow>
   P (irq_state_of_state b) (irq_masks_of_state b)"
  apply simp
  done

lemma sub_big_steps_not_related:
  "(s,a) \<in> sub_big_steps A R s1 \<Longrightarrow> \<not> R s1 s"
  apply (erule sub_big_steps.cases,simp+)
  done

lemma invs_if_sub_big_steps_ADT_A_if:
  "\<lbrakk>(s', evs) \<in> sub_big_steps (ADT_A_if utf) big_step_R s; invs_if s\<rbrakk>
   \<Longrightarrow> invs_if s'"
  apply (erule sub_big_steps.induct)
   apply simp
  apply (simp add: invs_if_Step_ADT_A_if)
  done

lemma small_step_irq_state_next_irq:
  "\<lbrakk>invs_if s1;
    (s',evs) \<in> sub_big_steps (ADT_A_if utf) big_step_R s1;
    (s', s2) \<in> data_type.Step (ADT_A_if utf) a;
    big_step_R\<^sup>*\<^sup>* s0 s1; snd s1 = KernelExit; interrupted_modes (snd s2)\<rbrakk> \<Longrightarrow>
    next_irq_state_of_state (internal_state_if s1) = irq_state_of_state (internal_state_if s2)"
  apply (subgoal_tac "invs_if s'")
   apply (rule step_out_equivalent[where f="\<lambda>(states,mask). (next_irq_state (Suc states) mask,mask)"
                                     and g="\<lambda>s. (irq_state_of_state (internal_state_if s),
                                                 irq_masks_of_state (internal_state_if s))",
                                   simplified,
                                   THEN conjunct1])
      apply assumption
     apply assumption
    apply (rule conjI)
     apply (rule ADT_A_if_Step_measure_if''[THEN conjunct2,rule_format],assumption+)
       apply (rule ADT_A_if_sub_big_steps_measuref_if,assumption+)
      apply (frule sub_big_steps_not_related)
      apply (simp add: big_step_R_def)
     apply simp
    apply (rule ADT_A_if_Step_irq_masks,assumption+)
   apply clarsimp
   apply (subgoal_tac "invs_if ((a,b),ba)")
    apply (rule_tac b=b and a=a and c=ba in irq_state_back)
    apply (rule_tac b=bb and a=aa and c=bc in irq_state_back)
    apply (rule conjI)
     apply (rule sym)
     apply (rule ADT_A_if_Step_measure_if'[THEN conjunct2,rule_format],assumption+)
       apply (rule ADT_A_if_sub_big_steps_measuref_if,assumption+)
      apply (drule sub_big_steps_not_related)+
      apply (simp add: big_step_R_def)
     apply (simp add: big_step_R_def)
    apply (rule sym)
    apply (rule ADT_A_if_Step_irq_masks,assumption+)
   apply (simp add: invs_if_sub_big_steps_ADT_A_if)+
   done


(*Can probably be generalized*)
lemma small_step_to_big_step:
  assumes a:
    "\<And>s' evs. \<lbrakk> (s',evs) \<in> sub_big_steps (ADT_A_if utf) big_step_R s1;
                (s', s2) \<in> data_type.Step (ADT_A_if utf) a;
                big_step_R s1 s2
               \<rbrakk> \<Longrightarrow> S"
  assumes b: "(s1, s2) \<in> data_type.Step (big_step_ADT_A_if utf) a"
  shows "S"
  apply (insert b)
  apply (simp add: big_step_ADT_A_if_def big_step_adt_def)
  apply (erule big_steps.cases)
  apply (rule_tac s'=s' and evs=as in a)
    apply simp+
  done

lemma big_step_irq_state_next_irq:
  "\<lbrakk>invs_if s1; big_step_R\<^sup>*\<^sup>* s0 s1;
    (s1, s2) \<in> data_type.Step (big_step_ADT_A_if utf) a;
    snd s1 = KernelExit; i_s1 = internal_state_if s1; i_s2 = internal_state_if s2\<rbrakk> \<Longrightarrow>
   next_irq_state_of_state i_s1 = irq_state_of_state i_s2"
  apply simp
  apply (rule small_step_to_big_step)
  apply (rule small_step_irq_state_next_irq,(simp add: big_step_R_def)+)
  done

lemmas ADT_A_if_Step_measure_if = ADT_A_if_Step_measure_if'[THEN conjunct1]

lemmas ADT_A_if_Step_next_irq_state_of_state =
               ADT_A_if_Step_measure_if'[THEN conjunct2, rule_format]


lemma Step_ADT_A_if_def_global_automaton_if:
  "Step (ADT_A_if uop) = (\<lambda>u. global_automaton_if check_active_irq_A_if
          (do_user_op_A_if uop) kernel_call_A_if
          kernel_handle_preemption_if kernel_schedule_if
          kernel_exit_A_if \<inter>
         {(s, y). step_restrict y})"
  by(clarsimp simp: ADT_A_if_def)


lemma ADT_A_if_big_step_R_terminate:
  "rel_terminate (ADT_A_if utf) s0 big_step_R {s. invs_if s} measuref_if"
  apply(clarsimp simp: rel_terminate_def)
  apply(rule conjI)
   apply(rename_tac uc s mode as uc' s' mode' uc'' s'' mode'')
   apply(rule ADT_A_if_Step_measure_if)
     apply assumption
    apply (simp add: invs_if_sub_big_steps_ADT_A_if)
   apply(rule ADT_A_if_sub_big_steps_measuref_if)
    apply simp
   apply (simp add: ADT_A_if_def)
  apply (simp add: ADT_A_if_def)
  apply(drule tranclp_s0)
  apply(fastforce simp: measuref_if_def big_step_R_def Step_ADT_A_if
                        Step_ADT_A_if_def_global_automaton_if global_automaton_if_def
                 split: if_splits)
  done

lemma ADT_A_if_reachable_step_restrict:
  "system.reachable (ADT_A_if utf) s0 s \<Longrightarrow> step_restrict s"
  apply(clarsimp simp: system.reachable_def)
  apply (erule execution_restrict)
  done

lemma ADT_A_if_Init_inv_Fin:
  "Init_inv_Fin_system (ADT_A_if utf) s0"
  apply unfold_locales
    apply (simp add: ADT_A_if_def invs_if_full_invs_if extras_s0)
   apply (frule ADT_A_if_reachable_invs_if)
   apply (drule ADT_A_if_reachable_step_restrict)
   apply (simp add: ADT_A_if_def invs_if_full_invs_if)
  apply (simp add: ADT_A_if_def)
  done

lemma invs_if_inv_holds_ADT_A_if:
  "ADT_A_if utf [> Collect invs_if"
  by (force intro: inv_holdsI invs_if_Step_ADT_A_if)

lemma step_restrict_inv_holds_ADT_A_if:
  "ADT_A_if utf [> {s. step_restrict s}"
  apply (rule inv_holdsI)
  apply (clarsimp simp: Image_def ADT_A_if_def)
  done

lemma ADT_A_if_Init_Fin_serial_weak:
  "Init_Fin_serial_weak (ADT_A_if utf) s0 ({s. invs_if s} \<inter> {s. step_restrict s})"
  apply (rule Init_Fin_serial_weak_strengthen)
     apply (rule Init_Fin_serial.serial_to_weak[OF ADT_A_if_Init_Fin_serial])
    apply (intro inv_holds_conjI invs_if_inv_holds_ADT_A_if step_restrict_inv_holds_ADT_A_if)
   apply (clarsimp simp: invs_if_full_invs_if)
  apply (simp add: ADT_A_if_def)
  apply (insert invs_if_s0 extras_s0)
  apply blast
  done

lemma big_step_ADT_A_if_enabled_Step_system:
  "enabled_Step_system (big_step_ADT_A_if utf) s0"
  apply(simp add: big_step_ADT_A_if_def)
  apply(rule big_step_adt_enabled_Step_system)
      apply simp
     apply(fastforce simp: big_step_R_def)
    apply (rule ADT_A_if_Init_Fin_serial_weak)
   apply (rule ADT_A_if_Init_inv_Fin)
  apply (rule rel_terminate_weaken)
   apply (rule ADT_A_if_big_step_R_terminate)
  apply simp
  done

end
section \<open>Generic big step refinement\<close>
context begin interpretation Arch . (*FIXME: arch_split*)

definition internal_R
where
  "internal_R A R s s' \<equiv> R (Fin A s) (Fin A s')"

lemma invariant_holds_inv_holds:
  "A \<Turnstile> I \<Longrightarrow> A [> I"
  by (simp add: invariant_holds_def inv_holds_def)

lemma inv_holdsE:
  assumes I: "A [> I"
  and step: "(s, t) \<in> Step A e"
  and s_I: "s \<in> I"
  and t_I: "t \<in> I \<Longrightarrow> P"
  shows "P"
  apply (rule t_I)
  apply (insert step I s_I)
  apply (force simp: inv_holds_def)
  done

lemma LI_sub_big_steps:
  "\<lbrakk>(s',as) \<in> sub_big_steps C (internal_R C R) s;
    LI A C S (Ia \<times> Ic); A \<Turnstile> Ia; C \<Turnstile> Ic;
    (t, s) \<in> S; s \<in> Ic; t \<in> Ia\<rbrakk>
  \<Longrightarrow> \<exists>t'. (t',as) \<in> sub_big_steps A (internal_R A R) t \<and> (t', s') \<in> S \<and> t' \<in> Ia"
  apply (induct rule: sub_big_steps.induct)
   apply(clarsimp simp: LI_def)
   apply (rule_tac x=t in exI)
   apply clarsimp
   apply (rule sub_big_steps.nil, simp_all)[1]
   apply (force simp: internal_R_def)
  apply (clarsimp simp: LI_def)
  apply (erule_tac x=e in allE)
  apply (clarsimp simp: rel_semi_def)
  apply (drule_tac c="(t', ta)" in set_mp)
   apply (rule_tac b=s' in relcompI)
    apply simp
    apply (rule sub_big_steps_I_holds)
      apply (rule invariant_holds_inv_holds, assumption+)
  apply clarsimp
  apply (rule_tac x=y in exI)
  apply clarsimp
  apply (subst conj_commute)
  apply (rule context_conjI)
   apply (erule inv_holdsE[OF invariant_holds_inv_holds])
     apply assumption+
  apply (rule sub_big_steps.step[OF refl])
    apply assumption+
  apply (subgoal_tac "z \<in> Ic")
   prefer 2
   apply (rule_tac I=Ic in inv_holdsE[OF invariant_holds_inv_holds])
      apply assumption+
    apply (erule sub_big_steps_I_holds[OF invariant_holds_inv_holds])
     apply assumption+
  apply (subgoal_tac "Fin A t = Fin C s")
   apply (subgoal_tac "Fin A y = Fin C z")
    apply (simp(no_asm_use) add: internal_R_def)
    apply metis
   apply force+
  done

lemma LI_big_steps:
  "\<lbrakk>(s, s') \<in> big_steps C (internal_R C R) exmap ev;
    LI A C S (Ia \<times> Ic); A \<Turnstile> Ia; C \<Turnstile> Ic;
    (t, s) \<in> S; s \<in> Ic; t \<in> Ia\<rbrakk>
  \<Longrightarrow> \<exists>t'. (t, t') \<in> big_steps A (internal_R A R) exmap ev \<and> (t', s') \<in> S \<and> t' \<in> Ia"
  apply (drule big_stepsD)
  apply clarsimp
  apply (frule(2) sub_big_steps_I_holds[OF invariant_holds_inv_holds])
  apply (drule (6) LI_sub_big_steps)
  apply clarsimp
  apply (clarsimp simp: LI_def)
  apply (erule_tac x=a in allE)
  apply (clarsimp simp: rel_semi_def)
  apply (drule_tac c="(t', s')" in set_mp)
   apply (rule_tac b="s'a" in relcompI)
    apply simp
   apply simp
  apply clarsimp
  apply (rule_tac x=y in exI)
  apply simp
  apply (subst conj_commute)
  apply (rule context_conjI)
   apply (clarsimp simp: invariant_holds_def, blast)
  apply (rule big_steps.cstep)
     apply assumption+
   apply (simp add: internal_R_def)
   apply (subgoal_tac "Fin A t = Fin C s")
    apply (subgoal_tac "s' \<in> Ic")
     apply (subgoal_tac "Fin A y = Fin C s'")
      apply metis
     apply metis
    apply (simp(no_asm_use) add: invariant_holds_def, blast)
   apply force
  apply simp
  done

lemma inv_holds_Run_big_steps:
  "\<lbrakk>A [> I; s \<in> I; (s, t) \<in> Run (big_steps A R exmap) js\<rbrakk> \<Longrightarrow> t \<in> I"
  apply (induct js arbitrary: t rule: rev_induct)
   apply force
  apply (force intro: big_steps_I_holds dest: Run_mid)
  done

lemma refines_Run_big_steps:
  "\<lbrakk>(s, s') \<in> Run (big_steps C (internal_R C R) exmap) js;
    LI A C S (Ia \<times> Ic); A \<Turnstile> Ia; C \<Turnstile> Ic;
    (t, s) \<in> S; s \<in> Ic; t \<in> Ia\<rbrakk>
  \<Longrightarrow> \<exists>t'. (t, t') \<in> Run (big_steps A (internal_R A R) exmap) js \<and> (t', s') \<in> S \<and> t' \<in> Ia"
  apply (induct js arbitrary: s' rule: rev_induct)
   apply force
  apply (frule Run_mid)
  apply clarsimp
  apply atomize
  apply (erule_tac x=ta in allE)
  apply clarsimp
  apply (drule(4) LI_big_steps)
    apply (erule(2) inv_holds_Run_big_steps[OF invariant_holds_inv_holds])
   apply assumption
  apply clarsimp
  apply (rule_tac x="t'a" in exI)
  apply (force intro: Run_trans)
  done

text\<open>
   TODO: with some more work we can probably change both @{term "refines"}
   to be @{term "refines'"} (see below).
\<close>

lemma big_step_adt_refines:
  "\<lbrakk>LI A C S (Ia \<times> Ic); A \<Turnstile> Ia; C \<Turnstile> Ic\<rbrakk>
  \<Longrightarrow> refines (big_step_adt C (internal_R C R) exmap) (big_step_adt A (internal_R A R) exmap)"
  apply (subst refines_def)
  apply (clarsimp simp: execution_def steps_eq_Run)
  apply (clarsimp simp: image_def)
  apply (subst Bex_def, subst steps_eq_Run)
  apply (clarsimp simp: big_step_adt_def)
  apply (subgoal_tac "\<exists>a0'\<in> Init A s. (a0', s0') \<in> S")
   prefer 2
   apply (force simp: LI_def)
  apply clarsimp
  apply (frule(4) refines_Run_big_steps)
    apply (force simp: invariant_holds_def)
   apply (force simp: invariant_holds_def)
  apply clarsimp
  apply (rule_tac x="t'" in exI)
  apply (clarsimp simp: LI_def)
  apply (rule conjI)
   apply blast
  apply (subgoal_tac "xa \<in> Ic")
   apply simp
  apply (rule_tac s="s0'" in inv_holds_Run_big_steps[OF invariant_holds_inv_holds], assumption+)
   apply (force simp: invariant_holds_def)
  apply simp
  done

text \<open>
  A start at making the change mentioned above to
  @{thm big_step_adt_refines}.
\<close>

text \<open>
  Refinement restricted to states reachable from a common initial state
\<close>
definition refines'
where
  "refines' C A s0 \<equiv> \<forall>js s. system.reachable C s0 s \<longrightarrow> execution C s js \<subseteq> execution A s js"

lemma refines_refines':
  "refines C A \<Longrightarrow> refines' C A s"
  apply(auto simp: refines_def refines'_def)
  done

text \<open>Two validity requirements on the user operation (uop) of the infoflow adt.
        These definitions are mostly only needed in ADT_A_if_Refine.\<close>

text \<open>uop_nonempty is required to prove corres between do_user_op_if and doUserOp_if\<close>
definition uop_nonempty :: "user_transition_if \<Rightarrow> bool"
where
  "uop_nonempty uop \<equiv> \<forall>t pl pr pxn tc um es. uop t pl pr pxn (tc, um, es) \<noteq> {}"

text \<open>uop_sane is required to prove that the infoflow adt describes an enabled system\<close>
definition uop_sane :: "user_transition_if \<Rightarrow> bool"
where
  "uop_sane f \<equiv> \<forall>t pl pr pxn tcu. (f t pl pr pxn tcu) \<noteq> {} \<and>
                (\<forall>tc um es. (Some Interrupt, tc, um, es) \<notin> (f t pl pr pxn tcu))"

end

end
