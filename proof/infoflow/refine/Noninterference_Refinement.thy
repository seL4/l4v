(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Noninterference_Refinement
imports
  "InfoFlow.ArchNoninterference"
  "ArchADT_IF_Refine_C"
  "InfoFlow.Noninterference_Base_Refinement"
begin

(* FIXME: fp is currently ignored by ADT_C_if *)
consts fp :: bool

lemma internal_R_ADT_A_if:
  "internal_R (ADT_A_if uop) R = R"
  apply (rule ext, rule ext)
  apply (simp add: internal_R_def ADT_A_if_def)
  done

lemma LI_trans:
  "\<lbrakk>LI A H R (Ia \<times> Ih); LI H C S (Ih \<times> Ic); H \<Turnstile> Ih\<rbrakk>
    \<Longrightarrow> LI A C (R O (S \<inter> {(h, c). h \<in> Ih})) (Ia \<times> Ic)"
  apply (clarsimp simp: LI_def)
  apply safe
    apply (clarsimp simp: Image_def)
    apply (erule_tac x=s in allE)+
    apply (drule(1) set_mp)
    apply clarsimp
    apply (drule(1) set_mp)
    apply (clarsimp simp: invariant_holds_def)
    apply blast
   apply (clarsimp simp: rel_semi_def)
   apply (erule_tac x=j in allE)+
   apply (drule_tac c="(ya, z)" in set_mp)
    apply blast
   apply (clarsimp simp: invariant_holds_def)
   apply blast
  apply (erule_tac x=x in allE)
  apply (erule_tac x=y in allE)+
  apply (erule_tac x=z in allE)
  apply simp
  done

context kernel_m begin

definition big_step_ADT_C_if where
  "big_step_ADT_C_if utf \<equiv> big_step_adt (ADT_C_if fp utf) (internal_R (ADT_C_if fp utf) big_step_R) big_step_evmap"

(*Note: Might be able to generalise big_step_adt_refines for fw_sim*)
lemma big_step_ADT_C_if_big_step_ADT_A_if_refines:
  "uop_nonempty utf \<Longrightarrow> refines (big_step_ADT_C_if utf) (big_step_ADT_A_if utf) "
  apply (simp add: big_step_ADT_A_if_def big_step_ADT_C_if_def)
  apply (rule big_step_adt_refines[where A="ADT_A_if utf", simplified internal_R_ADT_A_if])
    apply (rule LI_trans)
      apply (erule global_automata_refine.fw_sim_abs_conc[OF haskell_to_abs])
     apply (erule global_automata_refine.fw_sim_abs_conc[OF c_to_haskell])
    apply (rule global_automaton_invs.ADT_invs[OF haskell_invs])
   apply (rule global_automaton_invs.ADT_invs[OF abstract_invs])
  apply simp
  done

end

lemma LI_sub_big_steps':
  "\<lbrakk>(s',as) \<in> sub_big_steps C (internal_R C R) s;
    LI A C S (Ia \<times> Ic); A [> Ia; C [> Ic;
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
      apply assumption+
  apply clarsimp
  apply (rule_tac x=y in exI)
  apply clarsimp
  apply (subst conj_commute)
  apply (rule context_conjI)
   apply (erule inv_holdsE)
     apply assumption+
  apply (rule sub_big_steps.step[OF refl])
    apply assumption+
  apply (subgoal_tac "z \<in> Ic")
   prefer 2
   apply (rule_tac I=Ic in inv_holdsE)
      apply assumption+
    apply (erule sub_big_steps_I_holds)
     apply assumption+
   apply (force simp: internal_R_def)
   done

lemma LI_rel_terminate:
  fixes s0
  assumes ex_abs: "\<And>s'. s' \<in> Ic \<Longrightarrow> (\<exists>s. s \<in> Ia \<and> (s, s') \<in> S)"
  assumes rel_correct: "\<And>s s' s0''. \<lbrakk>(internal_R C R)\<^sup>+\<^sup>+ s0'' s'; s0''\<in>Init C s0; (s, s') \<in> S\<rbrakk> \<Longrightarrow> \<exists>s0'\<in>Init A s0. (internal_R A R)\<^sup>+\<^sup>+ s0' s"
  assumes init_rel_correct: "\<And>s0''. s0'' \<in> Init C s0 \<Longrightarrow> \<exists>s0' \<in> Init A s0. (s0', s0'') \<in> S"
  assumes Ia_inv: "A [> Ia"
  assumes s0_Ia: "Init A s0 \<subseteq> Ia"
  assumes Ic_inv: "C [> Ic"
  assumes s0_Ic: "Init C s0 \<subseteq> Ic"
  assumes li: "LI A C S (Ia \<times> Ic)"
  shows "\<lbrakk>rel_terminate A s0 (internal_R A R) Ia (internal_R A measuref)\<rbrakk>
    \<Longrightarrow> rel_terminate C s0 (internal_R C R) Ic (internal_R C measuref)"
  apply (simp add: rel_terminate_def)
  apply (clarsimp simp: rtranclp_def2)
  apply (erule disjE)
   apply (cut_tac s'=s in ex_abs, assumption)
   apply clarsimp
   apply (cut_tac s=sa and s'=s in rel_correct, assumption+)
   apply (erule_tac x="sa" in allE)
   apply simp
   apply (erule impE)
    apply blast
   apply (erule_tac x=as in allE)
   apply (frule(3) LI_sub_big_steps'[OF _ li Ia_inv Ic_inv])
   apply clarsimp
   apply (erule_tac x=t' in allE)
   apply simp
   using li
   apply (clarsimp simp: LI_def)
   apply (erule_tac x=a in allE)
   apply (clarsimp simp: rel_semi_def)
   apply (frule(1) sub_big_steps_I_holds[OF Ic_inv])
   apply (drule_tac c="(t', s'')" in set_mp)
    apply blast
   apply clarsimp
   apply (erule_tac x=y in allE)
   apply (erule impE)
    apply blast
   apply (simp add: internal_R_def)
   apply (frule_tac x=sa in spec, drule_tac x=s in spec)
   apply (frule_tac x=y in spec, drule_tac x=z in spec)
   apply (drule_tac x=x in spec, drule_tac x=s' in spec)
   apply simp
   using Ia_inv Ic_inv
   apply (clarsimp simp: invariant_holds_def inv_holds_def)
   apply (erule_tac x=a in allE)+
   apply (drule_tac c=y in set_mp, blast)
   apply (drule_tac c=z in set_mp, blast)
   apply simp
  apply clarsimp
  apply (cut_tac s0''=s0' in init_rel_correct, assumption+)
  apply clarsimp
  apply (erule_tac x="s0'a" in allE)
  apply (frule set_mp[OF s0_Ia])
  apply (erule impE)
   apply blast
  apply (erule_tac x=as in allE)
  apply (frule(3) LI_sub_big_steps'[OF _ li Ia_inv Ic_inv])
  apply clarsimp
  apply (erule_tac x=t' in allE)
  apply simp
  using li
  apply (clarsimp simp: LI_def)
  apply (erule_tac x=a in allE)+
  apply (clarsimp simp: rel_semi_def)
  apply (frule(1) sub_big_steps_I_holds[OF Ic_inv])
  apply (drule_tac c="(t', s'')" in set_mp)
   apply blast
  apply clarsimp
  apply (erule_tac x=y in allE)
  apply (erule impE)
   apply blast
  apply (simp add: internal_R_def)
  apply (frule_tac x=s0'a in spec, drule_tac x=s0' in spec)
  apply (frule_tac x=y in spec, drule_tac x=z in spec)
  apply (drule_tac x=x in spec, drule_tac x=s' in spec)
  apply simp
  using Ia_inv Ic_inv
  apply (clarsimp simp: invariant_holds_def inv_holds_def)
  apply (erule_tac x=a in allE)+
  apply (drule_tac c=y in set_mp, blast)
  apply (drule_tac c=z in set_mp, blast)
  apply simp
  done


locale valid_initial_state_C = valid_initial_state + kernel_m +
  assumes ADT_C_if_serial:
    "\<forall>s' a. (\<exists>hs. (hs, s') \<in> lift_fst_rel (lift_snd_rel rf_sr) \<and> hs \<in> full_invs_if')
                        \<longrightarrow> (\<exists>t. (s', t) \<in> data_type.Step (ADT_C_if fp utf) a)"

lemma internal_R_tranclp:
  "(internal_R A R)\<^sup>+\<^sup>+ s s' \<Longrightarrow> R\<^sup>+\<^sup>+ (Fin A s) (Fin A s')"
  apply (induct rule: tranclp.induct)
   apply (simp add: internal_R_def)
  apply (simp add: internal_R_def)
  done

lemma inv_holds_transport:
  "\<lbrakk> A [> Ia; C [> Ic; LI A C R (Ia \<times> Ic) \<rbrakk> \<Longrightarrow> C [> {s'. \<exists>s. (s,s') \<in> R \<and> s \<in> Ia \<and> s' \<in> Ic}"
  apply (clarsimp simp: LI_def inv_holds_def)
  apply (erule_tac x=j in allE)+
  apply (clarsimp simp: rel_semi_def)
  apply (subgoal_tac "(s,x) \<in> Step A j O R")
   prefer 2
   apply blast
  apply blast
  done

lemma inv_holds_T: "A [> UNIV"
  by (simp add: inv_holds_def)

context valid_initial_state_C begin

lemma LI_abs_to_c:
  "LI (ADT_A_if utf) (ADT_C_if fp utf)
   (((lift_fst_rel (lift_snd_rel state_relation)))
     O ((lift_fst_rel (lift_snd_rel rf_sr)) \<inter> {(h, c). h \<in> full_invs_if'}))
   (full_invs_if \<times> UNIV)"
  apply (rule LI_trans)
    apply (rule global_automata_refine.fw_sim_abs_conc[OF haskell_to_abs])
    apply (rule uop_nonempty)
   apply (rule global_automata_refine.fw_sim_abs_conc[OF c_to_haskell])
   apply (rule uop_nonempty)
  apply (rule global_automaton_invs.ADT_invs[OF haskell_invs])
  done

lemma ADT_C_if_Init_Fin_serial:
  "Init_Fin_serial (ADT_C_if fp utf) s {s'. \<exists>hs. (hs, s') \<in> lift_fst_rel (lift_snd_rel rf_sr) \<and> hs \<in> full_invs_if'}"
  apply (unfold_locales)
     apply (subgoal_tac "ADT_C_if fp utf \<Turnstile> P" for P)
      prefer 2
      apply (rule fw_inv_transport)
        apply (rule global_automaton_invs.ADT_invs)
        apply (rule haskell_invs)
       apply (rule invariant_T)
      apply (rule global_automata_refine.fw_sim_abs_conc)
      apply (rule c_to_haskell)
      apply (rule uop_nonempty)
     apply simp
    apply (rule ADT_C_if_serial[rule_format])
    apply simp
   apply (clarsimp simp: ADT_C_if_def lift_fst_rel_def lift_snd_rel_def)
   apply blast
  apply (clarsimp simp: lift_fst_rel_def lift_snd_rel_def ADT_C_if_def)
  apply (rule_tac x=bb in exI)
  apply (clarsimp simp: full_invs_if'_def)
  apply (case_tac "sys_mode_of s", simp_all)
  done

lemma ADT_C_if_Init_Fin_serial_weak:
  "Init_Fin_serial_weak (ADT_C_if fp utf) s {s'.
                \<exists>hs. (hs, s') \<in> lift_fst_rel (lift_snd_rel rf_sr) \<and> hs \<in> full_invs_if'}"
  apply (rule Init_Fin_serial.serial_to_weak)
  apply (rule ADT_C_if_Init_Fin_serial)
  done

lemma Fin_ADT_C_if:
  "Fin (ADT_C_if fp utf) ((uc, s), m) = ((uc, cstate_to_A s), m)"
  by (simp add: ADT_C_if_def)

lemma Fin_Init_s0_ADT_C_if:
  "s0' \<in> Init (ADT_C_if fp utf) s0 \<Longrightarrow> Fin (ADT_C_if fp utf) s0' = s0"
  by (clarsimp simp: ADT_C_if_def s0_def)

lemma big_step_R_tranclp_abs':
        "\<lbrakk>(s, s')
        \<in> lift_fst_rel (lift_snd_rel state_relation) O
          lift_fst_rel (lift_snd_rel rf_sr);
        big_step_R\<^sup>+\<^sup>+ s0 s''\<rbrakk> \<Longrightarrow> s'' = (Fin (ADT_C_if fp utf) s')
       \<longrightarrow> big_step_R\<^sup>+\<^sup>+ s0 s"
  apply (erule tranclp_induct)
   apply (clarsimp simp: Fin_ADT_C_if lift_fst_rel_def)
   apply (rule tranclp.r_into_trancl)
   apply (simp add: big_step_R_def)
  apply (clarsimp simp: Fin_ADT_C_if lift_fst_rel_def)
  apply (rule tranclp.trancl_into_trancl)
   apply assumption
  apply (simp add: big_step_R_def)
  done

lemmas big_step_R_tranclp_abs = big_step_R_tranclp_abs'[rule_format]

lemma ADT_C_if_inv_holds_transport:
  "ADT_C_if fp utf [>
    {s'.
     \<exists>hs. (hs, s') \<in> lift_fst_rel (lift_snd_rel rf_sr) \<and>
          hs \<in> full_invs_if' \<and>
          (\<exists>as. (as, hs) \<in> lift_fst_rel (lift_snd_rel state_relation) \<and>
                invs_if as)}"
  apply (subst arg_cong[where f="\<lambda>S. ADT_C_if fp utf [> S"])
   prefer 2
   apply (rule_tac A="ADT_A_if utf" in inv_holds_transport)
     prefer 3
     apply (rule weaken_LI)
      apply (rule LI_abs_to_c)
     prefer 2
     apply (rule invs_if_inv_holds_ADT_A_if)
    prefer 2
    apply (rule inv_holds_T)
   apply (clarsimp simp: invs_if_full_invs_if)
  apply force
  done

lemma ADT_C_if_Init_transport:
  "Init (ADT_C_if fp utf) s0
    \<subseteq> {s'.
       \<exists>hs. (hs, s') \<in> lift_fst_rel (lift_snd_rel rf_sr) \<and>
            hs \<in> full_invs_if' \<and>
            (\<exists>as. (as, hs) \<in> lift_fst_rel (lift_snd_rel state_relation) \<and>
                  invs_if as)}"
  apply clarsimp
  apply (frule set_mp[OF global_automata_refine.init_refinement[OF c_to_haskell[OF uop_nonempty]]])
  apply (clarsimp simp: Image_def lift_fst_rel_def lift_snd_rel_def)
  apply (frule set_mp[OF global_automata_refine.init_refinement[OF haskell_to_abs[OF uop_nonempty]]])
  apply (clarsimp simp: Image_def lift_fst_rel_def lift_snd_rel_def)
  apply (rule_tac x=bb in exI)
  apply simp
  apply (rule conjI)
   apply (force simp: ADT_H_if_def)
  apply (rule_tac x=ba in exI)
  apply (clarsimp simp: ADT_A_if_def)
  done

lemma ADT_C_if_big_step_R_terminate:
  "rel_terminate (ADT_C_if fp utf) s0
           (internal_R (ADT_C_if fp utf) big_step_R)
           {s'. \<exists>hs. (hs, s') \<in> lift_fst_rel (lift_snd_rel rf_sr) \<and>
                hs \<in> full_invs_if' \<and> (\<exists>as. (as, hs) \<in>
                 lift_fst_rel (lift_snd_rel state_relation) \<and> invs_if as)}
           (\<lambda>s s'. internal_R (ADT_C_if fp utf) measuref_if s s')"
  apply (rule_tac S="lift_fst_rel (lift_snd_rel state_relation) O
                 (lift_fst_rel (lift_snd_rel rf_sr) \<inter> {(h, c). h \<in> full_invs_if'})"
             and Ia="Collect invs_if" and A="ADT_A_if utf" in LI_rel_terminate)
          apply blast
         prefer 8
         apply (simp add: internal_R_ADT_A_if)
         apply (rule ADT_A_if_big_step_R_terminate)
        apply (simp add: internal_R_ADT_A_if, simp add: ADT_A_if_def)
        apply (rule_tac x="s0" in bexI)
         apply (drule internal_R_tranclp)
         apply (simp add: Fin_Init_s0_ADT_C_if)
         apply clarsimp
         apply (rule big_step_R_tranclp_abs)
           apply force
          apply assumption
         apply simp
        apply (clarsimp simp: invs_if_full_invs_if extras_s0)
       apply (drule set_mp[OF global_automata_refine.init_refinement[OF c_to_haskell[OF uop_nonempty]]])
       apply (clarsimp simp: Image_def lift_fst_rel_def lift_snd_rel_def)
       apply (frule set_mp[OF global_automata_refine.init_refinement[OF haskell_to_abs[OF uop_nonempty]]])
       apply (clarsimp simp: Image_def lift_fst_rel_def lift_snd_rel_def)
       apply (rule_tac x="((aa, bc), bd)" in bexI)
        apply (rule_tac b="((aa, bb), bd)" in relcompI)
         apply simp
        apply (force simp: ADT_H_if_def)
       apply simp
      apply (rule invs_if_inv_holds_ADT_A_if)
     apply (simp add: ADT_A_if_def invs_if_full_invs_if extras_s0)
    apply (rule ADT_C_if_inv_holds_transport)
   apply (rule ADT_C_if_Init_transport)
  apply (rule weaken_LI[OF LI_abs_to_c])
  apply (clarsimp simp: invs_if_full_invs_if)
  done

lemma big_step_ADT_C_if_enabled_system:
  "enabled_system (big_step_ADT_C_if utf) s0"
  apply (simp add: big_step_ADT_C_if_def)
  apply (rule_tac measuref="internal_R (ADT_C_if fp utf) measuref_if" in big_step_adt_enabled_system)
     apply simp
    apply (force simp: big_step_R_def internal_R_def)
   apply (rule Init_Fin_serial_weak_strengthen)
      apply (rule ADT_C_if_Init_Fin_serial_weak)
     apply (rule ADT_C_if_inv_holds_transport)
    apply force
   apply (rule ADT_C_if_Init_transport)
  apply (rule ADT_C_if_big_step_R_terminate)
  done

end

sublocale valid_initial_state_C \<subseteq>
     abstract_to_C: noninterference_refinement
                           "big_step_ADT_A_if utf" (* the ADT that we prove infoflow for *)
                           s0                      (* initial state *)
                           "\<lambda>e s. part s"          (* dom function *)
                           "uwr" (* uwr *)
                           "policyFlows (pasPolicy initial_aag)" (* policy *)
                           "undefined"             (* out -- unused *)
                           PSched                  (* scheduler partition name *)
                           "big_step_ADT_C_if utf"
  apply(unfold_locales)
   apply(insert big_step_ADT_C_if_enabled_system)[1]
   apply(fastforce simp: enabled_system_def)
  apply(rule big_step_ADT_C_if_big_step_ADT_A_if_refines)
  apply (rule uop_nonempty)
  done

context valid_initial_state_C begin

lemma xnonleakage_C:
  "abstract_to_C.conc.xNonleakage_gen"
  apply(rule abstract_to_C.xNonleakage_gen_refinement_closed)
  apply(rule xnonleakage)
  done

end

end
