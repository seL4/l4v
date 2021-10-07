(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory UserOp_IF
imports ArchSyscall_IF "Access.ArchADT_AC"
begin

text \<open>
  This theory defines an enhanced @{term do_user_op} function for the
  automaton used for the information flow proofs. This enhanced model of
  user behaviour is a less abstract representation than the original one;
  eventually we should probably extend the original one to match up with
  this one and remove the duplication.
\<close>

lemma equiv_symmetric:
  "equiv_for a b c d = equiv_for a b d c"
  by (auto simp: equiv_for_def)

lemma gets_ev''':
  "equiv_valid_inv I A (\<lambda>s. P s \<and> (\<forall>t. I s t \<and> A s t \<and> P t \<longrightarrow> f s = f t)) (gets f)"
  apply (simp add: equiv_valid_def2)
  apply (auto simp: equiv_valid_2_def in_monad)
  done

lemma spec_equiv_valid_add_asm:
  "(P st \<Longrightarrow> spec_equiv_valid_inv st I A P f) \<Longrightarrow> spec_equiv_valid_inv st I A P f"
  by (clarsimp simp: spec_equiv_valid_def equiv_valid_2_def)

lemma spec_equiv_valid_add_rel:
  "\<lbrakk> spec_equiv_valid_inv st I A (P and I st) f; \<And>s. I s s \<rbrakk>
     \<Longrightarrow> spec_equiv_valid_inv st I A P f"
  by (clarsimp simp: spec_equiv_valid_def equiv_valid_2_def)

lemma spec_equiv_valid_add_rel':
  "\<lbrakk> spec_equiv_valid_inv st I A (P and A st) f; \<And>s. A s s \<rbrakk>
     \<Longrightarrow> spec_equiv_valid_inv st I A P f"
  by (clarsimp simp: spec_equiv_valid_def equiv_valid_2_def)

lemma reads_equiv_g_refl:
  "reads_equiv_g aag s s"
  apply (rule reads_equiv_gI)
   apply (rule reads_equiv_refl)
  apply (rule globals_equiv_refl)
  done

lemma spec_equiv_valid_inv_gets:
  assumes proj_retain: "\<And>t. \<lbrakk> P st; P t; I st t; A st t \<rbrakk> \<Longrightarrow> proj (f st) = proj (f t)"
  and spec_eqv_valid: "spec_equiv_valid_inv st I A P (g (proj (f st)))"
  shows "spec_equiv_valid_inv st I A P (do r \<leftarrow> gets f; g (proj r) od)"
  apply (clarsimp simp: spec_equiv_valid_def equiv_valid_2_def gets_def get_def bind_def return_def)
  apply (frule (3) proj_retain)
  apply (cut_tac spec_eqv_valid)
  apply (clarsimp simp: spec_equiv_valid_def equiv_valid_2_def gets_def get_def bind_def return_def)
  apply (drule spec)+
  apply (erule impE)
   apply fastforce
  apply fastforce
  done

lemmas spec_equiv_valid_inv_gets_more =
  spec_equiv_valid_inv_gets[where proj="\<lambda>x. (proj x, projsnd x)"
                              and g="\<lambda>z. g (fst z) (snd z)"
                              for proj and projsnd and g, simplified]

lemmas spec_equiv_valid_inv_gets_triple =
  spec_equiv_valid_inv_gets_more[where projsnd="\<lambda>x. (p (projsnd x), p' (projsnd x))"
                                   and g="\<lambda>a z. g a (fst z) (snd z)"
                                   for projsnd and p and p' and g, simplified]

lemma restrict_eq_imp_dom_eq:
  "a |` r = b|` r \<Longrightarrow> dom a \<inter> r = dom b \<inter> r"
  apply (clarsimp simp: set_eq_iff restrict_map_def)
  apply (drule_tac x = x in fun_cong)
  apply fastforce
  done

lemma restrict_map_eq_same_domain:
  "(\<And>x. x\<in> dom a \<Longrightarrow> b x = c x) \<Longrightarrow> a |` dom b = a |` dom c"
  apply (rule ext)
  apply (clarsimp simp: restrict_map_def)
  apply (intro conjI impI)
   apply fastforce
  apply (rule ccontr)
  apply (drule not_sym)
  apply fastforce
  done

lemma restrict_map_eq_same_domain_compl:
  "(\<And>x. x\<in> dom a \<Longrightarrow> b x = c x) \<Longrightarrow> a |` (- dom b) = a |` (- dom c)"
  apply (rule ext)
  apply (clarsimp simp: restrict_map_def)
  apply (intro conjI impI)
   apply fastforce
  apply (rule ccontr)
  apply (drule not_sym)
  apply fastforce
  done

lemma map_add_eq:
  "ms x = ms' x \<Longrightarrow> (ms ++ um) x = (ms' ++ um) x"
  by (clarsimp simp: map_add_def split: option.splits)


locale UserOp_IF_1 =
  assumes arch_globals_equiv_underlying_memory_update[simp]:
    "\<And>f. arch_globals_equiv ct it kh kh' as as' (underlying_memory_update f ms) ms' =
          arch_globals_equiv ct it kh kh' as as' ms ms'"
    "\<And>f. arch_globals_equiv ct it kh kh' as as' ms (underlying_memory_update f ms') =
          arch_globals_equiv ct it kh kh' as as' ms ms'"
  and arch_globals_equiv_device_state_update[simp]:
    "\<And>f. arch_globals_equiv ct it kh kh' as as' (device_state_update f ms) ms' =
          arch_globals_equiv ct it kh kh' as as' ms ms'"
    "\<And>f. arch_globals_equiv ct it kh kh' as as' ms (device_state_update f ms') =
          arch_globals_equiv ct it kh kh' as as' ms ms'"
begin

(* Assumptions:
 * User is deterministic based on an address being mapped with no rights or not mapped at all.
 * We implicitly assume that if you have any rights you must have at least read rights.
*)

lemma dmo_user_memory_update_reads_respects_g:
  "reads_respects_g aag l \<top> (do_machine_op (user_memory_update um))"
  apply (clarsimp simp: equiv_valid_def2 equiv_valid_2_def)
  apply (clarsimp simp: do_machine_op_def user_memory_update_def
                        gets_def get_def select_f_def bind_def in_monad)
  apply (clarsimp simp: reads_equiv_g_def globals_equiv_def split: option.splits)
  apply (subgoal_tac "reads_respects aag l \<top> (do_machine_op (user_memory_update um))")
   apply (fastforce simp: equiv_valid_def2 equiv_valid_2_def in_monad do_machine_op_def
                          user_memory_update_def select_f_def idle_equiv_def)
  apply (rule use_spec_ev)
  apply (simp add: user_memory_update_def)
  apply (rule do_machine_op_spec_reads_respects)
   apply (simp add: equiv_valid_def2)
   apply (rule modify_ev2)
   apply (fastforce intro: equiv_forI elim: equiv_forE split: option.splits)
  apply (wp | simp)+
  done

lemma dmo_device_state_update_reads_respects_g:
  "reads_respects_g aag l (\<lambda>s. dom um \<subseteq> device_region s) (do_machine_op (device_memory_update um))"
  apply (clarsimp simp: equiv_valid_def2 equiv_valid_2_def)
  apply (clarsimp simp: do_machine_op_def device_memory_update_def
                        gets_def get_def select_f_def bind_def in_monad)
  apply (clarsimp simp: reads_equiv_g_def globals_equiv_def split: option.splits)
  apply (subgoal_tac "reads_respects aag l \<top> (do_machine_op (device_memory_update um))")
   apply (fastforce simp: equiv_valid_def2 equiv_valid_2_def in_monad do_machine_op_def
                          device_memory_update_def select_f_def idle_equiv_def)
  apply (rule use_spec_ev)
  apply (simp add: device_memory_update_def)
  apply (rule do_machine_op_spec_reads_respects)
   apply (simp add: equiv_valid_def2)
   apply (rule modify_ev2)
   apply (fastforce intro: map_add_eq equiv_forI elim: equiv_forE split: option.splits)
  apply (wp | simp)+
  done

end

end
