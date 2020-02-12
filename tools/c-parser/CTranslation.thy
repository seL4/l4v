(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory CTranslation
imports
  "PackedTypes"
  "PrettyProgs"
  "StaticFun"
  "IndirectCalls"
  "ModifiesProofs"
  "Lib.MLUtils"
  "HOL-Eisbach.Eisbach"
keywords
  "cond_sorry_modifies_proofs"
  "install_C_file"
  "install_C_types"
  "new_C_include_dir":: thy_decl
and
  "memsafe"
  "c_types"
  "c_defs"
begin

lemma TWO: "Suc (Suc 0) = 2" by arith

definition
  fun_addr_of :: "int \<Rightarrow> unit ptr" where
  "fun_addr_of i \<equiv> Ptr (word_of_int i)"

definition
  ptr_range :: "'a::c_type ptr \<Rightarrow> addr set" where
  "ptr_range p \<equiv> {ptr_val (p::'a ptr) ..< ptr_val p + word_of_int(int(size_of (TYPE('a)))) }"

lemma guarded_spec_body_wp [vcg_hoare]:
  "P \<subseteq> {s. (\<forall>t. (s,t) \<in> R \<longrightarrow> t \<in> Q) \<and> (Ft \<notin> F \<longrightarrow> (\<exists>t. (s,t) \<in> R))}
  \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F \<^esub> P (guarded_spec_body Ft R) Q, A"
  apply (simp add: guarded_spec_body_def)
  apply (cases "Ft \<in> F")
   apply (erule HoarePartialDef.Guarantee)
   apply (rule HoarePartialDef.conseqPre, rule HoarePartialDef.Spec)
   apply auto[1]
  apply (rule HoarePartialDef.conseqPre, rule HoarePartialDef.Guard[where P=P])
   apply (rule HoarePartialDef.conseqPre, rule HoarePartialDef.Spec)
   apply auto[1]
  apply simp
  apply (erule order_trans)
  apply (auto simp: image_def Bex_def)
  done


ML_file "tools/mlyacc/mlyacclib/MLY_base-sig.ML"
ML_file "tools/mlyacc/mlyacclib/MLY_join.ML"
ML_file "tools/mlyacc/mlyacclib/MLY_lrtable.ML"
ML_file "tools/mlyacc/mlyacclib/MLY_stream.ML"
ML_file "tools/mlyacc/mlyacclib/MLY_parser2.ML"
ML_file "FunctionalRecordUpdate.ML"
ML_file "topo_sort.ML"
ML_file "isa_termstypes.ML"
ML_file "StrictC.grm.sig"
ML_file "StrictC.grm.sml"
ML_file "StrictC.lex.sml"
ML_file "StrictCParser.ML"
ML_file "complit.ML"
ML_file "hp_termstypes.ML"
ML_file "termstypes-sig.ML"
ML_file "termstypes.ML"
ML_file "UMM_termstypes.ML"
ML_file "recursive_records/recursive_record_pp.ML"
ML_file "recursive_records/recursive_record_package.ML"
ML_file "expression_typing.ML"
ML_file "UMM_Proofs.ML"
ML_file "program_analysis.ML"
ML_file "heapstatetype.ML"
ML_file "MemoryModelExtras-sig.ML"
ML_file "MemoryModelExtras.ML"
ML_file "calculate_state.ML"
ML_file "syntax_transforms.ML"
ML_file "expression_translation.ML"
ML_file "modifies_proofs.ML"
ML_file "HPInter.ML"
ML_file "stmt_translation.ML"
ML_file "isar_install.ML"
ML_file "shorten_names.ML"

method_setup shorten_names = \<open>Shorten_Names.shorten_names\<close>
    "shorten munged C parser names in bound variables"

method_setup shorten_names_preserve_new = \<open>Shorten_Names.shorten_names_preserve_new\<close>
    "shorten munged C parser names in bound variables, preserving newer names in case of collisions"

ML \<open>
  fun then_shorten_names mp =
      mp -- Shorten_Names.shorten_names >> MethodExtras.then_all_new;
\<close>

method_setup vcg = \<open>Hoare.vcg |> then_shorten_names\<close>
    "Simpl 'vcg' followed by C parser 'shorten_names'"

method_setup vcg_step = \<open>Hoare.vcg_step |> then_shorten_names\<close>
    "Simpl 'vcg_step' followed by C parser 'shorten_names'"

declare typ_info_word [simp del]
declare typ_info_ptr [simp del]

lemma valid_call_Spec_eq_subset:
  "\<Gamma>' procname = Some (Spec R) \<Longrightarrow>
  HoarePartialDef.valid \<Gamma>' NF P (Call procname) Q A = (P \<subseteq> fst ` R \<and> (R \<subseteq> (- P) \<times> UNIV \<union> UNIV \<times> Q))"
  apply (safe; simp?)
    apply (clarsimp simp: HoarePartialDef.valid_def)
    apply (rule ccontr)
    apply (drule_tac x="Normal x" in spec, elim allE,
           drule mp, erule exec.Call, rule exec.SpecStuck)
     apply (auto simp: image_def)[2]
   apply (clarsimp simp: HoarePartialDef.valid_def)
   apply (elim allE, drule mp, erule exec.Call, erule exec.Spec)
   apply auto[1]
  apply (clarsimp simp: HoarePartialDef.valid_def)
  apply (erule exec_Normal_elim_cases, simp_all)
  apply (erule exec_Normal_elim_cases, auto)
  done

lemma creturn_wp [vcg_hoare]:
  assumes "P \<subseteq> {s. (exnupd (\<lambda>_. Return)) (rvupd (\<lambda>_. v s) s) \<in> A}"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F \<^esub>P creturn exnupd rvupd v Q, A"
  unfolding creturn_def
  by vcg

lemma creturn_void_wp [vcg_hoare]:
  assumes "P \<subseteq> {s. (exnupd (\<lambda>_. Return)) s \<in> A}"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F \<^esub>P creturn_void exnupd Q, A"
  unfolding creturn_void_def
  by vcg

lemma cbreak_wp [vcg_hoare]:
  assumes "P \<subseteq> {s. (exnupd (\<lambda>_. Break)) s \<in> A}"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F \<^esub>P cbreak exnupd Q, A"
  unfolding cbreak_def
  by vcg

lemma ccatchbrk_wp [vcg_hoare]:
  assumes "P \<subseteq> {s. (exnupd s = Break \<longrightarrow> s \<in> Q) \<and>
                    (exnupd s \<noteq> Break \<longrightarrow> s \<in> A)}"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F \<^esub>P ccatchbrk exnupd Q, A"
  unfolding ccatchbrk_def
  by vcg

lemma cchaos_wp [vcg_hoare]:
  assumes "P \<subseteq>  {s. \<forall>x. (v x s) \<in> Q }"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F \<^esub>P cchaos v Q, A"
  unfolding cchaos_def
  using assms by (blast intro: HoarePartial.Spec)

lemma lvar_nondet_init_wp [vcg_hoare]:
  "P \<subseteq> {s. \<forall>v. (upd (\<lambda>_. v)) s \<in> Q} \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F \<^esub> P lvar_nondet_init accessor upd Q, A"
  unfolding lvar_nondet_init_def
  by (rule HoarePartialDef.conseqPre, vcg, auto)

lemma mem_safe_lvar_init [simp,intro]:
  assumes upd: "\<And>g v s. globals_update g (upd (\<lambda>_. v) s) = upd (\<lambda>_. v) (globals_update g s)"
  assumes acc: "\<And>v s. globals (upd (\<lambda>_. v) s) = globals s"
  assumes upd_acc: "\<And>s. upd (\<lambda>_. accessor s) s = s"
  shows "mem_safe (lvar_nondet_init accessor upd) x"
  apply (clarsimp simp: mem_safe_def lvar_nondet_init_def)
  apply (erule exec.cases; clarsimp simp: restrict_safe_def)
   apply (fastforce simp: restrict_safe_OK_def restrict_htd_def upd acc intro: exec.Spec)
  apply (fastforce simp: exec_fatal_def restrict_htd_def upd acc intro: upd_acc exec.SpecStuck)
  done

lemma intra_safe_lvar_nondet_init [simp]:
  "intra_safe (lvar_nondet_init accessor upd :: (('a::heap_state_type','d) state_scheme,'b,'c) com) =
   (\<forall>\<Gamma>. mem_safe (lvar_nondet_init accessor upd :: (('a::heap_state_type','d) state_scheme,'b,'c) com)
                 (\<Gamma> :: (('a,'d) state_scheme,'b,'c) body))"
  by (simp add: lvar_nondet_init_def)

lemma proc_deps_lvar_nondet_init [simp]:
  "proc_deps (lvar_nondet_init accessor upd) \<Gamma> = {}"
  by (simp add: lvar_nondet_init_def)

declare word_neq_0_conv[simp] (* FIXME: for backward compatibility; remove *)

end
