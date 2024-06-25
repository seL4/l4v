(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory ExtraSpecs

imports
  "CParser.TypHeapLib"

begin

definition
  "simple_simpl_refines \<Gamma> com com'
    = (\<forall>s. (\<exists>ft. \<Gamma> \<turnstile> \<langle>com', Normal s\<rangle> \<Rightarrow> Fault ft)
        \<or> ((\<forall>xs. \<Gamma> \<turnstile> \<langle>com, Normal s\<rangle> \<Rightarrow> xs \<longrightarrow> \<Gamma> \<turnstile> \<langle>com', Normal s\<rangle> \<Rightarrow> xs)
            \<and> (\<not> terminates \<Gamma> com (Normal s) \<longrightarrow> \<not> terminates \<Gamma> com' (Normal s))))"

lemma simple_simpl_refines_no_fault_execD:
  "\<Gamma> \<turnstile> \<langle>com,Normal s\<rangle> \<Rightarrow> xs
    \<Longrightarrow> simple_simpl_refines \<Gamma> com com'
    \<Longrightarrow> (\<forall>ft. \<not> \<Gamma> \<turnstile> \<langle>com',Normal s\<rangle> \<Rightarrow> Fault ft)
    \<Longrightarrow> \<Gamma> \<turnstile> \<langle>com', Normal s\<rangle> \<Rightarrow> xs"
  by (auto simp add: simple_simpl_refines_def)

lemma simple_simpl_refines_no_fault_terminatesD:
  "simple_simpl_refines \<Gamma> com com'
    \<Longrightarrow> (\<forall>ft. \<not> \<Gamma> \<turnstile> \<langle>com',Normal s\<rangle> \<Rightarrow> Fault ft)
    \<Longrightarrow> \<not> terminates \<Gamma> com (Normal s) \<longrightarrow> \<not> terminates \<Gamma> com' (Normal s)"
  by (auto simp add: simple_simpl_refines_def)

lemma simple_simpl_refines_refl:
  "simple_simpl_refines \<Gamma> com com"
  by (auto simp add: simple_simpl_refines_def)

lemma simple_simpl_refines_from_def_eq:
  "body \<equiv> body' \<Longrightarrow> simple_simpl_refines \<Gamma> body' body"
  (* these are flipped, because the "implementation" is on the rhs of
     definitional equalities, but the lhs of refinement thms. *)
  by (simp add: simple_simpl_refines_def)

lemma simple_simpl_refines_trans:
  "simple_simpl_refines \<Gamma> com com' \<Longrightarrow> simple_simpl_refines \<Gamma> com' com''
    \<Longrightarrow> simple_simpl_refines \<Gamma> com com''"
  by (simp add: simple_simpl_refines_def, metis)

lemma simple_simpl_refines_drop_Guard:
  "simple_simpl_refines \<Gamma> com (Guard F G com)"
  apply (clarsimp simp add: simple_simpl_refines_def)
  apply (case_tac "s \<in> G")
  apply (auto intro: exec.Guard exec.GuardFault
              elim!: terminates_Normal_elim_cases)
  done

lemma simple_simpl_refines_guarded_Basic_guarded_spec_body:
  "(\<forall>s s'. (s, s') \<in> R \<longrightarrow> (s \<in> G \<and> (s, f s) \<in> R))
    \<Longrightarrow> simple_simpl_refines \<Gamma> (Guard F' G (Basic f)) (guarded_spec_body F R)"
  apply (simp add: guarded_spec_body_def simple_simpl_refines_def)
  apply (intro allI, drule_tac x=s in spec)
  apply (erule impCE)
   apply (rule disjI1)
   apply (fastforce intro: exec.GuardFault)
  apply (rule disjI2)
  apply (auto intro!: exec.Guard terminates.Guard
               intro: exec.GuardFault exec.Spec terminates.Basic image_eqI[rotated]
              elim!: exec_Normal_elim_cases terminates_Normal_elim_cases)
  done

lemmas simple_simpl_refines_Basic_guarded_spec_body
    = simple_simpl_refines_trans[OF
        simple_simpl_refines_drop_Guard[where G=UNIV]
        simple_simpl_refines_guarded_Basic_guarded_spec_body
        ]

ML \<open>
structure Get_Body_Refines = struct

fun get ctxt name = let
    fun pget sfx = try (Proof_Context.get_thm ctxt o suffix sfx) name
    val eqv = pget "_body_refines"
    val def = pget "_body_def"
  in case (eqv, def) of
      (SOME eqvt, _) => eqvt
    | (_, SOME deft) => (deft RS @{thm simple_simpl_refines_from_def_eq})
    | _ => raise THM ("Get_Body_Refines.get: "
          ^ "no body_def or body_refines: " ^ name, 1, [])
  end

end
\<close>

end
