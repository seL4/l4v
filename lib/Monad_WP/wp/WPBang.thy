(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory WPBang
imports
  WP
  "../../ProvePart"
  "../NonDetMonadVCG"
begin

lemma conj_meta_forward:
  "P \<and> Q \<Longrightarrow> (P \<Longrightarrow> P') \<Longrightarrow> (Q \<Longrightarrow> Q') \<Longrightarrow> P' \<and> Q'"
  by simp

text \<open>Applying safe WP rules.\<close>
ML \<open>
structure WP_Safe = struct

fun check_has_frees_tac Ps (_ : int) thm = let
    val fs = Term.add_frees (Thm.prop_of thm) [] |> filter (member (=) Ps)
  in if null fs then Seq.empty else Seq.single thm end

fun wp_bang wp_safe_rules ctxt = let
    val wp_safe_rules_conj = ((wp_safe_rules RL @{thms hoare_vcg_conj_lift hoare_vcg_R_conj})
        RL @{thms hoare_strengthen_post hoare_post_imp_R})
      |> map (rotate_prems 1)
  in
    resolve_tac ctxt wp_safe_rules_conj
    THEN' Split_To_Conj.get_split_tac "P" ctxt
      (fn Ps => fn i => eresolve0_tac [@{thm conj_meta_forward}] i
        THEN (REPEAT_ALL_NEW ((CHANGED o asm_full_simp_tac ctxt)
              ORELSE' Classical.safe_steps_tac ctxt)
          THEN_ALL_NEW Partial_Prove.cleanup_tac ctxt Ps) i
        THEN (Partial_Prove.finish_tac ctxt Ps THEN' (assume_tac ctxt)) i
      )
  end

val wpe_args =
  Attrib.thms >> curry (fn (rules, ctxt) =>
    Method.SIMPLE_METHOD (
      wp_bang rules ctxt 1
    )
  );

end
\<close>

method_setup wpe = \<open>WP_Safe.wpe_args\<close>
  "applies 'safe' wp rules to eliminate postcondition components"

text \<open>Testing.\<close>

lemma
  assumes x: "\<lbrace> P \<rbrace> f \<lbrace> \<lambda>rv. Q \<rbrace>"
       and y: "\<lbrace> P \<rbrace> f \<lbrace> \<lambda>rv. R \<rbrace>"
  shows
  "\<lbrace> P \<rbrace> f \<lbrace> \<lambda>rv s. \<forall>x y. (fst rv = Some x \<longrightarrow> Q s)
    \<and> (snd rv = Some y \<longrightarrow> Q s )
    \<and> R s \<rbrace>"
  apply (rule hoare_pre)
   apply (simp add: all_conj_distrib)
   apply (rule hoare_vcg_conj_lift)
    apply (wpe x)
    apply wp
   apply (wpe x)
   apply (wp y)
  apply simp
  done

end
