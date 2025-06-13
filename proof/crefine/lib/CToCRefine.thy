(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory CToCRefine

imports
    "CSpec.Substitute"
    "CLib.SimplRewrite"
    Lib.Lib
    "CParser.TypHeapLib"
begin

lemma spec_statefn_simulates_lookup_tree_Node:
  "\<lbrakk> exec_statefn_simulates g UNIV UNIV v v';
     spec_statefn_simulates g (lookup_tree a f) (lookup_tree c f);
     spec_statefn_simulates g (lookup_tree b f) (lookup_tree d f) \<rbrakk>
    \<Longrightarrow> spec_statefn_simulates g (lookup_tree (Node n v a b) f) (lookup_tree (Node n v' c d) f)"
  by (simp add: spec_statefn_simulates_def)

lemma spec_statefn_simulates_lookup_tree_Leaf:
  "spec_statefn_simulates g (lookup_tree Leaf f) (lookup_tree Leaf f')"
  by (simp add: spec_statefn_simulates_def)

ML \<open>
fun mk_meta_eq_safe t = mk_meta_eq t
  handle THM _ => t;

val unfold_bodies = Simplifier.make_simproc @{context}
  {name = "unfold constants named *_body",
   kind = Simproc,
   lhss = [@{term "v"}],
   proc = fn _ =>
     (fn ctxt => (fn t => case head_of (Thm.term_of t) of
       Const (s, _) => if String.isSuffix "_body" s
          then try (Global_Theory.get_thm (Proof_Context.theory_of ctxt) #> mk_meta_eq_safe) (suffix "_def" s)
          else NONE
      | _ => NONE)),
   identifier = []}
\<close>

theorem spec_refine:
  notes if_split[split del]
  shows
  "spec_statefn_simulates id (kernel_all_global_addresses.\<Gamma> symbol_table)
     (kernel_all_substitute.\<Gamma> symbol_table domain)"
  apply (simp add: kernel_all_global_addresses.\<Gamma>_def kernel_all_substitute.\<Gamma>_def)
  apply (intro spec_statefn_simulates_lookup_tree_Node spec_statefn_simulates_lookup_tree_Leaf)
  apply (tactic \<open>ALLGOALS (asm_simp_tac (put_simpset HOL_ss @{context} addsimps @{thms switch.simps fst_conv snd_conv}
                  addsimprocs [unfold_bodies] |> Splitter.del_split @{thm if_split}))
              THEN ALLGOALS (TRY o resolve_tac @{context} @{thms exec_statefn_simulates_refl})\<close>)

  apply (tactic \<open>ALLGOALS (REPEAT_ALL_NEW (resolve_tac @{context} @{thms exec_statefn_simulates_comI
                      exec_statefn_simulates_additionals}))\<close>)
  apply (unfold id_apply)
  apply (tactic \<open>ALLGOALS (TRY o resolve_tac @{context} @{thms refl bij_id})\<close>)
  apply (tactic \<open>ALLGOALS (TRY o (resolve_tac @{context} @{thms subsetI} THEN' resolve_tac @{context} @{thms CollectI}
           THEN' REPEAT_ALL_NEW (eresolve_tac @{context} @{thms IntE CollectE conjE exE h_t_valid_c_guard conjI} ORELSE' assume_tac @{context})))\<close>)
  (*
    apply (tactic {* ALLGOALS (TRY o ((REPEAT_ALL_NEW (rtac @{thm c_guard_field}) THEN' etac @{thm h_t_valid_c_guard})
                          THEN_ALL_NEW simp_tac @{simpset}
                          THEN_ALL_NEW simp_tac @{simpset}
                          THEN_ALL_NEW K no_tac))  *})
  *)
  apply (rule bij_id[simplified id_def])+
  done (* Woo! *)

end

