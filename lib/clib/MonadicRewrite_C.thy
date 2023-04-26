(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* A theory of rewriting under refinement. *)

theory MonadicRewrite_C
imports
  "Lib.MonadicRewrite"
  Corres_UL_C
begin

lemma monadic_rewrite_ccorres_assemble:
  assumes cc: "ccorres_underlying sr G r xf ar axf P P' hs f c"
  assumes mr: "monadic_rewrite F E Q g f"
  shows       "ccorres_underlying sr G r xf ar axf (P and Q) P' hs g c"
proof -
  have snd: "\<And>s. \<lbrakk> Q s; \<not> snd (g s) \<rbrakk> \<Longrightarrow> \<not> snd (f s)"
    using mr
    by (fastforce simp: monadic_rewrite_def)

  have fst: "\<And>s v. \<lbrakk> Q s; \<not> snd (g s); v \<in> fst (f s) \<rbrakk> \<Longrightarrow> v \<in> fst (g s)"
    using mr
    by (auto simp add: monadic_rewrite_def)

  show ?thesis
    apply (rule ccorresI')
    apply (erule ccorresE[OF cc], (simp add: snd)+)
    apply clarsimp
    apply (rule rev_bexI[OF fst], assumption+)
    apply simp
    done
qed

end
