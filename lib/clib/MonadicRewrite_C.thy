(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(* A theory of rewriting under refinement. *)

theory MonadicRewrite_C
imports
  "Lib.MonadicRewrite"
  Corres_UL_C
begin

lemma monadic_rewrite_ccorres_assemble:
  assumes cc: "ccorres_underlying sr G r xf ar axf P P' hs f c"
  assumes mr: "monadic_rewrite True False Q g f"
  shows       "ccorres_underlying sr G r xf ar axf (P and Q) P' hs g c"
proof -
  have snd: "\<And>s. \<lbrakk> Q s; \<not> snd (g s) \<rbrakk> \<Longrightarrow> \<not> snd (f s)"
    using mr
    by (simp add: monadic_rewrite_def)

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
