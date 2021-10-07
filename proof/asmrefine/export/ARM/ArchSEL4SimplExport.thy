(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchSEL4SimplExport
imports "AsmRefine.SimplExport" "CSpec.Substitute"
begin

context kernel_all_substitute begin

lemma ctzl_body_refines:
  "simple_simpl_refines \<Gamma> (Guard ImpossibleSpec \<lbrace>\<acute>x___unsigned_long \<noteq> 0\<rbrace>
    (\<acute>ret__long :== ucast (bv_ctz (\<acute>x___unsigned_long)))) ctzl_body"
  apply (simp add: ctzl_body_def)
  apply (rule simple_simpl_refines_guarded_Basic_guarded_spec_body)
  apply (clarsimp simp: bv_ctz_def meq_def)
  done

lemma clzl_body_refines:
  "simple_simpl_refines \<Gamma> (Guard ImpossibleSpec \<lbrace>\<acute>x___unsigned_long \<noteq> 0\<rbrace>
    (\<acute>ret__long :== ucast (bv_clz (\<acute>x___unsigned_long)))) clzl_body"
  apply (simp add: clzl_body_def)
  apply (rule simple_simpl_refines_guarded_Basic_guarded_spec_body)
  apply (clarsimp simp: bv_clz_def meq_def)
  done

end

end
