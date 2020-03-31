(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory SEL4SimplExport
imports "AsmRefine.SimplExport" "CSpec.Substitute"
begin

ML \<open>
val csenv = let
    val the_csenv = CalculateState.get_csenv @{theory} "../c/build/$L4V_ARCH/kernel_all.c_pp" |> the
  in fn () => the_csenv end
\<close>

context kernel_all_substitute begin

lemma ctzl_body_refines:
  "simple_simpl_refines \<Gamma> (Guard ImpossibleSpec \<lbrace>\<acute>x \<noteq> 0\<rbrace>
    (\<acute>ret__long :== ucast (bv_ctz (\<acute>x)))) ctzl_body"
  apply (simp add: ctzl_body_def)
  apply (rule simple_simpl_refines_guarded_Basic_guarded_spec_body)
  apply (clarsimp simp: bv_ctz_def meq_def)
  done

lemma clzl_body_refines:
  "simple_simpl_refines \<Gamma> (Guard ImpossibleSpec \<lbrace>\<acute>x \<noteq> 0\<rbrace>
    (\<acute>ret__long :== ucast (bv_clz (\<acute>x)))) clzl_body"
  apply (simp add: clzl_body_def)
  apply (rule simple_simpl_refines_guarded_Basic_guarded_spec_body)
  apply (clarsimp simp: bv_clz_def meq_def)
  done

declare ctcb_offset_defs[simp]

ML \<open>
  ParseGraph.mkdir_relative @{theory} (getenv "L4V_ARCH");
  val CFunDump_filename_export = getenv "L4V_ARCH" ^ "/" ^ "CFunDump.txt";
  val CFunDump_filename = "export/" ^ CFunDump_filename_export;
  emit_C_everything_relative @{context} (csenv ()) CFunDump_filename_export;
\<close>

end

end

